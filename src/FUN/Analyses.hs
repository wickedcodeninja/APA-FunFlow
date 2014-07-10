-- (C) 2013 Pepijn Kokke & Wout Elsinghorst

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
module FUN.Analyses where

import FUN.Base
import FUN.Labeling
import FUN.Analyses.Flow
import FUN.Analyses.Measure
import FUN.Analyses.Utils

import Prelude hiding (mapM)

import Data.Monoid hiding ( Sum )
import Data.Functor ((<$>))
import Control.Applicative ( Applicative (..) )
import Data.Traversable ( sequenceA )
import Data.Foldable ( foldlM )
import Data.Traversable ( traverse )

import Control.Monad (foldM, join)
import Control.Monad.Error 
  ( Error (..)
  , ErrorT
  , runErrorT, throwError
  )

import Control.Monad.Supply 
  ( Supply, SupplyT
  , supply, evalSupply, evalSupplyT
  )
  
import Control.Monad.Trans (lift)

import Data.Traversable (forM, mapM)
import Data.Map (Map)
import Data.Set (Set, empty, union)

import qualified Data.Map  as M
import qualified Data.Set  as S
import qualified Data.List as L

import Text.Printf (printf)
        
        
-- * Type definitions

-- |Type variables
type TVar = String

-- |Representation for inferred types in our functional language. The Flow field
--  holds flow variables to which Control Flow Constraints are attached during the
--  execution of W. 
data Type
  = TVar  TVar
  | TBool
  | TInt  Scale Base
  | TArr  Flow Type Type        -- Function Arrow
  | TProd Flow Name Type Type   -- 
  | TSum  Flow Name Type Type
  | TUnit Flow Name
 -- deriving (Eq, Ord)

data TypeScheme
  = Type Type
  | Scheme (Set TVar) Type
  --deriving (Eq, Ord)

-- |Representation for possible errors in algorithm W.
data TypeError
  = CannotDestruct  Type      -- ^ thrown when attempting to destruct a non-product
  | PatternError    TVar TVar -- ^ thrown when pattern matching on a different type
  | UnboundVariable TVar      -- ^ thrown when unknown variable is encountered
  | OccursCheck     TVar Type -- ^ thrown when occurs check in unify fails
  | CannotUnify     Type Type -- ^ thrown when types cannot be unified
  | CannotUnifyMeasurement MeasureError
  | OtherError      String    -- ^ stores miscellaneous errors
 -- deriving Eq

class FTV t where
  ftv :: t -> [TVar]
  
  
-- |Returns the set of free type variables in a type.
instance FTV Type where 
  ftv TBool           = []
  ftv (TInt _ _)      = []
  ftv (TVar  n)     = [n]
  ftv (TArr  _   a b) = L.union (ftv a) (ftv b)
  ftv (TProd _ _ a b) = L.union (ftv a) (ftv b)
  ftv (TSum  _ _ a b) = L.union (ftv a) (ftv b)
  ftv (TUnit _ _)     = []
  
-- |Returns the set of free type variables in a type.
instance FTV TypeScheme where
  ftv (Type ty) = ftv ty
  ftv (Scheme bnds ty) = S.toList $ S.fromList (ftv ty) S.\\ bnds
  
-- |Extract the type from primitive literals.
typeOf :: Lit -> Type
typeOf (Bool _) = TBool
typeOf (Integer s b _) = TInt s b

-- |Collection of built-in functions available to all programs. At the time of writing, these
--  all serve to introduce (the by default) unitless integers to the world of typed units of
--  measure. The measure analysis makes sure all measure annotations properly propagate through
--  the program.
prelude :: Analysis (Env, [Decl])
prelude = 
  let id = Abs noLabel "x" (Var "x")
      predefs =
        [ ("asKelvin",  "Kelvin", id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        , ("asCelcius", "Kelvin", id, \v s -> TArr v (TInt SNil BNil) (TInt s  (BCon "Freezing")))
        , ("asFeet",    "Feet",   id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        , ("asMeters",  "Meter",  id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        , ("asDollars", "Dollar", id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        , ("asEuros",   "Euro",   id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        , ("asSeconds", "Second", id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        ]
  in do ps <- forM predefs $ \(nm, u, e, f) -> do v <- fresh;
                                                  return ( (nm, Type $ f v $ SCon u), Decl nm e)
        let (env, ds) = unzip ps;
        return ( mempty { typeMap = TSubst $ return $ M.fromList env }
               , ds
               )

-- |The Analysis Monad, the main datatype used by our implementation of W. The various
--  Monads have the following purposes:
--
--  ErrorT: this transformer is used for error reporting
--  SupplyT: this transformer threads a supply of fresh annotation variables. The supply
--           is shared by the various analyses.
--  Supply: thread a supply of fresh type variables
type Analysis a = ErrorT TypeError (SupplyT FVar (Supply TVar)) a


-- |`(x ~> t) env` can be read as 'simplify variable `x` to type `t` in the environment `env`
(~>) :: TVar -> Type -> Env -> Env
x ~> t = \env -> env { typeMap = TSubst $ do m <- getTSubst . typeMap $ env
                                             return $ M.insert x (Type t) m  
                     }

(~~>) :: TVar -> TypeScheme -> Env -> Env
x ~~> t = \env -> env { typeMap = TSubst $ do m <- getTSubst . typeMap $ env
                                              return $ M.insert x t m  
                      }
      
-- |The entrypoint to the analysis. Takes an untyped program as argument and returns either
--   Right:
--    1) An environment containing the type substitution necessary to make the program well typed.
--    2) The full program, including implicit prelude, together with Program Point annotations.
--    3) A set of unresolved constraints.
--   Left:
--    An error message saying why type checking failed.
--  
--  Errors are reported iff the type checking algorithm for the underlying type system would 
--  fail, although there may be unresolved constraints that are either inconsistent or just not fully
--  handled yet. 
analyseProgram :: Program -> Either TypeError (Map TVar TypeScheme, Program, Set Constraint)
analyseProgram (Prog ds) = withFreshVars $
  do -- |Initialize pre-typed prelude for standard measurement functions
    (preludeEnv, lib) <- prelude

    -- |Label both the incoming program and the prelude with program points
    let (labeledLib, labeledDecls) = runLabel $ (lib, ds)

    -- |Run W on each of the top level Decls of the Program, chaining the 
    --  results together, making the type of each Decl available to the Decls
    --  below it via the invironment.
        unpackedDecls = map (\(Decl nm e) -> (nm, e)) labeledDecls
    
        letBound = Let unpackedDecls (Lit . Bool $ False) 
    
    (_, checkedEnv, c0) <- analyse Global letBound $ preludeEnv
    
    let env = checkedEnv <> preludeEnv 
    
        scales = scaleMap env
    
    -- |Solve the various constraints
    let (f_s1, f_c1) = solveConstraints (flowMap env). extractFlowConstraints $ c0
        c1 = S.map FlowConstraint f_c1                                        
        
        (s_s2, s_c2) = solveConstraints (scaleMap env) . extractScaleConstraints $ c0
        c2 = S.map ScaleConstraint s_c2     
    
        (b_s3, b_c3) = solveConstraints (baseMap env) . extractBaseConstraints  $ c0
        c3 = S.map BaseConstraint b_c3
        
        finalEnv = subst b_s3 . subst s_s2  . subst f_s1 $ typeMap env
        
    unwrappedEnv <- getTSubst finalEnv


    -- |Return the refined environment, the input program together with prelude and
    --  a set of unsolved constraints.
    return ( unwrappedEnv
           , Prog $ labeledLib ++ labeledDecls
           , c1 `union` c2 `union` c3
           )

instantiate :: TypeScheme -> Analysis Type
instantiate (Type ty) = return ty 
instantiate (Scheme bnds ty) = 
  do r <- forM (S.toList bnds) $ \t -> 
            do v <- fresh
               return (t, Type $ v)
     subst (TSubst $ return $ M.fromList r) (return ty)
          
generalize :: Env -> Type -> Analysis TypeScheme
generalize env ty = 
  do let TSubst r = typeMap env
     env <- r
     let boundedVars   = M.keysSet env
         freeVars      = S.fromList $ ftv ty
         unboundedVars = freeVars S.\\ boundedVars
         
         freshNames = map (:[]) ['a'..'z'] ++ map (\n -> "t" ++ show n) [0..] 
         renameAssocs = zip (S.toList unboundedVars) freshNames
         renameMap = M.fromList renameAssocs

         renameVariables (TUnit f nm) = TUnit f nm
         renameVariables TBool = TBool
         renameVariables (TInt s b)  = TInt s b
         renameVariables (TVar n) = case M.lookup n renameMap of
                                         Just k  -> TVar k
                                         Nothing -> TVar n
         renameVariables (TArr f a b) = TArr f (renameVariables a) (renameVariables b)
         renameVariables (TProd f nm a b) = TProd f nm (renameVariables a) (renameVariables b)
         renameVariables (TSum f nm a b) = TSum f nm (renameVariables a) (renameVariables b)

         
     return $ Scheme (S.fromList $ map snd renameAssocs) (renameVariables ty)

     
liftedUnify :: Scale -> Scale -> Analysis SSubst
liftedUnify a b = lifter (unifyScales a b) where
  lifter (Left err) = throwError (CannotUnifyMeasurement err)
  lifter (Right r)  = return r

capture :: Type -> Env -> Env
capture r@(TVar nm) = nm ~> r
capture _ = error $ "capture: not implemented."

-- |Decides weither Lets should be interpreted as local declarations belonging to a function
--  or as a list of top-level declarations.
data ExportType 
  = Local 
  | Global 
  
-- |Runs the Algorithm W inference for Types and generates constraints later used 
--  by Control Flow analysis and Measure Analysis. The main part of the algorithm is 
--  adapted from the book, extended in the obvious way to handle construction and
--  destruction of sum and product types.
analyse :: ExportType -> Expr -> Env -> Analysis (Type, Env, Set Constraint)
analyse export exp env = case exp of
  Lit l           -> return ( typeOf l
                            , mempty
                            , empty
                            )

  Var x           -> do tyEnv <- getTSubst (typeMap env)
                        s <- (tyEnv $* x) $ throwError (UnboundVariable x)
                        v <- instantiate s
                 
                        return ( v
                               , mempty
                               , empty
                               )

  Abs pi x e      -> do a_x <- fresh
                        b_0 <- fresh

                        (t0, s0, c0) <- analyse export e . (x ~> a_x) . (capture a_x) $ env
                        
                        a_x <- substM s0 a_x
                        
                        return ( TArr b_0 a_x t0
                               , s0
                               , c0 `union` simpleFlow b_0 pi
                               )

  Fix pi f x e    -> do a_x <- fresh
                        a_0 <- fresh
                        b_0 <- fresh

                        (t0, s0, c0) <- analyse export e . (f ~> TArr b_0 a_x a_0) . (x ~> a_x) . (capture a_x) $ env
                        
                        a_0 <- substM s0 a_0
                        
                        (s1, c1) <- t0 `unify` a_0

                        let b_1 = subst (s1 <> s0) b_0
                        
                        t0  <- substM s1 t0
                        a_x <- substM (s1 <> s0) a_x
                        
                        return ( TArr b_1 a_x t0
                               , s1 <> s0
                               , subst s1 c0 `union` 
                                          c1 `union` simpleFlow b_1 pi
                               )


  App f e         -> do (t1, s1, c1) <- analyse export f $ env
                        (t2, s2, c2) <- analyse export e . subst s1 $ env

                        a <- fresh
                        b <- fresh

                        t1 <- substM s2 t1
                        
                        (s3, c3) <- t1 `unify` TArr b t2 a

                        a <- substM s3 a
                        
                        return (  a
                               , s3 <> s2 <> s1
                               , subst (s3 <> s2) c1 `union`
                                 subst  s3        c2 `union`
                                                  c3
                               )

                               
  Let es e2    -> do let es' = es >>~ \(x, e1) -> \env ->
                                 do (t1, s1, c1) <- analyse Local e1 $ env
    
                                    t1 <- generalize env t1
                                    let s1' = s1 { typeMap = singleton (x, t1) }
                                  
                                    return $ (s1', c1)
                   
                     (s1, c1) <- flip3 foldlM (mempty, S.empty) es' $ \(s1, c1) f -> 
                           do (s2, c2) <- f . subst s1 $ env
                              return $ (s2 <> s1, c1 `union` c2)
                              
                     let shadowedEnv = env { typeMap = TSubst $ do env <- getTSubst . typeMap $ env
                                                                   s1  <- getTSubst . typeMap $ s1
                                                                   return  $ s1 `M.union` env
                                       }
                                       
                     (t2, s2, c2) <- analyse Local e2 $ shadowedEnv

                     let finalSubst = case export of
                                        Local  -> s2
                                        Global -> s1
                     
                     return ( t2
                            , finalSubst
                            , subst s2 c1 `union` c2
                            )

  -- |If-Then-Else

  ITE b e1 e2     -> do (t0, s0, c0) <- analyse export b $ env;
                        (t1, s1, c1) <- analyse export e1 . subst s0 $ env
                        (t2, s2, c2) <- analyse export e2 . subst (s1 <> s0) $ env

                        t0 <- substM (s2 <> s1) t0
                        
                        (    s3, c3) <- t0 `unify` TBool
                        
                        t1 <- substM (s3 <> s2) t1
                        t2 <- substM  s3        t2

                        (    s4, c4) <- t1 `unify` t2;

                        t2 <- substM  s4        t2
                        
                        return ( t2 
                               , s4 <> s3 <> s2 <> s1
                               , subst (s4 <> s3 <> s2 <> s1) c0 `union`
                                 subst (s4 <> s3 <> s2)       c1 `union`
                                 subst (s4 <> s3)             c2 `union`
                                 subst  s4                    c3 `union`
                                                              c4
                               )

  -- |Unit Constructor                               
  Con pi nm Unit         -> do b_0 <- fresh

                               return ( TUnit b_0 nm
                                      , mempty
                                      , simpleFlow b_0 pi
                                      )
  -- |Product Constructor                                      
  Con pi nm (Prod x y)   -> do (t1, s1, c1) <- analyse export x $ env
                               (t2, s2, c2) <- analyse export y . subst s1 $ env

                               b_0 <- fresh

                               t1 <- substM s2 t1
                               
                               return ( TProd b_0 nm t1 t2
                                      , s2 <> s1
                                      , subst s2 c1 `union`
                                                 c2 `union` simpleFlow b_0 pi
                                      )
  -- |Left Sum Constructor                                      
  Con pi nm (Sum L t)   -> do (t1, s1, c1) <- analyse export t $ env
                              t2 <- fresh

                              b_0 <- fresh

                              return ( TSum b_0 nm t1 t2
                                      , s1
                                      , c1 `union` simpleFlow b_0 pi
                                      )
  -- |Right Sum Constructor                                      
  Con pi nm (Sum R t)   -> do (t2, s1, c1) <- analyse export t $ env
                              t1 <- fresh

                              b_0 <- fresh

                              return ( TSum b_0 nm t1 t2
                                      , s1
                                      , c1 `union` simpleFlow b_0 pi
                                      )

  -- |Unit Destruction                                                                            
  Des nm e1 (UnUnit e2)     -> do (t1, s1, c1) <- analyse export e1 $ env

                                  b_0 <- fresh

                                  (    s2, c2) <- t1 `unify` TUnit b_0 nm

                                  (t3, s3, c3) <- analyse export e2 . subst (s2 <> s1) $ env

                                  return ( t3
                                         , s3 <> s2 <> s1
                                         , subst (s3 <> s2) c1 `union`
                                           subst  s3        c2 `union` 
                                                            c3
                                         )
  -- |Product Destruction
  Des nm e1 (UnProd x y e2)   -> do (t1, s1, c1) <- analyse export e1 $ env

                                    a_x <- fresh
                                    a_y <- fresh

                                    b_0 <- fresh

                                    (    s2, c2) <- t1 `unify` TProd b_0 nm a_x a_y
                                    (t3, s3, c3) <- analyse export e2 . (y ~> a_y) . (x ~> a_x) . subst (s2 <> s1) $ env

                                    return ( t3
                                           , s3 <> s2 <> s1
                                           , subst (s3 <> s2) c1 `union`
                                             subst  s3        c2 `union`
                                                              c3
                                           )

  -- |Sum Destruction                                           
  Des nm e1 (UnSum (x, ex) (y, ey))     -> do (t1, s1, c1) <- analyse export e1 $ env

                                              a_x <- fresh
                                              a_y <- fresh

                                              b_0 <- fresh

                                              (    s2, c2) <- t1 `unify` TSum b_0 nm a_x a_y

                                              (tx, s3, c3) <- analyse export ex . (x ~> a_x) . subst (s2 <> s1) $ env
                                              (ty, s4, c4) <- analyse export ey . (y ~> a_y) . subst (s3 <> s2 <> s1) $ env

                                              (    s5, c5) <- tx `unify` ty

                                              tx <- substM s5 tx
                                              
                                              return ( tx
                                                     , s5 <> s4 <> s3 <> s2 <> s1
                                                     , subst (s5 <> s4 <> s3 <> s2) c1 `union`
                                                       subst (s5 <> s4 <> s3)       c2 `union`
                                                       subst (s5 <> s4)             c3 `union`
                                                       subst  s5                    c4 `union`
                                                                                    c5
                                                     )

                                                     
  -- |Binary Operators                                                     
  Oper op x y -> do rx <- fresh
                    bx <- fresh

                    ry <- fresh
                    by <- fresh

                    (t1, s1, c1) <- analyse export x $ env
                    (    s2, c2) <- t1 `unify` TInt rx bx


                    (t3, s3, c3) <- analyse export y . subst (s2 <> s1) $ env
                    (    s4, c4) <- t3 `unify` TInt ry by
                    
                    rz <- fresh
                    bz <- fresh
            
                    -- |Generate the Scale and Base constraints corresponding to the operations
                    let c0 = case op of
                          Add -> scaleEquality [rx, ry, rz]            `union` selectBase   (bx, by) bz
                          Sub -> scaleEquality [rx, ry, rz]            `union` preserveBase (bx, by) bz
                          Mul -> scaleEquality [rz, (SMul rx ry)]      `union` baseEquality [bx, by, bz, BNil]
                          Div -> scaleEquality [rz, SMul rx (SInv ry)] `union` baseEquality [bx, by, bz, BNil]
                          

                    return ( TInt rz bz
                           , s4 <> s3 <> s2 <> s1
                           , subst (s4 <> s3 <> s2 <> s1) c0 `union`
                             subst (s4 <> s3 <> s2)       c1 `union`
                             subst (s4 <> s3)             c2 `union`
                             subst  s4                    c3 `union`
                             c4
                           )

-- * Unifications

-- |Unification as per Robinson's unification algorithm. Equality constraints are 
--  generated for annotated types that need to be resolved later. No additional
--  failure paths are introduced compared to bare W unification.
unify :: Type -> Type -> Analysis (Env, Set Constraint)
unify TBool TBool = return $ mempty
unify (TInt r1 b1) (TInt r2 b2) = return $ (mempty, baseEquality [b1, b2] `S.union` scaleEquality [r1, r2])
                            
unify (TArr p1 a1 b1) (TArr p2 a2 b2)
                  = do let c0 = flowEquality p1 p2
                       (s1, c1) <- a1 `unify` a2
                       b1 <- substM s1 b1
                       b2 <- substM s1 b2
                       (s2, c2) <- b1 `unify` b2
                       return (s2 <> s1, c0 `union` c1 `union` c2)
unify t1@(TProd p1 n1 x1 y1) t2@(TProd p2 n2 x2 y2)
                  = if n1 == n2
                    then do let c0 = flowEquality p1 p2
                            (s1, c1) <- x1 `unify` x2;
                            y1' <- subst s1 (return y1)
                            y2' <- subst s1 (return y2)
                            (s2, c2) <- y1 `unify` y2
                            return (s2 <> s1, c0 `union` c1 `union` c2)
                    else do throwError (CannotUnify t1 t2)
unify t1@(TSum p1 n1 x1 y1) t2@(TSum p2 n2 x2 y2)
                  = if n1 == n2
                    then do let c0 = flowEquality p1 p2
                            (s1, c1) <- x1 `unify` x2;
                            y1' <- subst s1 (return y1)
                            y2' <- subst s1 (return y2)
                            (s2, c2) <- y1 `unify` y2
                            return (s2 <> s1, c0 `union` c1 `union` c2)
                    else do throwError (CannotUnify t1 t2)
unify t1@(TUnit p1 n1) t2@(TUnit p2 n2)
                  = if n1 == n2
                    then do let c0 = flowEquality p1 p2
                            return $ (mempty, c0)
                    else do throwError (CannotUnify t1 t2)

unify (TVar t1) t2@(TVar _) = return $ (singleton (t1, t2), empty)
unify t1 (TVar t2) | t2 `occurs` t1 = throwError (OccursCheck t2 t1)
                   | otherwise      = return $ (singleton (t2, t1), empty)
unify (TVar t1) t2 | t1 `occurs` t2 = throwError (OccursCheck t1 t2)
                   | otherwise      = return $ (singleton (t1, t2), empty)
unify t1 t2 = throwError (CannotUnify t1 t2)
        
occurs :: TVar -> Type -> Bool
occurs n t = n `elem` ftv t 

                           
-- * Fresh Names

-- |Provides an infinite stream of names to things in the @Analysis@ monad,
--  reducing it to just an @Either@ value containing perhaps a TypeError.
withFreshVars :: Analysis a -> Either TypeError a
withFreshVars x = evalSupply (evalSupplyT (runErrorT x) freshAVars) freshTVars
  where
  freshAVars = fmap show [0..]
  freshTVars = letters ++ numbers
    where
    letters = fmap (: []) ['a'..'z']
    numbers = fmap (('t' :) . show) [0..]

--type Analysis a = ErrorT TypeError (SupplyT FVar (Supply TVar)) a
     {-
-- |Refreshes all entries in a type environment.
refreshAll :: Either TypeError (Env, Program, Set Constraint) -> Either TypeError (Env, Program, Set Constraint)
refreshAll env = do (env, p, c) <- env;
                    m <- mapM (withFreshVars . refresh) . getTSubst . typeMap $ env
                    return ( env { 
                               typeMap = TSubst (return m) 
                             }
                           , p
                           , c
                           )
                           -}
-- |Replaces every type variable with a fresh one.
refresh :: TypeScheme -> Analysis TypeScheme
refresh t1 = do subs <- forM (ftv t1) $ \a ->
                          do b <- (fresh :: Analysis Type)
                             return $ singleton (a, Type b)
                subst (mconcat subs :: Env) (return t1)
                
class Fresh t where
  fresh :: Analysis t

instance Fresh Type where
  fresh = do n <- lift (lift supply)
             return $ TVar n

instance Fresh Flow where
  fresh = fmap FVar $ lift supply

instance Fresh Scale where
  fresh = fmap SVar $ lift supply

instance Fresh Base where
  fresh = fmap BVar $ lift supply

-- * Pretty Printing
  
-- |Data type used to specify which annotations should be printed as part 
--  of the final output.
data Annotations 
  = FlowInformation
  | MeasureInformation
  | ProgramPoints
    deriving (Ord, Eq, Show)

type PrintAnnotations = Set Annotations

-- |Extract relevant information from the annotation description.

printProgramPoints :: PrintAnnotations -> Bool
printProgramPoints = S.member ProgramPoints

printFlowInfo :: PrintAnnotations -> Bool
printFlowInfo = S.member FlowInformation

printMeasureInfo :: PrintAnnotations -> Bool
printMeasureInfo = S.member MeasureInformation

setAnnotations :: [Annotations] -> PrintAnnotations
setAnnotations = S.fromList

-- |Pretty print the whole program, using the environment for type information. The 
--  PrintAnnotation parameter is used to find-tune the printing of type annotations.
printProgram :: PrintAnnotations -> Program -> Map TVar TypeScheme -> String
printProgram cp (Prog p) env = 
  let funcType (Decl nm e) = case M.lookup nm env of
                               Just r  -> nm ++ " :: " ++ (showScheme cp r)
                               Nothing -> error $ "printProgram: no matching type found for function \"" ++ nm ++ "\""
      funcBody = showDecl (printProgramPoints cp)
      prefix = "{\n"
      suffix = "}"
      
      printer x xs = "  " ++ funcType x ++ "\n  " ++ funcBody x ++ "\n\n" ++ xs 
      
  in prefix ++ foldr printer "" p ++ suffix
  
showScheme :: PrintAnnotations -> TypeScheme -> String
showScheme ann (Type ty) = showType ann ty
showScheme ann (Scheme bnds ty) = forallString ++ showType ann ty where
  forallString = if not (S.null bnds)
                    then "forall " ++ (concat . L.intersperse " " . S.toList $ bnds) ++ " . "
                    else ""
-- |Pretty print a given type. The PrintAnnotation parameter is used to find-tune
--  the printing of type annotations.
showType :: PrintAnnotations -> Type -> String
showType cp =
  let printAnn (FVar s) = if printFlowInfo cp 
                             then "{" ++ s ++ "}" 
                             else ""
      printAnn (FSet l) = if printFlowInfo cp 
                             then "[" ++ (L.foldr1 (\x xs -> x ++ ", " ++ xs) . S.toList $ l) ++ "]" 
                             else "" where

      showType ty = case ty of
        TBool -> "Bool"
        TInt s b -> "Integer" ++ showScaleBase where
          showScaleBase = if printMeasureInfo cp
                             then if s == SNil
                                     then "" else
                                  if b == BNil
                                     then case s of
                                             SVar p -> "{" ++ p ++ "}"
                                             _      -> "[" ++ show (simplify s) ++ "]"
                                     else case (s, b) of
                                             (SVar p, BVar q) -> "{" ++ p ++ "@" ++ q ++ "}"
                                             (SVar p,      _) -> "{" ++ p ++ "}@[" ++ show b ++ "]"
                                             (_     , BVar q) -> "[" ++ show s ++ "]@{" ++ q ++ "}"
                                             (_     ,      _) -> "[" ++ show s ++ "@" ++ show b ++ "]"
                                             
                                             
                             else ""      
        TVar n -> n
        TArr  v a b -> printf "%s -%s> %s" (wrap a) (printAnn v) (wrap b) where
            wrap ty@(TArr _ _ _) = printf "(%s)" (showType ty)
            wrap ty              = showType ty
        TProd v nm a b -> printf "%s%s(%s, %s)" nm (printAnn v) (wrap a) (wrap b) where
            wrap ty@(TProd _ _ _ _) = printf "(%s)" (showType ty)
            wrap ty@(TSum  _ _ _ _) = printf "(%s)" (showType ty)
            wrap ty@(TArr _ _ _)    = printf "(%s)" (showType ty)
            wrap ty                 = showType ty
        TSum v nm a b -> printf "%s%s %s %s" nm (printAnn v) (wrap a) (wrap b) where
            wrap ty@(TProd _ _ _ _) = printf "(%s)" (showType ty)
            wrap ty@(TSum  _ _ _ _) = printf "(%s)" (showType ty)
            wrap ty@(TArr _ _ _)    = printf "(%s)" (showType ty)
            wrap ty                 = showType ty
        TUnit v nm -> printf "%s%s()" nm (printAnn v)
  in showType

instance Error TypeError where
  noMsg       = OtherError "no message"
  strMsg msg  = OtherError msg

 
instance Show Type where
  show = showType mempty

instance Show TypeScheme where
  show (Type ty) = showType mempty ty
  show (Scheme binders ty) = "forall " ++ (concat . L.intersperse " " . S.toList $ binders) ++ " . " ++ showType mempty ty

  
instance Show TypeError where
  show (CannotDestruct   t) = printf "Cannot deconstruct expression of type %s" (show t)
  show (PatternError   a b) = printf "Cannot match pattern %s with %s" a b
  show (UnboundVariable  n) = printf "Unknown variable %s" n
  show (OccursCheck    n t) = printf "Occurs check fails: %s occurs in %s" n (show t)
  show (CannotUnify    a b) = printf "Cannot unify %s with %s" (show a) (show b)
  show (CannotUnifyMeasurement err) =  show err 
  show (OtherError     msg) = msg


  
-- * Constraints

data Constraint
  = FlowConstraint  FlowConstraint
  | ScaleConstraint ScaleConstraint
  | BaseConstraint  BaseConstraint
    deriving (Eq, Ord, Show)

flowEquality :: Flow -> Flow -> Set Constraint
flowEquality a b = singleton $ FlowConstraint $ FlowEquality a b

-- |Constraint generated by the construction of a program point 
simpleFlow :: Flow -> Label -> Set Constraint
simpleFlow f l = singleton $ FlowConstraint $ FlowEquality f (FSet $ S.singleton l)


-- |Construct a Scale resp. Base Equality Constraint from a list of Scale resp. Base annotations. All 
--  annotations in the list will be unified post-W
scaleEquality :: [Scale] -> Set Constraint
scaleEquality = S.singleton . ScaleConstraint . ScaleEquality . S.fromList

baseEquality :: [Base] -> Set Constraint
baseEquality = S.singleton . BaseConstraint . BaseEquality . S.fromList

-- |Constraint generated by the addition of two measures
selectBase :: (Base, Base) -> Base -> Set Constraint
selectBase xy z = S.singleton $ BaseConstraint $ BaseSelection xy z

-- |Constraint generated by the subtraction of two measures
preserveBase :: (Base, Base) -> Base -> Set Constraint
preserveBase xy z = S.singleton $ BaseConstraint $ BasePreservation xy z

-- |Seperate the Flow Constraints from the rest of the Constraint set
extractFlowConstraints :: Set Constraint -> Set FlowConstraint
extractFlowConstraints = unionMap findFlows where
  findFlows (FlowConstraint r)      = S.singleton r
  findFlows _                       = S.empty

-- |Seperate the Scale Constraints from the rest of the Constraint set
extractScaleConstraints :: Set Constraint -> Set ScaleConstraint
extractScaleConstraints = unionMap findScales where
    findScales (ScaleConstraint ss) = S.singleton ss
    findScales _                    = S.empty

-- |Seperate the Base Constraints from the rest of the Constraint set
extractBaseConstraints :: Set Constraint -> Set BaseConstraint
extractBaseConstraints = unionMap findBases where
  findBases (BaseConstraint bs) = S.singleton bs
  findBases _                   = S.empty
                    
-- * Environments

newtype TSubst = TSubst { 
    getTSubst :: Analysis (Map TVar TypeScheme)
  } --deriving (Eq, Ord, Show)

strength :: Functor f => (a, f b) -> f (a, b)
strength (a, m) = fmap (a,) m
  
instance Subst TSubst TSubst where
  subst m@(TSubst t) (TSubst r) = TSubst $ do r <- r
                                              t <- t
                                              tyMap <- sequenceA . M.map (substM m) $ r
                                              return $ tyMap `M.union` t
                                              
instance Subst TSubst (Analysis TypeScheme) where
  subst m s = do r <- s
                 case r of
                   Type ty -> do ty' <- subst m (return ty)
                                 return $ Type ty'
                   Scheme bnds ty -> do let cleanEnv = TSubst . fmap (M.filterWithKey $ \k v -> not $ k `S.member` bnds) . getTSubst $ m
                                        ty <- substM cleanEnv ty
                                        return $ Scheme bnds ty 

instance Subst FSubst Type where 
  subst m TBool            = TBool
  subst m (TInt s b)       = TInt  s b
  subst m (TArr  f    a b) = flip3 TArr (subst m a) (subst m b) $ 
    case f of 
      FVar n -> M.findWithDefault f n $ getFSubst m
      _      -> f
  subst m (TProd f nm a b) = flip4 TProd nm (subst m a) (subst m b) $ 
    case f of 
      FVar n -> M.findWithDefault f n $ getFSubst m
      _      -> f
  subst m (TSum  f nm a b) = flip4 TSum  nm (subst m a) (subst m b) $ 
    case f of 
      FVar n -> M.findWithDefault f n $ getFSubst m
      _      -> f
  subst m (TUnit f nm)     = flip2 TUnit nm $ 
    case f of 
      FVar n -> M.findWithDefault f n $ getFSubst m
      _      -> f
  subst m v@(TVar _)       = v

instance Subst FSubst TypeScheme where
  subst m (Type ty) = Type (subst m ty)
  subst m (Scheme bnds ty) = Scheme bnds (subst m ty)
  
-- |Substitutes a type for a type variable in a type.
instance Subst SSubst Type where
  subst m TBool               = TBool
  subst m (TInt s b)          = flip TInt b $ case s of
                                     SVar n   -> M.findWithDefault s n $ getSSubst m
                                     SInv s   -> SInv (subst m s)
                                     SMul x y -> SMul (subst m x) (subst m y)
                                     _        -> s
  subst m (TArr  v    a b)    = TArr  v (subst m a) (subst m b)
  subst m (TProd v nm a b)    = TProd v nm (subst m a) (subst m b)
  subst m (TSum  v nm a b)    = TSum  v nm (subst m a) (subst m b)
  subst m (TUnit v nm)        = TUnit v nm
  subst m v@(TVar _)          = v

instance Subst SSubst TypeScheme where
  subst m (Type ty) = Type (subst m ty)
  subst m (Scheme bnds ty) = Scheme bnds (subst m ty)
  
instance Subst BSubst Type where
  subst m TBool               = TBool
  subst m (TInt s b)          = TInt  s $ case b of
                                               BVar n -> M.findWithDefault b n $ getBSubst m
                                               _      -> b
  subst m (TArr  v    a b)    = TArr  v (subst m a) (subst m b)
  subst m (TProd v nm a b)    = TProd v nm (subst m a) (subst m b)
  subst m (TSum  v nm a b)    = TSum  v nm (subst m a) (subst m b)
  subst m (TUnit v nm)        = TUnit v nm
  subst m v@(TVar _)          = v

instance Subst BSubst TypeScheme where
  subst m (Type ty) = Type (subst m ty)
  subst m (Scheme bnds ty) = Scheme bnds (subst m ty)
  
instance Subst FSubst TSubst where
  subst m (TSubst r) = TSubst $ do r <- r; return $ M.map (subst m) r
  
instance Subst SSubst TSubst where
  subst m (TSubst r) = TSubst $ do r <- r; return $ M.map (subst m) r

instance Subst BSubst TSubst where
  subst m (TSubst r) = TSubst $ do r <- r; return $ M.map (subst m) r
 
instance Monoid TSubst where
  s `mappend` t = TSubst $ do st <- getTSubst (subst s t) 
                              s' <- getTSubst s
                              return $ st `M.union` s' 
  mempty        = TSubst $ return M.empty
  
data Env = Env { 
    typeMap  :: TSubst          -- ^ Type substitutions used in W
  , flowMap  :: FSubst
  , scaleMap :: SSubst
  , baseMap  :: BSubst
  }

instance Subst TSubst (Analysis Type) where 
  subst m = join . fmap subst' where 
    subst' :: Type -> Analysis Type
    subst' f@(TVar n) = do env <- getTSubst m
                           instantiate (M.findWithDefault (Type f) n env)
    subst' r@ TBool     = return $ r
    subst' r@(TInt _ _) = return $ r

    subst' (TArr  f    a b) = do a' <- substM m a
                                 b' <- substM m b
                                 return $ TArr f a' b'
    subst' (TProd f nm a b) = do a' <- substM m a
                                 b' <- substM m b
                                 return $ TProd f nm a' b'
    subst' (TSum  f nm a b) = do a' <- substM m a
                                 b' <- substM m b
                                 return $ TSum  f nm a' b'
    subst' (TUnit f nm)     = return $ TUnit f nm

-- |Substitutes a type for a type variable in a type.


instance Subst Env (Analysis Type) where
  subst m = join . fmap subst' where
    subst' :: Type -> Analysis Type
    subst' TBool = return TBool
    subst' r@(TInt s b)     = do let s' = subst (scaleMap m) s
                                 let b' = subst (baseMap m) b
                                 return $ TInt s' b'
    subst' f@(TVar _)       = substM (typeMap m) f
    
    subst' (TArr  f    a b) = do let f' = subst (flowMap m) f
                                 a' <- substM m a
                                 b' <- substM m b
                                 return $ TArr f' a' b'
                                 
    subst' (TProd f nm a b) = do let f' = subst (flowMap m) f
                                 a' <- substM m a
                                 b' <- substM m b
                                 return $ TProd f' nm a' b'
    subst' (TSum  f nm a b) = do let f' = subst (flowMap m) f
                                 a' <- substM m a
                                 b' <- substM m b
                                 return $ TSum  f' nm a' b'
    subst' (TUnit f nm)     = do let f' = subst (flowMap m) f
                                 return $ TUnit f' nm
 
instance Subst Env TSubst where
  subst m = subst (baseMap m)
          . subst (scaleMap m)
          . subst (flowMap m)
          . subst (typeMap m)
  
instance Subst Env FSubst where
  subst m r = subst (flowMap m) r
instance Subst Env SSubst where
  subst m r = subst (scaleMap m) r
instance Subst Env BSubst where
  subst m r = subst (baseMap m) r

 
instance Subst Env (Analysis TypeScheme) where
  subst m d = 
    do d <- d
       case d of
          Type ty -> do ty <- substM m ty
                        return $ Type ty
          Scheme bnds ty -> do ty <- substM m ty
                               return $ Scheme bnds ty
instance Subst Env Env where
  subst m env = env { typeMap  = subst m (typeMap  env)
                    , flowMap  = subst m (flowMap  env)
                    , scaleMap = subst m (scaleMap env)
                    , baseMap  = subst m (baseMap  env)
                    }


--instance Subst TSubst Constraint where
--  subst m = id
  
instance Subst Env Constraint where
  subst m (FlowConstraint  fs) = FlowConstraint  $ subst m fs
  subst m (ScaleConstraint ss) = ScaleConstraint $ subst m ss
  subst m (BaseConstraint  ss) = BaseConstraint  $ subst m ss
  
instance Subst Env Flow where
  subst = subst . flowMap

instance Subst Env Scale where
  subst = subst . scaleMap

instance Subst Env Base where
  subst = subst . baseMap

instance Subst TSubst Env where
  subst s env = env { typeMap = subst s (typeMap env) }
  
instance Subst FSubst Env where
  subst s env = env { typeMap = subst s (typeMap env), flowMap = s <> flowMap env }
  
instance Subst SSubst Env where
  subst s env = env { typeMap = subst s (typeMap env), scaleMap = s <> scaleMap env }

instance Subst BSubst Env where
  subst s env = env { typeMap = subst s (typeMap env), baseMap = s <> baseMap env }

instance Monoid Env where                    
  -- |Substitutions can be chained by first recursively substituting the left substitution
  --  over the right environment then unioning with the left invironment
  p `mappend` q = 
    Env { 
      typeMap  = typeMap  p <> typeMap  q,
      flowMap  = flowMap  p <> flowMap  q,
      scaleMap = scaleMap p <> scaleMap q,
      baseMap  = baseMap  p <> baseMap  q
    }
      
  mempty = 
    Env { 
      typeMap  = mempty, 
      flowMap  = mempty,
      scaleMap = mempty,
      baseMap  = mempty
    }

  
instance Subst FSubst Constraint where
  subst s (FlowConstraint c) = FlowConstraint $ subst s c
  subst s v                  = v
  
instance Subst SSubst Constraint where
  subst s (ScaleConstraint c) = ScaleConstraint $ subst s c
  subst s v                   = v
  
instance Subst BSubst Constraint where
  subst s (BaseConstraint c) = BaseConstraint $ subst s c
  subst s v                  = v
 
 
 
-- * Singleton Constructors
instance Singleton TSubst (Name, TypeScheme) where
  singleton (k, a) = TSubst . return . M.fromList $ [(k, a)] 

instance Singleton Env (TVar, Type) where
  singleton (k, a) = mempty { typeMap = TSubst . return $ M.singleton k (Type a) } 

instance Singleton Env (TVar, TypeScheme) where
  singleton (k, a) = mempty { typeMap = TSubst . return $ M.singleton k a } 
  
instance Singleton Env (FVar, Flow) where
  singleton (k, a) = mempty { flowMap = FSubst $ M.singleton k a }

instance Singleton Env (SVar, Scale) where
  singleton (k, a) = mempty { scaleMap = SSubst $ M.singleton k a }

instance Singleton Env (BVar, Base) where
  singleton (k, a) = mempty { baseMap = BSubst $ M.singleton k a }
