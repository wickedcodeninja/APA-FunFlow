-- (C) 2013 Pepijn Kokke & Wout Elsinghorst

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses.Measure where

import FUN.Analyses.Utils

import Debug.Trace

import Data.Functor
import Data.Monoid
import Data.List

import Data.Map (Map)
import Data.Set (Set)

import Control.Applicative

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Foldable as F

type SVar = String
type SCon = String
type BVar = String
type BCon = String

data Scale
  = SVar SVar        -- |Variable measure
  | SCon SCon        -- |Concrete measure       
  | SNil             -- |1
  | SMul Scale Scale -- |s*s
  | SInv Scale       -- |1/s
  deriving (Eq, Ord)

data Base
  = BVar BVar        -- |Variable Base
  | BCon BCon        -- |Concrete Base
  | BNil             -- |No Base
  deriving (Eq, Ord)

instance Show Scale where
  show SNil               = "Unit"
  show (SVar v)           = v
  show (SCon c)           = c 
                                              
  --show (SMul SNil b)      = show b
  show (SMul a (SInv b))  = "(" ++ show a ++ "/" ++ show b ++ ")"
  show (SMul (SInv a) b)  = "(" ++ show b ++ "/" ++ show a ++ ")"
  show (SMul a b)         = "(" ++ show a ++ "*" ++ show b ++ ")"
  show (SInv a)           = "(1/" ++ show a ++ ")"
   
data MeasureError = MeasuresDontUnify String

instance Show MeasureError where
  show (MeasuresDontUnify str) = str

 
throwMeasureError :: MeasureError -> Either MeasureError SSubst
throwMeasureError = Left
 
unifyScales :: Scale -> Scale -> Either MeasureError SSubst
unifyScales p q = unifyOne $ SMul p (SInv q)
  
data Term = Variable SVar | Concrete SCon
  deriving (Eq, Show)
  
instance Ord Term where
  Variable _ `compare` Concrete _ = LT
  Concrete _ `compare` Variable _ = GT
  Variable p `compare` Variable q = p `compare` q
  Concrete p `compare` Concrete q = p `compare` q
  
linearize :: Scale -> Map Term Integer
linearize = M.filter (/= 0) . linearize' where
  linearize' SNil = mempty
  linearize' (SVar v) = M.fromList [(Variable v, 1)]
  linearize' (SCon c) = M.fromList [(Concrete c, 1)]
  linearize' (SMul a b) = M.unionWith (+) (linearize a) (linearize b)
  linearize' (SInv s) = M.map negate (linearize s)

reconstruct :: Map Term Integer -> Scale
reconstruct = fixer . M.toList where
  noob (Variable v, k) = case k `compare` 0 of
                              GT -> genericReplicate k (SVar v)
                              EQ -> []
                              LT -> genericReplicate (negate k) (SInv $ SVar v)
  noob (Concrete c, k) = case k `compare` 0 of
                              GT -> genericReplicate k (SCon c)
                              EQ -> []
                              LT -> genericReplicate (negate k) (SInv $ SCon c)
  
  fixer [] = SNil
  fixer xs = foldr1 SMul (xs >>= noob)
  
reconstruct' :: ([(SVar, Integer)], [(SCon, Integer)]) -> Scale
reconstruct' (varList, conList) = reconstruct (varList' `M.union` conList') where
  varList' = M.fromList $ map (\(a, k) -> (Variable a, k)) varList
  conList' = M.fromList $ map (\(c, k) -> (Concrete c, k)) conList
  
 
  
collect :: Scale -> [Term]
collect SNil = []
collect (SVar a) = [Variable a]
collect (SCon c) = [Concrete c]
collect (SMul a b) = collect a ++ collect b
collect (SInv a) = collect a      
  
simplify :: Scale -> Scale
simplify = reconstruct . linearize
  
normalize :: Scale -> ([Either SVar (SVar, Integer)], [(SCon, Integer)])
normalize s = (varList, conList) where
  sortedList = sort (nub $ collect s)
  varList = sortedList >>= \g -> case g of  
                                        Variable v -> let k = expScale s $ Variable v
                                                      in if k /= 0 
                                                            then [Right(v, k)]
                                                            else [Left v]
                                        Concrete _ -> []
  conList = sortedList >>= \g -> case g of  
                                        Concrete c -> let k = expScale s $ Concrete c
                                                      in if k /= 0 
                                                            then [(c, k)]
                                                            else []
                                        Variable _ -> []

                                   
scalify :: (String -> Scale) -> [(String, Integer)] -> Scale
scalify maker = flip foldr SNil $ \(v, k) xs ->
  case k `compare` 0 of
       GT -> SMul xs $ foldr1 SMul $ L.genericReplicate k (maker v)
       EQ -> xs
       LT -> SMul xs $ foldr1 SMul $ L.genericReplicate (negate k) (SInv (maker v))

expScale :: Scale -> Term -> Integer
expScale SNil       w = 0
expScale (SMul a b) w = expScale a w + expScale b w
expScale (SInv u)   w = negate (expScale u w)
expScale (SVar a)   (Variable w) = if a == w then 1 else 0
expScale (SVar a)   (Concrete w) = 0
expScale (SCon c)   (Variable w) = 0
expScale (SCon c)   (Concrete w) = if c == w then 1 else 0

       
unifyOne :: Scale -> Either MeasureError SSubst
unifyOne p =
  do let p'@(mixedVars, normCons) = normalize p

     let normVars = mixedVars >>= fixer where
           fixer (Left err) = []
           fixer (Right a)  = [a]
  
         badVars = mixedVars >>= fixer where
           fixer (Left a) = [(a, SNil)]
           fixer (Right a)  = []
         s0 = SSubst $ M.fromList badVars
     case (normVars, normCons) of
        ([]      , []) -> return mempty
        ([]      , rest) -> throwMeasureError $ MeasuresDontUnify $ "Can't solve equality " ++ show (reconstruct' ([], rest)) ++ " ~ " ++ "1"
        ([(v, x)], rest) -> let dividesThemAll = and . map (\(c, k) -> k `rem` x == 0) $ normCons
                            in if dividesThemAll
                                 then return $ singleton (v, scalify SCon . map (\(c, k) -> (c, negate $ k `div` x) ) $ normCons)
                                 else throwMeasureError $ MeasuresDontUnify $ "Equation not congruent. Equality " ++ show p ++ " ~ " ++ "1 not solvable"
        ((v, x):vs, cs) -> do let s1v = map (\(c, k) -> (Variable c, negate $ k `div` x) ) $ vs
                                  s1c = map (\(c, k) -> (Concrete c, negate $ k `div` x) ) $ cs
                                  s1t = M.fromList $ [(Variable v, 1)] ++ s1v ++ s1c
                                  s1 =  singleton $ (v, reconstruct s1t)
                                  reduced = (subst s1 p)
                              s2 <- unifyOne reduced
                              return $ s2 <> s1
       
instance Solver ScaleConstraint SSubst where
  solveConstraints = solveScaleConstraints
       
pick :: Int -> [a] -> [[a]]
pick 0 _ = [[]]
pick _ [] = []
pick n (x : xs) = map (x :) (pick (n - 1) xs) ++ pick n xs
     

setJoin :: Ord a => Set (Set a) -> Set a
setJoin = (>>>= id)
         
solveScaleConstraints :: SSubst -> Set ScaleConstraint -> (SSubst, Set ScaleConstraint)
solveScaleConstraints s0 c0 = 
  let binaryPairs    = S.toList . setJoin . S.map (\(ScaleEquality r) -> S.fromList . map (\[a, b] -> (a, b)) . pick 2 . S.toList $ r) $ c0
      singletonPairs = S.toList . setJoin . flip S.map c0 $ \(ScaleEquality r) -> if S.size r == 1 
                                                                            then case S.toList r of 
                                                                                      [x] -> S.singleton (x, SNil)
                                                  
                                                                            else S.empty
      
      loop :: SSubst -> [(Scale, Scale)] -> (SSubst, [Either (MeasureError, (Scale, Scale)) (Scale, Scale)])
      loop s0 [] = (s0, [])
      loop s0 (r@(a, b) : xs) = case unifyScales (subst s0 a) (subst s0 b) of
                                  Left err -> case loop s0 xs of
                                                   (sX, rest) -> (sX, (Left (err, r) ) : rest)
                                  Right s1 -> case loop (s1 <> s0) xs of 
                                                   (sX, rest) -> (sX, (Right $ apply s1 r) : rest) 
        where
                                    apply s (a, b) = (subst s a, subst s b)
      
      (s1, flattenedPairs) = loop s0 (binaryPairs) 
      
      errorPairs = flattenedPairs >>= filter where -- ignore for now..
        filter (Left (err, r)) = [r]
        filter (Right r)  = []
      goodPairs = flattenedPairs >>= filter where
        filter (Left err) = []
        filter (Right r)  = [r]
        
      order (SVar a, b) = [(a, b)]
      order (a, SVar b) = [(b, a)]
      order x@(a, b) = [ ]
      
      s2 = SSubst $ M.fromList . concatMap (order) $ goodPairs
  
      totalSub = s2 <> s1 <> s0
  
      maker (ScaleEquality r) = 
        let simplified = S.map (simplify) r
            isTrivial [ ] = True  -- Empty constraint set
            isTrivial [r] = True  -- Single constraint, corresponding to identities p == p
            isTrivial _   = False -- Non-trivial equality
            
        in if isTrivial (S.toList simplified)
              then S.empty
              else S.singleton $ ScaleEquality $ simplified

              
  
      c1 = (subst totalSub c0) >>>= maker
          
          
  in (totalSub, c1)
       
instance Show Base where
  show BNil     = "None"
  show (BVar v) = "[" ++ v ++ "]"
  show (BCon c) = c

-- * Constraints
  
data ScaleConstraint
  = ScaleEquality (Set Scale)
  deriving (Eq, Ord)
     
instance Show ScaleConstraint where
  show (ScaleEquality ss) = "equality: " ++ (foldr1 (\x xs -> x ++ " ~ " ++ xs) . map show . S.toList $ ss)
  
data BaseConstraint 
  = BaseEquality (Set Base)             -- |All Bases should unify to the same Base
  | BasePreservation (Base, Base) Base  -- |Generated by addition, see book
  | BaseSelection (Base, Base) Base     -- |Generated by subtraction, see book
  deriving (Eq, Ord)
    
-- |Print the semantics of the corresponding constraint. 
instance Show BaseConstraint where
  show (BaseEquality bs)
    = "equality: " ++ (foldr1 (\x xs -> x ++ " ~ " ++ xs) . map show . S.toList $ bs) 
  show (BasePreservation (x, y) z)
    = "preservation: " ++ show z ++ " = if " ++ show y ++ " = none then " ++ show x 
                                 ++  "; if " ++ show x ++ " = " ++ show y ++ "then none" 
                                 ++  "; else undefined"
  show (BaseSelection (x, y) z)
    = "selection: " ++ show z ++ " = if " ++ show y ++ " = none then " ++ show x
                              ++  "; if " ++ show x ++ " = none then " ++ show y
                              ++  "; else error"


-- |Number of times to repeat the various algorithms which have no guaranteed fixed point.
iterationCount :: Int
iterationCount = 8
                              
-- |Solve Base constraints. The equality case is the same as in the Scale case.
solveBaseConstraints :: BSubst -> Set BaseConstraint -> (BSubst, Set BaseConstraint)
solveBaseConstraints _ = loop iterationCount mempty where
  loop 0 s0 c0 = (s0, removeSolved c0)
  loop n s0 c0 = 
    let (s1, c1) = solveBaseEquality . unionMap unpackEquality $ c0
        
        (s2, c2) = solveBaseSelection . unionMap unpackSelection $ subst s1 c0
      
        (s3, c3) = solveBasePreservation . unionMap unpackPreservation $ subst (s2 <> s1) c0
                
    in if s1 == mempty &&
          s2 == mempty &&
          s3 == mempty
          then (s0, removeSolved c0)
          else loop (n-1) (s3 <> s2 <> s1 <> s0) (  S.map packEquality     c1
                                                 <> S.map packSelection    c2
                                                 <> S.map packPreservation c3
                                                 )
                                                 
  removeSolved = unionMap (\r -> case r of 
                                   BaseEquality t -> if S.size t == 0 || 
                                                        S.size t == 1 
                                                        then mempty 
                                                        else S.singleton $ BaseEquality t
                
                                   _              -> S.singleton r
                          )
                                              
  unpackEquality  (BaseEquality gr) = singleton gr
  unpackEquality _                  = S.empty
  packEquality = BaseEquality
  
  unpackSelection (BaseSelection (x, y) z) = singleton (x, y, z)
  unpackSelection _                        = S.empty
  packSelection (x, y, z) = BaseSelection (x, y) z
  
  unpackPreservation (BasePreservation (x, y) z) = singleton (x, y, z)
  unpackPreservation _                           = S.empty
  packPreservation (x, y, z) = BasePreservation (x, y) z


instance Solver BaseConstraint BSubst where
  solveConstraints = solveBaseConstraints

type BaseSelection = (Base, Base, Base)
  
-- |Constraints added by addition of two vagriables  
solveBaseSelection :: Set BaseSelection -> (BSubst, Set BaseSelection)
solveBaseSelection = F.foldMap solver where
  solver r@(x, y, BVar z) = if x == BNil
                               then (singleton (z, y), mempty) 
                               else
                            if y == BNil
                               then (singleton (z, x), mempty) 
                               else (mempty, S.singleton r)
  solver r@(BNil, y, z) = case (y, z) of
                            (BVar a,  b) -> (singleton (a, b), mempty)
                            (a,  BVar b) -> (singleton (b, a), mempty)
                            (BNil, BNil) -> (mempty, mempty)
                            (_,       _) -> (mempty, S.singleton r)
  solver r@(x, BNil, z) = case (x, z) of
                            (BVar a,  b) -> (singleton (a, b), mempty)
                            (a,  BVar b) -> (singleton (b, a), mempty)
                            (BNil, BNil) -> (mempty, mempty)
                            (_,       _) -> (mempty, S.singleton r)        

                            
type BasePreservation = (Base, Base, Base)
                                    
-- |Constraints added by subtraction of two variables  
solveBasePreservation :: Set BasePreservation -> (BSubst, Set BasePreservation)
solveBasePreservation = F.foldMap solver where
  solver r@(x, y, BVar z) = if y == BNil
                               then (singleton (z, x), mempty) 
                               else
                            if x == y
                               then (singleton (z, BNil), mempty) 
                               else (mempty, S.singleton r) 
  solver r@(x, BNil, z) = case (x, z) of
                            (BVar a, b) -> (singleton (a, b), mempty)
                            (a, BVar b) -> (singleton (b, a), mempty)
                            (_,      _) -> (mempty, S.singleton r)        

type BaseEquality = Set Base
                           
                          
-- |See @solveScaleEquality for details
solveBaseEquality:: Set BaseEquality -> (BSubst, Set BaseEquality)
solveBaseEquality = loop mempty where
  loop s0 c0 =
    let s1 = F.foldMap solveCons $ subst s0 c0
    in if s1 == mempty
          then (s0, c0)
          else loop (s1 <> s0) (subst s1 c0)
   
  solveCons cs = withSingle (single cons) where
    list = S.toList cs
    
    cons = getBCons list
    vars = getBVars list
    
    single [     ] = case vars of
                          [ ] -> Nothing
                          [x] -> Nothing
                          (x:y:[]) -> Just $ BVar x
    single [  x  ] = Just $ x
    single (x:y:_) = Nothing
    
    withSingle (Just  x) = foldr (\v m -> m <> singleton (v,x)) mempty vars
    withSingle (Nothing) = mempty
    
  getBCons = filter isBCon where
    isBCon  (BNil    ) = True
    isBCon  (BCon _  ) = True
    isBCon  (BVar _  ) = False
    
  getBVars = concatMap $ \t ->
    case t of BVar v -> [v]
              _      -> [ ]

              
printScaleInformation :: Set ScaleConstraint -> String
printScaleInformation m =
  let prefix = "{\n"
      content = S.foldr (\x xs -> "  " ++ show x ++ "\n" ++ xs) "" m
      suffix = "}"
  in prefix ++ content ++ suffix


printBaseInformation :: Set BaseConstraint -> String
printBaseInformation m = 
  let prefix = "{\n"
      content = S.foldr (\x xs -> "  " ++ show x ++ "\n" ++ xs) "" m
      suffix = "}"
  in prefix ++ content ++ suffix
  
-- * Scale Substitutions
    
instance (Subst e Scale) => Subst e ScaleConstraint where
  subst m (ScaleEquality ss) = ScaleEquality $ subst m ss

newtype SSubst = SSubst { 
    getSSubst :: Map SVar Scale
  } deriving (Eq, Ord, Show)

instance Subst SSubst SSubst where
  subst m (SSubst s) = SSubst (subst m s)
  
instance Subst SSubst Scale where
  subst m v@(SVar n)   = M.findWithDefault v n (getSSubst m)
  subst m v@(SCon _)   = v
  subst m   (SMul a b) = SMul (subst m a) (subst m b)
  subst m   (SInv a)   = SInv (subst m a)
  subst m v@_          = v
   
instance Monoid SSubst where
  s `mappend` t = SSubst $ let r = getSSubst (subst s t) `M.union` getSSubst s
                           in M.map simplify r
  mempty        = SSubst $ M.empty
                
instance Singleton SSubst (SVar,Scale) where
  singleton (k,a) = SSubst (M.singleton k a)
  
-- * Base Substitutions
  
instance (Subst e Base) => Subst e BaseConstraint where
  subst m (BaseEquality ss)           = BaseEquality $ subst m ss
  subst m (BasePreservation (x, y) z) = BasePreservation (subst m x, subst m y) (subst m z)
  subst m (BaseSelection (x, y) z)    = BaseSelection (subst m x, subst m y) (subst m z)

newtype BSubst = BSubst { 
  getBSubst :: Map BVar Base
  } deriving (Eq, Ord, Show)

instance Subst BSubst BSubst where
  subst m (BSubst s) = BSubst (subst m s)
  
instance Subst BSubst Base where
  subst m v@(BVar n) = M.findWithDefault v n (getBSubst m)
  subst m v@(BCon _) = v
  subst m BNil       = BNil

instance Subst BSubst (Base, Base, Base) where
  subst m (a, b, c) = (subst m a, subst m b, subst m c)
  
instance Monoid BSubst where
  s `mappend` t = BSubst $ getBSubst (subst s t) `M.union` getBSubst s
  mempty        = BSubst $ mempty
  
instance Singleton BSubst (BVar, Base) where
  singleton (k,a) = BSubst (M.singleton k a)
