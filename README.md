# FunFlow

*An implementation of Control-Flow and Units of Measure Analysis for a Simple Functional Programming Language by Wout Elsinghorst and Pepijn Kokke.*

## Description

For this assignment we've implemented the following two analyses for a basic 
functional programming language:

 - Control Flow Analysis
 - Units of Measure Analysis
 
The main language is based on the Fun language introduced in the book by Henkin et al. It has polymorphic
types, Sums and Pairs and Let is generalized.

For Control Flow Analysis (CFA) we have extended the basic syntax of the FUN language 
to support the construction en destruction of binary Sums and Products. These kind of 
types can be named by the programmer and for CFA their creation points will be tracked.
The analysis has no subeffecting and is monovariant.

The Units of Measure Analysis (UMA) exposes a few new builtin functions to the programmer to
allow him to instantiate integer terms with certain measurement unit type annotations. 
These annotations are propagated and combined during type inference to aid the programmer
in writing unit-correct programs. This analysis is also monovariant. The implementation of
UMA is based on the paper "Types for Units-of-Measure: Theory and Practice" by Andrew Kennedy.
The type rules can be found in said paper.

The implementation of these analyses follows a two stage approach. In the first stage
types are inferred and constraints are generated while in the second stage the constraints
are solved. The type inference is done by an our own implementation of algorithm W.

## Feature Completeness
  -The main language is Let polymorphic and supports Sums and Pairs
  -Units of Measure Analysis (UMA) is fully working. I haven't been able to find any solvable 
   constraints that the algorithm was unable to solve or any inconsistent constraints that 
   the algorithm didn't error out on.
  -UMA is only monovariant
  -Control Flow Analysis doesn't have subeffecting or polyvariance, but is otherwise fully functional


## Program Input / Output

The file `src/Main.hs` contains the programs on which an analysis can be run. The desired program
is chosen by tweaking the case expression in the `example` function. 

The output of the program is a typed and annotated version of the input program. The convention is
that annotation variables are put between curly braces `{ }` while concrete annotations are put
between square brackets `[ ]`.

## Code Layout / Points of Interest

### In `src/FUN.hs`

  `main :: IO ()`

Loads the example code. Prints the results.
  
  `example :: Program`

A switch statement coming with a collection of pre-written programs to test the code.
Use option 1 to see measurement analysis in action.

### In `src/Base.hs`
Basic definitions of the AST and some helper functions.
    
### In `src/Parsing.hs`
Code to parse a basic functional programming language. 
  
### In `src/Labeling.hs`
Code to attach unique labels to a specific component. Mostly used for 
generating the unique Program Points used in Control Flow Analysis.

### In `src/Analysis.hs`

  `type Analysis a = ErrorT TypeError (SupplyT FVar (Supply TVar)) a`

  Our W algorithm lives in this Monad. ErrorT is used to report error messages 
during unification and the two Supplies are used to have fresh streams of both
type and annotation variables.

  `analyse :: Expr -> Env -> Analysis (Type, Env, Set Constraint)`

Runs W on a given expression and generate the necessary constraints
for the respective annotation analyses.

  `analyseProgram :: Program -> Either TypeError (Map TVar TypeScheme, Program, Set Constraint)`

Runs W on a bunch of top level declarations and finalizes the Supply monads. Every Decl
has the inferred type of the Decls above it available to it via the environment. Type 
checking happens in a single pass, so Decls don't have access to the types of Decls 
defined below them.
  
  `unify :: Type -> Type -> Analysis (Env, Set Constraint)`

The function `unify` tries to create a unification for its two arguments. It returns
an substituion such that applying the substitution on both arguments makes them have
equal types in the underlying type system, but their type annotations are not unified
yet. Instead, equality constraints are generated which will be used by a specific 
constraint solver in a later phase to unify the annotations in a proper way. If type
unification is impossible, an error is raised. Is used only by src/Analyses.hs:analysis
  
  `prelude :: Analysis (Env, [Decl])`

Builds an initial environment containing the builtin functions used to give unit
annotations to FUN programs. Think 'asKelvin', 'asMeter', etc...
  
### In `src/Analyses/Flow.hs`

  `solveFlowConstraints :: FSubst -> Set FlowConstraint -> (FSubst, Set FlowConstraint)`

Takes a set of FlowConstraints and builds a substitution mapping each flow variable to the set
program points reaching this variable.

### In `src/Analyses/Measure.hs`

  `solveScaleConstraints :: SSubst -> Set ScaleConstraint -> (SSubst, Set ScaleConstraint)`

From a set of ScaleConstraints, build a scale substitution that unifies all matching annotations.
The resulting substitution is then applied to the resulting type environment to obtain a
final annotated type environment.  
  
  `printScaleInformation :: Set ScaleConstraint -> String`

Print the set of Scale Constraints. Usually the constraint set is first simplified using
`solveScaleConstraints`.
  
  `solveBaseConstraints :: BSubst -> Set BaseConstraint -> (BSubst, Set BaseConstraint)`

Similar to `solveScaleConstraints`.
  
  `printBaseInformation :: Set ScaleConstraint -> String`

Similar to `printScaleInformation`.
