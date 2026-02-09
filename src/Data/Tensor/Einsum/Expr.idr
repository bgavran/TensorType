module Data.Tensor.Einsum.Expr

import public Data.Vect
import public Data.List
import Data.List.Quantifiers
import Data.DPair
import Data.HashMap
import Decidable.Equality
import Data.String
import Language.Reflection

import Data.Unique.Vect
import Data.Unique.List
import Data.Tensor
-- import Data.Functor.Naperian
import Misc

%language ElabReflection

-- TODO should axes be ordered?
-- For cubical tensors (or generally Naperian) order is generally irrelevant, but for non-cubical ones order matters! CTensor [BinTree, List] a is very different than CTensor [List, BinTree] a?

||| Correct by construction Einsum expression whose inputs are lists of labels
||| Ensures that
||| a) each output label appears only once
||| b) each output label has appeared in the input
public export
data EinsumExpr : (a : Type) -> DecEq a => Type where
  MkEinsumExpr : {a : Type} -> DecEq a =>
    (inputTy : List (List a)) ->
    (outputTy : UniqueList a) ->
    {auto prf : outputTy `IsFrom` (toList (uniqueJoin inputTy))} ->
    EinsumExpr a

||| Indices used in the output type
public export
freeIndices : {a : Type} -> DecEq a => EinsumExpr a -> UniqueList a
freeIndices (MkEinsumExpr _ outputTy) = outputTy

||| Indices used in the input that *do not* appear in the output type
public export
summationIndices : {a : Type} -> DecEq a => EinsumExpr a -> UniqueList a
summationIndices (MkEinsumExpr inputTy outputTy) = fromList $
  complement (uniqueJoin inputTy) outputTy

-- Note that freeIndices + summationIndices = all starting indices

||| Machinery for pretty-printing Einsum expressions
namespace EinsumToString
  ||| If a=Char, we write it as a string
  ||| Anything else we add commas between elements and brackets around
  public export
  labelToString : {a : Type} -> DecEq a => Show a => List a -> String
  labelToString {a=Char} xs = pack xs
  labelToString xs
    = let inter = case a of
            String => xs -- necessary so extra quotes aren't added
            _ => show <$> xs
      in "[" ++ concat (intersperse "," inter)  ++ "]"
  
  public export
  inputToString : {a : Type} -> DecEq a => Show a =>
    (inputTy : List (List a)) -> String
  inputToString inputTy = concat $ intersperse "," (labelToString <$> inputTy)
  
  
  public export
  outputToString : {a : Type} -> DecEq a => Show a =>
    UniqueList a -> String
  outputToString = labelToString . toList
  
  public export
  toString : DecEq a => Show a => EinsumExpr a -> String
  toString (MkEinsumExpr inputTy outputTy)
    = (inputToString inputTy) ++ "->" ++ (outputToString outputTy)

  public export
  DecEq a => Show a => Show (EinsumExpr a) where
    show = toString

  public export
  oo : EinsumExpr String
  oo = MkEinsumExpr [["i", "j"], ["j", "k"]] ["i", "k"]

  public export 
  ooChar : EinsumExpr Char
  ooChar = MkEinsumExpr [['i', 'j'], ['j', 'k']] ['i', 'k']

||| Machinery for parsing a string into an EinsumExpr
||| We focus on parsing into EinsumExpr Char ("ij,jk->ik")
||| Other options are possible, i.e. "[bt,inp],[inp,out]->[bt,out]"
||| But we do not explore them here
namespace Parsing
  public export
  data EinsumParseError : Type where
    EmptyInput : EinsumParseError
    MissingArrow : EinsumParseError
    ContentBothSidesArrow : EinsumParseError
    DuplicateOutputAxis : EinsumParseError
    OutputAxisNotInInput : EinsumParseError
    MultipleArrows : EinsumParseError
    NonAlphaAxis : EinsumParseError
    BindingInconsistency : EinsumParseError
  
  public export
  Show EinsumParseError where
    show EmptyInput = "Empty input string."
    show MissingArrow = "Missing '->' arrow."
    show ContentBothSidesArrow = "Content missing on one side of arrow."
    show DuplicateOutputAxis = "Duplicate axis in output."
    show OutputAxisNotInInput = "Output axis not found in input."
    show MultipleArrows = "Multiple '->' arrows found."
    show NonAlphaAxis = "Non-alphabetic character found in axis labels. Only [A-Z][a-z] are allowed."
    show BindingInconsistency = "Binding inconsistency in axis labels and tensors." -- should this be here?

  public export
  parseEinsumString : String -> Either EinsumParseError (EinsumExpr Char)
  parseEinsumString str = case str of
    "" => Left EmptyInput
    _ => case splitString str "->" of
      (0 ** _) => Left MissingArrow  -- Technically impossible
      (1 ** _) => Left ContentBothSidesArrow 
      (2 ** [left, right]) => 
        let xs : Vect _ String := snd (splitString left ",")
            inputLabels : List (List Char) := unpack <$> (toList xs)
            outputLabels : List Char := unpack right
        in case all (all isAlpha) inputLabels of
          False => Left NonAlphaAxis
          True => case all isAlphaNum outputLabels of
            False => Left NonAlphaAxis
            True => case fromListMaybe outputLabels of
             Nothing => Left DuplicateOutputAxis
             Just outputTy => 
               case checkAllInInput outputTy (uniqueJoin inputLabels) of
                    Nothing => Left OutputAxisNotInInput
                    Just prf => Right (MkEinsumExpr inputLabels outputTy {prf = (IndeedItIs {prf=prf})})
      (_ ** _) => Left MultipleArrows
    where
      -- Check if all output labels appear in input labels and provide proof
      checkAllInInput : (outputTy : UniqueList Char) ->
        (inputChars : UniqueList Char) -> 
        Maybe (All (\x => Elem x (toList inputChars)) outputTy)
      checkAllInInput [] inputChars = Just []
      checkAllInInput (x :: xs) inputChars = 
        case isElem x (toList inputChars) of
          Yes prf => case checkAllInInput xs inputChars of
                       Just restPrf => Just (prf :: restPrf)
                       Nothing => Nothing
          No _ => Nothing


||| Correct by construction Einsum expression whose input is a string
||| together with a proof that it correctly parses into a valid expression
public export
data EinsumStrExpr : Type where
  EinsumChar : (einsumExprString : String) ->
    {einsumExpr : EinsumExpr Char} ->
    {auto prf : parseEinsumString einsumExprString = Right einsumExpr} ->
    EinsumStrExpr

||| Project out the input of an einsum expression
public export
inputTyProj : EinsumStrExpr -> List (List Char)
inputTyProj (EinsumChar _ {einsumExpr = (MkEinsumExpr inputTy _)}) = inputTy

||| Project out the output of an einsum expression
public export
outputTyProj : EinsumStrExpr -> UniqueList Char
outputTyProj (EinsumChar _ {einsumExpr = (MkEinsumExpr _ outputTy)}) = outputTy

||| Number of input tensors
public export
numInputs : EinsumStrExpr -> Nat
numInputs (EinsumChar _ {einsumExpr = (MkEinsumExpr inputTy _)}) = length inputTy


esTest : EinsumStrExpr 
esTest = EinsumChar "ij,jk->ik"

esTest2 : EinsumStrExpr 
esTest2 = EinsumChar "ij,jk->ij"

failing
  esFail : EinsumStrExpr
  esFail = EinsumChar "ij->xx"

-- ||| Inductive representation of a heterogeneous list of variable-shape tensors 
-- ||| It exposes the shape information the type, and allows us to use the usual 
-- ||| list syntax like [t1, t2] with tensors of different shapes
-- ||| This means that shape parameter can be inferred by the typechecker, instead
-- ||| of needing to be manually supplied
-- ||| For instance, f : TensorList shapes -> ... can consume f [m, n, k] where these are tensors of all different shaeps
-- public export
-- data CTensorList : List (List Cont) -> Type -> Type where
--   Nil : CTensorList [] a
--   (::) : CTensor sh a -> CTensorList shapes a -> CTensorList (sh :: shapes) a

public export
inputType : EinsumStrExpr -> Type
inputType s = Vect (numInputs s) ?inputType_rhs

public export
outputType : (s : EinsumStrExpr) -> (inputType : inputType s) -> Type

public export
einsum : (s : EinsumStrExpr) -> (it : inputType s) -> outputType s it

-- TODO something also about checking for transposes?
-- "ij->ji" counts as a transpose, but what about "i,j->ji"? Or "ij,ji->ij"? Transpose in which variable, that's important?

{-
We need
1. A map einsumType : EinsumStrExpr -> Type which produces a list of input tensors of appropriate types

"ij,jk->ik" -> Tensor [i, j] Double, Tensor [j, k] Double

But technically, all we need at first is to produce a Vect numInputs (List Nat)?
Then from these we can produce the tensors

then from 
einsum : (s : EinsumStrExpr) -> (inputType : einsumType s) -> outputType s inputTensors

  


-}



{-
Elab cons: can't get rid of %runElab at call sites (maybe possible with %macro?)
Elab con2: can't use it for gradient computation since it has to be a constant at compile time

Manual: can't generate implicit variables? Not sure how to do it at all?
 -}





t1 : Tensor [2, 3] ["i", "j"] Double
t1 = ># [ [1, 2, 3], [4, 5, 6] ]

t2 : Tensor [3, 4] ["i", "j"] Double
t2 = ># [ [1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12] ]

||| The name for an axis is an arbitrary string, usually a single character
AxisName : Type
AxisName = Char

AxisBinding : Type
AxisBinding = HashMap AxisName Nat

-- simpleSum : {i : Nat} -> Tensor [i] Double -> Tensor [] Double
-- simpleSum x = ToCubicalTensor $ TZ $ foldr (+) 0 x


-- simpleTrace : {i : Nat} -> Tensor [i, i] Double -> Tensor [] Double
-- simpleTrace x = ToCubicalTensor $ TZ $ foldr (+) 0 x
-- 
-- simpleDiagonal : {i : Nat} -> Tensor [i, i] Double -> Tensor [i] Double
-- simpleDiagonal x = ToCubicalTensor $ TS $ tabulate (\k => TZ $ x @@@ [k, k])

-- nestedFold : {i, j : Nat} -> Tensor [i, j] Double -> Tensor [] Double
-- nestedFold x = ToCubicalTensor $ TZ $ foldr (+) 0 x


-- public export
-- uniqueJoinVect : {nInputs : Nat} -> Vect nInputs String -> UniqueList Char
-- uniqueJoinVect xs = uniqueJoin $ (unpack <$>) (toList xs)
--
-- data EinsumStrExpr' : Type where
--   EinsumChar' : (einsumExpr : String) ->
--     {left, right : String} ->
--     {auto prf : splitString einsumExpr "->" = (2 ** [left, right])} ->
--     {nInputs : Nat} ->
--     {xs : Vect nInputs String} ->
--     {auto prf_left : splitString left "," = (nInputs ** xs)} ->
--     {outputTy : UniqueList Char} ->
--     {auto prf_unique : fromListMaybe (unpack right) = Just outputTy} ->
--     {auto prf_from_input : All (\x => Elem x (toList (uniqueJoinVect xs))) outputTy} ->
--     EinsumStrExpr'

