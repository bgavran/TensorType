module Data.Tensor.Einsum.Elab

import Data.DPair
import Data.List.Quantifiers
import Decidable.Equality
import Language.Reflection

import Data.Tensor
import Data.Tensor.Einsum.Expr
import Data.Tensor.Einsum.ElabUtils
import Misc

%language ElabReflection

------------------------------------------------------------
----- Elaborator Reflection for Einsum Function Generation
------------------------------------------------------------

||| Inductive representation of a heterogeneous list of variable-shape tensors 
||| It exposes the shape information the type, and allows us to use the usual 
||| list syntax like [t1, t2] with tensors of different shapes
||| This means that shape parameter can be inferred by the typechecker, instead
||| of needing to be manually supplied
||| For instance, f : TensorList shapes -> ... can consume f [m, n, k] where these are tensors of all different shaeps
public export
data TensorAList : List (List Nat) -> Type -> Type where
  Nil : TensorAList [] a
  (::) : Tensor sh a -> TensorAList shapes a -> TensorAList (sh :: shapes) a


public export
toHList : TensorAList shapes a -> HList (shapes <&> (\sh => Tensor sh a))
toHList [] = []
toHList (t :: ts) = t :: toHList ts


-----------------------------------------------------------------


||| Find index of the first occurence of a character in a list of lists
public export
findCharPosition : Char -> List (List Char) -> Maybe (Nat, Nat)
findCharPosition c [] = Nothing
findCharPosition c (xs :: xss) = 
  case findIndex (== c) xs of
    Just innerIdx => Just (0, finToNat innerIdx)
    Nothing => case findCharPosition c xss of
      Just (outerIdx, innerIdx) => Just (S outerIdx, innerIdx)
      Nothing => Nothing

||| Compute dimension of a tensor at given position
public export
getTensorADimSize : {shapes : List (List Nat)} -> 
  (tensorIdx : Nat) -> 
  (dimIdx : Nat) -> 
  TensorAList shapes a -> 
  Maybe Nat
getTensorADimSize {shapes = []} _ _ [] = Nothing
getTensorADimSize {shapes = (sh :: shs)} Z dimIdx (t :: ts) = 
  case inBounds dimIdx sh of
    Yes prf => Just (index dimIdx sh)
    No _ => Nothing
getTensorADimSize {shapes = (sh :: shs)} (S k) dimIdx (t :: ts) = 
  getTensorADimSize k dimIdx ts

||| Given a name of an axis, a list of axis names and the corresponding tensors, produce the size of that axis
public export
getSize : {shapes : List (List Nat)} ->
  (outputName : Char) ->
  (inputNames : List (List Char)) -> 
  (inputTensorAs : TensorAList shapes a) ->
  Maybe Nat
getSize outputName inputNames inputTensorAs = do
  (tensorIdx, dimIdx) <- findCharPosition outputName inputNames
  getTensorADimSize tensorIdx dimIdx inputTensorAs

||| Given an input string and a list of tensors, compute the output tensor shape
||| Notably doesn't throw errors related to binding inconsistencies w.r.t. the tensor list
||| We rely on elab reflection in next step to take care of that
public export
einsumComputeOutputType : {a : Type} -> {shapes : List (List Nat)} ->
  String -> TensorAList shapes a -> Either EinsumParseError Type
einsumComputeOutputType exprStr ts = case parseEinsumString exprStr of
  Left err => Left err
  Right expr => let outputChars : List Char := toList (outputTyProj expr)
                    maybeNats : List (Maybe Nat) = (\c => getSize c (inputTyProj expr) ts) <$> outputChars
                    result : Maybe (List Nat) = sequence maybeNats
                in case result of
                  Nothing => Left BindingInconsistency
                  Just listOfNats => Right (Tensor listOfNats a)


partial
isRight : Either a b -> b 
isRight (Right x) = x

{-
I've been playing around with elaborator reflection recently and I'm wondering whether it's possible to provide an interface by which it's possible to interact with functions that use elaborator reflection without using %runElab at call sites.
 -}


-- exUsage : (b : Bool) -> exType b
-- exUsage b = %runElab (exVal b)

einsumTestO : String -> (n : Nat) -> Either Unit Type
einsumTestO "a" n = Right (Vect n Int -> Int)
einsumTestO "b" _ = Right (Double -> List Double)
einsumTestO _ _ = Left ()

partial
einsumTest : (str : String) -> (n : Nat) -> Elab (isRight (einsumTestO str n))
einsumTest str n = case str of
  "a" => pure (\xs => foldr (+) 0 xs)
  "b" => pure (\d => [d, d, d])


-- einsumTestImpl : (str : String) -> (n : Nat) -> isRight (einsumTestO str n)
-- einsumTestImpl str n = %runElab (einsumTest str n)

partial
esVal : List Double
esVal = let a : Elab (Vect 7 Int -> Int) := einsumTest "a" 7
            c : Elab (Double -> List Double) := einsumTest "b" 7
            ae : Vect 7 Int -> Int := %runElab (einsumTest "a" 7)
            ce : Double -> List Double := %runElab (einsumTest "b" 7)
        in (%runElab (einsumTest "b" 7)) 3.7
  
-- Macro that provides NumPy-like einsum("ij,jk->ik", m, n) syntax  
-- This automatically generates einsum functions on-demand with dummy implementation
public export
partial
einsum : {a : Type} -> {shapes : List (List Nat)} ->
  (exprStr : String) ->
  (args : TensorAList shapes a) ->
  Elab (isRight (einsumComputeOutputType exprStr args))
einsum exprStr args = case parseEinsumString exprStr of
  Left err => fail "Parse error in Einsum string: \{show err}"
  Right expr@(MkEinsumExpr inputTy outputTy) => do
    let inpLength : Nat := length inputTy
    when (inpLength /= length shapes) $
      fail "Argument count mismatch: \{toString expr} defines \{show inpLength} inputs, but we got \{show (length shapes)} arguments"

    let uniqueVars : List Char := toList (uniqueJoin inputTy)
        fnName : String := generateFunctionName exprStr
        fnType : TTImp := buildEinsumFunctionType uniqueVars inputTy (toList outputTy)
        -- Generate the function declaration
        claimData = MkIClaimData MW Public [] (MkTy EmptyFC (NoFC (UN (Basic fnName))) fnType)
        tyDecl = IClaim (MkFCVal EmptyFC claimData)

        -- Build lambda parameters for each input tensor
        paramNames = [UN (Basic ("x" ++ show i)) | i <- [0..length inputTy `minus` 1]]
        lambdaParams = zip paramNames inputTy
        
        -- Create the implementation body that matches the output tensor shape
        -- Generate the output shape as a vector literal from the output type
        outputShape = generateShapeVect (toList outputTy)
        -- Create zeros' with the correct output shape and generic type 'a'
        implBody = `(zeros {shape = ~outputShape} {a = dtype})

        -- Build the full lambda expression
        fullImpl = foldr (\(paramName, shape), body => 
                         ILam EmptyFC MW ExplicitArg (Just paramName) (generateTensorAType shape) body) 
                        implBody lambdaParams
       -- 
--  
        -- Create the definition using the correct IDef pattern
        clause = PatClause EmptyFC (IVar EmptyFC (UN (Basic fnName))) fullImpl
        funDef = IDef EmptyFC (UN (Basic fnName)) [clause]

    declare [tyDecl, funDef]

    -- pure (zeros' {a = a})
    -- fn' <- check (IVar EmptyFC (UN (Basic fnName)))
    -- Now call the generated function directly with the actual arguments
    case args of
      [] => fail "No arguments provided"
      [x] => do
        fn <- check (IVar EmptyFC (UN (Basic fnName)))
        pure (fn x)
      [x, y] => do
        fn <- check (IVar EmptyFC (UN (Basic fnName)))
        pure (fn x y)
      [x, y, z] => do
        fn <- check (IVar EmptyFC (UN (Basic fnName)))
        pure (fn x y z)
      _ => fail "More than 3 arguments not yet supported"

{-
Impossible to get rid of %runElab macro at callsites, very annoying! The code below won't compile 
 -}
public export
partial
einsumImpl : {a : Type} -> Num a => {shapes : List (List Nat)} ->
  (exprStr : String) -> (args : TensorAList shapes a) ->
  isRight (einsumComputeOutputType exprStr args)
einsumImpl exprStr args = 
  let t = einsum exprStr args
  in ?lall -- %runElab t

{-
runElab : Elab a -> a
`(_) : ? -> TTImp
quote : (0 val : Type) -> Elaboration m
  => (0 _ : val) -> m TTImp
check : {0 expected : Type} -> Elaboration m =>
  TTImp -> m expected
 -}

gg : Elab Int       
gg = pure 3

gh : Int
gh = %runElab gg

ghQuote : Int
ghQuote = %runElab check `(3)

m : Tensor [2, 3] Double
m = ># [[1, 2, 3], [4, 5, 6]]

n : Tensor [3, 4] Double
n = ># [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]]

-- Test the fixed einsum macro with a unique pattern
testNewPattern : Tensor [3, 2] Double
testNewPattern = %runElab einsum "ab->ba" [m]

einsumImplementation : {a : Type} -> Num a =>
  {is : List Nat} ->  -- free indices
  {ls : List Nat} ->  -- all indices
  {inputShs : List (List Nat)} ->
  {outputSh : List Nat} ->
  {auto prf : (fromList outputSh) `IsFrom` is} ->
  List1 (Exists (\sh => (Tensor sh a, (fromList sh) `IsFrom` ls))) ->
  Tensor outputSh a
einsumImplementation xs = ?hmma
--   -- According to the blog post, einsum works as nested for loops
--   -- 1. Initialize output tensor to zeros
--   let outputTensorA : Tensor outputSh a := zeros'
--   -- 2. For each combination of free indices (outer loops)
--   -- 3. For each combination of summation indices (inner loops)  
--   -- 4. Compute product of all input tensors at appropriate indices
--   -- 5. Add this product to output tensor at current free index position
--   in 
--   -- This is a simplified implementation that needs to be expanded
--   -- based on the actual index manipulation and tensor operations
--   -- The core idea is to iterate through all valid index combinations
--   -- and perform the sum of products as described in the blog post
--   case xs of
--     (x ::: xs) => 
--       -- For now, we return the zero tensor as a placeholder
--       -- The full implementation would need to:
--       -- 1. Extract the tensors from the existential types
--       -- 2. Create index iterators for free and summation indices  
--       -- 3. Implement the nested loops as described in the blog post
--       -- 4. Perform the products and sums according to Einstein notation
--       outputTensorA


{-
TODO interesting cases of above:
a) one output index, repeated in input: M[i] += M[i, i] 
This means that the einsum string determines where to apply it.
Though, notably we've already *created the variables via Elab reflection*, so we should be able to apply them?
I.e. we should be able to 'find all occurences of i' in context, and apply the current value to it?

Consider
einsum "ii->i" m 
vs
einsum "ij->i" m

If we have a matrix m : Tensor [3, 3] a

in both cases we'd need to look at the free index i, and then realise that depending on the einsum string we'd need to ..

In both we'd need to look at the free index i, and then realise that depending on the string we'd need to 

---

einsum "isj->ij" t



-}

parameters {a : Type} {auto _ : Num a} {b, i, j, k : Nat}

  matMul : Tensor [i, j] a -> Tensor [j, k] a -> Tensor [i, k] a
  matMul m n = %runElab einsum "ij,jk->ik" [m, n]

  batchedMatMul : Tensor [b, i, j] a -> Tensor [b, j, k] a -> Tensor [b, i, k] a
  batchedMatMul m n = %runElab einsum "bij,bjk->bik" [m, n]
  
  outer : Tensor [i] a -> Tensor [j] a -> Tensor [i, j] a
  outer v w = %runElab einsum "i,j->ij" [v, w]
  
  inner : Tensor [i] a -> Tensor [i] a -> Tensor [] a
  inner v w = %runElab einsum "i,i->" [v, w]

  elementwise : Tensor [i] a -> Tensor [i] a -> Tensor [i] a
  elementwise v w = %runElab einsum "i,i->i" [v, w]

  transpose : Tensor [i, j] a -> Tensor [j, i] a
  transpose m = %runElab einsum "ij->ji" [m]
  
  trace : Tensor [i, i] a -> Tensor [] a
  trace m = %runElab einsum "ii->" [m]
  
  diag : Tensor [i, i] a -> Tensor [i] a
  diag m = %runElab einsum "ii->i" [m]
  
  sum : Tensor [i] a -> Tensor [] a
  sum v = %runElab einsum "i->" [v]

  matrixVectorProduct : Tensor [i, j] a -> Tensor [j] a -> Tensor [i] a
  matrixVectorProduct m v = %runElab einsum "ij,j->i" [m, v]

  vectorMatrixProduct : Tensor [i] a -> Tensor [i, j] a -> Tensor [j] a
  vectorMatrixProduct v m = %runElab einsum "i,ij->j" [v, m]