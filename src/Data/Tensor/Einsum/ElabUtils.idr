module Data.Tensor.Einsum.ElabUtils

import Data.DPair
import Data.List.Quantifiers
import Decidable.Equality
import Language.Reflection

import Data.Tensor.Einsum.Expr
import Data.Unique
import Misc

||| Helper function to convert Char to variable name
public export
charToVarName : Char -> Name
charToVarName c = UN (Basic (singleton c))

||| Generate [i, j, k] from ['i', 'j', 'k']
public export
generateShapeVect : List Char -> TTImp
generateShapeVect [] = `([])
generateShapeVect (x :: xs) = 
  `(~(IVar EmptyFC (charToVarName x)) :: ~(generateShapeVect xs))

||| Generate Tensor [i, j] dtype from shape ['i', 'j']
public export
generateTensorAType : List Char -> TTImp
generateTensorAType shape = 
  let shapeVect = generateShapeVect shape
  in `(Tensor ~(shapeVect) dtype)


||| ['i', 'j', 'k'] -> {dtype : Type} -> Num a => {i, j, k : Nat} -> TensorA [i, j, k] dtype
public export
generateOutputType : List Char -> TTImp
generateOutputType cs =
  let outputTensorAType : TTImp := generateTensorAType cs
      -- Add implicit {i, j, k : Nat} parameters
      withNatParams : TTImp := foldr (\var, acc => 
        IPi EmptyFC MW ImplicitArg (Just (charToVarName var)) `(Nat) acc) outputTensorAType cs

      -- Add Num a constraint
      withNumConstraint : TTImp := IPi EmptyFC MW AutoImplicit Nothing `(Num dtype) withNatParams

      fullType : TTImp := IPi EmptyFC MW ImplicitArg (Just (UN (Basic "dtype"))) `(Type) withNumConstraint
  in fullType


||| Build einsum function type with tensor shapes and implicit Nat parameters
public export
buildEinsumFunctionType : List Char -> List (List Char) -> List Char -> TTImp
buildEinsumFunctionType uniqueVars inputShapes outputShape =
  let
    inputTensorATypes : List TTImp := generateTensorAType <$> inputShapes
    outputTensorAType : TTImp := generateTensorAType outputShape
    
    -- Build the main function type: input1 -> input2 -> ... -> output
    mainFunctionType : TTImp := foldr (\inputType, acc =>
      IPi EmptyFC MW ExplicitArg Nothing inputType acc)
      outputTensorAType inputTensorATypes
    
    -- Add implicit {i, j, k : Nat} parameters
    withNatParams : TTImp := foldr (\var, acc => 
      IPi EmptyFC MW ImplicitArg (Just (charToVarName var)) `(Nat) acc) mainFunctionType uniqueVars
    
    -- Add Num a constraint
    withNumConstraint : TTImp := IPi EmptyFC MW AutoImplicit Nothing `(Num dtype) withNatParams
    
    -- Add implicit {a : Type} parameter FIRST (before everything else)
    fullType : TTImp := IPi EmptyFC MW ImplicitArg (Just (UN (Basic "dtype"))) `(Type) withNumConstraint
    
  in fullType

||| Generate a function name from the einsum expression
public export
generateFunctionName : String -> String
generateFunctionName einsumStr = "einsum_" ++ withUnderscores where
  withUnderscores = replaceString "->" "__" (replaceString "," "_" einsumStr)


||| Main function to generate Einsum function type from string
export
partial
generateEinsumType : String -> Elab ()
generateEinsumType einsumStr = case parseEinsumString einsumStr of
  Left err => fail "Parse error in Einsum string: \{show err}"
  Right (MkEinsumExpr inputTy outputTy) => do
    let uniqueVars = toList (uniqueJoin inputTy)
        fnName = generateFunctionName einsumStr
        fnType = buildEinsumFunctionType uniqueVars inputTy (toList outputTy)
    
    -- Create the type declaration
        claimData = MkIClaimData MW Public [] (MkTy EmptyFC (NoFC (UN (Basic fnName))) fnType)
        tyDecl = IClaim (MkFCVal EmptyFC claimData)
    
    declare [tyDecl]





