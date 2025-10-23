module Data.Tensor.Einsum.TestVariableFind

import Data.Tensor.Einsum.VariableFind
import Language.Reflection

%language ElabReflection

-- Test function that demonstrates how to use VariableFind
-- This function has variables in scope that we can test with
export
testVariableFind : Int -> String -> Bool -> Elab ()
testVariableFind x y z = do
  -- Now we have variables x, y, z in scope
  -- Test finding variables by name
  findVariableByName "x"
  findVariableByName "y" 
  findVariableByName "z"
  
  -- Test getting type information as strings
  typeX <- getVariableTypeString "x"
  typeY <- getVariableTypeString "y"
  typeZ <- getVariableTypeString "z"
  
  logMsg "info" 0 $ "Type of x: \{typeX}"
  logMsg "info" 0 $ "Type of y: \{typeY}"
  logMsg "info" 0 $ "Type of z: \{typeZ}"

-- Test function for variable references
export
testVariableReferences : Int -> String -> Bool -> Elab ()
testVariableReferences x y z = do
  -- Get all local variables
  localVars <- localVars
  case localVars of
    [] => logMsg "info" 0 "No local variables found"
    (firstVar :: _) => do
      -- Create a variable reference
      let varRef = varRef firstVar
      
      -- Test processing the variable reference
      result <- processVarRef varRef
      logMsg "info" 0 $ "Processed variable: \{result}"
      
      -- Test getting the type of the variable reference
      varType <- getVarRefType varRef
      logMsg "info" 0 $ "Variable type: \{show varType}"

-- Simple test function with just one variable
export
simpleTest : Int -> Elab ()
simpleTest x = do
  -- Test finding the variable x
  findVariableByName "x"
  
  -- Test getting its type
  typeStr <- getVariableTypeString "x"
  logMsg "info" 0 $ "x has type: \{typeStr}"

-- Test function that tries to find a non-existent variable
export
testNonExistent : Int -> Elab ()
testNonExistent x = do
  -- This should fail
  findVariableByName "nonExistent"
