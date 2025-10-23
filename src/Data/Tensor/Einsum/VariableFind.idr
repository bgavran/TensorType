module Data.Tensor.Einsum.VariableFind

import Language.Reflection
import Data.List
import Data.String

import Data.Tensor

%language ElabReflection

-- Find variable by name and get its type as a string
export
getVariableTypeString : String -> Elab String
getVariableTypeString varName = do
  localVars <- localVars
  case filter (\name => show name == varName) localVars of
    (name :: _) => do 
      -- Found in local scope
      varType <- getLocalType name
      pure $ show varType
    [] => do
      -- Not found locally, try global scope
      let globalName = UN (Basic varName)
      globalTypes <- getType globalName
      case globalTypes of
        [] => fail $ "Variable '\{varName}' not found in local or global scope"
        ((name, varType) :: _) => do
          pure $ show varType


-- Helper function to extract names from a shape list
extractFromShapeList : TTImp -> List String
extractFromShapeList (IVar _ name) = [show name]
extractFromShapeList (IApp _ (IVar _ name) rest) = show name :: extractFromShapeList rest
extractFromShapeList (IApp _ f x) = extractFromShapeList f ++ extractFromShapeList x
extractFromShapeList _ = []

-- Helper function to recursively search for CTensor in the type
findCTensorInType : TTImp -> List String
findCTensorInType (IApp _ (IApp _ (IVar _ name) shapeList) _) = 
  if show name == "CTensor" then 
    extractFromShapeList shapeList
  else []
findCTensorInType (IApp _ f x) = 
  findCTensorInType f ++ findCTensorInType x
findCTensorInType _ = []

-- Helper function to extract container names from a TTImp type
extractContainerNamesFromType : TTImp -> List String
extractContainerNamesFromType (IApp _ (IApp _ (IVar _ name) shapeList) _) = 
  if show name == "CTensor" then extractFromShapeList shapeList else []
extractContainerNamesFromType (IApp _ f x) = 
  extractContainerNamesFromType f ++ extractContainerNamesFromType x
extractContainerNamesFromType (IVar _ name) = 
  if show name == "CTensor" then [] else [show name]
extractContainerNamesFromType _ = []

||| Get variable references of all containers making up a tensor
||| I.e. given c1 : Cont and c2 : Cont
||| getTensorContainerRefs [c1, c2] will return [c1, c2]
getTensorContainerRefs : CTensor shape a -> Elab (List String)
getTensorContainerRefs tensor = do
  -- Get the type of the tensor using quote
  tensorType <- quote tensor
  
  -- Debug: log the actual type structure
  logMsg "info" 0 $ "Tensor type: \{show tensorType}"
  
  -- Try different parsing approaches
  let result1 = findCTensorInType tensorType
  let result2 = extractContainerNamesFromType tensorType
  let result3 = extractAllNames tensorType
  
  logMsg "info" 0 $ "Method 1 (findCTensorInType): \{show result1}"
  logMsg "info" 0 $ "Method 2 (extractContainerNamesFromType): \{show result2}"
  logMsg "info" 0 $ "Method 3 (extractAllNames): \{show result3}"
  
  -- Return the first non-empty result
  case result1 of
    [] => case result2 of
      [] => pure result3
      xs => pure xs
    xs => pure xs

-- Extract all names from any TTImp structure
extractAllNames : TTImp -> List String
extractAllNames (IVar _ name) = [show name]
extractAllNames (IApp _ f x) = extractAllNames f ++ extractAllNames x
extractAllNames _ = []


myVar2 : Int
myVar2 = 7

testt : String
testt = let myVar = 3 in %runElab getVariableTypeString "myVar"

testt2 : String
testt2 = %runElab getVariableTypeString "myVar2"


t1 : CTensor [BinTree, Vect 2] Double
t1 = ># Node [1, 2] (Leaf [3,4]) (Leaf [4,5])

ns : List String
ns = %runElab getTensorContainerRefs t1

-- Let's also test with a simpler case to see the structure
simpleTest : List String
simpleTest = %runElab do
  let simpleTensor : CTensor [BinTree] Int = ?hole
  getTensorContainerRefs simpleTensor