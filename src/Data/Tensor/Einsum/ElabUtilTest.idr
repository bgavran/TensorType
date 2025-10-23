module Data.Tensor.Einsum.ElabUtilTest

import Language.Reflection

%language ElabReflection

-- First, let's see what a quoted expression looks like
exampleQuote : TTImp
exampleQuote = `(x + y)

-- Function to show the structure of a quoted expression
showStructure : TTImp -> String
showStructure tm = show tm

-- Test function to explore elaborator reflection
export
testExpr : IO ()
testExpr = putStrLn $ show `(x * y + 3)

testExpr2 : IO () 
testExpr2 = putStrLn $ show `(let t = x * y in t + 3)

----------------------------------------
----- Creating variables with chosen names using %runElab
----------------------------------------

-- Function to create an integer variable with a chosen name and value
createIntVar : String -> Int -> Elab ()
createIntVar name value = do
  let varName : Name := UN (Basic name)
  let varType : TTImp := `(Int)
  let varValue : TTImp := IPrimVal EmptyFC (I value)
  
  -- Create type declaration using correct constructors
  let tyDecl : Decl
      tyDecl = IClaim (NoFC (MkIClaimData MW Public [] (MkTy EmptyFC (NoFC varName) varType)))
  
  -- Create function definition with the constant value
  let funDef : Decl := IDef EmptyFC varName [PatClause EmptyFC (IVar EmptyFC varName) varValue]
  
  -- Use declare with a list of declarations
  declare [tyDecl, funDef]

%runElab createIntVar "myVar" 42
%runElab createIntVar "ieva" 100000000

gg : Int
gg = myVar + 40

-- Test that our generated variables work
export
testGeneratedVars : IO ()
testGeneratedVars = do
  putStrLn $ "myGeneratedVar = " ++ show myVar
  putStrLn $ "anotherVar = " ++ show gg

----------------------------------------
----- %runElab on the Right-Hand Side - YES it has a type!
----------------------------------------

-- %runElab CAN be used on the right-hand side of = and DOES have a type!
-- It evaluates to a value at compile time that matches the expected type.

-- More complex example: Use %runElab with check to create a typed value
-- This is the pattern from the tutorial you shared
createTypedInt : Int
createTypedInt = %runElab check `(42)


createTypedInt2 : Int
createTypedInt2 = %runElab check `(42 + 13)


--- Non-dependent variant

fnn : Int -> Int
fnn = (+ 15)

createAddFunction : Int -> Int
createAddFunction = %runElab check `(fnn)

export
testRHSElabFunction : Int
testRHSElabFunction = createAddFunction 10 -- Should be 25

-- Dependent variant 2

public export
einsumZeroDimensional : String -> Type
einsumZeroDimensional "int" = Int -> Int
einsumZeroDimensional "double" = Double -> Double
einsumZeroDimensional _ = Void

partial
public export
einsumImpl : (xs : String) -> einsumZeroDimensional xs
einsumImpl "int" = %runElab check `(\x => x + 2)
einsumImpl "double" = %runElab check `(\x => x * 17)


einsumTest : (xs : String) -> einsumZeroDimensional xs
einsumTest xs = assert_total $ einsumImpl xs

ggh : Double
ggh = einsumTest "double" 3

-- Test version that returns Elab type (to test the hypothesis)
partial
einsumImplElab : (xs : String) -> Elab (einsumZeroDimensional xs)
einsumImplElab "->" = check `(\x => einsumElab [x])
einsumImplElab ",->" = check `(\x, y => einsumElab [x, y])
einsumImplElab ",,->" = check `(\x, y, z => einsumElab [x, y, z])

-- rrt : Double
-- rrt = einsumTest "asdf" 3

--- Dependent variant 3

ifn : String -> Type
ifn s = case s of
  "ij->ji" => Bool
  _ => Int

-- Maybe-based approach: Explicitly handle partiality
dfnMaybe : (s : String) -> ifn s
--dfnMaybe s with (s)
--  dfnMaybe s | "ij->ji" = True
--  dfnMaybe s | "ii->" = 4
--  dfnMaybe s | _ = ?uiiiiiiiiiiiiiiiiiiii

-- dfnMaybe "ij->ji" = True   -- We know ifn "ij->ji" = Bool, so True : Bool
-- dfnMaybe "ii->" = 4        -- We know ifn "ii->" = Int, so 4 : Int  
-- dfnMaybe _ = ?uii            -- For unknown strings, we return Nothing


{-
testMaybe1 : Maybe Int
testMaybe1 = %runElab check `(dfnMaybe "->")


-- Another example: create a value by running elaboration that builds an expression
createComputedValue : Int  
createComputedValue = %runElab do
  let expr = `(5 * 8 + 2)
  check expr

-- Example showing %runElab with Elab monad computations on RHS
computeStringLength : Nat
computeStringLength = %runElab do
  let str = "Hello, Idris!"
  check `(cast {to=Nat} ~(IPrimVal EmptyFC (I (cast (String.length str)))))

-- Test that these work
export
testRHSExamples : IO ()
testRHSExamples = do
  putStrLn "=== Testing %runElab on Right-Hand Side ==="
  putStrLn $ "simpleExample structure: " ++ show simpleExample
  putStrLn $ "createTypedInt: " ++ show createTypedInt  
  putStrLn $ "createAddFunction 10 20: " ++ show testRHSElabFunction
  putStrLn $ "createComputedValue: " ++ show createComputedValue
  putStrLn $ "computeStringLength: " ++ show computeStringLength

{- These functions don't work because declareType and defineFunction don't exist
-- Function to create a String variable with a chosen name and value
createStringVar : String -> String -> Elab ()
createStringVar name value = do
  let varName = UN (Basic name)
  let varType = `(String)
  let varValue = IPrimVal EmptyFC (Str value)
  
  -- Declare the type
  declareType $ ToCubicalTensory EmptyFC EmptyFC varName varType
  
  -- Define the function with a single clause
  let clause = PatClause EmptyFC (IVar EmptyFC varName) varValue
  defineFunction $ MkFunDef EmptyFC varName [clause]

-- Create string variables
%runElab createStringVar "greeting" "Hello from generated code!"
%runElab createStringVar "farewell" "Goodbye from Idris!"

-- Test the generated string variables
export
testGeneratedStrings : IO ()
testGeneratedStrings = do
  putStrLn greeting
  putStrLn farewell

-- More flexible function that can create variables of any type (as long as we can quote the value)
createVar : String -> TTImp -> TTImp -> Elab ()
createVar name varType varValue = do
  let varName = UN (Basic name)
  
  -- Declare the type
  declareType $ ToCubicalTensory EmptyFC EmptyFC varName varType
  
  -- Define the function with a single clause
  let clause = PatClause EmptyFC (IVar EmptyFC varName) varValue
  defineFunction $ MkFunDef EmptyFC varName [clause]

-- Create a Bool variable using the flexible function
%runElab createVar "isReady" `(Bool) `(True)

-- Create a List variable
%runElab createVar "myList" `(List Int) `([1, 2, 3, 4, 5])

-- Test the flexibly generated variables
export
testFlexibleVars : IO ()
testFlexibleVars = do
  putStrLn $ "isReady = " ++ show isReady
  putStrLn $ "myList = " ++ show myList
  putStrLn $ "length myList = " ++ show (length myList)
-}


--- Dependent variant 0

rr : List Char -> Type
rr [] = Bool
rr (_ :: _) = Int

rrd : (xs : List Char) -> rr xs
rrd [] = True
rrd ['a', 'b', 'c'] = 4
rrd (_ :: _) = 5  -- Match non-empty lists explicitly instead of catch-all

testList : (xs : List Char) -> rr xs
testList = %runElab check `(rrd)

