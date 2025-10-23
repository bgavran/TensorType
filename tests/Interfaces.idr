module Interfaces

import Data.Container

{-------------------------------------------------------------------------------
Testing of interfaces on various containers

-- todo add tests for what the show should display
-- Vectors, and nesting thereof
-------------------------------------------------------------------------------}


namespace Vect
  concreteVal1 : Vect 4 Int
  concreteVal1 = [1,2,3,4]

  val1 : Vect' 4 Int
  val1 = fromConcreteTy concreteVal1

  ||| Can be shown
  showval1 : String
  showval1 = show val1

  -- Need to do this at runtime since show relies on certain primitive operations
  -- Though does it only do that for Int?
  -- Perhaps we can use my `Display` functionality to get around this?
  ||| Expected output
  public export
  showv1Expected : IO ()
  showv1Expected = do
    case showval1 == show concreteVal1 of
      True => putStrLn "Test passed"
      False => putStrLn "Test did not pass"

namespace BinTree
  concreteVal1 : BinTreeSame Int
  concreteVal1 = Node 4 (Node 7 (Leaf 0) (Leaf (-1))) (Leaf 14)

  val1 : BinTree' Int
  val1 = fromConcreteTy concreteVal1

  showval1 : String
  showval1 = show val1


namespace Tensor
  concreteVal1 : Int
  concreteVal1 = 16

  concreteVal2 : Vect 2 Int
  concreteVal2 = [10, 11]

  concreteVal3 : Vect 3 (Vect 2 Int)
  concreteVal3 = [[10, 11], [20, 21], [30, 31]]



  showval1 : String
  showval1 = show val1

  showval2 : String
  showval2 = show val2

  showval3 : String
  showval3 = show val3


  namespace EqualityTests
    testEq1 : (Tensor.val1 == Tensor.val1) = True
    testEq1 = %search

    testEq2 : (Tensor.val2 == Tensor.val2) = True
    testEq2 = Refl

    -- testEq3 : (Tensor.val3 == Tensor.val3) = True
    -- testEq3 = %search


  v1 : Tensor' [Vect 5] Int
  v1 = pure 9
  
  v11 : Tensor' [Vect 5, Vect 5] Int
  v11 = pure 10
  
  v2 : Tensor' [Vect 4] Int
  v2 = fromConcreteTy [1,2,3,4]
  
  -- v1show : String
  -- v1show = show v1
  
  v11show : String
  v11show = show v11
  
  v2show : String
  v2show = show v2
  
  -- Lists, and nesting thereof
  
  
  l1 : Tensor' [List] Int
  l1 = pure 3
  
  l11 : Tensor' [List, List] Int
  l11 = fromConcreteTy [[1,2], [3,4]]
  
  l2 : Tensor' [List] Int
  l2 = fromConcreteTy [4, 5, 6]
  
  
  l1show : String
  l1show = show l1
  
  l11show : String
  l11show = show l11
  
  l2show : String
  l2show = show l2
  
  -- BinTrees, and nesting thereof
  
  b1 : Tensor' [BinTree] Int
  b1 = fromConcreteTy $ Node 1 (Leaf 2) (Leaf 3)
  
  b11 : Tensor' [BinTree, BinTree] Int
  b11 = fromConcreteTy $
    Node (Leaf 3) (Leaf (Node 44 (Leaf 100) (Leaf 101))) (Leaf (Leaf (-14)))
  
  
  
  
  -- various combinations of containers
  bl : Tensor' [BinTree, List] Int
  bl = fromConcreteTy $
    Node [1,2,3] (Node [4,5,6,7] (Leaf [0]) (Leaf [3])) (Leaf [99])
  
  
  -- testing for various sorts of interfaces we wish to have with Tensors
  
  -- Eq
  
  -- Show
  
  -- Foldable