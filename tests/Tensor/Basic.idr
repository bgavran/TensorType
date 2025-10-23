module Tensor.Basic

import Data.Tensor

----------------------------------------------
-- Initialisation of some tensors we will use
----------------------------------------------

-- A 3x4 tensor
t0 : Tensor [3, 4] Double
t0 = fromConcreteTy [ [0, 1, 2, 3]
                    , [4, 5, 6, 7]
                    , [8, 9, 10, 11]]

t1 : Tensor [6] Double
t1 = fromConcreteTy [0,1,2,3,4,5]

t2 : Tensor [2, 3] Double
t2 = fromConcreteTy [ [0, 1, 2]
                    , [3, 4, 5]]

{---------------------------------------------
Tests of only some functions present in the 
library, and by no means exhaustive.

A bit of a wild west here.
---------------------------------------------}

t1FromArange : Tensor [6] Double
t1FromArange = arange


arangeWorks : Basic.t1 = Basic.t1FromArange
arangeWorks = Refl

failing
  ||| Which will fail if we supply an array with the wrong shape
  failConcrete : Tensor [3, 4] Double
  failConcrete = fromConcreteTy [ [0, 1, 2, 3, 999]
                                , [4, 5, 6, 7]
                                , [8, 9, 10, 11]]

failing
  ||| Or if the reshape is not possible
  failReshape : Tensor [7, 2] Double
  failReshape = reshape t1

t0Sum : Tensor [3, 4] Double
t0Sum = t0 + t0

||| And all sorts of numeric operations
numericOps : Tensor [3, 4] Double
numericOps = abs (- (t0 * t0) <&> (+7))

dotProduct : Tensor [] Double
dotProduct = dot t1 t1

failing
  ||| Failing if we add tensors of different shapes
  tSumFail : Tensor [3, 4] Double
  tSumFail = t1 + t2

failing
  ||| Or if types mismatch in contractions
  dotProductFail : Tensor [] Double
  dotProductFail = dot t1 (arange {n=7})

||| We can safely index into tensors
indexExample : Double
indexExample = t0 @@ [1, 2]

failing
   ||| And fail if we index outside of the tensor's shape
   indexExampleFail : Double
   indexExampleFail = t1 @@ [7, 2]

||| Safe transposition
t1Transposed : Tensor [4, 3] Double
t1Transposed = transposeMatrix t0

-- ||| Safe slicing
-- takeExample : Tensor [2, 1] Double
-- takeExample = takeTensor [2, 1] t0
-- 
-- failing
--   ||| Which fails when we try to take more than exists
--   takeExampleFail : Tensor [10, 2] Double
--   takeExampleFail = takeTensor [10, 2] t0


----------------------------------------
-- Generalised tensor examples
-- These include list, tree shaped tensors, and other non-cubical tensors
----------------------------------------

||| TensorA can do everything that Tensor can
t0Again : CTensor [Vect 3, Vect 4] Double
t0Again = t0

||| Including building concrete Tensors
t1again : CTensor [Vect 6] Double
t1again = fromConcreteTy [1,2,3,4,5,6]

||| Above, the container Vect is made explicit in the type
||| There are other containers we can use in its place
||| We can use List which allows us to store an arbitrary number of elements
exList : CTensor [List] Double
exList = fromConcreteTy [1,2,3,4,5,6,7,8]

||| Same type as above, different number of elements
exList2 : CTensor [List] Double
exList2 = fromConcreteTy [100,-200,1000]

{- 
We can also use BinTreeLeaf, allowing us to store a tree with data on its leaves

        *
      /   \
     *     2 
    / \
(-42)  46 
-}
exTree1 : CTensor [BinTreeLeaf] Double
exTree1 = fromConcreteTy $ Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)



{- 
Here's another tree, with a different number of elements
        *
      /   \
     10   100 
-}
exTree2 : CTensor [BinTreeLeaf] Double
exTree2 = fromConcreteTy $ Node' (Leaf 10) (Leaf 100)

||| We can take the dot product of these two trees
||| The fact that they don't have the same number of elements is irrelevant
||| What matters is that the container defining them 'BinTreeLeaf' is the same
dotProduct2 : CTensor [] Double
dotProduct2 = dot exTree1 exTree2

||| Here's a tree with whose nodes are vectors of size 2
exTree3 : CTensor [BinTreeNode, Vect 2] Double
exTree3 = fromConcreteTy $ Node [4,1] (Node [17, 4] Leaf' Leaf') Leaf'

||| This can get very complex, but is still fully type-checked
exTree4 : CTensor [BinTreeNode, BinTreeLeaf, Vect 3] Double
exTree4 = fromConcreteTy $
  Node (Node'
          (Leaf [1,2,3])
          (Leaf [4,5,6]))
    Leaf'
    (Node (Leaf [178, -43, 63]) Leaf' Leaf')

{- 
We can index into any of these structures
        *
      /   \
     *     2  <---- indexing here is okay
    / \
(-42)  46 
-}
indexTreeExample : Double
indexTreeExample = exTree1 @@ [GoLeft (GoLeft Done)]


failing
  {- 
  And we'll get errors if we try to index outside of the structure
          *
        /   \
       *     2  
      / \     \
  (-42)  46    X   <---- indexing here throws an error
  -}
  indexTreeExampleFail : Double
  indexTreeExampleFail = ex1 @@ [GoRight (GoRight Done)]


{- 
We can also perform reshapes, views, and traversals of non-cubical tensors.
Here's a tree-vector with nodes as elements
        3
      /   \
     2     4
    / \   / \
   1   * *   * 
  / \
 *   *
-}
exTree5 : CTensor [BinTreeNode] Double
exTree5 = fromConcreteTy $ Node 3 (Node 2 (Node 1 Leaf' Leaf') Leaf') (Node 4 Leaf' Leaf')

-- ||| And here is the in-order traversal of that tree
-- traverseTree : TensorA [List] Double
-- traverseTree = reshapeTensorA inorderBinTreeNode exTree5