module BasicExamples

import Data.Tensor

%hide Syntax.WithProof.prefix.(@@) -- (@@) is used here for indexing

----------------------------------------
-- Examples of standard, cubical tensors
----------------------------------------

||| Now you can construct Tensors directly:
t0 : Tensor [3, 4] Double
t0 = ># [ [0, 1, 2, 3]
        , [4, 5, 6, 7]
        , [8, 9, 10, 11]]

{--------------------
Here `>#` behaves like a constructor: it takes a concrete value and turns it into the tensor of the appropriate shape (It should be visually read as a 'map' (`>`) into 'tensor' (`#`)).

You can also use functions analogous to numpy's, such as `np.arange` and `np.reshape`:
--------------------}
t1 : Tensor [6] Double
t1 = arange

-- These implicit arguments will not be necessary in the future
t2 : Tensor [2, 3] Double
t2 = reshape {oldShape=[6], newShape=[2, 3]} t1

{-
where the difference between numpy is that these operations are typechecked
- meaning they fail at compile-time if you supply an array with the wrong shape.
-}
failing
  failConcrete : Tensor [3, 4] Double
  failConcrete = ># [ [0, 1, 2, 3, 999]
                    , [4, 5, 6, 7]
                    , [8, 9, 10, 11]]

failing
  failReshape : Tensor [7, 2] Double
  failReshape = arange {n=7}

||| You can perform all sorts of familiar numeric operations:
exampleSum : Tensor [3, 4] Double
exampleSum = t0 + t0

exampleOp : Tensor [3, 4] Double
exampleOp = abs (- (t0 * t0) <&> (+7))

||| including standard linear algebra
dotExample : Tensor [] Double
dotExample = dot t1 (t1 <&> (+5))

matMulExample : Tensor [2, 4] Double
matMulExample = matMul t2 t0

transposeExample : Tensor [4, 3] Double
transposeExample = transposeMatrix t0

{--------------------
which all have their types checked at compile-time. For instance, you can't 
add tensors of different shapes, or perform matrix multiplication if the 
dimensions of matrices don't match.
--------------------}
failing
  sumFail : Tensor [3, 4] Double
  sumFail = t0 + t1

failing
  matMulFail : Tensor [7] Double
  matMulFail = matMul t0 t1

||| Like in numpy, you can safely index into tensors, set values of tensors, and perform slicing:
||| This retrieves the value of t- at location [1,2]
indexExample : Double
indexExample = t0 @@ [1, 2]

-- TODO needs to be fixed
-- ||| Sets the value of t0 at location [1, 3] to 99 
-- setExample : Tensor [3, 4]
-- setExample = set t0 [1, 3] 99

||| Takes the first two rows, and 1st column of t0
sliceExample : Tensor [2, 1] Double
sliceExample = take [2, 1] t0

-- Which will all fail if you go out of bounds
failing
  indexExampleFail : Double
  indexExampleFail = t1 @@ [7, 2]

failing
  sliceFail : Tensor [10, 2] Double
  sliceFail = take [10, 2] t0

{---------------------------------------
**And most importantly, you can do all of this with *non-cubical* tensors.** These describe tensors whose shape isn't rectangular/cubical, but can be branching/recursive/higher-order. We will see in a moment what that means. These tensors are described via 'containers' and the corresponding datatype named `CTensor` (standing for "Container Tensor").
We have already seen this datatype -- as matter of fact every `Tensor` we have seen was secretly desugared to `CTensor` internally:
---------------------------------------}
t0Again : CTensor [Vect 3, Vect 4] Double
t0Again = t0

{--------------------
Here `Vect` does not refer to `Vect` from `Data.Vect`, but rather the `Vect` container implemented [here](https://github.com/bgavran/TensorType/blob/main/src/Data/Container/Object/Instances.idr#L68).

Everything we can do with `Tensor` we can do with `CTensor`, including building concrete tensors:
--------------------}
t1again : CTensor [Vect 6] Double
t1again = ># [1,2,3,4,5,6]

{--------------------
The real power of container tensors comes from using other containers in the place of `Vect`. Here is a container `BinTree` of binary trees recast as a tree-tensor:

       60
      /  \
     7    2 
    / \
(-42)  46 
--------------------}
treeExample1 : CTensor [BinTree] Double
treeExample1 = ># Node 60 (Node 7 (Leaf (-42)) (Leaf 46)) (Leaf 2)

{--------------------
Unlike `Vect`, this container allows us to store an arbitrary number of elements. Here is another tree-tensor.

   5
  / \
100  4
--------------------}
treeExample2 : CTensor [BinTree] Double
treeExample2 = ># Node 5 (Leaf 100) (Leaf 4)

{--------------------
Perhaps surpisingly, all linear algebra operations follow smoothly. The example below is the _dot product of trees_. The fact that these trees don't have the same number of elements is irrelevant; what matters is that the container defining them (`BinTree`) is the same.
--------------------}
dotProductTree : CTensor [] Double
dotProductTree = dot treeExample1 treeExample2

{--------------------
We can do much more.
Here's a tree-tensor with values only on its leaves:
        *
      /   \
     *     2 
    / \
(-42)  46 
--------------------}
treeLeafExample : CTensor [BinTreeLeaf] Double
treeLeafExample = ># Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)

{--------------------
and here's a tree-tensor with values only on its nodes:
       60
      /  \
     7    *
    / \
   *   * 
--------------------}
treeNodeExample : CTensor [BinTreeNode] Double
treeNodeExample = ># Node 60 (Node 7 Leaf' Leaf')  Leaf'

||| And this can get very complex and nested, as `exTree3` and `exTree4` show.
||| But it still fully type-checked, and working as you'd expect.
treeExample3 : CTensor [BinTreeNode, Vect 2] Double
treeExample3 = ># Node [4,1] (Node [17, 4] Leaf' Leaf') Leaf'

treeExample4 : CTensor [BinTreeNode, BinTreeLeaf, Vect 3] Double
treeExample4 = >#
  Node (Node'
          (Leaf [1,2,3])
          (Leaf [4,5,6]))
    Leaf'
    (Node (Leaf [178, -43, 63]) Leaf' Leaf')

{--------------------
For instance, we can index into `treeExample1`:
       60
      /  \
     7    2  <---- indexing here is okay
    / \
(-42)  46 
--------------------}
indexTreeExample1 : Double
indexTreeExample1 = treeExample1 @@ [GoRight AtLeaf]

-- This will fail at compile-time if you try to index outside of the tree structure:
failing
  {--------------------
          *
        /   \
       *     2  
      / \     \
  (-42)  46    X   <---- indexing here throws an error
  --------------------}
  indexTreeExampleFail : Double
  indexTreeExampleFail = ex1 @@ [GoRight (GoRight AtLeaf)]


{--------------------
Likewise, you can perform reshapes, views, reversals, sorting and traversals of non-cubical tensors.
Here is the in-order traversal of `treeExample1` from above.
       60
      /  \
     7    2 
    / \
(-42)  46 

Can also use Utils.Traversals.inorder
--------------------}
traversalExample : CTensor [List] Double
traversalExample = restructure (wrapIntoVector inorder) treeExample1