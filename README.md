
# TensorType

[![build](https://github.com/bgavran/TypeSafe_Tensors/actions/workflows/build.yml/badge.svg)](https://github.com/bgavran/TypeSafe_Tensors/actions/workflows/build.yml)

> TLDR; NumPy reimagined with dependent types: native support for trees, braching and interaction

TensorType is a framework for pure functional tensor processing, implemented in Idris 2. It
* is **type-safe**: tensor shapes, indexing and contractions are checked at compile time
* **handles structured data natively**: supports tensors over trees, interaction protocols and arbitrary containers, instead of just rectangular arrays
* **supports named axes**: axes are first-class objects carrying names, checked for consistency at call sites
* **provides a familiar interface**: it aims to offer the standard NumPy/PyTorch API in a purely functional, dependently typed language

At the moment its main purpose is enabling rapid prototyping of structured neural network architectures. For instance, it is expressive enough to [implement generalised cross-attention](https://github.com/bgavran/TensorType/blob/main/src/NN/Architectures/Transformer/Attention.idr#L9) (as described in the [Generalised Transformers blog post](https://glaive-research.org/2025/02/11/Generalized-Transformers-from-Applicative-Functors.html)).

> [!NOTE]
> TensorType is in early stages of development; expect breaking changes. Named axes are not yet fully integrated, and TensorType is not yet performant. Down the line the goal is to obtain performance systematically, not at the expense of types, but [because of them](#Aim-of-TensorType).

* [Examples](#Examples)
* [Installation instructions](#Installation-instructions)
* [Aim of TensorType](#Aim-of-TensorType)
* [Technical details](#Technical-details)
* [Planned features](#Planned-features)

## Examples

(taken from `examples/BasicExamples.idr`)

Import `Data.Tensor` at the top of your file.

```idris
import Data.Tensor
```

Now you can construct tensors directly:

```idris
myVector : Tensor ["i" ~~> 5] Double
myVector = ># [1,2,3,4,5]
```

This is a vector of size `5`, with its axis named "i".

```idris
myMatrix : Tensor ["j" ~~> 3, "k" ~~> 4] Double
myMatrix = ># [ [0, 1, 2, 3]
              , [4, 5, 6, 7]
              , [8, 9, 10, 11]]
```

This is a matrix with dimensions `3 x 4` with its axes named "j" and "k". In both examples them `>#` is used to populate the tensor with concrete values.

If you load these up in the REPL (`pack repl examples/BasicExamples.idr`), you can print them:
```idris
BasicExamples> :exec printLn myVector
[1.0 2.0 3.0 4.0 5.0]
BasicExamples> :exec printLn myMatrix
[[ 0.0  1.0  2.0  3.0]
 [ 4.0  5.0  6.0  7.0]
 [ 8.0  9.0 10.0 11.0]]
```

You can use functions analogous to NumPy's, such as `np.arange` and `np.reshape`:

```idris
t1 : Tensor ["i" ~~> 6] Double
t1 = arange

t2 : Tensor ["i" ~~> 2, "j" ~~> 3] Double
t2 = reshape t1
```

These do what you might expect if you're familiar with NumPy:
```idris
BasicExamples> :exec printLn t1
[0.0 1.0 2.0 3.0 4.0 5.0]
BasicExamples> :exec printLn t2
[[0.0 1.0 2.0]
 [3.0 4.0 5.0]]
```

The difference from NumPy is that these operations are typechecked - meaning they will fail _at compile-time_ if you supply an array with the wrong shape.
```idris
failing
  failConcrete : Tensor ["j" ~~> 3, "k" ~~> 4] Double
  failConcrete = ># [ [0, 1, 2, 3, 999]
                    , [4, 5, 6, 7]
                    , [8, 9, 10, 11]]
failing
  failReshape : Tensor ["i" ~~> 7, "j" ~~> 2] Double
  failReshape = arange {n=7}
```

They will also fail if you inconsistently bind axis names, for instance if you bind the same name to two different sizes:

```idris
failing
  failBinding : Tensor ["j" ~~> 3, "j" ~~> 4] Double
  failBinding = ># [ [0, 1, 2, 3]
                   , [4, 5, 6, 7]
                   , [8, 9, 10, 11]]
```

You can perform all sorts of familiar numeric operations:

```idris
exampleSum : Tensor ["j" ~~> 3, "k" ~~> 4] Double
exampleSum = myMatrix + myMatrix

exampleOp : Tensor ["j" ~~> 3, "k" ~~> 4] Double
exampleOp = abs (- (myMatrix * myMatrix) <&> (+7))
```

including standard linear algebra:

```idris
dotExample : Tensor [] Double
dotExample = dot t1 (t1 <&> (+5))

matMulExample : Tensor ["i" ~~> 2, "k" ~~> 4] Double
matMulExample = matMul t2 myMatrix

transposeExample : Tensor ["k" ~~> 4, "j" ~~> 3] Double
transposeExample = transposeMatrix myMatrix
```

```idris
BasicExamples> :exec printLn dotExample
130.0
BasicExamples> :exec printLn matMulExample
[[20.0 23.0 26.0 29.0]
 [56.0 68.0 80.0 92.0]]
```

All of these types are checked before you run your program. For instance, you can't add tensors of different shapes, perform matrix multiplication if the dimensions of matrices don't match, or do any of these if you mislabel an axis.

```idris
failing
  sumFail : Tensor ["j" ~~> 3, "k" ~~> 4] Double
  sumFail = myMatrix + t1
  
failing
  matMulFail : Tensor ["i" ~~> 7] Double
  matMulFail = matMul myMatrix t1
```

Like in NumPy, you can safely index into tensors, set values of tensors, and perform slicing:

```idris
||| Retrieves the value of `myMatrix` at location [1, 2]
indexExample : Double
indexExample = myMatrix @@ [1, 2]

||| Sets the value of `myMatrix` at location [1, 3] to 99 
setExample : Tensor ["j" ~~> 3, "k" ~~> 4] Double
setExample = set myMatrix [1, 3] 99

||| Takes the first two rows, and 1st column of t0
sliceExample : Tensor ["j" ~~> 2, "k" ~~> 1] Double
sliceExample = take [2, 1] myMatrix
```

which will all fail if you go out of bounds:
```idris
failing
  indexExampleFail : Double
  indexExampleFail = t1 @@ [7, 2]

failing
  sliceFail : Tensor ["j" ~~> 10, "k" ~~> 2] Double
  sliceFail = take [10, 2] myMatrix
```

**All of the above also works with non-rectangular tensors.** These are tensors whose shape is not a list of numbers, but a list of *containers*. A container can model a tree, an inductive type, a continuation, and all sorts of different things.
As a matter of fact, our previous syntax for defining axes (`~~>`) was behind the scenes desugaring to a container-based one (which is `~>`).
We have been using it all along.
Let's see `myMatrix` in this new form:

```idris
myMatrixAgain : Tensor ["j" ~> Vect 3, "k" ~> Vect 4] Double
myMatrixAgain = myMatrix
```

Here `Vect` does not refer to `Vect` from `Data.Vect`, but rather the `Vect` container implemented [here](https://github.com/bgavran/TensorType/blob/main/src/Data/Container/Base/Object/Instances.idr#L68).

Everything we've seen above can be recast with this new type explicitly:

```idris
t1again : Tensor ["i" ~> Vect 6] Double
t1again = arange
```

The real power of container tensors comes from using other containers in the place of `Vect`. Here is a container `BinTree` of binary trees recast as a tree-tensor:

```idris
treeExample1 : Tensor ["myTree" ~> BinTree] Double
treeExample1 = ># Node 60 (Node 7 (Leaf (-42)) (Leaf 46)) (Leaf 2)
```

We can print it out in the same way, and observe its branching shape:
```idris
BasicExamples> :exec printLn treeExample1
60.0
│
├─ 7.0
│  │
│  ├─ -42.0
│  │
│  └─ 46.0
│
└─ 2.0
```

Here is another tree-tensor with a different shape:

```idris
treeExample2 : Tensor ["myTree" ~> BinTree] Double
treeExample2 = ># Node 5 (Leaf 100) (Leaf 4)
```

```idris
BasicExamples> :exec printLn treeExample2
5.0
│
├─ 100.0
│
└─ 4.0
```

Perhaps surprisingly, all linear algebra operations follow smoothly. The example below is the _dot product of trees_. The fact that these trees don't have the same number of elements is irrelevant; what matters is that the container defining them (`BinTree`) is the same.

```idris
dotProductTree : Tensor [] Double
dotProductTree = dot treeExample1 treeExample2
```

```idris
BasicExamples> :exec printLn dotProductTree
1408.0
```

We can do much more. Here's a tree-tensor with values only on its leaves:

```idris
treeLeafExample : Tensor ["myTree" ~> BinTreeLeaf] Double
treeLeafExample = ># Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)
```

```idris
BasicExamples> :exec printLn treeLeafExample
·
│
├─ ·
│  │
│  ├─ -42.0
│  │
│  └─ 46.0
│
└─ 2.0
```

and here's a tree-tensor with values only on its nodes:

```idris
treeNodeExample : Tensor ["myTree" ~> BinTreeNode] Double
treeNodeExample = ># Node 60 (Node 7 Leaf' Leaf')  Leaf'
```

```idris
BasicExamples> :exec printLn treeNodeExample
60.0
│
├─ 7.0
│  │
│  ├─ ·
│  │
│  └─ ·
│
└─ ·
```

This can get complex and nested, as `treeExample3` and `treeExample4` show.

```idris
treeExample3 : Tensor ["myTree" ~> BinTreeNode, "j" ~> Vect 2] Double
treeExample3 = ># Node [4,1] (Node [17, 4] Leaf' Leaf') Leaf'

treeExample4 : Tensor ["myTree"     ~> BinTreeNode,
                       "myTreeLeaf" ~> BinTreeLeaf,
                       "k"          ~> Vect 3] Double
treeExample4 = >#
  Node (Node'
          (Leaf [1,2,3])
          (Leaf [4,5,6]))
    Leaf'
    (Node (Leaf [178, -43, 63]) Leaf' Leaf')
```


```idris
BasicExamples> :exec printLn treeExample4
╔════════════════╗
║·               ║
║│               ║
║├─ [1.0 2.0 3.0]║
║│               ║
║└─ [4.0 5.0 6.0]║
╚════════════════╝
│
├─ ·
│
└─ ╔═══════════════════╗
   ║[178.0 -43.0  63.0]║
   ╚═══════════════════╝
   │
   ├─ ·
   │
   └─ ·
```

But all of this is still fully type-checked and works as you'd expect.
For instance, we can index into `treeExample1`:
```idris
{- 
60.0
│
├─ 7.0
│  │
│  ├─ -42.0
│  │
│  └─ 46.0
│
└─ 2.0     <---- indexing here is okay
-}
indexTreeExample1 : Double
indexTreeExample1 = treeExample1 @@ [GoRight AtLeaf]
```

This will fail _at compile-time_ if you try to index outside of the tree structure:

```idris
failing
  {- 
  60.0
  │
  ├─ 7.0
  │  │
  │  ├─ -42.0
  │  │
  │  └─ 46.0
  │
  └─ 2.0
      │
      └─ X  <---- indexing here throws an error
  -}
  indexTreeExample1Fail : Double
  indexTreeExample1Fail = treeExample1 @@ [GoRight (GoRight AtLeaf)]
```

Likewise, you can perform reshapes, views, reversals, sorting and traversals of non-cubical tensors.
Here is the in-order traversal of `treeExample1` from above.

```idris
traversalExample : Tensor ["myList" ~> List] Double
traversalExample = restructure (wrapIntoVector inorder) treeExample1
```

```idris
BasicExamples> :exec printLn traversalExample
[-42.0, 7.0, 46.0, 60.0, 2.0]
```

All of these can be used to define novel network architectures, see [src/Architectures](https://github.com/bgavran/TensorType/tree/main/src/NN/Architectures) for examples.

## Installation instructions

It is recommended to manage the installation of this package (and generally, Idris 2) using the package manager [pack](https://github.com/stefan-hoeck/idris2-pack). The instructions below assume you've got both Idris 2 and pack installed.

**If you want to just try it out in the REPL:**
1. Clone the repository, and `cd` into it.
2. Run `pack repl examples/BasicExamples.idr`.
3. That's it!

**To use TensorType in your project:**
1. Add `tensortype` to the `depends` argument in your project's `.ipkg` file. (See `examples/tensortype-examples.ipkg` for an example)
2. Include `import Data.Tensor` at the top of your source files.
3. That's it!

## Aim of TensorType

Attempts to bring deep learning to statically typed languages have struggled with expressiveness and ergonomics, typically only replicating what exists without imagining what can be. TensorType aims to do both: provide a practical, type-safe tensor library, and enable fundamentally new capabilities. Specifically, the aim is to:

> Enable type-driven development of structured neural network architectures.

Existing frameworks like PyTorch, TensorFlow and JAX -- by virtue of being implemented in a dynamically typed language -- do not come with [elaboration facilities](https://dl.acm.org/doi/10.1145/2951913.2951932) that give programmers powerful tools to inspect and construct programs, nor do they enable writing highly generic programs without sacrificing reliability.

> Achieve performance not at the expense of types, but because of them.

The goal is to move towards CUDA-level performance of generalised tensor contractions without sacrificing type safety, modularity, or our ability to reason about code. Types are meta-information about programs, and this information permits static analysis not available to untyped frameworks.
This especially holds for non-rectangular tensors, which are at the moment only scarcely explored, without any existing CUDA packages or optimisation algorithms.


## Technical details

TensorType's implementation hinges on three interdependent components:

* **Containers** for **well-typed indexing of non-cubical tensors**: they allow us to validate that an index into a generalised tensor is not out of bounds at compile-time. Doing this with cubical containers is easy since they expose the size information at the type level (i.e. `Tensor ["i" ~> Vect 2] Double`), but once we move on to the world of applicative functors this is no longer the case. Checking that an index into a `Tensor ["b" ~> BinTreeNode] Double` is not out of bounds is only possible if the underlying functor additionally comes equipped with the data of the valid set of "shapes" and the valid "positions" for that shape. This is equivalent to asking that the functor is polynomial, or equivalently that the functor is the extension of some container.
* **Applicative functors** for **generalised linear algebra**: they allow us to perform generalised linear algebra operations as described in the [Applicative Programming with Naperian Functors](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf) paper.
* **Dependent lenses** for **reshaping and traversing operations**: they allow us to define morphisms of containers, and therefore generalised tensor reshaping operations that do not operate on the content of the data, only the shape. These include views, reshapes, and traversals, and many other operations that appear in libraries like NumPy.

To find out more about the container aspect of TensorType, check out the following [blog post](https://glaive-research.org/2026/01/21/Generalised-tensors.html).


The training harness and neural network aspects are based on the research from my PhD thesis [Fundamental Components of Deep Learning: A category-theoretic approach](https://arxiv.org/abs/2403.13001).


## Planned features

* Functionality:
  * Full support for persistent named axes and tensor operations involving them
  * Type-safe einsum
  * Type-safe broadcasting, stacking, padding, etc. for both cubical and applicative tensors
  * Common linear algebra operations
  * Neural network facilities:
    * Automatic differentiation (forward/backward mode AD, differentiation through products, sums, (co)inductive types)
    * Parameter management (initialisation, updates)
* Efficiency:
  * In-place operations/views, and research on feasibility of linear types for doing so
  * Support for different tensor representation in the backend, and their tracking at the type level:
    * Strided (at various levels; boxed, bytes, but also column/row major, including research on feasibility of [strides for non-cubical tensors](https://en.wikipedia.org/wiki/Iliffe_vector))
    * Sparse
    * Tabulated/delayed (for Naperian tensors)
  * Systematic optimisation via a FFI to a low-level kernel
* Other:
  * Pretty printing of tensors as described [here](https://blog.ezyang.com/2025/10/draw-high-dimensional-tensors-as-a-matrix-of-matrices/)
  * Better error reporting
  * Documentation

## Contact

Contributions and collaboration are welcome, feel free to submit pull requests/issues or get in touch directly.