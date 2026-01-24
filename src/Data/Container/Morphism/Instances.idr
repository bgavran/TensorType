module Data.Container.Morphism.Instances

import Data.Fin
import Data.Fin.Split
import Data.List.Quantifiers

import Data.Container.Object.Instances
import Data.Container.Morphism.Definition
import Data.Container.Extension.Definition

import Data.Layout
import Misc

||| Ext is a functor of type Cont -> [Type, Type]
||| On objects it maps a container to a polynomial functor
||| On morphisms it maps a dependent lens to a natural transformation
||| This is the action on morphisms
public export
extMap : {c, d : Cont} ->
  c =%> d ->
  Ext c a -> Ext d a
extMap f (sh <| index) = let (y ** ky) = (%!) f sh
                         in y <| (index . ky)


||| Wraps a dependent lens `c =%> d`
||| into one of type `c >@ Scalar =%> d >@ Scalar`
||| Needed because `c >@ Scalar` isn't automatically reduced to `c`
public export
wrapIntoVector : {c, d : Cont} ->
  c =%> d ->
  Tensor [c] =%> Tensor [d]
wrapIntoVector (!% f) =
  !% \e => let (y ** ky) = f (shapeExt e)
           in (y <| \_ => () ** \(cp ** ()) => (ky cp ** ()))


||| Layout-aware depenent lens flattening a cubical tensor
public export
flattenCubical : {shape : List Cont} ->
  (ac : All IsCubical shape) =>
  LayoutOrder ->
  Tensor shape =%> Vect (size shape)
flattenCubical {shape = [], ac=[]} _ = !% \() => (() ** \FZ => ())
flattenCubical {shape = (_ :: ss), ac=((MkIsCubical n) :: as)} lo
  = !% \(() <| t) => (() ** \idx =>
      let (!% recBackward) = flattenCubical {shape = ss} lo
          (i, rest) = splitFinProd lo idx
          (_ ** backRec) = recBackward (t i)
      in (i ** backRec rest))

||| Layout-aware dependent lens unflattening a tensor
public export
unflattenCubical : {shape : List Cont} ->
  (ac : All IsCubical shape) =>
  LayoutOrder ->
  Vect (size shape) =%> Tensor shape
unflattenCubical {shape = [], ac=[]} lo = !% \() => (() ** \() => FZ)
unflattenCubical {shape = (_ :: ss), ac=((MkIsCubical n) :: as)} lo =
  let (!% f) = unflattenCubical {shape = ss} lo
      (innerShape ** innerBack) = f ()
  in !% \() => ((() <| \_ => innerShape) ** (\(cp ** restPos) =>
    indexFinProd lo cp (innerBack restPos)))

||| This is simply a rewrite!
public export
reshapeFlattenedTensor : {oldShape, newShape : List Cont} ->
  (oldAc : All IsCubical oldShape) => (newAc : All IsCubical newShape) =>
  {auto prf : size oldShape = size newShape} ->
  Vect (size oldShape) =%> Vect (size newShape)
reshapeFlattenedTensor = !% \() => (() ** \i => rewrite prf in i)

||| Reshapes a cubical tensor by first flattening it to a linear representation,
||| casting the type to the new shape, and then unflattening it back
||| Is generic over layout order
public export
reshape : {oldShape, newShape : List Cont} ->
  (oldAc : All IsCubical oldShape) => (newAc : All IsCubical newShape) =>
  LayoutOrder ->
  {auto prf : size oldShape = size newShape} ->
  Tensor oldShape =%> Tensor newShape
reshape lo = flattenCubical lo
         %>> reshapeFlattenedTensor
         %>> unflattenCubical lo

-- need to organise this
namespace BinTree
  public export
  inorderBackward : (b : BinTreeShape) ->
    Fin (numNodesAndLeaves b) ->
    BinTreePos b
  inorderBackward LeafS FZ = AtLeaf
  inorderBackward (NodeS lt rt) n with (strengthenN {m=numNodesAndLeaves lt} n)
     _ | Left p = GoLeft (inorderBackward lt p)
     _ | Right FZ = AtNode
     _ | Right (FS g) = GoRight (inorderBackward rt g)


  public export
  inorder : BinTree =%> List
  inorder = !% \b => (numNodesAndLeaves b ** inorderBackward b)

namespace BinTreeNode
  public export
  inorderBackward : (b : BinTreeShape) ->
    Fin (numNodes b) ->
    BinTreePosNode b
  inorderBackward (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
    _ | Left p = GoLeft (inorderBackward lt p)
    _ | Right FZ = AtNode
    _ | Right (FS g) = GoRight (inorderBackward rt g)

  ||| Traverses a binary tree container in order, producing a list container
  public export
  inorder : BinTreeNode =%> List
  inorder = !% \b => (numNodes b ** inorderBackward b)

  -- Need to do some rewriting for preorder
  public export
  preorderBinTreeNode : (b : BinTreeShape) ->
    Fin (numNodes b) -> BinTreePosNode b
  preorderBinTreeNode (NodeS lt rt) x = ?preorderBinTreeNode_rhs_1
  --preorderBinTreeNode (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
  --  _ | Left p = ?whl
  --  _ | Right FZ = ?whn
  --  _ | Right (FS g) = ?whr

-- public export
-- traverseLeaf : (x : BinTreeShape) -> FinBinTreeLeaf x -> Fin (numLeaves x)
-- traverseLeaf LeafS Done = FZ
-- traverseLeaf (NodeS lt rt) (GoLeft x) = weakenN (numLeaves rt) (traverseLeaf lt x)
-- traverseLeaf (NodeS lt rt) (GoRight x) = shift (numLeaves lt) (traverseLeaf rt x)
-- 

public export
maybeToList : Maybe =%> List
maybeToList = !% \b => case b of 
  False => (0 ** absurd)
  True => (1 ** \_ => ())