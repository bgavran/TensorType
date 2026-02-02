module Data.Container.Base.Morphism.Instances

import Data.Fin
import Data.Fin.Split

import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Object.Instances

import Data.Layout
import Misc

public export
Costate : {0 c : Cont} ->
  (s : (x : c.Shp) -> c.Pos x) ->
  c =%> Scalar
Costate s = !% \x => (() ** \() => s x)

public export
fromCostate : {0 c : Cont} ->
  c =%> Scalar ->
  (x : c.Shp) -> c.Pos x
fromCostate f x = snd ((%! f) x) ()


public export
rightUnit : (c >< Scalar) =%> c
rightUnit = !% \(x, ()) => (x ** \x' => (x', ()))

||| Ext is a functor of type Cont -> [Type, Type]
||| On objects it maps a container to a polynomial functor
||| On morphisms it maps a dependent lens to a natural transformation
||| This is the action on morphisms
public export
extMap : {c, d : Cont} ->
  c =%> d ->
  Ext c a -> Ext d a
extMap (!% f) (sh <| index) = let (y ** ky) = f sh
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

||| Layout-aware isomorphism between a cubical tensor and a vector
||| Uses the specified layout order for index mapping
public export
flatten : {shape : List Nat} ->
  LayoutOrder ->
  Tensor (Vect <$> shape) =%> Vect (prod shape)
flatten {shape = []} _ = !% \() => (() ** \FZ => ())
flatten {shape = (s :: ss)} lo = !% \(() <| t) => (() ** \idx => 
  let (!% recBackward) = flatten {shape = ss} lo
      (i, rest) = splitFinProd lo idx
      (_ ** backRec) = recBackward (t i)
  in (i ** backRec rest))

||| Unflattens a vector into a cubical tensor of specific shape
||| Is generic over layout order
public export
unflatten : {shape : List Nat} ->
  LayoutOrder ->
  Vect (prod shape) =%> Tensor (Vect <$> shape)
unflatten {shape = []} lo = !% \() => (() ** \() => FZ)
unflatten {shape = (s :: ss)} lo =
  let (!% f) = unflatten {shape = ss} lo
      (innerShape ** innerBack) = f ()
  in !% \() => ((() <| \_ => innerShape) ** (\(cp ** restPos) =>
    indexFinProd lo cp (innerBack restPos)))

||| This is simply a rewrite!
public export
reshapeFlattenedTensor : {oldShape, newShape : List Nat} ->
  {auto prf : prod oldShape = prod newShape} ->
  Vect (prod oldShape) =%> Vect (prod newShape)
reshapeFlattenedTensor = !% \() => (() ** \i => rewrite prf in i)

||| Reshapes a cubical tensor by first flattening it to a linear representation,
||| casting the type to the new shape, and then unflattening it back
||| Is generic over layout order
public export
reshape : {oldShape, newShape : List Nat} ->
  LayoutOrder ->
  {auto prf : prod oldShape = prod newShape} ->
  Tensor (Vect <$> oldShape) =%> Tensor (Vect <$> newShape)
reshape lo = flatten lo %>> reshapeFlattenedTensor %>> unflatten lo

  
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


  -- TODO reshape commented out for the same reason as reshapeTensorA is
  -- public export
  -- reshape : {oldShape, newShape : List Nat} ->
  --   Tensor oldShape a ->
  --   {auto prf : prod oldShape = prod newShape} ->
  --   Tensor newShape a

-- Need to do some rewriting for preorder
public export
preorderBinTreeNode : (b : BinTreeShape) -> Fin (numNodes b) -> BinTreePosNode b
preorderBinTreeNode (NodeS lt rt) x = ?preorderBinTreeNode_rhs_1
--preorderBinTreeNode (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
--  _ | Left p = ?whl
--  _ | Right FZ = ?whn
--  _ | Right (FS g) = ?whr

public export
maybeToList : Maybe =%> List
maybeToList = !% \b => case b of 
  False => (0 ** absurd)
  True => (1 ** \_ => ())


-- public export
-- traverseLeaf : (x : BinTreeShape) -> FinBinTreeLeaf x -> Fin (numLeaves x)
-- traverseLeaf LeafS Done = FZ
-- traverseLeaf (NodeS lt rt) (GoLeft x) = weakenN (numLeaves rt) (traverseLeaf lt x)
-- traverseLeaf (NodeS lt rt) (GoRight x) = shift (numLeaves lt) (traverseLeaf rt x)
-- 