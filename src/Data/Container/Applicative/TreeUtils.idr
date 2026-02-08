module Data.Container.Applicative.TreeUtils


import Data.Container.Base


||| Requires a TensorMonoid (Applicative) to even be stated
namespace RoseTree
  public export
  data RoseTreeShape : (c : Cont) -> TensorMonoid c => Type where
    LeafS : TensorMonoid c => RoseTreeShape c
    NodeS : TensorMonoid c => c `fullOf` (RoseTreeShape c) -> RoseTreeShape c

  public export
  numLeaves : TensorMonoid c => Foldable (Ext c) => RoseTreeShape c -> Nat
  numLeaves LeafS = 1
  numLeaves (NodeS exts) = sum (numLeaves <$> exts)

  public export
  numNodes : TensorMonoid c => Foldable (Ext c) => RoseTreeShape c -> Nat
  numNodes LeafS = 0
  numNodes (NodeS exts) = 1 + sum (numNodes <$> exts)

  namespace NodesAndLeaves
    ||| Positions corresponding to both nodes and leaves within a RoseTreeShape
    public export
    data RoseTreePos :
      (c : Cont) -> TensorMonoid c => RoseTreeShape c -> Type where
      AtLeaf : TensorMonoid c => RoseTreePos c LeafS
      AtNode : TensorMonoid c => {ts : c `fullOf` (RoseTreeShape c)} ->
        RoseTreePos c (NodeS ts)
      SubTree : TensorMonoid c => {ts : c `fullOf` (RoseTreeShape c)} ->
        (ps : c.Pos (shapeExt ts)) -> -- position in a given list
        RoseTreePos c (index ts ps) -> -- position in the shape of RoseTree at a location specified by ps
        RoseTreePos c (NodeS ts)


  namespace Nodes
    public export
    data RoseTreePosNode :
      (c : Cont) -> TensorMonoid c => RoseTreeShape c -> Type where
      AtNode : TensorMonoid c => {ts : c `fullOf` (RoseTreeShape c)} ->
        RoseTreePosNode c (NodeS ts)
      SubTree : TensorMonoid c => {ts : c `fullOf` (RoseTreeShape c)} ->
        (ps : c.Pos (shapeExt ts)) -> -- position in a given list
        RoseTreePosNode c (index ts ps) -> -- position in the sub-tree at the above defined position
        RoseTreePosNode c (NodeS ts)

  namespace Leaves
    public export
    data RoseTreePosLeaf :
      (c : Cont) -> TensorMonoid c => RoseTreeShape c -> Type where
      AtLeaf : TensorMonoid c => RoseTreePosLeaf c LeafS
      SubTree : TensorMonoid c => {ts : c `fullOf` (RoseTreeShape c)} ->
        (ps : c.Pos (shapeExt ts)) -> -- position in a given list
        RoseTreePosLeaf c (index ts ps) -> -- position in the sub-tree at the above defined position
        RoseTreePosLeaf c (NodeS ts)