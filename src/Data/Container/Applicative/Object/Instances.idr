module Data.Container.Applicative.Object.Instances

import Data.Container.Base
import Data.Container.Applicative.TreeUtils

||| Generalisation of Rose trees with a container of subtrees instead of
||| a list of subtrees. It's required that the container is a TensorMonoid
public export
ApplicativeRoseTree : {c : Cont} -> TensorMonoid c => Cont
ApplicativeRoseTree = (t : RoseTreeShape c) !> RoseTreePos c t

||| Same as above, but with data stored at nodes
public export
ApplicativeRoseTreeNode : {c : Cont} -> TensorMonoid c => Cont
ApplicativeRoseTreeNode = (t : RoseTreeShape c) !> RoseTreePosNode c t

||| Same as above, but with data stored at leaf
public export
ApplicativeRoseTreeLeaf : {c : Cont} -> TensorMonoid c => Cont
ApplicativeRoseTreeLeaf = (t : RoseTreeShape c) !> RoseTreePosNode c t

||| Rose trees with data stored at both nodes and leaves
public export
RoseTree : Cont
RoseTree = ApplicativeRoseTree {c=List}
  
||| Rose trees with data stored at nodes
public export
RoseTreeNode : Cont
RoseTreeNode = ApplicativeRoseTreeNode {c=List}
  
||| Rose trees with data stored at leaves
public export
RoseTreeLeaf : Cont
RoseTreeLeaf = ApplicativeRoseTreeLeaf {c=List}


{-
old rose tree implementation
namespace RoseTrees
  ||| Rose tree, a tree with a variable number of children.
  ||| This can likely be generalised to other Applicatives than List
  public export
  data RoseTreeShape : Type where
    LeafS : RoseTreeShape
    NodeS : List RoseTreeShape -> RoseTreeShape

  %runElab derive "RoseTreeShape" [Eq, Show]
  %name RoseTreeShape t, t1, t2, t3

  public export
  numLeaves : RoseTreeShape -> Nat
  numLeaves LeafS = 1
  numLeaves (NodeS ts) = sum (numLeaves <$> ts)
  
  public export
  numNodes : RoseTreeShape -> Nat
  numNodes LeafS = 0
  numNodes (NodeS ts) = 1 + sum (numNodes <$> ts)

  namespace NodesAndLeaves
    ||| Positions corresponding to both nodes and leaves within a RoseTreeShape
    public export
    data RoseTreePos : (t : RoseTreeShape) -> Type where
      AtLeaf : RoseTreePos LeafS
      AtNode : {ts : List RoseTreeShape} -> RoseTreePos (NodeS ts)
      SubTree : {ts : List RoseTreeShape} ->
        (i : Fin (length ts)) -> -- which subtree
        RoseTreePos (index' ts i) -> -- position in that subtree
        RoseTreePos (NodeS ts)

    -- For some reason the line below breaks?
    -- %runElab deriveIndexed "RoseTreePos" [Eq, Show]

  namespace Nodes
    ||| Positions corresponding to internal nodes within a RoseTreeNode shape.
    public export
    data RoseTreePosNode : (t : RoseTreeShape) -> Type where
      Done : {ts : List RoseTreeShape} -> RoseTreePosNode (NodeS ts)
      SubTree : {ts : List RoseTreeShape} ->
        (i : Fin (length ts)) -> -- which subtree
        RoseTreePosNode (index' ts i) -> -- position in that subtree
        RoseTreePosNode (NodeS ts)

    -- %runElab deriveIndexed "RoseTreePosNode" [Eq, Show]
  
  namespace Leaves
    ||| Positions corresponding to leaves within a RoseTreeLeaf shape.
    public export
    data RoseTreePosLeaf : (t : RoseTreeShape) -> Type where
      Done : RoseTreePosLeaf LeafS
      SubTree : {ts : List RoseTreeShape} ->
        (i : Fin (length ts)) -> -- which subtree
        RoseTreePosLeaf (index' ts i) -> -- position in that subtree
        RoseTreePosLeaf (NodeS ts)
  
    -- %runElab deriveIndexed "RoseTreePosLeaf" [Eq, Show]
 -}