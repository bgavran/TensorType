module Data.Container.Base.TreeUtils

import Decidable.Equality
import Language.Reflection
import Derive.Prelude

import Data.Container.Base.Object.Definition
import Data.Container.Base.Extension.Definition

import Data.Container.SubTerm

%language ElabReflection

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
This file defines the types of shapes and positions 
for various tree types for usage in containers.
All of the trees here are *finite*.

Specifically, this file defines the type of shapes of 
* Binary trees, together with the type of positions for
  * Binary trees with data stored both at nodes and leaves
  * Binary trees with data stored at nodes only
  * Binary trees with data stored at leaves only
* Rose trees, together with the type of positions for
  * Rose trees with data stored both at nodes and leaves
  * Rose trees with data stored at nodes only
  * Rose trees with data stored at leaves only
-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}


namespace BinaryTrees
  ||| Shapes of binary trees
  public export
  data BinTreeShape : Type where
    LeafS : BinTreeShape
    NodeS : BinTreeShape -> BinTreeShape -> BinTreeShape

  %runElab derive "BinTreeShape" [Eq, Show]
  %name BinTreeShape b, b1, b2, b3, b4, b5

  public export
  numLeaves : BinTreeShape -> Nat
  numLeaves LeafS = 1
  numLeaves (NodeS lt rt) = numLeaves lt + numLeaves rt
  
  public export
  numNodes : BinTreeShape -> Nat
  numNodes LeafS = 0
  numNodes (NodeS lt rt) = numNodes lt + (1 + numNodes rt)

  public export
  numNodesAndLeaves : BinTreeShape -> Nat
  numNodesAndLeaves LeafS = 1
  numNodesAndLeaves (NodeS lt rt)
    = numNodesAndLeaves lt + (1 + numNodesAndLeaves rt)
  
  namespace NodesAndLeaves
    ||| Positions corresponding to both nodes and leaves within a BinTreeShape
    public export
    data BinTreePos : (b : BinTreeShape) -> Type where
      AtLeaf : BinTreePos LeafS
      AtNode : {l, r : BinTreeShape} -> BinTreePos (NodeS l r)
      GoLeft : {l, r : BinTreeShape} -> BinTreePos l -> BinTreePos (NodeS l r)
      GoRight : {l, r : BinTreeShape} -> BinTreePos r -> BinTreePos (NodeS l r)

    %runElab deriveIndexed "BinTreePos" [Eq, Show]

    ||| Check if a term is a subterm of another term
    ||| t1 < t2 means that t2 > t1
    public export
    MOrd (BinTreePos b) where
      mcompare AtLeaf AtLeaf = Just EQ
      mcompare AtNode AtNode = Just EQ
      mcompare (GoLeft b1) (GoLeft b2) = mcompare b1 b2
      mcompare (GoRight b1) (GoRight b2) = mcompare b1 b2
      mcompare AtNode (GoLeft _) = Just LT
      mcompare AtNode (GoRight _) = Just LT
      mcompare (GoLeft _) AtNode = Just GT
      mcompare (GoRight _) AtNode = Just GT
      mcompare (GoLeft _) (GoRight _) = Nothing -- they diverge
      mcompare (GoRight _) (GoLeft _) = Nothing -- they diverge
      -- for quantitave version of MOrd the last two should map to BinTreePos b extende with a negative direction


  namespace Nodes
    ||| Positions corresponding to nodes within a BinTreeNode shape.
    public export
    data BinTreePosNode : (b : BinTreeShape) -> Type where
      AtNode : {l, r : BinTreeShape} -> BinTreePosNode (NodeS l r)
      GoLeft  : {l, r : BinTreeShape} -> BinTreePosNode l -> BinTreePosNode (NodeS l r)
      GoRight  : {l, r : BinTreeShape} -> BinTreePosNode r -> BinTreePosNode (NodeS l r)

    %runElab deriveIndexed "BinTreePosNode" [Eq, Show]

    public export
    MOrd (BinTreePosNode b) where
      mcompare AtNode AtNode = Just EQ
      mcompare (GoLeft b1) (GoLeft b2) = mcompare b1 b2
      mcompare (GoRight b1) (GoRight b2) = mcompare b1 b2
      mcompare AtNode (GoLeft _) = Just LT
      mcompare AtNode (GoRight _) = Just LT
      mcompare (GoLeft _) AtNode = Just GT
      mcompare (GoRight _) AtNode = Just GT
      mcompare (GoLeft _) (GoRight _) = Nothing -- they diverge
      mcompare (GoRight _) (GoLeft _) = Nothing -- they diverge
  
  namespace Leaves
    ||| Positions corresponding to leaves within a BinTreeShape 
    public export
    data BinTreePosLeaf : (b : BinTreeShape) -> Type where
      AtLeaf : BinTreePosLeaf LeafS
      GoLeft : {l, r : BinTreeShape} -> BinTreePosLeaf l -> BinTreePosLeaf (NodeS l r)
      GoRight : {l, r : BinTreeShape} -> BinTreePosLeaf r -> BinTreePosLeaf (NodeS l r)

    %runElab deriveIndexed "BinTreePosLeaf" [Eq, Show]

    public export
    MOrd (BinTreePosLeaf b) where
      mcompare AtLeaf AtLeaf = Just EQ
      mcompare (GoLeft b1) (GoLeft b2) = mcompare b1 b2
      mcompare (GoRight b1) (GoRight b2) = mcompare b1 b2
      mcompare (GoLeft _) (GoRight _) = Nothing -- they diverge
      mcompare (GoRight _) (GoLeft _) = Nothing -- they diverge