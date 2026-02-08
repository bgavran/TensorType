module Data.Container.Applicative.Extension.Instances

import Data.Container.Base
import Data.Container.Applicative.Object.Instances

||| Isomorphic to Data.Tree.ApplicativeRoseTree (TODO)
public export
ApplicativeRoseTree' : {c : Cont} -> TensorMonoid c => Type -> Type
ApplicativeRoseTree' = Ext (ApplicativeRoseTree {c=c})

public export
ApplicativeRoseTreeNode' : {c : Cont} -> TensorMonoid c => Type -> Type
ApplicativeRoseTreeNode' = Ext (ApplicativeRoseTreeNode {c=c})

public export
ApplicativeRoseTreeLeaf' : {c : Cont} -> TensorMonoid c => Type -> Type
ApplicativeRoseTreeLeaf' = Ext (ApplicativeRoseTreeLeaf {c=c})


||| Isomorphic to Data.Tree.RoseTree
public export
RoseTree' : Type -> Type
RoseTree' = Ext RoseTree

||| Isomorphic to Data.Tree.RoseTreeNode (TODO)
public export
RoseTreeNode' : Type -> Type
RoseTreeNode' = Ext RoseTreeNode

||| Isomorphic to Data.Tree.RoseTreeLeaf (TODO)
public export
RoseTreeLeaf' : Type -> Type
RoseTreeLeaf' = Ext RoseTreeLeaf

