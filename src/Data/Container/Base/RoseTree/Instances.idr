module Data.Container.Base.RoseTree.Instances

import Data.Fin
import Data.Vect
import Data.List.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Properties.Definition
import Data.Container.Base.Product.Definition
import Data.Container.Base.Object.Instances
import Data.Container.Base.Morphism.Instances
import Data.Container.Base.Extension.Instances
import Data.Container.Base.Properties.Instances
import Data.Container.Base.Monoid.Definition
import Data.Container.Base.Monoid.Instances
import Data.Container.Base.RoseTree.Definition

import Data.Trees

||| Generalisation of Rose trees with a container of subtrees instead of
||| a list of subtrees. It's required that the container is a TensorMonoid
public export
ApplicativeRoseTree : TensorMonoid c => Cont
ApplicativeRoseTree = (t : RoseTreeShape c) !> RoseTreePos c t

||| Same as above, but with data stored at nodes
public export
ApplicativeRoseTreeNode : TensorMonoid c => Cont
ApplicativeRoseTreeNode = (t : RoseTreeShape c) !> RoseTreePosNode c t

||| Same as above, but with data stored at leaf
public export
ApplicativeRoseTreeLeaf : TensorMonoid c => Cont
ApplicativeRoseTreeLeaf = (t : RoseTreeShape c) !> RoseTreePosLeaf c t

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


||| Isomorphic to Data.Tree.ApplicativeRoseTree (TODO)
public export
ApplicativeRoseTree' : TensorMonoid c => Type -> Type
ApplicativeRoseTree' = Ext (ApplicativeRoseTree {c=c})

public export
ApplicativeRoseTreeNode' : TensorMonoid c => Type -> Type
ApplicativeRoseTreeNode' = Ext (ApplicativeRoseTreeNode {c=c})

public export
ApplicativeRoseTreeLeaf' : TensorMonoid c => Type -> Type
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



public export covering
fromRoseTreeSame : RoseTreeSame a -> RoseTree' a
fromRoseTreeSame (Leaf a) = LeafS <| \_ => a
fromRoseTreeSame (Node a rts) =
  let t = fromRoseTreeSame <$> fromList rts
  in NodeS (shapeExt <$> t) <| \case
    AtNode => a
    SubTree ps posSt =>
      let rw1 : (shapeExt t = shapeExt (shapeExt <$> t)) := sym (mapShapeExt t)
          rw2 : (shapeExt (index t (rewrite sym (mapShapeExt {f=shapeExt} t) in ps)) = index (shapeExt <$> t) ps) := mapIndexCont {c=List} {f=shapeExt} t ps
      in index
      (index t (rewrite rw1 in ps))
      (rewrite rw2 in posSt)
      -- for some reason all the explicit type annotations above are needed
      -- to convince the typechecker

public export covering
toRoseTreeSame : RoseTree' a -> RoseTreeSame a
toRoseTreeSame (LeafS <| contentAt) = Leaf (contentAt AtLeaf)
toRoseTreeSame (NodeS (len <| content) <| contentAt)
  = Node (contentAt AtNode)
         (toList $ toRoseTreeSame 
                <$> (\i => content i <| contentAt . SubTree i)
                <$> positionsCont)

public export covering
IsConcrete RoseTree where
  func = RoseTreeSame
  functorInstance = %search
  fromConcreteTy = fromRoseTreeSame
  toConcreteTy = toRoseTreeSame


||| In `Data.Tree` we have analogos maps that need to be translated here
public export
TensorMonoid c => TensorMonoid (ApplicativeRoseTree {c=c}) where
  tensorN = !% \() => (LeafS ** \_ => ())
  tensorM = !% \(lt, rt) => ?applicativeRoseTree_tensorM

public export
TensorMonoid c => TensorMonoid (ApplicativeRoseTreeLeaf {c=c}) where
  tensorN = ?applicativeRoseTreeLeaf_tensorN
  tensorM = ?applicativeRoseTreeLeaf_tensorM

-- Node version likely does not exist?
public export
TensorMonoid c => TensorMonoid (ApplicativeRoseTreeNode {c=c}) where
  tensorN = ?applicativeRoseTreeNode_tensorN
  tensorM = ?applicativeRoseTreeNode_tensorM

  -- public export
  -- ApplicativeRoseTree : ContA -> ContA
  -- ApplicativeRoseTree c = (#) (ApplicativeRoseTree c)


-- namespace RoseTreeInstances
--   -- TODO this should be superseeded by the general applicative instance above?
--   public export
--   liftA2RoseTree' : RoseTree' a -> RoseTree' b -> RoseTree' (a, b)
--   liftA2RoseTree' t1 t2 = fromRoseTreeSame $
--     liftA2RoseTreeSame (toRoseTreeSame t1) (toRoseTreeSame t2)
-- 
--   public export
--   Applicative RoseTree' where
--     pure a = LeafS <| \_ => a
--     fs <*> vs = uncurry ($) <$> liftA2RoseTree' fs vs
