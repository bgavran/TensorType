module Data.Container.Base.Extension.Instances

import Data.DPair
import Data.Vect

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Product.Definition

import Data.Container.Base.Object.Instances
import Data.Container.Base.TreeUtils

import Data.Trees
import Data.Fin.Split

-- import Data.Functor.Naperian
import Misc

%hide Data.Vect.fromList
%hide Prelude.toList
%hide Prelude.(<|)

-- todo are these necessary still?
namespace ExtensionsOfMainExamples
  ||| Isomorphic to the Identity
  public export
  Scalar' : Type -> Type
  Scalar' = Ext Scalar

  ||| Isomorphic to Pair
  public export
  Pair' : Type -> Type
  Pair' = Ext Pair
  
  ||| Isomorphic to Either
  public export
  Either' : Type -> Type
  Either' = Ext Either

  ||| Isomorphic to Maybe
  public export
  Maybe' : Type -> Type
  Maybe' = Ext Maybe
  
  ||| Isomorphic to List
  public export
  List' : Type -> Type
  List' = Ext List

  ||| Isomorphic to Vect
  public export
  Vect' : (n : Nat) -> Type -> Type
  Vect' n = Ext (Vect n)

  ||| Isomorphic to Stream
  public export
  Stream' : Type -> Type
  Stream' = Ext Stream

  ||| Isomorphic to Data.Tree.BinTreeSame
  public export
  BinTree' : Type -> Type
  BinTree' = Ext BinTree

  ||| Isomorphic to Data.Tree.BinTreeNode
  public export
  BinTreeNode' : Type -> Type
  BinTreeNode' = Ext BinTreeNode
  
  ||| Isomorphic to Data.Tree.BinTreeLeaf
  public export
  BinTreeLeaf' : Type -> Type
  BinTreeLeaf' = Ext BinTreeLeaf

  {-
  Technically it is possible to a) use the alias that is below, and b) define Tensor' here, but a decision was made not to do any of these.
  Rather, Tensor' was defined as a record, and this was done in Data.Tensor as
  in most linear algebra operations explicit and cumbersome shape annotations 
  would have been otherwise necessary. Likewise, the definition of usual 
  interfaces the datatype Tensor' are often involved, making it much simpler
  to create a separate file for it.
  -}
  -- public export
  -- Tensor' : List Cont -> Type -> Type
  -- Tensor' cs = Ext (Tensor cs)

public export
composeExtensions : List Cont -> Type -> Type
composeExtensions = foldr (\c, f => (Ext c) . f) (Ext Scalar)

public export
fixShape : {c : Cont} ->
  Ext c a -> Cont
fixShape e = At c (shapeExt e)

||| Continer describing how from an extension of another we can get a value out
public export
Pick : Cont -> Type -> Cont
Pick c a = Const2 (Ext c a) a

namespace ComposeExtensionsVect
  public export
  composeExtensions : Vect n Cont -> Type -> Type
  composeExtensions = foldr @{straightforward} (\c, f => (Ext c) . f) (Ext Scalar)

public export
[fe] {shape : List Cont} -> Functor (composeExtensions shape) where
  map {shape = []} f = map f
  map {shape = (s :: ss)} f = (map @{fe} f <$>)

||| Generalisation of 'positions' from Data.Functor.Naperian
||| Works for an arbitrary container, as long as we supply its shape
||| The definition in Data.Functor.Naperian.positions is for Naperian containers
||| i.e. containers with a unit shape
public export
positionsCont : {0 c : Cont} -> {sh : c.Shp} -> Ext c (c.Pos sh)
positionsCont = sh <| id

{-------------------------------------------------------------------------------
Conversions witnessing the isomorphisms of `ExtensionsOfMainExamples`
-------------------------------------------------------------------------------}

namespace List
  public export
  fromList : List a -> List' a
  fromList [] = (0 <| absurd)
  fromList (x :: xs) = let (l <| c) = fromList xs
                       in (S l <| cons x c)

  public export
  toList : List' a -> List a
  toList (0 <| _) = []
  toList l@((S k) <| ind) = head ind :: toList
    (assert_smaller l (k <| tail ind))

namespace Vect
  public export
  fromVect : Vect n a -> Vect' n a
  fromVect v = () <| \i => index i v

  public export
  toVect : {n : Nat} -> Vect' n a -> Vect n a
  toVect (_ <| index) = Vect.Fin.tabulate index

namespace BinTreeSame
  public export
  fromBinTreeSame : BinTreeSame a -> BinTree' a
  fromBinTreeSame (Leaf x) = LeafS <| \_ => x
  fromBinTreeSame (Node x lt rt) =
    let (fblt, fbrt) = (fromBinTreeSame lt, fromBinTreeSame rt)
    in NodeS (shapeExt fblt) (shapeExt fbrt) <| \case
        AtNode => x
        GoLeft posL => index fblt posL
        GoRight posR => index fbrt posR

  public export
  toBinTreeSame : BinTree' a -> BinTreeSame a
  toBinTreeSame (LeafS <| index) = Leaf (index AtLeaf)
  toBinTreeSame n@(NodeS lt rt <| index) =
    Node (index AtNode)
         (toBinTreeSame $ assert_smaller n (lt <| index . GoLeft))
         (toBinTreeSame $ assert_smaller n (rt <| index . GoRight))

namespace BinTreeNode
  public export
  fromTreeHelper : BinTreePosNode LeafS -> a
  fromTreeHelper AtNode impossible
  fromTreeHelper (GoLeft x) impossible
  fromTreeHelper (GoRight x) impossible

  public export
  fromBinTreeNode : BinTreeNode a -> BinTreeNode' a
  fromBinTreeNode (Leaf ()) = LeafS <| fromTreeHelper
  fromBinTreeNode (Node node leftTree rightTree)
    = let (fblt, fbrt) = (fromBinTreeNode leftTree, fromBinTreeNode rightTree)
      in (NodeS (shapeExt fblt) (shapeExt fbrt) <| \case
            AtNode => node
            GoLeft posL => index fblt posL
            GoRight posR => index fbrt posR)

  public export
  toBinTreeNode : BinTreeNode' a -> BinTreeNode a
  toBinTreeNode (LeafS <| index) = Leaf ()
  toBinTreeNode n@(NodeS lt rt <| index) = 
    Node (index AtNode)
         (toBinTreeNode $ assert_smaller n (lt <| index . GoLeft))
         (toBinTreeNode $ assert_smaller n (rt <| index . GoRight))

namespace BinTreeLeaf
  public export
  fromBinTreeLeaf : BinTreeLeaf a -> BinTreeLeaf' a
  fromBinTreeLeaf (Leaf leaf) = LeafS <| \_ => leaf
  fromBinTreeLeaf (Node node lt rt) =
    let (fblt, fbrt) = (fromBinTreeLeaf lt, fromBinTreeLeaf rt)
    in NodeS (shapeExt fblt) (shapeExt fbrt) <| \case
          GoLeft posL => index fblt posL
          GoRight posR => index fbrt posR

  public export
  toBinTreeLeaf : BinTreeLeaf' a -> BinTreeLeaf a
  toBinTreeLeaf (LeafS <| content) = Leaf (content AtLeaf)
  toBinTreeLeaf n@(NodeS l r <| content) =
    Node' (toBinTreeLeaf $ assert_smaller n (l <| content . GoLeft))
          (toBinTreeLeaf $ assert_smaller n (r <| content . GoRight))

-- the idea is that the bottom part of this file will slowly be made obsolete 
-- as more and more things are implemented in terms of containers


namespace VectInstances
  public export
  {n : Nat} -> Eq x => Eq (Vect' n x) where
    v == v' = (toVect v) == (toVect v')
 
  -- public export
  -- {n : Nat} -> Show x => Show (Vect' n x) where
  --   show v = show (toVect v)

  -- Applicative and Naperian instance follow because the set of shapes is ()

  -- analogus to Misc.takeFin, but for Vect'
  public export 
  take : {n : Nat} ->
    (s : Fin (S n)) -> Vect' n a -> Vect' (finToNat s) a
  take s = fromVect . takeFin s . toVect

  public export
  (++) : {n : Nat} -> Vect' n a -> Vect' m a -> Vect' (n + m) a
  (++) v1 v2 = () <| \i => case splitSum i of
    Left i1 => index v1 i1
    Right i2 => index v2 i2

{---
Ideally, all instances would be defined in terms of ConcreteTypes,
but there are totality checking issues with types whose size isn't known
at compile time
---}
namespace ListInstances
  ||| Is there a different way to convince Idris' totality checker?
  public export
  Eq a => Eq (List' a) where
    l == l' = assert_total ((toList l) == (toList l'))

  -- ||| Is there a different way to convince Idris' totality checker?
  -- public export
  -- Show a => Show (List' a) where
  --   show x = assert_total (show (toList x))


  -- some attempts at fixing partiality below
  -- public export
  -- showListHelper : Show a => List' a -> String
  -- showListHelper (0 <| _) = ""
  -- showListHelper (1 <| index) = show $ index FZ
  -- showListHelper ((S k) <| index)
  --   = let (s, rest) = headTail index
  --     in show s ++ ", " ++ showListHelper (k <| rest)

  -- public export
  -- showListHelper : Show a => List' a -> String
  -- showListHelper x = show (toList x)


namespace BinTreeInstances
  ||| Is there a different way to convince Idris' totality checker?
  public export
  Eq a => Eq (BinTree' a) where
    t == t' = assert_total (toBinTreeSame t == toBinTreeSame t')

  -- ||| Is there a different way to convince Idris' totality checker?
  -- public export
  -- Show a => Show (BinTree' a) where
  --   show = assert_total (show . toBinTreeSame)


namespace BinTreeLeafInstances
  ||| Is there a different way to convince Idris' totality checker?
  public export
  Eq a => Eq (BinTreeLeaf' a) where
    t == t' = assert_total (toBinTreeLeaf t == toBinTreeLeaf t')

  -- ||| Is there a different way to convince Idris' totality checker?
  -- public export
  -- Show a => Show (BinTreeLeaf' a) where
  --   show = assert_total (show . toBinTreeLeaf)


namespace BinTreeNodeInstances
  ||| Is there a different way to convince Idris' totality checker?
  public export
  Eq a => Eq (BinTreeNode' a) where
    t == t' = assert_total (toBinTreeNode t == toBinTreeNode t')

  -- ||| Is there a different way to convince Idris' totality checker?
  -- public export
  -- Show a => Show (BinTreeNode' a) where
  --   show = assert_total (show . toBinTreeNode)
