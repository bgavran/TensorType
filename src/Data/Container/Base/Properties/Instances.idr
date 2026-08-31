module Data.Container.Base.Properties.Instances

import Data.Fin
import Data.Vect
import Decidable.Equality
import Data.Fin.Split
import Data.Finite

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Properties.Definition
import Data.Container.Base.Product.Definition

import Data.Container.Base.Object.Instances
import Data.Container.Base.Extension.Instances
import Data.Container.Base.Morphism.Instances

import Data.Trees
import Data.Functor.Products
import Data.Functor.Algebra
import Data.Container.Base.TreeUtils

import Misc

%hide Data.Vect.fromList
%hide Prelude.toList

public export
IsConcrete Scalar where
  func = id
  functorInstance = MkFunctor id
  fromConcreteTy = pure
  toConcreteTy (() <| f) = f ()

public export
IsConcrete Maybe where
  func = Maybe
  functorInstance = %search

  fromConcreteTy Nothing = False <| absurd
  fromConcreteTy (Just x) = True <| \() => x

  toConcreteTy (False <| _) = Nothing
  toConcreteTy (True <| f) = Just (f ())

public export
IsConcrete Pair where
  func = \a => Pair a a
  functorInstance = MkFunctor $ \f, (x, y) => (f x, f y)
  fromConcreteTy (x, y) = () <| \case False => x; True => y
  toConcreteTy (() <| f) = (f False, f True)

||| This is a concrete instance for Naperian containers
||| It applies also to `s=Fin n` which is covered by Vect
||| We therefore want this to only be applied if Vect isn't
%defaulthint
public export
lambdaNap : {s : Type} -> IsConcrete (Nap s)
lambdaNap = MkIsConcrete
  (\a => s -> a)
  (MkFunctor (.))
  (\content => () <| content)
  (\(() <| content) => content)

public export
(icc : IsConcrete c) => (icd : IsConcrete d) => IsConcrete (c >< d) where
  func = func @{icc} >< func @{icd}
  functorInstance = ?functorInstanceHancockProduct
  fromConcreteTy = ?fromConcreteTyHancockProduct
  toConcreteTy = ?toConcreteTyHancockProduct

public export
(icc : IsConcrete c) => (icd : IsConcrete d) => IsConcrete (c >@ d) where
  func = func @{icc} . func @{icd}
  functorInstance = MkFunctor $ \f => ?functorInstanceCompositionProduct
  fromConcreteTy = ?fromConcreteTyCompositionProduct
  toConcreteTy = ?toConcreteTyCompositionProduct


||| For recursive types we need to extract out the conversion functions
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

  public export
  IsConcrete List where
    func = List
    functorInstance = %search
    fromConcreteTy = fromList
    toConcreteTy = toList

namespace Vect
  public export
  fromVect : Vect n a -> Vect' n a
  fromVect v = () <| \i => index i v
  
  public export
  toVect : {n : Nat} -> Vect' n a -> Vect n a
  toVect (_ <| index) = Vect.Fin.tabulate index

  -- public export
  -- test : {n : Nat} -> IsConcrete (Vect n)
  -- test = MkIsConcrete
  --   (Vect n)
  --   (%search)
  --   (fromVect)
  --   (toVect)

  public export
  {n : Nat} -> IsConcrete (Vect n) where
    func = Vect n
    functorInstance = %search
    fromConcreteTy = fromVect
    toConcreteTy = toVect

namespace Grid
  public export
  {h, w : Nat} -> IsConcrete (Grid (h, w)) where
    func a = (Fin h, Fin w) -> a
    functorInstance = MkFunctor (.)
    fromConcreteTy content = ((), ()) <| content
    toConcreteTy (((), ()) <| content) = content

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

  public export
  IsConcrete BinTree where
    func = BinTreeSame
    functorInstance = %search
    fromConcreteTy = fromBinTreeSame
    toConcreteTy = toBinTreeSame

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

  public export
  IsConcrete BinTreeNode where
    func = BinTreeNode
    functorInstance = %search
    fromConcreteTy = fromBinTreeNode
    toConcreteTy = toBinTreeNode

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

  public export
  IsConcrete BinTreeLeaf where
    func = BinTreeLeaf
    functorInstance = %search
    fromConcreteTy = fromBinTreeLeaf
    toConcreteTy = toBinTreeLeaf


public export
foldList : (a -> b -> b) -> b -> List' a -> b
foldList f z (0 <| _) = z
foldList f z l@((S k) <| content)
  = f (head content) $ foldList f z
    (assert_smaller l (k <| tail content))

public export
IsFoldable c => Foldable (Ext c) where
  foldr @{(MkIsFoldable toL)} f z = foldList f z . extMap toL 

public export
IsFoldable List where
  mapToList = id

public export
{n : Nat} -> IsFoldable (Vect n) where
  mapToList = vectToList

||| Requires making a choice of traversal order
||| Is there a good reason to prefer a particular order?
public export
IsFoldable BinTreeLeaf where
  mapToList = inorder

public export
IsFoldable BinTreeNode where
  mapToList = inorder

public export
IsFoldable BinTree where
  mapToList = inorder

-- old
-- ||| Indexing an element of `xs` and then applying `f` to it is the same as
-- ||| mapping `f` over xs, and then indexing the result
-- public export
-- mapIndexPreserve : {0 f : a -> b} ->
--   (xs : List a) ->
--   (i : Fin (length (f <$> xs))) ->
--   f (index' xs (rewrite sym (lengthMap {f=f} xs) in i))
--     = index' (f <$> xs) i
-- mapIndexPreserve (x :: xs) FZ = Refl
-- mapIndexPreserve (x :: xs) (FS j) = mapIndexPreserve xs j


-- the idea is that the bottom part of this file will slowly be made obsolete 
-- as more and more things are implemented in terms of containers


||| Any finite container (i.e. whose each set of positions is finite) can be
||| given an algebra instance simply by summing up all the concrete values
public export
algebraFinite : 
  (0 c : Cont) -> (isFinite : IsFinite c) =>
  (0 a : Type) -> Num a =>
  Algebra (Ext c) a
algebraFinite c {isFinite = MkI p} _
  = MkAlgebra $ \(shp <| content) => reduce $ values @{p shp} <&> content


namespace VectInstances
  public export
  {n : Nat} -> Eq x => Eq (Vect' n x) where
    v == v' = (toVect v) == (toVect v')
 
  -- public export
  -- {n : Nat} -> Show x => Show (Vect' n x) where
  --   show v = show (toVect v)

  public export
  {n : Nat} -> Num a => Algebra (Vect' n) a where
    reduce v = reduce (toVect v)

  public export
  {n : Nat} -> Traversable (Vect' n) where
    traverse f v = fromVect <$> traverse f (toVect v)

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

  public export
  Num a => Algebra List' a where
    reduce = reduce {f=List} . toList


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

  ||| Summing up nodes and leaves of the tree given by the Num a structure
  public export
  Num a => Algebra BinTree' a where
    reduce = reduce {f=BinTreeSame} . toBinTreeSame

  -- public export
  -- binTreePosInterface : InterfaceOnPositions BinTree DecEq
  -- binTreePosInterface = MkI


namespace BinTreeLeafInstances
  ||| Is there a different way to convince Idris' totality checker?
  public export
  Eq a => Eq (BinTreeLeaf' a) where
    t == t' = assert_total (toBinTreeLeaf t == toBinTreeLeaf t')

  -- ||| Is there a different way to convince Idris' totality checker?
  -- public export
  -- Show a => Show (BinTreeLeaf' a) where
  --   show = assert_total (show . toBinTreeLeaf)

  ||| Summing up leaves of the tree given by the Num a structure
  public export
  Num a => Algebra BinTreeLeaf' a where
    reduce = reduce {f=BinTreeLeaf} . toBinTreeLeaf


namespace BinTreeNodeInstances
  ||| Is there a different way to convince Idris' totality checker?
  public export
  Eq a => Eq (BinTreeNode' a) where
    t == t' = assert_total (toBinTreeNode t == toBinTreeNode t')

  -- ||| Is there a different way to convince Idris' totality checker?
  -- public export
  -- Show a => Show (BinTreeNode' a) where
  --   show = assert_total (show . toBinTreeNode)

  ||| Summing up nodes of the tree given by the Num a structure
  public export
  Num a => Algebra BinTreeNode' a where
    reduce = reduce {f=BinTreeNode} . toBinTreeNode