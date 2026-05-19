module Data.Container.Base.Properties.Instances

import Data.Fin
import Data.Vect

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Properties.Definitions
import Data.Container.Base.Product.Definitions

import Data.Container.Base.Object.Instances
import Data.Container.Base.Extension.Instances
import Data.Container.Base.Morphism.Instances

import Data.Trees
import Data.Functor.Products
import Data.Container.Base.TreeUtils

import Misc

%hide Data.Vect.fromList

public export
IsConcrete Scalar where
  concreteType = id
  concreteFunctor = MkFunctor id
  fromConcreteTy = pure
  toConcreteTy (() <| f) = f ()

public export
IsConcrete Maybe where
  concreteType = Maybe
  concreteFunctor = %search

  fromConcreteTy Nothing = False <| absurd
  fromConcreteTy (Just x) = True <| \() => x

  toConcreteTy (False <| _) = Nothing
  toConcreteTy (True <| f) = Just (f ())

public export
IsConcrete Pair where
  concreteType = \a => Pair a a
  concreteFunctor = MkFunctor $ \f, (x, y) => (f x, f y)
  fromConcreteTy (x, y) = () <| \case False => x; True => y
  toConcreteTy (() <| f) = (f False, f True)

public export
(icc : IsConcrete c) => (icd : IsConcrete d) => IsConcrete (c >< d) where
  concreteType = concreteType @{icc} >< concreteType @{icd}
  concreteFunctor = ?concreteFunctorHancockProduct
  fromConcreteTy = ?fromConcreteTyHancockProduct
  toConcreteTy = ?toConcreteTyHancockProduct

public export
(icc : IsConcrete c) => (icd : IsConcrete d) => IsConcrete (c >@ d) where
  concreteType = concreteType @{icc} . concreteType @{icd}
  concreteFunctor = MkFunctor $ \f => ?concreteFunctorCompositionProduct
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
  toList ((S k) <| ind) = head ind :: toList (k <| tail ind)

  public export
  IsConcrete List where
    concreteType = List
    concreteFunctor = %search
    fromConcreteTy = fromList
    toConcreteTy = toList

namespace Vect
  public export
  fromVect : Vect n a -> Vect' n a
  fromVect v = () <| \i => index i v
  
  public export
  toVect : {n : Nat} -> Vect' n a -> Vect n a
  toVect (_ <| index) = Vect.Fin.tabulate index

  public export
  {n : Nat} -> IsConcrete (Vect n) where
    concreteType = Vect n
    concreteFunctor = %search
    fromConcreteTy = fromVect
    toConcreteTy = toVect

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
  toBinTreeSame (NodeS lt rt <| index) =
    Node (index AtNode)
         (toBinTreeSame (lt <| index . GoLeft))
         (toBinTreeSame (rt <| index . GoRight))

  public export
  IsConcrete BinTree where
    concreteType = BinTreeSame
    concreteFunctor = %search
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
  toBinTreeNode (NodeS lt rt <| index) = 
    Node (index AtNode)
         (toBinTreeNode (lt <| index . GoLeft))
         (toBinTreeNode (rt <| index . GoRight))

  public export
  IsConcrete BinTreeNode where
    concreteType = BinTreeNode
    concreteFunctor = %search
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
  toBinTreeLeaf (NodeS l r <| content) =
    Node' (toBinTreeLeaf (l <| content . GoLeft))
          (toBinTreeLeaf (r <| content . GoRight))

  public export
  IsConcrete BinTreeLeaf where
    concreteType = BinTreeLeaf
    concreteFunctor = %search
    fromConcreteTy = fromBinTreeLeaf
    toConcreteTy = toBinTreeLeaf


public export
foldList : (a -> b -> b) -> b -> List' a -> b
foldList f z (0 <| _) = z
foldList f z ((S k) <| content)
  = f (head content) $ foldList f z (k <| tail content)

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