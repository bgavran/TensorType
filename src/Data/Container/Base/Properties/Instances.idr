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

  public export prefix 0 >##, ##>

  public export
  (>##) : Vect n a -> Vect' n a
  (>##) = fromVect

  public export
  (##>) : {n : Nat} -> Vect' n a -> Vect n a
  (##>) = toVect

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