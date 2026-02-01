module Data.Container.Base.Concrete.Instances

import Data.Fin
import Data.Vect
import Data.List
import Data.DPair

import Data.Container.Base.Object.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Concrete.Definition
import Data.Container.Base.Object.Instances
import Data.Container.Base.Extension.Instances

import public Data.Functor.Naperian
import public Data.Tree

import Misc

%hide Data.Vect.fromList

namespace ConversionFunctions
  public export
  toScalar : a -> Scalar' a
  toScalar a = () <| (\_ => a)

  public export
  extract : Scalar' a -> a
  extract (() <| f) = f ()

  public export
  fromMaybe : Maybe a -> Maybe' a
  fromMaybe Nothing = (False <| absurd)
  fromMaybe (Just a) = (True <| \_ => a)

  public export
  toMaybe : Maybe' a -> Maybe a
  toMaybe (False <| absurd) = Nothing
  toMaybe (True <| f) = Just (f ())

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
  fromVect : Vect n a -> Vect' n a
  fromVect v = () <| \i => index i v
  
  public export
  toVect : {n : Nat} -> Vect' n a -> Vect n a
  toVect (_ <| index) = Vect.Fin.tabulate index

  public export
  fromBinTreeSame : BinTreeSame a -> BinTree' a
  fromBinTreeSame (Leaf x) = LeafS <| \_ => x
  fromBinTreeSame (Node x lt rt) =
    let fblt = fromBinTreeSame lt
        fbrt = fromBinTreeSame rt
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
  fromTreeHelper : BinTreePosNode LeafS -> a
  fromTreeHelper AtNode impossible
  fromTreeHelper (GoLeft x) impossible
  fromTreeHelper (GoRight x) impossible
  
  public export
  fromBinTreeNode : BinTreeNode a -> BinTreeNode' a
  fromBinTreeNode (Leaf ()) = LeafS <| fromTreeHelper
  fromBinTreeNode (Node node leftTree rightTree)
    = let fblt = fromBinTreeNode leftTree
          fbrt = fromBinTreeNode rightTree
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
  fromBinTreeLeaf : BinTreeLeaf a -> BinTreeLeaf' a
  fromBinTreeLeaf (Leaf leaf) = LeafS <| \_ => leaf
  fromBinTreeLeaf (Node node lt rt) =
    let fblt = fromBinTreeLeaf lt
        fbrt = fromBinTreeLeaf rt
    in NodeS (shapeExt fblt) (shapeExt fbrt) <| \case
          GoLeft posL => index fblt posL
          GoRight posR => index fbrt posR

  public export
  toBinTreeLeaf : BinTreeLeaf' a -> BinTreeLeaf a
  toBinTreeLeaf (LeafS <| content) = Leaf (content AtLeaf)
  toBinTreeLeaf (NodeS l r <| content) =
    Node' (toBinTreeLeaf (l <| content . GoLeft))
          (toBinTreeLeaf (r <| content . GoRight))

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


public export
FromConcrete Scalar where
  concreteType = id
  concreteFunctor = MkFunctor id
  fromConcreteTy = pure
  toConcreteTy = extract

public export
FromConcrete Maybe where
  concreteType = Maybe
  concreteFunctor = %search
  fromConcreteTy = fromMaybe
  toConcreteTy = toMaybe

public export
FromConcrete List where
  concreteType = List
  concreteFunctor = %search -- TODO how to find the result of the search and place it here directly?
  fromConcreteTy = fromList
  toConcreteTy = toList

public export
{n : Nat} -> FromConcrete (Vect n) where
  concreteType = Vect n
  concreteFunctor = %search
  fromConcreteTy = fromVect
  toConcreteTy = toVect

public export
FromConcrete BinTree where
  concreteType = BinTreeSame
  concreteFunctor = %search
  fromConcreteTy = fromBinTreeSame
  toConcreteTy = toBinTreeSame

public export
FromConcrete BinTreeNode where
  concreteType = BinTreeNode
  concreteFunctor = %search
  fromConcreteTy = fromBinTreeNode
  toConcreteTy = toBinTreeNode

public export
FromConcrete BinTreeLeaf where
  concreteType = BinTreeLeaf
  concreteFunctor = %search
  fromConcreteTy = fromBinTreeLeaf
  toConcreteTy = toBinTreeLeaf

