module Data.Container.Extension.Instances

import Data.DPair
import Data.Vect

import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Container.Extension.Definition

import Data.Functor.Naperian
import Misc

%hide Prelude.(<|)

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

namespace ComposeExtensionsVect
  public export
  composeExtensions : Vect n Cont -> Type -> Type
  composeExtensions = foldr @{straightforward} (\c, f => (Ext c) . f) (Ext Scalar)

public export
[fe] {shape : List Cont} -> Functor (composeExtensions shape) where
  map {shape = []} f = map f
  map {shape = (s :: ss)} f = (map @{fe} f <$>)

public export
EmptyExt : {0 c : Cont} -> IsNaperian c => Ext c Unit
EmptyExt @{MkIsNaperian _} = () <| \_ => ()

public export
liftA2ConstCont : IsNaperian c => Ext c a -> Ext c b -> Ext c (a, b)
liftA2ConstCont @{MkIsNaperian _} ea eb = () <| (\x => (index ea x, index eb x))

||| The extension of any Naperian container is an applicative functor
||| Examples: Scalar, Pair, Vect n, Stream
||| But not all Applicatives are Naperian, examples being: List and Maybe
public export
IsNaperian c => Applicative (Ext c) where
  pure @{MkIsNaperian _} a = () <| \_ => a
  (<*>) fs xs @{MkIsNaperian _} = uncurry ($) <$> liftA2ConstCont fs xs 

||| The extension of a Naperian container is a Naperian functor
||| All Naperian functors are applicative, but not vice versa
||| Notably, lists are not applicative
public export
IsNaperian c => Naperian (Ext c) where
  Log @{MkIsNaperian pos} = pos
  lookup @{MkIsNaperian pos} = index
  tabulate @{MkIsNaperian pos} = \content => () <| content

||| Generalisation of 'positions' from Data.Functor
||| Works for an arbitrary container, as long as we supply its shape
||| The definition in Data.Functor.positions is for Naperian containers
||| i.e. containers with a unit shape
public export
positionsCont : {sh : c.Shp} -> Ext c (c.Pos sh)
positionsCont = sh <| id