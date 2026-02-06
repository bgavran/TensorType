module Data.Container.Base.Extension.Instances

import Data.DPair

import Data.Container.Base.Object.Definition
import Data.Container.Base.Object.Instances
import Data.Container.Base.Extension.Definition

import Data.Functor.Naperian

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

public export
[fe] {shape : List Cont} -> Functor (composeExtensions shape) where
  map {shape = []} f = map f
  map {shape = (s :: ss)} f = (map @{fe} f <$>)

public export
EmptyExt : Ext (Nap l) Builtin.Unit
EmptyExt = () <| \_ => ()

public export
liftA2ConstCont : Ext (Nap l) a -> Ext (Nap l) b -> Ext (Nap l) (a, b)
liftA2ConstCont (() <| va) (() <| vb) = () <| (\x => (va x, vb x))

||| The extension of any container with a unit shape
||| is an applicative functor
||| Examples: Scalar, Pair, Vect n, Stream
||| Notably, List and Maybe are also applicative
public export
Applicative (Ext (Nap l)) where
  pure a = () <| (\_ => a)
  fs <*> xs = uncurry ($) <$> liftA2ConstCont fs xs 

||| The extension of any container with a unit shape
||| is an Naperian functor
||| Notably, lists are not applicative
public export
{l : Type} -> Naperian (Ext (Nap l)) where
  Log = l
  lookup = index
  tabulate t = () <| t

||| Generalisation of 'positions' from Data.Functor
||| Works for an arbitrary container, as long as we supply its shape
||| The definition in Data.Functor.positions is for Naperian containers
||| i.e. containers with a unit shape
public export
positionsCont : {sh : c.Shp} -> Ext c (c.Pos sh)
positionsCont = sh <| id
