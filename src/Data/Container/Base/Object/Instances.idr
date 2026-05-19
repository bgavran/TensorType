module Data.Container.Base.Object.Instances

import Data.Fin
import Data.List.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Product.Definitions
import Data.Container.Base.TreeUtils
import Control.Monad.Distribution


{-------------------------------------------------------------------------------
This file defines a number of different containers
Some of them are possible to express in terms of each other, but we opt to define all of them directly
-------------------------------------------------------------------------------}

||| Constant (non-dependent) container: positions do not depend on shapes
||| As a polynomial functor: F(X) = aX^b
public export
Const2 : Type -> Type -> Cont
Const2 a b = (_ : a) !> b

||| Constant container whose shapes and positions coincide
||| As a polynomial functor: F(X) = aX^a
public export 
Const : Type -> Cont
Const a = Const2 a a

||| Naperian container: a constant container with a single shape
||| As a polynomial functor: F(X) = X^b
public export
Nap : Type -> Cont
Nap b = Const2 Unit b

||| Flat container: a constant container with a single position
||| As a polynomial functor: F(X) = aX
public export
Flat : Type -> Cont
Flat a = Const2 a Unit

||| Sharp container: a constant container without any positions
||| As a polynomial functor: F(X) = a
public export
Sharp : Type -> Cont
Sharp a = Const2 a Void

||| Empty container, isomorphic to Void
||| As a polynomial functor: F(X) = 0
||| Initial container
public export
Empty : Cont
Empty = (_ : Void) !> Void

||| Container of a single thing
||| As a polynomial functor: F(X) = X
public export
Scalar : Cont
Scalar = (_ : Unit) !> Unit

||| Container with a single shape, but no positions. Isomorphic to Unit : Type
||| As a polynomial functor: F(X) = 1
||| Terminal container
public export
UnitCont : Cont
UnitCont = (_ : Unit) !> Void

||| Product, container of two things
||| Isomorphic to Scalar >*< Scalar
||| As a polynomial functor: F(X) = X^2
public export
Pair : Cont
Pair = (_ : Unit) !> Bool

||| Coproduct, container of either one of two things
||| Isomorphic to Scalar >+< Scalar
||| As a polynomial functor: F(X) = X + X
public export
Either : Cont
Either = (_ : Bool) !> Unit

||| Container of either one thing, or nothing
||| Isomorphic to Scalar >+< UnitCont
||| Initial algebra is Nat
||| As a polynomial functor: F(X) = 1 + X
public export
Maybe : Cont
Maybe = (b : Bool) !> (if b then Unit else Void)

||| Container of either two things, or nothing
||| Isomorphic to Pair >+< UnitCont
||| Initial algebra is BinTreeShape
||| As a polynomial functor: F(X) = 1 + X^2
public export
MaybeTwo : Cont
MaybeTwo = (b : Bool) !> (if b then Fin 2 else Void)

||| List, container with an arbitrary number of things
||| As a polynomial functor: F(X) = 1 + X + X^2 + X^3 + ...
public export
List : Cont
List = (n : Nat) !> Fin n

||| Vect, container of a fixed/known number of things
||| As a polynomial functor: F(X) = X^n
public export
Vect : List .Shp -> Cont
Vect n = (_ : Unit) !> Fin n

||| Grid, container of things arranged along two axes
||| As a polynomial functor: F(X) = X^(hw)
public export
Grid : (List .Shp, List .Shp) -> Cont
Grid (h, w) = (Vect h) >< (Vect w)

||| Container of an infinite number of things
||| As a polynomial functor: F(X) = X^Nat
public export
Stream : Cont
Stream = (_ : Unit) !> Nat

||| Container of things stored at nodes and leaves of a binary tree
||| As a polynomial functor: F(X) = 1 + 2X + 3X^2 + 7X^3 + ...
public export
BinTree : Cont
BinTree = (b : BinTreeShape) !> BinTreePos b

||| Container of things stored at nodes of a binary tree
||| As a polynomial functor: F(X) = 1 + X + 2X^2 + 5X^3 +
public export
BinTreeNode : Cont
BinTreeNode = (b : BinTreeShape) !> BinTreePosNode b

||| Container of things stored at leaves of a binary tree
||| As a polynomial functor: F(X) = X + X^2 + 2X^3 + 5X^4 +
public export
BinTreeLeaf : Cont
BinTreeLeaf = (b : BinTreeShape) !> BinTreePosLeaf b

||| Tensors are containers
||| As a polynomial functor: F(X) = ?
public export
Tensor : List Cont -> Cont
Tensor = foldr (>@) Scalar

public export
CartesianTensor : List Cont -> Cont
CartesianTensor = foldr (>*<) UnitCont

public export
HancockTensor : List Cont -> Cont
HancockTensor = foldr (><) Scalar

public export
CoproductTensor : List Cont -> Cont
CoproductTensor = foldr (>+<) Empty

||| Ignoring universe levels here
||| This should be the analogue of `Type : Type`
public export
ContUniverse : Cont
ContUniverse = (_ : (s : Type ** s -> Type)) !> Void

||| Given a natural number `n`, this is a container whose shape represents a 
||| distribution over `n` choices, and its position represents the choice made.
public export
Sample : Nat -> Cont
Sample n = Const2 (Dist n) (Fin n)
