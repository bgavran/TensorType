module Data.Container.Object.Instances

import Data.Fin

import public Data.Container.Object.Definition
import public Data.Container.Product.Definitions
import public Data.Container.TreeUtils

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
Vect : Nat -> Cont
Vect n = (_ : Unit) !> Fin n

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

-- TODO duoidal structure between with hancock product and composition

||| Every lens gives rise to a container
||| The set of shapes is the lens itself
||| The set of positions is the inputs to the lens
||| This is the closure with respect to the Hancock tensor product
public export
InternalLens : Cont -> Cont -> Cont
InternalLens c d
  = (f : ((x : c.Shp) -> (y : d.Shp ** d.Pos y -> c.Pos x)))
    !> (xx : c.Shp ** d.Pos (fst (f xx)))

||| From https://www.cs.ox.ac.uk/people/samuel.staton/papers/cie10.pdf
public export
CartesianClosure : Cont -> Cont -> Cont
CartesianClosure c d
  = (f : ((x : c.Shp) -> (y : d.Shp ** d.Pos y -> Maybe (c.Pos x))))
    !> (xx : c.Shp ** yy' : d.Pos (fst (f xx)) ** ?cartesianClosureImpl)

||| Constant container, positions do not depend on shapes
||| Some of the above containers can be refactored in terms of these
||| But it's more illuminating to keep them in their raw form for now
||| As a polynomial functor: F(X) = a * (X^b)
public export
Const : Type -> Type -> Cont
Const a b = (_ : a) !> b

||| Constant container with a single shape
||| Naperian container
||| As a polynomial functor: F(X) = X^b
public export
Nap : Type -> Cont
Nap b = Const Unit b

-- Some more examples that require the Applicative constraint can be found in
-- `Data.Container.Object.Applicative`
