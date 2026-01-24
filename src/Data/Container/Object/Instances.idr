module Data.Container.Object.Instances

import Data.Fin
import Data.List.Quantifiers

import public Data.Container.Object.Definition
import public Data.Container.Product.Definitions
import public Data.Container.TreeUtils
import public Misc

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

-- TODO what is "Tensor" with hancock product? with cartesian product?
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


namespace Cubical
  {-
  A container is said to be:
  * Finite: when for every shape the set of positions is finite.
    * Examples: vectors, lists, but also finite binary trees.
  * Naperian: when the set of shapes is `Unit`. This means that there is only one set of positions for that container.
    * Examples: Scalar, UnitCont, Pair, Vect n, Stream.
    * Notably, the `Stream` example shows us Naperian does not imply Finite
  * Cubical: when it is both Finite and Naperian.
    * Examples: for any `n : Nat`, `Vect n`. Those are all the examples, up to isomorphism
    * Notably, this also includes, a container whose unique set of positions is the set of positions of binary trees of a particular shape. But this is isomorphic to the `Vect k` container, where `k` is the number of positions in that binary tree.
  -}
  -- TODO, define `Finite` datatype? Perhaps by using `idris2-finite`?

  ||| A container is `Naperian` when there is only one set of shapes, and
  ||| thus only one set of positions for that container
  public export
  data IsNaperian : Cont -> Type where
    MkIsNaperian : (pos : Type) -> IsNaperian (Const Unit pos)

  ||| A container is cubical whenever it is Finite and Naperian
  ||| Effectively, captures `Vect n` containers, up to isomorphism
  public export
  data IsCubical : Cont -> Type where
    MkIsCubical : (n : Nat) -> IsCubical (Const Unit (Fin n))

  public export
  dimHelper : IsCubical c -> Nat
  dimHelper (MkIsCubical n) = n

  ||| We call dimension the size of the set of positions of a finite container 
  public export
  dim : (0 c : Cont) -> IsCubical c => Nat
  dim _ @{ic} = dimHelper ic

  ||| Helper function allowing `shape` in `cubicalShape` to have zero annotation
  public export
  cubicalShapeHelper : All IsCubical shape -> List Nat
  cubicalShapeHelper [] = []
  cubicalShapeHelper (ic :: ics) = dimHelper ic :: cubicalShapeHelper ics

  ||| Given a list of cubical containers, return the list of their dimensions
  public export
  cubicalShape : (0 shape : List Cont) -> All IsCubical shape => List Nat
  cubicalShape _ @{ac} = cubicalShapeHelper ac

  ||| Size of a list of cubical containers is the product of their dimensions
  public export
  size : (0 shape : List Cont) -> All IsCubical shape => Nat
  size shape = prod (cubicalShape shape)

