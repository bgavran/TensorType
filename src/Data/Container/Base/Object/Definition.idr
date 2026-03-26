module Data.Container.Base.Object.Definition

import Data.Fin
import Data.Finite

||| Containers capture the idea that datatypes consist of groups of memory 
||| locations where data can be stored. Locations for a particular group are 
||| referred to as 'positions' and a particular group is referred to as a
||| 'shape'.
public export
record Cont where
  constructor (!>)
  ||| A type of shapes
  Shp : Type
  ||| For each shape, a set of positions
  Pos : Shp -> Type

export typebind infixr 0 !>

%name Cont c, c', c''

||| Constant container, one where positions do not depend on shapes
public export
Const2 : Type -> Type -> Cont
Const2 a b = (_ : a) !> b

||| Constant container, one where positions do not depend on shapes
public export 
Const : Type -> Cont
Const a = Const2 a a

||| Naperian container: a constant container with a single shape
public export
Nap : Type -> Cont
Nap b = Const2 Unit b

||| Convenience datatype for storing the data that a container `c` has an
||| interface `i` on its positions
||| TODO does the argument of MkI need to be auto implicit?
public export
data InterfaceOnPositions : (c : Cont) -> (i : Type -> Type) -> Type where
  ||| For every shape `s` the set of positions `c.Pos s` has that interface
  MkI : (p : (s : c.Shp) -> i (c.Pos s)) =>
    InterfaceOnPositions c i

||| A container is finite when for every shape the set of positions is finite.
||| Examples: vectors, lists, but also finite binary trees.
||| Note, provision of a finite instance for trees requires a choice of a tree
||| traversal. (All of these choices isomorphic, but are necessary to make)
public export
IsFinite : Cont -> Type
IsFinite c = InterfaceOnPositions c Finite

||| A container is Naperian when the set of shapes is `Unit`, i.e. when it
||| contains only one set of positions.
||| Examples: Scalar, UnitCont, Pair, Vect n, Stream.
||| Notably, Naperian does not imply Finite, as the `Stream` example shows.
public export
data IsNaperian : Cont -> Type where
  MkIsNaperian : (pos : Type) -> IsNaperian (Nap pos)

public export
LogHelper : IsNaperian c => Type
LogHelper @{MkIsNaperian pos} = pos

public export
Log : (0 c : Cont) -> IsNaperian c => Type
Log _ @{MkIsNaperian pos} = pos

-- ||| If we have a Naperian container, we can always produce (the unique)
-- ||| inhabitant of it shape
-- public export
-- naperianShape : IsNaperian c => c.Shp
-- naperianShape @{(MkIsNaperian pos)} = ()
-- 
public export
naperianPosEq : IsNaperian c => {0 x, y : c.Shp} -> c.Pos x = c.Pos y
naperianPosEq @{MkIsNaperian _} = Refl

||| A container is cubical whenever it is Finite and Naperian
||| Effectively, captures `Vect n` containers, up to isomorphism
||| Examples: for any `n : Nat`, `Vect n`. Those are all the examples, up to
||| isomorphism. Notably, this also includes a container whose unique set of
||| positions is the set of positions of a binary tree of a particular shape.
||| This is isomorphic to the `Vect k` container, for some `k`,  assuming a 
||| choice of tree traversal (though all of them yield the same `k`). Here 
||| `k` corresponds to the number of positions in that binary tree
public export
data IsCubical : Cont -> Type where
  MkIsCubical : (n : Nat) -> IsCubical (Nap (Fin n))
  
public export
dimHelper : IsCubical c -> Nat
dimHelper (MkIsCubical n) = n
  
||| We call dimension the size of the set of positions of a finite container 
public export
dim : (0 c : Cont) -> IsCubical c => Nat
dim _ @{ic} = dimHelper ic


||| Used in learning, where we want to know that the tangent space over a
||| particular parameter is equal to the parameter space itself
public export
data IsFlat : Cont -> Type where
  MkIsFlat : (p : Type) -> IsFlat ((_ : p) !> p)
