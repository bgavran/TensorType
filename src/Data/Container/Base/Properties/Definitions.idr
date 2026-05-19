module Data.Container.Base.Properties.Definitions

import Data.Fin
import Data.Finite

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition

import Misc

{-------------------------------------------------------------------------------
States various properties a container can have
Some of these mirror aliases in `Object.Definitions`, they're purposefully 
separated with imports, and don't refer to each other

These are thought of as extensional declarations: we need not know anything 
about concrete instances to define these?

-------------------------------------------------------------------------------}

||| Convenience datatype for storing the data that a container `c` has an
||| interface `i` on its positions
public export
data InterfaceOnPositions : (c : Cont) -> (i : Type -> Type) -> Type where
  ||| For every shape `s` the set of positions `c.Pos s` has that interface
  MkI : ((s : c.Shp) -> i (c.Pos s)) -> InterfaceOnPositions c i

||| A container is finite when for every shape the set of positions is finite.
||| Examples: vectors, lists, but also finite binary trees.
||| Note, provision of a finite instance for trees requires a choice of a tree
||| traversal. (All of these choices isomorphic, but are necessary to make)
public export
IsFinite : Cont -> Type
IsFinite c = InterfaceOnPositions c Finite

||| A container is non-dependent when positions do not depend on shapes
public export
data IsNonDep : Cont -> Type where
  MkIsNonDep : (s, p : Type) -> IsNonDep ((_ : s) !> p)

||| Used in learning, where we want to know that the tangent space over a
||| particular parameter is equal to the parameter space itself
public export
data IsConst : Cont -> Type where
  ItIsConst : (p : Type) -> IsConst ((_ : p) !> p)

||| Following the flat-sharp terminology
public export
data IsFlat : Cont -> Type where
  ItIsFlat : (s : Type) -> IsFlat ((_ : s) !> Unit)

public export
data IsSharp : Cont -> Type where
  ItIsSharp : (s : Type) -> IsSharp ((_ : s) !> Void)

namespace Naperian
  ||| Local alias used solely to keep `MkIsNaperian`'s index out of raw
  ||| record-constructor form. Without this, pattern matches like
  ||| `(MkIsNaperian p :: as)` against `All IsNaperian shape` trip an
  ||| Idris 2 coverage-checker incompleteness (see issue #3721).
  ||| Definitionally equal to `Nap pos` from `Object.Instances`,
  ||| but defined here to avoid an import cycle.
  public export
  NaperianCont : Type -> Cont
  NaperianCont pos = (_ : Unit) !> pos

  ||| A container is Naperian when the set of shapes is `Unit`, i.e. when it
  ||| contains only one set of positions.
  ||| Examples: Scalar, UnitCont, Pair, Vect n, Stream.
  ||| Notably, Naperian does not imply Finite, as the `Stream` example shows.
  public export
  data IsNaperian : Cont -> Type where
    MkIsNaperian : (pos : Type) -> IsNaperian (NaperianCont pos)
  
  public export
  LogHelper : IsNaperian c => Type
  LogHelper @{MkIsNaperian pos} = pos
  
  public export
  Log : (0 c : Cont) -> IsNaperian c => Type
  Log _ @{MkIsNaperian pos} = pos
  
  public export
  naperianPosEq : IsNaperian c => {0 x, y : c.Shp} -> c.Pos x = c.Pos y
  naperianPosEq @{MkIsNaperian _} = Refl

namespace Cubical
  ||| Will be removed later, temp fix for now as otherwise the coverage 
  ||| checker complains
  public export
  CubicalCont : Nat -> Cont
  CubicalCont n = (_ : Unit) !> Fin n

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
    MkIsCubical : (n : Nat) -> IsCubical (CubicalCont n)
    
  public export
  dimHelper : IsCubical c -> Nat
  dimHelper (MkIsCubical n) = n
    
  ||| We call dimension the size of the set of positions of a finite container 
  public export
  dim : (0 c : Cont) -> IsCubical c => Nat
  dim _ @{ic} = dimHelper ic
  
  ||| Every cubical container is `Nap (Fin n)` with `n = dim ic` (used for rewrites).
  public export
  isCubicalContEq : IsCubical d -> d = ((_ : Unit) !> (Fin (dim {c=d})))
  isCubicalContEq (MkIsCubical n) = Refl


namespace IsFoldable
  ||| A container is foldable if `c ≃ List`
  ||| That is, there ought to exist a dependent lens `c =%> List` and back
  ||| Here we only encode one part of this
  public export
  interface IsFoldable (0 c : Cont) where
    constructor MkIsFoldable
    mapToList : c =%> ((n : Nat) !> Fin n)


namespace IsConcrete
  ||| Many datatypes in the Idris standard library are already
  ||| concrete representations of particular containers
  public export
  interface IsConcrete (0 c : Cont) where
    constructor MkIsConcrete
    concreteType : Type -> Type
    concreteFunctor : Functor concreteType
    fromConcreteTy : concreteType a -> Ext c a
    toConcreteTy : Ext c a -> concreteType a

  public export prefix 0 >#, #>

  public export
  (>#) : IsConcrete c => concreteType {c=c} a -> Ext c a
  (>#) = fromConcreteTy

  public export
  (#>) : IsConcrete c => Ext c a -> concreteType {c=c} a
  (#>) = toConcreteTy