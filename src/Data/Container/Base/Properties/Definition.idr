module Data.Container.Base.Properties.Definition

import public Decidable.Equality
import Data.Fin
import Data.Finite
import Data.Vect

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition

import Misc

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
Properties of containers expressed as type-level predicates.
Some of these mirror aliases in `Object.Definitions`, they're purposefully 
separated with imports, and don't refer to each other

These are thought of as extensional declarations: we need not know anything 
about concrete instances to define these?
-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| Stores the data of a container `c` with an interface `i` on its positions
||| TODO relationship to `Costate (i <!> c)`?
public export
record InterfaceOnPositions (0 c : Cont) (i : Type -> Type) where
  constructor MkI
  ||| For every shape `s` the set of positions `c.Pos s` has that interface
  GetInterface : (s : c.Shp) -> i (c.Pos s)

||| A container is finite when for every shape the set of positions is finite.
||| Examples: vectors, lists, but also finite binary trees.
||| Note, this also requires provision of a particular order. That is, trees 
||| require a choice of a tree traversal. (All of these choices are isomorphic, 
||| but here necessary to make). An alternative would have been a bag instead of
||| a list.
public export
IsFinite : Cont -> Type
IsFinite c = InterfaceOnPositions c Finite

||| A container is decidable if for every shape its set of positions has 
||| decidable equality
public export
IsDecidable : Cont -> Type
IsDecidable c = InterfaceOnPositions c DecEq

||| A container is non-empty when for every shape the set of positions is
||| non-empty. It's witnessed constructively by choosing a position for every
||| shape. It's also the same data as a costate of a container.
||| TODO can this be done without a specific witness?
public export
IsNonEmpty : Cont -> Type 
IsNonEmpty c = InterfaceOnPositions c id

public export
ChosenPositions : Cont -> Type
ChosenPositions = IsNonEmpty

||| A container is non-dependent when positions do not depend on shapes
public export
data IsNonDep : Cont -> Type where
  MkIsNonDep : (s, p : Type) -> IsNonDep ((_ : s) !> p)

||| Following the flat-sharp terminology
public export
data IsFlat : Cont -> Type where
  ItIsFlat : (s : Type) -> IsFlat ((_ : s) !> Unit)

public export
data IsSharp : Cont -> Type where
  ItIsSharp : (s : Type) -> IsSharp ((_ : s) !> Void)

||| Used in learning, where we want to know that the tangent space over a
||| particular parameter is equal to the parameter space itself
||| Follows the terminology of `Const` used in `Object.Instances`
public export
data IsConst : Cont -> Type where
  ItIsConst : (p : Type) -> IsConst ((_ : p) !> p)


namespace Naperian
  ||| Will be removed later, temp fix for now as otherwise the coverage 
  ||| checker complains
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
  ||| A container is foldable if there exists a dependent lens `c =%> List`
  ||| Notably, we do not require this to be an isomorphism. For instance, 
  ||| binary trees are foldable, but not not isomorphic to lists.
  public export
  interface IsFoldable (0 c : Cont) where
    constructor MkIsFoldable
    mapToList : c =%> ((n : Nat) !> Fin n)

  public export
  IsFoldable c => Foldable (Ext c) where
    foldr @{(MkIsFoldable toL)} f z e = foldr
      (\p, acc => f (index e p) acc)
      z
      (tabulate (toL.bwd (shapeExt e)))


  {-
  todo there is a relationship:
  IsFoldable <=> IsFinite
  IsCubical => IsFoldable
  -}



namespace IsConcrete
  ||| Many datatypes in the Idris standard library are already
  ||| concrete representations of particular containers
  public export
  interface IsConcrete (0 c : Cont) where
    constructor MkIsConcrete
    func : Type -> Type
    functorInstance : Functor func
    fromConcreteTy : func a -> Ext c a
    toConcreteTy : Ext c a -> func a

  public export prefix 0 >#, #>

  public export
  (>#) : IsConcrete c => func {c=c} a -> Ext c a
  (>#) = fromConcreteTy

  public export
  (#>) : IsConcrete c => Ext c a -> func {c=c} a
  (#>) = toConcreteTy