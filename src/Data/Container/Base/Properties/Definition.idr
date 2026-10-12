module Data.Container.Base.Properties.Definition

import public Decidable.Equality
import Data.Fin
import Data.Finite
import Data.Vect

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Endofunctor.Definition

import Data.Container.Base.Object.Instances
import Data.Container.Base.Morphism.Instances

import Misc

{-------------------------------------------------------------------------------
Properties of containers expressed in terms of two constructions:
`MapToWith` and `IsA`.

`Properties` is the intentional exception to the rule of `Definition` not importing `Instances`, as the definitions here refer to *specific* containers, such as `List`, `Scalar`, and `Bag`.
-------------------------------------------------------------------------------}

||| The data of a lens from `d`, with `i` on its positions into `c`. Used to 
||| generically define `IsFoldable`, `IsSummable`, and `InterfaceOnPositions`
public export
interface MapToWith (0 i : Type -> Type) (0 c : Cont) (0 d : Cont) where
  constructor Along
  mapTo : i <!> d =%> c

public export
MapTo : {default id i : Type -> Type} -> Cont -> Cont -> Type
MapTo c d = MapToWith i c d

||| Stores the data of a container `c` with an interface `i` on its positions
||| As a lens `i <!> c =%> Scalar` it is a costate of `i <!> c`
public export
InterfaceOnPositions : Cont -> (Type -> Type) -> Type
InterfaceOnPositions c i = MapTo {i} Scalar c

public export
MkI : ((s : c.Shp) -> i (c.Pos s)) -> InterfaceOnPositions c i
MkI f = Along (toCostate f)

||| For every shape `s` the set of positions `c.Pos s` has that interface
public export
GetInterface : InterfaceOnPositions c i -> (s : c.Shp) -> i (c.Pos s)
GetInterface _ = fromCostate mapTo

%hint
public export
fromPositions : {0 c : Cont} -> {0 i : Type -> Type} ->
  (pos : (s : c.Shp) -> i (c.Pos s)) => InterfaceOnPositions c i
fromPositions @{pos} = MkI pos

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

||| Name more accurately reflecting the fact that position choice is arbitrary
public export
ChosenPositions : Cont -> Type
ChosenPositions = IsNonEmpty

||| Proof that a container `c` of the form `f x` for some `x`.
||| Does not work with two arguments, i.e. this 
||| (https://github.com/bgavran/TensorType/blob/cc67c8b4461467874a55af7756e1b4a7f768c1f0/src/Data/Container/Base/Properties/Definition.idr#L63) does not work with this definition, and would instead 
||| require a `IsA2`. (That particular example was removed because nothing 
||| depended on it)
public export
data IsA : Cont -> (0 f : a -> Cont) -> Type where
  Via : (x : a) -> IsA (f x) f

public export
IsFlat : Cont -> Type
IsFlat c = IsA c Flat

public export
IsSharp : Cont -> Type
IsSharp c = IsA c Sharp

||| Used in learning, where we want to know that the tangent space over a
||| particular parameter is equal to the parameter space itself
public export
IsConst : Cont -> Type
IsConst c = IsA c Const

||| Notably, Naperian does not imply Finite (`Stream` is Naperian)
public export
IsNaperian : Cont -> Type
IsNaperian c = IsA c Nap

namespace NaperianHelpers
  public export
  LogHelper : IsNaperian c => Type
  LogHelper @{Via pos} = pos
  
  public export
  Log : (0 c : Cont) -> IsNaperian c => Type
  Log _ @{Via pos} = pos
  
  public export
  naperianPosEq : IsNaperian c => {0 x, y : c.Shp} -> c.Pos x = c.Pos y
  naperianPosEq @{Via _} = Refl

||| A container is cubical whenever it is Finite and Naperian.
||| All of such containers are `Vect n`, up to isomorphism. Notably, this also 
||| includes a container whose positions are the set of positions of a binary 
||| tree of a particular shape.  This is isomorphic to the `Vect k` container, 
||| for some `k`, assuming a choice of tree traversal
public export
IsCubical : Cont -> Type
IsCubical c = IsA c Vect

namespace CubicalHelpers
  public export
  dimHelper : IsCubical c -> Nat
  dimHelper (Via n) = n
  
  ||| We call dimension the size of the set of positions of a finite container 
  public export
  dim : (0 c : Cont) -> IsCubical c => Nat
  dim _ @{ic} = dimHelper ic
  
  ||| Every cubical container is `Vect n` with `n = dim ic` (used for rewrites).
  public export
  isCubicalContEq : IsCubical d -> d = Vect (dim {c=d})
  isCubicalContEq (Via n) = Refl

||| A container is foldable if there exists a lens `c =%> List`
||| Notably, this isn't required to be an isomorphism. For instance, binary 
||| trees (with ordered branches) are foldable, but not isomorphic to lists.
public export
IsFoldable : Cont -> Type
IsFoldable c = MapTo List c

||| A container is summable if there is a dependent lens `c =%> Bag`. That is,
||| a fold whose order does not matter.
public export
IsSummable : Cont -> Type
IsSummable c = MapTo Bag c

||| The lens of a foldable container into `List`
||| Ideally we would not need this, but `id <!> c` does not reduce to `c`
public export
mapToList : IsFoldable c => c =%> List
mapToList @{Along toL} = !% (%! toL)

public export
mapToBag : IsSummable c => c =%> Bag
mapToBag @{Along toB} = !% (%! toB)

||| A container is enumerable when at every shape its positions are in
||| bijection with `Fin n`, i.e. there is a cartesian morphism into `List`
||| Are these lawful traversables? Every position is visited exactly once, in a 
||| chosen order.  Unlike with `IsFoldable`, positions can neither be skipped 
||| nor repeated
public export
interface IsEnumerable (0 c : Cont) where
  constructor MkIsEnum
  enumerate : c =:> List

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