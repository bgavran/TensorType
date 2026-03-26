module Data.Tensor.Axis

import public Decidable.Equality
import Data.Vect.Elem
import Data.Vect.Quantifiers

import Data.Container.Base
import Data.Unique.Vect
import Misc

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------

~~~~~~~~~~~~~~~
Design choices:
~~~~~~~~~~~~~~~

1) Persistent axis names.

Instead of transient axis names (bound within a function using the tensor, erased with the completion of the said function), axis names persist with the lifetime of the tensor.

2) Axis declarations persist globally, but are only checked for consistency at call sites.

This means that axis names are checked for consistency at each call site, rather than at declaration sites. In a proper programming language we'd track names at declaration sites and raise errors if inconsistencies/duplicates are detected, here we opt for a more pragmatic approach.

3) Duplicate axis names within a tensor are allowed, as long as they refer to the same container.

Otherwise it would not be clear how to take the diagonal/trace of a matrix while referring only to the axes: they'd have to have different names.

4) Does tensor contraction allow duplicate axis names?



Does tensor contraction allow duplicate axis names
  * in the input (yes, this is what Einsum also allows)
  * in the output (no, because otherwise its not clear what should happen)
    * this means that we can't write `einsum("i,i->ii")`
3) How does contraction work?
  3.1) Given `t : Tensor [BatchSize, BatchSize] Double`, what is `dotGeneral t`?

Need to figure out how `reduce name t` acts when:
1) `name="BatchSize"` and `t : Tensor [BatchSize, BatchSize] Double`
  - Should sum up the diagonal?
2) `name="BatchSize"` and `t : Tensor [BatchSize] Double`
  - Should sum up the vector?
3) `name="BatchSize"` and `t : Tensor [BatchSize, SeqLen, BatchSize] Double`
  - Should sum up the diagonal slices of SeqLen

I suppose this is about iterators
iterating through 




--- Consistency checking: ----------------- 
We check consistency at each call site.
Alternatively if we were building a programming languge we'd check consistency with each declaration. That is, writing something like:
```idris
BatchSize1 : Axis
BatchSize1 = "batchSize" ~> Vect 128

BatchSize2 : Axis
BatchSize2 = "batchSize" ~> Vect 129
```
would throw an error on the line `BatchSize2 = ...` because we're redeclaring "batchSize" which already exists.

------------------------------------------- 

Similar projects/ideas:
* XArray: https://docs.xarray.dev/en/stable/ (persistent axis names)
* Haliax: https://github.com/marin-community/haliax

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| The name for an axis is an arbitrary string
public export
AxisName : Type
AxisName = String

public export infixr 0 ~> -- Constructor for container-based axes
public export infixr 0 ~~> -- 'Constructor' for cubical axes

||| An axis is a container (the "size" of the axis) together with its name
public export
record Axis where
  constructor (~>)
  name : AxisName
  cont : Cont

public export
rename : Axis -> AxisName -> Axis
rename a str = str ~> a.cont


||| In some cases we TensorType might need to assign a default name to an axis,
||| one which is internal and will not be exposed to the user.
||| This is the default name for such cases
public export
TTInternalName : AxisName
TTInternalName = "__tensortype_tempaxis__"


namespace Cubical
  ||| A "constructor" for cubical axes
  public export
  (~~>) : AxisName -> Nat -> Axis
  (~~>) axisName n = axisName ~> Vect n

  ||| Follows the pattern of `IsCubical` from `Data.Container.Object.Instances`
  public export
  data IsCubical : Axis -> Type where
    MkIsCubical : (name : AxisName) -> (n : Nat) -> IsCubical (name ~~> n)

  public export
  dimHelper : {0 a : Axis} -> IsCubical a -> Nat
  dimHelper (MkIsCubical _ n) = n

  public export
  dim : (0 a : Axis) -> IsCubical a => Nat
  dim _ @{ic} = dimHelper ic

  public export
  data IsNaperian : Axis -> Type where
    MkIsNaperian : (name : AxisName) -> (pos : Type) ->
      IsNaperian (name ~> Nap pos)

  public export
  LogHelper : {0 a : Axis} -> IsNaperian a => Type
  LogHelper @{MkIsNaperian _ pos} = pos

  public export
  Log : (0 a : Axis) -> IsNaperian a => Type
  Log a @{inn} = LogHelper @{inn}

  public export
  toContNaperian : {0 a : Axis} -> IsNaperian a ->  IsNaperian a.cont
  toContNaperian (MkIsNaperian name pos) = MkIsNaperian pos

  public export
  cubicalShapeHelper : {0 shape : Vect r Axis} ->
    All IsCubical shape -> List Nat
  cubicalShapeHelper [] = []
  cubicalShapeHelper (ic :: ns) = dimHelper ic :: cubicalShapeHelper ns

  ||| Given a list of cubical axes, return the list of their dimensions
  public export
  cubicalShape : (0 shape : Vect r Axis) -> All IsCubical shape => List Nat
  cubicalShape _ @{ac} = cubicalShapeHelper ac

  ||| Size of a cubical tensor, i.e. its number of elements
  public export
  size : (0 shape : Vect r Axis) -> (ac : All IsCubical shape) => Nat
  size ss = prod (cubicalShape ss)


namespace TensorShape
  mutual
    public export
    data TensorShape : (rank : Nat) ->Type where
      Nil : TensorShape 0
      (::) : (a : Axis) -> (as : TensorShape k) ->
        (ac : NewAxisConsistent a as) =>
        TensorShape (S k)

    public export
    toVect : TensorShape k -> Vect k Axis
    toVect [] = []
    toVect (a :: as) = a :: toVect as

    public export
    data NewAxisConsistent : Axis -> TensorShape k -> Type where
      NewAxis : {0 a : Axis} -> {0 as : TensorShape k} ->
        NotElem a.name (Axis.name <$> toVect as) ->
        NewAxisConsistent a as
      ExistingAxis : {0 a : Axis} -> {0 as : TensorShape k} ->
        (e : Elem a.name (Axis.name <$> toVect as)) ->
        (index (elemToFin e) (toVect as)).cont = a.cont ->
        NewAxisConsistent a as

  public export
  toList : TensorShape k -> List Axis
  toList [] = []
  toList (a :: as) = a :: toList as

  ||| Convenience function, turns it also into a list
  ||| Because `Data.Container` uses lists with tensors
  public export
  conts : TensorShape k -> List Cont
  conts ts = cont <$> toList ts

  ||| Names of the axes in a tensor shape
  public export
  axisNames : TensorShape k -> Vect k AxisName
  axisNames ts = name <$> toVect ts

  ||| Sizes of the axes in a tensor shape
  public export
  axisSizes : TensorShape k -> Vect k Cont
  axisSizes ts = cont <$> toVect ts

  ||| Size of a tensor shape, i.e. its number of elements
  public export
  size : (shape : TensorShape k) -> All IsCubical (conts shape) => Nat
  size shape = size (conts shape)

  test1 : TensorShape 2
  test1 = ["batchSize" ~> Vect 128, "seqLen" ~> List]

  test2 : TensorShape 3
  test2 = ["batchSize" ~> Vect 128, "seqLen" ~> List, "batchSize" ~> Vect 128]

  failing
    test3 : TensorShape 2
    test3 = ["batchSize" ~> Vect 128, "batchSize" ~> Vect 13]

  -- ||| If an axis `i` can be added into a singleton list `[j]`, then
  -- ||| the axis `j` can be added into a singleton list `[i]`
  -- public export
  -- axisConsistentSym : {i, j : Axis} ->
  --   NewAxisConsistent i [j] -> NewAxisConsistent j [i]
  -- axisConsistentSym (NewAxis ne) = NewAxis (notElemSym ne)
  -- -- For some reason we can't pattern match on `Here`? The proof should still 
  -- -- be fine... 
  -- axisConsistentSym (ExistingAxis (There Here) _) impossible
  -- axisConsistentSym (ExistingAxis (There (There later)) _) impossible

  ||| Proof that an axis name appears in a tensor shape n times
  ||| The proof indirectly carries data of the exact indices where it appears
  ||| Notably, can appear zero times, this case is needed for recursion
  public export
  data InShape : AxisName -> TensorShape k -> Nat -> Type where
    Here : {as : TensorShape k} -> InShape axisName as n =>
      NewAxisConsistent (axisName ~> a) as =>
      InShape axisName ((axisName ~> a) :: as) (S n)
    There : {as : TensorShape k} -> InShape axisName as n =>
      NewAxisConsistent a as =>
      InShape axisName (a :: as) n


  ||| Recovers the axis from a shape given its name, and a prof that it is there
  ||| Recovers the first occurence
  public export
  (.getByName) : (shape : TensorShape k) ->
    (axisName : AxisName) -> 
    (inShape : InShape axisName shape n) ->
    IsSucc n =>
    Axis
  (.getByName) ((axisName ~> a) :: as) axisName Here = axisName ~> a
  (.getByName) (a :: as) axisName (There @{is}) = as.getByName axisName is

  public export
  removeAllOccurrences : {k, rank : Nat} ->(shape : TensorShape rank) ->
    (toDelete : AxisName) ->
    (inShape : InShape toDelete shape k) =>
    (m : Nat ** TensorShape m)
  removeAllOccurrences {k=0} shape toDelete = (rank ** shape)
  removeAllOccurrences ((toDelete ~> a) :: ss) toDelete @{Here @{is}}
    = removeAllOccurrences ss toDelete @{is}
  removeAllOccurrences (s :: ss) toDelete @{There @{is}}
    = let (m ** ss') = removeAllOccurrences ss toDelete @{is}
      in (S m ** (::) {ac=(believe_me ())} s ss') -- should write this later


  ||| TODO rethink this function?
  ||| In a tensor shape removes all but the first occurence of an axis
  ||| removeDuplicates ["x" ~> 1, "y" ~> 3, "x" ~> 1] "x" = ["x" ~> 1, "y" ~> 1]
  public export
  removeDuplicates : {k, rank : Nat} -> (shape : TensorShape rank) ->
    (axisName : AxisName) ->
    (inShape : InShape axisName shape k) =>
    IsSucc k =>
    (m : Nat ** TensorShape m)
  removeDuplicates shape axisName {inShape} {k = 1}
    = (rank ** shape)
  removeDuplicates ((_ ~> a) :: as) axisName {inShape = Here @{is}} {k = (S (S k))}
    = removeDuplicates as axisName {inShape=is}
  removeDuplicates (s :: as) axisName {inShape = There @{is}} {k = (S (S k))}
    = let (m ** as') = removeDuplicates as axisName {inShape=is}
      in (S m ** (::) {ac=(believe_me ())} s as')