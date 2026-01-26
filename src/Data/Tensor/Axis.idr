module Data.Tensor.Axis

import public Decidable.Equality
import Data.Vect.Elem
import Data.Vect.Quantifiers

import Data.Container
import Data.Unique.Vect
import Misc

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------

Design choices:
1) Are axis names bound local to a tensor, or do they persist globally?
2) Can a tensor contain duplicate axis names? (Yes?)
3) Does tensor contraction allow duplicate axis names
  * in the input (yes, this is what Einsum also allows)
  * in the output (no, because otherwise its not clear what should happen)
    * this means that we can't write `einsum("i,i->ii")`
3) How does contraction work?
  3.1) Given `t : Tensor [BatchSize, BatchSize] Double`, what is `dotGeneral t`?

"instead of having 'names' be transient bindings to axes that require validation at each einsum function call invocation, and which dissapear right after the said function call, I'm attempting to build in a naming system into the core tensor calculus that persists with the lifetime of the underlying tensor. Similar to Python's XArray"


Need to figure out how `reduce name t` acts when:
1) `name="BatchSize"` and `t : Tensor [BatchSize, BatchSize] Double`
  - Should sum up the diagonal?
2) `name="BatchSize"` and `t : Tensor [BatchSize] Double`
  - Should sum up the vector?
3) `name="BatchSize"` and `t : Tensor [BatchSize, SeqLen, BatchSize] Double`
  - Should sum up the diagonal slices of SeqLen

I suppose this is about iterators
iterating through 



-- axes names persist globally, but are only checked for incompatibilities during
-- tensor formation or tensor operations. Otherwise we'd have to track contexts manually


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
* XArray: https://docs.xarray.dev/en/stable/
* Haliax: https://github.com/marin-community/haliax

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| The name for an axis is an arbitrary string
public export
AxisName : Type
AxisName = String

public export infixr 0 ~> -- Constructor for container-based axes
public export infixr 0 ~~> -- 'Constructor' for cubical axes

||| An axis is a container (representing its size) together with its name
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

  ||| If an axis `i` can be added into a singleton list `[j]`, then
  ||| the axis `j` can be added into a singleton list `[i]`
  %hint
  public export
  axisConsistentSym : {i, j : Axis} ->
    NewAxisConsistent i [j] -> NewAxisConsistent j [i]
  axisConsistentSym (NewAxis ne) = NewAxis (notElemSym ne)
  -- For some reason we can't pattern match on `Here`? The proof should still 
  -- be fine... 
  axisConsistentSym (ExistingAxis (There Here) _) impossible
  axisConsistentSym (ExistingAxis (There (There later)) _) impossible

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

  -- ||| Proof that an axis name is in a tensor shape
  -- ||| There might be multiple axes that match, this contains the proof
  -- ||| for one of them/in
  -- public export
  -- data InShape : AxisName -> TensorShape k -> Type where
  --   Here : {as : TensorShape k} ->
  --     NewAxisConsistent (axisName ~> a) as =>
  --     InShape axisName ((axisName ~> a) :: as)
  --   There : {as : TensorShape k} ->
  --     InShape axisName as ->
  --     NewAxisConsistent a as =>
  --     InShape axisName (a :: as)

  public export
  removeAllOccurrences : {k, n : Nat} ->(shape : TensorShape k) ->
    (toDelete : AxisName) ->
    (inShape : InShape toDelete shape n) =>
    (m : Nat ** TensorShape m)
  removeAllOccurrences {n=0} shape toDelete = (k ** shape)
  removeAllOccurrences ((toDelete ~> a) :: ss) toDelete @{Here @{is}}
    = removeAllOccurrences ss toDelete @{is}
  removeAllOccurrences (s :: ss) toDelete @{There @{is}}
    = let (m ** ss') = removeAllOccurrences ss toDelete @{is}
      in (S m ** (::) {ac=(believe_me ())} s ss') -- should write this later

  --public export
  --removeAllOccurrences : (name : AxisName) ->
  --  TensorShape n ->
  --  (m : Nat ** ts : TensorShape m ** NotElem name (Axis.name <$> toVect ts))
  --removeAllOccurrences name [] = (0 ** [] ** NotInEmptyVect)
  --removeAllOccurrences name (a :: as) = case a.name == name of
  --  True => removeAllOccurrences name as
  --  False => let (k ** ts' ** notInTs) = removeAllOccurrences name as
  --           in (S k ** (::) a ts' @{?bibibi} ** ?vnvnn)

  -- ||| Proof that an axis name is in the shape type
  -- public export
  -- data InShape : AxisName -> Vect n Axis -> Type where
  --   Here : {as : Vect k Axis} -> InShape axisName ((axisName ~> a) :: as)
  --   There : {as : Vect k Axis} -> InShape axisName as -> InShape axisName (a :: as)
  

{-

-- public export
-- allCubicalAxisToCont : {shape : Vect r Axis} ->
--   All IsCubical shape -> All IsCubical (conts shape)
-- allCubicalAxisToCont {shape = []} [] = []
-- allCubicalAxisToCont {shape = ((_ ~> _) :: ss)} ((MkIsCubical _ n) :: ics)
--   = MkIsCubical n :: allCubicalAxisToCont ics




||| A proof that filtering preserves the property that axes are consistent
public export
filterPreservesConsistent : {shape : Vect n Axis} ->
  (ac : AxesConsistent shape) =>
  (p : Axis -> Bool) ->
  AxesConsistent (snd $ filter p shape)
filterPreservesConsistent {shape = []} p = []
filterPreservesConsistent {shape=(s::ss)} {ac = ((NewAxis x) :: as)} p = ?aiii_0
filterPreservesConsistent {shape=(s::ss)} {ac = ((ExistingAxis e prf) :: as)} p = ?aiii_1
-- -- with (filter p ss)
--   _ | (k ** ss') = case p s of
--       True => ?ai 
--       False => ?bi -- case p s of

public export
removingAllOccurencesIsConsistent : {shape : Vect n Axis} ->
  AxesConsistent shape =>
  (toDelete : AxisName) ->
  (InShape : InShape toDelete shape) =>
  AxesConsistent (snd $ removeAllOccurrences toDelete shape)
removingAllOccurencesIsConsistent toDelete @{InShape} = ?remm


aa : {c : Axis} -> AxesConsistent [c, c]
aa = %search

||| While here we can create a new axis with the same name but a different size,
||| they can never be used together in any operations. Theoretically this could
||| be checked at declaration time but it's too much work.
batchSizeNew : Axis
batchSizeNew = "batchSize" ~> Vect 13




{-
namespace Old
  public export
  data NewElemConsistent : String -> Cont ->
    Vect n String -> Vect n Cont -> Type where
    ||| Adding a binding `s->c` not already in `AllConsistent ss cs`
    NewElem : NotElem s ss ->
      NewElemConsistent s c ss cs
    ||| Adding a binding `s->c` already in `AllConsistent ss cs`
    ExistingElem : (e : Elem s ss) ->
      index (elemToFin e) cs = c ->
      NewElemConsistent s c ss cs
  
  
  ||| Type-level predicate: For all pairs of positions where names match,
  ||| the corresponding containers must be equal
  public export
  data AllConsistent : Vect n String -> Vect n Cont -> Type where
    Nil : AllConsistent [] []
    (::) : NewElemConsistent s c ss cs ->
      AllConsistent ss cs ->
      AllConsistent (s :: ss) (c :: cs)
-}

{-
||| Given some axes, we cannot add one with the same name but a different 
||| container
public export
data NewAxisConsistent : Axis -> Vect n Axis -> Type where
  NewAxis : {0 a : Axis} -> {0 as : Vect n Axis} ->
    NotElem (Axis.name a) (Axis.name <$> as) ->
    NewAxisConsistent a as
  ExistingAxis : {0 a : Axis} -> {0 as : Vect n Axis} ->
    (e : Elem (Axis.name a) (Axis.name <$> as)) ->
    (index (elemToFin e) as).cont = a.cont ->
    NewAxisConsistent a as


||| Axes forming a tensor cannot have the same name but different containers
public export
data AxesConsistent : Vect n Axis -> Type where
  Nil : AxesConsistent []
  (::) : NewAxisConsistent a as -> AxesConsistent as -> AxesConsistent (a :: as)
-}
