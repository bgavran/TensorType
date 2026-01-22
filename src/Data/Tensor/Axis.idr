module Data.Tensor.Axis

import public Decidable.Equality
import Data.Vect.Elem
import Data.Vect.Quantifiers

import Data.Container
import Data.Unique.Vect
import Misc

%hide Syntax.PreorderReasoning.Ops.infixl.(<~)

{-
Design choices:
1) Are axis names bound local to a tensor, or do they persist globally?
2) Can a tensor contain duplicate axis names? (Yes?)
3) How does contraction work?
  3.1) Given `t : Tensor [BatchSize, BatchSize] Double`, what is `dotGeneral t`?


-- axes names persist globally, but are only checked for incompatibilities during
-- tensor formation or tensor operations. Otherwise we'd have to track contexts manually

Language should track context?

"instead of having 'names' be transient bindings to axes that require validation at each einsum function call invocation, and which dissapear right after the said function call, I'm attempting to build in a naming system into the core tensor calculus that persists with the lifetime of the underlying tensor. Similar to Python's XArray"

-}

||| The name for an axis is an arbitrary string
public export
AxisName : Type
AxisName = String

public export infixr 0 ~> -- Constructor for containre-based axes
public export infixr 0 ~~> -- 'Constructor' for cubical axes

||| An axis is a container (representing its size) together with its name
public export
record Axis where
  constructor (~>)
  name : AxisName
  ToCont : Cont

public export
rename : Axis -> AxisName -> Axis
rename a str = str ~> a.ToCont

namespace Cubical
  public export
  (~~>) : AxisName -> Nat -> Axis
  (~~>) axisName n = axisName ~> Vect n
  
  public export
  data IsCubical : Axis -> Type where
    MkIsCubical : (axisName : AxisName) -> (n : Nat) ->
      IsCubical (axisName ~~> n)

  -- public export
  -- cubicalAxisToCont : IsCubical c => IsCubical (c.ToCont)
  -- cubicalAxisToCont @{MkIsCubical _ n} = MkIsCubical n

  -- %hint
  -- public export
  -- cubicalToTensorMonoid : IsCubical c => TensorMonoid (c.ToCont)
  -- cubicalToTensorMonoid @{(MkIsCubical _ n)} = %search

  -- testtt : IsCubical c => TensorMonoid (c.ToCont)
  -- testtt = %search


  public export
  dim : (0 a : Axis) -> IsCubical a => Nat
  dim _ @{(MkIsCubical _ n)} = n

  
  public export
  cubicalShape : (shape : Vect r Axis) -> (ac : All IsCubical shape) => List Nat
  cubicalShape [] {ac = []} = []
  cubicalShape ((_ ~> Vect n) :: ss) {ac = ((MkIsCubical _ n) :: ns)}
    = n :: cubicalShape ss
  
  ||| Size of a cubical tensor, i.e. its number of elements
  public export
  size : (shape : Vect r Axis) -> (ac : All IsCubical shape) => Nat
  size ss = prod (cubicalShape ss)

||| Convenience function, turns it also into a list
||| Because `Data.Container` uses lists with tensors
public export
conts : Vect n Axis -> List Cont
conts as = toList' (ToCont <$> as)

public export
allCubicalAxisToCont : {shape : Vect r Axis} ->
  All IsCubical shape -> All IsCubical (conts shape)
allCubicalAxisToCont {shape = []} [] = []
allCubicalAxisToCont {shape = ((_ ~> _) :: ss)} ((MkIsCubical _ n) :: ics)
  = MkIsCubical n :: allCubicalAxisToCont ics

||| Given some axes, we cannot add one with the same name but a different 
||| container
public export
data NewAxisConsistent : Axis -> Vect n Axis -> Type where
  NewAxis : {0 a : Axis} -> {0 as : Vect n Axis} ->
    NotElem (Axis.name a) (Axis.name <$> as) ->
    NewAxisConsistent a as
  ExistingAxis : {0 a : Axis} -> {0 as : Vect n Axis} ->
    (e : Elem (Axis.name a) (Axis.name <$> as)) ->
    ToCont (index (elemToFin e) as) = ToCont a ->
    NewAxisConsistent a as


||| Axes forming a tensor cannot have the same name but different containers
public export
data AxesConsistent : Vect n Axis -> Type where
  Nil : AxesConsistent []
  (::) : NewAxisConsistent a as -> AxesConsistent as -> AxesConsistent (a :: as)


||| Proof that an axis name is in the shape type
public export
data InAxes : AxisName -> Vect n Axis -> Type where
  Here : {as : Vect k Axis} -> InAxes axisName ((axisName ~> a) :: as)
  There : {as : Vect k Axis} -> InAxes axisName as -> InAxes axisName (a :: as)

public export
removeAllOccurrences : AxisName -> Vect n Axis -> (m : Nat ** Vect m Axis)
removeAllOccurrences name axes = filter (\a => a.name /= name) axes

||| A proof that filtering preserves the property that axes are consistent
public export
filterPreservesConsistent : {shape : Vect n Axis} ->
  (ac : AxesConsistent shape) =>
  (p : Axis -> Bool) ->
  AxesConsistent (snd $ filter p shape)
filterPreservesConsistent {shape = []} p = []
filterPreservesConsistent {shape=(s::ss)} {ac = (a :: as)} p with (filter p ss)
  _ | (k ** ss') = case p s of
      True => ?ai 
      False => ?bi -- case p s of

public export
removingAllOccurencesIsConsistent : {shape : Vect n Axis} ->
  AxesConsistent shape =>
  (toDelete : AxisName) ->
  (inAxes : InAxes toDelete shape) =>
  AxesConsistent (snd $ removeAllOccurrences toDelete shape)
removingAllOccurencesIsConsistent toDelete @{inAxes} = ?remm


aa : {c : Axis} -> AxesConsistent [c, c]
aa = %search

||| Examples
batchSize : Axis
batchSize = "batchSize" ~> Vect 128

seqLen : Axis
seqLen = "seqLen" ~> List

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