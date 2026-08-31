module Data.Container.Additive.Object.Definition

import Data.Container.Base
import Data.ComMonoid

||| Additive container: a container whose every set of positions is a
||| commutative monoid.
||| Not to be confused with `TensorMonoid` where the set of shapes is a monoid,
||| and every set of positions is a comonoid
||| We need additivity only because we want to copy/delete information: on the
||| backwards pass this sums up or creates a zero value
||| TODO this in some sense dual to `TensorMonoid`, since by default we have a
||| unique comonoid structure on shapes? I.e. every set is uniquely a comonoid
public export
record AddCont where
  constructor MkAddCont
  Shp : Type
  Pos : Shp -> ComMonoid

||| The underlying container of an additive container.
||| Left adjoint
public export
UC : AddCont -> Cont
UC c = (s : c.Shp) !> uSet (c.Pos s)

public export
(.PosSet) : (c : AddCont) -> c.Shp -> Type
(.PosSet) c s = uSet (c.Pos s)

||| Underlying monoid structure of positions
public export
UMon : (c : AddCont) -> (s : c.Shp) -> ComMonoid (c.PosSet s)
UMon c s = snd (c.Pos s)

namespace NotExposingType
  public export
  UMon : (c : AddCont) -> (s : c.Shp) -> ComMonoid
  UMon c s = c.Pos s

||| The monoid structure on positions, packaged as an interface section on the
||| underlying container (compatibility with the unbundled presentation)
public export
mon : (c : AddCont) -> InterfaceOnPositions (UC c) ComMonoid
mon c = MkI (\s => UMon c s)

public export
(.Plus) : (c : AddCont) -> (s : c.Shp) -> c.PosSet s -> c.PosSet s -> c.PosSet s
(.Plus) c s = plus (UMon c s)

public export
(.Zero) : (c : AddCont) -> (s : c.Shp) -> c.PosSet s
(.Zero) c s = neutral (UMon c s)

||| Given a container `c`, i.e. a`c.Shp`-indexed family of sets, it is
||| straightforward to compute the coproduct of this family/its Sigma type:
||| It is simply the type of dependent pairs `(s : c.Shp ** c.Pos s)`.
|||
||| But given an additive container, i.e. a `c.Shp`-indexed family of
||| *commutative monoids*, its coproduct / Sigma type is a bit tricky:
||| Despite the fact that we have a monoid structure on every `c.PosSet s`, we
||| cannot naively use the type of dependent pairs `(s : c.Shp ** c.PosSet s)` 
||| as the base set. This is because it doesn't form a monoid: we cannot add
||| `(s1 ** p1)` and `(s2 ** p2)` when `s1 ≠ s2` as `p1` and `p2` have 
||| different types.
|||
||| Instead, we add them *formally*. We can use the free commutative monoid
||| construction on this dependent pair, and quotient it out by certain
||| relations. Specifically, we use the base set `Bag (x : c.Shp ** c.PosSet x)`
||| quotiented out by:
||| 1) `(s, 0) : xs = xs` (pairs where output is zero can be dropped)
||| 2) `(s, p1) : (s, p2) : xs` = (s, p1 + p2) : xs` (same-shape entires add)
|||
||| We don't enforce these properties here, but instead need to check that all
||| maps consuming this type preserve them.
|||
||| Abstractly, we can state the following:
||| * the Pi type of additive containers is inherited from ordinary containers
||| * When `c.Shp` is finite, Pi and Sigma type of additive containers coincide
|||   (i.e. in the finitary case, product and coproduct coincide)
||| * When `c.Shp` is not finite, Sigma type is the subtype of Pi type, with finite support
public export
DPair : AddCont -> Type
DPair c = Bag (DPair (UC c))
