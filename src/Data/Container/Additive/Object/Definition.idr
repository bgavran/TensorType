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
  UC : Cont
  {auto mon : InterfaceOnPositions UC ComMonoid}

public export
(.Shp) : AddCont -> Type
(.Shp) c = Shp (UC c)

public export
(.Pos) : (c : AddCont) -> c.Shp -> Type
(.Pos) c = Pos (UC c)

||| Underlying monoid structure of positions
public export
UMon : (c : AddCont) -> (s : c.Shp) -> ComMonoid (c.Pos s)
UMon c = GetInterface (mon c)

public export
(.Plus) : (c : AddCont) -> (s : c.Shp) -> c.Pos s -> c.Pos s -> c.Pos s
(.Plus) c s = plus (UMon c s)

public export
(.Zero) : (c : AddCont) -> (s : c.Shp) -> c.Pos s
(.Zero) c s = neutral (UMon c s)

||| Given a container `c`, i.e. a`c.Shp`-indexed family of sets, it is 
||| straightforward to compute the coproduct of this family/its Sigma type:
||| It is simply the type of dependent pairs `(s : c.Shp ** c.Pos s)`.
|||
||| But given an additive container, i.e. a `c.Shp`-indexed family of 
||| *commutative monoids*, its coproduct / Sigma type is a bit tricky:
||| Despite the fact that we have a monoid structure on every `c.Pos s`, we
||| cannot naively use the type of dependent pairs `(s : c.Shp ** c.Pos s)` as
||| the base set. This is because it doesn't form a monoid: we cannot add 
||| `(s1 ** p1)` and `(s2 ** p2)` when `s1 ≠ s2` as `p1` and `p2` have 
||| different types.
|||
||| Instead, we add them *formally*. We can use the free monoid construction on
||| this dependent pair, and quotient it out by certain relations. Specifically,
||| we use the base set `List (x : c.Shp ** c.Pos x)` quotiented out by:
||| 1) Permutation (the list order should not matter)
||| 2) `(s, 0) : xs = xs` (pairs where output is zero can be dropped)
||| 3) `(s, p1) : (s, p2) : xs` = (s, p1 + p2) : xs` (same-shape entires add)
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
DPair c = List (DPair (UC c))