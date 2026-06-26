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

||| Can be represented as a derivative
||| See Data.Container.Base.Object.Definition.Path
public export
Path : AddCont -> Type
Path c = (x : c.Shp ** c.Pos x)


||| With an ordinary container `c`, the Pi and Sigma type simple are the 
||| dependent function ((s : c.Shp) -> c.Pos s) and the dependent pair
||| ((s : c.Shp ** c.Pos s)) type: they rely on the (co)product in Set.
||| When the container is additive, the Pi and Sigma type rely on the 
||| (co)product in the category ComMon. Here Pi stays the same, but Sigma
||| ends up being a subtype of the Pi type, with finite support. This means that
||| in the finitary case, product and coproduct coincide.
|||
||| This is a complicated way of saying something simple:
||| The Sigma type, as inherited from Set, is not a monoid. This is because,
||| despite the fact that `c` gives us a monoid structure on every `c.Pos s`, we
||| still can't add `(s1 ** p1)` and `(s2 ** p2)` when `s1 ≠ s2` as
||| `p1` and `p2` have different types. At best, we could do it if `c.Shp` was
||| a monoid, and `c.Pos` was somehow laxly preserving the monoid structure.
|||
||| Instead, we need to use the Pi type representation: ((s : c.Shp) -> c.Pos s)
||| whose monoid structure is given pointwise. When `c.Shp` is an infinite type,
||| we need to ensure that the map above has finite support. Carrying this 
||| explicit support data together with the function is very fiddly
|||
||| It turns out that there is a pragmatic representation of the coproduct:
||| simply as a list of pairs `(s, p)` where `p : c.Pos s` such that:
||| 1) The list order doesn't matter (we need to quotient it out by permutation)
||| 2) Pairs where output is zero can be dropped, i.e. `(s, 0) : xs = xs`
||| 3) Same-shape entires add: `(s, p1) : (s, p2) : xs` = (s, p1 + p2) : xs`
||| That is, all maps that consume this type have to preserve these properties.
|||
||| It turns out that this works surprisingly well, and helps us be performant
||| especially when dealing with autodiff.
|||
||| In other words, any dependent pairs that want to be a monoid should ask
||| themselves if they're instead a list of input-output pairs.
public export
CoprodMon : AddCont -> ComMonoid
CoprodMon c = (List (Path c) ** listIsMonoid)