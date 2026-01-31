module Data.Autodiff.Core.DType

import Data.Container
import Data.Autodiff.AdditiveContainer

||| Wrapper around an additive container exposing its shape at the type level
||| Given `a`, we think of `D a` as evidence of it being differentiable
||| Follows the `D` terminology from Simple Essence of AD paper
public export
data D : (a : Type) -> Type where
  MkTangent : (c : AddCont) -> D (c.Shp)

||| Convenience function to create this wrapper from concrete data
public export
MkD : {a : Type} ->
  (b : a -> Type) ->
  ((x : a) -> ComMonoid (b x)) =>
  D a
MkD b = MkTangent $ MkAddCont $ (x : a) !> b x

||| Extract the underlying additive container, "U" stands for "underlying"
public export
UC : D a -> AddCont
UC (MkTangent c) = c

||| Extract the tangent space
public export
T : D a -> a -> Type
T (MkTangent c) = c.Pos

{-------------------------------
Concrete instances
All of these are annotated with the `%hint` pragma as we do not want the user
to manually have to supply the underlying monoid structure during
-------------------------------}

%hint
public export
doubleTangent : D Double
doubleTangent = MkD (\_ => Double)

-- Note: this should also cover Tensor, since they have a Num instance
%hint
public export
numTangent : {a : Type} -> Num a => D a
numTangent = MkD (\_ => a)

%hint
public export
unitTangent : D Unit
unitTangent = MkD (\_ => ())

%hint
public export
pairTangent : D a -> D b -> D (a, b)
pairTangent (MkTangent (MkAddCont (_ !> posA) @{MkI}))
            (MkTangent (MkAddCont (_ !> posB) @{MkI}))
  = MkD $ \ss => (posA (fst ss), posB (snd ss))

||| Similar to `VectAddCont`, except `VectAddCont` is heterogeneous vectors
public export
vectTangent : {a : Type} -> D a -> D (Vect n a)
vectTangent x = ?vectTangent_rhs

-- = MkD ?vectTangent_rhs @{?cmon}
-- vectD (MkTangent (shp !> pos) {mon=monV}) = MkD
--   (\xs => (i : Fin n) -> pos (index i xs))
--   {mon=(\xs => ?vectD_mon)}

-- listD (MkTangent (Shp !> pos)) = MkD
--   (\xs => let tt = pos <$> xs in ?listD_rhs_1)
--   {mon=(\x => ?llll)}

public export
listTangent : D a -> D (List a)
listTangent x = ?listTangent_rhs