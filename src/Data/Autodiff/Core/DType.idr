module Data.Autodiff.Core.DType

import Data.Container
import Data.Autodiff.AdditiveContainer

||| Wrapper around an additive container exposing its shape at the type level
||| We think of `D a` as containing the tangent space of `a`
public export
data D : (a : Type) -> Type where
  MkTangent : (c : AddCont) -> D (c.Shp)

||| Convenience function to create this wrapper from concrete data
public export
MkD : {a : Type} ->
  (b : a -> Type) ->
  {auto mon : (x : a) -> ComMonoid (b x)} ->
  D a
MkD b = MkTangent $ MkAddCont $ (x : a) !> b x

||| Extract the tangent space
public export
T : D a -> a -> Type
T (MkTangent c) = c.Pos

||| Extract the underlying additive container
public export
UC : D a -> Cont
UC (MkTangent c) = UC c

-- ||| Underlying monoid structure of positions
-- public export
-- UMon : {a : Type} ->
--   (da : D a) -> (s : (UC da).Shp) -> ComMonoid (let tt = T da in ?hhh) -- T {a=a} da s)

-- public export
-- UMon : (c : AddCont) -> (s : c.Shp) -> ComMonoid (c.Pos s)

--------------------------------
-- Concrete instances
--------------------------------

%hint
public export
doubleTangent : D Double
doubleTangent = MkD (\_ => Double)

-- since tensors have a Num instance, this should cover them
%hint
public export
numTangent : {a : Type} ->
  Num a => D a
numTangent = MkD (\_ => a)

%hint
public export
unitTangent : D Unit
unitTangent = MkD (\_ => ())

%hint
public export
pairD : D a -> D b -> D (a, b)
pairD (MkTangent (MkAddCont (shp !> pos) @{MkI}))
      (MkTangent (MkAddCont (shp' !> pos') @{MkI}))
  = MkD (\ss => (pos (fst ss), pos' (snd ss)))