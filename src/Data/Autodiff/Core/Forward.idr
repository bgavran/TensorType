module Data.Autodiff.Core.Forward

import Data.Tensor
import Data.Autodiff.AdditiveContainer
import Data.Autodiff.Core.DType

||| Forward differentiable functions, modelled as dependent charts
||| Exposing the type of the forward pass at the type level
public export
data FwDifferentiable : (da : D a) => (db : D b) => (f : a -> b) -> Type where
  MkFwDifferentiable : {c, d : AddCont} ->
    (dChart : c =&> d) ->
    FwDifferentiable {da=(MkTangent c)} {db=(MkTangent d)} (dChart.fwd)

||| Extracts the underlying chart from a differentiable function
public export
UChart : {0 a, b : Type} -> {da : D a} -> {db : D b} -> {f : a -> b} ->
   FwDifferentiable f -> UC da =&> UC db
UChart (MkFwDifferentiable dChart) = UChart dChart

||| Convenience function to create a differentiable function
||| `f` is implicit because on call sites we don't want to repeat it twice
public export
MkFwDiff :
  {a, b : Type} -> (da : D a) => (db : D b) =>
  {f : a -> b} -> -- implicit because available in type signature
  (f' : (x : a) -> T da x -> T db (f x)) ->
  FwDifferentiable {da = da} {db = db} f
MkFwDiff {da = (MkTangent $ MkAddCont (a !> a')) }
         {db = (MkTangent $ MkAddCont (b !> b')) }
         {f} f' = MkFwDifferentiable
    {c=(MkAddCont ((x : a) !> a' x) )}
    {d=(MkAddCont ((y : b) !> b' y) )}
    (!& (!& \x => (f x ** f' x)))


public export
composeFwDifferentiable : {ca, cb, cc : AddCont} ->
  (f : ca.Shp -> cb.Shp) -> (g : cb.Shp  -> cc.Shp) ->
  (f' : FwDifferentiable {da=(MkTangent ca)} {db=(MkTangent cb)} f) =>
  (g' : FwDifferentiable {da=(MkTangent cb)} {db=(MkTangent cc)} g) =>
  FwDifferentiable {da=(MkTangent ca)} {db=(MkTangent cc)} (g . f)
composeFwDifferentiable (fChart .fwd) (gChart .fwd)
  {f' = (MkFwDifferentiable fChart)}
  {g' = (MkFwDifferentiable gChart)} = MkFwDiff
    {da=(MkTangent ca)}
    {db=(MkTangent cc)}
    (\x, x' => believe_me $ snd ((&! fChart &>> gChart) x) x')

{-

%hint
public export
vectD : {n : Nat} -> D a -> D (Vect n a)
vectD (MkTangent (shp !> pos) {mon=monV}) = MkD
  (\xs => (i : Fin n) -> pos (index i xs))
  {mon=(\xs => ?vectD_mon)}

-- Can't really do lists, not sure why
listD : D a -> D (List a)
-- listD (MkTangent (Shp !> pos)) = MkD
--   (\xs => let tt = pos <$> xs in ?listD_rhs_1)
--   {mon=(\x => ?llll)}


