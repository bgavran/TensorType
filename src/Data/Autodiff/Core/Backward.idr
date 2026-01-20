module Data.Autodiff.Core.Backward

import Data.Tensor
import Data.Autodiff.AdditiveContainer
import Data.Autodiff.Core.DType

||| Backward differentiable functions, modelled as dependent lenses
||| Exposing the type of the forward pass at the type level
public export
data BwDifferentiable : (da : D a) => (db : D b) => (f : a -> b) -> Type where
  MkBwDifferentiable : {c, d : AddCont} ->
    (bLens : c =%> d) ->
    BwDifferentiable {da=(MkTangent c)} {db=(MkTangent d)} (bLens.fwd)

public export
ULens : {0 a, b : Type} -> {da : D a} -> {db : D b} -> {f : a -> b} ->
  BwDifferentiable f -> UC da =%> UC db
ULens (MkBwDifferentiable f) = ULens f

public export
MkBwDiff :
  {a, b : Type} -> (da : D a) => (db : D b) =>
  {f : a -> b} -> -- implicit because available in type signature
  (f' : (x : a) -> T db (f x) -> T da x) ->
  BwDifferentiable {da = da} {db = db} f
MkBwDiff {da = (MkTangent $ MkAddCont (a !> a')) }
         {db = (MkTangent $ MkAddCont (b !> b')) }
         {f} f' = MkBwDifferentiable
    {c=(MkAddCont ((x : a) !> a' x) )}
    {d=(MkAddCont ((y : b) !> b' y) )}
    (!% (!% \x => (f x ** f' x)))

public export
composeBwDifferentiable : {ca, cb, cc : AddCont} ->
  (f : ca.Shp -> cb.Shp) -> (g : cb.Shp  -> cc.Shp) ->
  (f' : BwDifferentiable {da=(MkTangent ca)} {db=(MkTangent cb)} f) =>
  (g' : BwDifferentiable {da=(MkTangent cb)} {db=(MkTangent cc)} g) =>
  BwDifferentiable {da=(MkTangent ca)} {db=(MkTangent cc)} (g . f)
composeBwDifferentiable (fLens .fwd) (gLens .fwd)
  {f' = (MkBwDifferentiable fLens)}
  {g' = (MkBwDifferentiable gLens)} = MkBwDiff
    {da=(MkTangent ca)}
    {db=(MkTangent cc)}
    (\x, x' => snd ((%! fLens %>> gLens) x) (believe_me x')) -- rewrite


-- probably good to add some functionality for converting between forward and backward mode