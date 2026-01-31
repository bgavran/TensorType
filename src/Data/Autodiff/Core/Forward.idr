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
    FwDifferentiable {da=(MkTangent c)} {db=(MkTangent d)} dChart.fwd

||| Extracts the underlying chart from a differentiable function
public export
UChart : {da : D a} -> {db : D b} -> {f : a -> b} ->
   FwDifferentiable f -> UC da =&> UC db
UChart (MkFwDifferentiable dChart) = dChart

||| Convenience function for creating a forward differentiable function
||| `f` is implicit because on call sites we don't want to repeat it twice
public export
MkFwDiff : {da : D a} -> {db : D b} ->
  {f : a -> b} ->
  (f' : (x : a) -> T da x -> T db (f x)) ->
  FwDifferentiable f
MkFwDiff {da = MkTangent _} {db = MkTangent _} f'
  = MkFwDifferentiable (!& (!& \x => (f x ** f' x)))

{------------------------------
But there is a problem with the above code: it doesn't work. Here's why.
------------------------------}

-- The idea is to be able to take a function like this:
public export
MyMul : Num a => (a, a) -> a
MyMul = uncurry (*)

-- write its derivaive like this, and annotate it with `%hint`
%hint
public export
myMulDifferentiable : {a : Type} -> Num a => FwDifferentiable (MyMul {a=a})
myMulDifferentiable = MkFwDiff $ \(a1, a2), (a1', a2') => a1' * a2 + a2' * a1

-- so that whenever we use `MyMul`, it becomes directly discoverable.
-- the problem is, that doesn't work.
failing "Can't find an implementation for FwDifferentiable MyMul"
  findDerivativeOfMyMul : FwDifferentiable MyMul
  findDerivativeOfMyMul = %search

-- The same problem happens with other functions, for example
public export
MyCopy : a -> (a, a)
MyCopy x = (x, x)

-- and then we'd want to make this work for a definition of composition
-- such as this:
%hint
public export
composeFwDifferentiable :
  {da : D a} -> {db : D b} -> {dc : D c} ->
  (f : a -> b) -> (df : FwDifferentiable f) =>
  (g : b -> c) -> (dg : FwDifferentiable g) =>
  FwDifferentiable (g . f)
composeFwDifferentiable
  {da = MkTangent contA}
  {db = MkTangent contB}
  {dc = MkTangent contC}
  f
  g = believe_me $ MkFwDifferentiable $ (UChart df &>> UChart dg)
  -- or MkFwDiff ?

-- but instantiations of this with concrete data are very fiddly, and I can't seem to get them to work with the cryptic errors of "non-linear pattern variable"

{- old code and tests below:

%hint
public export
myCopyDifferentiable : Num a => FwDifferentiable (MyCopy {a=a})
myCopyDifferentiable = MkFwDiff $ \x1', x2' => x1' + x2'

testCp  : FwDifferentiable MyCopy
testCp = %search


compositionTest : FwDifferentiable (MyMul {a=Double} . MyCopy {a=Double})
compositionTest = ?aai -- let tcomp = composeFwDifferentiable (MyCopy {a=Double}) (MyMul {a=Double})
                  -- in ?compositionTest_rhs


{-
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

{-
-- Composition using chart composition directly
public export
(>>>) : {ca, cb, cc : AddCont} ->
  {0 f : ca.Shp -> cb.Shp} ->
  {0 g : cb.Shp -> cc.Shp} ->
  FwDifferentiable {da=MkTangent ca} {db=MkTangent cb} f ->
  FwDifferentiable {da=MkTangent cb} {db=MkTangent cc} g ->
  FwDifferentiable {da=MkTangent ca} {db=MkTangent cc} (g . f)
-- Note: believe_me is needed because (fChart &>> gChart).fwd doesn't
-- definitionally equal (gChart.fwd . fChart.fwd), even though they
-- compute the same thing. This is safe because the chart composition
-- is correct.
(>>>) (MkFwDifferentiable {c=ca'} {d=cb'} fChart) 
      (MkFwDifferentiable {c=cb'} {d=cc'} gChart) =
  believe_me $ MkFwDifferentiable (fChart &>> gChart)

%hint
public export
composeFwDifferentiable :
  D a => D b => D c =>
  {f : a -> b} -> FwDifferentiable f =>
  {g : b -> c} -> FwDifferentiable g =>
  FwDifferentiable (g . f)
composeFwDifferentiable = ?composeFwDifferentiable_rhs