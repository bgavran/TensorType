module Data.Container.Additive.Morphism.Instances

import Data.Vect
import Data.Vect.Quantifiers

import Data.Container.Base
import Data.ComMonoid
import Data.Num
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Object.Instances
import Data.Container.Additive.Morphism.Definition
import Data.Container.Additive.Product.Definitions

import Control.Monad.Distribution
import Control.Monad.Sample.Definition

import Misc

%hide Data.Container.Base.Object.Instances.Const
%hide Data.Vect.Quantifiers.All.index

public export
State : {0 c : AddCont} -> (x : c.Shp) -> Scalar =%> c
State x = !%+ \() => (x ** \_ => ())

public export
Costate : {0 c : AddCont} ->
  (s : (x : c.Shp) -> c.Pos x) ->
  c =%> Scalar
Costate s = !%+ \x => (() ** \() => s x)

namespace Monadic
  public export
  State : {m : Type -> Type} -> Monad m => {0 c : AddCont} ->
    (x : c.Shp) -> MAddLens {m} Scalar c
  State x = !%%+ \() => pure (x ** \_ => ())

public export
constantOne : {c : AddCont} ->
  InterfaceOnPositions c Num =>
  c =%> Scalar
constantOne @{MkI @{p}} = Costate {c=c} (\x => let numPos = p x in 1)

public export
rightUnit : {c : AddCont} -> (c >< Scalar) =%> c
rightUnit = !%+ \(x, ()) => (x ** \x' => (x', ()))

public export
rightUnitInv : {c : AddCont} -> c =%> (c >< Scalar)
rightUnitInv = !%+ \x => ((x, ()) ** \(x', ()) => x')

public export
leftUnitInv : {c : AddCont} -> c =%> (Scalar >< c)
leftUnitInv = !%+ \x => (((), x) ** \((), x') => x')

namespace Monadic
  public export
  rightUnitInv : {m : Type -> Type} -> Monad m => {c : AddCont} ->
    MAddLens {m} c (c >< Scalar)
  rightUnitInv = !%%+ \x => pure ((x, ()) ** \x'unit => fst x'unit)

  public export
  leftUnitInv : {m : Type -> Type} -> Monad m => {c : AddCont} ->
    MAddLens {m} c (Scalar >< c)
  leftUnitInv = !%%+ \x => pure (((), x) ** \unitx' => snd unitx')

public export
swapMiddle : {c1, c2, c3, c4 : AddCont} ->
  ((c1 >< c2) >< (c3 >< c4)) =%> ((c1 >< c3) >< (c2 >< c4))
swapMiddle = !%+ \((x, y), (z, w)) => (((x, z), (y, w)) **
  \((x', z'), (y', w')) => ((x', y'), (z', w')))

public export
Copy : {c : AddCont} ->
  c =%> (c >< c)
Copy = !%+ \x => ((x, x) ** uncurry (c.Plus x))

public export
Delete : {c : AddCont} ->
  c =%> Scalar
Delete = !%+ \x => (() ** \() => c.Zero x)

public export
ProjLeft : {c, d : AddCont} ->
  (c >< d) =%> c
ProjLeft = !%+ \(x, y) => (x ** \x' => (x', d.Zero y))

public export
ProjRight : {c, d : AddCont} ->
  (c >< d) =%> d
ProjRight = !%+ \(x, y) => (y ** \y' => (c.Zero x, y'))

public export
Sum : Num a =>
  (Const a >< Const a) =%> Const a
Sum = !%+ \(x1, x2) => (x1 + x2 ** \x' => (x', x'))

public export
Negate : Num a => Neg a =>
  Const a =%> Const a
Negate = !%+ \x => (-x ** \x' => -x')

public export
Zero : Num a =>
  Scalar =%> Const a
Zero = State 0

public export
Mul : Num a =>
  (Const a >< Const a) =%> Const a
Mul = !%+ \(x1, x2) => (x1 * x2 ** \x' => (x' * x2, x' * x1))

||| Mean squared error
public export
SquaredDifference : {a : Type} -> Num a => Neg a => (Const a >< Const a) =%> (Const a)
SquaredDifference = ((id {c=Const a}) >< Negate) %>> Sum %>> Copy %>> Mul

public export
fromCostate : {m : Type -> Type} -> Monad m => {0 c : AddCont} ->
  MAddLens {m=m} c Scalar ->
  (x : c.Shp) -> m (c.Pos x)
fromCostate f x = ((\b => b ()) . snd) <$> ((%%!+ f) x)

namespace Sample
  ||| Select a shape from All to produce an Any at the given index
  ||| Same as `index i (allAnies shapes)` but reduces better
  public export
  selectShape : {cs : Vect k AddCont} ->
    (i : Fin k) -> (shapes : All (.Shp) cs) -> Any (.Shp) cs
  selectShape FZ (s :: ss) = Here s
  selectShape (FS j) (s :: ss) = There (selectShape j ss)

  ||| Extract the position from an AnyPos at a given index
  public export
  extractPos : {n : Nat} -> {xs : Vect n AddCont} -> {shapes : All (.Shp) xs} ->
    (i : Fin n) ->
    AnyPos (selectShape i shapes) ->
    (index i xs).Pos (index i shapes)
  extractPos {shapes = (_ :: _)} FZ (Here x') = x'
  extractPos {shapes = (_ :: _)} (FS j) (There rest) = extractPos j rest
  
  ||| Sample from a convex combination of options.
  |||
  ||| Forward: Sample an index, and route only the chosen shape forward.
  |||
  ||| Backward: receive a position for the chosen branch, and return it
  ||| as a singleton tagged list. Gradients w.r.t. distribution are 0
  public export
  Sample : {m : Type -> Type} -> MonadSample m =>
    {n : Nat} -> IsSucc n =>
    {xs : Vect n AddCont} ->
    MAddLens {m=m} (ConvexComb xs) (Any xs)
  Sample = !%%+ \(d, shapes) => do
    i <- sample d
    pure (selectShape i shapes ** \x' => (0, [(i ** extractPos i x')]))

  public export
  GetDist : {m : Type -> Type} -> MonadSample m =>
    {n : Nat} -> IsSucc n =>
    {xs : Vect n AddCont} ->
    MAddLens {m=m} (ConvexComb xs) (Simplex n)
  GetDist = liftAddDLens (ProjLeft {d=PreparedChoice xs})

  ||| Same as 'Sample' but preserves the distribution
  public export
  SampleAndKeepDist : {m : Type -> Type} -> MonadSample m =>
    {n : Nat} -> IsSucc n =>
    {xs : Vect n AddCont} ->
    MAddLens {m=m} (ConvexComb xs) (Simplex n >< Any xs)
  SampleAndKeepDist = liftAddDLens Copy %%+>> (GetDist >< Sample)

  ||| Same as 'Sample' but preserves the distribution
  public export
  SampleAndKeepDistt : {m : Type -> Type} -> MonadSample m =>
    {n : Nat} -> IsSucc n =>
    {xs : Vect n AddCont} ->
    MAddLens {m=m} (ConvexComb xs) (Simplex n >@ Any xs)
  SampleAndKeepDistt = !%%+ \(d, shapes) => do
    (i ** ki) <- (%%!+ Sample) (d, shapes)
    pure (d <| \_ => i ** \di => ki (snd di))
