module Data.Container.Additive.Morphism.Instances

import Data.Vect
import Data.List.Quantifiers
import Data.Vect.Quantifiers

import Data.Container.Base
import Data.ComMonoid
import Data.Num
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Object.Instances
import Data.Container.Additive.Morphism.Definition
import Data.Container.Additive.Product.Definitions

import Data.Container.Additive.Quantifiers

import Control.Monad.Distribution
import Control.Monad.Sample.Definition

import Misc

%hide Data.Container.Base.Object.Instances.Const
%hide Data.Vect.Quantifiers.All.index

public export
toState : {0 c : AddCont} -> (x : c.Shp) -> Scalar =%> c
toState x = !%+ \() => (x ** \_ => ())

public export
fromState : {0 c : AddCont} -> Scalar =%> c -> c.Shp
fromState f = f.fwd ()

public export
toCostate : {0 c : AddCont} ->
  (s : (x : c.Shp) -> c.Pos x) ->
  c =%> Scalar
toCostate s = !%+ \x => (() ** \() => s x)

public export
fromCostate : {0 c : AddCont} ->
  c =%> Scalar ->
  (x : c.Shp) -> c.Pos x
fromCostate f x = f.bwd x ()


public export
pushDown : AddCont -> AddCont
pushDown d = !! (Const2 Unit d.Shp)

public export
pushIntoContinuationList : {d, p, l : AddCont} ->
  (f : d >< p =%> l) ->
  (p =%> (pushDown d) >@ (List l))
pushIntoContinuationList f = !%+ \param => (() <|
  \ds => map (\dShp => f.fwd (dShp, param)) ds **
    \ll => sum @{UMon p param} (ll >>=
      \(ds ** grads) => extractPGrads param ds grads))
  where
    extractPGrads : (param : p.Shp) ->
      (ds : List d.Shp) ->
      All l.Pos ((\dShp => f.fwd (dShp, param)) <$> ds) ->
      List (p.Pos param)
    extractPGrads param [] [] = []
    extractPGrads param (dShp :: ds) (grad :: grads) =
      snd (f.bwd (dShp, param) grad) :: extractPGrads param ds grads

public export
pushIntoContinuation : {d, p, l : AddCont} -> (flat : IsFlat l) => Num l.Shp =>
  (f : d >< p =%> l) ->
  (p =%> (pushDown d) >@ l)
pushIntoContinuation {flat = MkIsFlat _} f = !%+ \param => (() <|
  \ds => sum @{numIsMonoid} (map (\dShp => f.fwd (dShp, param)) ds) **
    \ll => sum @{UMon p param} (ll >>=
      \(ds ** grad) => (\dShp => snd (f.bwd (dShp, param) grad)) <$> ds))

namespace Monadic
  public export
  State : {m : Type -> Type} -> Monad m => {0 c : AddCont} ->
    (x : c.Shp) -> MAddLens {m} Scalar c
  State x = !%%+ \() => pure (x ** \_ => ())

public export
constantOne : {c : AddCont} ->
  InterfaceOnPositions c Num =>
  c =%> Scalar
constantOne @{MkI @{p}} = toCostate {c=c} (\x => let numPos = p x in 1)

namespace HancockTensorProduct
  public export
  leftUnit : {c : AddCont} -> (Scalar >< c) =%> c
  leftUnit = !%+ \((), s) => (s ** \p => ((), p))
  
  public export
  rightUnit : {c : AddCont} -> (c >< Scalar) =%> c
  rightUnit = !%+ \(x, ()) => (x ** \x' => (x', ()))

  public export
  leftUnitInv : {c : AddCont} -> c =%> (Scalar >< c)
  leftUnitInv = !%+ \x => (((), x) ** \((), x') => x')
  
  public export
  rightUnitInv : {c : AddCont} -> c =%> (c >< Scalar)
  rightUnitInv = !%+ \x => ((x, ()) ** \(x', ()) => x')

  public export
  assocL : {0 a, b, c : AddCont} -> ((a >< b) >< c) =%> (a >< (b >< c))
  assocL = !%+ \((a, b), c) => ((a, (b, c)) ** \(a', (b', c')) => ((a', b'), c'))

  public export
  assocR : {0 a, b, c : AddCont} -> (a >< (b >< c)) =%> ((a >< b) >< c)
  assocR = !%+ \(a, (b, c)) => (((a, b), c) ** \((a', b'), c') => (a', (b', c')))

  public export
  swap : {0 a, b : AddCont} -> (a >< b) =%> (b >< a)
  swap = !%+ \(a, b) => ((b, a) ** \(b', a') => (a', b'))

namespace CompositionProduct
  public export
  leftUnit : {c : AddCont} -> (Scalar >@ c) =%> c
  leftUnit = !%+ \(() <| cShp) => (cShp () ** \c' => [(() ** c')])

  public export
  rightUnit : {c : AddCont} -> (c >@ Scalar) =%> c
  rightUnit = !%+ \(s <| _) => (s ** \p => [(p ** ())])

  public export
  leftUnitInv : {c : AddCont} -> c =%> (Scalar >@ c)
  leftUnitInv = !%+ \s => (() <| (\_ => s) ** \ll =>
    sum @{UMon c s} (snd <$> ll))
  
  ||| Right unit inverse: c =%> c >@ I
  public export
  rightUnitInv : {c : AddCont} -> c =%> (c >@ Scalar)
  rightUnitInv = !%+ \s => (s <| const () ** \ll =>
    sum @{UMon c s} (fst <$> ll))

public export
duoidal : {c, d, e, f : AddCont} ->
  ((c >@ d) >< (e >@ f)) =%> ((c >< e) >@ (d >< f))
duoidal = !%+ \((sc <| idxC), (se <| idxE)) =>
  ((sc, se) <| \(cp, ep) => (idxC cp, idxE ep) **
    \ll => ((\((cp, ep) ** (dp, fp)) => (cp ** dp)) <$> ll,
            (\((cp, ep) ** (dp, fp)) => (ep ** fp)) <$> ll))

public export
rebracketcomptensor: {e, y : AddCont} -> ((e >@ y) >< y) =%> (e >@ (y >< y))
rebracketcomptensor = (id {c=e >@ y} >< leftUnitInv {c=y})
                      %>> duoidal {c=e} {d=y} {e=Scalar} {f=y}
                      %>> (rightUnit {c=e} >@ id {c=(y><y)})


public export
distribute : {c, e, g : AddCont} ->
  ((c >< e) =%> s) ->
  ((c >< (e >@ g)) =%> (s >@ g))
distribute f = (rightUnitInv >< id {c=e >@ g})
             %>> duoidal {d = Scalar}
             %>> (f >@ leftUnit)

  
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
PairMaps : {c, d, e : AddCont} ->
  (f : c =%> d) ->
  (g : c =%> e) ->
  c =%> (d >< e)
PairMaps f g = Copy %>> (f >< g)

public export
Delete : {c : AddCont} ->
  c =%> Scalar
Delete = !%+ \x => (() ** \() => c.Zero x)

||| Note that this doesn't exist for ordinary containers!
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
Zero = toState 0

public export
Mul : Num a =>
  (Const a >< Const a) =%> Const a
Mul = !%+ \(x1, x2) => (x1 * x2 ** \x' => (x' * x2, x' * x1))

||| Mean squared error
public export
SquaredDifference : {a : Type} -> Num a => Neg a => (Const a >< Const a) =%> (Const a)
SquaredDifference = ((id {c=Const a}) >< Negate) %>> Sum %>> Copy %>> Mul

namespace Monadic
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
    (shapes : All (.Shp) cs) -> (i : Fin k) -> Any (.Shp) cs
  selectShape (s :: ss) FZ = Here s
  selectShape (s :: ss) (FS j) = There (selectShape ss j)

  ||| Extract the position from an AnyPos at a given index
  public export
  extractPos : {n : Nat} -> {xs : Vect n AddCont} -> {shapes : All (.Shp) xs} ->
    (i : Fin n) ->
    AnyShpPos (selectShape shapes i) ->
    (index i xs).Pos (index i shapes)
  extractPos {shapes = (_ :: _)} FZ (Here x') = x'
  extractPos {shapes = (_ :: _)} (FS j) (There rest) = extractPos j rest

  -- public export
  -- SampleAndChooseWithDist : {n : Nat} -> {xs : Vect n AddCont} ->
  --   ConvexComb xs =%> (Simplex n >< (Sample n >@ Any xs))
  -- SampleAndChooseWithDist = ?SampleAndChooseWithDist_rhs


  {-
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
    pure (selectShape shapes i ** \x' => (0, [(i ** extractPos i x')]))

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
  -

-- parameters (f : Type -> Type)
--   ||| These are all of the morphisms in the cokleisli category of (f <!> -)  
--   public export
--   MonLens : Cont -> Cont -> Type
--   MonLens c d = (f <!> c) =%> d
-- 
--   public export
--   counit : Monad f => f <!> c =%> c
--   counit = !% \x => (x ** pure)
-- 
--   public export
--   cojoin : Monad f => (f <!> c) =%> (f <!> (f <!> c))
--   cojoin = !% \x => (x ** join)

  
public export
record FCoAlgCont (f : Type -> Type) where
  constructor MkFCoAlgCont
  carrier : Cont
  coalg : (a : carrier.Shp) -> f (carrier.Pos a) -> carrier.Pos a

public export
coAlgMorphism : (c, d : FCoAlgCont f) -> Type
coAlgMorphism c d = c.carrier =%> d.carrier

convert : FCoAlgCont List -> AddCont
convert (MkFCoAlgCont carrier coalg) = MkAddCont
  carrier
  {mon=(MkI @{\s => MkComMonoid
    (\l, r => coalg s [l, r])
    (coalg s [])})}