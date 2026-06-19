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
import Data.Container.Additive.Properties.Definitions

import Data.Container.Additive.Quantifiers

import Control.Monad.Distribution
import Control.Monad.Sample.Definition

import Misc

%hide Base.Object.Instances.Const
%hide Data.Vect.Quantifiers.All.index
%hide Base.Morphism.Definition.DependentLenses.(=%>)
%hide Base.Morphism.Instances.State.State
%hide Base.Morphism.Instances.Costate.Costate
%hide Base.Product.Definitions.HancockTensorProduct.(><)

namespace State
  ||| "State" as defined in https://arxiv.org/abs/2403.13001 and open games 
  |||
  |||       ┌─────────────┐
  |||       │             ├──► (x : c.Shp)
  |||       │    State    │
  |||       │             ├◄── c.Pos x
  |||       └─────────────┘
  public export
  State : AddCont -> Type
  State c = Scalar =%> c

  public export
  toState : (x : c.Shp) -> State c
  toState x = !% toState x
  
  public export
  fromState : State c -> c.Shp
  fromState f = f.fwd ()

namespace Costate
  ||| "Costate" as defined in https://arxiv.org/abs/2403.13001 and open games 
  |||
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             │
  |||                  │   Costate   │
  |||     c.Pos x   ◄──┤             │
  |||                  └─────────────┘
  public export
  Costate : AddCont -> Type
  Costate c = c =%> Scalar
  
  public export
  toCostate : ((x : c.Shp) -> c.Pos x) -> Costate c
  toCostate s = !% toCostate s
  
  public export
  fromCostate : Costate c -> (x : c.Shp) -> c.Pos x
  fromCostate f x = f.bwd x ()

  public export
  constantOne : InterfaceOnPositions c Num => Costate c
  constantOne @{MkI p} = toCostate (\x => let numPos = p x in 1)

  public export
  Delete : {c : AddCont} -> Costate c 
  Delete = toCostate c.Zero
  

||| If we model the idea of a container (S !> P) as a box
|||  ┌──────┐
|||  │ s:S  │
|||  ├──────┤
|||  │  Ps  │
|||  └──────┘
||| then `pushDown` is interpreted as pushing down the container,
||| pruning anything that goes out of the box, and using `Unit` for
||| anything new that appears:
|||  ┌──────┐
|||  │ Unit │
|||  ├──────┤
|||  │ s:S  │
|||  └──────┘
|||     Ps
||| For additive containers we need to take the free monoid
public export
pushDown : AddCont -> AddCont
pushDown c = !! pushDown (UC c)

public export
pushIntoContinuationList : {p : AddCont} -> {0 d, l : AddCont} ->
  d >< p =%> l ->
  p =%> (pushDown d) >@ (List l)
pushIntoContinuationList f = !%+ \param => (() <|
  \ds => ds <&> (\dShp => f.fwd (dShp, param)) **
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
pushIntoContinuation : {p : AddCont} -> (flat : IsFlat l) => Num l.Shp =>
  (f : d >< p =%> l) ->
  (p =%> (pushDown d) >@ l)
pushIntoContinuation {flat = MkIsFlat _} f = !%+ \param => (() <|
  \ds => sum @{numIsMonoid} ((\dShp => f.fwd (dShp, param)) <$> ds) **
    \ll => sum @{UMon p param} (ll >>=
      \(ds ** grad) => (\dShp => snd (f.bwd (dShp, param) grad)) <$> ds))

||| This is also the categorical product since our containers are additive
namespace HancockTensorProduct
  public export
  leftUnit : Scalar >< c =%> c
  leftUnit = !% leftUnit
  
  public export
  rightUnit : c >< Scalar =%> c
  rightUnit = !% rightUnit

  public export
  leftUnitInv : c =%> Scalar >< c
  leftUnitInv = !% leftUnitInv
  
  public export
  rightUnitInv : c =%> c >< Scalar
  rightUnitInv = !% rightUnitInv

  public export
  assocL : (a >< b) >< c =%> a >< (b >< c)
  assocL = !% assocL

  public export
  assocR : a >< (b >< c) =%> (a >< b) >< c
  assocR = !% assocR

  public export
  swap : a >< b =%> b >< a
  swap = !% swap

  public export
  swapMiddle : (c1 >< c2) >< (c3 >< c4) =%> (c1 >< c3) >< (c2 >< c4)
  swapMiddle = !% swapMiddle

  ||| These do not exist for ordinary containers!
  ||| Here we need `c` not to be erased since we're using its monoid structure
  public export
  Copy : {c : AddCont} -> c =%> c >< c
  Copy = !%+ \x => ((x, x) ** uncurry (c.Plus x))
  
  public export
  PairMaps : {c : AddCont} ->
    c =%> d ->
    c =%> e ->
    c =%> d >< e
  PairMaps f g = Copy %>> (f >< g)
  
  public export
  ProjLeft : {d : AddCont} -> c >< d =%> c
  ProjLeft = !%+ \(x, y) => (x ** \x' => (x', d.Zero y))
  
  public export
  ProjRight : {c : AddCont} -> c >< d =%> d
  ProjRight = !%+ \(x, y) => (y ** \y' => (c.Zero x, y'))


namespace CompositionProduct
  public export
  leftUnit : Scalar >@ c =%> c
  leftUnit = !% pureBw %>> leftUnit

  public export
  rightUnit : c >@ Scalar =%> c
  rightUnit = !% pureBw %>> rightUnit

  public export
  leftUnitInv : {c : AddCont} -> c =%> Scalar >@ c
  leftUnitInv = !%+ \s => (() <| (\_ => s) ** \ll => 
    sum @{UMon c s} (snd <$> ll))
  -- leftUnitInv {c=MkAddCont uc} = (!% CompositionProduct.leftUnitInv) %>> ?eiei
  
  ||| Right unit inverse: c =%> c >@ I
  public export
  rightUnitInv : {c : AddCont} -> c =%> (c >@ Scalar)
  rightUnitInv = !%+ \s => (s <| const () ** \ll =>
    sum @{UMon c s} (fst <$> ll))


namespace Coproduct
  public export
  elim : c >+< c =%> c
  elim = !% elim

public export
duoidal : (c >@ d) >< (e >@ f) =%> (c >< e) >@ (d >< f)
duoidal = !%+ \((sc <| idxC), (se <| idxE)) =>
  ((sc, se) <| \(cp, ep) => (idxC cp, idxE ep) **
    \ll => ((\((cp, ep) ** (dp, fp)) => (cp ** dp)) <$> ll,
            (\((cp, ep) ** (dp, fp)) => (ep ** fp)) <$> ll))

public export
coprodDistrOverTensor : {q, p : AddCont} ->
  (a >+< b) >< (p >< q) =%> (a >< p) >+< (b >< q)
coprodDistrOverTensor = !%+ \case
  (Left a, (p, _)) => (Left (a, p) ** \(a', p') => (a', (p', q.Zero _)))
  (Right b, (_, q)) => (Right (b, q) ** \(b', q') => (b', (p.Zero _, q')))

||| Not an isomorphism, arising from duoidal structure between >@ and ><
public export
rebracketcomptensor: {y : AddCont} -> (e >@ y) >< y =%> e >@ (y >< y)
rebracketcomptensor = (id {c=e >@ y} >< leftUnitInv {c=y})
                      %>> duoidal {c=e} {d=y} {e=Scalar} {f=y}
                      %>> (rightUnit {c=e} >@ id {c=(y><y)})


public export
distribute : {c : AddCont} ->
  c >< e =%> s ->
  c >< (e >@ g) =%> s >@ g
distribute f = (rightUnitInv >< id {c=e >@ g})
             %>> duoidal {d = Scalar}
             %>> (f >@ leftUnit)

public export
extractEffect : {d : AddCont} ->
  d >< (e >@ f) =%> e >@ (d >< f)
extractEffect = (leftUnitInv >< (id {c=e >@ f}))
            %>> duoidal {c=Scalar}
            %>> (leftUnit >@ (id {c=d><f}))

  
public export
Sum : Num a =>
  (Const a >< Const a) =%> Const a
Sum = !%+ \(x1, x2) => (x1 + x2 ** \x' => (x', x'))

public export
bwSumList : {l : Type} -> ComMonoid l =>
  (xs : List l) ->
  (d' : l) ->
  All (const l) xs
bwSumList [] d' = []
bwSumList (x :: xs) d' = x :: bwSumList xs x


public export
SumList : {l : Type} -> ComMonoid l =>
  List (Const l) =%> Const l
SumList = !%+ \xs => (sum xs ** \d' => bwSumList xs d')

public export
Negate : Num a => Neg a =>
  Const a =%> Const a
Negate = !%+ \x => (-x ** \x' => -x')

public export
Zero : {c : AddCont} -> Num a =>
  c =%> Const a
Zero = !%+ \_ => (0 ** \_ => c.Zero _)

public export
Mul : Num a =>
  (Const a >< Const a) =%> Const a
Mul = !%+ \(x1, x2) => (x1 * x2 ** \x' => (x' * x2, x' * x1))

||| Mean squared error
public export
SquaredDifference : {a : Type} -> Num a => Neg a => (Const a >< Const a) =%> (Const a)
SquaredDifference = ((id {c=Const a}) >< Negate) %>> Sum %>> Copy %>> Mul

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

  
-- public export
-- record FCoAlgCont (f : Type -> Type) where
--   constructor MkFCoAlgCont
--   carrier : Cont
--   coalg : (a : carrier.Shp) -> f (carrier.Pos a) -> carrier.Pos a

-- public export
-- coAlgMorphism : (c, d : FCoAlgCont f) -> Type
-- coAlgMorphism c d = c.carrier =%> d.carrier
-- 
-- convert : FCoAlgCont List -> AddCont
-- convert (MkFCoAlgCont carrier coalg) = MkAddCont
--   carrier
--   {mon=(MkI $ \s => MkComMonoid
--     (\l, r => coalg s [l, r])
--     (coalg s []))}