module Data.Container.Additive.Morphism.Instances

import Data.Vect
import Data.List.Quantifiers
import Data.Vect.Quantifiers

import Data.Container.Base
import Data.Container.Base.Morphism.Instances as Base
import Data.ComMonoid
import Data.Num
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Object.Instances
import Data.Container.Additive.Extension.Definition
import Data.Container.Additive.Morphism.Definition
import Data.Container.Additive.Product.Definitions
import Data.Container.Additive.Properties.Definitions

import Data.Container.Additive.Quantifiers

import Control.Monad.Distribution
import Control.Monad.Sample.Definition

import Misc

%hide Base.Object.Instances.Const
%hide Data.Vect.Quantifiers.All.index
%hide Base.Morphism.Instances.State.State
%hide Base.Morphism.Instances.Costate.Costate


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
||| For additive containers we need to take the free commutative monoid
public export
pushDown : AddCont -> AddCont
pushDown c = !* pushDown (UC c)

public export
pushIntoContinuationBag : {p : AddCont} -> {0 d, l : AddCont} ->
  d >< p =%+> l ->
  p =%+> (pushDown d) >+@ (Bag l)
pushIntoContinuationBag f = !%+ \param => (() <|
  map (\dShp => f.fwd (dShp, param)) **
    \ll => sum @{UMon p param} $ ll >>=
      \(ds ** grads) => extractPGradsBag param ds grads)
  where
    extractPGrads : (param : p.Shp) ->
      (ds : List d.Shp) ->
      All l.Pos ((\dShp => f.fwd (dShp, param)) <$> ds) ->
      List (p.Pos param)
    extractPGrads param [] [] = []
    extractPGrads param (dShp :: ds) (grad :: grads) =
      snd (f.bwd (dShp, param) grad) :: extractPGrads param ds grads

    extractPGradsBag : (param : p.Shp) ->
      (ds : Bag d.Shp) ->
      All l.Pos ((\dShp => f.fwd (dShp, param)) <$> ds) ->
      Bag (p.Pos param)
    extractPGradsBag param (MkBag dsl) grads
      = MkBag $ extractPGrads param dsl grads


public export
pushIntoContinuation : {p : AddCont} -> (flat : IsFlat l) => Num l.Shp =>
  (f : d >< p =%+> l) ->
  (p =%+> (pushDown d) >+@ l)
pushIntoContinuation {flat = MkIsFlat lp} f = !%+ \param => (() <|
  \ds => sum @{numIsMonoid} ((\dShp => f.fwd (dShp, param)) <$> ds) **
    \bb => sum @{UMon p param} (bb >>=
      \(ds ** grad) => ds <&> (\dShp => snd (f.bwd (dShp, param) grad))))

||| This is also the categorical product since our containers are additive
namespace HancockTensorProduct
  public export
  leftUnit : Scalar >< c =%+> c
  leftUnit = !% leftUnit
  
  public export
  rightUnit : c >< Scalar =%+> c
  rightUnit = !% rightUnit

  public export
  leftUnitInv : c =%+> Scalar >< c
  leftUnitInv = !% leftUnitInv
  
  public export
  rightUnitInv : c =%+> c >< Scalar
  rightUnitInv = !% rightUnitInv

  public export
  assocL : (a >< b) >< c =%+> a >< (b >< c)
  assocL = !% assocL

  public export
  assocR : a >< (b >< c) =%+> (a >< b) >< c
  assocR = !% assocR

  public export
  swap : a >< b =%+> b >< a
  swap = !% swap

  public export
  swapMiddle : (c1 >< c2) >< (c3 >< c4) =%+> (c1 >< c3) >< (c2 >< c4)
  swapMiddle = !% swapMiddle

  ||| These do not exist for ordinary containers!
  ||| Here we need `c` not to be erased since we're using its monoid structure
  public export
  copy : {c : AddCont} -> c =%+> c >< c
  copy = !%+ \x => ((x, x) ** uncurry (c.Plus x))
  
  public export
  pairMaps : {c : AddCont} ->
    c =%+> d ->
    c =%+> e ->
    c =%+> d >< e
  pairMaps f g = copy %+>> (f >< g)
  
  public export
  projLeft : {d : AddCont} -> c >< d =%+> c
  projLeft = !%+ \(x, y) => (x ** \x' => (x', d.Zero y))
  
  public export
  projRight : {c : AddCont} -> c >< d =%+> d
  projRight = !%+ \(x, y) => (y ** \y' => (c.Zero x, y'))

namespace CompositionProduct
  public export
  leftUnit : Scalar >+@ c =%+> c
  leftUnit = !% pureBw %>> leftUnit

  public export
  rightUnit : c >+@ Scalar =%+> c
  rightUnit = !% pureBw %>> rightUnit

  ||| Left unit inverse: c =%+> Scalar >+@ c
  public export
  leftUnitInv : {c : AddCont} -> c =%+> Scalar >+@ c
  leftUnitInv = !% sumBw @{mon c} %>> (Bag <!> leftUnitInv)

  ||| Right unit inverse: c =%+> c >@ I
  public export
  rightUnitInv : {c : AddCont} -> c =%+> c >+@ Scalar
  rightUnitInv = !% sumBw @{mon c} %>> (Bag <!> rightUnitInv)

  public export
  assocL : (a >+@ b) >+@ c =%+> a >+@ (b >+@ c)
  assocL = !%+ \((aShp <| f) <| g) =>
    (aShp <| \aPos => f aPos <| \bPos => g (MkBag [(aPos ** bPos)]) **
      \ll => join $ ll <&> \(aPos ** lbc) =>
        lbc <&> \(bPos ** cPos) => (MkBag [(aPos ** bPos)] ** cPos))

  ||| Associator, "un-flatten" direction. NOT definable as a total lens in
  ||| general: the forward would have to produce the target's outer index
  ||| `g : List (aPos ** bPos) -> c.Shp`, i.e. collapse a whole list of
  ||| (a,b)-positions into a single c-shape. All we have is one c-shape per
  ||| element (`index (f aPos) bPos`), and c-shapes carry no monoid/default,
  ||| so the empty-list case has no answer. This is the precise sense in which
  ||| the free composition product is only laxly (one-directionally) associative.
  public export
  assocR : a >+@ (b >+@ c) =%+> (a >+@ b) >+@ c
  assocR = !%+ \(aShp <| f) => (((aShp <| shapeExt . f) <|
    \ll => let ff : (aPos : a.Pos aShp ** b.Pos (Ext.shapeExt $ f aPos)) -> c.Shp 
               ff (aPos ** bPos) = index (f aPos) bPos
           in ?llb) ** ?fififi)


namespace Coproduct
  public export
  elim : c >+< c =%+> c
  elim = !% elim

public export
duoidal : (c >+@ d) >< (e >+@ f) =%+> (c >< e) >+@ (d >< f)
duoidal = !%+ \((sc <| idxC), (se <| idxE)) =>
  ((sc, se) <| \(cp, ep) => (idxC cp, idxE ep) **
    \ll => ((\((cp, ep) ** (dp, fp)) => (cp ** dp)) <$> ll,
            (\((cp, ep) ** (dp, fp)) => (ep ** fp)) <$> ll))


public export
coprodDistrOverTensor : {q, p : AddCont} ->
  (a >+< b) >< (p >< q) =%+> (a >< p) >+< (b >< q)
coprodDistrOverTensor = !%+ \case
  (Left a, (p, _)) => (Left (a, p) ** \(a', p') => (a', (p', q.Zero _)))
  (Right b, (_, q)) => (Right (b, q) ** \(b', q') => (b', (p.Zero _, q')))

||| Not an isomorphism, arising from duoidal structure between >@ and ><
public export
rebracketcomptensor: {y : AddCont} -> (e >+@ y) >< y =%+> e >+@ (y >< y)
rebracketcomptensor = (id {c=e >+@ y} >< leftUnitInv {c=y})
                      %+>> duoidal {c=e} {d=y} {e=Scalar} {f=y}
                      %+>> (rightUnit {c=e} >+@ id {c=(y><y)})


public export
distribute : {c : AddCont} ->
  c >< e =%+> s ->
  c >< (e >+@ g) =%+> s >+@ g
distribute f = (rightUnitInv >< id {c=e >+@ g})
             %+>> duoidal {d = Scalar}
             %+>> (f >+@ leftUnit)

public export
extractEffect : {d : AddCont} ->
  d >< (e >+@ f) =%+> e >+@ (d >< f)
extractEffect = (leftUnitInv >< (id {c=e >+@ f}))
            %+>> duoidal {c=Scalar}
            %+>> (leftUnit >+@ (id {c=d><f}))


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
  State c = Scalar =%+> c

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
  Costate c = c =%+> Scalar
  
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
  

  
public export
sum : Num a =>
  (Const a >< Const a) =%+> Const a
sum = !%+ \(x1, x2) => (x1 + x2 ** \x' => (x', x'))

public export
bwSumList : {l : Type} -> ComMonoid l =>
  (xs : List l) ->
  (d' : l) ->
  All (const l) xs
bwSumList [] d' = []
bwSumList (x :: xs) d' = x :: bwSumList xs x

public export
bwSumBag : {l : Type} -> ComMonoid l =>
  (xs : Bag l) ->
  (d' : l) ->
  All (const l) xs
bwSumBag (MkBag xs) d' = bwSumList xs d'


public export
sumList : {l : Type} -> ComMonoid l =>
  Bag (Const l) =%+> Const l
sumList = !%+ \xs => (sum xs ** \d' => bwSumBag xs d')

public export
negate : Num a => Neg a =>
  Const a =%+> Const a
negate = !%+ \x => (-x ** \x' => -x')

public export
zero : {c : AddCont} -> Num a =>
  c =%+> Const a
zero = !%+ \_ => (0 ** \_ => c.Zero _)

public export
mul : Num a =>
  (Const a >< Const a) =%+> Const a
mul = !%+ \(x1, x2) => (x1 * x2 ** \x' => (x' * x2, x' * x1))

||| Mean squared error
public export
SquaredDifference : {a : Type} -> Num a => Neg a =>
  (Const a >< Const a) =%+> (Const a)
SquaredDifference = ((id {c=Const a}) >< negate) %+>> sum %+>> copy %+>> mul

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