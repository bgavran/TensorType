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


import Misc

%hide Base.Object.Instances.Const
%hide Data.Vect.Quantifiers.All.index
%hide Base.Morphism.Instances.State.State
%hide Base.Morphism.Instances.Costate.Costate

-- Not sure if we'll need these?
-- public export
-- pushIntoContinuationBag : {p : AddCont} -> {0 d, l : AddCont} ->
--   d >< p =%+> l ->
--   p =%+> (pushDown d) >+@ (Bag l)
-- pushIntoContinuationBag f = !%+ \param => (() <|
--   map (\dShp => f.fwd (dShp, param)) **
--     \ll => sum @{UMon p param} $ ll >>=
--       \(ds ** grads) => extractPGradsBag param ds grads)
--   where
--     extractPGrads : (param : p.Shp) ->
--       (ds : List d.Shp) ->
--       All l.Pos ((\dShp => f.fwd (dShp, param)) <$> ds) ->
--       List (p.Pos param)
--     extractPGrads param [] [] = []
--     extractPGrads param (dShp :: ds) (grad :: grads) =
--       snd (f.bwd (dShp, param) grad) :: extractPGrads param ds grads
-- 
--     extractPGradsBag : (param : p.Shp) ->
--       (ds : Bag d.Shp) ->
--       All l.Pos ((\dShp => f.fwd (dShp, param)) <$> ds) ->
--       Bag (p.Pos param)
--     extractPGradsBag param (MkBag dsl) grads
--       = MkBag $ extractPGrads param dsl grads
-- 
-- 

public export
pushIntoContinuation : {p : AddCont} ->
  (f : d >*< p =%+> l) ->
  (p =%+> (pushDown d.Shp) >-+@ l)
pushIntoContinuation f = !%+ \param => (() <| \dShp => f.fwd (dShp, param) **
    fromGenerators @{UMon p param}
      (\(dShp ** grad) => snd (f.bwd (dShp, param) grad)))

||| Categorical product of additive containers
||| On underlying containers computed as the hancock tensor product
namespace CategoricalProduct
  public export
  leftUnit : UnitCont >*< c =%+> c
  leftUnit = !% leftUnit
  
  public export
  rightUnit : c >*< UnitCont =%+> c
  rightUnit = !% rightUnit

  public export
  leftUnitInv : c =%+> UnitCont >*< c
  leftUnitInv = !% leftUnitInv
  
  public export
  rightUnitInv : c =%+> c >*< UnitCont
  rightUnitInv = !% rightUnitInv

  public export
  assocL : (a >*< b) >*< c =%+> a >*< (b >*< c)
  assocL = !% assocL

  public export
  assocR : a >*< (b >*< c) =%+> (a >*< b) >*< c
  assocR = !% assocR

  public export
  swap : a >*< b =%+> b >*< a
  swap = !% swap

  public export
  swapMiddle : (c1 >*< c2) >*< (c3 >*< c4) =%+> (c1 >*< c3) >*< (c2 >*< c4)
  swapMiddle = !% swapMiddle

  ||| These do not exist for ordinary containers!
  ||| Here we need `c` not to be erased since we're using its monoid structure
  public export
  copy : {c : AddCont} -> c =%+> c >*< c
  copy = !%+ \x => ((x, x) ** uncurry (c.Plus x))
  
  public export
  pairMaps : {c : AddCont} ->
    c =%+> d ->
    c =%+> e ->
    c =%+> d >*< e
  pairMaps f g = copy %+>> (f >*< g)
  
  public export
  projLeft : {d : AddCont} -> c >*< d =%+> c
  projLeft = !%+ \(x, y) => (x ** \x' => (x', d.Zero y))
  
  public export
  projRight : {c : AddCont} -> c >*< d =%+> d
  projRight = !%+ \(x, y) => (y ** \y' => (c.Zero x, y'))

||| Structure maps of the left action `>-+@` of `(Cont, >@, Scalar)` on AddCont
||| They generally use the following components:
||| * `pureBw` : a position becomes the singleton bag containing it
||| * `sumBw` : a bag of positions is added up using their monoid structure
||| * `joinBwComp` : nested bags of positions are flattened
namespace CompositionProductAction
  ||| Backwards pass is ComMon-homomorphism on the nose
  public export
  unitor : {c : AddCont} -> c =%+> Scalar >-+@ c
  unitor = !% (sumBw @{mon c} %>> (Bag <!> leftUnitInv))

  ||| Backwards map is a ComMon-homomorphism only through the quotient
  public export
  unitorInv : Scalar >-+@ c =%+> c
  unitorInv = !% ((Bag <!> leftUnit) %>> pureBw)

  public export
  multiplicator : (m >-+@ (n >-+@ c)) =%+> ((m >@ n) >-+@ c)
  multiplicator = !% (Bag <!> ((id >@ pureBw {c = n >@ UC c}) %>> assocR))

  public export
  multiplicatorInv : ((m >@ n) >-+@ c) =%+> (m >-+@ (n >-+@ c))
  multiplicatorInv = !% ((Bag <!> assocL) %>> joinBwComp {d = n >@ UC c})

||| `!*` and `- >-+@ Scalar` are isomorphic: they're both right adjoint to 
||| `UC`.  They are two presentations of the same free commutative monoid on
||| positions: `!*` stores a bag of positions directly, while `- >-+@ Scalar` 
||| stores generators tagged with `Nat` multiplicities.
namespace CompositionActionBang
  ||| Read each position as the generator it is, with multiplicity one
  public export
  actionToFree : {0 e : Cont} -> e >-+@ Scalar =%+> !* e
  actionToFree = !%+ \ex => (shapeExt ex ** map (\mp => (mp ** 1)))

  ||| Expand each generator into as many copies as its multiplicity says
  public export
  freeToAction : {0 e : Cont} -> !* e =%+> e >-+@ Scalar
  freeToAction = !%+ \x => (x <| \_ => () ** fromGenerators @{bagIsMonoid}
    (\(mp ** n) => scale @{bagIsMonoid} n (pure mp)))

||| Structure maps of the left-skew monoidal product `>+@` on AddCont
||| These definitions follow Theorem 3.1 in https://arxiv.org/abs/2506.06847
namespace SkewCompositionProduct
  ||| Hom-set isomorphism of the adjunction, which is the general purpose
  ||| `addContTranspose` read through the isomorphism above
  public export
  adjR : {c : AddCont} -> UC c =%> m -> c =%+> m >-+@ Scalar
  adjR f = addContTranspose f %+>> freeToAction

  ||| Inverse of the hom-set isomorphism of the adjunction
  public export
  adjL : c =%+> m >-+@ Scalar -> UC c =%> m
  adjL g = addContTransposeInv (g %+>> actionToFree)

  public export
  epsilon : UC Scalar =%> Scalar
  epsilon = adjL (unitor {c = Scalar})

  public export
  leftUnit : {c : AddCont} -> Scalar >+@ c =%+> c
  leftUnit = (epsilon >-+@ id) %+>> unitorInv

  public export
  rightUnit : {c : AddCont} -> c =%+> c >+@ Scalar
  rightUnit = adjR id

  public export
  associator : {b : AddCont} -> (a >+@ b) >+@ c =%+> a >+@ (b >+@ c)
  associator = (adjL ((id >-+@ SkewCompositionProduct.rightUnit {c = b})
    %+>> multiplicator {c = Scalar}) >-+@ id) %+>> multiplicatorInv 

  {-
  Beyond skew structure, only `leftUnitInv` exists, rightUnitInv and assocR do not.

  leftUnitInv is also not inverse to leftUnit. We only have
  `leftUnitInv %+>> leftUnit = id`, but not the other way around.

  The right associator is not definable because the forward  part involves the
  the function `g : List (aPos ** bPos) -> c.Shp` which would have to collapse
  a whole list of of positions into a single shape
  -}
  public export
  leftUnitInv : {c : AddCont} -> c =%+> Scalar >+@ c
  leftUnitInv = unitor %+>> (toState () >-+@ id)


namespace Coproduct
  public export
  elim : c >+< c =%+> c
  elim = !% elim

||| Lax interchange between the categorical product `>*<` on AddCont and the
||| action `>-+@` of `(Cont, ><)` on it. Not an isomorphism.
public export
duoidal : (m >-+@ d) >*< (n >-+@ g) =%+> (m >< n) >-+@ (d >*< g)
duoidal = !%+ \(exM, exN) =>
  ((shapeExt exM, shapeExt exN) <| \(mp, np) => (index exM mp, index exN np) **
    \bag => ((\((mp, np) ** (dp, gp)) => (mp ** dp)) <$> bag,
             (\((mp, np) ** (dp, gp)) => (np ** gp)) <$> bag))

||| Specific distributive law we need
public export
distribute : {c : AddCont} ->
  (f : c.Shp -> (e =%> s)) ->
  c >*< (e >-+@ g) =%+> s >-+@ g
distribute f = uncurry (!%+ \cs => (f cs >-+@ id {c=g} ** \_ => c.Zero cs))

public export
coprodDistrOverTensor : {q, p : AddCont} ->
  (a >+< b) >*< (p >*< q) =%+> (a >*< p) >+< (b >*< q)
coprodDistrOverTensor = !%+ \case
  (Left a, (p, _)) => (Left (a, p) ** \(a', p') => (a', (p', q.Zero _)))
  (Right b, (_, q)) => (Right (b, q) ** \(b', q') => (b', (p.Zero _, q')))

{-
||| Not an isomorphism, arising from duoidal structure between >@ and ><
public export
rebracketcomptensor: {y : AddCont} -> (e >+@ y) >< y =%+> e >+@ (y >< y)
rebracketcomptensor = (id {c=e >+@ y} >< leftUnitInv {c=y})
                      %+>> duoidal {c=e} {d=y} {e=Scalar} {f=y}
                      %+>> (rightUnit {c=e} >+@ id {c=(y><y)})


public export
extractEffect : {d : AddCont} ->
  d >< (e >+@ f) =%+> e >+@ (d >< f)
extractEffect = (leftUnitInv >< (id {c=e >+@ f}))
            %+>> duoidal {c=Scalar}
            %+>> (leftUnit >+@ (id {c=d><f}))

-}

||| References for State
||| Bruno's PhD thesis: https://arxiv.org/abs/2403.13001
||| Towards Foundations of Cat. Cybernetics: https://arxiv.org/abs/2105.06332
namespace State
  ||| State here differers for the one in `Cont`, because `Scalar` is different
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
  toState x = ?somethingInterestingHmm
  
  -- public export
  -- fromState : State c -> c.Shp
  -- fromState f = f.fwd ()

||| References for Costate
||| Bruno's PhD thesis: https://arxiv.org/abs/2403.13001
||| Towards Foundations of Cat. Cybernetics: https://arxiv.org/abs/2105.06332
namespace Costate
  ||| Costate here differs from the one in `Cont`, because `Scalar` is different
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             │
  |||                  │   Costate   │
  |||     c.Pos x   ◄──┤             │
  |||                  └─────────────┘
  public export
  Costate : AddCont -> Type
  Costate c = c =%+> Scalar
  
  public export
  toCostate : {c : AddCont} ->
    ((x : c.Shp) -> c.Pos x) -> Costate c
  toCostate s = !%+ \x => (() ** \n => scale @{UMon c x} n (s x))

  -- public export
  -- fromCostate : Costate c -> (x : c.Shp) -> c.Pos x
  -- fromCostate f x = f.bwd x ()

  public export
  constantOne : {c : AddCont} ->
    InterfaceOnPositions c Num => Costate c
  constantOne @{MkI p} = toCostate (\x => let numPos = p x in 1)

  public export
  Delete : {c : AddCont} -> Costate c 
  Delete = toCostate c.Zero
  

public export
sum : Num a =>
  (Const a >*< Const a) =%+> Const a
sum = !%+ \(x1, x2) => (x1 + x2 ** \x' => (x', x'))

public export
bwSumBag : {l : Type} ->
  (xs : List l) ->
  (d' : l) ->
  All (const l) xs
bwSumBag [] d' = []
bwSumBag (x :: xs) d' = d' :: bwSumBag xs d'

public export
sumBag : {l : Type} -> ComMonoid l =>
  BagAll (Const l) =%+> Const l
sumBag = !%+ \(MkBag xs) => (sum (MkBag xs) ** \d' => bwSumBag xs d')

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
  (Const a >*< Const a) =%+> Const a
mul = !%+ \(x1, x2) => (x1 * x2 ** \x' => (x' * x2, x' * x1))

||| Mean squared error
public export
SquaredDifference : {a : Type} -> Num a => Neg a =>
  (Const a >*< Const a) =%+> (Const a)
SquaredDifference = ((id {c=Const a}) >*< negate) %+>> sum %+>> copy %+>> mul

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