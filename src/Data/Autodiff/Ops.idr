module Data.Autodiff.Ops

import Data.Tensor
import Data.Container.Additive
import Data.Para
import Control.Monad.Distribution
import Control.Monad.Identity
import Data.ComMonoid

import Misc

%hide Data.Container.Base.Morphism.Definition.DependentLenses.(=%>)
%hide Syntax.WithProof.prefix.(@@)

-- This is here and not in Container.Additive because it uses `Tensor` 
public export
Simplex : Nat -> AddCont
Simplex n = MkAddCont $ (_ : Dist n) !> (Tensor [n] Double)

public export
MulParametric : {a : Type} -> Num a => ParaAddDLens (Const a) (Const a)
MulParametric = binaryOpToPara {p=Const a} Mul

public export
AddParametric : {a : Type} -> Num a => ParaAddDLens (Const a) (Const a)
AddParametric = binaryOpToPara {p=Const a} Sum

public export
AffineParametric : {a : Type} -> Num a => ParaAddDLens (Const a) (Const a)
AffineParametric = composePara MulParametric AddParametric

public export
LeakyReLU : {a : Type} -> Num a => Ord a => FromDouble a =>
  {default 0.01 alpha : a} ->
  ParaAddDLens (Const a) (Const a)
LeakyReLU = trivialParam (!%+ \x =>
  (if x > 0 then x else alpha * x ** \x' => if x > 0 then x' else alpha))

public export
LeakyReLUTensor : {a : Type} -> {n : Nat} -> Num a => Ord a => FromDouble a =>
  {default 0.01 alpha : a} ->
  ParaAddDLens (Const (Tensor [n] a)) (Const (Tensor [n] a))
LeakyReLUTensor = trivialParam (!%+ \x =>
  (x <&> (\xx => if xx > 0 then xx else alpha * xx) ** \dy =>
    (\(d, xx) => if xx > 0 then d else alpha * d) <$> liftA2Tensor dy x))

public export
parallelTensor2 : {a, b: Type} -> Num a => Num b =>
  ParaAddDLens (Const a) (Const b) ->
  ParaAddDLens (Const (Tensor [2] a)) (Const (Tensor [2] b))
parallelTensor2 (MkPara pCont f) = MkPara
  (pCont >< pCont)
  (!%+ \(x, (p, q)) =>
    let (b1 ** kf) = (%!) f (x @@ [0], p)
        (b2 ** kg) = (%!) f (x @@ [1], q)
    in (># [b1, b2] ** \bs' =>
      let (x1', p') = kf (bs' @@ [0])
          (x2', q') = kg (bs' @@ [1])
      in (># [x1', x2'], (p', q'))))

public export
parallelTensor3 : {a, b : Type} -> Num a => Num b =>
  ParaAddDLens (Const a) (Const b) ->
  ParaAddDLens (Const (Tensor [3] a)) (Const (Tensor [3] b))
parallelTensor3 (MkPara pCont f) = MkPara
  (pCont >< pCont >< pCont)
  (!%+ \(x, (p, q, r)) =>
    let (b1 ** kf) = (%!) f (x @@ [0], p)
        (b2 ** kg) = (%!) f (x @@ [1], q)
        (b3 ** kh) = (%!) f (x @@ [2], r)
    in (># [b1, b2, b3] ** \bs' =>
      let (x1', p') = kf (bs' @@ [0])
          (x2', q') = kg (bs' @@ [1])
          (x3', r') = kh (bs' @@ [2])
      in (># [x1', x2', x3'], (p', (q', r')))))

||| Produces a parametric map that produces `n` copies of the output, instead
||| of one, by using `n` different parameters
public export
sameFromTensor2 : {a, b : Type} -> Num a => Num b => 
  ParaAddDLens (Const a) (Const b) ->
  ParaAddDLens (Const (Tensor [1] a)) (Const (Tensor [2] b))
sameFromTensor2 (MkPara pCont f) = MkPara
  (pCont >< pCont)
  (!%+ \(x, (p, q)) =>
    let val = x @@ [0]
        (b1 ** kf) = (%!) f (val, p)
        (b2 ** kg) = (%!) f (val, q)
    in (># [b1, b2] ** \bs' =>
      let (x1', p') = kf (bs' @@ [0])
          (x2', q') = kg (bs' @@ [1])
      in (># [x1' + x2'], (p', q'))))

public export
sameFromTensor3 : {a, b : Type} -> Num a => Num b => 
  ParaAddDLens (Const a) (Const b) ->
  ParaAddDLens (Const (Tensor [1] a)) (Const (Tensor [3] b))
sameFromTensor3 (MkPara pCont f) = MkPara
  (pCont >< pCont >< pCont)
  (!%+ \(x, (p, q, r)) =>
    let val = x @@ [0]
        (b1 ** kf) = (%!) f (val, p)
        (b2 ** kg) = (%!) f (val, q)
        (b3 ** kh) = (%!) f (val, r)
    in (># [b1, b2, b3] ** \bs' =>
      let (x1', p') = kf (bs' @@ [0])
          (x2', q') = kg (bs' @@ [1])
          (x3', r') = kh (bs' @@ [2])
      in (># [x1' + x2' + x3'], (p', q', r'))))

||| Produces a parametric map that produces `n` copies of the output, instead
||| of one, by using `n` different parameters
public export
sameFromTensor : {a, b : Type} -> Num a => Num b => {n : Nat} -> 
  ParaAddDLens (Const a) (Const b) ->
  ParaAddDLens (Const (Tensor [1] a)) (Const (Tensor [n] b))
sameFromTensor (MkPara pCont f) = MkPara
  (AllAll $ replicate n pCont)
  (!%+ \(x, psShapes) =>
    let val = x @@ [0]
        outAndBw = runIdentity $ dTraverse
            (\p => Id $ (%!) f (val, p))
            (allToVect psShapes)
        out = mapPropertyRelevant (\_, (y ** bw) => y) outAndBw
        bw = mapPropertyRelevant (\_, (y ** bw) => bw) outAndBw
    in (># constantToVect out ** \bs' =>
      let tt = bw 
      in ?bww))

public export
sameFrom : {a : AddCont} -> ParaAddDLens a b ->
  ParaAddDLens a c ->
  ParaAddDLens a (b >< c)
sameFrom (MkPara p f) (MkPara q g) = MkPara
  (p >< q)
  (!%+ \(x, (p, q)) =>
    let (b ** kf) = (%!) f (x, p)
        (c ** kg) = (%!) g (x, q)
    in ((b, c) ** \(b', c') =>
      let (x'1, p') = kf b'
          (x'2, q') = kg c'
      in (a.Plus x x'1 x'2, (p', q'))))

public export
sameFromConst : {a, b, c : Type} -> Num a => Num b => Num c =>
  ParaAddDLens (Const a) (Const b) ->
  ParaAddDLens (Const a) (Const c) ->
  ParaAddDLens (Const a) (Const (b, c))
sameFromConst (MkPara p f) (MkPara q g) = MkPara
  (p >< q)
  (!%+ \(x, (p, q)) =>
    let (b ** kf) = (%!) f (x, p)
        (c ** kg) = (%!) g (x, q)
    in ((b, c) ** \(b', c') =>
      let (x'1, p') = kf b'
          (x'2, q') = kg c'
      in (x'1 + x'2, (p', q'))))

public export
sameFrom3 : {a : AddCont} -> ParaAddDLens a b ->
  ParaAddDLens a c ->
  ParaAddDLens a d ->
  ParaAddDLens a (b >< c >< d)
sameFrom3 (MkPara p f) (MkPara q g) (MkPara r h) = MkPara
  (p >< q >< r)
  (!%+ \(x, (p, q, r)) =>
    let (b ** kf) = (%!) f (x, p)
        (c ** kg) = (%!) g (x, q)
        (d ** kh) = (%!) h (x, r)
    in ((b, c, d) ** \(b', c', d') =>
      let (x'1, p') = kf b'
          (x'2, q') = kg c'
          (x'3, r') = kh d'
      in (a.Plus x (a.Plus x x'1 x'2) x'3, (p', q', r'))))

public export
sameFromConst3 : {a, b, c, d : Type} -> Num a => Num b => Num c => Num d =>
  ParaAddDLens (Const a) (Const b) ->
  ParaAddDLens (Const a) (Const c) ->
  ParaAddDLens (Const a) (Const d) ->
  ParaAddDLens (Const a) (Const (b, c, d))
sameFromConst3 (MkPara p f) (MkPara q g) (MkPara r h) = MkPara
  (p >< q >< r)
  (!%+ \(x, (p, q, r)) =>
    let (b ** kf) = (%!) f (x, p)
        (c ** kg) = (%!) g (x, q)
        (d ** kh) = (%!) h (x, r)
    in ((b, c, d) ** \(b', c', d') =>
      let (x'1, p') = kf b'
          (x'2, q') = kg c'
          (x'3, r') = kh d'
      in (x'1 + x'2 + x'3, (p', q', r'))))

-- ||| N-ary probability intro and elimination
-- NProbIntro : {ef : EffectType} ->
--   {i : Nat} -> IsSucc i =>
--   {ts : Vect i Ty} ->
--   All (\t => Term ef ctx t) ts ->  -- for now all the components need to run with the same effect
--   -- Treating probability as logits
--   Vect i (Term ef ctx Number) ->
--   Term Prob ctx (NProb ts)
-- NProbElim : {ef : EffectType} ->
--   {i : Nat} -> IsSucc i =>
--   {ts : Vect i Ty} ->
--   Term ef ctx (NProb ts) ->
--   All (\e => Term ef (e :: ctx) c) ts -> Term Prob ctx c