module Data.Autodiff.Ops

import Data.Tensor
import Data.Container.Additive
import Data.Container.Additive.Quantifiers
import Data.Para
import Control.Monad.Distribution
import Data.ComMonoid

import Misc

%hide Data.Container.Base.Morphism.Definition.DependentLenses.(=%>)
%hide Syntax.WithProof.prefix.(@@)

{-------------------------------------------------------------------------------
This file containers the derivatives of various useful building blocks

Eventually will be combined with functionality which functorially assigns these
to any forward pass

-------------------------------------------------------------------------------}

public export
MulParametric : {a : Type} -> Num a => Const a =\\=> Const a
MulParametric = binaryOpToPara {p=Const a} mul

public export
AddParametric : {a : Type} -> Num a => Const a =\\=> Const a
AddParametric = binaryOpToPara {p=Const a} sum

public export
AffineParametric : {a : Type} -> Num a => Const a =\\=> Const a
AffineParametric = composePara MulParametric AddParametric



||| Recovers `ReLU` when `alpha=0`
||| Cannot be written as a composition of scaling and `ReLU`
public export
LeakyReLU : {a : Type} -> Num a => Ord a => FromDouble a =>
  {default 0.01 alpha : a} ->
  Const a =\\=> Const a
LeakyReLU = trivialParam (!%+ \x =>
  (if x > 0 then x else alpha * x ** \x' => if x > 0 then x' else alpha))

public export
ReLU : {a : Type} -> Num a => Ord a => FromDouble a =>
  Const a =\\=> Const a
ReLU = LeakyReLU {alpha=0}

||| Applies a parametric map entrywise to a vector of size `n`, using `n` 
||| copies of its parameter.
||| Really, an instance of `n-fold` product of parametric maps
||| Todo write parallel and n-fold composition for general Para
public export
parallelTensorN : {a, b : Type} -> Num a => Num b =>
  {shape : TensorShape rank} ->
  AllC TensorMonoid shape =>
  (f : Const a =\\=> Const b) ->
  (isConst : IsConst (GetParam f)) =>
  Const (Tensor shape a) =\\=> Const (Tensor shape b)
parallelTensorN (MkPara _ f) {isConst = MkIsConst q @{mon}} = MkPara
  (Const (Tensor shape q) @{tensorComMonoid mon})
  (!%+ \(x, ps) =>
    let outs : Tensor shape (y : b ** b -> (a, q))
        outs = [| (x, ps) |] <&> (%!+) f
    in (fst <$> outs ** \ys' =>
      let grads : Tensor shape (a, q)
          grads = [| snd outs ys' |]
      in (fst <$> grads, snd <$> grads)))

public export
LeakyReLUTensor : {a : Type} -> Num a => Ord a => FromDouble a =>
  {default 0.01 alpha : a} ->
  {n : Axis} -> TensorMonoid n.cont =>
  Const (Tensor [n] a) =\\=> Const (Tensor [n] a)
LeakyReLUTensor = parallelTensorN (LeakyReLU {alpha})

||| Can this also be written in more generality?
public export
coproductPair : {a, b, c, d : AddCont} ->
  a =\\=> c ->
  b =\\=> d ->
  a >+< b =\\=> c >+< d
coproductPair (MkPara p f) (MkPara q g) = MkPara
  (p >*< q)
  (coprodDistrOverTensor %+>> (f >+< g))

||| Produces a parametric map that produces `n` copies of the output, instead
||| of one, by using `n` different parameters. On the backward pass the `n`
||| gradients of the input are summed up.
||| Just like `parallelTensorN`, the parameter has to be constant so that its
||| `n` copies can be stored as a tensor.
public export
sameFromTensorN : {a, b : Type} -> Num a => Num b => {n : Nat} ->
  {axisName1, axisName2 : AxisName} ->
  (f : Const a =\\=> Const b) ->
  (isConst : IsConst (GetParam f)) =>
  Const (Tensor [axisName1 ~~> 1] a) =\\=> Const (Tensor [axisName2 ~~> n] b)
sameFromTensorN (MkPara _ f) {isConst = MkIsConst q @{mon}} = MkPara
  (Const (Tensor [axisName2 ~~> n] q) @{tensorComMonoid mon})
  (!%+ \(x, ps) =>
    let x0 = x @@ [0]
        outs = ps <&> \p => (%!+) f (x0, p)
    in (fst <$> outs ** \ys' =>
      let grads : Tensor [axisName2 ~~> n] (a, q)
          grads = [| snd outs ys' |]
      in (pure (reduce (fst <$> grads)), snd <$> grads)))

public export
sameFrom : {a : AddCont} -> ParaAddLens a b ->
  a =\\=> c ->
  a =\\=> b >*< c
sameFrom (MkPara p f) (MkPara q g) = MkPara
  (p >*< q)
  (!%+ \(x, (p, q)) =>
    let (b ** kf) = (%!+) f (x, p)
        (c ** kg) = (%!+) g (x, q)
    in ((b, c) ** \(b', c') =>
      let (x'1, p') = kf b'
          (x'2, q') = kg c'
      in (a.Plus x x'1 x'2, (p', q'))))

public export
sameFromConst : {a, b, c : Type} -> Num a => Num b => Num c =>
  Const a =\\=> Const b ->
  Const a =\\=> Const c ->
  Const a =\\=> Const (b, c)
sameFromConst (MkPara p f) (MkPara q g) = MkPara
  (p >*< q)
  (!%+ \(x, (p, q)) =>
    let (b ** kf) = (%!+) f (x, p)
        (c ** kg) = (%!+) g (x, q)
    in ((b, c) ** \(b', c') =>
      let (x'1, p') = kf b'
          (x'2, q') = kg c'
      in (x'1 + x'2, (p', q'))))

public export
sameFrom3 : {a : AddCont} -> ParaAddLens a b ->
  a =\\=> c ->
  a =\\=> d ->
  a =\\=> b >*< c >*< d
sameFrom3 (MkPara p f) (MkPara q g) (MkPara r h) = MkPara
  (p >*< q >*< r)
  (!%+ \(x, (p, q, r)) =>
    let (b ** kf) = (%!+) f (x, p)
        (c ** kg) = (%!+) g (x, q)
        (d ** kh) = (%!+) h (x, r)
    in ((b, c, d) ** \(b', c', d') =>
      let (x'1, p') = kf b'
          (x'2, q') = kg c'
          (x'3, r') = kh d'
      in (a.Plus x (a.Plus x x'1 x'2) x'3, (p', q', r'))))

public export
sameFromConst3 : {a, b, c, d : Type} -> Num a => Num b => Num c => Num d =>
  Const a =\\=> Const b ->
  Const a =\\=> Const c ->
  Const a =\\=> Const d ->
  Const a =\\=> Const (b, c, d)
sameFromConst3 (MkPara p f) (MkPara q g) (MkPara r h) = MkPara
  (p >*< q >*< r)
  (!%+ \(x, (p, q, r)) =>
    let (b ** kf) = (%!+) f (x, p)
        (c ** kg) = (%!+) g (x, q)
        (d ** kh) = (%!+) h (x, r)
    in ((b, c, d) ** \(b', c', d') =>
      let (x'1, p') = kf b'
          (x'2, q') = kg c'
          (x'3, r') = kh d'
      in (x'1 + x'2 + x'3, (p', q', r'))))


||| Interpret a vector as logits of a distribution. The backward pass is 
||| identity: gradients are computed in the sme way
public export
fromLogits : {0 name : AxisName} -> {0 n : Nat} ->
  Const (Tensor [name ~~> n] Double) =%+> Simplex name n
fromLogits = !%+ \xs => (MkDist xs ** id)


{-------------------------------------------------------------------------------
N-ary versions of `sameFrom`: instead of two or three parametric lenses out of
the same input, take an arbitrary number of them.

Because the parameter of each lens is existentially bundled inside
`ParaAddLens`, the parameter of the result is the n-ary product `AllAll` of the
individual parameters.
-------------------------------------------------------------------------------}

namespace NAry
  ||| The parameter containers of a vector of parametric lenses
  public export
  paramsOf : Vect n (ParaAddLens a b) -> Vect n AddCont
  paramsOf [] = []
  paramsOf (MkPara p _ :: fs) = p :: paramsOf fs

  ||| The parameter containers of a heterogeneous collection of parametric
  ||| lenses, all with the same domain
  public export
  paramsOfAll : {0 bs : Vect n AddCont} ->
    All (a =\\=> ) bs -> Vect n AddCont
  paramsOfAll [] = []
  paramsOfAll (MkPara p _ :: fs) = p :: paramsOfAll fs

  ||| Runs every lens of `fs` on the same input `x`, each with its own
  ||| parameter. On the backward pass the incoming gradients of `x` coming from
  ||| each branch are summed up, and the parameter gradients are kept separate.
  public export
  runSameFromAll : {a : AddCont} -> {0 bs : Vect n AddCont} ->
    (fs : All (a =\\=> ) bs) ->
    (x : a.Shp) -> (ps : All (.Shp) (paramsOfAll fs)) ->
    (ys : All (.Shp) bs ** AllPos ys -> (a.Pos x, AllPos ps))
  runSameFromAll [] x [] = ([] ** \[] => (a.Zero x, []))
  runSameFromAll (MkPara p f :: fs) x (s :: ss) =
    let (y ** kf) = (%!+) f (x, s)
        (ys ** kfs) = runSameFromAll fs x ss
    in (y :: ys ** \(y' :: ys') =>
      let (x'1, p') = kf y'
          (x'2, ps') = kfs ys'
      in (a.Plus x x'1 x'2, p' :: ps'))

  ||| Same as `runSameFromAll`, but with all the codomains fixed to `Const a`,
  ||| allowing us to collect the outputs into a `Vect n a`
  public export
  runSameFromConst : {a : Type} -> Num a =>
    (fs : Vect n (Const a =\\=> Const a)) ->
    (x : a) -> (ps : All (.Shp) (paramsOf fs)) ->
    (ys : Vect n a ** Vect n a -> (a, AllPos ps))
  runSameFromConst [] x [] = ([] ** \_ => (0, []))
  runSameFromConst (MkPara p f :: fs) x (s :: ss) =
    let (y ** kf) = (%!+) f (x, s)
        (ys ** kfs) = runSameFromConst fs x ss
    in (y :: ys ** \(y' :: ys') =>
      let (x'1, p') = kf y'
          (x'2, ps') = kfs ys'
      in (x'1 + x'2, p' :: ps'))

public export
sameFromAll : {a : AddCont} -> {n : Nat} -> {bs : Vect n AddCont} ->
  (fs : All (a =\\=>) bs) ->
  a =\\=> AllAll bs
sameFromAll fs = MkPara
  (AllAll (paramsOfAll fs))
  (!%+ \(x, ps) => runSameFromAll fs x ps)

public export
sameFromConstN : {a : Type} -> Num a => {n : Nat} ->
  (fs : Vect n (Const a =\\=> Const a)) ->
  Const a =\\=> Const (Vect n a)
sameFromConstN fs = MkPara
  (AllAll (paramsOf fs))
  (!%+ \(x, ps) => runSameFromConst fs x ps)