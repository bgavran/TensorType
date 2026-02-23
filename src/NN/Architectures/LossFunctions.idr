module NN.Architectures.LossFunctions

import Data.Tensor
import Data.Tensor.Utils
import Data.Container.Additive
import NN.Architectures.Softargmax
import Control.Monad.Distribution

import Data.Para

%hide Data.Container.Base.Morphism.Definition.DependentLenses.(=%>)

||| Loss function alias
public export
Loss : AddCont -> {default Double l : Type} -> Num l => Type
Loss c = (c >< c) =%> (Const l)

namespace Combinators
  ||| Combinator for pairing up loss functions
  public export
  pairLossFunctions : {y, z : AddCont} ->
    {l : Type} -> Num l =>
    Loss y {l} -> Loss z {l} -> Loss (y >< z) {l}
  pairLossFunctions loss1 loss2 = swapMiddle %>> (loss1 >< loss2) %>> Sum

  public export
  sequenceLossFunctions : {y, z : AddCont} ->
    {l : Type} -> Num l =>
    Loss y {l} -> Loss z {l} -> Loss (y >@ z) {l}
  sequenceLossFunctions loss1 loss2 = !%+ \(x1, x2) => ?asdf

  -- TODO here it can be that we pair different types together!
  -- so if there is a mismath we have the ability to short circuit?
  public export
  UniversalMapOutOfCoproduct : Num d =>
    {n : Nat} -> IsSucc n =>
    {cs : Vect n AddCont} ->
    ((i : Fin n) -> Loss (index i cs) {l=d}) ->
    Loss (Any cs) {l=d}
  UniversalMapOutOfCoproduct {n = 1} {cs = [c]} s = !%+ \(Here l, Here r) =>
    ((s 0).fwd (l, r) ** \d' =>
    let (l', r') = (s 0).bwd (l, r) d'
    in (Here l', Here r'))
  UniversalMapOutOfCoproduct {n = (S (S k))} {cs = (c :: cs)} s
    = !%+ \case 
      (Here l, Here r) => ((s 0).fwd (l, r) ** \d' =>
        let (l', r') = (s 0).bwd (l, r) d'
        in (Here l', Here r'))
      (There l, (There r)) =>
         let restLens = UniversalMapOutOfCoproduct {cs=cs} (\i => s (FS i))
             d = restLens.fwd (l, r)
         in (d ** \d' => let (l', r') = restLens.bwd (l, r) d'
                         in (There l', There r'))
      -- if branches mismatch we shouldn't be asked this question
      -- using zeros for now
      (Here l, (There r)) => (0  ** \_ =>
        (Here (c.Zero l), There ((Any cs).Zero r)))
      (There l, (Here r)) => (0 ** \_ =>
        (There ((Any cs).Zero l), (Here (c.Zero r))))

||| Squared error
public export
SquaredError : {a : Type} -> Num a => Neg a => Loss (Const a) {l=a}
SquaredError = Additive.Morphism.Instances.SquaredDifference

public export
Sum : {n : Nat} -> Num a =>
  (Const (Tensor [n] a)) =%> (Const (Tensor [] a))
Sum = !%+ \t => (># reduce t ** \a' => fill (#> a'))

public export
Div : {a : Type} -> Num a => Fractional a =>
  (divBy : a) ->
  (Const (Tensor [] a)) =%> (Const (Tensor [] a))
Div divBy = !%+ \x => (x <&> (/ divBy) ** \x' => x' <&> (/ divBy))

public export
MeanSquaredError : {a : Type} -> Num a => Neg a => Fractional a =>
  Cast Nat a => {n : Nat} ->
  Loss (Const (Tensor [n] a)) {l=Tensor [] a}
MeanSquaredError = SquaredError %>> Sum %>> Div (cast n)

public export
SoftargmaxCrossEntropyLogits : {n : Nat} -> Loss (Simplex n) {l=Double}
SoftargmaxCrossEntropyLogits = !%+ \(logits, labels) =>
  let logSoftargmaxLogits = logSoftargmax (># (toVect logits))
      targetProbs = softargmaxImpl {i=Vect n} (># (toVect labels))
      out = - dot logSoftargmaxLogits targetProbs
  in (extract out ** \l' =>
    (#> (((l' *) <$> softargmaxImpl (># (toVect logits)) - targetProbs)),
      replicate n 0)) -- zeros for now
