module NN.Architectures.LossFunctions

import Data.List
import Data.Zippable

import Data.Tensor
import Data.Tensor.Utils
import Data.Container.Additive
import NN.Architectures.Softargmax
import Control.Monad.Distribution

import Data.Container.Additive.Quantifiers

import Data.Para

%hide Data.Container.Base.Morphism.Definition.DependentLenses.(=%>)

||| Loss function alias
public export
Loss : AddCont -> {default (Const Double) l : AddCont} -> Type
Loss c = (c >< c) =%> l

namespace Combinators
  ||| Combinator for pairing up loss functions
  public export
  pairLossFunctions : {y, z : AddCont} ->
    {l : Type} -> Num l =>
    Loss y {l=Const l} -> Loss z {l=Const l} -> Loss (y >< z) {l=Const l}
  pairLossFunctions loss1 loss2 = swapMiddle %>> (loss1 >< loss2) %>> Sum

  public export
  lossSame : {a, b : AddCont} ->
    ((a >+< b) >< (a >+< b)) =%> ((a >< a) >+< (b >< b))
  lossSame = !%+ \case
    (Left x1, Left x2) => (Left (x1, x2) ** id)
    (Right y1, Right y2) => (Right (y1, y2) ** id)
    (_, _) => believe_me "Should not happen"

  public export
  pairLossCoproduct : {y, z : AddCont} ->
    {l : Type} -> Num l =>
    Loss y {l=Const l} -> Loss z {l=Const l} -> Loss (y >+< z) {l=Const l}
  pairLossCoproduct l1 l2 = lossSame %>> (l1 >+< l2) %>> elim

  public export
  composeLossFunctions : {y, z, l : AddCont} ->
    Loss y {l} -> Loss z {l} -> Loss (y >@ z) {l}
  composeLossFunctions loss1 loss2 = let tt = loss1 >@ loss2
                                     in ?composeLossFunctions_rhs

  public export
  sequenceLossFunctions : {y, z : AddCont} ->
    Loss y {l} -> Loss z {l} -> Loss (y >@ z) {l}
  sequenceLossFunctions loss1 loss2 = !%+ \(x1, x2) => ?asdf

  public export
  zipListsBwd : {y : AddCont} ->
    (l1, l2 : List y.Shp) ->
    All (y >< y).Pos (zip l1 l2) -> (All y.Pos l1, All y.Pos l2)
  zipListsBwd [] l2 [] = ([], allIsComonoidNeutral l2)
  zipListsBwd (s1 :: ss1) [] [] = (allIsComonoidNeutral (s1 :: ss1), [])
  zipListsBwd (s1 :: ss1) (s2 :: ss2) ((p1, p2) :: rest) =
    let (ls, rs) = zipListsBwd ss1 ss2 rest
    in (p1 :: ls, p2 :: rs)

  public export
  zipLists : {y : AddCont} -> (List y) >< (List y) =%> List (y >< y)
  zipLists = !%+ \(l1, l2) => (zip l1 l2 ** zipListsBwd l1 l2)

  -- TODO here it can be that we pair different types together!
  -- so if there is a mismath we have the ability to short circuit?
  public export
  UniversalMapOutOfCoproduct : Num d =>
    {n : Nat} -> IsSucc n =>
    {cs : Vect n AddCont} ->
    ((i : Fin n) -> Loss (index i cs) {l=Const d}) ->
    Loss (Any cs) {l=Const d}
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
SquaredError : {a : Type} -> Num a => Neg a => Loss (Const a) {l=Const a}
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
  Loss (Const (Tensor [n] a)) {l=Const (Tensor [] a)}
MeanSquaredError = SquaredError %>> Sum %>> Div (cast n)

public export
SoftargmaxCrossEntropyLogits : {n : Nat} -> Loss (Simplex n)
SoftargmaxCrossEntropyLogits = !%+ \(logits, labels) =>
  let logSoftargmaxLogits = logSoftargmax (># (toVect logits))
      targetProbs = softargmaxImpl {i=Vect n} (># (toVect labels))
      out = - dot logSoftargmaxLogits targetProbs
  in (extract out ** \l' =>
    (#> (((l' *) <$> softargmaxImpl (># (toVect logits)) - targetProbs)),
      replicate n 0)) -- zeros for now
