module Data.Autodiff.Model

import Data.Fin
import Data.Bag
import Data.ComMonoid
import Data.Container.Additive
import public Data.Para
import Data.Materialise
import System.Random

{-------------------------------------------------------------------------------
Towards a typed analogue of nn.Module
-------------------------------------------------------------------------------}

-- todo need to rethink tihs syntax
export infixr 1 >>> -- sequential
export infixr 3 *** -- parallel
export infixr 3 &&& -- fan-out

||| A Model is a differentiable parametric map which
||| a) has its parameter container constant
||| b) comes with its own initialisation
public export
record Model (a, b : AddCont) where
  constructor MkModel
  Params : Type
  {auto pMon : ComMonoid Params}
  init : IO Params
  run  : (a >*< Const Params @{pMon}) =%+> b

||| Infix notation for the Model
public export
(-\->) : AddCont -> AddCont -> Type
a -\-> b = Model a b

public export
ParamCont : Model a b -> AddCont
ParamCont m = Const m.Params @{m.pMon}

namespace ParaConversion
  public export
  toPara : {0 a, b : AddCont} -> a -\-> b -> ParaAddLens a b
  toPara m = MkPara (ParamCont m) m.run
  
  public export
  fromPara : {0 a, b : AddCont} -> (f : ParaAddLens a b) ->
    (isConst : IsConst (Param f)) =>
    (init : IO (Param f).Shp) ->
    a -\-> b
  fromPara (MkPara _ f) {isConst = MkIsConst p @{mon}} init = MkModel p init f


||| Replace a model's initialisation
public export
withInit : {0 a, b : AddCont} -> (m : a -\-> b) -> IO m.Params -> a -\-> b
withInit m i = MkModel m.Params @{m.pMon} i m.run

||| Default parameter initialisation, uniform on (-1, 1)
public export
DefaultInit : Random p => Neg p => IO p
DefaultInit = randomRIO (-1, 1)

||| A parameterless differentiable map
public export
trivialParam : {0 a, b : AddCont} -> a =%+> b -> a -\-> b
trivialParam f = MkModel Unit (pure ()) $
  !%+ \(x, ()) =>
    let (y ** k) = (%!+) f x
    in (y ** \y' => (k y', ()))

public export
id : {a : AddCont} -> a -\-> a
id = trivialParam id

||| Sequential composition
public export
(>>>) : {0 a, b, c : AddCont} ->
  Materialise b.Shp => InterfaceOnPositions b Materialise =>
  a -\-> b ->
  b -\-> c ->
  a -\-> c
(MkModel p ip f) >>> (MkModel q iq g) = MkModel (p, q) [| (ip, iq) |] $
  (id >*< constPair)
    %+>> assocR {b=Const p, c=Const q}
    %+>> ((f %+>> materialiseCont) >*< id {c=Const q})
    %+>> g

||| Parallel composition
public export
(***) : {a, b, c, d : AddCont} ->
  a -\-> c ->
  b -\-> d ->
  a >*< b -\-> c >*< d
(MkModel p ip f) *** (MkModel q iq g) = MkModel (p, q) [| (ip, iq) |] $
  (id {c=a>*<b} >*< constPair)
    %+>> swapMiddle {c3=Const p} {c4=Const q}
    %+>> (f >*< g)

||| Fan-out
public export
(&&&) : {a : AddCont} -> {0 b, c : AddCont} ->
  a -\-> b ->
  a -\-> c ->
  a -\-> b >*< c
(MkModel p ip f) &&& (MkModel q iq g) = MkModel (p, q) [| (ip, iq) |] $
  (id >*< constPair)
    %+>> (copy >*< id {c=Const p >*< Const q})
    %+>> swapMiddle {c3=Const p} {c4=Const q}
    %+>> (f >*< g)

||| Fan-out of models
public export
dfunFinite : {a : AddCont} -> {n : Nat} -> {0 f : Fin n -> AddCont} ->
  ((i : Fin n) -> a -\-> f i) -> a -\-> AddContDFunFinite f
dfunFinite {n = 0} _ = trivialParam terminal
dfunFinite {n = S k} ms = ms 0 &&& dfunFinite {f = f . FS} (\i => ms (FS i))

||| Only evaluates the head if the index matches it
public export
lazyCons : {a : AddCont} ->
  {0 b : AddCont} -> {0 k : Nat} -> {0 bs : Vect k AddCont} ->
  a -\-> b -> a -\-> (Vect k >-+@ Coproduct bs) ->
  a -\-> (Vect (S k) >-+@ Coproduct (b :: bs))
lazyCons (MkModel p @{pm} ip f) (MkModel q @{qm} iq g) = MkModel
  (p, q) [| (ip, iq) |] $
  !%+ \(x, (px, qx)) =>
    let hd : Lazy (t : b.Shp ** b.PosSet t -> (a >*< Const p).PosSet (x, px))
        hd = (%!+) f (x, px)
        rest = (%!+) g (x, qx)
    in (() <| (\case
            FZ => (FZ ** fst hd)
            FS j => (FS (fst (index (fst rest) j)) ** snd (index (fst rest) j)))
        ** fromGenerators {y = (a >*< Const (p, q)).Pos (x, (px, qx))}
             (\(i ** gr) => case i of
                FZ => let (x', p') = snd hd gr
                      in (x', (p', (Const q).Zero qx))
                FS j => let (x', q') = snd rest (MkBag [(j ** gr)])
                        in (x', ((Const p @{pm}).Zero px, q'))))

||| Branch models under the choice effect: only the branch the environment asks
||| for runs. The type of `postcomposeLens (dfunFinite ms) graph`, without its work
public export
lazyBranches : {a : AddCont} -> {n : Nat} -> {0 branches : Vect n AddCont} ->
  ((i : Fin n) -> a -\-> index i branches) ->
  a -\-> (Vect n >-+@ Coproduct branches)
lazyBranches {n = 0} {branches = []} _ = trivialParam $
  !%+ \x => (() <| (\i => absurd i) ** fromGenerators (\(i ** _) => absurd i))
lazyBranches {n = S k} {branches = b :: bs} ms
  = lazyCons (ms 0) (lazyBranches (\i => ms (FS i)))

||| Act on the first component
public export
mapFst : {a, c : AddCont} ->
  a -\-> b ->
  a >*< c -\-> b >*< c
mapFst m = MkModel m.Params @{m.pMon} m.init $
  assocL {c=ParamCont m}
    %+>> (id >*< swap {a=c} {b=ParamCont m})
    %+>> assocR {a} {b=ParamCont m}
    %+>> (m.run >*< id)

||| Iterate a model `n` times
public export
nTimes : {a : AddCont} ->
  Materialise a.Shp =>
  InterfaceOnPositions a Materialise => 
  Nat -> a -\-> a -> a -\-> a
nTimes 0 m = id
nTimes 1 m = m
nTimes (S k) m = m >>> nTimes k m

public export
postcomposeLens : {0 a, b, c : AddCont} -> a -\-> b -> b =%+> c -> a -\-> c
postcomposeLens m g = MkModel m.Params @{m.pMon} m.init (m.run %+>> g)

||| Pre-compose a parameterless lens onto a model's input
public export
precomposeLens : {0 a, b, c : AddCont} -> a =%+> b -> b -\-> c -> a -\-> c
precomposeLens g m
  = MkModel m.Params @{m.pMon} m.init ((g >*< id {c = ParamCont m}) %+>> m.run)

||| A custom function without parameters
public export
prim : {0 a : AddCont} -> {b : AddCont} ->
  ((x : a.Shp) -> (y : b.Shp ** (b.PosSet y -> a.PosSet x))) ->
  a -\-> b
prim f = trivialParam (!%+ f)

||| A custom differentiable operation
public export
customOp : {s, t : Type} -> ComMonoid s => ComMonoid t =>
  (fwd : s -> t) -> (vjp : s -> t -> s) ->
  Const s -\-> Const t
customOp fwd vjp = prim (\x => (fwd x ** vjp x))

||| A custom parametric layer
public export
layer : {0 a : AddCont} -> {b : AddCont} ->
  (p : Type) -> ComMonoid p =>
  (initP : IO p) ->
  ((x : a.Shp) -> (param : p) -> (y : b.Shp ** (b.PosSet y -> (a.PosSet x, p)))) ->
  a -\-> b
layer p initP f = MkModel p initP $
  !%+ \(x, ps) => f x ps

||| Run a model at an input and a parameter
public export
runAt : {0 a, b : AddCont} -> (m : a -\-> b) ->
  (x : a.Shp) -> (p : m.Params) ->
  (y : b.Shp ** (b.PosSet y -> (a.PosSet x, m.Params)))
runAt m x p = (%!+) m.run (x, p)

||| Forward pass
public export
(.fwd) : {0 a, b : AddCont} -> (m : a -\-> b) ->
  (x : a.Shp) -> (p : m.Params) -> b.Shp
(.fwd) m x p = fst (runAt m x p)

||| Backward pass
public export
(.bwd) : {0 a, b : AddCont} -> (m : a -\-> b) ->
  (x : a.Shp) -> (p : m.Params) ->
  b.PosSet (m.fwd x p) -> (a.PosSet x, m.Params)
(.bwd) m x p = snd (runAt m x p)