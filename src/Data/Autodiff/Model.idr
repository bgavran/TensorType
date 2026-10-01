module Data.Autodiff.Model

import Data.Fin
import Data.Bag
import Data.ComMonoid
import Data.Container.Additive
import public Data.Para
import Data.Materialise
import public System.Random

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


||| Initialise every model of a family, into the tuple of their parameters
public export
initAll : {n : Nat} -> {0 a : AddCont} -> {0 f : Fin n -> AddCont} ->
  (ms : (i : Fin n) -> a -\-> f i) ->
  IO (Product (\i => ParamCont (ms i))).Shp
initAll {n = 0} _ = pure ()
initAll {n = S k} ms = [| ((ms 0).init, initAll (\i => ms (FS i))) |]

||| A family of models into the section of their codomains: the n-ary lazy
||| fan-out, a read running only the asked branch, with every branch's
||| parameters as one tuple
public export
fanOutModel : {a : AddCont} -> {n : Nat} -> {0 f : Fin n -> AddCont} ->
  (ms : (i : Fin n) -> a -\-> f i) -> a -\-> Section f
fanOutModel ms = MkModel
  (Product (\i => ParamCont (ms i))).Shp
  @{finiteShpMon {f = \i => ParamCont (ms i)} (\i => (ms i).pMon)}
  (initAll ms)
  ((id >*< constFinite {ps = \i => (ms i).Params} (\i => (ms i).pMon))
    %+>> fanOut (\i => (id >*< projFinite {f = \i => ParamCont (ms i)} i) %+>> (ms i).run))

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