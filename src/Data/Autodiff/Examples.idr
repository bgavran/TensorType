module Data.Autodiff.Examples

import Data.Autodiff.Core

public export
State : (x : a) -> Unit -> a
State x _ = x

public export
MulC : Num a => (a, a) -> a
MulC = uncurry (*)

public export
MulByK : Num a => a -> a -> a
MulByK k = \x => k * x

public export
AddC : Num a => (a, a) -> a
AddC = uncurry (+)

public export
ZeroC : Num a => Unit -> a
ZeroC = State 0

public export
Del : a -> Unit
Del _ = ()

public export
Copy : a -> (a, a)
Copy x = (x, x)

public export
DotTensor : {n: Nat} ->
  (Tensor [n] Double, Tensor [n] Double) -> Tensor [] Double
DotTensor (t1, t2) = dot t1 t2

-- Example differentiable function
public export
stateDifferentiable : {a : Type} -> D a => (x : a) -> BwDifferentiable (State x)
stateDifferentiable x = MkBwDiff (\_, _ => ())

public export
addDifferentiable : BwDifferentiable AddC
addDifferentiable = MkBwDiff (\_, db => (db, db))

public export
delDifferentiable : {a : Type} -> Num a => BwDifferentiable (Del {a})
delDifferentiable = MkBwDiff (\_, _ => 0)

%hint
public export
copyDifferentiable : {a : Type} -> Num a => BwDifferentiable (Copy {a})
copyDifferentiable = MkBwDiff (\_, (da1, da2) => da1 + da2)

%hint
public export
mulDifferentiable : BwDifferentiable MulC
mulDifferentiable = MkBwDiff $ \(a1, a2), db => (db * a2, db * a1)

%hint
public export
mulByKDifferentiable : {a : Type} -> Num a => (k : a) ->
  BwDifferentiable (MulByK {a} k)
mulByKDifferentiable k = MkBwDiff $ \x, db => db * k

-- public export
-- testCompose : BwDifferentiable (MulC . Copy {a=Double})
-- testCompose = MkBwDiff (let t = composeBwDifferentiable Copy MulC in ?hhhh) -- (let t = composeBwDifferentiable Copy MulC in ?ff)


public export
dotDifferentiable : {n : Nat} -> BwDifferentiable (DotTensor {n})
dotDifferentiable = MkBwDiff (\(t1, t2), dt =>
  ((\x => x * extract dt) <$> t2, (\x => x * extract dt) <$> t1))

public export
record Optimiser (pType : Type) {auto dp : D pType} where
  constructor MkOptimiser
  Opt : Const pType pType =%> ((p : pType) !> (T dp p))


||| If we want to write this for an arbitrary `D pType` we'd need the sharp
||| machinery from Diegetic open games
||| @lr is the learning rate, should be negative here since we are adding it
public export
sgd : Num pType => (lr : pType) -> Optimiser pType
sgd lr = MkOptimiser $ !% \p => (p ** \p' => p + lr * p')

public export
minimiseFnStep : (f : Double -> Double) ->
  (df : BwDifferentiable f) =>
  (startingValue : Double) ->
  Double -- result
minimiseFnStep f {df} startingValue =
  let fLens = (ULens df)
      opt = Opt (sgd {pType=Double} (-0.001))
  in (opt %>> fLens).bwd startingValue 1.0

public export
minimiseFn : (f : Double -> Double) ->
  (df : BwDifferentiable f) =>
  (startingValue : Double) ->
  (numSteps : Nat) ->
  IO ()
minimiseFn f {df} currentValue 0 = do
  putStrLn "Last step, current value: \{show currentValue}"
  putStrLn "Finished."
minimiseFn f {df} currentValue (S k) = do
  putStrLn "Step \{show (S k)}, current value: \{show currentValue}"
  let updatedValue = minimiseFnStep f {df} currentValue
  minimiseFn f {df} updatedValue k


public export
minimiseMulByK : (k : Double) ->
  (startingValue : Double) ->
  (numSteps : Nat) ->
  IO ()
minimiseMulByK k startingValue numSteps =
  minimiseFn (MulByK k) {df=mulByKDifferentiable k} startingValue numSteps







-- -- Example differentiable function
-- public export
-- mulDifferentiable : FwDifferentiable MulC
-- mulDifferentiable = MkFwDiff (\(a1, a2), (da, db) => a2 * da + a1 * db)
-- 
-- public export
-- addDifferentiable : FwDifferentiable AddC
-- addDifferentiable = MkFwDiff (\(a1, a2), (da, db) => da + db)
-- 
-- public export
-- zeroDifferentiable : FwDifferentiable ZeroC
-- zeroDifferentiable = MkFwDiff (\_, _ => 0)
-- 
-- public export
-- delDifferentiable : {a : Type} -> Num a => FwDifferentiable (Del {a})
-- delDifferentiable = MkFwDiff (\_, _ => ())
-- 
-- public export
-- copyDifferentiable : {a : Type} -> Num a => FwDifferentiable (Copy {a})
-- copyDifferentiable = MkFwDiff (\_, da => (da, da))
-- 
-- public export
-- dotDifferentiable : {n : Nat} -> FwDifferentiable (DotTensor {n})
-- dotDifferentiable = MkFwDiff (\(t1, t2), (dt1, dt2) => dot t2 dt1 + dot t1 dt2)

