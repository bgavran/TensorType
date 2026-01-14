module Data.Num

||| Interface for the Exponential
||| We also include minus infinity because of the necessity to compute
||| causal masks within the attention mechanism.
||| For rules that `exp` should satisfy, see https://arxiv.org/abs/1911.04790
||| We also have
||| `exp . log = id`, `log . exp = id`, `exp minusInfinity = 0`...
public export
interface Num a => Exp a where
  exp : a -> a
  log : a -> a
  minusInfinity : a

public export
Exp Double where
  exp = Prelude.exp
  log = Prelude.log
  minusInfinity = cast "-inf.0"

public export
interface Sqrt a where
  sqrt : a -> a

public export
Sqrt Double where
  sqrt = Prelude.sqrt
