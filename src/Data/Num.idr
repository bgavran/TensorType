module Data.Num

public export
Num a => Num b => Num (a, b) where
  (lFst, lSnd) * (rFst, rSnd) = (lFst * rFst, lSnd * rSnd)
  (+) (lFst, lSnd) (rFst, rSnd) = (lFst + rFst, lSnd + rSnd)
  fromInteger x = (fromInteger x, fromInteger x)

public export
Neg a => Neg b => Neg (a, b) where
  negate (lFst, lSnd) = (negate lFst, negate lSnd)
  (lFst, lSnd) - (rFst, rSnd) = (lFst - rFst, lSnd - rSnd)

public export
FromDouble a => FromDouble b => FromDouble (a, b) where
  fromDouble x = (fromDouble x, fromDouble x)

public export
Num a => Num b => Num (DPair a (const b)) where
  (lFst ** lSnd) * (rFst ** rSnd) = (lFst * rFst ** lSnd * rSnd)
  (+) (lFst ** lSnd) (rFst ** rSnd) = (lFst + rFst ** lSnd + rSnd)
  fromInteger x = (fromInteger x ** fromInteger x)

public export
Neg a => Neg b => Neg (DPair a (const b)) where
  negate (fst ** snd) = (negate fst ** negate snd)
  (fst ** snd) - (rFst ** rSnd) = (fst - rFst ** snd - rSnd)

public export
FromDouble a => FromDouble b => FromDouble (DPair a (const b)) where
  fromDouble x = (fromDouble x ** fromDouble x)
  

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
