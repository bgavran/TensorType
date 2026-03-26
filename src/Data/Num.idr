module Data.Num

import Data.Vect

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
interface Num a => Sqrt a where
  sqrt : a -> a

public export
Sqrt Double where
  sqrt = Prelude.sqrt


namespace Num
  public export
  {n : Nat} -> Num a => Num (Vect n a) where
    xs + ys = zipWith (+) xs ys
    xs * ys = zipWith (*) xs ys
    fromInteger x = replicate n (fromInteger x)

  public export
  Num Unit where
    () + () = ()
    () * () = ()
    fromInteger x = ()
  
  public export
  Num a => Num b => Num (a, b) where
    (lFst, lSnd) * (rFst, rSnd) = (lFst * rFst, lSnd * rSnd)
    (+) (lFst, lSnd) (rFst, rSnd) = (lFst + rFst, lSnd + rSnd)
    fromInteger x = (fromInteger x, fromInteger x)

  public export
  Num a => Num b => Num (DPair a (const b)) where
    (lFst ** lSnd) * (rFst ** rSnd) = (lFst * rFst ** lSnd * rSnd)
    (+) (lFst ** lSnd) (rFst ** rSnd) = (lFst + rFst ** lSnd + rSnd)
    fromInteger x = (fromInteger x ** fromInteger x)

  %hint
  public export
  depFunNum : {k : Fin n -> Type} ->
    {ss : (i : Fin n) -> Num (k i)} ->
     Num ((i : Fin n) -> k i)
  depFunNum = MkNum
    (\s, t => \i => s i + t i)
    (\f, g => \i => f i * g i)
    (\n => \i => fromInteger n)



namespace Neg
  public export
  Neg Unit where
    negate () = ()
    () - () = ()

  public export
  Neg a => Neg b => Neg (a, b) where
    negate (lFst, lSnd) = (negate lFst, negate lSnd)
    (lFst, lSnd) - (rFst, rSnd) = (lFst - rFst, lSnd - rSnd)

  public export
  Neg a => Neg b => Neg (DPair a (const b)) where
    negate (fst ** snd) = (negate fst ** negate snd)
    (fst ** snd) - (rFst ** rSnd) = (fst - rFst ** snd - rSnd)

  %hint
  public export
  depFunNeg : {k : Fin n -> Type} ->
    {ss : (i : Fin n) -> Neg (k i)} ->
     Neg ((i : Fin n) -> k i)
  depFunNeg = MkNeg
    (\s => \i => negate (s i))
    (\f, g => \i => f i - g i)

namespace FromDouble
  public export
  FromDouble Unit where
    fromDouble x = ()

  public export
  FromDouble a => FromDouble b => FromDouble (a, b) where
    fromDouble x = (fromDouble x, fromDouble x)
  
  public export
  FromDouble a => FromDouble b => FromDouble (DPair a (const b)) where
    fromDouble x = (fromDouble x ** fromDouble x)

  %hint
  public export
  depFunFromDouble : {k : Fin n -> Type} ->
    {ss : (i : Fin n) -> FromDouble (k i)} ->
     FromDouble ((i : Fin n) -> k i)
  depFunFromDouble = MkFromDouble
    (\s => \i => fromDouble s)

namespace Fractional
  public export
  Fractional Unit where
    () / () = ()
    
  public export 
  Fractional a => Fractional b => Fractional (a, b) where
    (lFst, lSnd) / (rFst, rSnd) = (lFst / rFst, lSnd / rSnd)

  public export
  Fractional a => Fractional b => Fractional (DPair a (const b)) where
    (fst ** snd) / (rFst ** rSnd) = (fst / rFst ** snd / rSnd)

namespace Sqrt
  public export
  Sqrt Unit where
    sqrt () = ()

  public export
  Sqrt a => Sqrt b => Sqrt (a, b) where
    sqrt (lFst, lSnd) = (sqrt lFst, sqrt lSnd)

  public export
  Sqrt a => Sqrt b => Sqrt (DPair a (const b)) where
    sqrt (fst ** snd) = (sqrt fst ** sqrt snd)