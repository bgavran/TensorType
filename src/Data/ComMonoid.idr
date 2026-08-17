module Data.ComMonoid

import public Data.Num
import public Data.Bag

%hide Prelude.Semigroup
%hide Prelude.Monoid

||| Commutative monoid
||| Not encoding monoid laws, nor commutativity here
public export
record ComMonoid (a : Type) where
  constructor MkComMonoid
  plus : a -> a -> a
  neutral : a

%hint
public export
numIsMonoid : Num a => ComMonoid a
numIsMonoid = MkComMonoid (+) 0

public export
listIsMonoid : ComMonoid (List a)
listIsMonoid = MkComMonoid (++) []

public export
bagIsMonoid : ComMonoid (Bag a)
bagIsMonoid = MkComMonoid (++) (MkBag [])

%hint
public export
pairIsMonoid : ComMonoid a => ComMonoid b => ComMonoid (a, b)
pairIsMonoid @{MkComMonoid plusA neutralA} @{MkComMonoid plusB neutralB}
  = MkComMonoid
    (\(a, b), (a', b') => (plusA a a', plusB b b'))
    (neutralA, neutralB)

public export
sum : ComMonoid a => Bag a -> a
sum @{mon} = foldr (plus mon) (neutral mon)

-- public export
-- ComMonoidHomo : {a, b : Type} -> ComMonoid a -> ComMonoid b -> Type
-- ComMonoidHomo _ _ = a -> b


namespace NotExposingType
  ||| Same as ComMonoid, but without exposing the underlying carrier in the type
  public export
  ComMonoid : Type
  ComMonoid = (t : Type ** ComMonoid t)

  public export
  uSet : ComMonoid -> Type
  uSet = fst

  ||| Not encoding the rules for now
  public export
  ComMonoidHomo : ComMonoid -> ComMonoid -> Type
  ComMonoidHomo (t ** _) (t' ** _) = t -> t'

  -- public export
  -- record ComMonoidHomo (c, d : ComMonoid) where
  --   constructor MkComMonoidHomo
  --   underlyingMap : c.fst -> d.fst
  --   plusPreserve : (x, y : c.fst) ->
  --     underlyingMap (c.snd.plus x y) = d.snd.plus (underlyingMap x) (underlyingMap y)
  --   neutralPreserve : underlyingMap c.snd.neutral = d.snd.neutral

||| One way of the hom-set isomorphism of the free-forgetful adjunction. It 
||| extends a map on generators to a homomorphism out of the free commutative
||| monoid on those generators.
public export
fromGenerators : {0 a : Type} -> (mon : ComMonoid y) => (a -> y) ->
  ComMonoidHomo (Bag a ** bagIsMonoid {a}) (y ** mon)
fromGenerators h = sum . map h

||| Canonical action of `Nat` on a commutative monoid
||| `scale n x` is the `n`-fold sum `x + ... + x`
||| The one-generator case of `fromGenerators`, with `Nat \cong Bag Unit`
public export
scale : ComMonoid a => Nat -> a -> a
scale @{mon} 0 a = neutral mon
scale @{mon} (S k) a = plus mon a (scale k a)

