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

||| Every `Num` type is a commutative monoid under addition.
||| Deliberately `export` and not `public export`, as it complicates search
||| It spawns a witness for every `Const a` with numeric `a`
%hint
export
numIsMonoid : Num a => ComMonoid a
numIsMonoid = MkComMonoid (+) 0

-- todo figure out a consistent strategy for when `%hint` is needed or not
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

namespace NotExposingType
  ||| Same as ComMonoid, but without exposing the underlying carrier in the type
  public export
  ComMonoid : Type
  ComMonoid = (t : Type ** ComMonoid t)

  ||| Forgetful functor
  public export
  uSet : ComMonoid -> Type
  uSet = fst

  ||| Not encoding the rules for now
  ||| Not using pattern matching so it reduces
  public export
  ComMonoidHomo : ComMonoid -> ComMonoid -> Type
  ComMonoidHomo m n = uSet m -> uSet n

  ||| Hom object of commutative monoids 
  ||| Notably, without commutativity this does not exist
  public export
  functionIsMonoid : {0 a : Type} -> ComMonoid b -> ComMonoid (a -> b)
  functionIsMonoid m = MkComMonoid
    (\f, g => \x => plus m (f x) (g x))
    (\_ => neutral m)

  ||| Natural numbers, the free commutative monoid on one generator.
  public export
  natMon : ComMonoid
  natMon = (Nat ** numIsMonoid)

  public export
  Free : Type -> ComMonoid
  Free a = (Bag a ** bagIsMonoid)

||| Hom-set isomorphism of the free-forgetful adjunction between ComMon and Set
||| A map on generators is extended to a homomorphism out of a free commtuative 
||| monoid on the generators
public export
fromGenerators : {0 a : Type} -> {y : ComMonoid} ->
  (a -> uSet y) -> -- a map on generators
  ComMonoidHomo (Free a) y
fromGenerators f b = sum @{snd y} (f <$> b)

||| Canonical action of `Nat` on a commutative monoid
||| `scale n x` is the `n`-fold sum `x + ... + x`
||| Special case of `fromGenerators` whe `a=Unit`.
public export
scale : ComMonoid a => Nat -> a -> a
scale @{mon} 0 a = neutral mon
scale @{mon} (S k) a = plus mon a (scale k a)

