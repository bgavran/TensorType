module Data.ComMonoid

%hide Prelude.Semigroup
%hide Prelude.Monoid

||| Commutative monoid
||| Not encoding the property of commutativity here
public export
record ComMonoid (a : Type) where
  constructor MkComMonoid
  plus : a -> a -> a
  neutral : a

%hint
public export
doubleIsMonoid : ComMonoid Double
doubleIsMonoid = MkComMonoid (+) 0

%hint
public export
unitIsMonoid : ComMonoid Unit
unitIsMonoid = MkComMonoid (\(), () => ()) ()

%hint
public export
numIsMonoid : Num a => ComMonoid a
numIsMonoid = MkComMonoid (+) 0

public export
listIsMonoid : ComMonoid (List a)
listIsMonoid = MkComMonoid (++) []


%hint
public export
pairIsMonoid : ComMonoid a => ComMonoid b => ComMonoid (a, b)
pairIsMonoid @{MkComMonoid plusA neutralA} @{MkComMonoid plusB neutralB}
  = MkComMonoid
    (\(a, b), (a', b') => (plusA a a', plusB b b'))
    (neutralA, neutralB)


public export
sum : ComMonoid a => List a -> a
sum @{mon} = foldr (plus mon) (neutral mon)


namespace NotExposingType
  ||| Same as ComMonoid, but without exposing the underlying carrier in the type
  public export
  ComMonoid : Type
  ComMonoid = (t : Type ** ComMonoid t)

  public export
  record ComMonoidHomo (c, d : ComMonoid) where
    constructor MkComMonoidHomo
    underlyingMap : c.fst -> d.fst
    plusPreserve : (x, y : c.fst) ->
      underlyingMap (c.snd.plus x y) = d.snd.plus (underlyingMap x) (underlyingMap y)
    neutralPreserve : underlyingMap c.snd.neutral = d.snd.neutral
