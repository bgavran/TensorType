module Data.Bag

import Misc
import Data.List.Quantifiers

||| Bag ~ Multiset, a set where each element can appear multiple times
||| Free *commutative* monoid on a set
||| Equivalently, a list without order, i.e. quotiented out by permutations
||| Using the list representation here, without enforcing permutation quotient
public export
record Bag (a : Type) where
  constructor MkBag
  toList : List a

public export
Multiset : Type -> Type
Multiset = Bag

public export
multiplicities : Eq a => List a -> (a -> Nat)
multiplicities [] = const 0
multiplicities (x :: xs) = \y => applyWhen (x == y) (1 +) (multiplicities xs y)

namespace Bag 
  ||| A multiset is equivalently a function `a -> Nat` with finite support
  public export
  multiplicities : Eq a => Bag a -> (a -> Nat)
  multiplicities = multiplicities . toList


export infixr 7 ++

public export
(++) : Bag a -> Bag a -> Bag a
(MkBag xs) ++ (MkBag ys) = MkBag (xs ++ ys)

public export
Functor Bag where
  map f (MkBag xs) = MkBag (map f xs)

public export
Applicative Bag where
  pure a = MkBag (pure a)
  (MkBag fs) <*> (MkBag xs) = MkBag (fs <*> xs)

public export
Monad Bag where
  join (MkBag b) = MkBag $ join (toList <$> b)

public export
Foldable Bag where
  foldr f z (MkBag xs) = foldr f z xs


namespace Quantifiers
  public export
  All : (p : a -> Type) -> Bag a -> Type
  All p (MkBag xs) = All p xs

  public export
  Any : (p : a -> Type) -> Bag a -> Type
  Any p (MkBag xs) = Any p xs
    


-- The input always comes with the data of a position, by virtue of needing to be stored on the disk?