module Data.Bag

import Misc

||| Bag ~ Multiset, a set where each element can appear multiple times
||| Equivalently, a list without order
||| Representing the bag as a list quotiented out by permutations, though
||| permutations are not enforced. This record is only used for type clarity
public export
record Bag (a : Type) where
  constructor MkBag
  bag : List a

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
  multiplicities = multiplicities . bag


export infixr 7 ++

public export
(++) : Bag a -> Bag a -> Bag a
(MkBag xs) ++ (MkBag ys) = MkBag (xs ++ ys)

public export
Foldable Bag where
  foldr f z (MkBag xs) = foldr f z xs


-- The input always comes with the data of a position, by virtue of needing to be stored on the disk?