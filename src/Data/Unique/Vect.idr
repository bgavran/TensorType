module Data.Unique.Vect

import Data.Vect
import Data.List
import Data.List.Quantifiers
import Decidable.Equality
import Decidable.Equality.Core
import public Data.List.Elem
import Misc

||| A vector with unique elements
||| Requires a mutual block since it is defined in terms of NotElem
namespace UniqueVect
  mutual
    ||| A list with unique elements, length tracked statically
    ||| An element can be inserted if it is not already in the list
    ||| Like a Set, but with ordering
    ||| @ a The type of the elements in the list
    public export
    data UniqueVect : (0 n : Nat) -> (0 a : Type) -> DecEq a => Type where
      Nil : {0 a : Type} -> DecEq a => UniqueVect 0 a
      (::) : {0 a : Type} -> DecEq a =>
        (x : a) ->
        (xs : UniqueVect n a) ->
        {auto prf : NotElem x xs} ->
        UniqueVect (S n) a
  
    ||| A proof that an element is *not* found in the unique vector
    public export
    data NotElem : DecEq a =>
      (x : a) -> (xs : UniqueVect n a) -> Type where
      NotInEmptyVect : {0 a : Type} -> DecEq a => (x : a)
        -> NotElem {a=a} x []
      NotInNonEmptyVect : {0 a : Type} -> (de : DecEq a) =>
        {x, y : a} ->
        (xs : UniqueVect n a) ->
        (ne : NotElem x xs) ->
        {auto neq : IsNo (decEq x y)} ->
        {auto prf : NotElem y xs} ->
        NotElem x (y :: xs)


    public export
    toVect : DecEq a => UniqueVect n a -> Vect n a
    toVect [] = []
    toVect (x :: xs) = x :: toVect xs

    ||| A proof that an element is found in a vector with unique elements
    public export
    data Elem : DecEq a => (x : a) -> (xs : UniqueVect n a) -> Type where
      Here : DecEq a =>
        {x : a} ->
        {xs : UniqueVect k a} ->
        (prf : NotElem x xs) =>
        Elem x (x :: xs)
      There : DecEq a => {x : a} ->
        {xs : UniqueVect k a} ->
        (prf : NotElem y xs) =>
        (later : Elem x xs) ->
        Elem x (y :: xs)


    public export
    index : DecEq a => {x : a} -> {xs : UniqueVect n a} ->
      Elem x xs -> Fin n
    index Here = FZ
    index (There later) = FS (index later)

    mutual
      ||| Remove element from a unique vector at a given index
      public export
      removeIndex : DecEq a =>
        {n : Nat} ->
        (xs : UniqueVect (S n) a) ->
        Fin (S n) ->
        UniqueVect n a
      removeIndex (x :: xs) FZ = xs
      removeIndex {n = (S k)} (x :: xs) (FS i)
        = (::) x (removeIndex xs i) {prf=removingElemIsStillNotElem}

      ||| Given a vector `xs` and a proof that `x` is not in `xs`, then even if
      ||| we remove any elemens from `xs`, `x` will still not be in the result
      public export
      removingElemIsStillNotElem : DecEq a =>
        {n : Nat} ->
        {x : a} ->
        {xs : UniqueVect (S n) a} ->
        {i : Fin (S n)} ->
        (ne : NotElem x xs) =>
        NotElem x (removeIndex xs i)
      removingElemIsStillNotElem {xs = (_ :: _)} {ne = (NotInNonEmptyVect _ ne)} {i = FZ}
        = ne
      removingElemIsStillNotElem {n = (S k)} {xs = (y :: ys)} {ne = (NotInNonEmptyVect ys ne)} {i = (FS j)}
        = NotInNonEmptyVect (removeIndex ys j) removingElemIsStillNotElem {prf=removingElemIsStillNotElem} 




    -- fromVect : DecEq a => Vect n a -> UniqueVect n a
    -- fromVect [] = []
    -- fromVect (x :: xs) = case fromVect xs of
    --   Yes _ => x :: fromVect xs
    --   No _ => fromVect xs