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
        NotElem x xs ->
        {auto neq : IsNo (decEq x y)} ->
        {auto prf : NotElem y xs} ->
        NotElem x (y :: xs)


    public export
    toVect : DecEq a => UniqueVect n a -> Vect n a
    toVect [] = []
    toVect (x :: xs) = x :: toVect xs

    -- fromVect : DecEq a => Vect n a -> UniqueVect n a
    -- fromVect [] = []
    -- fromVect (x :: xs) = case fromVect xs of
    --   Yes _ => x :: fromVect xs
    --   No _ => fromVect xs