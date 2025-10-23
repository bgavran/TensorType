module Data.Unique

import Data.Vect
import Data.List
import Data.List.Quantifiers
import Decidable.Equality
import Decidable.Equality.Core
import public Data.List.Elem
import Misc

||| A list with unique elements
||| Requires a mutual block since it is defined in terms of NotElem
namespace UniqueList
  mutual
    ||| A list with unique elements
    ||| An element can be inserted if it is not already in the list
    ||| Like a Set, but with ordering
    ||| @ a The type of the elements in the list
    public export
    data UniqueList : (a : Type) -> DecEq a => Type where
      Nil : {a : Type} -> DecEq a => UniqueList a
      (::) : {a : Type} -> DecEq a =>
        (x : a) ->
        (xs : UniqueList a) ->
        {auto prf : NotElem x xs} ->
        UniqueList a
  
    ||| A proof that an element is *not* found in the unique list
    public export
    data NotElem : DecEq a =>
      (x : a) -> (xs : UniqueList a) -> Type where
      NotInEmptyList : {a : Type} -> DecEq a => (x : a)
        -> NotElem {a=a} x []
      NotInNonEmptyList : {a : Type} -> (de : DecEq a) =>
        {x, y : a} ->
        (xs : UniqueList a) ->
        NotElem x xs ->
        {auto neq : IsNo (decEq x y)} ->
        {auto prf : NotElem y xs} ->
        NotElem x (y :: xs)


  ||| Decision procedure for proving an element is *not* found in an unique list
  public export
  decElemNotInUniqueList : {a : Type} -> DecEq a =>
    (x : a) -> (xs : UniqueList a) -> Dec (NotElem x xs)
  decElemNotInUniqueList x [] = Yes $ NotInEmptyList x
  decElemNotInUniqueList x (y :: xs) = case decEq x y of
    Yes Refl => No $ \(NotInNonEmptyList  _ _ {neq})
      => uninhabited @{uniqueUninhabited} neq
    No neq => case decElemNotInUniqueList x xs of
      Yes prf => Yes $ NotInNonEmptyList _ prf {neq=(proofIneqIsNo neq)}
      No nprf => No $ \(NotInNonEmptyList _ prf') => nprf prf'
  
  ||| Convert an unique list to a list
  public export
  toList : {a : Type} -> DecEq a => UniqueList a -> List a
  toList [] = []
  toList (x :: xs) = x :: toList xs
  
  ||| Convert a list to an unique list, removing duplicates
  public export
  fromList : {a : Type} -> DecEq a => List a -> UniqueList a
  fromList [] = []
  fromList (x :: xs) = case decElemNotInUniqueList x (fromList xs) of
    Yes _ => x :: fromList xs
    No _ => fromList xs
  
  ||| Convert a list to an unique list, throw an error if there are duplicates
  public export
  fromListMaybe : {a : Type} -> DecEq a => List a -> Maybe (UniqueList a)
  fromListMaybe [] = Just []
  fromListMaybe (x :: xs) = case fromListMaybe xs of
    Just xs' => case decElemNotInUniqueList x xs' of
      Yes _ => Just (x :: xs')
      No _ => Nothing
    Nothing => Nothing
  
  public export
  fromVect : {a : Type} -> DecEq a => Vect n a -> UniqueList a
  fromVect [] = []
  fromVect (x :: xs) = case decElemNotInUniqueList x (fromVect xs) of
    Yes _ => x :: fromVect xs
    No _ => fromVect xs
  
  public export
  toVect : {a : Type} -> DecEq a => UniqueList a -> (n : Nat ** Vect n a)
  toVect [] = (0 ** [])
  toVect (x :: xs) = let (n ** xs) = toVect xs
                     in (S n ** x :: xs)
  
  
  public export
  packUnique : UniqueList Char -> String
  packUnique = pack . toList
  
  public export
  unpackUnique : String -> UniqueList Char
  unpackUnique = fromList . unpack

||| Concatenation of unique lists
||| Requires a mutual block since it is defined in terms of expandUnique
namespace UniqueListConcat
  
  public export infixr 5 +++
  public export
  (+++) : {a : Type} -> DecEq a =>
    (xs, ys : UniqueList a) -> UniqueList a

  public export
  expandUnique : {a : Type} -> DecEq a =>
    (x' : a) ->
    (xs, ys : UniqueList a) ->
    {prfx : NotElem x' xs} ->
    {prfy : NotElem x' ys} ->
    NotElem x' (xs +++ ys)

  (+++) [] ys = ys
  (+++) ((::) x xs {prf=prfx}) ys = case decElemNotInUniqueList x ys of
    Yes prfy_x => (::) x (xs +++ ys) {prf=(expandUnique x xs ys {prfx=prfx} {prfy=prfy_x})}
    No _ => xs +++ ys

  expandUnique _ [] _ {prfy} = prfy
  expandUnique x' ((::) x xs {prf=not_elem_x_xs}) ys
    {prfx = (NotInNonEmptyList {neq} xs not_elem_x'_xs)}
    {prfy=not_elem_x'_ys} with (decElemNotInUniqueList x ys)
    _ | (Yes _)
      = let v = expandUnique x' xs ys {prfx=not_elem_x'_xs} {prfy=not_elem_x'_ys}
        in NotInNonEmptyList {x=x'} {y=x} (xs +++ ys) v {neq} {prf=(expandUnique x xs ys)}
    _ | (No _)
      = expandUnique x' xs ys {prfx=not_elem_x'_xs} {prfy=not_elem_x'_ys}

  
  public export
  uniqueJoin : {a : Type} -> DecEq a => List (List a) -> UniqueList a
  uniqueJoin = fromList . join


||| A proof that all elements of a unique list satisfy a property. 
public export
data All : (0 p : a -> Type) -> DecEq a => UniqueList a -> Type where
  Nil  : {a : Type} -> {0 p : a -> Type} -> DecEq a => All p Nil
  (::) : {a : Type} -> DecEq a =>
    {0 p : a -> Type} ->
    {x : a} ->
    {0 xs : UniqueList a} ->
    {auto prf : NotElem x xs} ->
    p x ->
    All p xs ->
    All p (x :: xs)

||| A proof that all elements of a unique list in a chosen list
public export
data IsFrom : {a : Type} -> DecEq a =>
  (sublist : UniqueList a) ->
  (xs : List a) -> Type where
  IndeedItIs : {a : Type} -> DecEq a =>
    {sublist : UniqueList a} ->
    {xs : List a} ->
    {auto prf : All (\x => Elem x xs) sublist} ->
    IsFrom sublist xs


||| Takes lists xs and ys, and returns all the elements of xs that are not in ys
||| When ys is a sublist of xs, this is the complement of ys in xs
public export
complement : DecEq a =>
  (xs : UniqueList a) ->
  (ys : UniqueList a) -> 
  List a -- technically we also know this is unique
complement [] ys = []
complement (x :: xs) ys = case decElemNotInUniqueList x ys of
  Yes prf => complement xs ys
  No _ => x :: (complement xs ys)


data TestList : (a : Type) -> DecEq a => Type where
  ToCubicalTensorestList : DecEq a =>
    (xs : List a) ->
    {ul : UniqueList a} ->
    {auto prf : fromListMaybe xs = Just ul} ->
    TestList a



test : TestList Nat
test = ToCubicalTensorestList [1,2,3]

namespace UniqueListFrom
  ||| A list of unique elements with elements from ls
  public export
  data UniqueListFrom : (a : Type) -> DecEq a => (ls : List a) -> Type where
    MkUniqueListFrom : {a : Type} -> DecEq a => {ls : List a} ->
      (xs : UniqueList a) -> {auto prf : xs `IsFrom` ls} ->
      UniqueListFrom a ls

  public export
  toUniqueList : {a : Type} -> DecEq a => {ls : List a} ->
    UniqueListFrom a ls -> UniqueList a
  toUniqueList (MkUniqueListFrom xs) = xs


av : UniqueList Nat
av = [1, 2, 3]

as : UniqueList String
as = ["a", "b", "c", "ieva"]

avv : UniqueList Nat
avv = fromVect [1, 2, 3, 3]





aa : UniqueListFrom Nat [10, 11, 12]
aa = MkUniqueListFrom [10, 11]

at : UniqueList Nat
at = fromList [10, 11]

bb : UniqueListFrom Char ['a', 'b', 'c']
bb = MkUniqueListFrom ['a', 'b']

cc : UniqueListFrom String ["i", "j", "k"]
cc = MkUniqueListFrom ["i", "j", "k"]


-- Not used?
public export
data UniqueString : Type where
  MkUniqueString : (str : String) ->
    {auto prf : packUnique (unpackUnique str) = str} ->
    UniqueString

public export
data UniqueStringFrom : (alphabet : String) -> Type where
  MkUniqueStringFrom : {alphabet : String} ->
     (str : String) ->
     {auto prf : packUnique (unpackUnique str) = str} ->
     {auto prf22 : (unpackUnique str) `IsFrom` (unpack alphabet)} ->
     UniqueStringFrom alphabet

ttfrom : UniqueStringFrom "ijk"
ttfrom = MkUniqueStringFrom "ijk"


public export
toString : {alphabet : String} -> UniqueStringFrom alphabet -> String
toString (MkUniqueStringFrom str) = str


-- ||| A vector of unique elements
-- ||| Consists of a vector and a proof that once we remove duplicates, we get the same vector back
-- public export
-- record UniqueVect (n : Nat) (a : Type) {auto eq : Eq a} where
--    constructor MkUniqueVect
--    baseVect : Vect n a
--    isUnique: nub baseVect = baseVect


public export
concatMapUnique : {a : Type} -> DecEq a =>
  List (UniqueList a) -> UniqueList a
concatMapUnique [] = []
concatMapUnique (x :: xs) = x +++ concatMapUnique xs
