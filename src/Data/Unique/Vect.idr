module Data.Unique.Vect

import Data.Vect
import Decidable.Equality
import Decidable.Equality.Core
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

  namespace All
    ||| A proof that elements of a unique vector satisfy a property
    public export
    data All : DecEq a => (0 p : a -> Type) -> UniqueVect rank a -> Type where
      Nil : DecEq a => {0 p : a -> Type} -> All p []
      (::) : DecEq a => {0 p : a -> Type} ->
        {0 x : a} ->
        {0 xs : UniqueVect k a} ->
        NotElem x xs =>
        p x ->
        All p xs ->
        All p (x :: xs)

        


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
    There : DecEq a =>
      {x : a} ->
      {xs : UniqueVect k a} ->
      (prf : NotElem y xs) =>
      (later : Elem x xs) ->
      Elem x (y :: xs)

  public export
  notElem : DecEq a =>
    {x : a} ->
    {xs : UniqueVect n a} ->
    (Not (Elem x xs)) -> NotElem x xs
  notElem {xs = []} f = NotInEmptyVect x
  notElem {xs = (y :: ys)} f with (decEq x y)
    _ | (Yes Refl) = absurd (f Here)
    _ | (No neq) = NotInNonEmptyVect
      {neq=(proofIneqIsNo neq)} ys (notElem (\e => f ?bb))

  ||| An element cannot be in an empty vector
  public export
  {x : a} -> DecEq a => Uninhabited (Elem x []) where
    uninhabited Here impossible
    uninhabited (There later) impossible

  ||| Turn the proof that an element `x` is in a vector into the index of `x`
  public export
  indexOf : DecEq a => {0 n : Nat} -> {0 xs : UniqueVect n a} ->
    Elem x xs -> Fin n
  indexOf Here = FZ
  indexOf (There later) = FS (indexOf later)

  public export
  length : DecEq a => UniqueVect n a -> Nat
  length [] = 0
  length (x :: xs) = 1 + length xs

  ||| Drop all the elements up and until the element `x` from a unique vector
  public export
  drop : DecEq a =>
    (xs : UniqueVect n a) ->
    (elem : Elem x xs) ->
    UniqueVect (n `minus` (finToNat (FS (indexOf elem)))) a
  drop {n=S k} (_ :: xs) Here = rewrite minusZeroRight k in xs
  drop (_ :: xs) (There later) = drop xs later


  public export
  Test1 : UniqueVect 5 String
  Test1 = ["a", "b", "c", "d", "e"]

  public export
  wher : Elem "c" Test1
  wher = There $ There $ Here

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



  ||| If `x` is not equal to `y`, then `x` is not in the list `[y]`
  ||| It seems that Idris manages to discover this proof automatically, so 
  ||| this is not needed in practice
  ||| Its dual is needed, hence the %hint in for the declaration below
  public export
  notEqualNotElem : DecEq a =>
    {x, y : a} ->
    (neq : IsNo (decEq x y)) ->
    NotElem x [y]
  notEqualNotElem _ = NotInNonEmptyVect [] (NotInEmptyVect x)

  %hint
  public export
  notEqualNotElem2 : DecEq a =>
    {x, y : a} ->
    (neq : IsNo (decEq x y)) ->
    NotElem y [x]
  notEqualNotElem2 neq = notEqualNotElem {x=y} {y=x} (isNoSym neq)

  public export
  decElemInUniqueVect : DecEq a =>
    (x : a) -> (xs : UniqueVect n a) -> Dec (Elem x xs)
  decElemInUniqueVect x [] = No absurd
  decElemInUniqueVect x (y :: ys) = case decEq x y of
    Yes Refl => Yes Here
    No neq => case decElemInUniqueVect x ys of
      Yes prf => Yes $ There prf
      No nprf => No $ \case
        Here => neq Refl
        (There later) => nprf later

  ||| Number of unique elements found in any of two unique vectors
  public export
  numUnique : {n, m : Nat} -> DecEq a => UniqueVect n a -> UniqueVect m a -> Nat
  numUnique [] _ = m
  numUnique (x :: xs) ys = case decElemInUniqueVect x ys of
    Yes _ => numUnique xs ys -- found in ys, so don't count it again
    No _ => 1 + numUnique xs ys -- not found in ys, so count it

  ||| Number of unique elements that are found in both of the two unique vectors
  public export
  numOverlap : {n, m : Nat} -> DecEq a =>
    UniqueVect n a -> UniqueVect m a -> Nat
  numOverlap [] ys = 0
  numOverlap (x :: xs) ys = case decElemInUniqueVect x ys of
    Yes _ => 1 + numOverlap xs ys -- found also in ys, so count it
    No _ => numOverlap xs ys

  
  mutual
    public export infixr 5 +++

    ||| Union
    public export
    (+++) : DecEq a =>
      (xs : UniqueVect n a) ->
      (ys : UniqueVect m a) ->
      UniqueVect (numUnique xs ys) a
    [] +++ ys = ys
    (x :: xs) +++ ys with (decElemInUniqueVect x ys)
      _ | (Yes prf) = xs +++ ys -- x :: (xs +++ ys)
      _ | (No nprf) = (::) x (xs +++ ys) {prf=expandUnique {prfy=notElem nprf}}
   -- (x :: xs) +++ ys = case (decElemInUniqueVect x ys) of
   --   (Yes prf) => ?aa -- x :: (xs +++ ys)
   --   (No nprf) => ?bb -- xs +++ ys

    ||| If `x` is not in `xs` nor `ys`, then it also won't be in `xs +++ ys`
    public export
    expandUnique : DecEq a =>
      {x : a} ->
      {xs : UniqueVect n a} ->
      {ys : UniqueVect m a} ->
      (prfx : NotElem x xs) =>
      (prfy : NotElem x ys) =>
      NotElem x (xs +++ ys)
    -- todo implement this

  mutual
    public export
    intersect : DecEq a =>
      (xs : UniqueVect n a) ->
      (ys : UniqueVect m a) ->
      UniqueVect (numOverlap xs ys) a
    intersect [] ys = []
    intersect (x :: xs) ys with (decElemInUniqueVect x ys)
      _ | (Yes prf) = (::) x (intersect xs ys) {prf=notElemIntersect}
      _ | (No nprf) = intersect xs ys

    ||| If `x` is not in `xs`, then we can intersect `xs` with any other list,
    ||| and `x` still wont' be in the result (even if `x` was in the other list)
    public export
    notElemIntersect : DecEq a =>
      {x : a} ->
      {xs : UniqueVect n a} ->
      {ys : UniqueVect m a} ->
      (prfx : NotElem x xs) =>
      (prfy : Elem x ys) =>
      NotElem x (intersect xs ys)


  ||| All elements of the intersection of two vectors `xs` and `ys`
  ||| will be elements of `xs`
  public export
  allElemIntersectFst : DecEq a => 
    (xs : UniqueVect n a) ->
    (ys : UniqueVect m a) ->
    All (\x => Elem x xs) (intersect xs ys)
  allElemIntersectFst = ?allElemIntersect_rhs

  ||| All elements of the intersection of two vectors `xs` and `ys`
  ||| will be elements of `ys`
  public export
  allElemIntersectSnd : DecEq a => 
    (xs : UniqueVect n a) ->
    (ys : UniqueVect m a) ->
    All (\x => Elem x ys) (intersect xs ys)
  allElemIntersectSnd = ?allElemIntersect_rhs2



  public export
  l1 : UniqueVect 3 String
  l1 = ["a", "b", "c"]

  public export
  l2 : UniqueVect 3 String
  l2 = ["c", "d", "e"]

  public export
  l3 : UniqueVect 5 String
  l3 = l1 +++ l2

  public export
  l4 : UniqueVect 1 String
  l4 = intersect l1 l2

    -- expandUnique {xs = []} {ys = (_ :: _)} prf = prf
    -- expandUnique {xs = (x :: xs)} {ys = (y :: ys)} prf = case decElemInUniqueVect x ys of
    --   Yes prf' => expandUnique {prf=prf'} xs ys

  -- fromVect : DecEq a => Vect n a -> UniqueVect n a
  -- fromVect [] = []
  -- fromVect (x :: xs) = case fromVect xs of
  --   Yes _ => x :: fromVect xs
  --   No _ => fromVect xs