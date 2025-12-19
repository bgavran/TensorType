module Misc

import Data.Vect
import System.Random
import Data.Fin.Arith
import Data.List.Quantifiers
import Data.Vect.Quantifiers
import Decidable.Equality
import Decidable.Equality.Core
import Data.String
import Data.List
import Data.List1

%hide Builtin.infixr.(#)

namespace Applicative
  ||| Definition of liftA2 in terms of (<*>)
  public export
  liftA2 : Applicative f => f a -> f b -> f (a, b)
  liftA2 fa fb = ((,) <$> fa) <*> fb
  
  ||| Tensorial strength
  public export
  strength : Applicative f => a -> f b -> f (a, b)
  strength a fb = liftA2 (pure a) fb
  
  ||| Pointwise Num structure for Applicative functors
  public export
  [applicativeNum] Num a => Applicative f => Num (f a) where
    xs + ys = uncurry (+) <$> liftA2 xs ys
    xs * ys = uncurry (*) <$> liftA2 xs ys
    fromInteger = pure . fromInteger

namespace NaperianVect
  ||| Analogue of `(::)` for vectors, in a Naperian form
  ||| Takes an element and prepends it to some 'vector' 
  public export
  cons : x -> (Fin l -> x) -> (Fin (S l) -> x)
  cons x _ FZ = x
  cons _ f (FS k') = f k'
  
  public export
  head : (Fin (S l) -> x) -> x
  head f = f FZ
  
  public export
  tail : (Fin (S l) -> x) -> (Fin l -> x)
  tail f = f . FS
  
  ||| All but the last element of a 'vector'
  public export
  init : (Fin (S n) -> a) -> Fin n -> a
  init f x = f (weaken x)
  
  ||| Analogus to take in Data.Vect, but for Fin
  public export 
  takeFin : (s : Fin (S n)) -> Vect n a -> Vect (finToNat s) a
  takeFin FZ _ = []
  takeFin (FS s) (x :: xs) = x :: takeFin s xs

||| Interface fo the Exponential
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
interface Sqrt a where
  sqrt : a -> a

public export
Sqrt Double where
  sqrt = Prelude.sqrt

namespace Vect
  public export
  sum : Num a => Vect n a -> a
  sum xs = foldr (+) (fromInteger 0) xs
  
  -- Because of the way foldr for Vect is implemented in Idris 
  -- we have to use this approach below, otherwise allSuccThenProdSucc breaks
  public export 
  prod : Num a => Vect n a -> a
  prod [] = fromInteger 1
  prod (x :: xs) = x * prod xs

namespace List
  public export
  sum : Num a => List a -> a
  sum = foldr (+) (fromInteger 0) 

  public export
  prod : Num a => List a -> a
  prod = foldr (*) (fromInteger 1)

public export
listZip : List a -> List b -> List (a, b)
listZip (x :: xs) (y :: ys) = (x, y) :: listZip xs ys
listZip _ _ = []

public export
maxInList : Ord a => List a -> Maybe a
maxInList [] = Nothing
maxInList [x] = Just x
maxInList (x :: xs) = do
  mx <- maxInList xs
  pure (max x mx)

||| Dual to concat from Data.Vect
public export
unConcat : {n, m : Nat} -> Vect (n * m) a -> Vect n (Vect m a)
unConcat {n = 0} _ = []
unConcat {n = (S k)} xs = let (f, s) = splitAt m xs
                          in f :: unConcat s


namespace RandomUtils
-- Probably there's a faster way to do this
-- public export
-- {n : Nat} -> Random a => Random (Vect n a) where
--   randomIO = sequence $ replicate n randomIO
--   randomRIO (lo, hi) = sequence $ zipWith (\l, h => randomRIO (l, h)) lo hi

  public export
  Random Unit where
    randomIO = pure ()
    randomRIO _ = pure ()

  public export
  Random a => Random b => Random (a, b) where
    randomIO = ?what
    randomRIO (lo, hi) = ?what2



-- for reshaping a tensor
rrrrr : {n, x, y : Nat}
  -> Fin (S n)
  -> {auto prf : n = x * y}
  -> (Fin (S x), Fin (S y))
  -- -> Data.Fin.Arith.(*) (Fin (S x)) (Fin (S y))


||| Splits xs at each occurence of delimeter (general version for lists)
public export
splitList : Eq a =>
  (xs : List a) -> (delimeter : List a) -> (n : Nat ** Vect n (List a))
splitList xs delimeter = 
  if delimeter == []
    then (1 ** [xs]) -- Empty delimiter returns original list
    else case isInfixOfList delimeter xs of
      False => (1 ** [xs]) -- Delimiter not found, return original list
      True => 
        let (before, after) = breakOnList delimeter xs
        in case after of
          [] => (1 ** [before]) -- No more occurrences
          _  => let (restCount ** restVect) = splitList (drop (length delimeter) after) delimeter
                in (S restCount ** before :: restVect)
  where
    -- Check if list starts with delimiter
    isPrefixOfList : List a -> List a -> Bool
    isPrefixOfList [] _ = True
    isPrefixOfList _ [] = False
    isPrefixOfList (d :: ds) (x :: xs) = d == x && isPrefixOfList ds xs
    
    -- Check if delimiter occurs anywhere in the list
    isInfixOfList : List a -> List a -> Bool
    isInfixOfList del [] = del == []
    isInfixOfList del xs@(_ :: xs') = 
      isPrefixOfList del xs || isInfixOfList del xs'
    
    -- Break list at first occurrence of delimiter
    breakOnList : List a -> List a -> (List a, List a)
    breakOnList del xs = breakOnListAcc del xs []
      where
        breakOnListAcc : List a -> List a -> List a -> (List a, List a)
        breakOnListAcc del remaining acc = 
          case isPrefixOfList del remaining of
            True => (reverse acc, remaining)
            False => case remaining of
              [] => (reverse acc, [])
              (c :: cs) => breakOnListAcc del cs (c :: acc)

||| Splits xs at each occurence of delimeter (string version)
public export
splitString : (xs : String) -> (delimeter : String) -> (n : Nat ** Vect n String)
splitString xs delimeter = 
  let (n ** result) = splitList (unpack xs) (unpack delimeter)
  in (n ** pack <$> result)

||| Simple string replacement function
public export
replaceString : String -> String -> String -> String
replaceString old new str = 
  let chars = unpack str
      oldChars = unpack old
      newChars = unpack new
  in pack (replaceInList oldChars newChars chars)
  where
    replaceInList : List Char -> List Char -> List Char -> List Char
    replaceInList [] _ xs = xs
    replaceInList old new [] = []
    replaceInList old new xs@(x :: rest) =
      if isPrefixOf old xs
        then new ++ replaceInList old new (drop (length old) xs)
        else x :: replaceInList old new rest


public export
data IsNo : Dec a -> Type where
  ItIsNo : {prop : Type} -> {contra : Not prop} -> IsNo (No {prop=prop} contra)


public export
[uniqueUninhabited] {a : Type} -> {x : a} -> (de : DecEq a) =>
Uninhabited (IsNo (Equality.decEq x x)) where
  uninhabited y with (decEq x x)
    _ | (Yes _) with (y)
      _ | ItIsNo impossible
    _ | (No contra) = contra Refl


||| Proof of inequality yields IsNo
public export
proofIneqIsNo : {x, y : a} -> DecEq a => ((x = y) -> Void) -> (IsNo (Equality.decEq x y))
proofIneqIsNo f with (decEq x y)
  _ | (Yes prf) = absurd (f prf)
  _ | (No contra) = ItIsNo

||| Proofs about elements existing or not existing in vectors
namespace ElemVector
  ||| A proof that an element is found in a vector at position i
  ||| Position-relevant variant of Elem
  public export
  data ElemIndex : a -> Fin n -> Vect n a -> Type where 
    Here : ElemIndex x FZ (x :: xs)
    There : (later : ElemIndex x i xs) -> ElemIndex x (FS i) (y :: xs)


  ||| A proof that an element is *not* found in vector
  ||| Dual of Elem
  data NotElem : (x : a) -> (xs : Vect n a) -> Type where
    NotElemEmpty : NotElem x []
    NotElemCons : Eq a => {x, y : a} ->
      NotElem x xs ->
      So (x /= y) ->
      NotElem x (y :: xs)


public export
constUnit : a -> Unit
constUnit _ = ()

public export
const2Unit : a -> b -> Unit
const2Unit _ _ = ()

public export
fromBool : Num a => Bool -> a
fromBool False = fromInteger 0
fromBool True = fromInteger 1

public export
applyWhen : Bool -> (a -> a) -> a -> a
applyWhen False f a = a
applyWhen True f a = f a


namespace All
  namespace Vect
    public export
    rewriteAllMap : {xs : Vect n a} ->
      All p (f <$> xs) ->
      All (p . f) xs
    rewriteAllMap {xs = []} [] = []
    rewriteAllMap {xs = (x :: xs)} (a :: as) = a :: rewriteAllMap as
  
  namespace List
    public export
    rewriteAllMap : {xs : List a} ->
      All p (f <$> xs) ->
      All (p . f) xs
    rewriteAllMap {xs = []} [] = []
    rewriteAllMap {xs = (x :: xs)} (a :: as) = a :: rewriteAllMap as


public export
record Iso (a, b : Type) where
  constructor MkIso
  forward : a -> b
  backward : b -> a
  forwardBackward : (x : a) -> backward (forward x) = x
  backwardForward : (y : b) -> forward (backward y) = y


namespace FinArithmetic
  ||| There is a similar function in Data.Fin.Arith, which has the smallest
  ||| possible bound. This one does not, but has a simpler type signature.
  public export
  multFin : {m, n : Nat} -> Fin m -> Fin n -> Fin (m * n)
  multFin {n = (S _)} FZ y = FZ
  multFin {n = (S _)} (FS x) y = y + weaken (multFin x y)

  ||| Like weakenN from Data.Fin, but where n is on the other side of +
  public export
  weakenN' : (0 n : Nat) -> Fin m -> Fin (n + m)
  weakenN' n x = rewrite plusCommutative n m in weakenN n x
  
  ||| Like weakenN, but with mutliplication
  ||| Like shiftMul, but without changing the value of the index
  public export
  weakenMultN : {n : Nat} ->
    (m : Nat) -> {auto prf : IsSucc m} ->
    (i : Fin n) -> Fin (m * n)
  weakenMultN (S 0) {prf = ItIsSucc} i = rewrite multOneLeftNeutral n in i
  weakenMultN (S (S k)) {prf = ItIsSucc} i = weakenN' n (weakenMultN (S k) i)

  multRightUnit : (m : Nat) -> m * 1 = m
  multRightUnit 0 = Refl
  multRightUnit (S k) = cong S (multRightUnit k)

  multRightZeroCancel : (m : Nat) -> m * 0 = 0
  multRightZeroCancel 0 = Refl
  multRightZeroCancel (S k) = multRightZeroCancel k

  ||| Variant of `shift` from Data.Fin, but with multiplication
  ||| Given an index i : Fin n, it recasts it as one where steps are stride sized
  ||| That is, returns stride * i : Fin (stride * n)
  ||| Implemented by recursing on i, adding stride each time
  public export
  shiftMul : {n : Nat} ->
    (stride : Nat) -> {auto prf : IsSucc stride} ->
    (i : Fin n) -> Fin (n * stride)
  shiftMul (S s) {prf = ItIsSucc} FZ = FZ
  shiftMul stride (FS i) = shift stride (shiftMul stride i)

  shiftMulTest : shiftMul {n=3} 5 1 = 5
  shiftMulTest = Refl

  ||| Analogous to strengthen from Data.Fin
  ||| Attempts to strengthen the bound on Fin (m + n) to Fin m
  ||| If it doesn't succeed, then returns the remainder in Fin n
  public export
  strengthenN : {m, n : Nat} -> Fin (m + n) -> Either (Fin m) (Fin n)
  strengthenN {m = 0} x = Right x
  strengthenN {m = (S k)} FZ = Left FZ
  strengthenN {m = (S k)} (FS x) with (strengthenN x)
    _ | (Left p) = Left $ FS p
    _ | (Right q) = Right q
  -- strengthenN {m = 0} x = Nothing
  -- strengthenN {m = (S k)} FZ = Just FZ
  -- strengthenN {m = (S k)} (FS x) with (strengthenN x)
  --   _ | Nothing = Nothing
  --   _ | (Just p) = Just $ FS p
    --= let t = strengthenN x
    --  in ?strengthenN_rhs_3

  -- strengthenN {n = 0} x = Just x
  -- strengthenN {m = 0} {n = (S k)} FZ = Nothing
  -- strengthenN {m = (S j)} {n = (S k)} FZ = Just FZ
  -- strengthenN {m} {n = (S k)} (FS x)
  --   = let t = strengthenN x
  --         v = Fin.FS
  --     in ?what -- strengthenN x


--         restCount = indexCount is -- fpn = 13 : Fin (20)
-- iCTest1 : indexCount {shape = [3, 4, 5]} [1, 2, 3] = 33
-- iCTest1 = ?iCTest_rhs
  
  ||| Like finS, but without wrapping
  ||| finS' last = last
  public export
  finS' : {n : Nat} -> Fin n -> Fin n
  finS' {n = 1} x = x
  finS' {n = (S (S k))} FZ = FS FZ
  finS' {n = (S (S k))} (FS x) = FS $ finS' x
  --finS' {n = S _} x = case strengthen x of
  --    Nothing => x
  --    Just y => FS y

  finSTest : finS' {n = 5} 3 = 4
  finSTest = Refl

  finSTest2 : finS' {n = 5} 4 = 4
  finSTest2 = Refl
  
  
  ||| Adds two Fin n, and bounds the result
  ||| Meaning (93:Fin 5) + (4 : Fin 5) = 4
  public export
  addFinsBounded : {n : Nat} -> Fin n -> Fin n -> Fin n
  addFinsBounded x FZ = x
  addFinsBounded x (FS y) = addFinsBounded (finS' x) (weaken y)


public export
multSucc : {m, n : Nat} -> IsSucc m -> IsSucc n -> IsSucc (m * n)
multSucc {m = S m'} {n = S n'} ItIsSucc ItIsSucc = ItIsSucc

public export
allSuccThenProdSucc : (xs : List Nat) -> {auto ps : All IsSucc xs} -> IsSucc (prod xs)
allSuccThenProdSucc [] {ps = []} = ItIsSucc
allSuccThenProdSucc (_ :: xs') {ps = p :: _} = multSucc p (allSuccThenProdSucc xs')


public export
updateAt : Eq a => (a -> b) -> (a, b) -> (a -> b)
updateAt f (i, val) i' = if i == i' then val else f i'


||| Graph of a dependent function
public export
graph : {t : a -> Type} ->
  (g : (x : a) -> t x) ->
  a -> (x : a ** t x)
graph g x = (x ** g x)

||| Version of `map` for dependent function
||| Note that here `x : a` is identity in some sense, it comes from `f a`
public export
dependentMap : Functor f => {t : a -> Type} ->
  (g : (x : a) -> t x) ->
  f a -> f (x : a ** t x)
dependentMap g fa = map (graph g) fa


||| Interface describing how a type can be displayed as a 2d grid of characters
public export
interface Display (a : Type) where
  display : (x : a) -> (h : Nat ** w : Nat ** Vect h ((Vect w) Char))

-- ||| Any type that implements Display can be shown as a string
-- public export
-- {a : Type} -> Display a => Show a where
--   show x = let (h ** w ** xs) = display x
--                ss = toList (intersperse "\n" (pack . toList <$> xs)) -- add intercalate here, and newline
--            in fastUnlines ss

-- public export
-- Display Char where
--   display x = (1 ** 1 ** [[x]])



{-

interface Comult (f : Type -> Type) a where
  comult : f a -> f (f a)

{shape : Vect n Nat} -> Num a => Comult (TensorA shape) a where
  comult t = ?eir

gg : TensorA [3] Double -> TensorA [3, 3] Double
gg (TS xs) = TS $ map ?fn ?gg_rhs_0

-- [1, 2, 3]
-- can we even do outer product?
-- we wouldn't need reduce, but something like multiply?
outer : {f : Type -> Type} -> {a : Type}
  -> (Num a, Applicative f, Algebra f a)
  => f a -> f a -> f (f a)
outer xs ys = let t = liftA2 xs ys
              in ?outer_rhs 
  
 -}

|||| filter' works without `with`?
filter' : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter' p [] = (0 ** [])
filter' p (x :: xs) = case filter' p xs of 
  (_ ** xs') => if p x then (_ ** x :: xs') else (_ ** xs')

||| filter'' implemented with `with`
filter'' : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter'' p [] = (0 ** [])
filter'' p (x :: xs) with (filter' p xs)
  _ | (_ ** xs') = if p x then (_ ** x :: xs') else (_ ** xs')

{-
Prelude.absurd : Uninhabited t => t -> a

-}

-- h : {n : Nat} -> Vect n a -> Nat
-- h xs = n
-- 
-- 
-- g : {0 n : Nat} -> Vect n a -> Nat
-- g [] = 0
-- g (x :: xs) = 1 + (g xs)
-- 
-- proof2 : (v : Vect n a) -> g v = n
-- proof2 [] = Refl
-- proof2 (x :: xs) = cong (1 +) (proof2 xs)