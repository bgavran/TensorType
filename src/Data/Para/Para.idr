module Data.Para.Para

import Data.Vect
import Data.Vect.Quantifiers

||| Dependent Para
public export
record Para (a : Type) (b : Type) where
    constructor MkPara
    Param : a -> Type
    Run : (x : a) -> Param x -> b

%name Para fp, gp, hp

public export infixr 0 -\->

||| Experimental infix notation, for now
public export
(-\->) : (a, b : Type) -> Type
a -\-> b = Para a b

public export
trivialParam : (a -> b) -> a -\-> b
trivialParam f = MkPara 
  (\_ => Unit)
  (\a, _ => f a)

public export
id : a -\-> a
id = trivialParam id

public export
composePara : a -\-> b -> b -\-> c -> a -\-> c
composePara (MkPara p f) (MkPara q g) = MkPara
  (\x => (p' : p x ** q (f x p')))
  (\x, (p' ** q') => g (f x p') q')

public export infixr 10 \>>

public export
(\>>) : a -\-> b -> b -\-> c -> a -\-> c
(\>>) = composePara


public export
reparam : (pf : a -\-> b) ->
  {q : a -> Type} ->
  (r : (x : a) -> q x -> pf.Param x) ->
  a -\-> b
reparam (MkPara p f) r = MkPara q (\x, qq => f x (r x qq))

public export
data IsNotDependent : Para a b -> Type where
  MkNonDep : (p : Type) -> (f : a -> p -> b) ->
    IsNotDependent (MkPara (\_ => p) f)


public export
GetNonDep : {pf : Para a b} ->
  IsNotDependent pf -> (p : Type ** a -> p -> b)
GetNonDep (MkNonDep p f) = (p ** f)


-- mapRunPara : {a : Type} -> {b : Type} ->
--   (model : Para a b) -> Vect n a -> Vect n b
public export
depMap : {t : a -> Type} -> (f : (x : a) -> t x) ->
  Vect n a -> Vect n (x : a ** t x)
depMap f [] = []
depMap f (x :: xs) = (x ** f x) :: depMap f xs

public export infixr 10 <$^>
public export
(<$^>) : {t : a -> Type} -> (f : (x : a) -> t x) ->
  Vect n a -> Vect n (x : a ** t x)
(<$^>) f xs = depMap f xs


public export
composeNTimes : Nat -> a -\-> a -> a -\-> a
composeNTimes 0 f = id
composeNTimes 1 f = f -- to get rid of the annoying Unit parameter
composeNTimes (S k) f = composePara f (composeNTimes k f)


-- composePara_rhs_1 : (p : Vect n Type) -> (q : Vect m Type)
--   -> (a -> All Prelude.id p -> b)
--   -> (b -> All Prelude.id q -> c)
--   -> (a -> All Prelude.id (p ++ q) -> c)
-- composePara_rhs_1 [] [] f g a [] = ?composePara_rhs_1_rhs_2
-- composePara_rhs_1 [] (q :: ws) f g a (pq :: pqs) = ?composePara_rhs_1_rhs_3
-- composePara_rhs_1 (p :: ps) q f g a pq = ?composePara_rhs_1_rhs_1
-- 
-- composePara : Para a n b -> Para b m c -> Para a (n + m) c
-- composePara (MkPara p f) (MkPara q g) = MkPara (p ++ q) (composePara_rhs_1 p q f g)


