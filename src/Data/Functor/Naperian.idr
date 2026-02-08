module Data.Functor.Naperian

import Data.Vect

%hide Data.Vect.transpose

-- Needed to define transposition, and diagonal elements
{-
Lists -> not Naperian! Their shape isn't uniform (they can be of different lengths)
Stream -> Naperian, and is represented by Nat
Vect n ->Naperian, and are represented by Fin n

BinTree in general is not Naperian, but if we restrict to trees of a particular shape, then they are Naperian

Naperian functors arise out of containers with a unit shape
* Would ragged shapes imply dependent types?
-}

public export
interface Applicative f => Naperian f where
    Log : Type -- perhaps a better name is Shape
    lookup : f a -> (Log -> a) -- This and the line below
    tabulate : (Log -> a) -> f a -- are an isomorphism

public export
positions : Naperian f => f (Log {f=f})
positions = tabulate id

public export
transpose : Naperian f => Naperian g => f (g a) -> g (f a)
transpose x = tabulate <$> tabulate (flip (lookup . (lookup x)))

public export
{n : Nat} -> Naperian (Vect n) where
    Log = Fin n
    lookup = flip index
    tabulate = Vect.Fin.tabulate

public export
Naperian f => Naperian g => Naperian (g . f) using Applicative.Compose where
  Log = (Log {f=f}, Log {f=g})
  lookup gfa (pf, pg) = lookup (lookup gfa pg) pf
  tabulate f = tabulate <$> tabulate (flip (curry f))


vectPositionsEx : Vect 3 (Fin 3)
vectPositionsEx = positions

-- reshapeTensorANap : {shape : Vect n Nat} -> {newShape : Vect m Nat}
--   -> TensorA shape a
--   -> (newShape : Vect n Nat)
--   -> {auto prf : prod shape = prod newShape}
--   -> TensorA newShape a
-- reshapeTensorANap t newShape = let tR = lookup t in tabulate ?aa
-- 
-- reshapeIndex : {shape : Vect n Nat} -> {newShape : Vect m Nat}
--   -> {auto prf : prod shape = prod newShape}
--   -> IndexT newShape
--   -> IndexT shape
-- reshapeIndex [] = ?reshapeIndex_rhs_0
-- reshapeIndex (x :: xs) = ?reshapeIndex_rhs_1


-- mapNats : {t, t' : Vect n Nat} -> {auto prf : prod t = prod t'}
--   -> Fin (prod t) -> Fin (prod t')
-- mapNats i = ?mapNats_rhs


-- reshapeIndex' : IndexT [2, 3]
--   -> IndexT [6]
-- reshapeIndex' (i :: j :: Nil) = ?yuu :: Nil

-- tensorPositionsEx : TensorA [3, 3, 3] (IndexT [3, 3, 3])
-- tensorPositionsEx = positions

  -- not sure how to represent Pair, it's curried?
-- Naperian (Pair) where
--     Log = Bool
--     lookup = pairLookup
--     tabulate f = (f False, f True)
    


{-
           a
         x  y

  a'                a''
x' y'             x'' y''

transposed would be


           a
         a'  a''

  x                  y
x' x''             y' y''

---

If it was ragged we would not be able to transpose it
-}
