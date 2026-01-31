module Data.Autodiff.AdditiveContainer.Product.Definitions

import Data.Container
import Data.ComMonoid
import Data.Autodiff.AdditiveContainer.Object.Definition
import Data.Autodiff.AdditiveContainer.Object.Instances


public export infixr 0 ><
public export infixr 0 >+<

||| Hancock tensor product
public export
(><) : AddCont -> AddCont -> AddCont
c >< d = MkAddCont (UC c >< UC d)
  @{MkI @{\(cs, ds) => MkComMonoid (\(cl, dl), (cr, dr) =>
    (plus (UMon c cs) cl cr, plus (UMon d ds) dl dr))
    (neutral (UMon c cs), neutral (UMon d ds))}}

||| Coproduct
public export
(>+<) : AddCont -> AddCont -> AddCont
c >+< d = MkAddCont (UC c >+< UC d)
  @{MkI @{\case
    Left cs => MkComMonoid (plus (UMon c cs)) (neutral (UMon c cs))
    Right ds => MkComMonoid (plus (UMon d ds)) (neutral (UMon d ds))}}

{- is waiting for merge of sampling into main
public export
ProbContMonNeutral : {cs : Vect n AddCont} -> (d : Dist n) ->
  (ss : All Shp cs) ->
  AllPos ss
ProbContMonNeutral {cs = []} (MkDist []) [] = []
ProbContMonNeutral {cs = (c :: cs)} (MkDist (p :: ps)) (x :: xs)
  = neutral (UMon c x) :: ProbContMonNeutral {cs=cs} (MkDist ps) xs


public export
ProbContMonPlus : {cs : Vect n AddCont} -> (d : Dist n) ->
  (ss : All Shp cs) ->
  AllPos ss ->
  AllPos ss ->
  AllPos ss
ProbContMonPlus {cs = []} (MkDist []) [] [] [] = []
ProbContMonPlus {cs = (c :: cs)} (MkDist (p :: ps)) (s :: ss) (x :: xs) (y :: ys)
  = plus (UMon c s) x y :: ProbContMonPlus {cs=cs} (MkDist ps) ss xs ys

||| Convex combination of additive containers
public export
ConvexComb : {n : Nat} -> Vect n AddCont -> AddCont
ConvexComb xs = MkAddCont
   (((d, shapes) : (Dist n, All Shp xs)) !> AllPos shapes)
   @{MkI @{\(d, ss) => GoodBoi (ProbContMonPlus d ss) (ProbContMonNeutral d ss)}}
-}