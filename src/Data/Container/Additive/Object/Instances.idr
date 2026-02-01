module Data.Container.Additive.Object.Instances

import Data.List.Quantifiers
import Data.Vect.Quantifiers

import Data.Container.Base
import Data.ComMonoid
import Data.Container.Additive.Object.Definition

||| Scalar additive container
public export
Scalar : AddCont
Scalar = MkAddCont Scalar

||| Constant additive container, positions not dependent on shapes
||| Allows the backward part to be different than forward one
public export
Const : Type -> ComMonoid -> AddCont
Const a (t ** m) = MkAddCont (Const2 a t) @{MkI @{\_ => m}}

namespace NumConst
  ||| Like above, but where backward part is same as forward one
  ||| Also arises from Num instance
  public export
  Const : (a : Type) -> Num a => AddCont
  Const a = Const a (a ** numIsMonoid)

namespace ListAddCont
  public export
  data AllPos : {cs : List AddCont} -> All (.Shp) cs -> Type where
    Nil : AllPos []
    (::) : c.Pos s -> AllPos ss -> AllPos {cs=(c::cs)} (s :: ss)

  -- implicit variables because of name clash
  public export
  head : {0 c : AddCont} -> {0 s : c.Shp} ->
    AllPos {cs=c::cs} (s :: ss) -> c.Pos s
  head (a :: as) = a
  
  public export
  tail : {0 c : AddCont} -> {0 s : c.Shp} ->
    AllPos {cs=c::cs} (s :: ss) -> AllPos {cs=cs} ss
  tail (a :: as) = as

  public export
  listAddContMonPlus : {cs : List AddCont} ->
    (s : All (.Shp) cs) ->
    AllPos s -> AllPos s -> AllPos s
  listAddContMonPlus [] [] [] = []
  listAddContMonPlus {cs=c::_} (s :: ss) (l :: ls) (r :: rs)
    = plus (UMon c s) l r :: listAddContMonPlus ss ls rs

  public export
  listAddContMonNeutral : {cs : List AddCont} ->
    (s : All (.Shp) cs) ->
    AllPos s
  listAddContMonNeutral {cs = []} [] = []
  listAddContMonNeutral {cs = (c :: cs)} (s :: ss)
    = neutral (UMon c s) :: listAddContMonNeutral {cs} ss
  
  public export
  ListAddContMon : {cs : List AddCont} ->
    (s : All (.Shp) cs) -> ComMonoid (AllPos s)
  ListAddContMon s = MkComMonoid (listAddContMonPlus s) (listAddContMonNeutral s)

  public export
  ListAddCont : List AddCont -> AddCont
  ListAddCont cs = MkAddCont
    ((xs : All (.Shp) cs) !> AllPos xs)
    @{MkI @{ListAddContMon}}


namespace VectAddCont
  ||| Analogue of AllPos for Vects
  ||| Need a lot of implicits to disambiguate
  public export
  data AllPos : {n : Nat} -> {cs : Vect n AddCont} -> All (.Shp) cs -> Type where
    Nil : AllPos []
    (::) : {0 k : Nat} ->
      {0 cs : Vect k AddCont} ->
      {0 ss : All (.Shp) cs} ->
      c.Pos s -> AllPos {cs=cs} ss -> AllPos {cs=(c::cs)} (s :: ss)

  public export
  head : {0 c : AddCont} -> {0 s : c.Shp} -> {0 cs : Vect (S k) AddCont} ->
    {0 ss : All (.Shp) cs} ->
    AllPos {cs=(c::cs)} (s :: ss) -> c.Pos s
  head (a :: as) = a

  public export
  tail : {0 c : AddCont} -> {0 s : c.Shp} -> {0 cs : Vect (S k) AddCont} ->
    {0 ss : All (.Shp) cs} ->
    AllPos {cs=(c::cs)} (s :: ss) -> AllPos {cs=cs} ss
  tail (a :: as) = as

  public export
  vectAddContMonPlus : {n : Nat} -> {cs : Vect n AddCont} ->
    (s : All (.Shp) cs) ->
    AllPos s -> AllPos s -> AllPos s
  vectAddContMonPlus [] [] [] = []
  vectAddContMonPlus {cs=c::_} (s :: ss) (l :: ls) (r :: rs)
    = plus (UMon c s) l r :: vectAddContMonPlus ss ls rs

  public export
  vectAddContMonNeutral : {n : Nat} -> {cs : Vect n AddCont} ->
    (s : All (.Shp) cs) ->
    AllPos s
  vectAddContMonNeutral {cs = []} [] = []
  vectAddContMonNeutral {cs = (c :: cs)} (s :: ss)
    = neutral (UMon c s) :: vectAddContMonNeutral {cs} ss

  public export
  VectAddContMon : {n : Nat} -> {cs : Vect n AddCont} ->
    (s : All (.Shp) cs) -> ComMonoid (AllPos s)
  VectAddContMon s = MkComMonoid (vectAddContMonPlus s) (vectAddContMonNeutral s)

  public export
  VectAddCont : {n : Nat} -> Vect n AddCont -> AddCont
  VectAddCont cs = MkAddCont
    ((xs : All (.Shp) cs) !> AllPos xs)
    @{MkI @{VectAddContMon}}


