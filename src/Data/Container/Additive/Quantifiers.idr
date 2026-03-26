module Data.Container.Additive.Quantifiers

import Data.Vect
import Data.List.Quantifiers
import Data.Vect.Quantifiers

import Data.Container.Base

import Data.Container.Additive.Object.Definition
import Data.ComMonoid

-- Follows the structure of `Data.Container.Base.Quantifiers`


||| Quantifiers for lists
||| We can have All/Any on shapes, and All/Any on positions
||| Because additivity is required, there are only two valid combinations
||| AllAll and AnyShpPos
namespace List
  namespace AllShp
    public export
    data AllPos : {cs : List AddCont} -> All (.Shp) cs -> Type where
      Nil : AllPos []
      (::) : c.Pos s -> AllPos ss -> AllPos {cs=(c::cs)} (s :: ss)

    public export
    head : {0 cs : List AddCont} -> {0 ss : All (.Shp) cs} ->
      AllPos {cs=c::cs} (s :: ss) -> c.Pos s
    head (p :: ps) = p

    public export
    tail : {0 cs : List AddCont} -> {0 ss : All (.Shp) cs} ->
      AllPos {cs=c::cs} (s :: ss) -> AllPos {cs=cs} ss
    tail (p :: ps) = ps

    public export
    allPosPlus : {cs : List AddCont} ->
      (s : All (.Shp) cs) ->
      AllPos s -> AllPos s -> AllPos s
    allPosPlus [] [] [] = []
    allPosPlus {cs=c::_} (s :: ss) (l :: ls) (r :: rs)
      = plus (UMon c s) l r :: allPosPlus ss ls rs

    public export
    allPosNeutral : {cs : List AddCont} ->
      (s : All (.Shp) cs) ->
      AllPos s
    allPosNeutral {cs = []} [] = []
    allPosNeutral {cs = (c :: cs)} (s :: ss)
      = neutral (UMon c s) :: allPosNeutral ss

    public export
    allPosComMonoid : {cs : List AddCont} ->
      (s : All (.Shp) cs) -> ComMonoid (AllPos s)
    allPosComMonoid s = MkComMonoid (allPosPlus s) (allPosNeutral s)

  public export
  data AnyShpPos : {cs : List AddCont} -> Any (.Shp) cs -> Type where
    Here : c.Pos s -> AnyShpPos (Here {x=c} {xs=cs} s)
    There : AnyShpPos ss -> AnyShpPos (There ss)

  public export
  anyShpPosPlus : {cs : List AddCont} ->
    (s : Any (.Shp) cs) -> AnyShpPos s -> AnyShpPos s -> AnyShpPos s
  anyShpPosPlus {cs = (c :: _)} (Here s) (Here l) (Here r)
    = Here (c.Plus s l r)
  anyShpPosPlus {cs = (c :: cs)} (There ss) (There l) (There r)
    = There (anyShpPosPlus ss l r)

  public export
  anyShpPosNeutral : {cs : List AddCont} ->
    (s : Any (.Shp) cs) -> AnyShpPos s
  anyShpPosNeutral {cs = (c :: _)} (Here s) = Here (c.Zero s)
  anyShpPosNeutral {cs = (_ :: _)} (There ss) = There (anyShpPosNeutral ss)

  public export
  anyShpPosComMonoid : {cs : List AddCont} ->
    (s : Any (.Shp) cs) -> ComMonoid (AnyShpPos s)
  anyShpPosComMonoid s = MkComMonoid (anyShpPosPlus s) (anyShpPosNeutral s)



namespace Vect
  namespace AllShp
    public export
    data AllPos : {cs : Vect n AddCont} -> All (.Shp) cs -> Type where
      Nil : AllPos []
      (::) : c.Pos s -> AllPos {cs=cs} ss -> AllPos {cs=(c::cs)} (s :: ss)

    public export
    head : {0 cs : Vect n AddCont} -> {0 ss : All (.Shp) cs} ->
      AllPos {cs=c::cs} (s :: ss) -> c.Pos s
    head (p :: ps) = p

    public export
    tail : {0 cs : Vect n AddCont} -> {0 ss : All (.Shp) cs} ->
      AllPos {cs=c::cs} (s :: ss) -> AllPos {cs=cs} ss
    tail (p :: ps) = ps

    public export
    allPosPlus : {cs : Vect n AddCont} ->
      (s : All (.Shp) cs) ->
      AllPos s -> AllPos s -> AllPos s
    allPosPlus [] [] [] = []
    allPosPlus {cs=c::_} (s :: ss) (l :: ls) (r :: rs)
      = plus (UMon c s) l r :: allPosPlus ss ls rs

    allPosNeutral : {cs : Vect n AddCont} ->
      (s : All (.Shp) cs) ->
      AllPos s
    allPosNeutral {cs = []} [] = []
    allPosNeutral {cs = (c :: cs)} (s :: ss)
      = neutral (UMon c s) :: allPosNeutral ss

    public export
    allPosComMonoid : {cs : Vect n AddCont} ->
      (s : All (.Shp) cs) -> ComMonoid (AllPos s)
    allPosComMonoid s = MkComMonoid (allPosPlus s) (allPosNeutral s)


  public export
  data AnyShpPos : {cs : Vect n AddCont} -> Any (.Shp) cs -> Type where
    Here : c.Pos s -> AnyShpPos (Here {x=c} {xs=cs} s)
    There : AnyShpPos ss -> AnyShpPos (There ss)

  public export
  anyShpPosPlus : {cs : Vect n AddCont} ->
    (s : Any (.Shp) cs) -> AnyShpPos s -> AnyShpPos s -> AnyShpPos s
  anyShpPosPlus {cs = (c :: _)} (Here s) (Here l) (Here r)
    = Here (c.Plus s l r)
  anyShpPosPlus {cs = (c :: cs)} (There ss) (There l) (There r)
    = There (anyShpPosPlus ss l r)

  public export
  anyShpPosNeutral : {cs : Vect n AddCont} ->
    (s : Any (.Shp) cs) -> AnyShpPos s
  anyShpPosNeutral {cs = (c :: _)} (Here s) = Here (c.Zero s)
  anyShpPosNeutral {cs = (_ :: _)} (There ss) = There (anyShpPosNeutral ss)

  public export
  anyShpPosComMonoid : {cs : Vect n AddCont} ->
    (s : Any (.Shp) cs) -> ComMonoid (AnyShpPos s)
  anyShpPosComMonoid s = MkComMonoid (anyShpPosPlus s) (anyShpPosNeutral s)