module Data.Container.Base.Quantifiers

import Data.Vect
import Data.List.Quantifiers
import Data.Vect.Quantifiers

import Data.Container.Base.Object.Definition

||| Quantifiers for lists
||| We can have All/Any on shapes, and All/Any on positions
||| We get 3 valid combinations, since AnyAll=AnyAny.
||| That overlap is called AnyShpPos below
namespace List
  namespace AllShp
    public export
    data AllPos : {cs : List Cont} -> All Shp cs -> Type where
      Nil : AllPos []
      (::) : Pos c s -> AllPos {cs=cs} ss -> AllPos {cs=(c::cs)} (s :: ss)

    public export
    head : AllPos {cs=c::cs} (s :: ss) -> c.Pos s
    head (p :: ps) = p

    public export
    tail : AllPos {cs=c::cs} (s :: ss) -> AllPos {cs=cs} ss
    tail (p :: ps) = ps

    public export
    data AnyPos : {cs : List Cont} -> All Shp cs -> Type where
      Here : c.Pos s -> AnyPos {cs=(c::cs)} (s :: ss)
      There : AnyPos ss -> AnyPos (s :: ss)
  
  ||| Once we pick a particular shape, we're forced to pick that position
  public export
  data AnyShpPos : {cs : List Cont} -> Any Shp cs -> Type where
    Here : c.Pos s -> AnyShpPos (Here {x=c} {xs=cs} s)
    There : AnyShpPos ss -> AnyShpPos (There ss)
    

||| Same deal as above, but for Vects
namespace Vect
  namespace AllShp
    public export
    data AllPos : {cs : Vect n Cont} -> All Shp cs -> Type where
      Nil : AllPos []
      (::) : Pos c s -> AllPos {cs=cs} ss -> AllPos {cs=(c::cs)} (s :: ss)

    public export
    head : {0 cs : Vect n Cont} -> {0 ss : All Shp cs} ->
      AllPos {cs=c::cs} (s :: ss) -> c.Pos s
    head (p :: ps) = p

    public export
    tail : {0 cs : Vect n Cont} -> {0 ss : All Shp cs} ->
      AllPos {cs=c::cs} (s :: ss) -> AllPos {cs=cs} ss
    tail (p :: ps) = ps


    public export 
    data AnyPos : {cs : Vect n Cont} -> All Shp cs -> Type where
      Here : c.Pos s -> AnyPos {cs=(c::cs)} (s :: ss)
      There : AnyPos ss -> AnyPos {cs=(c::cs)} (s :: ss)

public export
data AnyShpPos : {cs : Vect n Cont} -> Any Shp cs -> Type where
  Here : c.Pos s -> AnyShpPos (Here {x=c} {xs=cs} s)
  There : AnyShpPos ss -> AnyShpPos (There ss)