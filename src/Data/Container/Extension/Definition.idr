module Data.Container.Extension.Definition

import Data.Container.Object.Definition

import Data.Functor.Naperian
import Misc


||| Extension of a container
||| This allows us to talk about the content, or payload of a container
public export
record Ext (c : Cont) (x : Type) where
  constructor (<|)
  shapeExt : c.Shp
  index : c.Pos shapeExt -> x

||| Container c can be said to be "full off" a type x
||| `fullOf` is sometimes used as infix operator to aid readability
public export
fullOf : Cont -> Type -> Type
fullOf c x = Ext c x 

||| Every extension is a functor : Type -> Type
public export
Functor (Ext c) where
  map {c=shp !> pos} f (s <| v) = s <| f . v

||| Composition of extensions is a functor
public export
Functor ((Ext d) . (Ext c)) where
  map f e = (map f) <$> e

||| Container setter
public export
set : {c : Cont} -> InterfaceOnPositions c Eq =>
  (e : Ext c x) -> c.Pos (shapeExt e) -> x -> Ext c x
set {c=(s !> p)} @{MkI} (sh <| contentAt) i x
  = sh <| updateAt contentAt (i, x)

namespace ExtProofs
  ||| Map preserves the shape of the extension
  public export
  mapShapeExt : {c : Cont} ->
    (l : c `fullOf` a) ->
    shapeExt (f <$> l) = shapeExt l
  mapShapeExt {c=shp !> pos} (sh <| _) = Refl
  
  public export
  mapIndexCont : {0 f : a -> b} -> {c : Cont} ->
    (l : c `fullOf` a) ->
    (ps : c.Pos (shapeExt (f <$> l))) ->
    f (index l (rewrite sym (mapShapeExt {f=f} l) in ps))
      = index (f <$> l) ps
  mapIndexCont {c=shp !> pos} (sh <| contentAt) ps = Refl


||| Notably, Eq instance is not possible to write for a general Ext c a
||| This is because Eq needs to be total, and some containers have an infinite number of positions, meaning they cannot be checked for equality in finite time.
||| Meaning, the decidability works when the user provides a function to perform that check (perhaps by higher-order symbolic manipulation, as opposed to brute-force)
||| The trick of using DecEq to create an Eq instance is used in DPair?
||| TODO do we need this? 
namespace EqExt
  ||| Structure needed to store the equality data for Ext
  public export
  record EqExt (e1, e2 : Ext c a) where
    constructor MkEqExt
    ||| The shapes must be equal
    shapesEqual : e1.shapeExt = e2.shapeExt
    ||| For each position in that shape, the values must be equal
    ||| Relying on rewrite to get the correct type for the position
    valuesEqual : (p : c.Pos (e1.shapeExt)) ->
      e1.index p =
      e2.index (rewrite__impl (c.Pos) (sym shapesEqual) p)
    {-
    Another alternative is to use DecEq, and a different explicit rewrite
     -}

  public export
  decEqExt : (e1, e2 : Ext c a) ->
    EqExt e1 e2 ->
    Dec (e1 = e2)
  -- decEqExt e1 e2 (MkEqExt shapesEqual valuesEqual)
  --   = Yes ?decEqExt_rhs_0 -- complicated, but doable?

  