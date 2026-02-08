module Data.Container.Base.Extension.Definition

import Data.Container.Base.Object.Definition

import Misc

||| Extension of a container
||| This allows us to talk about the content, or payload of a container
public export
record Ext (0 c : Cont) (x : Type) where
  constructor (<|)
  shapeExt : c.Shp
  index : c.Pos shapeExt -> x

||| In `Ext c x`, the container `c` is said to be "full off" values of type `x`
||| `fullOf` is sometimes used as infix operator to aid readability
public export
fullOf : Cont -> Type -> Type
fullOf c x = Ext c x 

public export
Path : Cont -> Type
Path c = (x : c.Shp ** c.Pos x)

||| Every extension is a functor : Type -> Type
public export
Functor (Ext c) where
  map {c=shp !> pos} f (s <| v) = s <| f . v

||| Composition of extensions is a functor
public export
Functor ((Ext d) . (Ext c)) where
  map f e = (map f) <$> e

||| The `index` field of an extension defines a "getter" for a container
||| This is the container setter
public export
set : {0 c : Cont} -> InterfaceOnPositions c Eq =>
  (e : Ext c x) -> c.Pos (shapeExt e) -> x -> Ext c x
set {c=(s !> p)} @{MkI} (sh <| contentAt) i x
  = sh <| updateAt contentAt (i, x)

namespace ExtProofs
  ||| Map ing over an extension preserves its shape 
  public export
  mapShapeExt : {0 c : Cont} ->
    {0 f : a -> b} ->
    (l : c `fullOf` a) ->
    shapeExt (f <$> l) = shapeExt l
  mapShapeExt {c=shp !> pos} (sh <| _) = Refl

  ||| Indexing over a mapped extension is the same as indexing over a rewrite
  ||| of the map
  public export
  mapIndexCont : {c : Cont} ->
    {0 f : a -> b} -> 
    (l : c `fullOf` a) ->
    (ps : c.Pos (shapeExt (f <$> l))) ->
    f (index l (rewrite sym (mapShapeExt {f=f} l) in ps))
      = index (f <$> l) ps
  mapIndexCont {c=shp !> pos} (sh <| contentAt) ps = Refl

||| Structure needed to store equality data for Ext.
||| To prove that two extensions `e1, e2` are equal, we need to provide a proof
||| in two steps, and use the first one to rewrite the second. That is, we need
||| a) a proof that the chosen shape types are equal. This allows us to 
||| rewrite the position maps of both extensions to the same type.
||| b) for each shape, a proof that the positions are equal as types
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


||| Another alternative is to use DecEq, and a different explicit rewrite
public export
decEqExt : (e1, e2 : Ext c a) ->
  EqExt e1 e2 ->
  Dec (e1 = e2)

{-
TODO how does automatic deriving of equality work if the number of positions is infinite? (As is the case with some containers)
Checking for equality by simple brute-force clearly cannot be done in finite time (this works for DecEq, but also for Eq since it is marked as total)

Can decidability work if the user provides a function to perform that check (perhaps by higher-order symbolic manipulation, as opposed to brute-force)?

TODO the trick of using DecEq to create an Eq instance is used in DPair?

-- decEqExt e1 e2 (MkEqExt shapesEqual valuesEqual)
--   = Yes ?decEqExt_rhs_0 -- complicated, but doable?
-}