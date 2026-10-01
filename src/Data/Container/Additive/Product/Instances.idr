module Data.Container.Additive.Product.Instances

import Data.Fin

import Data.Container.Base
import Data.ComMonoid
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Product.Definition
import Data.Container.Additive.Object.Instances

-- Some of this stuff might need moving

||| The product of a finite family, a special case of `Section,` but eager
||| Used for parameters at the moment, where all of them are updated at every
||| step
||| TODO there is some difference with the `Coproduct` in Base?
public export
Product : {n : Nat} -> (Fin n -> AddCont) -> AddCont
Product {n = 0} i = UnitCont
Product {n = (S k)} i = i 0 >*< Product (i . FS)

public export
indexShp : {n : Nat} -> {f : Fin n -> AddCont} ->
  (j : Fin n) ->
  (Product f).Shp -> (f j).Shp
indexShp {n = (S k)} FZ (s, _) = s
indexShp {n = (S k)} {f} (FS y) (_, ss) = indexShp {f = f . FS} y ss

||| Eager form of `Section`, inverse to `indexShp`
public export
tabulateShp : {n : Nat} -> {0 f : Fin n -> AddCont} ->
  ((i : Fin n) -> (f i).Shp) -> (Product f).Shp
tabulateShp {n = 0} _ = ()
tabulateShp {n = S k} s = (s 0, tabulateShp {f = f . FS} (\i => s (FS i)))

public export
injectPos : {n : Nat} -> {f : Fin n -> AddCont} ->
  (j : Fin n) -> (bp : (Product f).Shp) ->
  (f j).PosSet (indexShp {f} j bp) ->
  (Product f).PosSet bp
injectPos {n = S k} FZ (p, rest) g =
  (g, (Product (f . FS)).Zero rest)
injectPos {n = S k} {f} (FS j) (p, rest) g =
  ((f FZ).Zero p, injectPos {f=f . FS} j rest g)

public export
finiteShpMon : {n : Nat} -> {f : Fin n -> AddCont} ->
  ((i : Fin n) -> ComMonoid (f i).Shp) -> ComMonoid (Product f).Shp
finiteShpMon {n = 0} _ = %search
finiteShpMon {n = S k} {f} ms
  = pairIsMonoid @{ms 0} @{finiteShpMon {f = f . FS} (\i => ms (FS i))}
