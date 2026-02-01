module Data.CT.Functor.Instances

import Data.CT.Category.Definition
import Data.CT.Category.Instances
import Data.CT.Functor.Definition

import Data.Container.Base

||| Functor Type -> Cat^op
public export
IndCat : (c : Cat) -> Type
IndCat c = Functor c (opCat Cat)

namespace Fam
  public export
  FamObj : {c : Cat} -> (a : Type) -> Cat
  FamObj a = MkCat (a -> c.Obj) (\a', b' => (x : a) -> c.Hom (a' x) (b' x))
  
  public export
  FamMor : {c : Cat} ->
    {x, y : Type} -> (x -> y) -> Functor (FamObj {c=c} y) (FamObj {c=c} x)
  FamMor f = MkFunctor (. f) (\j, xx => j (f xx))

  ||| We will mostly instantiate this for `c=TypeCat` 
  ||| Functor Type -> Cat^op
  public export
  FamIndCat : {c : Cat} -> IndCat TypeCat
  FamIndCat = MkFunctor (\a => FamObj {c=c} a) FamMor
  

||| Functor which projects the forward part of a dependent lens
public export
Base : Functor DLens TypeCat
Base = MkFunctor Shp (.fwd)

||| DLens -> Type -> Cat^op
public export
FamDLens : {c : Cat} -> IndCat DLens
FamDLens = composeFunctors Base (FamIndCat {c=c})