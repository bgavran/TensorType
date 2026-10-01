module Data.CT.Functor.Instances

import Data.CT.Category.Definition
import Data.CT.Category.Instances
import Data.CT.Functor.Definition

import Data.Vect
import Data.Container.Base
import Data.Container.Additive

public export
id : Functor c c
id = MkFunctor id id

||| Functor Type -> Cat^op
public export
IndCat : (c : Cat) -> Type
IndCat c = Functor c (opCat Cat)

public export
Const : {c : Cat} -> IndCat c
Const = MkFunctor (\_ => c) (\_ => id)

namespace Fam
  public export
  FamObj : {c : Cat} -> (a : Type) -> Cat
  FamObj a = MkCat (a -> c.Obj) (\a', b' => (x : a) -> c.Hom (a' x) (b' x))

  public export
  FamMor : {c : Cat} ->
    {0 x, y : Type} -> (x -> y) -> Functor (FamObj {c=c} y) (FamObj {c=c} x)
  FamMor f = MkFunctor (. f) (\j, xx => j (f xx))

  ||| Functor Type -> Cat^op, we will mostly instantiate this for `c=TypeCat`
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

||| Functor which projects out the forward part of an additive dependent lens
public export
AddBase : Functor AddDLens TypeCat
AddBase = MkFunctor (.Shp) (.fwd)

public export
FamAddDLens : {c : Cat} -> IndCat AddDLens
FamAddDLens = composeFunctors AddBase (FamIndCat {c=c})

-- need to check everything from here onwards

namespace Type
  public export
  IndexedType : Type -> Type
  IndexedType a = a -> Type
  
  public export
  TypeDPair : {a : Type} -> IndexedType a -> Type
  TypeDPair fam = (x : a ** fam x)

  public export
  TypeDFun : {a : Type} -> IndexedType a -> Type
  TypeDFun fam = (x : a) -> fam x

namespace Cont
  ||| TODO probably name clash with other "Indexed container"
  public export
  IndexedCont : Cont -> Type
  IndexedCont c = c.Shp -> Cont
  
  public export
  ContDPair : {a : Cont} -> IndexedCont a -> Cont
  ContDPair a' = ((x ** t) : DPair a.Shp (Shp . a')) !> (a' x).Pos t

  public export
  ContProbDPair : {a : Cont} -> IndexedCont a -> Cont
  ContProbDPair a' = (((x, d) ** t) : DPair (a.Shp, Double) (Shp . a' . fst)) !>
    (a' x).Pos t

-- public export
-- ContDPair : (c : Cont) -> IndexedCont c -> Cont
-- ContDPair c fam = 
--   (st : (s : c.Shp ** (fam s).Shp)) !> 
--   Either (c.Pos (fst st)) ((fam (fst st)).Pos (snd st))

-- Simpler version: just the family positions (no base positions)
-- This corresponds to the "total space" of a display map
public export
ContDPairSimple : (c : Cont) -> IndexedCont c -> Cont
ContDPairSimple c fam = 
  (st : (s : c.Shp ** (fam s).Shp)) !> 
  (fam (fst st)).Pos (snd st)

--------------------------------------------------------------------------------
-- DEPENDENT PRODUCT in Poly (Π-types) — MORE SUBTLE
--
-- Π-types do NOT always exist in Poly. When they do exist:
--   - Shapes: Π(s : S). (fam s).Shp     -- sections of the family
--   - Positions: Σ(s : S). Σ(p : P s). (fam s).Pos (f s)
--
-- This only type-checks when S is "small enough" that we can form Π over it.
--------------------------------------------------------------------------------

public export
ContDFun : (c : Cont) -> IndexedCont c -> Cont
ContDFun c fam = 
  (f : ((s : c.Shp) -> (fam s).Shp)) !> 
  (s : c.Shp ** (p : c.Pos s ** (fam s).Pos (f s)))

--------------------------------------------------------------------------------
-- EXAMPLES
--------------------------------------------------------------------------------

-- Constant family: assigns the same container to every shape
public export
constFam : {c : Cont} -> Cont -> IndexedCont c
constFam d = \_ => d

-- Trivial family: assigns the unit container (one shape, no positions) to every shape
public export
trivialFam : {c : Cont} -> IndexedCont c
trivialFam = \_ => ((_ : ()) !> Void)

-- Family that assigns Bool shapes with no positions
public export
boolFam : {c : Cont} -> IndexedCont c
boolFam = \_ => ((_ : Bool) !> Void)