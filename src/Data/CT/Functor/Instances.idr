module Data.CT.Functor.Instances

import Data.CT.Category.Definition
import Data.CT.Category.Instances
import Data.CT.Functor.Definition

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
    {x, y : Type} -> (x -> y) -> Functor (FamObj {c=c} y) (FamObj {c=c} x)
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

--------------------------------------------------------------------------------
-- Dependent Types in Poly (Category of Containers & Dependent Lenses)
--
-- Reference: von Glehn, "Polynomials and Models of Type Theory", Section 4.1
--
-- Key insight: Poly is NOT locally cartesian closed, but:
--   1. Dependent sums (Σ-types) always exist
--   2. Dependent products (Π-types) exist only along cartesian morphisms
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- IN TYPE
--
-- A type family over `a` is: `a -> Type`
-- The dependent pair is:     `(x : a ** fam x)`
-- The dependent function is: `(x : a) -> fam x`
--------------------------------------------------------------------------------

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

namespace AddCont
  public export
  IndexedAddCont : AddCont -> Type
  IndexedAddCont c = c.Shp -> AddCont

  public export
  AddContDPair : {a : AddCont} -> IndexedAddCont a -> AddCont
  AddContDPair a' = MkAddCont
    (((x ** t) : DPair a.Shp ((.Shp) . a')) !> (a' x).Pos t)
    {mon=(?MonDPairAddCont)}


  public export
  AddContDFunFinite : {n : Nat} -> (Fin n -> AddCont) -> AddCont
  AddContDFunFinite {n = 0} i = Scalar
  AddContDFunFinite {n = (S k)} i = i 0 >< AddContDFunFinite (i . FS)

  public export
  indexShp : {n : Nat} -> {i : Fin n -> AddCont} ->
    (j : Fin n) ->
    (AddContDFunFinite i).Shp -> (i j).Shp
  indexShp {n = (S k)} FZ (s, _) = s
  indexShp {n = (S k)} {i} (FS y) (_, ss) = indexShp {i=i . FS} y ss

  public export
  AddContDFunction : {a : AddCont} -> IndexedAddCont a -> AddCont
  AddContDFunction a' = MkAddCont 
    ((s : (x : a.Shp) -> (a' x).Shp) !> ((x : a.Shp) -> (a' x).Pos (s x)))
    {mon=(?MonDFunctionAddCont)}
    --{mon=(MkI @{\s => MkComMonoid
    --  (\l, r => \x => (a' x).Plus (s x) (l x) (r x))
    --  (\x => (a' x).Zero (s x))})}

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

--------------------------------------------------------------------------------
-- COMPARISON WITH CHARTS/LENSES
--
-- A chart `c =&> d` is a MORPHISM in Poly, involving both shapes AND positions.
-- A family `c.Shp -> Cont` is just a FUNCTION on shapes.
--
-- Charts give richer structure (relating positions), but families are simpler
-- and sufficient for forming dependent sums and products.
--
-- You CAN extract a family from certain charts:
--------------------------------------------------------------------------------

-- The "universe" container: shapes are types, positions are their elements  
public export
ContUniverse : Cont
ContUniverse = (t : Type) !> t

-- From a chart to Universe, extract just the shape-level data as a family
-- (This loses the position-level information from the chart!)
public export
famFromChart : (c : Cont) -> (f : c =&> ContUniverse) -> IndexedCont c
famFromChart c f = \s => ((_ : f.fwd s) !> Void)
  -- We get family shapes from f.fwd, but lose the f.bwd data
  -- The chart's f.bwd : (s : c.Shp) -> c.Pos s -> f.fwd s 
  -- doesn't fit into ContFam's structure

--------------------------------------------------------------------------------
-- WHY Poly ISN'T LOCALLY CARTESIAN CLOSED
--
-- In a locally cartesian closed category, for any morphism f : A -> B,
-- the pullback functor f* : C/B -> C/A has a right adjoint Πf.
--
-- In Poly, this fails for general dependent lenses. The right adjoint
-- only exists for CARTESIAN morphisms (where the backward map is an iso).
--
-- Reference: von Glehn thesis, Section 4.3
--------------------------------------------------------------------------------
