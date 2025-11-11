module Data.Container.Morphism.Definition

import Data.DPair

import Data.Container.Object.Definition


{-------------------------------------------------------------------------------
Two different types of morphisms:
dependent lenses, and dependent charts
-------------------------------------------------------------------------------}

export infixr 1 =%> -- dependent lens
export infixr 1 =&> -- dependent chart
export infix 1 <%! -- constructor for dependent lens
export infix 1 <&! -- constructor for dependent chart
export prefix 0 !% -- constructor for closed dependent lens
export prefix 0 !& -- constructor for closed dependent chart
export infixl 5 %>> -- composition of dependent lenses

namespace DependentLenses
  ||| Dependent lenses
  ||| Forward-backward container morphisms
  public export
  record (=%>) (c1, c2 : Cont) where
    constructor (<%!)
    fwd : c1.Shp -> c2.Shp
    bwd : (x : c1.Shp) -> c2.Pos (fwd x) -> c1.Pos x

  %name (=%>) f, g, h
  
  
  ||| Constructor for closed dependent lens
  public export 
  (!%) : {0 c1, c2 : Cont} ->
    ((x : c1.Shp) -> (y : c2.Shp ** (c2.Pos y -> c1.Pos x))) ->
    c1 =%> c2
  (!%) f = (\x => fst (f x)) <%! (\x => snd (f x))

  public export
  (%!) : {0 c1, c2 : Cont} ->
    (f : c1 =%> c2) ->
    (x : c1.Shp) -> (y : c2.Shp ** (c2.Pos y -> c1.Pos x))
  (%!) f x = (f.fwd x ** f.bwd x)
  
  ||| Composition of dependent lenses
  public export
  compDepLens : a =%> b -> b =%> c -> a =%> c
  compDepLens f g =
      (g.fwd . f.fwd) <%!
      (\x => f.bwd x . g.bwd (f.fwd x))
  
  public export
  (%>>) : a =%> b -> b =%> c -> a =%> c
  (%>>) = compDepLens

  public export
  id : a =%> a
  id = !% \x => (x ** \y => y)

namespace DependentCharts
  ||| Dependent charts
  ||| Forward-forward container morphisms
  public export
  record (=&>) (c1, c2 : Cont) where
    constructor (<&!)
    fwd : c1.Shp -> c2.Shp
    fwd' : (x : c1.Shp) -> c1.Pos x -> c2.Pos (fwd x)
  
  
  ||| Constructor for closed dependent chart
  public export
  (!&) : {0 c1, c2 : Cont} ->
    ((x : c1.Shp) -> (y : c2.Shp ** (c1.Pos x -> c2.Pos y))) ->
    c1 =&> c2
  (!&) f = (\x => fst (f x)) <&! (\x => snd (f x))


  public export
  compDepChart : a =&> b -> b =&> c -> a =&> c
  compDepChart f g =
      (g.fwd . f.fwd) <&!
      (\x => g.fwd' (f.fwd x) . f.fwd' x)

  public export
  (&>>) : a =&> b -> b =&> c -> a =&> c
  (&>>) = compDepChart

  public export
  id : a =&> a
  id = !& \x => (x ** \y => y)


-- experimental stuff below
||| TODO is this the extension of a container?
val : Cont -> Type -> Cont
val (shp !> pos) r = (s : shp) !> (pos s -> r)

-- Chart -> DLens morphism 
-- Tangent bundle to Contanget bundle, effectively
valContMap : {c1, c2 : Cont} -> {r : Type}
  ->  (f : c1 =&> c2)
  ->  (c1 `val` r) =%> (c2 `val` r)
valContMap {c1=(shp !> pos)} {c2=(shp' !> pos')} (fwd <&! fwd')
  = fwd <%! (\x, k, x' => k (fwd' x x'))

-- ||| A container morphism
-- public export
-- record (~%>) (c1, c2 : ContF R) where
--   constructor (<~!)
--   fwd' : c1.Shp' -> c2.Shp'


-- upd : c1 ~%> c2 -> 
-- %pair (=%>) fwd bwd

