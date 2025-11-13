module Data.Container.Morphism.Definition

import Data.DPair

import Data.Container.Object.Definition


{-------------------------------------------------------------------------------
Two different types of morphisms:
dependent lenses, and dependent charts
-------------------------------------------------------------------------------}

export infixr 1 =%> -- (closed) dependent lens
export infixr 1 =&> -- (closed) dependent chart
export prefix 0 !% -- constructor the (closed) dependent lens
export prefix 0 !& -- constructor the (closed) dependent chart
export infixl 5 %>> -- composition of dependent lenses
export infixl 5 &>> -- composition of dependent charts

namespace DependentLenses
  ||| Dependent lenses
  ||| Forward-backward container morphisms
  public export
  data (=%>) : (c1, c2 : Cont) -> Type where
    (!%) : ((x : c1.Shp) -> (y : c2.Shp ** (c2.Pos y -> c1.Pos x))) -> c1 =%> c2

  %name (=%>) f, g, h

  public export
  (%!) : c1 =%> c2 -> (x : c1.Shp) -> (y : c2.Shp ** (c2.Pos y -> c1.Pos x))
  (%!) (!% f) x = f x
  
  ||| Composition of dependent lenses
  public export
  compDepLens : a =%> b -> b =%> c -> a =%> c
  compDepLens (!% f) (!% g) = !% \x => let (b ** kb) = f x 
                                           (c ** kc) = g b
                                       in (c ** kb . kc)
  public export
  (%>>) : a =%> b -> b =%> c -> a =%> c
  (%>>) = compDepLens

  public export
  id : a =%> a
  id = !% \x => (x ** id)

namespace DependentCharts
  ||| Dependent charts
  ||| Forward-forward container morphisms
  public export
  data (=&>) : (c1, c2 : Cont) -> Type where
    (!&) : ((x : c1.Shp) -> (y : c2.Shp ** (c1.Pos x -> c2.Pos y))) -> c1 =&> c2

  %name (=&>) f, g, h

  public export
  (&!) : c1 =&> c2 -> (x : c1.Shp) -> (y : c2.Shp ** (c1.Pos x -> c2.Pos y))
  (&!) (!& f) x = f x
  
  public export
  compDepChart : a =&> b -> b =&> c -> a =&> c
  compDepChart (!& f) (!& g) = !& \x => let (b ** kb) = f x 
                                            (c ** kc) = g b
                                        in (c ** kc . kb)

  public export
  (&>>) : a =&> b -> b =&> c -> a =&> c
  (&>>) = compDepChart

  public export
  id : a =&> a
  id = !& \x => (x ** id)

-- experimental stuff below
||| TODO is this the extension of a container?
val : Cont -> Type -> Cont
val (shp !> pos) r = (s : shp) !> (pos s -> r)

-- Chart -> DLens morphism 
-- Tangent bundle to Contanget bundle, effectively
valContMap : {c1, c2 : Cont} -> {r : Type}
  ->  (f : c1 =&> c2)
  ->  (c1 `val` r) =%> (c2 `val` r)
valContMap {c1=(shp !> pos)} {c2=(shp' !> pos')} (!& f)
  = !% \x => let (y ** ky) = f x in (y ** (. ky))