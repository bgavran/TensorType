module Data.Autodiff.AdditiveContainer.Morphism.Definition

import Data.Container
import Data.ComMonoid
import Data.Autodiff.AdditiveContainer.Object.Definition

export infixr 1 =%> -- (closed) dependent lens
export infixr 1 =&> -- (closed) dependent chart
export infixr 1 =:> -- (closed) cartesian morphism
export prefix 0 !% -- constructor the (closed) dependent lens
export prefix 0 !& -- constructor the (closed) dependent chart
export prefix 0 !: -- constructor the (closed) cartesian morphism
public export prefix 0 %!
public export prefix 0 &!
public export prefix 0 :!
export infixl 5 %>> -- composition of dependent lenses
export infixl 5 &>> -- composition of dependent charts

namespace DependentLenses
  ||| Morphism between additive containers
  ||| It should also encode the constraint that the backward part is a comonoid
  ||| homomorphism, that is left out
  public export
  record (=%>) (c1, c2 : AddCont) where
    constructor (!%)
    ULens : UC c1 =%> UC c2

  public export
  (%!) : {0 c1, c2 : AddCont} -> c1 =%> c2 -> (x : c1.Shp) -> (y : c2.Shp ** (c2.Pos y -> c1.Pos x))
  (%!) (!% f) = (%!) f

  public export
  (.fwd) : {0 c1, c2 : AddCont} -> c1 =%> c2 -> c1.Shp -> c2.Shp
  (.fwd) f = (ULens f).fwd

  public export
  (.bwd) : {0 c1, c2 : AddCont} -> (f : c1 =%> c2) ->
    (x : c1.Shp) -> c2.Pos (f.fwd x) -> c1.Pos x
  (.bwd) f = (ULens f).bwd

  public export
  compDepLens : {0 c1, c2, c3 : AddCont} -> c1 =%> c2 -> c2 =%> c3 -> c1 =%> c3
  compDepLens f g = (!%) (compDepLens (ULens f) (ULens g))

  public export
  (%>>) : {0 c1, c2, c3 : AddCont} -> c1 =%> c2 -> c2 =%> c3 -> c1 =%> c3
  (%>>) = compDepLens

  public export
  id : {0 c : AddCont} -> c =%> c
  id = (!%) id

  public export
  lensInputs : {c, d : AddCont} -> c =%> d -> AddCont
  lensInputs lens = MkAddCont
    (lensInputs (ULens lens))
    {mon=(MkI @{\s => ?lensInputsMon_rhs})}


namespace DependentCharts
  ||| Morphism between additive containers
  ||| It should also encode the constraint that the backward part is a comonoid
  ||| homomorphism, that is left out
  public export
  record (=&>) (c1, c2 : AddCont) where
    constructor (!&)
    UChart : UC c1 =&> UC c2

  public export
  (&!) : {0 c1, c2 : AddCont} -> c1 =&> c2 -> (x : c1.Shp) -> (y : c2.Shp ** (c1.Pos x -> c2.Pos y))
  (&!) (!& f) = (&!) f

  public export
  (.fwd) : {0 c1, c2 : AddCont} -> c1 =&> c2 -> c1.Shp -> c2.Shp
  (.fwd) f = (UChart f).fwd

  public export
  (.bwd) : {0 c1, c2 : AddCont} -> (f : c1 =&> c2) ->
    (x : c1.Shp) -> c1.Pos x -> c2.Pos (f.fwd x)
  (.bwd) f = (UChart f).bwd

  public export
  compDepChart : {0 c1, c2, c3 : AddCont} -> c1 =&> c2 -> c2 =&> c3 -> c1 =&> c3
  compDepChart f g = (!&) (compDepChart (UChart f) (UChart g))

  public export
  (&>>) : {0 c1, c2, c3 : AddCont} -> c1 =&> c2 -> c2 =&> c3 -> c1 =&> c3
  (&>>) = compDepChart

  public export
  id : {0 c : AddCont} -> c =&> c
  id = (!&) id