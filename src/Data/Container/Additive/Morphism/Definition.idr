module Data.Container.Additive.Morphism.Definition

import Data.Container.Base
import Data.ComMonoid
import Data.Container.Additive.Object.Definition

export infixr 1 =%+> -- (closed) additive dependent lens
export infixr 1 =&+> -- (closed) additive dependent chart
export prefix 0 !% -- constructor the (closed) dependent lens
export prefix 0 !& -- constructor the (closed) dependent chart
export prefix 0 !: -- constructor the (closed) cartesian morphism
public export prefix 0 %!
public export prefix 0 &!
public export prefix 0 :!
public export prefix 0 !%+ -- constructor the additive closed dlens
public export prefix 0 !&+ -- constructor the additive closed dlens
export infixl 5 %+>> -- composition of dependent lenses
export infixl 5 &+>> -- composition of dependent charts

namespace DependentLenses
  ||| Forward-backward morphism between additive containers
  ||| Analogous to `=%>`, but with an added `+` in syntax to denote additivity
  ||| It should also encode the constraint that the backward part is a comonoid
  ||| homomorphism. That is currently left out.
  |||
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             ├──► (y : c.Shp)
  |||                  │    lens     │
  |||     c.Pos x   ◄──┤             ├◄── d.Pos y
  |||                  └─────────────┘
  public export
  record (=%+>) (c, d : AddCont) where
    constructor (!%) -- at the moment, we do not plan to use this constructor
    ULens : UC c =%> UC d

  ||| Analogous to `!%` for ordinary containers, allows us to construct the 
  ||| lens directly
  public export
  (!%+) : {0 c, d : AddCont} ->
    ((x : c.Shp) -> (y : d.Shp ** (d.Pos y -> c.Pos x))) ->
    c =%+> d
  (!%+) f = (!%) ((!%) f)

  public export
  (%!+) : {0 c, d : AddCont} ->
    c =%+> d -> (x : c.Shp) -> (y : d.Shp ** (d.Pos y -> c.Pos x))
  (%!+) (!% f) = (%!) f

  public export
  (.fwd) : {0 c, d : AddCont} -> c =%+> d -> c.Shp -> d.Shp
  (.fwd) f = (ULens f).fwd

  public export
  (.bwd) : {0 c, d : AddCont} -> (f : c =%+> d) ->
    (x : c.Shp) -> d.Pos (f.fwd x) -> c.Pos x
  (.bwd) f = (ULens f).bwd

  public export
  compDepLens : {0 c, d, e : AddCont} -> c =%+> d -> d =%+> e -> c =%+> e
  compDepLens f g = (!%) (compDepLens (ULens f) (ULens g))

  public export
  (%+>>) : {0 c, d, e : AddCont} -> c =%+> d -> d =%+> e -> c =%+> e
  (%+>>) = compDepLens

  public export
  id : {0 c : AddCont} -> c =%+> c
  id = (!%) id

  ||| Pairing of all possible combinations of inputs to a particular lens
  |||
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             ├──►
  |||                  │    lens     │
  |||                  │             │
  |||               ◄──┤             ├◄── d.Pos (lens.fwd x)
  |||                  └─────────────┘
  public export
  lensInputs : {c, d : AddCont} -> c =%+> d -> AddCont
  lensInputs lens = MkAddCont
    (lensInputs (ULens lens))
    {mon=(MkI $ \s => UMon d (lens.fwd s))}


namespace DependentCharts
  ||| Forward-forward morphism between additive containers
  ||| It should also encode the constraint that the second component of the
  ||| chart is a commutative monoid homomorphism. That is currently left out
  |||
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             ├──► (y : c.Shp)
  |||                  │    lens     │
  |||     c.Pos x   ──►┤             ├──► d.Pos y
  |||                  └─────────────┘
  public export
  record (=&+>) (c, d : AddCont) where
    constructor (!&) -- at the moment, we do not plan to use this constructor
    UChart : UC c =&> UC d

  public export
  (!&+) : {0 c, d : AddCont} -> c =&+> d -> (x : c.Shp) -> (y : d.Shp ** (c.Pos x -> d.Pos y))
  (!&+) (!& f) = (&!) f

  public export
  (&!) : {0 c, d : AddCont} -> c =&+> d -> (x : c.Shp) -> (y : d.Shp ** (c.Pos x -> d.Pos y))
  (&!) (!& f) = (&!) f

  public export
  (.fwd) : {0 c, d : AddCont} -> c =&+> d -> c.Shp -> d.Shp
  (.fwd) f = (UChart f).fwd

  public export
  (.bwd) : {0 c, d : AddCont} -> (f : c =&+> d) ->
    (x : c.Shp) -> c.Pos x -> d.Pos (f.fwd x)
  (.bwd) f = (UChart f).bwd

  public export
  compDepChart : {0 c, d, e : AddCont} -> c =&+> d -> d =&+> e -> c =&+> e
  compDepChart f g = (!&) (compDepChart (UChart f) (UChart g))

  public export
  (&>>) : {0 c, d, e : AddCont} -> c =&+> d -> d =&+> e -> c =&+> e
  (&>>) = compDepChart

  public export
  id : {0 c : AddCont} -> c =&+> c
  id = (!&) id

  ||| Unlike with lenses, the set of all inputs to a chart is simpler, it is 
  ||| just the input container.
  public export
  chartInputs : {c, d : AddCont} -> (0 f : c =&+> d) -> AddCont
  chartInputs _ = c