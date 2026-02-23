module Data.Container.Additive.Morphism.Definition

import Data.Container.Base
import Data.ComMonoid
import Data.Container.Additive.Object.Definition

export infixr 1 =%> -- (closed) dependent lens
export infixr 1 =&> -- (closed) dependent chart
export infixr 1 =:> -- (closed) cartesian morphism
export prefix 0 !% -- constructor the (closed) dependent lens
export prefix 0 !& -- constructor the (closed) dependent chart
export prefix 0 !: -- constructor the (closed) cartesian morphism
public export prefix 0 %!
public export prefix 0 &!
public export prefix 0 :!
public export prefix 0 !%+ -- constructor the addittive closed dlens
export infixl 5 %>> -- composition of dependent lenses
export infixl 5 &>> -- composition of dependent charts
export infixl 5 %%+>> -- composition of monadic dependent lenses

public export prefix 0 !%%+
public export prefix 0 %%!+

namespace DependentLenses
  ||| Forward-backward morphism between additive containers
  ||| It should also encode the constraint that the backward part is a comonoid
  ||| homomorphism. That is currently left out.
  public export
  record (=%>) (c1, c2 : AddCont) where
    constructor (!%)
    ULens : UC c1 =%> UC c2

  ||| Analogous to `!%` for ordinary containers, allows us to construct the 
  ||| lens directly
  public export
  (!%+) : {0 c1, c2 : AddCont} ->
    ((x : c1.Shp) -> (y : c2.Shp ** (c2.Pos y -> c1.Pos x))) ->
    c1 =%> c2
  (!%+) f = (!%) ((!%) f)

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

  ||| Pairing of all possible combinations of inputs to a particular lens
  |||
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             ├──►
  |||                  │    lens     │
  |||                  │             │
  |||               ◄──┤             ├◄── d.Pos (lens.fwd x)
  |||                  └─────────────┘
  public export
  lensInputs : {c, d : AddCont} -> c =%> d -> AddCont
  lensInputs lens = MkAddCont
    (lensInputs (ULens lens))
    {mon=(MkI @{\s => ?lensInputsMon_rhs})}


namespace DependentCharts
  ||| Forward-forward morphism between additive containers
  ||| It should also encode the constraint that the second component of the
  ||| chart is a commutative monoid homomorphism. That is currently left out
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

  ||| Unlike with lenses, the set of all inputs to a chart is simpler, it is 
  ||| just the input container.
  public export
  chartInputs : {c, d : AddCont} -> (0 f : c =&> d) -> AddCont
  chartInputs _ = c


namespace MLens
  parameters {m : Type -> Type} {auto mm : Monad m} 
    ||| Similar to a monadic dependent lens, but not quite
    public export
    data MAddLens : (c1, c2 : AddCont) -> Type where
        (!%%+) : {0 c1, c2 : AddCont} ->
          ((x : c1.Shp) -> m (y : c2.Shp ** (c2.Pos y -> c1.Pos x))) ->
          MAddLens c1 c2
  
    public export
    (%%!+) : MAddLens c1 c2 -> (x : c1.Shp) ->
      m (y : c2.Shp ** (c2.Pos y -> c1.Pos x))
    (%%!+) (!%%+ f) x = f x

    public export
    (.fwd) : MAddLens c1 c2 -> c1.Shp -> m c2.Shp
    (.fwd) f = \x => fst <$> (%%!+ f) x

    public export
    compMAddLens : MAddLens a b -> MAddLens b c -> MAddLens a c
    compMAddLens (!%%+ f) (!%%+ g) = !%%+ \x => do
      (b ** kb) <- f x
      (c ** kc) <- g b
      pure (c ** kb . kc)

    public export
    (%%+>>) : MAddLens a b -> MAddLens b c -> MAddLens a c
    (%%+>>) = compMAddLens

    public export
    id : MAddLens c c
    id = !%%+ \x => pure (x ** id)

    public export
    liftAddDLens : (c1 =%> c2) -> MAddLens c1 c2
    liftAddDLens f = !%%+ \x => pure (f.fwd x ** f.bwd x)

    public export
    UMLens : MAddLens c1 c2 -> MLens {m=m} (UC c1) (UC c2)
    UMLens (!%%+ f) = !%% f
