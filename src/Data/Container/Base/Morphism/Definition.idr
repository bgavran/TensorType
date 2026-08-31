module Data.Container.Base.Morphism.Definition

import Data.DPair

import Data.Container.Base.Object.Definition
import Misc

{-------------------------------------------------------------------------------
Two different types of morphisms:
* Dependent lenses: forward-backward container morphisms
* Dependent charts: forward-forward container morphisms

There are also cartesian container morphisms, which are both lenses and charts: 
their map on positions is an isomorphism
-------------------------------------------------------------------------------}

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
  ||| Dependent lenses
  ||| Forward-backward container morphisms
  |||
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             ├──► (y : c.Shp)
  |||                  │    lens     │
  |||     c.Pos x   ◄──┤             ├◄── d.Pos y
  |||                  └─────────────┘
  public export
  data (=%>) : (c, d : Cont) -> Type where
    (!%) : ((x : c.Shp) -> (y : d.Shp ** (d.Pos y -> c.Pos x))) -> c =%> d

  %name (=%>) f, g, h

  public export
  (%!) : c =%> d -> (x : c.Shp) -> (y : d.Shp ** (d.Pos y -> c.Pos x))
  (%!) (!% f) = f

  ||| See fwd of `DChart`
  public export
  (.fwd) : c =%> d -> c.Shp -> d.Shp
  (.fwd) (!% f) x = (f x).fst

  public export
  (.bwd) : (f : c =%> d) -> (x : c.Shp) -> d.Pos (f.fwd x) -> c.Pos x
  (.bwd) (!% f) x y' = (f x).snd y'

  ||| Composition of dependent lenses.
  public export
  compDepLens : c =%> d -> d =%> e -> c =%> e
  compDepLens f g = !% \x => let (y ** ky) = (%!) f x
                                 (z ** kz) = (%!) g y
                             in (z ** ky . kz)

  public export
  (%>>) : c =%> d -> d =%> e -> c =%> e
  (%>>) = compDepLens

  public export
  id : c =%> c
  id = !% \x => (x ** id)

  ||| Pairing of all possible combinations of inputs to a particular lens
  |||
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             ├──►
  |||                  │    lens     │
  |||               ◄──┤             ├◄── d.Pos (lens.fwd x)
  |||                  └─────────────┘
  public export
  lensInputs : {c, d : Cont} -> c =%> d -> Cont
  lensInputs lens = (x : c.Shp) !> d.Pos (lens.fwd x)


namespace DependentCharts
  ||| Dependent charts
  ||| Forward-forward container morphisms
  |||
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             ├──► (y : c.Shp)
  |||                  │    chart    │
  |||     c.Pos x   ──►┤             ├──► d.Pos y
  |||                  └─────────────┘
  public export
  data (=&>) : (c, d : Cont) -> Type where
    (!&) : ((x : c.Shp) -> (y : d.Shp ** (c.Pos x -> d.Pos y))) -> c =&> d

  %name (=&>) f, g, h

  public export
  (&!) : c =&> d -> (x : c.Shp) -> (y : d.Shp ** (c.Pos x -> d.Pos y))
  (&!) (!& f) x = f x

  ||| For some reason, this has to be a lambda for
  ||| `Autodiff.Core.Forward.MkDiff` to reduce correctly
  public export
  (.fwd) : c =&> d -> c.Shp -> d.Shp
  (.fwd) f = \x => ((&! f) x).fst

  public export
  (.bwd) : (f : c =&> d) -> (x : c.Shp) -> c.Pos x -> d.Pos (f.fwd x)
  (.bwd) f = \x => ((&! f) x).snd

  public export
  compDepChart : c =&> d -> d =&> e -> c =&> e
  compDepChart f g = !& \x => let (y ** ky) = (&!) f x
                                  (z ** kz) = (&!) g y
                              in (z ** kz . ky)

  public export
  (&>>) : c =&> d -> d =&> e -> c =&> e
  (&>>) = compDepChart

  public export
  id : c =&> c
  id = !& \x => (x ** id)


namespace Cartesian
  ||| Cartesian morphisms
  ||| Morphisms whose function on positions is an isomorphism
  ||| There is a sense in which these are "linear" morphisms of containers
  public export
  data (=:>) : (c, d : Cont) -> Type where
    (!:) : ((x : c.Shp) -> (y : d.Shp ** Iso (c.Pos x) (d.Pos y)))
      -> c =:> d

  %name (=:>) f, g, h

  public export
  (:!) : c =:> d -> ((x : c.Shp) -> (y : d.Shp ** Iso (c.Pos x) (d.Pos y)))
  (:!) (!: f) x = f x

  ||| Every cartesian morphism is a dependent lens
  public export
  (:%) : c =:> d -> c =%> d
  (:%) (!: f) = !% \x => let (y ** ky) = f x in (y ** backward ky)

  ||| Every cartesian morphism is a dependent chart
  public export
  (:&) : c =:> d -> c =&> d
  (:&) (!: f) = !& \x => let (y ** ky) = f x in (y ** forward ky)

public export
reduceVia : {0 c, d : Cont} ->
  ((s' : d.Shp) -> d.Pos s') -> -- given a solution to a problem
  c =%> d -> -- and a way of transforming another problem into it
  ((s : c.Shp) -> c.Pos s) -- we obtain a solution of the other problem
reduceVia f l s = l.bwd s (f (l.fwd s))

||| Similar to the extension of a container. Following some ideas in
||| Diegetic open games (https://arxiv.org/abs/2206.12338)
||| Is this recovered via container composition when `r` is a some container?
||| Probably something like `c >@ (Const Unit r) = valuedIn c r`?
public export
valuedIn : Cont -> Type -> Cont
valuedIn c r = (s : c.Shp) !> (c.Pos s -> r)

||| Chart -> DLens
||| Tangent bundle to Contanget bundle, effectively
public export
chartToLens : {c1, c2 : Cont} -> {r : Type}
  ->  c1 =&> c2
  ->  (c1 `valuedIn` r) =%> (c2 `valuedIn` r)
chartToLens f = !% \x => let (y ** ky) = (&!) f x
                         in (y ** (. ky))