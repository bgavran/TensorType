module Data.Container.Base.Morphism.Definition

import Data.DPair

import Data.Container.Base.Object.Definition
import Misc

{-------------------------------------------------------------------------------
Two different types of morphisms:
dependent lenses, and dependent charts
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
  public export
  data (=%>) : (c1, c2 : Cont) -> Type where
    (!%) : ((x : c1.Shp) -> (y : c2.Shp ** (c2.Pos y -> c1.Pos x))) -> c1 =%> c2

  %name (=%>) f, g, h

  public export
  (%!) : c1 =%> c2 -> (x : c1.Shp) -> (y : c2.Shp ** (c2.Pos y -> c1.Pos x))
  (%!) (!% f) x = f x

  ||| See fwd of `DChart`
  public export
  (.fwd) : c1 =%> c2 -> c1.Shp -> c2.Shp
  (.fwd) f = \y => ((%! f) y).fst

  public export
  (.bwd) : (f : c1 =%> c2) -> (x : c1.Shp) -> c2.Pos (f.fwd x) -> c1.Pos x
  (.bwd) f = \x => ((%! f) x).snd

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

  ||| Pairing of all possible combinations of inputs to a particular lens
  |||
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             ├──►
  |||                  │    lens     │
  |||                  │             │
  |||               ◄──┤             ├◄── d.Pos (lens.fwd x)
  |||                  └─────────────┘
  public export
  lensInputs : {c, d : Cont} -> c =%> d -> Cont
  lensInputs lens = (x : c.Shp) !> d.Pos (lens.fwd x)


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

  ||| For some reason, this has to be a lambda for
  ||| `Autodiff.Core.Forward.MkDiff` to reduce correctly
  public export
  (.fwd) : c1 =&> c2 -> c1.Shp -> c2.Shp
  (.fwd) f = \x => ((&! f) x).fst

  public export
  (.bwd) : (f : c1 =&> c2) -> (x : c1.Shp) -> c1.Pos x -> c2.Pos (f.fwd x)
  (.bwd) f = \x => ((&! f) x).snd

  public export
  compDepChart : a =&> b -> b =&> c -> a =&> c
  compDepChart f g = !& \x => let (b ** kb) = (&! f) x
                                  (c ** kc) = (&! g) b
                              in (c ** kc . kb)

  public export
  (&>>) : a =&> b -> b =&> c -> a =&> c
  (&>>) = compDepChart

  public export
  id : a =&> a
  id = !& \x => (x ** id)


namespace Cartesian
  ||| Cartesian morphisms
  ||| Morphisms whose function on positions is an isomorphism
  ||| There is a sense in which these are "linear" morphisms of containers
  public export
  data (=:>) : (c1, c2 : Cont) -> Type where
    (!:) : ((x : c1.Shp) -> (y : c2.Shp ** Iso (c1.Pos x) (c2.Pos y)))
      -> c1 =:> c2

  %name (=:>) f, g, h

  public export
  (:!) : c1 =:> c2 -> ((x : c1.Shp) -> (y : c2.Shp ** Iso (c1.Pos x) (c2.Pos y)))
  (:!) (!: f) x = f x

  ||| Every cartesian morphism is a dependent lens
  public export
  (:%) : c1 =:> c2 -> c1 =%> c2
  (:%) (!: f) = !% \x => let (y ** ky) = f x in (y ** backward ky)

  ||| Every cartesian morphism is a dependent chart
  public export
  (:&) : c1 =:> c2 -> c1 =&> c2
  (:&) (!: f) = !& \x => let (y ** ky) = f x in (y ** forward ky)

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
chartToLens f = !% \x => let (y ** ky) = (((&!) f) x)
                         in (y ** (. ky))
