module Data.Container.Additive.Product.Definitions

import Data.Container.Base
import Data.ComMonoid
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Morphism.Definition
import Data.Container.Additive.Extension.Definition
import Data.Container.Additive.Object.Instances


public export infixr 0 ><
public export infixr 0 >+<

namespace HancockTensorProduct
  ||| Hancock tensor product
  public export
  (><) : AddCont -> AddCont -> AddCont
  c >< d = MkAddCont (UC c >< UC d)
    @{MkI @{\sh => MkComMonoid (\l, r =>
      (c.Plus (fst sh) (fst l) (fst r), d.Plus (snd sh) (snd l) (snd r)))
      (c.Zero (fst sh), d.Zero (snd sh))}}

  namespace Morphism
    public export
    (><) : {0 c1, d1, c2, d2 : AddCont} ->
      (c1 =%> d1) -> (c2 =%> d2) -> (c1 >< c2) =%> (d1 >< d2)
    (><) f g = !%+ \(c, d) => ((f.fwd c, g.fwd d) **
      \(c', d') => (f.bwd c c', g.bwd d d'))

  ||| Dependent Hancock (tensor) product of additive containers.
  ||| This is the analogue of DPair for containers:
  ||| Given a container `pc` and a family `qc : pc.Shp -> AddCont`,
  ||| form the container whose shapes are dependent pairs of shapes
  ||| and positions are pairs of positions.
  public export
  DepHancockProduct : (pc : AddCont) -> (qc : pc.Shp -> AddCont) -> AddCont
  DepHancockProduct pc qc = MkAddCont
    (DepHancockProduct (UC pc) (UC . qc))
    @{MkI @{\(ps ** qs) => MkComMonoid
      (\(pcPos1, qcPos1), (pcPos2, qcPos2) =>
        (plus (UMon pc ps) pcPos1 pcPos2, plus (UMon (qc ps) qs) qcPos1 qcPos2))
      (neutral (UMon pc ps), neutral (UMon (qc ps) qs))}}


||| Coproduct
public export
(>+<) : AddCont -> AddCont -> AddCont
c >+< d = MkAddCont (UC c >+< UC d)
  @{MkI @{\case
    Left cs => MkComMonoid (plus (UMon c cs)) (neutral (UMon c cs))
    Right ds => MkComMonoid (plus (UMon d ds)) (neutral (UMon d ds))}}


||| Composition
(>@) : AddCont -> AddCont -> AddCont
c @> d = MkAddCont (UC c @> UC d)
  @{MkI @{\(dShp <| dPosToCShp) => MkComMonoid
    (\l, r => (d.Plus dShp (fst l) (fst r) ** c.Plus ?xxx ?ccccc ?ddddd))
    (d.Zero dShp ** c.Zero $ dPosToCShp (d .Zero dShp))}} 

||| (Infinitary) coproduct of monoids
||| It is a subtype of the Pi type with finite support
||| This means that in the finite case it coincides with the monoid product
||| But in the infinite case we need to be explicit about the support:
||| which elements of the domain map to nonzero, and what are their values?
||| This ends up being equivalent to the graph of the function of all the 
||| nonzero elements, i.e. a list of input-output pairs such that
||| 1) order of the list does not matter (quotiented out by permutations)
||| 2) IO pairs where the output is zero is same as not having them, i.e.
|||    `(i, 0) : xs = xs`
||| 3) input duplicates add the outputs, i.e if the same input `i` appears twice
|||    then  `(i, xi) : (i, xj) : xs = (i, xi + xj) : xs`
||| All maps out of this type have to satisfy these constraints
public export
CoprodMon : AddCont -> ComMonoid
CoprodMon c = (List (Path c) ** MkComMonoid (++) [])


namespace MonoidalClosure
  ||| Internal hom in the category of additive lenses
  ||| Using CoprodMon makes this more elegant, but requires making Additive
  ||| instances for `=%>`, `lensInputs` and a few other things
  ||| Can't be written directly in terms of `InternalLens`
  public export
  InternalLensAdditive : AddCont -> AddCont -> AddCont
  InternalLensAdditive c d = MkAddCont
    ((l : c =%> d) !> List (Path (lensInputs l)))
    @{MkI @{\_ => MkComMonoid (++) []}}

  public export
  curry : {c : AddCont} -> (c >< d) =%> e -> c =%> (InternalLensAdditive d e)
  curry f = !%+ \x => (!%+ \y => (f.fwd (x, y) ** snd . f.bwd (x, y)) **
    \l => foldr (\(y ** b') => c.Plus x (fst (f.bwd (x, y) b'))) (c.Zero x) l)

  public export
  uncurry : {c : AddCont} -> c =%> (InternalLensAdditive d e) -> (c >< d) =%> e
  uncurry f = !%+ \(x, y) => ((f.fwd x).fwd y **
    \e' => (f.bwd x [(y ** e')], (f.fwd x).bwd y e'))


{- is waiting for merge of sampling into main
public export
ProbContMonNeutral : {cs : Vect n AddCont} -> (d : Dist n) ->
  (ss : All Shp cs) ->
  AllPos ss
ProbContMonNeutral {cs = []} (MkDist []) [] = []
ProbContMonNeutral {cs = (c :: cs)} (MkDist (p :: ps)) (x :: xs)
  = neutral (UMon c x) :: ProbContMonNeutral {cs=cs} (MkDist ps) xs


public export
ProbContMonPlus : {cs : Vect n AddCont} -> (d : Dist n) ->
  (ss : All Shp cs) ->
  AllPos ss ->
  AllPos ss ->
  AllPos ss
ProbContMonPlus {cs = []} (MkDist []) [] [] [] = []
ProbContMonPlus {cs = (c :: cs)} (MkDist (p :: ps)) (s :: ss) (x :: xs) (y :: ys)
  = plus (UMon c s) x y :: ProbContMonPlus {cs=cs} (MkDist ps) ss xs ys

||| Convex combination of additive containers
public export
ConvexComb : {n : Nat} -> Vect n AddCont -> AddCont
ConvexComb xs = MkAddCont
   (((d, shapes) : (Dist n, All Shp xs)) !> AllPos shapes)
   @{MkI @{\(d, ss) => GoodBoi (ProbContMonPlus d ss) (ProbContMonNeutral d ss)}}
-}