module Data.Container.Additive.Product.Definitions

import Data.Vect
import Data.Vect.Quantifiers

import Data.Container.Base
import Data.ComMonoid
import Data.Num
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Morphism.Definition
import Data.Container.Additive.Extension.Definition
import Data.Container.Additive.Object.Instances

import Data.Container.Base.Quantifiers
import Data.Container.Additive.Quantifiers

import Control.Monad.Distribution

import Misc

%hide Data.Vect.Quantifiers.All.index

public export infixr 3 ><  -- Hancock tensor product
public export infixr 3 >*< -- categorical product
public export infixr 3 >+< -- coproduct
public export infixr 3 >@  -- composition
public export infixr 3 <%> 


{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
Compared to ordinary containers, for additive containers:
* Categorical product cannot be defined as it is in ordinary containers
* Hancock tensor product becomes the categorical product
* Coproduct is still coproduct

* The identity functor from Cont -> AddCont with product on domain and hancock product on codomain is not monoidal in any sense: it is not strict, strong, lax nor oplax

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| Hancock tensor product here becomes the categorical product
namespace Product
  public export
  (><) : AddCont -> AddCont -> AddCont
  c >< d = MkAddCont (UC c >< UC d)
    @{MkI @{\sh => MkComMonoid (\l, r =>
      (c.Plus (fst sh) (fst l) (fst r), d.Plus (snd sh) (snd l) (snd r)))
      (c.Zero (fst sh), d.Zero (snd sh))}}

  ||| Can also use the product operator
  public export
  (>*<) : AddCont -> AddCont -> AddCont
  (>*<) = (><)

  namespace List
    ||| N-ary version of hancock product
    public export
    AllAll : List AddCont -> AddCont
    AllAll xs = MkAddCont
      ((shapes : All (.Shp) xs) !> AllPos shapes)
      @{MkI @{allPosComMonoid}}

  namespace Vect
    ||| N-ary version of hancock product
    public export
    AllAll : Vect n AddCont -> AddCont
    AllAll xs = MkAddCont
      ((shapes : All (.Shp) xs) !> AllPos shapes)
      @{MkI @{allPosComMonoid}}

  namespace Morphism
    public export
    (><) : {0 c1, d1, c2, d2 : AddCont} ->
      (c1 =%> d1) -> (c2 =%> d2) -> (c1 >< c2) =%> (d1 >< d2)
    (><) f g = !%+ \(c, d) => ((f.fwd c, g.fwd d) **
      \(c', d') => (f.bwd c c', g.bwd d d'))

    namespace Monadic -- todo this needs to be cleaned up
      public export -- move monadic stuff into its own container directory
      (><) : {m : Type -> Type} -> Monad m =>
        {c1, d1, c2, d2 : AddCont} ->
        MAddLens {m=m} c1 d1 -> MAddLens {m=m} c2 d2 ->
          MAddLens {m=m} (c1 >< c2) (d1 >< d2)
      (><) f g = !%%+ \(c, d) => do
        (c' ** kb) <- (%%!+ f) c
        (d' ** kc) <- (%%!+ g) d
        pure ((c', d') ** \c'd' => (kb (fst c'd'), kc (snd c'd')))


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


||| Same as in ordinary containers
namespace Coproduct
  ||| Coproduct
  public export
  (>+<) : AddCont -> AddCont -> AddCont
  c >+< d = MkAddCont (UC c >+< UC d)
    @{MkI @{\case
      Left cs => MkComMonoid (plus (UMon c cs)) (neutral (UMon c cs))
      Right ds => MkComMonoid (plus (UMon d ds)) (neutral (UMon d ds))}}

  namespace Morphism
    public export
    (>+<) : {0 c1, d1, c2, d2 : AddCont} ->
      (c1 =%> d1) -> (c2 =%> d2) -> (c1 >+< c2) =%> (d1 >+< d2)
    (>+<) f g = !%+ \case
      (Left x) => (Left (f.fwd x) ** f.bwd x)
      (Right y) => (Right (g.fwd y) ** g.bwd y)

  namespace List
    ||| N-ary version of coproduct
    public export
    Any : List AddCont -> AddCont
    Any xs = MkAddCont
      ((shapes : Any (.Shp) xs) !> AnyShpPos shapes)
      @{MkI @{anyShpPosComMonoid}}

  namespace Vect
    ||| N-ary version of coproduct
    public export
    Any : Vect n AddCont -> AddCont
    Any xs = MkAddCont
      ((shapes : Any (.Shp) xs) !> AnyShpPos shapes)
      @{MkI @{anyShpPosComMonoid}}

||| With an ordinary container `c`, the Pi and Sigma type simple are the 
||| dependent function ((s : c.Shp) -> c.Pos s) and the dependent pair
||| ((s : c.Shp ** c.Pos s)) type: they rely on the (co)product in Set.
||| When the container is additive, the Pi and Sigma type rely on the 
||| (co)product in the category ComMon. Here Pi stays the same, but Sigma
||| ends up being a subtype of the Pi type, with finite support. This means that
||| in the finitary case, product and coproduct coincide.
|||
||| This is a complicated way of saying something simple:
||| The Sigma type, as inherited from Set, is not a monoid. This is because,
||| despite the fact that `c` gives us a monoid structure on every `c.Pos s`, we
||| still can't add `(s1 ** p1)` and `(s2 ** p2)` when `s1 ≠ s2` as
||| `p1` and `p2` have different types. At best, we could do it if `c.Shp` was
||| a monoid, and `c.Pos` was somehow laxly preserving the monoid structure.
|||
||| Instead, we need to use the Pi type representation: ((s : c.Shp) -> c.Pos s)
||| whose monoid structure is given pointwise. When `c.Shp` is an infinite type,
||| we need to ensure that the map above has finite support. Carrying this 
||| explicit support data together with the function is very fiddly
|||
||| It turns out that there is a pragmatic representation of the coproduct:
||| simply as a list of pairs `(s, p)` where `p : c.Pos s` such that:
||| 1) The list order doesn't matter (we need to quotient it out by permutation)
||| 2) Pairs where output is zero can be dropped, i.e. `(s, 0) : xs = xs`
||| 3) Same-shape entires add: `(s, p1) : (s, p2) : xs` = (s, p1 + p2) : xs`
||| That is, all maps that consume this type have to preserve these properties.
|||
||| It turns out that this works surprisingly well, and helps us be performant
||| especially when dealing with autodiff.
|||
||| In other words, any dependent pairs that want to be a monoid should ask
||| themselves if they're instead a list of input-output pairs.
public export
CoprodMon : AddCont -> ComMonoid
CoprodMon c = (List (Path c) ** listIsMonoid)

||| Bang operator: list on positions, always has a monoid structure
public export
(!!) : Cont -> AddCont
(!!) c = MkAddCont
  (List <!> c)
  @{MkI @{\_ => listIsMonoid}}

export prefix 9 !!

||| Similar to `Nap`
public export
pushDown : Type -> AddCont
pushDown b = !! (Nap b)


namespace Composition
  -- Cannot be defined naively!
  --public export
  --reindexAlongPlus : {c, d : AddCont} ->
  --  {s : c.Shp} ->
  --  (l, r : c.Pos s) ->
  --  (reindex : c.Pos s -> d.Shp) ->
  --  (l' : d.Pos (reindex l)) ->
  --  (r' : d.Pos (reindex r)) ->
  --  d.Pos (reindex (c.Plus s l r))
  --reindexAlongPlus l r reindex l' r' = ?reindexAlongPlus_rhs
  
  
  --||| Composition
  --public export
  --(>@) : AddCont -> AddCont -> AddCont
  --c >@ d = MkAddCont (UC c >@ UC d)
  --  @{MkI @{\(cShp <| cPosToDShp) => MkComMonoid
  --    (\(l ** l'), (r ** r') => (c.Plus cShp l r **
  --      reindexAlongPlus l r cPosToDShp l' r'))
  --    (c.Zero cShp ** d.Zero $ cPosToDShp $ c.Zero cShp)}}

  ||| Composition
  public export
  (>@) : AddCont -> AddCont -> AddCont
  c >@ d = !! (UC c >@ UC d)

  namespace Morphism
    ||| Action on morphisms
    public export
    (>@) : {0 c1, d1, c2, d2 : AddCont} ->
      (c1 =%> d1) -> (c2 =%> d2) -> (c1 >@ c2) =%> (d1 >@ d2)
    (>@) f g = !%+ \(s <| idx) => (f.fwd s <| g.fwd . idx . f.bwd s **
      map (\(dp ** dp2) => (f.bwd s dp ** g.bwd (idx (f.bwd s dp)) dp2)))


||| Coincides with cartesian closure
namespace MonoidalClosure
  ||| Internal hom in the category of additive lenses
  ||| Using CoprodMon makes this more elegant, but requires making Additive
  ||| instances for `=%>`, `lensInputs` and a few other things
  ||| Can't be written directly in terms of `InternalLens`
  public export
  InternalLensAdditive : AddCont -> AddCont -> AddCont
  InternalLensAdditive c d = MkAddCont
    ((l : c =%> d) !> List (Path (lensInputs l)))
    @{MkI @{\_ => listIsMonoid}}

  public export
  curry : {c : AddCont} -> (c >< d) =%> e -> c =%> (InternalLensAdditive d e)
  curry f = !%+ \x => (!%+ \y => (f.fwd (x, y) ** snd . f.bwd (x, y)) **
    \l => foldr (\(y ** b') => c.Plus x (fst (f.bwd (x, y) b'))) (c.Zero x) l)

  public export
  uncurry : {c : AddCont} -> c =%> (InternalLensAdditive d e) -> (c >< d) =%> e
  uncurry f = !%+ \(x, y) => ((f.fwd x).fwd y **
    \e' => (f.bwd x [(y ** e')], (f.fwd x).bwd y e'))

public export
allIsComonoidPlus : {c : AddCont} ->
  (s : List c.Shp) ->
  All c.Pos s -> All c.Pos s -> All c.Pos s
allIsComonoidPlus [] [] [] = []
allIsComonoidPlus (s :: ss) (l :: ls) (r :: rs) =
  c.Plus s l r :: allIsComonoidPlus ss ls rs

public export
allIsComonoidNeutral : {c : AddCont} ->
  (s : List c.Shp) ->
  All c.Pos s
allIsComonoidNeutral [] = []
allIsComonoidNeutral (s :: ss) = c.Zero s :: allIsComonoidNeutral ss

public export
allIsComonoid : {c : AddCont} ->
  (s : List c.Shp) ->
  ComMonoid (All c.Pos s)
allIsComonoid s = MkComMonoid (allIsComonoidPlus s) (allIsComonoidNeutral s)

-- Not exactly a product
public export
List : AddCont -> AddCont
List c = MkAddCont
  (List (UC c))
  @{MkI @{allIsComonoid}}


namespace Morphism
  public export
  bww : {0 c, d : AddCont} -> (f : c =%> d) -> (cs : List c.Shp) ->
    All (d.Pos) (f.fwd <$> cs) -> All (c .Pos) cs
  bww f [] [] = []
  bww f (c :: cs) (a :: as) = (f.bwd c a) :: bww f cs as

  public export
  List : {0 c, d : AddCont} -> (c =%> d) -> (List c) =%> (List d)
  List f = !%+ \cs => (f.fwd <$> cs ** bww f cs)

-- duoidal and distribute have been moved to Additive.Morphism.Instances

||| In general, we'll want to instantiate `f` with `IO`, and in that case
||| it'll never be the case that the set of positions is additive
||| Hence we just overload the operator here, and return an ordinary container
public export
(<!>) : (f : Type -> Type) -> AddCont -> Cont
(<!>) f c = (f <!> (UC c))

namespace Morphism
  public export
  (<!>) : {0 c, d : AddCont} -> (f : Type -> Type) -> Functor f =>
    (c =%> d) ->
    ((f <!> c) =%> (f <!> d))
  (<!>) f l = !% \x => (l.fwd x ** ((l.bwd x) <$>) )

  public export infixr 9 <!>


||| Must produce all shapes (branches), expects a response from any subset of
||| branches, accumulated as a list. I.e. we might get more than one response
||| in a particular branch. Represented as a list.
||| No additive structure on input containers is required, nor is there a way
||| to use it.
public export
PreparedChoice : {n : Nat} -> Vect n Cont -> AddCont
PreparedChoice xs = !! (AllAny xs)

namespace ConvexCombProduct
  ||| Container whose shapes are distributions, positions their gradients.
  ||| Both are represented as logits
  ||| If we were treating this as non-logit distributions then we'd have a 
  ||| one less dimension: both for the simplex in the forward pass and the
  ||| gradients in the backwards one
  ||| That is, the effective dimension of this space is n-1 (we can add a 
  ||| constant to all logits without changing the answer), and there's a
  ||| direction in the gradient logit space that does not affect output
  public export
  Simplex : Nat -> AddCont
  Simplex n = MkAddCont (Simplex n)
  
  ||| Convex combination of containers. Uses ordinary containers as input.
  |||
  ||| Shape: all shapes from each branch, plus a distribution over branches.
  ||| Position: a list of tagged positions (coproduct of monoids structure).
  |||
  ||| The list represents a formal sum of branch-tagged gradients:
  ||| - Singleton [(i ** p)] means gradient p came from branch i
  ||| - Multiple entries accumulate (same-index entries add their positions)
  ||| - Empty list is the neutral element
  public export
  ConvexComb : {n : Nat} -> Vect n Cont -> AddCont
  ConvexComb xs = Simplex n >< PreparedChoice xs


  namespace Additive
    public export
    ConvexComb : {n : Nat} -> (xs : Vect n AddCont) -> AddCont
    ConvexComb xs = ConvexComb (UC <$> xs)

--public export
--UniversalMapAny : {n : Nat} -> {cs : Vect n AddCont} ->
--  ((i : Fin n) -> (index i cs) =%> d) ->
--  Any cs =%> d
--UniversalMapAny {cs = []} f = !%+ \c => ?shouldBeUninhabited
--UniversalMapAny {cs = (c :: cs)} f = !%+ \x => ?asdf