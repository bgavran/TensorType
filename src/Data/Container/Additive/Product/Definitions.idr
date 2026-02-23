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
import Control.Monad.Distribution

import Misc

%hide Data.Vect.Quantifiers.All.index

public export infixr 0 ><
public export infixr 0 >+<


{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
Compared to ordinary containers, for additive containers:
* Categorical product cannot be defined as it is in ordinary containers
* Hancock tensor product becomes the categorical product
* Coproduct is still coproduct

* The identity functor from Cont -> AddCont with product on domain and hancock product on codomain is not monoidal in any sense: it is not strict, strong, lax nor oplax

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

namespace List
  public export
  data AllPos : {cs : List AddCont} -> All (.Shp) cs -> Type where
    Nil : AllPos []
    (::) : c.Pos s -> AllPos ss -> AllPos {cs=(c::cs)} (s :: ss)

  public export
  listAddContMonPlus : {cs : List AddCont} ->
    (s : All (.Shp) cs) ->
    AllPos s -> AllPos s -> AllPos s
  listAddContMonPlus [] [] [] = []
  listAddContMonPlus {cs=c::_} (s :: ss) (l :: ls) (r :: rs)
    = plus (UMon c s) l r :: listAddContMonPlus ss ls rs

  public export
  listAddContMonNeutral : {cs : List AddCont} ->
    (s : All (.Shp) cs) ->
    AllPos s
  listAddContMonNeutral {cs = []} [] = []
  listAddContMonNeutral {cs = (c :: cs)} (s :: ss)
    = neutral (UMon c s) :: listAddContMonNeutral {cs} ss
  
  public export
  ListAddContMon : {cs : List AddCont} ->
    (s : All (.Shp) cs) -> ComMonoid (AllPos s)
  ListAddContMon s = MkComMonoid (listAddContMonPlus s) (listAddContMonNeutral s)

  public export
  ListAddCont : List AddCont -> AddCont
  ListAddCont cs = MkAddCont
    ((xs : All (.Shp) cs) !> AllPos xs)
    @{MkI @{ListAddContMon}}


  -- implicit variables because of name clash
  public export
  head : {0 c : AddCont} -> {0 s : c.Shp} ->
    AllPos {cs=c::cs} (s :: ss) -> c.Pos s
  head (a :: as) = a
  
  public export
  tail : {0 c : AddCont} -> {0 s : c.Shp} ->
    AllPos {cs=c::cs} (s :: ss) -> AllPos {cs=cs} ss
  tail (a :: as) = as



namespace Vect
  namespace All
    ||| Analogue of AllPos for Vects
    public export
    data AllPos : {cs : Vect n AddCont} -> All (.Shp) cs -> Type where
      Nil : AllPos []
      (::) : {0 cs : Vect k AddCont} -> {0 ss : All (.Shp) cs} ->
        c.Pos s -> AllPos {cs=cs} ss -> AllPos {cs=(c::cs)} (s :: ss)
  
  namespace Any
    public export
    data AnyPos : {cs : Vect n AddCont} -> Any (.Shp) cs -> Type where
      Here : {0 c : AddCont} -> {0 s : c.Shp} ->
        c.Pos s -> AnyPos (Here {x=c} {xs=cs} s)
      There : {0 cs : Vect m AddCont} -> {0 ss : Any (.Shp) cs} ->
        AnyPos ss -> AnyPos (There {x=c} ss)

  public export
  vectAddContMonPlus : {n : Nat} -> {cs : Vect n AddCont} ->
    (s : All (.Shp) cs) ->
    AllPos s -> AllPos s -> AllPos s
  vectAddContMonPlus [] [] [] = []
  vectAddContMonPlus {cs=c::_} (s :: ss) (l :: ls) (r :: rs)
    = plus (UMon c s) l r :: vectAddContMonPlus ss ls rs

  public export
  vectAddContMonNeutral : {n : Nat} -> {cs : Vect n AddCont} ->
    (s : All (.Shp) cs) ->
    AllPos s
  vectAddContMonNeutral {cs = []} [] = []
  vectAddContMonNeutral {cs = (c :: cs)} (s :: ss)
    = neutral (UMon c s) :: vectAddContMonNeutral {cs} ss

  public export
  VectAddContMon : {n : Nat} -> {cs : Vect n AddCont} ->
    (s : All (.Shp) cs) -> ComMonoid (AllPos s)
  VectAddContMon s = MkComMonoid (vectAddContMonPlus s) (vectAddContMonNeutral s)

  public export
  AllAll : {n : Nat} -> Vect n AddCont -> AddCont
  AllAll cs = MkAddCont
    ((xs : All (.Shp) cs) !> AllPos xs)
    @{MkI @{VectAddContMon}}

  public export
  VectAddCont : {n : Nat} -> Vect n AddCont -> AddCont
  VectAddCont cs = AllAll cs


  public export
  AnyComMonoidNeutral : {cs : Vect n AddCont} ->
    (s : Any (.Shp) cs) -> AnyPos s
  AnyComMonoidNeutral {cs = (c :: _)} (Here s) = Here (c.Zero s)
  AnyComMonoidNeutral {cs = (_ :: _)} (There ss) = There (AnyComMonoidNeutral ss)

  public export
  AnyComMonoidPlus : {cs : Vect n AddCont} ->
    (s : Any (.Shp) cs) -> AnyPos s -> AnyPos s -> AnyPos s
  AnyComMonoidPlus {cs = (c :: _)} (Here s) (Here l) (Here r)
    = Here (c.Plus s l r)
  AnyComMonoidPlus {cs = (c :: cs)} (There ss) (There l) (There r)
    = There (AnyComMonoidPlus ss l r)

  public export
  AnyComMonoid : {cs : Vect n AddCont} ->
    (s : Any (.Shp) cs) -> ComMonoid (AnyPos s)
  AnyComMonoid s = MkComMonoid (AnyComMonoidPlus s) (AnyComMonoidNeutral s)

  public export
  Any : {n : Nat} -> Vect n AddCont -> AddCont
  Any cs = MkAddCont
    ((xs : Any (.Shp) cs) !> AnyPos xs)
    @{MkI @{AnyComMonoid}}

  public export
  UniversalMapAny : {n : Nat} -> {cs : Vect n AddCont} ->
    ((i : Fin n) -> (index i cs) =%> d) ->
    Any cs =%> d
  UniversalMapAny {cs = []} f = !%+ \c => ?shouldBeUninhabited
  UniversalMapAny {cs = (c :: cs)} f = !%+ \x => ?asdf
    


  public export
  head : {0 c : AddCont} -> {0 s : c.Shp} -> {0 cs : Vect (S k) AddCont} ->
    {0 ss : All (.Shp) cs} ->
    AllPos {cs=(c::cs)} (s :: ss) -> c.Pos s
  head (a :: as) = a

  public export
  tail : {0 c : AddCont} -> {0 s : c.Shp} -> {0 cs : Vect (S k) AddCont} ->
    {0 ss : All (.Shp) cs} ->
    AllPos {cs=(c::cs)} (s :: ss) -> AllPos {cs=cs} ss
  tail (a :: as) = as




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


||| Coproduct
public export
(>+<) : AddCont -> AddCont -> AddCont
c >+< d = MkAddCont (UC c >+< UC d)
  @{MkI @{\case
    Left cs => MkComMonoid (plus (UMon c cs)) (neutral (UMon c cs))
    Right ds => MkComMonoid (plus (UMon d ds)) (neutral (UMon d ds))}}


||| Composition
public export
(>@) : AddCont -> AddCont -> AddCont
c >@ d = MkAddCont (UC c >@ UC d)
  @{MkI @{\(dShp <| dPosToCShp) => ?fhhhh}} -- MkComMonoid
    -- (\l, r => (d.Plus dShp (fst l) (fst r) ** c.Plus ?xxx ?ccccc ?ddddd))
    -- (d.Zero dShp ** c.Zero $ dPosToCShp (d .Zero dShp))}} 



||| Given an additive container `c`, this produces a monoid on the total space
||| `(s : c.Shp ** c.Pos s)`.
||| The idea is that `c` only gives us a monoid structure on `c.Pos s` for each
||| shape `s`. But we can't add `(s1 ** p1)` and `(s2 ** p2)` when `s1 ≠ s2` as
||| positions live in different types.
|||
||| The solution is to represent elements as lists of shape-position pairs, and
||| add them using concatenation
|||
||| (Infinitary) coproduct of monoids
||| It is a subtype of the Pi type with finite support
||| This means that in the finite case it coincides with the monoid product
||| But in the infinite case we need to be explicit about the support:
||| which elements of the domain map to nonzero, and what are their values?
||| This ends up being equivalent to the graph of the function of all the 
||| nonzero elements, i.e. a list of input-output pairs such that
||| 1) Order doesn't matter (quotiented out by permutations)
||| 2) Pairs where output is zero can be dropped, i.e. `(s, 0) : xs = xs`
||| 3) Same-shape entires add: `(s, p1) : (s, p2)` = (s, p1 + p2)`
||| 
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


namespace ConvexCombProduct
  ||| Container whose shapes are distributions, positions their gradients
  ||| Both are represented as logits
  ||| If we were treating this as non-logit distributions then we'd have a 
  ||| one less dimension: both for the simplex in the forward pass and the
  ||| gradients in the backwards one
  ||| That is, the effective dimension of this space is n-1 (we can add a 
  ||| constant to all logits without changing the answer), and there's a
  ||| direction in the gradient logit space that does not affect output
  public export
  Simplex : Nat -> AddCont
  Simplex n = MkAddCont $ (_ : Dist n) !> (Vect n Double)

  ||| A container where all branches must be prepared, but responses can come
  ||| from any subset of branches (accumulated as a list).
  |||
  ||| Shape: Product of all branch shapes (all branches must be ready)
  ||| Position: Free monoid on the coproduct of positions (formal sum of tagged responses)
  public export
  PreparedChoice : {n : Nat} -> Vect n AddCont -> AddCont
  PreparedChoice xs = MkAddCont
    ((shapes : All (.Shp) xs) !>
      List ((i : Fin n ** (index i xs).Pos (index i shapes))))
    @{MkI @{\_ => MkComMonoid (++) []}}
  
  ||| Convex combination of additive containers.
  |||
  ||| Shape: all shapes from each branch, plus a distribution over branches.
  ||| Position: a list of tagged positions (coproduct of monoids structure).
  |||
  ||| The list represents a formal sum of branch-tagged gradients:
  ||| - Singleton [(i ** p)] means gradient p came from branch i
  ||| - Multiple entries accumulate (same-index entries add their positions)
  ||| - Empty list is the neutral element
  ||| The monoid on List for tagged positions: concatenation with empty list neutral
  public export
  ConvexComb : {n : Nat} -> Vect n AddCont -> AddCont
  ConvexComb xs = Simplex n >< PreparedChoice xs