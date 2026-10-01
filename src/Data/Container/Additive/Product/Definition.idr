module Data.Container.Additive.Product.Definition

import Data.Vect
import Data.Vect.Quantifiers

import Data.Container.Base
import Data.ComMonoid
import Data.Num
import Data.Container.Additive.Object.Definition
import Data.Container.Additive.Morphism.Definition
import Data.Container.Additive.Extension.Definition

import Data.Container.Base.Quantifiers
import Data.Container.Additive.Quantifiers


import Misc

%hide Data.Vect.Quantifiers.All.index

public export infixr 3 ><  -- Hancock tensor product
public export infixr 3 >*< -- categorical product
public export infixr 3 >+< -- coproduct
public export infixr 3 >+@  -- composition
public export infixr 3 >-+@ -- composition action
public export infixr 3 <%> 


{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
The category Cont of ordinary containers has four interesting monoidal 
products: categorical product, hancock tensor product, coproduct, and composition product.

The category AddCont can be understood in terms of the monoidal products of its 
underlying containers;
* Categorical product of ordinary containers does not make an additive container
 (positions do not form a monoid)
* Hancock tensor product is an additive container, and it becomes the categorical product
* Coproduct is an additive container, and stays the coproduct
* Composition product tricky, and becomes (left)-skew monoidal

Notably, the forgetful functor AddCont -> Cont with hancock product on domain and categorical product on codomain is not monoidal in any sense: it is not strict, strong, lax nor oplax.

TODO update this writeup in light of new finds

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| Categorical product of additive containers
||| Monoid with UnitCont
||| On underlying containers, this computes the hancock tensor product
namespace CategoricalProduct
  ||| Binary version of product
  public export
  (>*<) : AddCont -> AddCont -> AddCont
  c >*< d = MkAddCont (c.Shp, d.Shp)
    (\sh => ((c.PosSet (fst sh), d.PosSet (snd sh)) ** MkComMonoid
      (\l, r => (c.Plus (fst sh) (fst l) (fst r), d.Plus (snd sh) (snd l) (snd r)))
      (c.Zero (fst sh), d.Zero (snd sh))))

  namespace List
    ||| N-ary version of hancock product
    public export
    AllAll : List AddCont -> AddCont
    AllAll xs = MkAddCont
      (All (.Shp) xs)
      (\shapes => (AllPos shapes ** allPosComMonoid shapes))

  namespace Vect
    ||| N-ary version of hancock product
    public export
    AllAll : Vect n AddCont -> AddCont
    AllAll xs = MkAddCont
      (All (.Shp) xs)
      (\shapes => (AllPos shapes ** allPosComMonoid shapes))

  namespace Morphism
    public export
    (>*<) : c1 =%+> d1 ->
      c2 =%+> d2 ->
      c1 >*< c2 =%+> d1 >*< d2
    (>*<) f g = !%+ \(c, d) =>
      let (c1 ** fk) = (%!+) f c
          (d1 ** gk) = (%!+) g d
      in ((c1, d1) ** \(c', d') => (fk c', gk d'))

  ||| Dependent pair type for additive containers
  ||| Can be thought of as the dependent tensor product of containers
  ||| Given a container `s` and a family `p : s.Shp -> Cont`,
  ||| form the container whose shapes are dependent pairs of shapes
  ||| and positions are pairs of positions.
  public export
  DPair : (pc : AddCont) -> (qc : pc.Shp -> AddCont) -> AddCont
  DPair pc qc = MkAddCont
    (DPair pc.Shp (\ps => (qc ps).Shp))
    (\sh => ((pc.PosSet (fst sh), (qc (fst sh)).PosSet (snd sh)) ** MkComMonoid
      (\l, r => (plus (UMon pc (fst sh)) (fst l) (fst r),
                 plus (UMon (qc (fst sh)) (snd sh)) (snd l) (snd r)))
      (neutral (UMon pc (fst sh)), neutral (UMon (qc (fst sh)) (snd sh)))))


||| Non-categorical product of additive containers
||| Does not have an expression in terms of ordinary containers, because it uses
||| the tensor product of commutative monoids
||| Monoid with Scalar
namespace TensorProduct
  -- TODO
  -- (><) : AddCont -> AddCont -> AddCont
  -- c >< d = MkAddCont (UC c >< UC d)


||| Same as in ordinary containers
||| Monoid with Empty
||| Dependent pair and dependent function of a family of additive containers
||| indexed by a type
namespace Dependent
  ||| One index, with the content at that index
  public export
  AddContDPair : {a : Type} -> (a -> AddCont) -> AddCont
  AddContDPair f = MkAddCont
    (x : a ** (f x).Shp)
    (\sh => (f (fst sh)).Pos (snd sh))

  ||| Container of the fibrewise positions of a family at a section
  public export
  fibreCont : {a : Type} -> {f : a -> AddCont} ->
    ((x : a) -> (f x).Shp) -> AddCont
  fibreCont s = MkAddCont a (\x => (f x).Pos (s x))

  ||| Sections of a family, with cotangents the free commutative monoid on the
  ||| fibrewise positions, so a backward pass carries only the indices it was
  ||| asked about
  ||| TODO this is costate, thought as the internal hom
  public export
  Section : {a : Type} -> (a -> AddCont) -> AddCont
  Section f = MkAddCont
    ((x : a) -> (f x).Shp)
    (\s => (DPair (fibreCont s) ** bagIsMonoid))


namespace CategoricalCoproduct
  ||| Coproduct
  public export
  (>+<) : AddCont -> AddCont -> AddCont
  c >+< d = MkAddCont (Either c.Shp d.Shp)
    (\es => (either (\cs => c.PosSet cs) (\ds => d.PosSet ds) es ** eitherMon es))
    where
      eitherMon : (es : Either c.Shp d.Shp) ->
        ComMonoid (either (\cs => c.PosSet cs) (\ds => d.PosSet ds) es)
      eitherMon (Left cs) = UMon c cs
      eitherMon (Right ds) = UMon d ds

  namespace Morphism
    public export
    (>+<) : (c1 =%+> d1) -> (c2 =%+> d2) -> (c1 >+< c2) =%+> (d1 >+< d2)
    (>+<) f g = !%+ \case
      (Left x) => (Left (f.fwd x) ** f.bwd x)
      (Right y) => (Right (g.fwd y) ** g.bwd y)

  namespace Vect
    ||| N-ary coproduct of a finite family, given as an extension of `Vect n`
    public export
    Coproduct : {n : Nat} -> (branches : Vect' n AddCont) -> AddCont
    Coproduct branches = AddContDPair (index branches)

    ||| Show a coproduct's shape from a `Show` for every branch's shapes.
    ||| Search can't provide these for an abstract index, so a `Show` instance
    ||| for a particular coproduct is written at its use site
    export
    showCoproduct : {branches : Vect' n AddCont} ->
      ((i : Fin n) -> Show (index branches i).Shp) ->
      (Coproduct branches).Shp -> String
    showCoproduct sh (i ** x) = show @{sh i} x

  namespace List
    ||| N-ary version of coproduct
    public export
    Any : List AddCont -> AddCont
    Any xs = MkAddCont
      (Any (.Shp) xs)
      (\shapes => (AnyShpPos shapes ** anyShpPosComMonoid shapes))

  namespace Vect
    ||| N-ary version of coproduct
    public export
    Any : Vect n AddCont -> AddCont
    Any xs = MkAddCont
      (Any (.Shp) xs)
      (\shapes => (AnyShpPos shapes ** anyShpPosComMonoid shapes))


-- Is All really a ComMonoid for List?
namespace ListAllComMonoid
  public export
  allIsComMonoidPlus : {c : AddCont} ->
    (s : List c.Shp) ->
    All c.PosSet s -> All c.PosSet s -> All c.PosSet s
  allIsComMonoidPlus [] [] [] = []
  allIsComMonoidPlus (s :: ss) (l :: ls) (r :: rs) =
    c.Plus s l r :: allIsComMonoidPlus ss ls rs
  
  public export
  allIsComMonoidNeutral : {c : AddCont} ->
    (s : List c.Shp) ->
    All c.PosSet s
  allIsComMonoidNeutral [] = []
  allIsComMonoidNeutral (s :: ss) = c.Zero s :: allIsComMonoidNeutral ss
  
  public export
  allIsComMonoid : {c : AddCont} ->
    (s : List c.Shp) ->
    ComMonoid (All c.PosSet s)
  allIsComMonoid s = MkComMonoid (allIsComMonoidPlus s) (allIsComMonoidNeutral s)

namespace BagAllComMonoid
  public export
  allIsComMonoidPlus : {c : AddCont} ->
    (s : Bag c.Shp) ->
    All c.PosSet s -> All c.PosSet s -> All c.PosSet s
  allIsComMonoidPlus (MkBag ul) l r = allIsComMonoidPlus ul l r
  
  public export
  allIsComMonoidNeutral : {c : AddCont} ->
    (s : Bag c.Shp) ->
    All c.PosSet s
  allIsComMonoidNeutral (MkBag ul) = allIsComMonoidNeutral ul

  public export
  allIsComMonoid : {c : AddCont} ->
    (s : Bag c.Shp) ->
    ComMonoid (All c.PosSet s)
  allIsComMonoid s = MkComMonoid
    (allIsComMonoidPlus s)
    (allIsComMonoidNeutral s)

namespace FunctorsOnAddCont
  public export
  BagAll : AddCont -> AddCont
  BagAll c = MkAddCont
    (Bag c.Shp)
    (\ss => (All c.PosSet ss ** allIsComMonoid ss))

  namespace Morphism
    -- public export
    -- bwww : (f : c =%+> d) -> (cs : Bag c.Shp) ->
    --   All (d.PosSet) (f.fwd <$> cs) -> All (c .PosSet) cs
    -- bwww f (MkBag []) [] = []
    -- bwww f (MkBag (c :: cs)) (a :: as) = (f.bwd c a) :: bwww  ?oo ?tt ?heiii 

    --   public export
    --   List : c =%+> d -> Bagw c =%+> Bag d
    --   List f = !%+ \cs => (f.fwd <$> cs ** bww f cs)

  public export
  ListAll : AddCont -> AddCont
  ListAll c = MkAddCont
    (List c.Shp)
    (\ss => (All c.PosSet ss ** allIsComMonoid ss))
  
  -- namespace Morphism
  --   public export
  --   bww : (f : c =%+> d) -> (cs : List c.Shp) ->
  --     All (d.PosSet) (f.fwd <$> cs) -> All (c .PosSet) cs
  --   bww f [] [] = []
  --   bww f (c :: cs) (a :: as) = (f.bwd c a) :: bww f cs as
  -- 
  --   public export
  --   List : c =%+> d -> List c =%+> List d
  --   List f = !%+ \cs => (f.fwd <$> cs ** bww f cs)

-- ||| In general, we'll want to instantiate `f` with `IO`, and in that case
-- ||| it'll never be the case that the set of positions is additive
-- ||| Hence we just overload the operator here, and return an ordinary container
-- ||| Edit,later: Hmm, but sometimes there is a need to return an additive cont, 
-- ||| for instance in leftUnitInv in additive morphism instances...
-- ||| See below
-- ||| TODO perhaps the distinguishing aspect here is whether `f` is a commutative
-- ||| monoid homomorphism
-- public export
-- (<!>) : (f : Type -> Type) -> AddCont -> Cont
-- (<!>) f c = (f <!> (UC c))
-- 
-- namespace Morphism
--   public export
--   (<!>) : (f : Type -> Type) -> Functor f =>
--     c =%+> d ->
--     (f <!> c) =%> (f <!> d)
--   (<!>) f l = !% \x => (l.fwd x ** map (l.bwd x))
-- 
--   public export infixr 9 <!>

namespace BangAddCont
  ||| Here we use join?
  public export
  (<!>) : {m : Type -> Type} -> Monad m => AddCont -> AddCont
  (<!>) c = MkAddCont ?bangAddContShp ?bangAddContMon
  
  -- public export
  -- ipList : {0 c : AddCont} -> InterfaceOnPositions (List <!> c) ComMonoid
  -- ipList = MkI $ \_ => listIsMonoid

export prefix 9 !*

||| Right adjoint of the free-forgetful adjunction between Cont and AddCont
||| Left adjoint us the `UC` function
public export
(!*) : Cont -> AddCont
(!*) c = MkAddCont
  c.Shp
  (\s => (Bag (c.Pos s) ** bagIsMonoid))

namespace Morphism
  public export
  (!*) : c =%> d -> !* c =%+> !* d
  (!*) f = (!%) (Bag <!> f)

||| Forward direction of the hom-set isomorphism of the Cont-AddCont adjunction
public export
addContTranspose : {c : AddCont} -> UC c =%> d -> c =%+> !* d
addContTranspose f = !% (sumBw @{mon c} %>> Bag <!> f)

||| Backward direction of the hom-set isomorphism of the Cont-AddCont adjunction
public export
addContTransposeInv : c =%+> !* d -> UC c =%> d
addContTransposeInv f = ULens f %>> pureBw

namespace CompositionAction
  ||| Container used to produce the position type in the composition product
  public export
  positionCont : {c : Cont} -> {d : AddCont} -> Ext c d.Shp -> AddCont
  positionCont ex = MkAddCont
    (c.Pos (shapeExt ex))
    (\cp => d.Pos (index ex cp))

  ||| Action of a container on an additive container
  public export
  (>-+@) : Cont -> AddCont -> AddCont
  c >-+@ d = MkAddCont
    (Ext c d.Shp)
    (\ex => (DPair (positionCont {d=d} ex) ** bagIsMonoid))

  namespace Morphism
    ||| Action on morphisms
    public export
    (>-+@) : c1 =%> d1 ->
      c2 =%+> d2 ->
      c1 >-+@ c2 =%+> d1 >-+@ d2
    (>-+@) f g = !%+ \ex =>
      let (y ** ky) = (%!) f (shapeExt ex)
      in (y <| g.fwd . (index ex) . ky **
          map (\(dp ** dp2) => (ky dp ** g.bwd (index ex (ky dp)) dp2)))

namespace CompositionProduct
  ||| Composition product of additive containers
  ||| Not fully monoidal, but left-skew monoidal
  ||| TODO add one extra argument?
  public export
  (>+@) : AddCont -> AddCont -> AddCont
  c >+@ d = (UC c) >-+@ d

  namespace Morphism
    ||| Action on morphisms
    public export
    (>+@) : c1 =%+> d1 ->
      c2 =%+> d2 ->
      c1 >+@ c2 =%+> d1 >+@ d2
    (>+@) f g = ULens f >-+@ g


namespace CartesianClosure
  ||| Internal hom in the category of additive lenses
  ||| Closely related to the internal hom in the category of ordinary containers
  public export
  InternalLensAdditive : AddCont -> AddCont -> AddCont
  InternalLensAdditive c d = MkAddCont
    (c =%+> d)
    (\l => (DPair (lensInputs l) ** bagIsMonoid))

  public export
  curry : {c : AddCont} -> (c >*< d) =%+> e -> c =%+> (InternalLensAdditive d e)
  curry f = !%+ \x => (!%+ \y => (f.fwd (x, y) ** snd . f.bwd (x, y)) **
    fromGenerators {y = c.Pos x} (\(d ** b') => fst (f.bwd (x, d) b')))

  public export
  uncurry : {c : AddCont} ->
    c =%+> (InternalLensAdditive d e) -> (c >*< d) =%+> e
  uncurry f = !%+ \(x, y) => ((f.fwd x).fwd y **
    \e' => (f.bwd x (MkBag [(y ** e')]), (f.fwd x).bwd y e'))