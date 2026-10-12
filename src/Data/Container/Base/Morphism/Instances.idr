module Data.Container.Base.Morphism.Instances

import Data.Fin
import Data.Fin.Split
import Data.Vect
import Data.List.Elem
import Data.List.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Product.Definition
import Data.Container.Base.Endofunctor.Definition

import Data.Container.Base.Object.Instances
import Data.Container.Base.Extension.Instances

import Data.Container.Base.Quantifiers
import Data.Container.Base.TreeUtils


import Data.Num
import Data.Layout
import Misc

||| If we model the idea of a container (S !> P) as a box
|||  ┌──────┐
|||  │ s:S  │
|||  ├──────┤
|||  │  Ps  │
|||  └──────┘
||| then `pushDown` is interpreted as keeping the box frame in place while
||| pushing down the container: pruning any part of the container that goes 
||| out of the box, and using `Unit` for anything new that appears:
|||  ┌──────┐
|||  │ Unit │
|||  ├──────┤
|||  │ s:S  │
|||  └──────┘
|||     Ps
public export
pushDown : Cont -> Cont
pushDown c = Const2 Unit c.Shp

public export
pushIntoContinuation : {0 d, p, l : Cont} ->
  d >< p =%> l ->
  p =%> (pushDown d) >@ l
pushIntoContinuation f = !% \p => (() <| \d => f.fwd (d, p) **
  \(d ** l') => snd $ f.bwd (d, p) l')


namespace CategoricalProduct
  public export
  terminal : c =%> UnitCont
  terminal = !% \_ => (() ** absurd)


namespace HancockTensorProduct
  public export
  leftUnit : Scalar >< c =%> c
  leftUnit = !% \((), s) => (s ** \p => ((), p))
  
  public export
  rightUnit : c >< Scalar =%> c
  rightUnit = !% \(x, ()) => (x ** \x' => (x', ()))

  public export
  leftUnitInv : c =%> Scalar >< c
  leftUnitInv = !% \x => (((), x) ** \((), x') => x')

  public export
  rightUnitInv : c =%> c >< Scalar
  rightUnitInv = !% \x => ((x, ()) ** \(x', ()) => x')

  public export
  assocL : (a >< b) >< c =%> a >< (b >< c)
  assocL = !% \((a, b), c) => ((a, (b, c)) ** \(a', (b', c')) => ((a', b'), c'))

  public export
  assocR : a >< (b >< c) =%> (a >< b) >< c
  assocR = !% \(a, (b, c)) => (((a, b), c) ** \((a', b'), c') => (a', (b', c')))

  public export
  swap : a >< b =%> b >< a
  swap = !% \(a, b) => ((b, a) ** \(b', a') => (a', b'))

  public export
  swapMiddle : (c1 >< c2) >< (c3 >< c4) =%> (c1 >< c3) >< (c2 >< c4)
  swapMiddle = assocL {c=_ >< _}
           %>> (id >< assocR)
           %>> (id >< swap >< id)
           %>> (id >< assocL)
           %>> assocR {c=_ >< _}

namespace CompositionProduct
  public export
  leftUnit : Scalar >@ c =%> c
  leftUnit = !% \ex => (index ex () ** \c' => (() ** c'))

  public export
  rightUnit : c >@ Scalar =%> c
  rightUnit = !% \ex => (shapeExt ex ** \cp => (cp ** ()))

  public export
  leftUnitInv : c =%> Scalar >@ c
  leftUnitInv = !% \s => (() <| (\_ => s) ** \(() ** c') => c')
  
  public export
  rightUnitInv : c =%> c >@ Scalar
  rightUnitInv = !% \s => (s <| \_ => () ** fst)

  public export
  assocL : (a >@ b) >@ c =%> a >@ (b >@ c)
  assocL = !% \((aShp <| f) <| g) =>
    (aShp <| \aPos => f aPos <| \bPos => g (aPos  ** bPos) **
      \(aPos ** bPos ** cPos) => ((aPos ** bPos) ** cPos))

  public export
  assocR : a >@ (b >@ c) =%> (a >@ b) >@ c
  assocR = !% \(aShp <| f) =>
    ((aShp <| shapeExt . f) <| \(aPos ** bPos) => index (f aPos) bPos **
      \((aPos ** bPos) ** cPos) => (aPos ** (bPos ** cPos)))

namespace Coproduct
  public export
  elim : c >+< c =%> c
  elim = !% \case
    Left x => (x ** id)
    Right y => (y ** id)

  public export
  initial : Empty =%> c
  initial = !% absurd

  public export
  cojoin : c =%> z ->
    d =%> z ->
    c >+< d =%> z
  cojoin f g = (f >+< g) %>> elim

  public export
  direct : (a.Shp -> Bool) ->
    a =%> a >+< a
  direct p = !% \x => case p x of
    False => (Left x ** id)
    True => (Right x ** id)



namespace CartesianClosure
  ||| The following is the proof that for any container `c` there is an
  ||| isomorphism in `Cont` between `c` and `CartesianClosure UnitCont c`
  ||| This holds in any monoidal closed category: `X ≅ [I, X]`
  namespace StateIsomorphismProof
    stateToCartClosureFw : c =%> (CartesianClosure UnitCont c)
    stateToCartClosureFw = !% \cShp => (!% \() => (cShp ** \_ => Nothing)
                                       ** \(() ** cPos ** ItIsNothing) => cPos)

    stateToCartClosureBw : CartesianClosure UnitCont c =%> c
    stateToCartClosureBw = !% \l => (l.fwd () ** \cPos =>
      (() ** cPos ** maybeVoidIsNothing (l.bwd () cPos)))


||| For a overview of this interaction from the categorical perspective, see
||| the Poly book (https://arxiv.org/abs/2312.00990) (Section 6.3.4)
namespace CompositionTensorInteraction
  ||| Interaction between composition and tensor product
  ||| Swaps the operations, and middle two containers
  ||| Not an isomorphism!
  public export
  duoidal : (c >@ d) >< (e >@ f) =%> (c >< e) >@ (d >< f)
  duoidal = !% \((sc <| idxC), (se <| idxE)) =>
    ((sc, se) <| \(cp, ep) => (idxC cp, idxE ep) **
      \((cp, ep) ** (dp, fp)) => ((cp ** dp), (ep ** fp)))
  
  ||| Tensor product embeds into composition
  ||| A special case of `duoidal`
  public export
  tensorToComp : c >< f =%> c >@ f
  tensorToComp =   (rightUnitInv >< leftUnitInv)
               %>> duoidal {d=Scalar,e=Scalar}
               %>> (rightUnit >@ leftUnit)

  ||| Specific distributive law we need
  public export
  distribute : c >< e =%> s ->
    c >< (e >@ g) =%> s >@ g
  distribute f = (rightUnitInv >< id {c=e >@ g})
               %>> duoidal {d = Scalar}
               %>> (f >@ leftUnit)


namespace State
  ||| "State" as defined in https://arxiv.org/abs/2403.13001 and open games 
  |||
  |||       ┌─────────────┐
  |||       │             ├──► (x : c.Shp)
  |||       │    State    │
  |||       │             ├◄── c.Pos x
  |||       └─────────────┘
  public export
  State : Cont -> Type
  State c = Scalar =%> c

  ||| Given a shape of any container, state can be defined
  public export
  toState : (x : c.Shp) -> State c
  toState x = !% \() => (x ** \_ => ())

  public export
  fromState : State c -> c.Shp
  fromState f = f.fwd ()

  public export
  mapState : State c ->
    c =%> d ->
    State d
  mapState s f = s %>> f

namespace Costate
  ||| "Costate" as defined in https://arxiv.org/abs/2403.13001 and open games 
  |||
  |||                  ┌─────────────┐
  |||  (x : c.Shp)  ──►┤             │
  |||                  │   Costate   │
  |||     c.Pos x   ◄──┤             │
  |||                  └─────────────┘
  public export
  Costate : Cont -> Type
  Costate c = c =%> Scalar

  public export
  toCostate : ((x : c.Shp) -> c.Pos x) -> Costate c
  toCostate s = !% \x => (() ** \() => s x)

  public export
  fromCostate : Costate c -> (x : c.Shp) -> c.Pos x
  fromCostate f x = f.bwd x ()

  public export
  mapCostate : Costate d ->
    c =%> d ->
    Costate c
  mapCostate s f = f %>> s

  public export
  pairCostate : Costate c -> Costate d -> Costate (c >< d)
  pairCostate f g = (f >< g) %>> leftUnit {c=Scalar}
  
public export
fromNapCostateToState : Costate (Nap c.Shp) -> State c
fromNapCostateToState f = toState (f.bwd () ())

public export
fromStateToNapCostate : State c -> Costate (Nap c.Shp)
fromStateToNapCostate f = toCostate f.fwd



||| Wraps a dependent lens `c =%> d`
||| into one of type `c >@ Scalar =%> d >@ Scalar`
||| Needed because `c >@ Scalar` isn't automatically reduced to `c`
public export
wrapIntoVector : c =%> d ->
  Tensor [c] =%> Tensor [d]
wrapIntoVector f = rightUnit %>> f %>> rightUnitInv

public export
wrapIntoMatrix : c >@ c' =%> d >@ d' ->
  Tensor [c, c'] =%> Tensor [d, d']
wrapIntoMatrix f =   (id >@ rightUnit)
                 %>> f
                 %>> (id >@ rightUnitInv)

||| Wraps a dependent lens `c =%> d`
||| into one of type `c >< Scalar =%> d >< Scalar`
||| Needed because `c >< Scalar` isn't automatically reduced to `c`
public export
wrapIntoVectorHancock : c =%> d ->
  HancockTensor [c] =%> HancockTensor [d]
wrapIntoVectorHancock f = rightUnit %>> f %>> rightUnitInv

public export
pick : Pick c a =%> c
pick = !% \e => (shapeExt e ** index e)

||| A lens from a container specialised to a shape to the container itself
public export
atShape : (s : c.Shp) -> At c s =%> c
atShape s = !% \() => (s ** id)

||| A vector of positive length is a non-empty list
public export
vectToList1 : {k : Nat} -> Vect (S k) =%> List1
vectToList1 = !% \() => (k ** id)
    

  -- ||| Technically this is Unit, but hard to prove
  -- public export
  -- foldOverNaperianShapeComp : {shape : List Cont} ->
  --   (allNap : All IsNaperian shape) =>
  --   (Tensor shape).Shp
  -- foldOverNaperianShapeComp {shape = []} = ()
  -- foldOverNaperianShapeComp {allNap = ((MkIsNaperian pos) :: ns)}
  --   = () <| \_ => foldOverNaperianShapeComp
  -- 
  -- public export
  -- naperianHancockShape : {shape : List Cont} ->
  --   (allNap : All IsNaperian shape) =>
  --   (HancockTensor shape).Shp = Unit
  -- naperianHancockShape = believe_me ()
  -- 
  -- public export
  -- foldOverNaperianShapeHancock : {shape : List Cont} ->
  --   (allNap : All IsNaperian shape) =>
  --   (HancockTensor shape).Shp
  -- foldOverNaperianShapeHancock {shape = []} = ()
  -- foldOverNaperianShapeHancock {allNap = ((MkIsNaperian _) :: _)}
  --   = ((), foldOverNaperianShapeHancock)


-- public export
-- tensorIsNaperianShape : {shape : List Cont} ->
--   (allNap : All IsNaperian shape) =>
--   IsNaperian (Tensor shape)
-- tensorIsNaperianShape {shape = []} = MkIsNaperian ()
-- tensorIsNaperianShape {shape = (_ :: ss), allNap = ((MkIsNaperian pos) :: ns)}
--   = let tg = tensorIsNaperianShape {shape = ss} 
--     in ?tensorIsNaperianShape_rhs_1
--     --in rewrite naperianShpEq @{tg}
--     --in (rewrite (EmptyExtEq {c=(Nap pos)})
--     --in let tg = MkIsNaperian in ?tensorIsNaperianShape_rhs_2)

-- public export
-- transformToHancock : {shape : List Cont} ->
--   All IsNaperian shape =>
--   Tensor shape =%> HancockTensor shape
-- transformToHancock {shape = []} = id
-- transformToHancock {shape = (_ :: ss)} @{((MkIsNaperian pos) :: ns)}
--   = let f = (%!) (transformToHancock {shape = ss} @{ns})
--         (_ ** h) = f (foldOverNaperianShapeComp {shape=ss})
--     in !% \(() <| content) => (((), foldOverNaperianShapeHancock) **
--       \(p, fld) => (p ** ?hhh))
--       -- (((), rewrite -- foldOverNaperianShapeHancock {shape=ss} @{ns} in ()) **
--     --   \(p, fld) => (p ** ?bnn))

-- need to organise this

public export
handleEffect : Monad m =>
  (handler : (m <!> effect) =%> Scalar) ->
  (program : a =%> effect) ->
  m <!> a =%> Scalar
handleEffect handler program = !% \x =>
  let (ef ** nn) = (%! program) x
      (() ** rest) = (%! handler) ef
  in (() ** \() => do 
    e <- rest ()
    pure (nn e))

namespace BinTree
  public export
  inorderBackward : (b : BinTreeShape) ->
    Fin (numNodesAndLeaves b) ->
    BinTreePos b
  inorderBackward LeafS FZ = AtLeaf
  inorderBackward (NodeS lt rt) n with (strengthenN {m=numNodesAndLeaves lt} n)
     _ | Left p = GoLeft (inorderBackward lt p)
     _ | Right FZ = AtNode
     _ | Right (FS g) = GoRight (inorderBackward rt g)


  public export
  inorder : BinTree =%> List
  inorder = !% \b => (numNodesAndLeaves b ** inorderBackward b)

namespace BinTreeNode
  public export
  inorderBackward : (b : BinTreeShape) ->
    Fin (numNodes b) ->
    BinTreePosNode b
  inorderBackward (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
    _ | Left p = GoLeft (inorderBackward lt p)
    _ | Right FZ = AtNode
    _ | Right (FS g) = GoRight (inorderBackward rt g)

  ||| Traverses a binary tree container in order, producing a list container
  public export
  inorder : BinTreeNode =%> List
  inorder = !% \b => (numNodes b ** inorderBackward b)

  -- Need to do some rewriting for preorder
  public export
  preorderBinTreeNode : (b : BinTreeShape) ->
    Fin (numNodes b) -> BinTreePosNode b
  preorderBinTreeNode (NodeS lt rt) x = ?preorderBinTreeNode_rhs_1
  --preorderBinTreeNode (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
  --  _ | Left p = ?whl
  --  _ | Right FZ = ?whn
  --  _ | Right (FS g) = ?whr

namespace BinTreeLeaf
  public export
  inorderBackward : (b : BinTreeShape) ->
    Fin (numLeaves b) ->
    BinTreePosLeaf b
  inorderBackward LeafS 0 = AtLeaf
  inorderBackward (NodeS lt rt) i with (strengthenN {m=numLeaves lt} i)
    _ | (Left indLeft) = GoLeft (inorderBackward lt indLeft)
    _ | (Right indRight) = GoRight (inorderBackward rt indRight)

  public export
  inorder : BinTreeLeaf =%> List
  inorder = !% \b => (numLeaves b ** inorderBackward b)

-- public export
-- traverseLeaf : (x : BinTreeShape) -> FinBinTreeLeaf x -> Fin (numLeaves x)
-- traverseLeaf LeafS Done = FZ
-- traverseLeaf (NodeS lt rt) (GoLeft x) = weakenN (numLeaves rt) (traverseLeaf lt x)
-- traverseLeaf (NodeS lt rt) (GoRight x) = shift (numLeaves lt) (traverseLeaf rt x)
-- 

public export
vectToList : {n : Nat} -> Vect n =%> List
vectToList = !% \() => (n ** id)

public export
maybeToList : Maybe =%> List
maybeToList = !% \b => case b of 
  False => (0 ** absurd)
  True => (1 ** \_ => ())
