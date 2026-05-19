module Data.Container.Base.Morphism.Instances

import Data.Fin
import Data.Fin.Split
import Data.Vect
import Data.List.Elem
import Data.List.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Properties.Definitions
import Data.Container.Base.Product.Definitions

import Data.Container.Base.Object.Instances

import Data.Container.Base.Quantifiers
import Data.Container.Base.TreeUtils

import Control.Monad.Distribution
import Control.Monad.Sample.Definition

import Data.Num
import Data.Layout
import Misc

namespace State
  ||| "State" as defined in https://arxiv.org/abs/2403.13001 and open games 
  ||| Given a shape of any container, state can be defined
  public export
  State : Cont -> Type
  State c = Scalar =%> c

  public export
  toState : {0 c : Cont} -> (x : c.Shp) -> State c
  toState x = !% \() => (x ** \_ => ())

  public export
  fromState : {0 c : Cont} ->
    State c ->
    c.Shp
  fromState f = f.fwd ()

namespace Costate
  public export
  Costate : Cont -> Type
  Costate c = c =%> Scalar

  public export
  fromCostate : {0 c : Cont} ->
    Costate c ->
    (x : c.Shp) -> c.Pos x
  fromCostate f x = f.bwd x ()
  
  public export
  toCostate : {0 c : Cont} ->
    ((x : c.Shp) -> c.Pos x) ->
    Costate c
  toCostate s = !% \x => (() ** \() => s x)

public export
fromNapCostateToState : Costate (Nap c.Shp) -> State c
fromNapCostateToState f = toState (f.bwd () ())

public export
fromStateToNapCostate : State c -> Costate (Nap c.Shp)
fromStateToNapCostate f = toCostate f.fwd

public export
pushDown : Cont -> Cont
pushDown c = Const2 Unit c.Shp

public export
pushIntoContinuation : {0 d, p, l : Cont} ->
  (d >< p =%> l) ->
  (p =%> (pushDown d) >@ l)
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

namespace CompositionProduct
  public export
  leftUnit : Scalar >@ c =%> c
  leftUnit = !% \(() <| cShp) => (cShp () ** \c' => (() ** c'))

  public export
  rightUnit : c >@ Scalar =%> c
  rightUnit = !% \(s <| _) => (s ** \cp => (cp ** ()))

  public export
  leftUnitInv : c =%> Scalar >@ c
  leftUnitInv = !% \x => (() <| (\_ => x) ** \(() ** c') => c')
  
  public export
  rightUnitInv : c =%> c >@ Scalar
  rightUnitInv = !% \s => (s <| const () ** fst)

namespace Coproduct
  public export
  elim : c >+< c =%> c
  elim = !% \case
    Left x => (x ** id)
    Right y => (y ** id)

  public export
  initial : Empty =%> c
  initial = !% absurd



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

  ||| Going the other way is impossible without any constraints 
  ||| Two possibilities on constraints (this, and `compToTensor2`)
  public export 
  compToTensor : IsNaperian d =>
    (c >@ d) =%> (c >< d)
  compToTensor @{(MkIsNaperian dPos)} = !% \(cShp <| content) =>
    ((cShp,()) ** \(cPos, dPos) => (cPos ** dPos))
  
  public export
  compToTensor2 : IsFlat c =>
    (c >@ d) =%> (c >< d)
  compToTensor2 @{(ItIsFlat cShp)} = !% \(cShp <| dShp) =>
    ((cShp, dShp ()) ** \((), dPos') => (() ** dPos'))
  
  ||| Specific distributive law we need
  public export
  distribute : (c >< e) =%> s ->
    c >< (e >@ g) =%> s >@ g
  distribute f = (rightUnitInv >< id {a=e >@ g})
               %>> duoidal {d = Scalar}
               %>> (f >@ leftUnit)


||| Wraps a dependent lens `c =%> d`
||| into one of type `c >@ Scalar =%> d >@ Scalar`
||| Needed because `c >@ Scalar` isn't automatically reduced to `c`
public export
wrapIntoVector : c =%> d ->
  Tensor [c] =%> Tensor [d]
wrapIntoVector f = rightUnit %>> f %>> rightUnitInv

public export
wrapIntoMatrix : (c >@ c') =%> (d >@ d') ->
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

namespace CubicalHelpers
  ||| Helper function allowing `shape` in `cubicalShape` to have zero annotation
  public export
  cubicalShapeHelper : All IsCubical shape -> List Nat
  cubicalShapeHelper [] = []
  cubicalShapeHelper (ic :: ics) = dimHelper ic :: cubicalShapeHelper ics
    
  ||| Given a list of cubical containers, return the list of their dimensions
  public export
  cubicalShape : (0 shape : List Cont) -> All IsCubical shape => List Nat
  cubicalShape _ @{ac} = cubicalShapeHelper ac
    
  ||| Size of a list of cubical containers is the product of their dimensions
  public export
  size : (0 shape : List Cont) -> All IsCubical shape => Nat
  size shape = prod (cubicalShape shape)

||| Layout-aware dependent lens flattening a cubical tensor
public export
flattenCubical : {shape : List Cont} ->
  (ac : All IsCubical shape) =>
  LayoutOrder ->
  Tensor shape =%> Vect (size shape)
flattenCubical {shape = [], ac=[]} _ = !% \() => (() ** \FZ => ())
flattenCubical {shape = (_ :: ss), ac=(MkIsCubical n :: as)} lo
  = !% \(() <| t) => (() ** \idx =>
      let (!% recBackward) = flattenCubical {shape = ss} lo
          (i, rest) = splitFinProd lo idx
          (_ ** backRec) = recBackward (t i)
      in (i ** backRec rest))

||| Layout-aware dependent lens unflattening a tensor
public export
unflattenCubical : {shape : List Cont} ->
  (ac : All IsCubical shape) =>
  LayoutOrder ->
  Vect (size shape) =%> Tensor shape
unflattenCubical {shape = [], ac=[]} lo = !% \() => (() ** \() => FZ)
unflattenCubical {shape = (_ :: ss), ac=((MkIsCubical n) :: as)} lo =
  let (!% f) = unflattenCubical {shape = ss} lo
      (innerShape ** innerBack) = f ()
  in !% \() => ((() <| \_ => innerShape) ** (\(cp ** restPos) =>
    indexFinProd lo cp (innerBack restPos)))

||| This is simply a rewrite!
public export
recastFlattenedTensor : {oldShape, newShape : List Cont} ->
  (oldAc : All IsCubical oldShape) => (newAc : All IsCubical newShape) =>
  {auto prf : size oldShape = size newShape} ->
  Vect (size oldShape) =%> Vect (size newShape)
recastFlattenedTensor = !% \() => (() ** \i => rewrite prf in i)

||| Reshapes a cubical tensor by first flattening it to a linear representation,
||| casting the type to the new shape, and then unflattening it back
||| Is generic over layout order
public export
reshape : {oldShape, newShape : List Cont} ->
  (oldAc : All IsCubical oldShape) => (newAc : All IsCubical newShape) =>
  LayoutOrder ->
  {auto prf : size oldShape = size newShape} ->
  Tensor oldShape =%> Tensor newShape
reshape lo = flattenCubical lo
         %>> recastFlattenedTensor
         %>> unflattenCubical lo


namespace Transpose
  public export
  transposeLens : IsNaperian c => IsNaperian d => c >@ d =%> d >@ c
  transposeLens @{MkIsNaperian _} @{MkIsNaperian _} = !% \(() <| _) =>
    (() <| (\_ => ()) ** \(dInd ** cInd) => (cInd ** dInd))

  public export
  transpose : IsNaperian c => IsNaperian d =>
    Tensor [c, d] =%> Tensor [d, c]
  transpose @{MkIsNaperian _} @{MkIsNaperian _} = wrapIntoMatrix transposeLens

  -- ||| experiment, does this work?
  -- public export
  -- transposeMiddle : IsNaperian c => IsNaperian e =>
  --   Tensor [c, e, d] =%> 
  

  --||| Transpose a given element to the front of the shape
  --public export
  --transposeToFront : (shape : List Cont) ->
  --  (c : Cont) ->
  --  (elem : Elem c shape) =>
  --  All IsNaperian (dropAfterElem shape elem) =>
  --  Tensor shape =%> Tensor (c :: dropElem shape elem)
  --transposeToFront (_ :: xs) c @{Here} @{allNap} = ?transposeToFront_rhs_0
  --transposeToFront (y :: xs) c @{(There x)} @{allNap} = ?transposeToFront_rhs_1
  
||| Functionality for transforming a tensor into a hancock tensor
namespace TransformIntoHancockTensor
  public export
  hancockTensorNaperianShape : {shape : List Cont} ->
    (allNap : All IsNaperian shape) =>
    (HancockTensor shape).Shp
  hancockTensorNaperianShape {shape = []} = ()
  hancockTensorNaperianShape {allNap = ((MkIsNaperian _) :: _)}
    = ((), hancockTensorNaperianShape)
  
  ||| Helper to compute the unique shape of Tensor when all containers are Naperian
  public export
  tensorNaperianShape : {shape : List Cont} ->
    (allNap : All IsNaperian shape) =>
    (Tensor shape).Shp
  tensorNaperianShape {shape = []} = ()
  tensorNaperianShape {shape = (_ :: ss), allNap = ((MkIsNaperian _) :: ns)}
    = () <| \_ => tensorNaperianShape {shape = ss} @{ns}
  
  ||| Analogous to `naperianPosEq` but for the HancockTensor structure
  ||| We can't use `naperianPosEq` directly because the shape of the resulting
  ||| container is not Unit, it is only isomorphic to it
  public export
  hancockTensorPosEq : {shape : List Cont} ->
    (allNap : All IsNaperian shape) =>
    {0 x, y : (HancockTensor shape).Shp} ->
    (HancockTensor shape).Pos x = (HancockTensor shape).Pos y
  hancockTensorPosEq {allNap = []} = Refl
  hancockTensorPosEq {allNap = ((MkIsNaperian _) :: _)} = cong2 Pair
    (naperianPosEq @{MkIsNaperian _} {x=()} {y=()})
    hancockTensorPosEq
  
  ||| Tensor shape is isomorphic to HancockTensor shape when all containers in
  ||| the shape are Naperian. This is one arrow of that isomorphism
  public export
  transformToHancock : {shape : List Cont} ->
    All IsNaperian shape =>
    Tensor shape =%> HancockTensor shape
  transformToHancock {shape = []} = id
  transformToHancock {shape = (_ :: _)} @{((MkIsNaperian _) :: _)}
    = !% \(() <| content) => (((), hancockTensorNaperianShape) **
       \(p, restPos) =>
         let (_ ** recBack) = (%!) transformToHancock (content p)
         in (p ** recBack $ replace {p = id} hancockTensorPosEq restPos))

  public export
  transformFromHancock : {shape : List Cont} ->
    All IsNaperian shape =>
    HancockTensor shape =%> Tensor shape
  transformFromHancock {shape = []} = id
  transformFromHancock {shape = (Nap s :: ss)} @{((MkIsNaperian s) :: _)}
    = !% \((), hShp) =>
        let (tShp ** recBack) = (%!) transformFromHancock hShp
        in (() <| (\_ => tShp) ** \(p ** restPos) => (p, recBack restPos))

    

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

public export
Sample : MonadSample m => {n : Nat} -> IsSucc n =>
  (m <!> Sample n) =%> Scalar
Sample = toCostate sample

-- TODO here maybe need to uncomment during merge?
-- public export
-- selectShape : {cs : Vect k Cont} ->
--   (shapes : All Shp cs) -> (i : Fin k) -> Any Shp cs
-- selectShape (s :: _) FZ = Here s
-- selectShape (_ :: ss) (FS j) = There (selectShape ss j)
-- 
-- ||| Extract the position from an AnyPos at a given index
-- public export
-- extractPos : {n : Nat} -> {xs : Vect n Cont} ->
--   {shapes : All Shp xs} ->
--   (i : Fin n) ->
--   AnyShpPos (selectShape shapes i) ->
--   AnyPos shapes
-- extractPos {shapes = (_ :: _)} FZ (Here x) = Here x
-- extractPos {shapes = (_ :: _)} (FS j) (There rest)
--   = There $ extractPos j rest
-- 
-- public export
-- SampleAndChoose : {n : Nat} -> {xs : Vect n Cont} ->
--   ConvexComb xs =%> (Sample n >@ Any xs)
-- SampleAndChoose = !% \(d, shapes) =>
--   (d <| selectShape shapes ** \(i ** grad) => (0, [extractPos i grad]))

-- SampleAndChooseWithDist = !% \(d, shapes) =>
--   (d <| electShape shapes ** \(i ** grad) => (0, [(i ** extractPos i grad)]))

-- public export
-- GetDist : {n : Nat} -> {xs : Vect n Cont} ->
--   ConvexComb xs =%> Simplex n
-- GetDist = !% \(d, shapes) => (d ** \d' => (d', ?GetDist_rhs))

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
