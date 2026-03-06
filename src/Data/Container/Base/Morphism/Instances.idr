module Data.Container.Base.Morphism.Instances

import Data.Fin
import Data.Fin.Split
import Data.Vect
import Data.Vect.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Product.Definitions
import Data.Container.Base.Object.Instances

import Data.Container.Base.Quantifiers
import Data.Container.Base.TreeUtils

import Control.Monad.Distribution
import Control.Monad.Sample.Definition

import Data.Num
import Data.Layout
import Misc

public export
State : Cont -> Type
State c = Scalar =%> c

public export
Costate : Cont -> Type
Costate c = c =%> Scalar

public export
toState : {0 c : Cont} -> (x : c.Shp) -> State c
toState x = !% \() => (x ** \_ => ())

public export
fromState : {0 c : Cont} ->
  State c ->
  c.Shp
fromState f = f.fwd ()

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
fromNapCostateToState : {0 c : Cont} ->
  Costate (Nap c.Shp) -> State c
fromNapCostateToState f = toState (f.bwd () ())

public export
fromStateToNapCostate : {0 c : Cont} ->
  State c -> Costate (Nap c.Shp)
fromStateToNapCostate f = toCostate f.fwd

public export
pushDown : Cont -> Cont
pushDown c = Const2 Unit c.Shp

public export
pushIntoContinuation : {d, p, l : Cont} ->
  (d >< p =%> l) ->
  (p =%> (pushDown d) >@ l)
pushIntoContinuation f = !% \p => (() <| \d => f.fwd (d, p) **
  \(d ** l') => snd $ f.bwd (d, p) l')



namespace Monadic
  public export
  fromCostate : {m : Type -> Type} -> Monad m => {0 c : Cont} ->
    MLens {m=m} c Scalar ->
    (x : c.Shp) -> m (c.Pos x)
  fromCostate f x = ((\b => b ()) . snd) <$> ((%%! f) x)


namespace HancockTensorProduct
  public export
  leftUnit : (Scalar >< c) =%> c
  leftUnit = !% \((), s) => (s ** \p => ((), p))
  
  public export
  rightUnit : (c >< Scalar) =%> c
  rightUnit = !% \(x, ()) => (x ** \x' => (x', ()))

  public export
  leftUnitInv : c =%> (Scalar >< c)
  leftUnitInv = !% \x => (((), x) ** \((), x') => x')

  public export
  rightUnitInv : c =%> (c >< Scalar)
  rightUnitInv = !% \x => ((x, ()) ** \(x', ()) => x')

  public export
  assocL : ((a >< b) >< c) =%> (a >< (b >< c))
  assocL = !% \((a, b), c) => ((a, (b, c)) ** \(a', (b', c')) => ((a', b'), c'))

  public export
  assocR : (a >< (b >< c)) =%> ((a >< b) >< c)
  assocR = !% \(a, (b, c)) => (((a, b), c) ** \((a', b'), c') => (a', (b', c')))

  public export
  swap : (a >< b) =%> (b >< a)
  swap = !% \(a, b) => ((b, a) ** \(b', a') => (a', b'))

namespace CompositionProduct
  public export
  leftUnit : (Scalar >@ c) =%> c
  leftUnit = !% \(() <| cShp) => (cShp () ** \c' => (() ** c'))

  public export
  rightUnit : (c >@ Scalar) =%> c
  rightUnit = !% \(s <| _) => (s ** \cp => (cp ** ()))

  public export
  leftUnitInv : c =%> (Scalar >@ c)
  leftUnitInv = !% \x => (() <| (\_ => x) ** \(() ** c') => c')
  
  public export
  rightUnitInv : c =%> (c >@ Scalar)
  rightUnitInv = !% \s => (s <| const () ** fst)


||| Interaction between composition and tensor product
public export
duoidal : ((c >@ d) >< (e >@ f)) =%> ((c >< e) >@ (d >< f))
duoidal = !% \((sc <| idxC), (se <| idxE)) =>
  ((sc, se) <| \(cp, ep) => (idxC cp, idxE ep) **
    \((cp, ep) ** (dp, fp)) => ((cp ** dp), (ep ** fp)))

||| Specific distributive law we need
public export
distribute : ((c >< e) =%> s) ->
  ((c >< (e >@ g)) =%> (s >@ g))
distribute f = (rightUnitInv >< id {a=e >@ g})
             %>> duoidal {d = Scalar}
             %>> (f >@ leftUnit)

||| Ext is a functor of type Cont -> [Type, Type]
||| On objects it maps a container to a polynomial functor
||| On morphisms it maps a dependent lens to a natural transformation
||| This is the action on morphisms
public export
extMap : {c, d : Cont} ->
  c =%> d ->
  Ext c a -> Ext d a
extMap (!% f) (sh <| index) = let (y ** ky) = f sh
                              in y <| (index . ky)


||| Wraps a dependent lens `c =%> d`
||| into one of type `c >@ Scalar =%> d >@ Scalar`
||| Needed because `c >@ Scalar` isn't automatically reduced to `c`
public export
wrapIntoVector : {c, d : Cont} ->
  c =%> d ->
  Tensor [c] =%> Tensor [d]
wrapIntoVector (!% f) =
  !% \e => let (y ** ky) = f (shapeExt e)
           in (y <| \_ => () ** \(cp ** ()) => (ky cp ** ()))

||| Layout-aware isomorphism between a cubical tensor and a vector
||| Uses the specified layout order for index mapping
public export
flatten : {shape : List Nat} ->
  LayoutOrder ->
  Tensor (Vect <$> shape) =%> Vect (prod shape)
flatten {shape = []} _ = !% \() => (() ** \FZ => ())
flatten {shape = (s :: ss)} lo = !% \(() <| t) => (() ** \idx => 
  let (!% recBackward) = flatten {shape = ss} lo
      (i, rest) = splitFinProd lo idx
      (_ ** backRec) = recBackward (t i)
  in (i ** backRec rest))

||| Unflattens a vector into a cubical tensor of specific shape
||| Is generic over layout order
public export
unflatten : {shape : List Nat} ->
  LayoutOrder ->
  Vect (prod shape) =%> Tensor (Vect <$> shape)
unflatten {shape = []} lo = !% \() => (() ** \() => FZ)
unflatten {shape = (s :: ss)} lo =
  let (!% f) = unflatten {shape = ss} lo
      (innerShape ** innerBack) = f ()
  in !% \() => ((() <| \_ => innerShape) ** (\(cp ** restPos) =>
    indexFinProd lo cp (innerBack restPos)))

||| This is simply a rewrite!
public export
reshapeFlattenedTensor : {oldShape, newShape : List Nat} ->
  {auto prf : prod oldShape = prod newShape} ->
  Vect (prod oldShape) =%> Vect (prod newShape)
reshapeFlattenedTensor = !% \() => (() ** \i => rewrite prf in i)

||| Reshapes a cubical tensor by first flattening it to a linear representation,
||| casting the type to the new shape, and then unflattening it back
||| Is generic over layout order
public export
reshape : {oldShape, newShape : List Nat} ->
  LayoutOrder ->
  {auto prf : prod oldShape = prod newShape} ->
  Tensor (Vect <$> oldShape) =%> Tensor (Vect <$> newShape)
reshape lo = flatten lo %>> reshapeFlattenedTensor %>> unflatten lo

  
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


  -- TODO reshape commented out for the same reason as reshapeTensorA is
  -- public export
  -- reshape : {oldShape, newShape : List Nat} ->
  --   Tensor oldShape a ->
  --   {auto prf : prod oldShape = prod newShape} ->
  --   Tensor newShape a

-- Need to do some rewriting for preorder
public export
preorderBinTreeNode : (b : BinTreeShape) -> Fin (numNodes b) -> BinTreePosNode b
preorderBinTreeNode (NodeS lt rt) x = ?preorderBinTreeNode_rhs_1
--preorderBinTreeNode (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
--  _ | Left p = ?whl
--  _ | Right FZ = ?whn
--  _ | Right (FS g) = ?whr

public export
maybeToList : Maybe =%> List
maybeToList = !% \b => case b of 
  False => (0 ** absurd)
  True => (1 ** \_ => ())


-- public export
-- traverseLeaf : (x : BinTreeShape) -> FinBinTreeLeaf x -> Fin (numLeaves x)
-- traverseLeaf LeafS Done = FZ
-- traverseLeaf (NodeS lt rt) (GoLeft x) = weakenN (numLeaves rt) (traverseLeaf lt x)
-- traverseLeaf (NodeS lt rt) (GoRight x) = shift (numLeaves lt) (traverseLeaf rt x)
-- 

public export
Sample : MonadSample m => {n : Nat} -> IsSucc n =>
  (m <!> Sample n) =%> Scalar
Sample = toCostate sample

public export
selectShape : {cs : Vect k Cont} ->
  (shapes : All Shp cs) -> (i : Fin k) -> Any Shp cs
selectShape (s :: _) FZ = Here s
selectShape (_ :: ss) (FS j) = There (selectShape ss j)

||| Extract the position from an AnyPos at a given index
public export
extractPos : {n : Nat} -> {xs : Vect n Cont} ->
  {shapes : All Shp xs} ->
  (i : Fin n) ->
  AnyShpPos (selectShape shapes i) ->
  AnyPos shapes
extractPos {shapes = (_ :: _)} FZ (Here x) = Here x
extractPos {shapes = (_ :: _)} (FS j) (There rest)
  = There $ extractPos j rest

public export
SampleAndChoose : {n : Nat} -> {xs : Vect n Cont} ->
  ConvexComb xs =%> (Sample n >@ Any xs)
SampleAndChoose = !% \(d, shapes) =>
  (d <| selectShape shapes ** \(i ** grad) => (0, [extractPos i grad]))

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