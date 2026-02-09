module Data.Container.Base.Morphism.Instances

import Data.Fin
import Data.Fin.Split
import Data.List.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Product.Definitions
import Data.Container.Base.Object.Instances

import Data.Container.Base.TreeUtils

import Data.Layout
import Misc

||| "State" as defined in https://arxiv.org/abs/2403.13001 and open games 
||| Given a shape of any container, can be defined as a dependent lens
public export
State : {c : Cont} -> c.Shp -> Scalar =%> c
State x = !% \() => (x ** const ())

||| "Costate" as defined in categorical deep learning and open games
||| Models the notion of a dependent function using dependent lenses
public export
Costate : {0 c : Cont} ->
  (s : (x : c.Shp) -> c.Pos x) ->
  c =%> Scalar
Costate s = !% \x => (() ** \() => s x)

public export
fromCostate : {0 c : Cont} ->
  c =%> Scalar ->
  (x : c.Shp) -> c.Pos x
fromCostate f x = snd ((%! f) x) ()


public export
rightUnit : (c >< Scalar) =%> c
rightUnit = !% \(x, ()) => (x ** \x' => (x', ()))

||| Ext is a functor of type Cont -> [Type, Type]
||| On objects it maps a container to a polynomial functor
||| On morphisms it maps a dependent lens to a natural transformation
||| This is the action on morphisms
public export
extMap : {0 c, d : Cont} ->
  c =%> d ->
  Ext c a -> Ext d a
extMap f (sh <| index) = let (y ** ky) = (%!) f sh
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
reshapeFlattenedTensor : {oldShape, newShape : List Cont} ->
  (oldAc : All IsCubical oldShape) => (newAc : All IsCubical newShape) =>
  {auto prf : size oldShape = size newShape} ->
  Vect (size oldShape) =%> Vect (size newShape)
reshapeFlattenedTensor = !% \() => (() ** \i => rewrite prf in i)

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
         %>> reshapeFlattenedTensor
         %>> unflattenCubical lo


||| Technically this is Unit, but hard to prove
public export
foldOverNaperianShapeComp : {shape : List Cont} ->
  (allNap : All IsNaperian shape) =>
  (Tensor shape).Shp
foldOverNaperianShapeComp {shape = []} = ()
foldOverNaperianShapeComp {allNap = ((MkIsNaperian pos) :: ns)}
  = () <| \_ => foldOverNaperianShapeComp

public export
naperianHancockShape : {shape : List Cont} ->
  (allNap : All IsNaperian shape) =>
  (HancockTensor shape).Shp = Unit
naperianHancockShape = believe_me ()

public export
foldOverNaperianShapeHancock : {shape : List Cont} ->
  (allNap : All IsNaperian shape) =>
  (HancockTensor shape).Shp
foldOverNaperianShapeHancock {shape = []} = ()
foldOverNaperianShapeHancock {allNap = ((MkIsNaperian _) :: _)}
  = ((), foldOverNaperianShapeHancock)

public export
EmptyExtEq : {0 c : Cont} -> IsNaperian c => Ext c Unit = Unit
EmptyExtEq @{(MkIsNaperian pos)} = believe_me () -- what does wrong if we do this

namespace Transpose
  public export
  transposeLens : IsNaperian c => IsNaperian d => (c >@ d) =%> (d >@ c)
  transposeLens @{MkIsNaperian _} @{MkIsNaperian _} = !% \(() <| _) =>
    (() <| (\_ => ()) ** \(dInd ** cInd) => (cInd ** dInd))

  ||| This and the above function should be one and the same, up to rebracketing
  public export
  transpose : IsNaperian c => IsNaperian d =>
    Tensor [c, d] =%> Tensor [d, c]
  transpose @{MkIsNaperian _} @{MkIsNaperian _} = !% \(() <| _) =>
    (() <| (\_ => () <| (\_ => ())) ** \(dInd ** cInd ** ()) =>
      (cInd ** (dInd ** ())))
    


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

-- public export
-- traverseLeaf : (x : BinTreeShape) -> FinBinTreeLeaf x -> Fin (numLeaves x)
-- traverseLeaf LeafS Done = FZ
-- traverseLeaf (NodeS lt rt) (GoLeft x) = weakenN (numLeaves rt) (traverseLeaf lt x)
-- traverseLeaf (NodeS lt rt) (GoRight x) = shift (numLeaves lt) (traverseLeaf rt x)
-- 

public export
maybeToList : Maybe =%> List
maybeToList = !% \b => case b of 
  False => (0 ** absurd)
  True => (1 ** \_ => ())