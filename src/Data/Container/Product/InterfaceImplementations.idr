module Data.Container.Product.InterfaceImplementations

import Data.Container.Object.Instances
import Data.Container.Extension.Definition
import Data.Container.Morphism.Definition
import Data.Container.Morphism.Instances
import Data.Container.Product.Interfaces
import Data.Fin.Split
import Data.Functor.Algebra
import Data.Layout

export
TensorMonoid Maybe where
  tensorN = State True
  tensorM = !% \(b1, b2) => (b1 && b2 ** \bb => case b1 of
    True => ((), if b2 then bb else absurd bb)
    False => absurd bb)

||| Follows Applicative instance in `Prelude.Types`
||| `splitFinProd` here is a layout-aware variant of `splitProd`
export
TensorMonoid List where
  tensorN = State 1
  tensorM = !% \(n, m) => (n * m ** splitFinProd DefaultLayoutOrder) 

||| Covers vectors, among others
||| For vecotrs produces a `zip` operation
export
IsNaperian c => TensorMonoid c where
  tensorN @{(MkIsNaperian pos)} = State ()
  tensorM @{(MkIsNaperian pos)} = !% \((), ()) => (() ** \i => (i, i))

export
IsCubical c => SeqMonoid c where
  seqN @{MkIsCubical n} = State ()
  seqM @{MkIsCubical n} = !% \(() <| _) => (() ** \i => (i ** i))

namespace BinTreeUtils
  public export
  pairBTreeShapes : BinTreeShape -> BinTreeShape -> BinTreeShape
  pairBTreeShapes LeafS LeafS
    = LeafS
  pairBTreeShapes LeafS (NodeS ltb rtb)
    = NodeS (pairBTreeShapes LeafS ltb) (pairBTreeShapes LeafS rtb)
  pairBTreeShapes (NodeS lta rta) LeafS
    = NodeS (pairBTreeShapes lta LeafS) (pairBTreeShapes rta LeafS)
  pairBTreeShapes (NodeS lta rta) (NodeS ltb rtb)
    = NodeS (pairBTreeShapes lta ltb) (pairBTreeShapes rta rtb)

  -- needs to be checked if this is right...  some previous related code at
  -- git show adf4ad5:src/Data/Container/Applicative/Instances.idr
  public export
  pairBTreePos : {sh1, sh2 : BinTreeShape} ->
    BinTreePos (pairBTreeShapes sh1 sh2) -> (BinTreePos sh1, BinTreePos sh2)
  pairBTreePos {sh1 = LeafS, sh2 = LeafS} AtLeaf
    = (AtLeaf, AtLeaf)
  pairBTreePos {sh1 = LeafS, sh2 = (NodeS ltb rtb)} p
    = (AtLeaf, case p of
        AtNode => AtNode
        GoLeft posL => GoLeft $ snd (pairBTreePos posL)
        GoRight posR => GoRight $ snd (pairBTreePos posR))
  pairBTreePos {sh1 = (NodeS lta rta), sh2 = LeafS} p
    = (case p of
        AtNode => AtNode
        GoLeft posL => GoLeft $ fst (pairBTreePos posL)
        GoRight posR => GoRight $ fst (pairBTreePos posR), AtLeaf)
  pairBTreePos {sh1 = (NodeS lta rta), sh2 = (NodeS ltb rtb)} p
    = case p of
        AtNode => (AtNode, AtNode)
        GoLeft posL => let (pl, pr) = pairBTreePos posL
                       in (GoLeft $ pl, GoLeft $ pr)
        GoRight posR => let (pl, pr) = pairBTreePos posR
                       in (GoRight $ pl, GoRight $ pr)
  
  public export
  pairBTreeLeafPos : {sh1, sh2 : BinTreeShape} ->
    BinTreePosLeaf (pairBTreeShapes sh1 sh2) ->
    (BinTreePosLeaf sh1, BinTreePosLeaf sh2)
  pairBTreeLeafPos {sh1 = LeafS, sh2 = LeafS} AtLeaf
    = (AtLeaf, AtLeaf)
  pairBTreeLeafPos {sh1 = LeafS, sh2 = (NodeS ltb rtb)} p
    = (AtLeaf, case p of
        GoLeft posL => GoLeft $ snd (pairBTreeLeafPos posL)
        GoRight posR => GoRight $ snd (pairBTreeLeafPos posR))
  pairBTreeLeafPos {sh1 = (NodeS lta rta), sh2 = LeafS} p
    = (case p of
        GoLeft posL => GoLeft $ fst (pairBTreeLeafPos posL)
        GoRight posR => GoRight $ fst (pairBTreeLeafPos posR), AtLeaf)
  pairBTreeLeafPos {sh1 = (NodeS lta rta), sh2 = (NodeS ltb rtb)} p
    = case p of
        GoLeft posL => let (pl, pr) = pairBTreeLeafPos posL
                       in (GoLeft $ pl, GoLeft $ pr)
        GoRight posR => let (pl, pr) = pairBTreeLeafPos posR
                       in (GoRight $ pl, GoRight $ pr)

export
TensorMonoid BinTree where
  tensorN = State LeafS
  tensorM = !% \(sh1, sh2) => (pairBTreeShapes sh1 sh2 ** pairBTreePos)

export
TensorMonoid BinTreeLeaf where
  tensorN = State LeafS
  tensorM = !% \(sh1, sh2) => (pairBTreeShapes sh1 sh2 ** pairBTreeLeafPos)

-- Note, there is no TensorMonoid/Applicative instance for BinTreeNode
-- There exists one for infinite trees, but not finite ones

reduce : {c : Cont} -> Algebra (Ext c) a =>
  Ext c a -> Ext Scalar a
reduce x = () <| \() => reduce x

public export
dotWith : {cont : Cont} -> TensorMonoid cont => Algebra (Ext cont) c =>
  (a -> b -> c) ->
  Ext cont a -> Ext cont b -> Ext Scalar c
dotWith f ea eb = reduce $ uncurry f <$> liftA2Ext ea eb