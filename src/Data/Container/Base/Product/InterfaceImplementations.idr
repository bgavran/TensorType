module Data.Container.Base.Product.InterfaceImplementations

import Data.Container.Base.Object.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Product.Definitions
import Data.Container.Base.Concrete.Definition

import Data.Container.Base.Object.Instances
import Data.Container.Base.Extension.Instances
import Data.Container.Base.Morphism.Instances
import Data.Container.Base.Product.Interfaces
import Data.Container.Base.Concrete.Instances

import Data.Container.Base.TreeUtils

import Data.Fin.Split
import Data.Layout
import Data.Algebra


export
TensorMonoid Maybe where
  tensorN = !% \() => (True ** \_ => ())
  -- for multiplication, only true if both b1 and b2 are True
  tensorM = !% \(b1, b2) => (b1 && b2 ** \bb => ?todoFinish)


-- TODO Either Applicative?

||| Corresponds to the Applicative instance in `Prelude.Types`
||| It behaves like a cartesian product, but compared to `Prelude.Types`
||| applicative this is layout-aware
export
TensorMonoid List where
  tensorN = !% \() => (1 ** const ())
  tensorM = !% \(n, m) => (n * m ** splitFinProd DefaultLayoutOrder) 

{--
It is usually said that List has two applicative structures: one defined above,
and another one defined by `zipList` (Section 3 of 
https://www.staff.city.ac.uk/~ross/papers/Constructors.pdf). However, such
a definition relies on the laziness of the underlying programming language
and implicitly recast the type not to `List` but `CoList` (sometimes called 
`LazyList`), i.e. a list with potentially infinite number of elements. This permits defining `pure` and showing that applicative laws hold. However, since Idris is a strict language, List is not equal to CoList, and we cannot lawfully
make `List` an applicative functor. More precisely, the following is not a valid applicative instance, because unital laws do not hold:

Applicative List where
  pure a = [a]
  fs <*> xs = uncurry ($) <$> listZip fs xs
--}   


||| Follows Applicative instance in `Data.Vect`, i.e. zip
export
TensorMonoid (Vect n) where
  tensorN = !% \() => (() ** const ())
  tensorM = !% \((), ()) => (() ** \i => (i, i))

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
  tensorN = !% \() => (LeafS ** \_ => ())
  tensorM = !% \(sh1, sh2) => (pairBTreeShapes sh1 sh2 ** pairBTreePos)


export
TensorMonoid BinTreeLeaf where
  tensorN = !% \() => (LeafS ** \_ => ())
  tensorM = !% \(sh1, sh2) => (pairBTreeShapes sh1 sh2 ** pairBTreeLeafPos)

-- Note, there is no TensorMonoid/Applicative instance for BinTreeNode
-- There exists one for infinite trees, but not finite ones