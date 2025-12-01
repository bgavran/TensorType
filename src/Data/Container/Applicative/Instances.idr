module Data.Container.Applicative.Instances

import Data.Fin
import Data.DPair

import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Container.Extension.Definition
import Data.Container.Extension.Instances
import Data.Container.Concrete.Definition
import Data.Container.Concrete.Instances
import Data.Container.Applicative.Definition

import Misc

%hide Prelude.(<|)

namespace ListApplicative
  ||| This arises out of the Prelude.Types List applicative 
  ||| Effectively it behaves like a cartesian product
  public export 
  Applicative List' where
    pure = fromList . pure
    fs <*> vs = fromList $ toList fs <*> toList vs

  ||| Note that usually it is said that List has two applicative structures
  ||| one defined above, and another one defined by `zipList` (Section 3 of 
  ||| https://www.staff.city.ac.uk/~ross/papers/Constructors.pdf).
  ||| However, note that such definitions rely on implciit laziness of the
  ||| underlying language, and recast the type not to `List` but `CoList` (or
  ||| usually called `LazyList`), i.e. a list with potentially infinite number
  ||| of elements. 
  ||| This allows them to define the `pure` and show that applicative laws hold.
  ||| However, since we are working in Idris which is strict, this does not hold
  ||| and we cannot lawfully make `List` an applicative functor in such a way.
  ||| For instance, this is not a valid applicative instance, because unital 
  ||| laws do not hold:
  |||
  ||| Applicative List where
  |||   pure a = [a]
  |||   fs <*> xs = uncurry ($) <$> listZip fs xs



namespace BinTreeLeafApplicative
  public export
  liftA2BBinTreeLeaf' : BinTreeLeaf' a -> BinTreeLeaf' b -> BinTreeLeaf' (a, b)
  liftA2BBinTreeLeaf' t1 t2 = fromBinTreeLeaf $
    liftA2BinTreeLeaf (toBinTreeLeaf t1) (toBinTreeLeaf t2)

  public export
  Applicative BinTreeLeaf' where
    pure a = fromBinTreeLeaf (Leaf a)
    fs <*> vs = uncurry ($) <$> liftA2BBinTreeLeaf' fs vs 


-- no applicative instance for BinTreeNode
-- there is one for infinite trees

namespace BinTreeApplicative
  public export
  liftA2BinTree' : BinTree' a -> BinTree' b -> BinTree' (a, b)
  liftA2BinTree' t1 t2 = fromBinTreeSame $
    liftA2BinTreeSame (toBinTreeSame t1) (toBinTreeSame t2)

  public export
  Applicative BinTree' where
    pure a = fromBinTreeSame (Leaf a)
    fs <*> vs = uncurry ($) <$> liftA2BinTree' fs vs


namespace MaybeApplicative
  public export
  liftA2Maybe' : Maybe' a -> Maybe' b -> Maybe' (a, b)
  liftA2Maybe' m1 m2 = fromConcreteTy $
    liftA2 (toConcreteTy m1) (toConcreteTy m2)

  public export
  Applicative Maybe' where
    pure a = fromConcreteTy $ Just a
    fs <*> vs = uncurry ($) <$> liftA2Maybe' fs vs

namespace ApplicativeInstances
  ||| Container with a single thing
  public export
  Scalar : ContA
  Scalar = (#) Scalar
  
  ||| Product
  public export
  Pair : ContA
  Pair = (#) Pair

  -- TODO applicatives for these commented out types?
  -- ||| Coproduct
  -- public export
  -- Either : ContA
  -- Either = (#) Either

  -- ||| +1  
  public export
  Maybe : ContA
  Maybe = (#) Maybe
  
  public export
  List : ContA
  List = (#) List
  
  ||| Container of n things 
  ||| Every natural number n corresponds to a Vect n, which is applicative
  ||| Used in cubical tensors whose shapes are defined by lists of natural numbers
  public export
  Vect : Nat -> ContA
  Vect n = (#) (Vect n)

  ||| Container of an infinite number of things
  public export
  Stream : ContA
  Stream = (#) Stream

  ||| Binary trees with data stored at both nodes and leaves
  public export
  BinTree : ContA
  BinTree = (#) BinTree
  
  ||| Binary trees with data stored at leaves
  public export
  BinTreeLeaf : ContA
  BinTreeLeaf = (#) BinTreeLeaf

  public export
  Tensor : List ContA -> Cont
  Tensor cs = Tensor (GetC <$> cs)
  
  public export
  composeExtensionsA : List ContA -> Type -> Type
  composeExtensionsA cs = composeExtensions (GetC <$> cs)

  ||| Generalisation of Rose trees with a container
  ||| of subtrees (container whose extension is applicative)
  ||| instead of a list of a subtrees
  public export
  ApplicativeRoseTree : ContA -> Cont
  ApplicativeRoseTree c = (t : RoseTreeShape c) !> RoseTreePos c t

  ||| Same as above, but with data stored at nodes
  public export
  ApplicativeRoseTreeNode : ContA -> Cont
  ApplicativeRoseTreeNode c = (t : RoseTreeShape c) !> RoseTreePosNode c t

  ||| Same as above, but with data stored at leaf
  public export
  ApplicativeRoseTreeLeaf : ContA -> Cont
  ApplicativeRoseTreeLeaf c = (t : RoseTreeShape c) !> RoseTreePosNode c t


  ||| Rose tree here means ApplicativeRoseTree List
  namespace ContDefs
    ||| Rose trees with data stored at both nodes and leaves
    public export
    RoseTree : Cont
    RoseTree = ApplicativeRoseTree List
  
    ||| Rose trees with data stored at nodes
    public export
    RoseTreeNode : Cont
    RoseTreeNode = ApplicativeRoseTreeNode List
  
    ||| Rose trees with data stored at leaves
    public export
    RoseTreeLeaf : Cont
    RoseTreeLeaf = ApplicativeRoseTreeLeaf List


namespace ExtensionsOfApplicativeExamples
  ||| Isomorphic to Data.Tree.ApplicativeRoseTree (TODO)
  public export
  ApplicativeRoseTree' : (c : ContA) -> Type -> Type
  ApplicativeRoseTree' c = Ext (ApplicativeRoseTree c)

  public export
  ApplicativeRoseTreeNode' : (c : ContA) -> Type -> Type
  ApplicativeRoseTreeNode' c = Ext (ApplicativeRoseTreeNode c)

  public export
  ApplicativeRoseTreeLeaf' : (c : ContA) -> Type -> Type
  ApplicativeRoseTreeLeaf' c = Ext (ApplicativeRoseTreeLeaf c)


  ||| Isomorphic to Data.Tree.RoseTree
  public export
  RoseTree' : Type -> Type
  RoseTree' = Ext RoseTree

  ||| Isomorphic to Data.Tree.RoseTreeNode (TODO)
  public export
  RoseTreeNode' : Type -> Type
  RoseTreeNode' = Ext RoseTreeNode

  ||| Isomorphic to Data.Tree.RoseTreeLeaf (TODO)
  public export
  RoseTreeLeaf' : Type -> Type
  RoseTreeLeaf' = Ext RoseTreeLeaf


  -- TODO
  public export
  Applicative (Ext (ApplicativeRoseTree c)) where
    pure a = ?applicativeRoseTree_pure
    fs <*> xs = ?applicativeRoseTree_ap

  public export
  ApplicativeRoseTree : ContA -> ContA
  ApplicativeRoseTree c = (#) (ApplicativeRoseTree c)



namespace ConversionFunctions
  public export
  fromRoseTreeSame : RoseTreeSame a -> RoseTree' a
  fromRoseTreeSame (Leaf a) = LeafS <| \_ => a
  fromRoseTreeSame (Node a rts) =
    let t = fromRoseTreeSame <$> fromList rts
    in NodeS (shapeExt <$> t) <| \case
      AtNode => a
      SubTree ps posSt =>
        let rw1 : (shapeExt t = shapeExt (shapeExt <$> t)) := sym (mapShapeExt t)
            rw2 : (shapeExt (index t (rewrite sym (mapShapeExt {f=shapeExt} t) in ps)) = index (shapeExt <$> t) ps) := mapIndexCont {c=List} {f=shapeExt} t ps
        in index
        (index t (rewrite rw1 in ps))
        (rewrite rw2 in posSt)
        -- for some reason all the explicit type annotations above are needed
        -- to convince the typechecker

  public export
  toRoseTreeSame : RoseTree' a -> RoseTreeSame a
  toRoseTreeSame (LeafS <| contentAt) = Leaf (contentAt AtLeaf)
  toRoseTreeSame (NodeS (len <| content) <| contentAt)
    = Node (contentAt AtNode)
           (toList $ toRoseTreeSame 
                  <$> (\i => content i <| contentAt . SubTree i)
                  <$> positionsCont)


public export
FromConcrete RoseTree where
  concreteType = RoseTreeSame
  concreteFunctor = %search
  fromConcreteTy = fromRoseTreeSame
  toConcreteTy = toRoseTreeSame

namespace RoseTreeInstances
  -- TODO this should be superseeded by the general applicative instance above?
  public export
  liftA2RoseTree' : RoseTree' a -> RoseTree' b -> RoseTree' (a, b)
  liftA2RoseTree' t1 t2 = fromRoseTreeSame $
    liftA2RoseTreeSame (toRoseTreeSame t1) (toRoseTreeSame t2)

  public export
  Applicative RoseTree' where
    pure a = LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2RoseTree' fs vs