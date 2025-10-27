module Data.Algebra

import Data.Vect

import Data.Tree
import Misc

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
This file defines the Algebra interface, which is a pragmatic implementation of
the concept of F-algebra from category theory.

It is pragmatic since it is not defined for an arbitrary category, but rather
for the vaguely defined category of Idris types and functions.

Instantiating it for 'other' categories is solved by exposing the carrier of the algebra at the type level, allow us to use interface constraints to specify
the constraints on the carrier.
This comes at the cost of needing to always specify the carrier type in the type
of every function that uses this algebra interface.
-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| Generalised sum operation
||| Categorically, an F-Algebra
public export
interface Algebra (f : Type -> Type) (0 carrier : Type)where
  constructor MkAlgebra
  reduce : f carrier -> carrier

||| In many instances below, we assume Num a defines a Rig structure on a
||| This means we assume the sum operation is both commutative and associative,
||| allowing us to define the Algebra instance for trees without any additional
||| assumptions, for instance (TODO unpack why)
namespace Instances
  public export
  Num a => Algebra List a where
    reduce = foldr (+) (fromInteger 0)

  -- Does this work for any Applicative? I think not, because in trees we have to choose an order of summation. But that might not impact things?
  -- if the sum operation is commutative, then it should not impact things
  public export
  {n : Nat} -> Num a => Algebra (Vect n) a where
    reduce = foldr (+) (fromInteger 0)
  
  ||| Summing up leaves of a tree given by the Num a structure
  ||| This assumes that Num a is a Rig structure, meaning the sum operation is
  ||| assumed to be both commutative and associative.
  ||| Otherwise we would need to be expose the data of the ordering and 
  ||| bracketing by which the summation below was performed
  public export
  Num a => Algebra BinTreeLeaf a where
    reduce (Leaf leaf) = leaf
    reduce (Node _ leftTree rightTree)
      = (reduce {f=BinTreeLeaf} leftTree) + 
        (reduce {f=BinTreeLeaf} rightTree)
  
  ||| Summing up nodes of a tree given by the Num a structure
  ||| This assumes that Num a is a Rig structure, meaning the sum operation is
  ||| assumed to be both commutative and associative.
  ||| Otherwise we would need to be expose the data of the ordering and 
  ||| bracketing by which the summation below was performed
  public export
  Num a => Algebra BinTreeNode a where
    reduce (Leaf _) = fromInteger 0
    reduce (Node node leftTree rightTree)
       = node + (reduce {f=BinTreeNode} leftTree)
              + (reduce {f=BinTreeNode} rightTree)
  
  ||| Summing up nodes and leaves of a tree given by the Num a structure
  ||| This assumes that Num a is a Rig structure, meaning the sum operation is
  ||| assumed to be both commutative and associative.
  ||| Otherwise we would need to be expose the data of the ordering and 
  ||| bracketing by which the summation below was performed
  public export
  Num a => Algebra BinTreeSame a where
    reduce (Leaf leaf) = leaf
    reduce (Node node leftTree rightTree)
      = node + (reduce {f=BinTreeSame} leftTree)
            + (reduce {f=BinTreeSame} rightTree)
  
  -- public export
  -- [usualSum] Num a => Applicative f => Algebra BinTreeSame (f a) where
  --   reduce (Leaf leaf) = leaf
  --   reduce (Node node leftTree rightTree)
  --     = let lt = reduce {f=BinTreeSame} leftTree 
  --           rt = reduce {f=BinTreeSame} rightTree
  --       in (uncurry (+)) <$> (liftA2 lt rt) 
  
  -- can be simplified by uncommenting the Num (f a) instance in Num.idr
  public export
  [usualSumLeaf] Num a => Applicative f => Algebra BinTreeLeaf (f a) where
    reduce (Leaf leaf) = leaf
    reduce (Node node leftTree rightTree)
      = let lt = reduce {f=BinTreeLeaf} leftTree 
            rt = reduce {f=BinTreeLeaf} rightTree
        in (uncurry (+)) <$> (liftA2 lt rt) 
  
  
  public export
  Num a => Algebra RoseTreeSame a where
    reduce (Leaf x) = x
    reduce (Node x subTrees)
      = x + reduce ((reduce {f=RoseTreeSame}) <$> subTrees)


  -- public export
  -- [appSum] {shape : Vect n Nat} -> 
  -- Num a => Applicative f =>
  -- Algebra (TensorA shape) (f a) using applicativeNum where
  --   reduce (TZ val) = val
  --   reduce (TS xs) = reduce (reduce <$> xs)
  -- 
  -- aa : Algebra (TensorA [2]) (TensorA [3] a) => a


namespace Initial
  ||| Initial algebra for an endofunctor
  public export
  data Initial : (f : Type -> Type) -> Type where
    ||| One part of the isomorphism
    In : f (Initial f) -> Initial f
  
  ||| Second part of the isomorphism 
  public export
  Out : Initial f -> f (Initial f)
  Out (In r) = r
  
  public export
  cata : Functor f =>
    Algebra f a -> (Initial f -> a)
  cata (MkAlgebra g) rs = g $ cata (MkAlgebra g) <$> Out rs 