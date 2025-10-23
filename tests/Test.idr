module Architectures.Test

import Decidable.Equality

import Data.Tensor
import Data.Container
import Misc



namespace BasicExamples
  -- the only problem is that here we have to supply the implicit `shape` argument to `dot`?
  -- And in writing functions it gets complicated
  -- question of separating CTensor in its own datatype
  -- but also question of separating Tensor in its own datatype
  -- likely we only need to do the former
  -- first figure this out, and then do the traverse/reshape/morphism part?
  t0 : Tensor [3, 4] Double
  t0 = fromConcreteTy [ [0, 1, 2, 3]
                      , [4, 5, 6, 7]
                      , [8, 9, 10, 11]]

  public export
  t1 : Tensor [6] Double
  t1 = fromConcreteTy [1,2,3,4,5,6]

  -- TODO Reshape

  t0Sum : Tensor [3, 4] Double
  t0Sum = t0 + t0

  numericOps : Tensor [3, 4] Double
  numericOps = abs (- (t0 * t0) <&> (+7))

  dotProduct : CTensor [] Double
  dotProduct = dot t1 t1

  -- TODO indexing syntax
  indexExample : Double
  indexExample = indexC t0 [1, 2]

  t0Transposed : Tensor [4, 3] Double
  t0Transposed = transposeMatrix t0

  t0Again : CTensor [Vect 3, Vect 4] Double
  t0Again = t0

  t1Again : CTensor [Vect 6] Double
  t1Again = t1

  exList : CTensor [List] Double
  exList = fromConcreteTy [1,2,3,4,5,6,7,8]

  exList2 : CTensor [List] Double
  exList2 = fromConcreteTy [100,-200,1000]

  exTree1 : CTensor [BinTreeLeaf] Double
  exTree1 = fromConcreteTy $ Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)

  exTree2 : CTensor [BinTreeLeaf] Double
  exTree2 = fromConcreteTy $ Node' (Leaf 10) (Leaf 100)

  dotProduct2 : CTensor [] Double
  dotProduct2 = dot {shape=[BinTreeLeaf]} exTree1 exTree2

  exTree3 : CTensor [BinTreeNode, Vect 2] Double
  exTree3 = fromConcreteTy $ Node [4,1] (Node [17, 4] Leaf' Leaf') Leaf'

  exTree4 : CTensor [BinTreeNode, BinTreeLeaf, Vect 3] Double
  exTree4 = fromConcreteTy $
    Node (Node'
            (Leaf [1,2,3])
            (Leaf [4,5,6]))
      Leaf'
      (Node (Leaf [178, -43, 63]) Leaf' Leaf')

  exTree5 : CTensor [BinTreeNode] Double
  exTree5 = fromConcreteTy $ Node 3 (Node 2 (Node 1 Leaf' Leaf') Leaf') (Node 4 Leaf' Leaf')

  -- traverseTree : CTensor [List] Double
  -- traverseTree = restructure inorderBinTreeNode exTree5





namespace DerivZipper
  BinTreeD : Cont
  BinTreeD = Deriv BinTree
  
  {-
      *
     / \
    *   *
   / \
  *  *
   -}
  treeShapeExample : BinTreeShape
  treeShapeExample = NodeS (NodeS LeafS LeafS) LeafS
  
  btd : BinTreeD `fullOf` Int
  
  
  Zipper : (c : Cont) -> InterfaceOnPositions c DecEq => Type -> Type
  Zipper c a = (a, Ext (Deriv c) a)






namespace EqualityQuestions
  L1 : BinTree' Int
  L1 = fromBinTreeSame (Node 1 (Leaf 3) (Leaf 4))
  
  L2 : BinTree' Int
  L2 = fromBinTreeSame (Node 1 (Leaf 3) (Leaf 4))
  
  
  fp1 : BinTreePos (NodeS LeafS LeafS) -> Int
  fp1 (AtNode) = 1
  fp1 (GoLeft AtLeaf) = 3
  fp1 (GoRight AtLeaf) = 4
  
  fp2 : BinTreePos (NodeS LeafS LeafS) -> Int
  fp2 (AtNode) = 1
  fp2 (GoLeft AtLeaf) = 3
  fp2 (GoRight AtLeaf) = 4
  
  L3 : BinTree' Int
  L3 = (NodeS LeafS LeafS) <| fp1
  
  L4 : BinTree' Int
  L4 = (NodeS LeafS LeafS) <| fp2
  
  L5 : BinTree' Int
  L5 = (NodeS LeafS LeafS) <| \case
    AtNode => 1
    (GoLeft AtLeaf) => 3
    (GoRight AtLeaf) => 4
  
  L6 : BinTree' Int
  L6 = (NodeS LeafS LeafS) <| \case
    AtNode => 1
    (GoLeft AtLeaf) => 3
    (GoRight AtLeaf) => 4


  feq : EqExt L1 L2
  feq = %search -- MkEqExt Refl (\p => Refl)
  
  fq : L5 = L6

  DecEq (Ext c a) => Eq (Ext c a) where
    t1 == t2 = case decEq t1 t2 of 
      Yes gn => True
      No bm => False
  
  
  feeq : L1 = L2
  feeq = %search
  
  -- feeqq : Bool
  -- feeqq = L1 == L2
  
  
  Vf : Int -> Int
  Vf = \x => 1 + x
  
  Gf : Int -> Int
  Gf = \x => 1 + x
  
  
  -- Functions equal by reference, literally has to be the function defined in the same place in file (so only one exists)
  fhiiTrue : Vf = Vf
  fhiiTrue = Refl
  
  -- Can't provide proof
  thisFalse : Vf = Gf
  thisFalse = Refl






