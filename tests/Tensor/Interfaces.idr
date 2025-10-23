module Tensor.Interfaces

import Data.Tensor


----------------------------------------------
-- Initialisation of some tensors we will use
----------------------------------------------

-- Cubical tensors
ct0 : Tensor [3, 4] Double
ct0 = fromConcreteTy [ [0, 1, 2, 3]
                     , [4, 5, 6, 7]
                     , [8, 9, 10, 11]]

ct1 : Tensor [6] Double
ct1 = fromConcreteTy [0,1,2,3,4,5]

ct2 : Tensor [2, 3] Double
ct2 = fromConcreteTy [ [0, 1, 2]
                    , [3, 4, 5]]


-- Generalised tensors
t0 : CTensor [BinTree] Double
t0 = fromConcreteTy $ Node 3 (Node 2 (Leaf 1) (Leaf 2)) (Leaf 3)

t1 : CTensor [BinTree, Vect 2] Double
t1 = fromConcreteTy $ Node [4,1] (Node [17, 4] (Leaf [100, 101]) (Leaf [102, 103])) (Leaf [15, (-13)])

t2 : CTensor [Vect 2, BinTreeLeaf] Double
t2 = fromConcreteTy $ [Node' (Leaf 4) (Leaf 3), Node' (Leaf 10) (Leaf 100)]

namespace Functor
  a : Tensor [3, 4] Double
  a = ct0 <&> (+7)
