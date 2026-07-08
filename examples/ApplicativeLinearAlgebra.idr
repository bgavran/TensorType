module ApplicativeLinearAlgebra

import Data.Tensor

v1 : Tensor ["vect" ~~> 4] Double
v1 = ># [1,2,3,4]

v2 : Tensor ["vect" ~~> 4] Double
v2 = ># [100, 200, 300, 400]

v3 : Tensor ["vect2" ~~> 2] Double
v3 = ># [100, 1000]

l1 : Tensor ["list" ~> List] Double
l1 = ># [1,2,3,4]

l2 : Tensor ["list" ~> List] Double
l2 = ># [100, 1000]

t1 : Tensor ["t" ~> BinTreeLeaf] Double
t1 = ># Node' (Leaf 100) (Leaf 1000)

t2 : Tensor ["t" ~> BinTreeLeaf] Double
t2 = ># Node' (Node' (Leaf 1) (Leaf 2))
              (Node' (Leaf 3) (Leaf 4))