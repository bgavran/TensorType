module Tensor.Contractions

import Hedgehog

import Data.Tensor

A : Axis
A = "a" ~~> 2

B : Axis
B = "b" ~~> 2

C : Axis
C = "c" ~~> 2

I : Axis
I = "i" ~~> 3

J : Axis
J = "j" ~~> 4

W : Axis
W = "w" ~~> 6

F : Axis
F = "f" ~~> 12

v1 : Tensor [I] Integer
v1 = ># [1, 2, 3]

v2 : Tensor [I] Integer
v2 = ># [4, 5, 6]

u2 : Tensor [A] Integer
u2 = ># [1, 2]

u3 : Tensor [I] Integer
u3 = ># [3, 4, 5]

m1 : Tensor [A, B] Integer
m1 = ># [ [1, 2]
        , [3, 4] ]

m2 : Tensor [B, C] Integer
m2 = ># [ [5, 6]
        , [7, 8] ]

m3 : Tensor [C, B] Integer
m3 = ># [ [5, 6]
        , [7, 8] ]

t34 : Tensor [I, J] Integer
t34 = ># [ [1, 2, 3, 4]
         , [5, 6, 7, 8]
         , [9, 10, 11, 12] ]

t12 : Tensor [F] Integer
t12 = ># [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

export
contractionsGroup : Group
contractionsGroup = MkGroup "Tensor contractions"
  [ ("Full reduction sums all entries", property1 $
      reduce t34 === 78)
  , ("Dot product of vectors", property1 $
      dot v1 v2 === embed 32)
  , ("Dot product of matrices (full contraction)", property1 $
      dot t34 t34 === embed 650)
  , ("Outer product", property1 $
      outer u2 u3 === ># [ [3, 4, 5]
                         , [6, 8, 10] ])
  , ("Matrix-vector product (row sums)", property1 $
      matrixVectorProduct t34 ones === ># [10, 26, 42])
  , ("Vector-matrix product (column sums)", property1 $
      vectorMatrixProduct u2 m1 === ># [7, 10])
  , ("Matrix multiplication ab,bc->ac", property1 $
      matMul m1 m2 === ># [ [19, 22]
                          , [43, 50] ])
  , ("Matrix multiplication ab,cb->ca", property1 $
      matrixMatrixProduct m1 m3 === ># [ [17, 39]
                                       , [23, 53] ])
  , ("Reshape flattens row-major", property1 $
      the (Tensor [F] Integer) (reshape t34) === t12)
  , ("Reshape round-trips", property1 $
      the (Tensor [I, J] Integer) (reshape t12) === t34)
  , ("Reshape to a different rank-2 shape", property1 $
      the (Tensor [A, W] Integer) (reshape t12)
        === ># [ [1, 2, 3, 4, 5, 6]
               , [7, 8, 9, 10, 11, 12] ])
  ]
