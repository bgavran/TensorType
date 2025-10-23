module Tests.TensorAccess

import Data.Tensor

strideTest1 : strides [2,3,4,5] = [60, 20, 5, 1]
strideTest1 = Refl

strideTest2 : strides [3,4,5] = [20, 5, 1]
strideTest2 = Refl

strideTest3 : strides [4, 5] = [5, 1]
strideTest3 = Refl

indexCountExample1 : indexCount {shape = [3, 4, 5]} [0, 3, 4] = 19 -- : Fin 60
indexCountExample1 = Refl
    
indexCountExample2 : indexCount {shape = [3, 4, 5]} [0, 2, 1] = 11 -- : Fin 60
indexCountExample2 = Refl
    
indexCountExample3 : indexCount {shape = [3, 4, 5]} [1, 2, 3] = 33 -- : Fin 60
indexCountExample3 = Refl
    
indexCountExample4 : indexCount {shape = [3, 4]} [0, 1] = 1 -- : Fin 12
indexCountExample4 = Refl
    

failing
  failIndex : Fin 12
  failIndex = indexCount {shape = [3, 4]} [10, 20]