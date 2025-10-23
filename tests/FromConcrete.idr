module FromConcrete

import Data.Container

{-----------
Tests of functionality to construct a tensor from a concrete type
-----------}

lst : List' Int
lst = fromConcreteTy [1,2,3,4,5]

vct : Vect' 7 Int
vct = fromConcreteTy [1,2,3,4,5,6,70]

failing
  vct2 : (Vect 6) `fullOf` Int
  vct2 = fromConcreteTy [1,2,3,4,5,6,7]

bt : BinTree' Char
bt = fromConcreteTy (Node 'a' (Leaf 'b') (Leaf 'c'))

t11 : Tensor' [BinTree] Int
t11 = fromConcreteTy ?t1rhs

tg : Tensor' [Vect 5] Int
tg = pure 9

tgg : Tensor' [Vect 5, Vect 5] Int
tgg = pure 10

waitt : Tensor' [List] Int
waitt = fromConcreteTy ?waittrhs

tens : Tensor' [Vect 3, List] Double
tens = fromConcreteTy [[1,2,3], [4,5,6,6,7], [1299]]

vvv : Tensor' [Vect 2, Vect 4] Int
vvv = ?vvvrhs -- fromConcreteTy [[1,2,3,4], [21,22,23,24]]