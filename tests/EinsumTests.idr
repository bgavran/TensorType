module Tests.EinsumTests

import Data.Either
import Decidable.Equality

import Data.Tensor.Einsum.EinsumExpr
import Misc


----------------------------------------
----- Tests
----------------------------------------

test0 : IsRight (parseEinsumString "ij,ij->")
test0 = %search

test1 : IsRight (parseEinsumString "ij,jk->ik")
test1 = %search

test2 : IsRight (parseEinsumString "ijk->")
test2 = %search

test3 : IsRight (parseEinsumString "i,j->ij")
test3 = %search

test4 : IsLeft (parseEinsumString "invalid")
test4 = %search

test5 : IsLeft (parseEinsumString "")
test5 = %search

test6 : IsLeft (parseEinsumString "123,456->789")
test6 = %search

test7 : IsRight (parseEinsumString "i,,j->ij")
test7 = %search 

test8 : IsLeft (parseEinsumString "i,j->123")
test8 = %search 

test9 : IsLeft (parseEinsumString "i->j->k")
test9 = %search

test10 : IsLeft (parseEinsumString "i@j->@i")
test10 = %search