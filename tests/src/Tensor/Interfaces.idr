module Tensor.Interfaces

import Hedgehog

import Data.Tensor


namespace Num
  ||| We should always be able to find a numeric instance for a tensor made out
  ||| of containers which are tensor monoids
  numFoundApplicative : {shape : TensorShape rank} ->
    Num a => AllC TensorMonoid shape => Num (Tensor shape a)
  numFoundApplicative = %search
  
  failing
    numNotFoundGeneral : {shape : TensorShape rank} ->
      Num a => Num (Tensor shape a)
    numNotFoundGeneral = %search

namespace Neg
  negFoundApplicative : {shape : TensorShape rank} ->
    Neg a => AllC TensorMonoid shape => Neg (Tensor shape a)
  negFoundApplicative = %search
  
  failing
    negNotFound : {shape : TensorShape rank} ->
      Neg a => Neg (Tensor shape a)
    negNotFound = %search


||| This test should trivially pass if everything above it compiles
export
interfaceTests : Group
interfaceTests = MkGroup "Interface tests"
  [ ("Interface tests", property1 success) ]



-- todo testing for various other interfaces
-- eq (this should especially be done for pure containers, and things involving Ext)
-- foldable
-- traversable
-- fromConcrete (as well as valdiation that the roundtrip answer is same)