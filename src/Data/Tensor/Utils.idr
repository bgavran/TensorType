module Data.Tensor.Utils

import Data.Nat -- Add import for Cast
import System.Random

import Data.Tensor.Tensor
import Data.Container.SubTerm
import Misc


{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
This file defines common tensor utility functions
Mirrors those found in numpy/pytorch, and includes:
* zeros
* ones
* range
* size
* flatten
* oneHot
and the corresponding container variants, when they exist.

Naming needs to be made more consistent

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

namespace CommonNames
  public export
  CScalar : (dtype : Type) -> Type
  CScalar dtype = CTensor [] dtype

  public export
  CVector : (c : Cont) -> (dtype : Type) -> Type
  CVector c dtype = CTensor [c] dtype
  
  public export
  CMatrix : (row, col : Cont) -> (dtype : Type) -> Type
  CMatrix row col dtype = CTensor [row, col] dtype

  public export
  Scalar : (dtype : Type) -> Type
  Scalar dtype = Tensor [] dtype

  public export
  Vector : (n : Nat) -> (dtype : Type) -> Type
  Vector n dtype = Tensor [n] dtype
  
  public export
  Matrix : (row, col : Nat) -> (dtype : Type) -> Type
  Matrix row col dtype = Tensor [row, col] dtype

namespace ZerosOnes
  public export
  zeros : Num a => {shape : List Cont} -> AllApplicative shape => 
    CTensor shape a
  zeros = tensorReplicate (fromInteger 0)
  
  public export
  ones : Num a => {shape : List Cont} -> AllApplicative shape => 
    CTensor shape a
  ones = tensorReplicate (fromInteger 1)


  ||| An identity matrix with True on the diagonal and False elsewhere
  public export
  identityBool : {n : Nat} -> Tensor [n, n] Bool
  identityBool = outerWith (==) (positions {sh=()}) (positions {sh=()})

  ||| An identity matrix with ones on the diagonal and zeros elsewhere
  ||| Analogous to numpy.eye
  public export
  identity : Num a => {n : Nat} -> Tensor [n, n] a
  identity = fromBool <$> identityBool

namespace Range
  {----- 
  This one is interesting, as in the cubical case it's effectively a version of 'tabulate' from Naperian functors.
  The cubical version is implemented first, and it's possible that a more general version of rangeA can be defined for container based tensors, possibly by tabulating contents of each shape respectively
  -----}
  ||| Separate implementation for the case of one vs two arguments
  ||| This allows the typechecker to more easily match the right implementation at call sites, as with only TwoArg implementation the following doesn't compile:
  ||| a = Tensor [6] Double
  ||| a = arange
  ||| Otoh, we preclude calling this without a type specified
  namespace OneArg
    ||| A range of numbers [0, stop>
    public export
    arange : {stop : Nat} ->
      Cast Nat a => Tensor [stop] a
    arange {stop} = ># (cast . finToNat) <$> positions {f=Vect (stop)}

  namespace TwoArgs
    ||| A range of numbers [start, stop>
    public export
    arange : {default 0 start : Nat} -> {stop : Nat} ->
      Cast Nat a => Tensor [minus stop start] a
    arange {start} {stop} = >#
      (cast . (+start) . finToNat) <$> positions {f=Vect (minus stop start)}

  ||| Here the type 'a' has to somehow be dependent on the shape?
  rangeA : CTensor ?whatShape ?whatType

namespace Flip
  ||| Reverse a tensor along a given axis
  public export
  flip : (axis : Fin (length shape)) -> Tensor shape a -> Tensor shape a

namespace Size
  {----- 
  Can we measure the size of a tensor of containers?
  Likely need to impose an additional constraint that the set of positions is enumerable
  -----}
  ||| Number of elements in a non-cubical tensor
  public export
  cSize : {shape : List Cont} -> CTensor shape a -> Nat
  
  ||| Number of elements in a cubical tensor
  public export
  size : {shape : List Nat} -> (0 _ : Tensor shape a) -> Nat
  size {shape} _ = prod shape

namespace Flatten
  ||| Flatten a non-cubical tensor into a list
  ||| Requires that we have Foldable on all the components
  ||| In general we won't know the number of elements of a non-cubical tensor at compile time
  public export
  cFlatten : Foldable (CTensor shape) => CTensor shape a -> List a
  cFlatten = toList
  
  ||| Flatten a cubical tensor into a vector
  ||| Number of elements is known at compile time
  ||| Can even be zero, if any of shape elements is zero
  flatten : {shape : List Nat} ->
    Tensor shape a -> Vect (prod shape) a
  flatten t = ?flatten_rhs

  -- This was the old version with a strided implementation
  -- flatten : {shape : List Nat} ->
  --   Tensor shape a -> Vect (prod shape) a
  -- flatten (ToCubicalTensor (TS ex)) = extract <$> toVect ex

namespace Max
  ||| Maximum value in a tensor
  ||| Returns Nothing if the tensor is empty
  public export
  max : Foldable (CTensor shape) => Ord a =>
    CTensor shape a -> Maybe a
  max = maxInList . cFlatten

  public export
  maxT : Foldable (CTensor shape) => Ord a =>
    CTensor shape a -> CTensor [Maybe] a
  maxT t = ># max t
  
  
  -- TODO Fix for strided
  -- max {shape = []} t = maxA (FromCubicalTensor t)
  -- max {shape = (s :: ss)} t = let tt = maxA (FromCubicalTensor t) in ?max_rhs_1
  -- maxA maxA . FromCubicalTensor  -- t = let tt = FromCubicalTensor t in maxA tt
  --maxA . FromCubicalTensor

namespace OneHot
  -- oneHotA : Num a => {c : Cont} -> (i : c .Shp) -> CTensor [c] a

  public export
  oneHot : Num a => {n : Nat} ->
    (i : Fin n) -> Tensor [n] a
  oneHot i = set (zeros {shape=[Vect n]}) [i] 1 


namespace Triangular
  public export
  cTriBool : {c : Cont} ->
    (ip : InterfaceOnPositions c MOrd) =>
    AllApplicative [c] =>
    (sh : c.Shp) -> CTensor [c, c] Bool
  cTriBool {ip = MkI {p}} sh
    = let cPositions = positions {sh=sh}
          pp : MOrd (c.Pos sh) := p sh
      in outerWith (flip isSubTerm) cPositions cPositions

  -- public export
  -- triA : Num a => {c : Cont} ->
  --   (ip : InterfaceOnPositions c MOrd) =>
  --   AllApplicative [c] =>
  --   (sh : c.Shp) -> CTensor [c, c] a
  -- triA sh = fromBool <$> cTriBool sh

  public export
  triBool : {n : Nat} -> Tensor [n, n] Bool
  triBool = cTriBool ()

  ||| A matrix with ones on and below the diagonal, and zeros elsewhere
  ||| Analogous to numpy.tri
  public export
  tri : Num a => {n : Nat} -> Tensor [n, n] a
  tri = fromBool <$> triBool

  ||| Lower triangular part of a matrix. Elements above the diagonal are set to
  ||| zero. Analogous to numpy.tril
  public export
  lowerTriangular : Num a => {n : Nat} -> Tensor [n, n] a -> Tensor [n, n] a
  lowerTriangular = (* tri)

  ||| Upper triangular part of a matrix. Elements below the diagonal are set to
  ||| zero. Analogous to numpy.triu(.., k=1)
  public export
  upperTriangular : Num a => {n : Nat} -> Tensor [n, n] a -> Tensor [n, n] a
  upperTriangular t = t * ((fromBool . not) <$> triBool)

  ||| Fill the elements of a tensor `t` with `fill` where `mask` is True
  public export
  maskedFill : {shape : List Cont} -> Num a => AllApplicative shape =>
    (t : CTensor shape a) ->
    (mask : CTensor shape Bool) ->
    (fill : a) ->
    CTensor shape a
  maskedFill t mask fill = liftA2Tensor mask t <&>
    (\(maskVal, tVal) => if maskVal then fill else tVal)


namespace Misc
  public export
  sum : {shape : List Cont} ->
    Algebra (CTensor shape) a =>
    CTensor shape a -> a
  sum = reduce

  public export
  mean : {shape : List Nat} ->
    Cast Nat a =>
    Fractional a => 
    Algebra (Tensor shape) a =>
    Tensor shape a -> a
  mean t = reduce t / cast (size t)

  public export
  variance : {n : Nat} -> Neg a => Fractional a => Cast Nat a =>
    Tensor [n] a -> a
  variance t =
    let inputMinusMean = t - pure (mean {shape=[n]} t)
    in mean {shape=[n]} (inputMinusMean * inputMinusMean)



namespace Traversals
  public export
  inorder : CTensor [BinTreeNode] a -> CTensor [List] a
  inorder = extToVector . extMap BinTreeNode.inorder . vectorToExt

namespace Random
  public export
  Random a =>
  Applicative (Tensor shape) => -- again, should we need this?
  Traversable (Tensor shape) =>
  Random (Tensor shape a) where
    randomIO = sequence (pure randomIO)
   
    randomRIO (lo, hi) = sequence $ randomRIO <$> liftA2 lo hi 

-- Idris can't find the parametric randomIO interface so reimpementing here 
public export
random : Num a => Random a => HasIO io =>
  (shape : List Nat) ->
  Applicative (Tensor shape) => 
  Traversable (Tensor shape) => 
  io (Tensor shape a)
random shape = sequence $ pure $ randomRIO (0, 1)

tt : Traversable (Vect 2)
tt = %search

ttt : Traversable (Ext (Vect 2))
ttt = %search

tttt : Traversable (Tensor [2])
tttt = %search

testRand : IO (Tensor [2, 3] Double)
testRand = do 
  t <- random [2,3]
  printLn $ show t
  pure t

testRand2 : IO (Tensor [5] Double)
testRand2 = random [5]

testRand3 : IO Unit
testRand3 = randomIO
