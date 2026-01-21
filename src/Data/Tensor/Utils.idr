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
  Scalar : (a : Type) -> Type
  Scalar a = Tensor [] a

  public export
  Vector : (c : Axis) -> (a : Type) -> Type
  Vector c a = Tensor [c] a
  
  public export
  Matrix : (row, col : Axis) -> AxesConsistent [row, col] => (a : Type) -> Type
  Matrix row col a = Tensor [row, col] a

namespace ZerosOnes
  public export
  zeros : Num a => {shape : Vect rank Axis} ->
    AxesConsistent shape =>
    All TensorMonoid (conts shape) => 
    Tensor shape a
  zeros = tensorReplicate (fromInteger 0)

  public export
  ones : Num a => {shape : Vect rank Axis} ->
    AxesConsistent shape =>
    All TensorMonoid (conts shape) => 
    Tensor shape a
  ones = tensorReplicate (fromInteger 1)

  ||| Todo is it possible to do this without pattern matching like this? 
  ||| An identity matrix with True on the diagonal and False elsewhere
  public export
  identityBool : {0 c : Axis} -> IsCubical c =>
    Tensor [c, c] Bool
  identityBool @{MkIsCubical _ n}
    = outerWith (==) (positions {sh=()}) (positions {sh=()})

  ||| An identity matrix with ones on the diagonal and zeros elsewhere
  ||| Analogous to numpy.eye
  public export
  identity : {0 c : Axis} -> IsCubical c =>
    Num a => Tensor [c, c] a
  identity @{MkIsCubical _ n} = fromBool <$> identityBool

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
    arange : {0 stop : Axis} -> IsCubical stop =>
      Cast Nat a => Tensor [stop] a
    arange @{MkIsCubical _ n} = ># (cast . finToNat) <$> positions {f=Vect n}

  namespace TwoArgs
    ||| A range of numbers [start, stop>
    public export
    arange : {0 start : Axis} -> {0 stop : Axis} -> {result : AxisName} ->
      (cStart : IsCubical start) => (cStop : IsCubical stop) =>
      Cast Nat a => Tensor [result ~~> minus (dim stop) (dim start)] a
    arange {cStart=(MkIsCubical _ n)} {cStop=(MkIsCubical _ m)}
      = ># (cast . (+n) . finToNat) <$> positions {f=Vect (minus m n)}

namespace Flip
  ||| Reverse a tensor along a given axis
  public export
  flip : {shape : Vect rank Axis} ->
    AxesConsistent shape =>
    (axis : Fin rank) ->
    IsCubical (index axis shape) =>
    Tensor shape a -> Tensor shape a

namespace Size
  {-----
  Can we measure the size of a tensor of containers?
  Likely need to impose an additional constraint that the set of positions is enumerable
  -----}
  ||| Number of elements in a non-cubical tensor
  public export
  cSize : {shape : Vect rank Axis} ->
    AxesConsistent shape =>
    Tensor shape a -> Nat
  
  ||| Number of elements in a cubical tensor
  public export
  size : {shape : Vect rank Axis} ->
    AxesConsistent shape =>
    All IsCubical shape =>
    (0 _ : Tensor shape a) -> Nat
  size {shape} _ = size shape

namespace Flatten
  ||| Flatten a non-cubical tensor into a list
  ||| Requires that we have Foldable on all the components
  ||| In general we won't know the number of elements of a non-cubical tensor at compile time
  public export
  cFlatten : {0 shape : Vect rank Axis} ->
    AxesConsistent shape =>
    Foldable (Tensor shape) =>
    Tensor shape a -> List a
  cFlatten = toList

  ||| Flatten a cubical tensor into a vector
  ||| Number of elements is known at compile time
  ||| Can even be zero, if any of shape elements is zero
  flatten : {shape : Vect rank Axis} ->
    AxesConsistent shape =>
    All IsCubical shape =>
    Tensor shape a -> Vect (size shape) a
  flatten t = ?flatten_rhs

  -- This was the old version with a strided implementation
  -- flatten : {shape : List Nat} ->
  --   Tensor shape a -> Vect (prod shape) a
  -- flatten (ToCubicalTensor (TS ex)) = extract <$> toVect ex

namespace Max
  ||| Maximum value in a tensor
  ||| Returns Nothing if the tensor is empty
  max : {0 shape : Vect rank Axis} ->
    AxesConsistent shape =>
    Foldable (Tensor shape) => Ord a =>
    Tensor shape a -> Maybe a
  max = maxInList . cFlatten

  -- TODO Fix for strided
  -- max {shape = []} t = maxA (FromCubicalTensor t)
  -- max {shape = (s :: ss)} t = let tt = maxA (FromCubicalTensor t) in ?max_rhs_1
  -- maxA maxA . FromCubicalTensor  -- t = let tt = FromCubicalTensor t in maxA tt
  --maxA . FromCubicalTensor

namespace OneHot
  public export
  oneHot : {0 c : Axis} -> IsCubical c =>
    (i : Fin (dim c)) ->
    Num a =>  Tensor [c] a
  oneHot @{MkIsCubical _ n} i = set zeros [i] 1 

namespace Triangular
  -- should we have ni,ni here, or ni,nj?
  public export
  cTriBool : {c : Axis} ->
    (ip : InterfaceOnPositions c.ToCont MOrd) =>
    TensorMonoid c.ToCont =>
    (sh : c.ToCont.Shp) -> Tensor [c, c] Bool
  cTriBool {ip = MkI {p}} sh
    = let cPositions = positions {sh=sh}
          pp : MOrd (c.ToCont.Pos sh) := p sh
      in outerWith (flip isSubTerm) cPositions cPositions

  -- public export
  -- triA : Num a => {c : Cont} ->
  --   (ip : InterfaceOnPositions c MOrd) =>
  --   All TensorMonoid [c] =>
  --   (sh : c.Shp) -> CTensor [c, c] a
  -- triA sh = fromBool <$> cTriBool sh

  public export
  triBool : {0 c : Axis} -> IsCubical c =>
    Tensor [c, c] Bool
  triBool @{MkIsCubical _ n} = cTriBool ()


  ||| A matrix with ones on and below the diagonal, and zeros elsewhere
  ||| Analogous to numpy.tri
  public export
  tri : {0 c : Axis} -> IsCubical c =>
    Num a => Tensor [c, c] a
  tri @{MkIsCubical _ n} = fromBool <$> triBool

  ||| Lower triangular part of a matrix. Elements above the diagonal are set to
  ||| zero. Analogous to numpy.tril
  public export
  lowerTriangular : {0 c : Axis} -> IsCubical c =>
    Num a => Tensor [c, c] a -> Tensor [c, c] a
  lowerTriangular @{MkIsCubical _ n} = (* tri)

  ||| Upper triangular part of a matrix. Elements below the diagonal are set to
  ||| zero. Analogous to numpy.triu(.., k=1)
  public export
  upperTriangular : {0 c : Axis} -> IsCubical c =>
    Num a => Tensor [c, c] a -> Tensor [c, c] a
  upperTriangular @{MkIsCubical _ n} = (* ((fromBool . not) <$> triBool))

  ||| Fill the elements of a tensor `t` with `fill` where `mask` is True
  public export
  maskedFill : {shape : Vect rank Axis} ->
    AxesConsistent shape =>
    Num a => All TensorMonoid (conts shape) =>
    (t : Tensor shape a) ->
    (mask : Tensor shape Bool) ->
    (fill : a) ->
    Tensor shape a
  maskedFill t mask fill = liftA2Tensor mask t <&>
    (\(maskVal, tVal) => if maskVal then fill else tVal)

namespace Misc
  public export
  sum : {shape : Vect rank Axis} ->
    AxesConsistent shape =>
    Algebra (Tensor shape) a =>
    Tensor shape a -> a
  sum = reduce

  public export
  mean : {shape : Vect rank Axis} ->
    All IsCubical shape =>
    AxesConsistent shape =>
    Cast Nat a =>
    Fractional a => 
    Algebra (Tensor shape) a =>
    Tensor shape a -> a
  mean t = sum t / cast (size t)

  public export
  variance : {c : Axis} -> IsCubical c =>
    Neg a => Fractional a => Cast Nat a =>
    Tensor [c] a -> a
  variance @{MkIsCubical _ n} t =
    let inputMinusMean = t - pure (mean t)
    in mean (inputMinusMean * inputMinusMean)


namespace Traversals
  public export
  inorder : Tensor [b ~> BinTreeNode] a -> Tensor [l ~> List] a
  inorder = extToVector . extMap BinTreeNode.inorder . vectorToExt

namespace Random
  public export
  {shape : Vect rank Axis} ->
  AxesConsistent shape =>
  Random a =>
  Applicative (Tensor shape) => -- again, should we need this?
  Traversable (Tensor shape) =>
  Random (Tensor shape a) where
    randomIO = sequence (pure randomIO)
    randomRIO = ?qhwhwh


-- Idris can't find the parametric randomIO interface so reimpementing here 
public export
random : Num a => Random a => HasIO io =>
  (shape : Vect rank Axis) ->
  All IsCubical shape =>
  AxesConsistent shape =>
  Applicative (Tensor shape) => 
  Traversable (Tensor shape) => 
  io (Tensor shape a)
random shape = sequence $ pure $ randomRIO (0, 1)

tt : Traversable (Vect 2)
tt = %search

ttt : Traversable (Ext (Vect 2))
ttt = %search

tttt : Traversable (Tensor ["i" ~~> 2])
tttt = %search

testRand : IO (Tensor ["i" ~~> 2, "j" ~~> 3] Double)
testRand = do 
  t <- random ["i" ~~> 2, "j" ~~> 3]
  printLn $ show t
  pure t

testRand2 : IO (Tensor ["i" ~~> 5] Double)
testRand2 = random ["i" ~~> 5]

testRand3 : IO Unit
testRand3 = randomIO
