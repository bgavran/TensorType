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
  Matrix : (row, col : Axis) -> NewAxisConsistent row [col] => (a : Type) -> Type
  Matrix row col a = Tensor [row, col] a

namespace FillZerosOnes
  public export
  fill : Num a => {shape : TensorShape rank} ->
    All TensorMonoid (conts shape) =>
    a -> Tensor shape a
  fill x = tensorReplicate x

  public export
  zeros : Num a => {shape : TensorShape rank} ->
    All TensorMonoid (conts shape) => 
    Tensor shape a
  zeros = fill (fromInteger 0)

  public export
  ones : Num a => {shape : TensorShape rank} ->
    All TensorMonoid (conts shape) => 
    Tensor shape a
  ones = fill (fromInteger 1)

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
    arange @{MkIsCubical _ n} = cast . finToNat <$> positions {sh=()}

  namespace TwoArgs
    ||| A range of numbers [start, stop>
    public export
    arangeFromTo : {default (TTInternalName ~~> 0) start : Axis} ->
      {0 stop : Axis} ->
      (cStart : IsCubical start) => (cStop : IsCubical stop) =>
      Cast Nat a => Tensor [stop.name ~~> minus (dim stop) (dim start)] a
    arangeFromTo {cStart=(MkIsCubical _ n)} {cStop=(MkIsCubical _ m)}
      = cast . (+n) . finToNat <$> positions {sh=()}

namespace Flip
  ||| Reverse a tensor along a given axis
  public export
  flip : {shape : TensorShape rank} ->
    (axis : Fin rank) ->
    IsCubical (index axis (toVect shape)) =>
    Tensor shape a -> Tensor shape a


namespace Concatenate
  ||| Concatenate two tensors along an existing axis, the first one
  ||| TODO extend to allow concatenation along an arbitrary/named axis
  public export
  concat : {shape : TensorShape rank} -> {l : AxisName} ->
    {x, y : Axis} -> IsCubical x => IsCubical y =>
    NewAxisConsistent (l ~~> dim x + dim y) shape =>
    NewAxisConsistent x shape =>
    NewAxisConsistent y shape =>
    Tensor (x :: shape) a ->
    Tensor (y :: shape) a ->
    Tensor ((l ~~> dim x + dim y) :: shape) a
  concat @{MkIsCubical _ n} @{MkIsCubical _ m} t t'
    = embedTopExt $ extractTopExt t ++ extractTopExt t'

namespace Size
  {-----
  Can we measure the size of a tensor of containers?
  Likely need to impose an additional constraint that the set of positions is enumerable
  -----}
  ||| Number of elements in a non-cubical tensor
  public export
  size : {shape : TensorShape rank} ->
    Tensor shape a -> Nat

  namespace Cubical 
    ||| Number of elements in a cubical tensor
    public export
    size : {shape : TensorShape rank} ->
      All IsCubical (toVect shape) =>
      (0 _ : Tensor shape a) -> Nat
    size {shape} _ = size (toVect shape)

namespace Flatten
  ||| Flatten a non-cubical tensor into a list
  ||| Requires that we have Foldable on all the components
  ||| In general we won't know the number of elements of a non-cubical tensor at compile time
  public export
  flatten : {0 shape : TensorShape rank} ->
    Foldable (Tensor shape) =>
    Tensor shape a -> List a
  flatten = toList

  namespace Cubical
    ||| Flatten a cubical tensor into a vector
    ||| Number of elements is known at compile time
    ||| Can even be zero, if any of shape elements is zero
    flatten : {shape : TensorShape rank} ->
      All IsCubical (conts shape) =>
      Tensor shape a -> Vect (size shape) a
    flatten = toVect . extMap (flattenCubical DefaultLayoutOrder) . GetT

namespace Max
  ||| Maximum value in a tensor
  ||| Returns Nothing if the tensor is empty
  public export
  max : {0 shape : TensorShape rank} ->
    Foldable (Tensor shape) => Ord a =>
    Tensor shape a -> Maybe a
  max = maxInList . flatten

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
    (ip : InterfaceOnPositions c.cont MOrd) =>
    TensorMonoid c.cont =>
    (sh : c.cont.Shp) -> Tensor [c, c] Bool
  cTriBool {ip = MkI {p}} sh
    = let cPositions = positions {sh=sh}
          pp : MOrd (c.cont.Pos sh) := p sh
      in outerWith (flip isSubTerm) cPositions cPositions

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
  maskedFill : {shape : TensorShape rank} ->
    Num a => All TensorMonoid (conts shape) =>
    (t : Tensor shape a) ->
    (mask : Tensor shape Bool) ->
    (fill : a) ->
    Tensor shape a
  maskedFill t mask fill = liftA2Tensor mask t <&>
    (\(maskVal, tVal) => if maskVal then fill else tVal)

namespace Misc
  public export
  sum : {shape : TensorShape rank} ->
    Algebra (Tensor shape) a =>
    Tensor shape a -> a
  sum = reduce

  public export
  mean : {shape : TensorShape rank} ->
    All IsCubical (toVect shape) =>
    Cast Nat a =>
    Fractional a => 
    Algebra (Tensor shape) a =>
    Tensor shape a -> a
  mean t = sum t / cast (Cubical.size t)

  public export
  variance : {c : Axis} -> IsCubical c =>
    Neg a => Fractional a => Cast Nat a =>
    Tensor [c] a -> a
  variance @{MkIsCubical _ n} t =
    let inputMinusMean = t - pure (mean t)
    in mean (inputMinusMean * inputMinusMean)

  public export
  cumulativeSum : {c : Axis} -> Num a =>
    (isCubical : IsCubical c) =>
    Tensor [c] a -> Tensor [c] a
  -- cumulativeSum {isCubical=(MkIsCubical _ n)} t
  --   = let tt = map {f=Vect n} (scanl1 (+)) (#> t)
  --         
  --     in ?qqwer -- #> ((scanl1 (+)) (#> t))  --(#>#) 




namespace Traversals
  public export
  inorder : Tensor [b ~> BinTreeNode] a -> Tensor [l ~> List] a
  inorder = extToVector . extMap BinTreeNode.inorder . vectorToExt

namespace Random
  public export
  {shape : TensorShape rank} ->
  Random a =>
  Applicative (Tensor shape) => -- again, should we need this?
  Traversable (Tensor shape) =>
  Random (Tensor shape a) where
    randomIO = sequence (pure randomIO)
    randomRIO = ?qhwhwh


  tta : Applicative (Tensor ["a" ~~> 1])
  tta = %search

  ttt : Traversable (Tensor ["b" ~~> 1])
  ttt = %search
  
  ttd : Random Double
  ttd = %search

-- Idris can't find the parametric randomIO interface so reimpementing here
public export
random : Num a => Random a => HasIO io =>
  (shape : TensorShape rank) ->
  All IsCubical (toVect shape) =>
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

public export
exMatrix : Ext (Vect 3 >< Vect 3) Double
exMatrix = ((), ()) <| \case
        (0, 0) => 0
        (0, 1) => 1
        (0, 2) => 2
        (1, 0) => 3
        (1, 1) => 4
        (1, 2) => 5
        (2, 0) => 6
        (2, 1) => 7
        (2, 2) => 8

public export
applMap : {n : Nat} -> Ext (Vect n >< Vect n) Double -> Ext (Vect n) Double
applMap = extMap tensorM

allPos : (BinTreePosLeaf (NodeS LeafS LeafS), BinTreePosLeaf (NodeS (NodeS LeafS LeafS) LeafS)) -> Double
allPos ((GoLeft AtLeaf), (GoLeft (GoLeft AtLeaf))) = 0
allPos ((GoRight AtLeaf), (GoLeft (GoLeft AtLeaf))) = 1
allPos ((GoLeft AtLeaf), (GoLeft (GoRight AtLeaf))) = 2
allPos ((GoRight AtLeaf), (GoLeft (GoRight AtLeaf))) = 3
allPos ((GoLeft AtLeaf), (GoRight AtLeaf)) = 4
allPos ((GoRight AtLeaf), (GoRight AtLeaf)) = 5

exTree : Ext (BinTreeLeaf >< BinTreeLeaf) Double
exTree = (NodeS LeafS LeafS, NodeS (NodeS LeafS LeafS) LeafS) <| allPos

applMapTree : Ext (BinTreeLeaf >< BinTreeLeaf) Double -> Ext (BinTreeLeaf) Double
applMapTree = extMap tensorM

ff : Tensor ["v" ~~> 4, "v" ~~> 4] Double -> Tensor ["v" ~~> 4] Double
ff t = let g = extMap {a=Double} (tensorM {c=Vect 4})
       in ?ff_rhs

||| Now you can construct Tensors directly:
t0 : Tensor ["j" ~~> 3, "k" ~~> 4] Double
t0 = ># [ [0, 1, 2, 3]
        , [4, 5, 6, 7]
        , [8, 9, 10, 11]]

t1 : Tensor ["i" ~~> 6] Double
t1 = arange

exMatrix2 : Tensor ["v" ~~> 3, "v" ~~> 3] Double
exMatrix2 = reshape $ arange {stop="v" ~~> 9}



public export
tTest : Tensor ["i" ~~> 800] Double
tTest = arange

public export
tRes : Tensor ["i" ~~> 2, "j" ~~> 400] Double
tRes = reshape tTest