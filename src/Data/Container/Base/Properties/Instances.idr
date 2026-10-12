module Data.Container.Base.Properties.Instances

import Data.Fin
import Data.Vect
import Data.List.Quantifiers
import Decidable.Equality
import Data.Fin.Split
import Data.Finite

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Properties.Definition
import Data.Container.Base.Endofunctor.Definition
import Data.Container.Base.Product.Definition

import Data.Container.Base.Object.Instances
import Data.Container.Base.Extension.Instances
import Data.Container.Base.Morphism.Instances

import Data.Trees
import Data.Functor.Products
import Data.Functor.Algebra
import Data.Layout
import Data.Container.Base.TreeUtils

import Misc

%hide Data.Vect.fromList
%hide Prelude.toList
%hide Prelude.(<|)


{-------------------------------------------------------------------------------
Instances of the properties for the zoo, and what follows from them
-------------------------------------------------------------------------------}

public export
EmptyExt : {0 c : Cont} -> IsNaperian c => Ext c Unit
EmptyExt @{Via _} = () <| \_ => ()

public export
liftA2ConstCont : IsNaperian c => Ext c a -> Ext c b -> Ext c (a, b)
liftA2ConstCont @{Via _} ea eb = () <| (\x => (index ea x, index eb x))

||| The extension of any Naperian container is an applicative functor
||| Examples: Scalar, Pair, Vect n, Stream
||| But not all Applicatives are Naperian, examples being: List and Maybe
public export
IsNaperian c => Applicative (Ext c) where
  pure @{Via _} a = () <| \_ => a
  (<*>) fs xs @{Via _} = uncurry ($) <$> liftA2ConstCont fs xs

namespace CompositionTensorInteraction
  ||| Going the other way is impossible without any constraints
  ||| Two possibilities on constraints (this, and `compToTensor2`)
  public export
  compToTensor : IsNaperian d =>
    c >@ d =%> c >< d
  compToTensor @{(Via dPos)} = !% \(cShp <| content) =>
    ((cShp,()) ** \(cPos, dPos) => (cPos ** dPos))

  public export
  compToTensor2 : IsFlat c =>
    c >@ d =%> c >< d
  compToTensor2 @{(Via cShp)} = !% \(cShp <| dShp) =>
    ((cShp, dShp ()) ** \((), dPos') => (() ** dPos'))

namespace Transpose
  public export
  transposeLens : IsNaperian c => IsNaperian d => c >@ d =%> d >@ c
  transposeLens @{Via _} @{Via _} = !% \(() <| _) =>
    (() <| (\_ => ()) ** \(dInd ** cInd) => (cInd ** dInd))

  public export
  transpose : IsNaperian c => IsNaperian d =>
    Tensor [c, d] =%> Tensor [d, c]
  transpose @{Via _} @{Via _} = wrapIntoMatrix transposeLens

  -- ||| experiment, does this work?
  -- public export
  -- transposeMiddle : IsNaperian c => IsNaperian e =>
  --   Tensor [c, e, d] =%>


  --||| Transpose a given element to the front of the shape
  --public export
  --transposeToFront : (shape : List Cont) ->
  --  (c : Cont) ->
  --  (elem : Elem c shape) =>
  --  All IsNaperian (dropAfterElem shape elem) =>
  --  Tensor shape =%> Tensor (c :: dropElem shape elem)
  --transposeToFront (_ :: xs) c @{Here} @{allNap} = ?transposeToFront_rhs_0
  --transposeToFront (y :: xs) c @{(There x)} @{allNap} = ?transposeToFront_rhs_1

namespace CubicalHelpers
  ||| Helper function allowing `shape` in `cubicalShape` to have zero annotation
  public export
  cubicalShapeHelper : All IsCubical shape -> List Nat
  cubicalShapeHelper [] = []
  cubicalShapeHelper (ic :: ics) = dimHelper ic :: cubicalShapeHelper ics
    
  ||| Given a list of cubical containers, return the list of their dimensions
  public export
  cubicalShape : (0 shape : List Cont) -> All IsCubical shape => List Nat
  cubicalShape _ @{ac} = cubicalShapeHelper ac
    
  ||| Size of a list of cubical containers is the product of their dimensions
  public export
  size : (0 shape : List Cont) -> All IsCubical shape => Nat
  size shape = prod (cubicalShape shape)

||| Layout-aware dependent lens flattening a cubical tensor
public export
flattenCubical : {shape : List Cont} ->
  (ac : All IsCubical shape) =>
  LayoutOrder ->
  Tensor shape =%> Vect (size shape)
flattenCubical {shape = [], ac=[]} _ = !% \() => (() ** \FZ => ())
flattenCubical {shape = (_ :: ss), ac=(Via n :: as)} lo
  = !% \(() <| t) => (() ** \idx =>
      let (!% recBackward) = flattenCubical {shape = ss} lo
          (i, rest) = splitFinProd lo idx
          (_ ** backRec) = recBackward (t i)
      in (i ** backRec rest))

||| Layout-aware dependent lens unflattening a tensor
public export
unflattenCubical : {shape : List Cont} ->
  (ac : All IsCubical shape) =>
  LayoutOrder ->
  Vect (size shape) =%> Tensor shape
unflattenCubical {shape = [], ac=[]} lo = !% \() => (() ** \() => FZ)
unflattenCubical {shape = (_ :: ss), ac=((Via n) :: as)} lo =
  let (!% f) = unflattenCubical {shape = ss} lo
      (innerShape ** innerBack) = f ()
  in !% \() => ((() <| \_ => innerShape) ** (\(cp ** restPos) =>
    indexFinProd lo cp (innerBack restPos)))

||| This is simply a rewrite!
public export
recastFlattenedTensor : {oldShape, newShape : List Cont} ->
  (oldAc : All IsCubical oldShape) => (newAc : All IsCubical newShape) =>
  {auto prf : size oldShape = size newShape} ->
  Vect (size oldShape) =%> Vect (size newShape)
recastFlattenedTensor = !% \() => (() ** \i => rewrite prf in i)

||| Reshapes a cubical tensor by first flattening it to a linear representation,
||| casting the type to the new shape, and then unflattening it back
||| Is generic over layout order
public export
reshape : {oldShape, newShape : List Cont} ->
  (oldAc : All IsCubical oldShape) => (newAc : All IsCubical newShape) =>
  LayoutOrder ->
  {auto prf : size oldShape = size newShape} ->
  Tensor oldShape =%> Tensor newShape
reshape lo = flattenCubical lo
         %>> recastFlattenedTensor
         %>> unflattenCubical lo

||| Functionality for transforming a tensor into a hancock tensor
namespace TransformIntoHancockTensor
  public export
  hancockTensorNaperianShape : {shape : List Cont} ->
    (allNap : All IsNaperian shape) =>
    (HancockTensor shape).Shp
  hancockTensorNaperianShape {shape = []} = ()
  hancockTensorNaperianShape {allNap = ((Via _) :: _)}
    = ((), hancockTensorNaperianShape)
  
  ||| Helper to compute the unique shape of Tensor when all containers are Naperian
  public export
  tensorNaperianShape : {shape : List Cont} ->
    (allNap : All IsNaperian shape) =>
    (Tensor shape).Shp
  tensorNaperianShape {shape = []} = ()
  tensorNaperianShape {shape = (_ :: ss), allNap = ((Via _) :: ns)}
    = () <| \_ => tensorNaperianShape {shape = ss} @{ns}
  
  ||| Analogous to `naperianPosEq` but for the HancockTensor structure
  ||| We can't use `naperianPosEq` directly because the shape of the resulting
  ||| container is not Unit, it is only isomorphic to it
  public export
  hancockTensorPosEq : {shape : List Cont} ->
    (allNap : All IsNaperian shape) =>
    {0 x, y : (HancockTensor shape).Shp} ->
    (HancockTensor shape).Pos x = (HancockTensor shape).Pos y
  hancockTensorPosEq {allNap = []} = Refl
  hancockTensorPosEq {allNap = ((Via _) :: _)} = cong2 Pair
    (naperianPosEq @{Via _} {x=()} {y=()})
    hancockTensorPosEq
  
  ||| Tensor shape is isomorphic to HancockTensor shape when all containers in
  ||| the shape are Naperian. This is one arrow of that isomorphism
  public export
  transformToHancock : {shape : List Cont} ->
    All IsNaperian shape =>
    Tensor shape =%> HancockTensor shape
  transformToHancock {shape = []} = id
  transformToHancock {shape = (_ :: _)} @{((Via _) :: _)}
    = !% \(() <| content) => (((), hancockTensorNaperianShape) **
       \(p, restPos) =>
         let (_ ** recBack) = (%!) transformToHancock (content p)
         in (p ** recBack $ replace {p = id} hancockTensorPosEq restPos))

  public export
  transformFromHancock : {shape : List Cont} ->
    All IsNaperian shape =>
    HancockTensor shape =%> Tensor shape
  transformFromHancock {shape = []} = id
  transformFromHancock {shape = (Nap s :: ss)} @{((Via s) :: _)}
    = !% \((), hShp) =>
        let (tShp ** recBack) = (%!) transformFromHancock hShp
        in (() <| (\_ => tShp) ** \(p ** restPos) => (p, recBack restPos))

public export
IsConcrete Scalar where
  func = id
  functorInstance = MkFunctor id
  fromConcreteTy x = () <| \_ => x
  toConcreteTy (() <| f) = f ()

public export
IsConcrete UnitCont where
  func = const Unit
  functorInstance = MkFunctor (\f, () => ())
  fromConcreteTy () = () <| absurd
  toConcreteTy _ = ()

public export
IsConcrete Maybe where
  func = Maybe
  functorInstance = %search

  fromConcreteTy Nothing = False <| absurd
  fromConcreteTy (Just x) = True <| \() => x

  toConcreteTy (False <| _) = Nothing
  toConcreteTy (True <| f) = Just (f ())

public export
IsConcrete Pair where
  func = \a => Pair a a
  functorInstance = MkFunctor $ \f, (x, y) => (f x, f y)
  fromConcreteTy (x, y) = () <| \case False => x; True => y
  toConcreteTy (() <| f) = (f False, f True)

||| This is a concrete instance for Naperian containers
||| It applies also to `s=Fin n` which is covered by Vect
||| We therefore want this to only be applied if Vect isn't
%defaulthint
public export
lambdaNap : {s : Type} -> IsConcrete (Nap s)
lambdaNap = MkIsConcrete
  (\a => s -> a)
  (MkFunctor (.))
  (\content => () <| content)
  (\(() <| content) => content)

public export
(icc : IsConcrete c) => (icd : IsConcrete d) => IsConcrete (c >< d) where
  func = func @{icc} >< func @{icd}
  functorInstance = ?functorInstanceHancockProduct
  fromConcreteTy = ?fromConcreteTyHancockProduct
  toConcreteTy = ?toConcreteTyHancockProduct

public export
(icc : IsConcrete c) => (icd : IsConcrete d) => IsConcrete (c >@ d) where
  func = func @{icc} . func @{icd}
  functorInstance = MkFunctor $ \f => ?functorInstanceCompositionProduct
  fromConcreteTy = ?fromConcreteTyCompositionProduct
  toConcreteTy = ?toConcreteTyCompositionProduct


||| For recursive types we need to extract out the conversion functions
||| They live in `Extension.Instances`, as they use no property
namespace List
  public export
  IsConcrete List where
    func = List
    functorInstance = %search
    fromConcreteTy = fromList
    toConcreteTy = toList

namespace Vect
  -- public export
  -- test : {n : Nat} -> IsConcrete (Vect n)
  -- test = MkIsConcrete
  --   (Vect n)
  --   (%search)
  --   (fromVect)
  --   (toVect)

  public export
  {n : Nat} -> IsConcrete (Vect n) where
    func = Vect n
    functorInstance = %search
    fromConcreteTy = fromVect
    toConcreteTy = toVect

namespace Grid
  public export
  {h, w : Nat} -> IsConcrete (Grid (h, w)) where
    func a = (Fin h, Fin w) -> a
    functorInstance = MkFunctor (.)
    fromConcreteTy content = ((), ()) <| content
    toConcreteTy (((), ()) <| content) = content

namespace BinTreeSame
  public export
  IsConcrete BinTree where
    func = BinTreeSame
    functorInstance = %search
    fromConcreteTy = fromBinTreeSame
    toConcreteTy = toBinTreeSame

namespace BinTreeNode
  public export
  IsConcrete BinTreeNode where
    func = BinTreeNode
    functorInstance = %search
    fromConcreteTy = fromBinTreeNode
    toConcreteTy = toBinTreeNode

namespace BinTreeLeaf
  public export
  IsConcrete BinTreeLeaf where
    func = BinTreeLeaf
    functorInstance = %search
    fromConcreteTy = fromBinTreeLeaf
    toConcreteTy = toBinTreeLeaf

-- Decidable instances for common containers

%hint
public export
maybeIsDecidable : IsDecidable Maybe
maybeIsDecidable = MkI decPos
  where decPos : (b : Bool) -> DecEq (if b then Unit else Void)
        decPos False = %search
        decPos True = %search

%hint
public export
maybeTwoIsDecidable : IsDecidable MaybeTwo
maybeTwoIsDecidable = MkI decPos
  where decPos : (b : Bool) -> DecEq (if b then Fin 2 else Void)
        decPos False = %search
        decPos True = %search

public export
compositionIsDecidable : IsDecidable c => IsDecidable d => IsDecidable (c >@ d)
compositionIsDecidable @{cd} @{dd} = MkI $ \ex => DecEqDPair
  @{GetInterface cd (shapeExt ex)} @{\cp => GetInterface dd (index ex cp)}

||| Positions are pairs of positions
public export
hancockIsDecidable : IsDecidable c => IsDecidable d => IsDecidable (c >< d)
hancockIsDecidable @{cd} @{dd} = MkI $ \ss =>
  let decC = GetInterface cd (fst ss)
      decD = GetInterface dd (snd ss)
  in %search

||| Positions are a position of one or of the other
public export
cartesianIsDecidable : IsDecidable c => IsDecidable d => IsDecidable (c >*< d)
cartesianIsDecidable @{cd} @{dd} = MkI $ \ss =>
  let decC = GetInterface cd (fst ss)
      decD = GetInterface dd (snd ss)
  in %search

||| Positions are those of whichever container the shape comes from
public export
coproductIsDecidable : IsDecidable c => IsDecidable d => IsDecidable (c >+< d)
coproductIsDecidable @{cd} @{dd} = MkI decPos
  where decPos : (es : Either c.Shp d.Shp) -> DecEq (either c.Pos d.Pos es)
        decPos (Left s) = GetInterface cd s
        decPos (Right s) = GetInterface dd s

||| `cs` can't be inferred from `Tensor cs`, so pass it as `{cs = ...}`.
||| The `All` itself is found by search when the containers in `cs` are
public export
tensorIsDecidable : All IsDecidable cs => IsDecidable (Tensor cs)
tensorIsDecidable @{[]} = %search
tensorIsDecidable @{cd :: cds}
  = compositionIsDecidable @{cd} @{tensorIsDecidable @{cds}}

-- public export
-- binTreePosInterface : InterfaceOnPositions BinTree DecEq
-- binTreePosInterface = MkI


-- old
-- ||| Indexing an element of `xs` and then applying `f` to it is the same as
-- ||| mapping `f` over xs, and then indexing the result
-- public export
-- mapIndexPreserve : {0 f : a -> b} ->
--   (xs : List a) ->
--   (i : Fin (length (f <$> xs))) ->
--   f (index' xs (rewrite sym (lengthMap {f=f} xs) in i))
--     = index' (f <$> xs) i
-- mapIndexPreserve (x :: xs) FZ = Refl
-- mapIndexPreserve (x :: xs) (FS j) = mapIndexPreserve xs j


||| The extension of a foldable container folds in its chosen order
public export
IsFoldable c => Foldable (Ext c) where
  foldr @{Along toL} f z e = foldr
    (\p, acc => f (index e p) acc)
    z
    (tabulate (toL.bwd (shapeExt e)))

||| Every enumeration is a fold, forgetting the map from positions to indices
%hint
public export
enumerableIsFoldable : IsEnumerable c => IsFoldable c
enumerableIsFoldable @{MkIsEnum e} = Along (!% (%! ((:%) e)))

||| Lists, non-empty lists and vectors number their own positions
%hint
public export
listIsEnumerable : IsEnumerable List
listIsEnumerable = MkIsEnum (!: \n => (n ** idIso))

%hint
public export
list1IsEnumerable : IsEnumerable List1
list1IsEnumerable = MkIsEnum (!: \n => (S n ** idIso))

%hint
public export
vectIsEnumerable : {n : Nat} -> IsEnumerable (Vect n)
vectIsEnumerable = MkIsEnum (!: \() => (n ** idIso))

||| Forgetting the order of a list gives a bag
public export
forgetOrder : List =%> Bag
forgetOrder = !% \n => (n ** toFin)

||| Every foldable container is summable, through the order its fold chose
%hint
public export
foldableIsSummable : IsFoldable c => IsSummable c
foldableIsSummable @{Along toL} = Along (toL %>> forgetOrder)

||| A foldable container restricted to one of its shapes is foldable
public export
foldableAt : IsFoldable c => (s : c.Shp) -> IsFoldable (At c s)
foldableAt s = Along (atShape s %>> mapToList)

||| Every extension of a foldable container indexes as a list
public export
index : IsFoldable c => Pick c a =%> List
index = pick %>> mapToList

||| Requires making a choice of traversal order
||| Is there a good reason to prefer a particular order?
||| The index of a position and the two round trips are not written yet
%hint
public export
binTreeLeafIsEnumerable : IsEnumerable BinTreeLeaf
binTreeLeafIsEnumerable = MkIsEnum (!: \b => (numLeaves b ** MkIso
  ?inorderForward_binTreeLeaf (BinTreeLeaf.inorderBackward b)
  ?inorderForwardBackward_binTreeLeaf ?inorderBackwardForward_binTreeLeaf))

%hint
public export
binTreeNodeIsEnumerable : IsEnumerable BinTreeNode
binTreeNodeIsEnumerable = MkIsEnum (!: \b => (numNodes b ** MkIso
  ?inorderForward_binTreeNode (BinTreeNode.inorderBackward b)
  ?inorderForwardBackward_binTreeNode ?inorderBackwardForward_binTreeNode))

%hint
public export
binTreeIsEnumerable : IsEnumerable BinTree
binTreeIsEnumerable = MkIsEnum (!: \b => (numNodesAndLeaves b ** MkIso
  ?inorderForward_binTree (BinTree.inorderBackward b)
  ?inorderForwardBackward_binTree ?inorderBackwardForward_binTree))

||| Any foldable functor can be given an algebra by summing its values
public export
algebraFoldable : {f : Type -> Type} ->
  Foldable f => Num a => Algebra f a
algebraFoldable = MkAlgebra sum

||| The extension of a foldable container, as an instance so that search finds
||| it, for `Vect'`, `List'`, the trees, and any container with `IsFoldable`
public export
IsFoldable c => Num a => Algebra (Ext c) a where
  reduce = sum

public export
argmax : Ord a => (isF : IsFoldable c) => (ne : IsNonEmpty c) =>
  (e : Ext c a) -> c.Pos (shapeExt e)
argmax e = foldr
  (\p, best => if index e p >= index e best then p else best)
  (GetInterface ne (shapeExt e))
  positionsCont

||| Traversal through the vector of contents, the shape-and-contents
||| representation of a finitary container
public export
IsEnumerable c => Traversable (Ext c) where
  traverse f (sh <| ind) =
    let (n ** iso) = (:!) enumerate sh
    in (\v => sh <| index (fromVect v) . iso.forward)
         <$> traverse f (toVect (() <| ind . iso.backward))
