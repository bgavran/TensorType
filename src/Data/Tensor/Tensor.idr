module Data.Tensor.Tensor

import Data.Nat
import public Data.Vect
import public Data.Vect.Quantifiers
import public Data.Vect.Elem -- for proofs about AxesConsistent
import Data.DPair
import public Decidable.Equality
import public Data.Fin.Split

import public Data.Container.Base
import public Data.Container.Applicative
import public Data.Container.Base.Object.Instances as Cont
import public Data.Num

import public Data.Layout
import public Data.Tensor.Axis
import public Misc

%hide Syntax.WithProof.prefix.(@@) -- used here for indexing

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
This file defines the main datatype of this repository: `Tensor`, and
utilities and instances for working with it. `Tensor` implements and generalies
1) `np.array` from NumPy 
2) `torch.Tensor` from PyTorch
3) `tf.Tensor` from TensorFlow
to name a few.  In this file `Tensor` is simply a wrapper around the extension of an eponymous container: `Cont.Tensor` which itself is simply a composition of containers.

Provided instances for `Tensor` include:
Functor, Applicative, Foldable, Naperian, Algebra, Eq, Show, Num, Neg, Abs,
Fractional, Exp

General functionality includes:
* Converting to and from nested tensors
* Converting to and from concrete types
* Various tensor contractions
* Slicing for cubical tensors
* Getters
* Setters (TODO)
* Functionality for general reshaping such as views, traversals
* Concrete reshape for cubical tensors that fails if there is a size mismatch

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| Tensor is the core datatype of TensorType.
||| Implementation-wise, it's a wrapper around the extension of `Cont.Tensor`
||| to aid type inference, and to add the axis name functionality
public export
record Tensor
  (shape : TensorShape rank)
  (a : Type) where
  constructor MkT
  GetT : Ext (Cont.Tensor (conts shape)) a

%name Tensor.Tensor t, t', t''

public export
(.shape) : {shape : TensorShape rank} ->
  (0 t : Tensor shape a) -> Vect rank Axis
(.shape) _ = toVect shape

public export
(.axisNames) : {shape : TensorShape rank} ->
  (0 t : Tensor shape a) -> Vect rank AxisName
(.axisNames) _ = axisNames shape

public export
(.sizes) : {shape : TensorShape rank} ->
  (0 t : Tensor shape a) -> Vect rank Cont
(.sizes) _ = axisSizes shape

namespace SomeTesting
  public export
  BatchSize : Axis
  BatchSize =  "batchSize" ~> Vect 32
  
  SeqLen : Axis
  SeqLen = "seqLen" ~> List
  
  FeatureSize : Axis
  FeatureSize = "featureSize" ~> Vect 128
  
  BatchSizeNew : Axis
  BatchSizeNew = "batchSize" ~> Vect 13
  
  testBinding0 : Tensor [] Double
  
  testBinding1 : Tensor [SeqLen] Double
  
  testBinding12 : Tensor [SeqLen, SeqLen] Double
  
  testBinding2 : Tensor [BatchSize, SeqLen] Double
  
  testBinding3 : Tensor [BatchSize, SeqLen, FeatureSize] Double
  
  testBinding4 : Tensor [BatchSize, SeqLen, FeatureSize, FeatureSize] Double
  
  failing
    ||| This fails because the same name here refers to two different sizes
    failBinding1 : Tensor [BatchSize, BatchSizeNew] Double
  
    ||| Same here 
    failBinding2 : Tensor [BatchSize, rename SeqLen "batchSize"] Double

public export
Functor (Tensor shape) where
  map f (MkT t) = MkT $ map f t

namespace NestedTensorUtils
  public export
  extract : Tensor [] a -> a
  extract (MkT t) = extract t

  public export
  embed : a -> Tensor [] a
  embed a = MkT (toScalar a)

  ||| With the added data of the wrapper around (Ext (Tensor shape) a), this
  ||| effectively states a list version of the following isomorphism
  ||| Ext c . Ext d = Ext (c . d)
  public export
  fromExtensionComposition : {shape : TensorShape rank} ->
    composeExtensions (conts shape) a -> Tensor shape a
  fromExtensionComposition {shape = []} ce = MkT ce
  fromExtensionComposition {shape = (c :: cs)} (sh <| contentAt)
    = MkT $
    let rest = GetT . fromExtensionComposition . contentAt
    in (sh <| shapeExt . rest) <| \(cp ** fsh) => index (rest cp) fsh

  public export
  toExtensionComposition : {shape : TensorShape rank} ->
    Tensor shape a -> composeExtensions (conts shape) a
  toExtensionComposition {shape = []} (MkT t) = t
  toExtensionComposition {shape = (_ :: _)} (MkT ((csh <| cpos) <| idx))
    = csh <| \d => toExtensionComposition (MkT (cpos d <| curry idx d))

  ||| For this and the function below, the commented out definition is 'cleaner'
  ||| but it requires non-erased `c` and `cs`
  public export
  extractTopExt : {0 cs : TensorShape rank} ->
    NewAxisConsistent c cs =>
    Tensor (c :: cs) a -> Ext (c.cont) (Tensor cs a)
  extractTopExt (MkT (sh <| ind))
    = shapeExt sh <| \p => MkT $ index sh p <| \p' => ind (p ** p')
  
  public export
  embedTopExt : {0 cs : TensorShape rank} ->
    NewAxisConsistent c cs =>
    Ext (c.cont) (Tensor cs a) -> Tensor (c :: cs)  a
  embedTopExt e =
    let tp = GetT . index e
    in MkT $ (shapeExt e <| shapeExt . tp) <| \(p ** p') => index (tp p) p'

  ||| This is useful because container composition adds non-trivial data to the
  ||| vector type (i.e. `c >@ Scalar` is not equal to `c`)
  public export
  extToVector : Ext (c.cont) a -> Tensor [c] a
  extToVector e = MkT $ (shapeExt e <| \_ => ()) <| \(cp ** ()) => index e cp

  public export
  vectorToExt : Tensor [c] a -> Ext (c.cont) a
  vectorToExt (MkT t) = shapeExt (shapeExt t) <| \cp => index t (cp ** ())

  public export
  toNestedTensor : {0 cs : TensorShape rank} ->
    NewAxisConsistent c cs =>
    Tensor (c :: cs) a -> Tensor [c] (Tensor cs a)
  toNestedTensor = extToVector . extractTopExt

  public export
  fromNestedTensor : {0 cs : TensorShape rank} ->
    NewAxisConsistent c cs =>
    Tensor [c] (Tensor cs a) -> Tensor (c :: cs) a
  fromNestedTensor = embedTopExt . vectorToExt 

  ||| TODO generalise to function operating on an axis name instead of index
  public export
  tensorMapFirstAxis : {0 c : Axis} ->
    {0 cs : TensorShape k} -> {0 ds : TensorShape k'} ->
    NewAxisConsistent c cs => NewAxisConsistent c ds =>
    (f : Tensor cs a -> Tensor ds a) ->
    Tensor (c :: cs) a -> Tensor (c :: ds) a
  tensorMapFirstAxis f = fromNestedTensor . map f . toNestedTensor

  public export infixr 4 <-$>
  ||| Is meant to look like infix map (i.e. `<$>`) with the added difference
  ||| that we keep the container on the left side untouched, hence the `<-$>`
  public export
  (<-$>) : {c : Axis} ->
    {0 cs : TensorShape k} -> {0 ds : TensorShape k'} ->
    NewAxisConsistent c cs => NewAxisConsistent c ds =>
    (f : Tensor cs a -> Tensor ds a) ->
    Tensor (c :: cs) a -> Tensor (c :: ds) a
  (<-$>) = tensorMapFirstAxis


namespace TensorFromConcrete
  public export
  concreteTypeTensor : (shape : TensorShape rank) ->
    (allConcrete : AllConcrete (conts shape)) =>
    Type -> Type
  concreteTypeTensor [] {allConcrete = []} = concreteType {cont=Scalar}
  concreteTypeTensor (c :: cs) {allConcrete = Cons @{fc}}
    = (concreteType @{fc}) . (concreteTypeTensor cs)

  public export
  concreteTypeFunctor : {shape : TensorShape rank} ->
    (allConcrete : AllConcrete (conts shape)) =>
    Functor (concreteTypeTensor shape)
  concreteTypeFunctor {shape = []} {allConcrete = []}
    = concreteFunctor {cont=Scalar}
  concreteTypeFunctor {shape = (c :: cs)} {allConcrete = Cons @{fc}}
    = Functor.Compose @{concreteFunctor @{fc} } @{concreteTypeFunctor}

  public export
  concreteToExtensions : {shape : TensorShape rank} ->
    (allConcrete : AllConcrete (conts shape)) =>
    concreteTypeTensor shape a -> composeExtensions (conts shape) a
  concreteToExtensions {shape = []} {allConcrete = []} ct = fromConcreteTy ct
  concreteToExtensions {shape = (_ :: _)} {allConcrete = Cons} ct =
    concreteToExtensions <$> fromConcreteTy ct

  public export
  extensionsToConcreteType : {shape : TensorShape rank} ->
    (allConcrete : AllConcrete (conts shape)) =>
    composeExtensions (conts shape) a -> concreteTypeTensor shape a
  extensionsToConcreteType {shape = []} {allConcrete = []} ct = toConcreteTy ct
  extensionsToConcreteType {shape = (_ :: _)} {allConcrete = Cons @{fc}} ct
    = (map @{concreteFunctor @{fc}} extensionsToConcreteType) (toConcreteTy ct)

  public export
  toTensor : {shape : TensorShape rank} ->
    (allConcrete : AllConcrete (conts shape)) =>
    concreteTypeTensor shape a -> Tensor shape a
  toTensor = fromExtensionComposition . concreteToExtensions

  public export
  fromTensor : {shape : TensorShape rank} ->
    (allConcrete : AllConcrete (conts shape)) =>
    Tensor shape a -> concreteTypeTensor shape a
  fromTensor = extensionsToConcreteType . toExtensionComposition

  ||| Many containers have a `FromConcrete` instance, allowing them to easily
  ||| be converted to and from a (usually familiar) Idris type
  ||| This works with tensors defined as a fold over contianers, but it requires
  ||| burdensome shape annotations everywhere
  ||| The decision was made to wrap that fold in `Tensor` as above, and then
  ||| (as this isn't a container anymore) provide equally named functions like
  ||| the ones `FromConcrete` provides. Idris' name resolution should be able to
  ||| detect which one needs to be used at call sites
  public export
  fromConcreteTy : {shape : TensorShape rank} ->
    (allConcrete : AllConcrete (conts shape)) =>
    concreteTypeTensor shape a -> Tensor shape a
  fromConcreteTy = toTensor

  public export
  toConcreteTy : {shape : TensorShape rank} ->
    (allConcrete : AllConcrete (conts shape)) =>
    Tensor shape a -> concreteTypeTensor shape a
  toConcreteTy = fromTensor

  public export prefix 0 >#, #>

  ||| Prefix operator for converting from a concrete type to a tensor
  ||| We read it as a map `>` going into the tensor `#`
  public export
  (>#) : {shape : TensorShape rank} ->
    (allConcrete : AllConcrete (conts shape)) =>
    concreteTypeTensor shape a -> Tensor shape a
  (>#) = fromConcreteTy

  ||| Prefix operator for converting from a tensor to concrete type
  ||| We read it as a map `>` going out of the tensor `#`
  public export
  (#>) : {shape : TensorShape rank} ->
    (allConcrete : AllConcrete (conts shape)) =>
    Tensor shape a -> concreteTypeTensor shape a
  (#>) = toConcreteTy

  public export infixr 0 >#>, #>#

  public export
  (>#>) : {rankOld, rankNew : Nat} ->
    {shapeOld : TensorShape rankOld} ->
    {shapeNew : TensorShape rankNew} ->
    (allConcreteOld : AllConcrete (conts shapeOld)) =>
    (allConcreteNew : AllConcrete (conts shapeNew)) =>
    (Tensor shapeOld a -> Tensor shapeNew b) ->
    concreteTypeTensor shapeOld a -> concreteTypeTensor shapeNew b
  (>#>) f ct = #> (f (># ct))

  public export
  (#>#) : {rankOld, rankNew : Nat} ->
    {shapeOld : TensorShape rankOld} ->
    {shapeNew : TensorShape rankNew} ->
    (allConcreteOld : AllConcrete (conts shapeOld)) =>
    (allConcreteNew : AllConcrete (conts shapeNew)) =>
    (concreteTypeTensor shapeOld a -> concreteTypeTensor shapeNew b) ->
    Tensor shapeOld a -> Tensor shapeNew b
  (#>#) f t = ># (f (#> t))


namespace Reshape
  ||| A wrapper around `extMap`
  ||| Allows us to define views, traversals and general reshaping
  public export
  restructure : {cs : TensorShape oldRank} -> {ds : TensorShape newRank} ->
    Cont.Tensor (conts cs) =%> Cont.Tensor (conts ds) ->
    Tensor cs a -> Tensor ds a
  restructure f = MkT . extMap f . GetT

  ||| Reshape is `restructure` for cubical tensors that leaves number of 
  ||| elements unchanged.  This is currently by
  ||| 1) flattening out the entire tensor into a vector
  ||| 2) recast the type to be of the right shape
  ||| 3) unflatten the vector into the right shape
  ||| Importantly, the content of tensors is never touched, only the shape is
  ||| manipulated
  public export
  reshape :
    {oldShape : TensorShape oldRank} -> {newShape : TensorShape newRank} ->
    (oldCub : All IsCubical (conts oldShape)) => (newCub : All IsCubical (conts newShape)) =>
    Tensor oldShape a ->
    {auto prf : size (conts oldShape) = size (conts newShape)} ->
    Tensor newShape a
  reshape t = restructure (reshape DefaultLayoutOrder) t

  -- public export
  -- treeExample1 : Tensor ["binTree" ~> BinTree] Double
  -- treeExample1 = ># Node 60 (Node 7 (Leaf (-42)) (Leaf 46)) (Leaf 2)

  ||| Performs an in-order traversal of a binary tree tensor into a list tensor
  public export
  traversalExample : Tensor ["binTree" ~> BinTree] Double ->
                     Tensor ["list" ~> List] Double
  traversalExample = restructure (wrapIntoVector inorder)

  -- ||| Down the line, we'll also want to adjust how we perform this 
  -- ||| transformation depending on the device we perform the computation on.



namespace TensorInstances
  namespace ApplicativeInstance
    public export
    tensorReplicate : {shape : TensorShape rank} ->
      (allAppl : All TensorMonoid (conts shape)) =>
      (x : a) -> Tensor shape a
    tensorReplicate {shape = []} = embed
    tensorReplicate {shape = (_ :: _), allAppl = (::) _ _}
      = fromExtensionComposition
      . pure
      . toExtensionComposition
      . tensorReplicate

    public export
    liftA2Tensor : {shape : TensorShape rank} ->
      (allAppl : All TensorMonoid (conts shape)) =>
      Tensor shape a -> Tensor shape b -> Tensor shape (a, b)
    liftA2Tensor {shape = [], allAppl=[]} (MkT t) (MkT t')
      = embed (index t (), index t' ())
    liftA2Tensor {shape = (s :: ss), allAppl = (::) _ _} t t'
      = embedTopExt $ uncurry liftA2Tensor <$>
          liftA2 (extractTopExt t) (extractTopExt t')

    public export
    {shape : TensorShape rank} ->
    (allAppl : All TensorMonoid (conts shape)) =>
    Applicative (Tensor shape) where
      pure = tensorReplicate
      fs <*> xs = uncurry ($) <$> liftA2Tensor fs xs

  namespace EqInstance
    public export
    data AllEq : (shape : TensorShape rank) ->
      (a : Type) -> Type where
      Nil : Eq a => AllEq [] a
      Cons : {c : Axis} -> {cs : TensorShape k} ->
        (eq : Eq (c.cont `fullOf` Tensor cs a)) => -- hmm, can be simplified? this would cause unification regarding AllConsistent to become much simpler?
        (ne : NewAxisConsistent c cs) =>
        AllEq (c :: cs) a

    public export
    tensorEq : {shape : TensorShape rank} ->
      (allEq : AllEq shape a) =>
      Tensor shape a -> Tensor shape a -> Bool
    tensorEq {allEq = []} t1 t2 = extract t1 == extract t2
    tensorEq {allEq = Cons} t1 t2 = (extractTopExt t1) == (extractTopExt t2)

    public export
    {shape : TensorShape rank} ->
    AllEq shape a =>
      Eq (Tensor shape a) where
        (==) = tensorEq

    -- Turns out only this is sufficient for the setC function to work
    %hint
    public export
    interfacePosEq : {n : Nat} -> InterfaceOnPositions (Cont.Tensor [Vect n]) Eq
    interfacePosEq = MkI -- follows from Data.DPair L57

  -- public export
  -- vectInterfacePos : {n : Nat} -> InterfaceOnPositions (Vect n) DecEq
  -- vectInterfacePos = MkI

  namespace NumericInstances
    public export
    {shape : TensorShape rank} ->
    Num a => All TensorMonoid (conts shape) =>
    Num (Tensor shape a) where
        fromInteger = tensorReplicate . fromInteger
        t + t' = uncurry (+) <$> liftA2Tensor t t'
        t * t' = uncurry (*) <$> liftA2Tensor t t'

    public export
    {shape : TensorShape rank} ->
    Neg a => All TensorMonoid (conts shape) =>
    Neg (Tensor shape a) where
      negate = (negate <$>)
      xs - ys = (uncurry (-)) <$> liftA2 xs ys

    -- TODO this throws an error?
    negNotFound : {shape : TensorShape rank} ->
      Neg a => Neg (Tensor shape a)
    negNotFound = ?interfaceProblemsAgain

    public export
    {shape : TensorShape rank} ->
    Abs a => All TensorMonoid (conts shape) =>
    Abs (Tensor shape a) where
      abs = (abs <$>)

    public export
    {shape : TensorShape rank} ->
    Fractional a => All TensorMonoid (conts shape) =>
    Fractional (Tensor shape a) where
      t / v = (uncurry (/)) <$> liftA2 t v

    public export
    {shape : TensorShape rank} ->
    Exp a =>
    All TensorMonoid (conts shape) =>
    Exp (Tensor shape a) where
      exp = (exp <$>)
      log = (log <$>)
      minusInfinity = pure minusInfinity

    public export
    {shape : TensorShape rank} ->
    FromDouble a =>
    All TensorMonoid (conts shape) =>
      FromDouble (Tensor shape a) where
        fromDouble x = tensorReplicate (fromDouble x)

  namespace DiagonalAxis
    public export
    diagonal : {i : Axis} ->
      (t : Tensor [i, i] a) ->
      IsNaperian i.cont => TensorMonoid (i.cont) =>
      Tensor [i] a
    diagonal t = restructure diagonal t

    public export
    tDiag : Tensor ["i" ~~> 2, "i" ~~> 2] Double
    tDiag = ># [ [100, 0]
               , [0, 47] ] 

    --public export
    --diagonal : {k : Nat} -> {shape : TensorShape rank} ->
    --  (t : Tensor shape a) ->
    --  (axisName : AxisName) ->
    --  (nap : All IsNaperian (conts shape)) =>
    --  (inShape : InShape axisName shape k) =>
    --  IsSucc k =>
    --  (isTensorMonoid : TensorMonoid (shape.getByName axisName inShape).cont) =>
    --  Tensor (snd $ removeDuplicates shape axisName {inShape=inShape}) a
    --diagonal {shape = (_ :: _)} t axisName {k = 1} = t
    --diagonal {shape = ((_ ~> a) :: ss)} t axisName {inShape = Here} {k = (S (S k'))}
    --  = ?diagonal_rhs_1
    --diagonal {shape = (s :: ss)} t axisName {inShape = There} {k = (S (S k'))}
    --  = ?diagonal_rhs_3




  namespace AlgebraInstance
    ||| Unlike all other instantiations of 'AllX', `AllAlgebra` is not
    ||| stating that each container in an list has an algebra, but rather
    ||| 'cumulatively'. For instance, `AllAlgebra [c, d] a` is not defined as
    ||| `Algebra c a` and `Algebra d a`, bur rather as `Algebra c (Algebra d a)`
    ||| and `Algebra d a`.
    public export
    data AllAlgebra : (shape : TensorShape rank) ->
      (dtype : Type) -> Type where
      Nil : AllAlgebra [] a
      Cons : {c : Axis} -> {cs : TensorShape k} ->
        (alg : Algebra (Ext c.cont) (Tensor cs a)) =>
        (rest : AllAlgebra cs a) =>
        NewAxisConsistent c cs =>
        AllAlgebra (c :: cs) a

    {-
    AllAlgebra [c, d, e] a
    needs
    * Algebra (CTensor [c]) (CTensor [d, e] a)
    * AllAlgebra [d, e] a which needs
      * Algebra (CTensor [d]) (CTensor [e] a)
      * AllAlgebra [e] a which needs
        * Algebra (CTensor [e]) (CTensor [] a)
        * AllAlgebra [] a

    So to define AllAlgebra [c, d, e] a in total we need
    * Algebra (CTensor [c]) (CTensor [d, e] a)
    * Algebra (CTensor [d]) (CTensor [e] a)
    * Algebra (CTensor [e]) (CTensor [] a)
    -}

    public export
    reduceTensor : {shape : TensorShape rank} ->
      (allAlg : AllAlgebra shape a) =>
      Tensor shape a -> a
    reduceTensor {allAlg = []} = extract
    reduceTensor {allAlg = Cons} = reduceTensor . reduce . extractTopExt


    public export
    {shape : TensorShape rank} ->
    (allAlg : AllAlgebra shape a) =>
    Algebra (Tensor shape) a where
      reduce = reduceTensor

    -- public export
    -- {c : Cont} -> Algebra (Ext c) a =>
    -- Algebra (CTensor [c]) (CTensor [] a) where
    --   reduce t = embed $ reduce $ vectorToExt $ extract <$> t

    -- The comment below is probably not as relevant anymore
    -- ||| Since we have non-unique axis labels, this likely needs to be 
    -- ||| implemented after `dot`
    namespace ReduceAxis
      ||| Takes in a tensor `t` and an axis name which we want to reduce along.
      ||| Returns a new tensor with all occurences of this axis summed over, 
      ||| correctly zipping if this axis appears multiple times.
      ||| We also ensure that this function can only be called if the axis truly
      ||| appears in the tensor, and if its underlying container is finite.
      ||| From finite we can get algebra
      public export
      reduceAxis : {shape : TensorShape rank} ->
        (t : Tensor shape a) ->
        (atm : All TensorMonoid (conts shape)) =>
        (nap : All IsNaperian (conts shape)) =>
        {k : Nat} ->
        (toReduce : AxisName) -> (inShape : InShape toReduce shape k) =>
        IsSucc k =>
        Num a =>
        (isFinite : IsFinite (shape.getByName toReduce inShape).cont) =>
        Tensor (snd $ removeAllOccurrences shape toReduce {inShape=inShape}) a
      -- reduceAxis {shape = ((toReduce ~> c) :: as)} {atm=(tm :: tms)} t toReduce {inShape = Here} {k=S k'} {nap} with (k')
      --   _ | 0 = reduce @{algebraFinite c {isFinite=isFinite} (Tensor as a)} (extractTopExt t) -- this is the last axis to reduce
      --   reduceAxis {shape = ((toReduce ~> (Nap pos)) :: as)} {atm=(tm :: tms)} t toReduce {inShape = Here} {k=S k'} {nap = (MkIsNaperian pos)} | (S k'') = ?redddd_2_S_0 -- there is at least one more axis after this
      -- reduceAxis {shape = (s :: as)} t toReduce {inShape = There} {k}
      --   = ?redddd_3

      -- reduceAxis {shape = ((toReduce ~> c) :: ss)} (MkT t) toReduce {inShape = Here}
      --   = let 
      --     in ?reduceAxis_rhs_0
      -- reduceAxis {shape = (s :: ss)} t toReduce {inShape = There}
      --   = ?reduceAxis_rhs_1

      -- For `Tensor ["v" ~~> 4, "v" ~~> 4] a` we know that reduce produces a trace, i.e. sum of the diagonal of the matrix.
      -- But how does trace work for non-cubical tensors?
      -- How does reduction work for
      -- `t : Tensor ["b" ~> BinTree, "b" ~> BinTree] a`?
      -- reduceAxis {shape = ((toDelete ~> a) :: ss)} t toDelete {inShape = Here}
      --   = ?reduceAxis_rhs_2
      -- reduceAxis {shape = (s :: ss)} t _ {inShape = There}
      --   = ?reduceAxis_rhs_3

     -- t : Ext (Ext c (Tensor (conts ss)).Shp) !> (\ex => (cp : c .Pos (ex .shapeExt) ** Tensor (conts ss).Pos (ex .index cp)))) a
        

      --reduce : {rank : Nat} ->
      --  {shape : Vect (S rank) Cont} ->
      --  {names : Vect (S rank) String} ->
      --  (ac : AllConsistent names shape) =>
      --  CTensor shape names a ->
      --  (toDelete : String) ->
      --  (InShape : Elem toDelete names) =>
      --  (alg : Algebra (Ext (index (elemToFin InShape) shape))
      --    (CTensor (drop (FS (elemToFin InShape)) shape)
      --             (DropElem.drop names InShape)
      --             {ac=allConsistentAfterDropElems {toDelete=toDelete} {names=names} {shape=shape}}
      --             a)

{-
      public export
      allConsistentAfterDropElems : {rank : Nat} ->
        {shape : Vect (S rank) Cont} ->
        {names : Vect (S rank) String} ->
        AllConsistent names shape =>
        (InShape : Elem toDelete names) =>
        AllConsistent (DropElem.drop names InShape)
                      (drop (FS (elemToFin InShape)) shape)
      allConsistentAfterDropElems = ?todo

      allConsistentAfterDropOneElem : {rank : Nat} ->
        {shape : Vect (S rank) Cont} ->
        {names : Vect (S rank) String} ->
        AllConsistent names shape =>
        {toDelete : String} ->
        (InShape : Elem toDelete names) =>
        AllConsistent (dropElem names InShape)
                      (deleteAt (elemToFin InShape) shape)
      allConsistentAfterDropOneElem = ?todo2
      public export
      reduce : {rank : Nat} ->
        {shape : Vect (S rank) Cont} ->
        {names : Vect (S rank) String} ->
        (ac : AllConsistent names shape) =>
        CTensor shape names a ->
        (toDelete : String) ->
        (InShape : Elem toDelete names) =>
        (alg : Algebra (Ext (index (elemToFin InShape) shape))
          (CTensor (drop (FS (elemToFin InShape)) shape)
                   (DropElem.drop names InShape)
                   {ac=allConsistentAfterDropElems {toDelete=toDelete} {names=names} {shape=shape}}
                   a)
        ) => -- have to increase `index InShape` by 1 because we're not indexing, but counting
        CTensor (deleteAt (elemToFin InShape) shape)
                (dropElem names InShape)
                {ac=allConsistentAfterDropOneElem {toDelete=toDelete} {names=names} {shape=shape}}
                a
      reduce {ac=aa::ac} t _ {shape = (s :: ss)} {InShape = Here {xs=ns}} {alg}
        = let algRewr : Ext s (CTensor ss ns a) -> CTensor ss ns a
              algRewr = rewrite sym (minusZeroRight rank) in reduce
          in algRewr (extractTopExt t)
      reduce {rank = (S k)} t toDelete {shape = (s :: ss)} {names = (n :: ns)} {InShape = There later}
        = let th : Ext s (CTensor (deleteAt (indexOf later) ss) (removeIndex ns (indexOf later)) a) 
              th = (\t' => ReduceAxis.reduce t' toDelete {InShape=later}) <$> extractTopExt t
              ne : NotElem n (removeIndex ns (indexOf later))
              ne = removingElemIsStillNotElem 
          -- For some reason Idris does not automatically reduce
          -- `deleteAt (indexOf (There later)) (s :: ss)` tp
          -- `s :: deleteAt (indexOf later) ss`
          in believe_me $ embedTopExt {prf = ne} th

    -- So to define this:
    allalg3 : AllAlgebra [BinTree, List, List] ["x", "y", "z"] Int
    allalg3 = %search

    -- we need to have:
    allAlg2 : Algebra (CTensor [BinTree] ["abc"]) (CTensor [List, List] ["def", "ced"] Int)
    allAlg2 = %search

    -- we need to have:
    allAlg1 : Algebra (CTensor [List] ["a"]) (CTensor [List] ["y"] Int)
    allAlg1 = %search

    allAlg0 : AllAlgebra [List] ["x"] Int
    allAlg0 = %search

    -- we need to have:
    alg0 : Algebra (CTensor [List] ["yy"]) (CTensor [] [] Int)
    alg0 = %search



    rrr : {shape : Vect rank Axis} ->
      {names : UniqueVect rank String} ->
      AllAlgebra shape a => Tensor shape a -> a
    rrr t = reduce t

    -- rrrc : {shape : Vect rank Nat} ->
    --   {names : UniqueVect rank String} ->
    --   AllAlgebra (Vect <$> shape) names a => Tensor shape names a -> a
    -- rrrc t = reduce t

    -- agtest0 : Algebra BinTreeNode Int
    -- agtest0 = %search

    zzn : Num (Tensor [] Int)
    zzn = %search

    zz : Algebra (Ext BinTree) (Tensor [] Int)
    zz = %search

    -- zz0 : Algebra (CTensor [BinTree]) Int
    -- zz0 = %search

    -- zzt : Algebra (CTensor [BinTree] ["p"]) (CTensor [] [] Int)
    -- zzt = %search

    -- agt0 : AllAlgebra [BinTree] ["o"] Int
    -- agt0 = %search

    -- agt1 : AllAlgebra [List] ["x"] Int
    -- agt1 = %search


    -- public export
    -- {shape : List Cont} ->
    -- Algebra (CTensor shape) a => Algebra (CTensor shape) (CTensor [] a) where
    --   reduce t = embed $ reduce $ extract <$> t

t1 : Tensor [4] ["features"] Double
t1 = reduce t0 "batch"

-}

  namespace FoldableInstance
    public export
    data AllFoldable : (shape : TensorShape rank) -> Type where
        Nil : AllFoldable []
        Cons : {0 cs : TensorShape k} ->
          Foldable (Ext c.cont) =>
          AllFoldable cs =>
          NewAxisConsistent c cs =>
          AllFoldable (c :: cs)
  
    public export
    tensorFoldr : {0 shape : TensorShape rank} ->
      (allFoldable : AllFoldable shape) =>
      (a -> acc -> acc) -> acc -> Tensor shape a -> acc
    tensorFoldr {allFoldable = []} f val t = f (extract t) val
    tensorFoldr {allFoldable = Cons} f val t = foldr
      (\ct, acc => tensorFoldr f acc ct) val (extractTopExt t)
  
    public export
    {shape : TensorShape rank} ->
    (allFoldable : AllFoldable shape) =>
    Foldable (Tensor shape) where
      foldr = tensorFoldr
  
    -- concreteWorks : Tensor [7, 2] ["a", "b"] Integer -> Integer
    -- concreteWorks t = foldr (+) 0 t
  
    -- parametricCTensorWorks : {shape : Vect rank Cont} ->
    --   {names : Vect rank String} ->
    --   (ac : AllConsistent names shape) =>
    --   AllFoldable shape =>
    --   CTensor shape names Integer -> Integer
    -- parametricCTensorWorks t = foldr (+) 0 t
  
    -- parametricDoesNotWork : {shape : List Nat} ->
    --   Tensor shape Integer -> Integer
    -- parametricDoesNotWork t = foldr (+) 0 t

  namespace TraversableInstance
    public export
    data AllTraversable : (shape : TensorShape rank) -> Type where
        Nil : AllTraversable []
        Cons : {0 cs : TensorShape k} ->
          Traversable (Ext c.cont) =>
          AllTraversable cs =>
          NewAxisConsistent c cs =>
          AllTraversable (c :: cs)

    public export
    tensorTraverse : {0 shape : TensorShape rank} ->
      (allTraversable : AllTraversable shape) =>
      Applicative f =>
      (a -> f b) -> Tensor shape a -> f (Tensor shape b)
    tensorTraverse {allTraversable = []} f t = pure <$> f (extract t)
    tensorTraverse {allTraversable = Cons} f t = embedTopExt <$> 
      traverse (\ct => tensorTraverse f ct) (extractTopExt t)

    public export
    {shape : TensorShape rank} ->
    (allTraversable : AllTraversable shape) =>
    (allFoldable : AllFoldable shape) =>
    Traversable (Tensor shape) where
      traverse = tensorTraverse

  namespace NaperianInstance
    public export
    transposeMatrix : {i, j : Axis} ->
      NewAxisConsistent i [j] => NewAxisConsistent j [i] =>
      (ni : IsNaperian i) => (nj : IsNaperian j) =>
      Tensor [i, j] a -> Tensor [j, i] a
    transposeMatrix {ni=(MkIsNaperian _ _)} {nj=(MkIsNaperian _ _)}
      = restructure transpose

    transposeTest : Tensor ["i" ~~> 2, "j" ~~> 3] a ->
                    Tensor ["j" ~~> 3, "i" ~~> 2] a
    transposeTest = transposeMatrix

    ||| Like 'positions' from Naperian, but parametric, and not requiring the
    ||| Naperian instance here
    public export
    positions : {0 c : Axis} ->
      {sh : c.cont.Shp} -> Tensor [c] (c.cont.Pos sh)
    positions = extToVector (positionsCont {sh=sh})

namespace ShowInstance
  public export
  data AllShow : (shape : TensorShape rank) ->
    (a : Type) -> Type where
    Nil : Show a => AllShow [] a
    -- for type below, we should be able to define what shExt is without referencing CTensor cs a? 
    Cons : {0 cs : TensorShape k} ->
      Show (c.cont `fullOf` Tensor cs a) =>
      NewAxisConsistent c cs =>
      AllShow (c :: cs) a

  public export
  show' : {0 rank : Nat} ->
    {shape : TensorShape rank} ->
    (allShow : AllShow shape a) =>
    Tensor shape a -> String
  show' {allShow = Nil} t = show (extract t)
  show' {allShow = Cons @{sh}} t = show (extractTopExt t)

  public export
  {shape : TensorShape rank} ->
  (allShow : AllShow shape a) =>
  Show (Tensor shape a) where
      show t = show' {allShow = allShow} t

  -- %hint
  -- public export
  -- allShowCubical : {shape : Vect rank Axis} ->
  --   (ac : AxesConsistent shape) =>
  --   Show a =>
  --   AllShow shape a
  -- allShowCubical {shape=[], ac = []} = Nil
  -- allShowCubical {shape=(c :: cs), ac = a::as}
  --   = ?allShowCubical_rhs -- Cons @{?oibim}

  -- public export
  -- {shape : Vect rank Axis} ->
  -- (ac : AllConsistent names (Vect <$> shape)) =>
  -- Show a =>
  -- Show (Tensor shape names a) where
  --   show t = show' {allShow=allShowCubical} t
  --   -- show {shape=(c :: cs)} t = show' {allShow = Cons @{?oiim}} t

  -- showCubical : {shape : List Nat} -> Show a => Tensor shape a -> String
  -- showCubical {shape=[]} t = show' {allShow = Nil} t
  -- showCubical {shape=(c :: cs)} t = show' {allShow = Cons @{?oiim}} t


  sst : {shape : TensorShape rank} ->
    AllShow shape a => Tensor shape a -> String
  sst t = show t

  -- sstc : {shape : List Nat} -> Show a => Tensor shape a -> String
  -- sstc t = show t

tEx0 : Tensor ["batch" ~~> 3, "features" ~~> 4] Double
tEx0 = ># [ [0, 1, 2, 3]
          , [4, 5, 6, 7]
          , [8, 9, 10, 11]]


tEx1 : Tensor ["i" ~~> 2, "j" ~~> 3, "i" ~~> 2] Double
tEx1 = ># [ [[0, 1], [2, 3], [4, 5]]
          , [[6, 7], [8, 9], [10, 11]] ]

namespace TensorContractions
  public export
  dotWith : {shape : TensorShape rank} ->
    Algebra (Tensor shape) c => All TensorMonoid (conts shape) =>
    (a -> b -> c) ->
    Tensor shape a -> Tensor shape b -> Tensor [] c
  dotWith f xs ys = embed $ reduce $ uncurry f <$> liftA2Tensor xs ys

  public export
  dot : {shape : TensorShape rank} ->
    Num a =>
    Algebra (Tensor shape) a => All TensorMonoid (conts shape) =>
    Tensor shape a -> Tensor shape a -> Tensor [] a
  dot xs ys = dotWith (*) xs ys

  namespace DotAxis
{-
    public export
    sh : Vect 3 Cont
    sh = [Vect 2, Vect 3, Vect 4]

    public export
    nn : UniqueVect 3 String
    nn = ["a", "b", "c"]

    ||| This ensures axes are coherently bound between between
    ||| names1 -> shape1 and names2 -> shape2
    public export
    coherentlyBound :
      (shape1 : Vect rank1 Cont) ->
      (shape2 : Vect rank2 Cont) ->
      (names1 : UniqueVect rank1 String) ->
      (names2 : UniqueVect rank2 String) ->
      Type
    coherentlyBound shape1 shape2 names1 names2 =
      selectAxes shape1 names1 (intersect names1 names2) {al=allElemIntersectFst names1 names2} = selectAxes shape2 names2 (intersect names1 names2) {al=allElemIntersectSnd names1 names2}


    public export
    coherentlyBoundCons : 
      {s : Cont} -> {ss : Vect rank Cont} ->
      {n : String} -> {ns : UniqueVect rank String} ->
      {shape2 : Vect rank2 Cont} ->
      {names2 : UniqueVect rank2 String} ->
      NotElem n ns =>
      coherentlyBound (s :: ss) shape2 (n :: ns) names2 ->
      coherentlyBound ss shape2 ns names2
    coherentlyBoundCons prf = ?coherentlyBoundCons_rhs

    ||| Shape of the output vector
    ||| Given    [2, 3] ["i", "j"]
    ||| and      [3, 4] ["j", "k"]
    ||| produces [2, 4] ["i", "k"]
    public export
    combinedShape :
      (shape1 : Vect rank1 Cont) ->
      (shape2 : Vect rank2 Cont) ->
      (names1 : UniqueVect rank1 String) ->
      (names2 : UniqueVect rank2 String) ->
      (coh : coherentlyBound shape1 shape2 names1 names2) =>
      Vect (numSymmetricDifference names1 names2) Cont
    combinedShape [] shape2 [] names2 = shape2
    combinedShape {rank1=S k} (s :: ss) shape2 (n :: ns) names2 @{cc} with (decElemInUniqueVect n names2)
      _ | (Yes prf) =
        let tt = coherentlyBoundCons {rank=k} {rank2=rank2} {s=s} {ss=ss} {n=n} {ns=ns} {shape2=shape2} {names2=names2}
        in ?abc -- combinedShape ss shape2 ns names2 @{(tt ?hhh)}
      _ | (No nprf) = ?def -- s :: (combinedShape ss shape2 ns names2 @{(?hhhh)})
    
    hh : selectAxes Sh1 N1 ["i"] = selectAxes Sh2 N2 ["i"]
    hh = Refl


-}

    -- ||| Combines the labels of two axes
    -- ||| Given    ["i", "j", "i"]
    -- ||| and      ["i", "k"]
    -- ||| produces ["j", "i", "k"] (or should it produce ["i", "j", "k"]?)
    -- public export
    -- combineNames :
    --   (names1 : Vect n String) ->
    --   (names2 : Vect m String) ->
    --   Vect (fst (UniqueVect.fromVect (names1 ++ names2))) String
    -- combineNames names1 names2 with (UniqueVect.fromVect (names1 ++ names2))
    --   _ | (_ ** res) = toVect res

    -- ||| Given a list of axes, the names of these axes, and a subset of their 
    -- ||| names, return the axes corresponding to that subset
    -- public export
    -- selectAxes : (shape : Vect rank Axis) ->
    --   (names : Vect rank AxisName) ->
    --   AxesConsistent shape =>
    --   (toSelect : Vect m AxisName) -> -- technically should be UniqueVect
    --   (al : All (\x => Elem x names) toSelect) =>
    --   Vect m Cont
    -- selectAxes _ _ [] = []
    -- selectAxes shape names (s :: ss) @{(p :: ps)} 
    --   = (index (indexOf p) shape) :: selectAxes shape names ss @{ps}

    -- public export
    -- N1 : Vect 3 String
    -- N1 = ["i", "j", "i"]

    -- public export
    -- N2 : Vect 3 String
    -- N2 = ["i", "k", "l"]

    -- ||| Generalised dot product which contracts over shared axes
    -- ||| For instance, given 
    -- ||| Given    [2, 3, 2] ["i", "j", "i"]
    -- ||| and      [2, 4]    ["i", "k"]
    -- ||| produces [2, 3, 4] ["i", "j", "k"]
    -- public export
    -- dot : {shape1 : Vect rank1 Cont} ->
    --   {shape2 : Vect rank2 Cont} ->
    --   {names1 : Vect rank1 String} ->
    --   {names2 : Vect rank2 String} ->
    --   AllConsistent names1 shape1 => -- t1 is consistently bound
    --   AllConsistent names2 shape2 => -- t2 to
    --   AllConsistent (names1 ++ names2) (shape1 ++ shape2) => -- but the result should too
    --   Num a =>
    --   CTensor shape1 names1 a -> CTensor shape2 names2 a ->
    --   CTensor (selectAxes (shape1 ++ shape2) (names1 ++ names2)
    --             (snd (UniqueVect.fromVect (names1 ++ names2))))
    --           (toVect (snd (fromVect names1 ++ names2)))
    --           a
    -- dot {rank1 = 0} {shape1 = []} {names1 = []} t t' = (extract t * ) <$> t'
    -- dot {rank1 = (S k)} {shape1 = (s :: ss)} {names1 = (n :: ns)} t t'
    --   with (decElemInUniqueVect n names2)
    --   _ | (Yes prf) = ?dot_rhs_1
    --   _ | (No nprf) = ?dot_rhs_2

    
    public export
    outerWith : {i, j : Axis} ->
      TensorMonoid i.cont => TensorMonoid j.cont =>
      (ac : NewAxisConsistent i [j]) =>
      (a -> b -> c) ->
      Tensor [i] a -> Tensor [j] b -> Tensor [i, j] c
    outerWith f t t' =
      let tt = (\(t, a) => strength a t) <$> strength t' t
      in uncurry f <$> fromNestedTensor tt

    public export
    outer : {i, j : Axis} ->
      TensorMonoid i.cont => TensorMonoid j.cont =>
      (ac : NewAxisConsistent i [j]) =>
      Num a => 
      Tensor [i] a -> Tensor [j] a -> Tensor [i, j] a
    outer = outerWith (*)

    public export
    matrixVectorProduct : Num a => {i, j : Axis} ->
      TensorMonoid j.cont =>
      AllAlgebra [j] a =>
      (ac : NewAxisConsistent i [j]) =>
      Tensor [i, j] a -> Tensor [j] a -> Tensor [i] a
    matrixVectorProduct m v = dot v <-$> m

    public export
    vectorMatrixProduct : Num a => {i, j : Axis} ->
      TensorMonoid i.cont => 
      (ac : NewAxisConsistent i [j]) =>
      Algebra (Ext i.cont) (Tensor [j] a) =>
      Tensor [i] a -> Tensor [i, j] a -> Tensor [j] a
    vectorMatrixProduct v m =
      let em : Ext i.cont (Tensor [j] a) := extractTopExt m
          ev : Ext i.cont (Tensor [] a) := extractTopExt v
      in reduce $ (\(x, gx) => ((extract x) *) <$> gx) <$> liftA2 ev em
      --let t : CTensor [i] (CTensor [j] a) := toNestedTensor m
      --in extract $ dotWith (\x, gx => (x *) <$> gx) v t

    public export
    matMul : Num a => {i, j, k : Axis} ->
      TensorMonoid j.cont =>
      (ac1 : NewAxisConsistent i [j]) =>
      (ac2 : NewAxisConsistent j [k]) =>
      (ac3 : NewAxisConsistent i [k]) =>
      Algebra (Ext j.cont) (Tensor [k] a) =>
      Tensor [i, j] a -> Tensor [j, k] a -> Tensor [i, k] a
    matMul m1 m2 = fromNestedTensor $ 
      toNestedTensor m1 <&> (\row => vectorMatrixProduct row m2)

    -- "ij,kj->ki"
    public export
    matrixMatrixProduct : {i, j, k : Axis} ->
      (ac1 : NewAxisConsistent i [j]) =>
      (ac2 : NewAxisConsistent k [j]) =>
      (ac3 : NewAxisConsistent k [i]) =>
      Num a =>
      TensorMonoid j.cont =>
      (allAlg : AllAlgebra [j] a) =>
      Tensor [i, j] a -> Tensor [k, j] a -> Tensor [k, i] a
    matrixMatrixProduct m1 = tensorMapFirstAxis (matrixVectorProduct m1)

-- tt0 : CTensor [] [] Integer
-- tt0 = pure 13
-- 
-- fg : CTensor [Vect 7] ["i"] Integer
-- fg = pure 5
-- 
-- fgh : CTensor [Vect 7, Vect 7] ["i", "j"] Integer
-- fgh = pure 13
-- 
-- sht0 : String
-- sht0 = show tt0
-- 
-- fsh0 : Show (Vect 8 `fullOf` (CTensor [] [] Integer))
-- fsh0 = %search
-- 
-- fsh : String
-- fsh = show fg
-- 
-- fshh : String
-- fshh = show fgh
-- 
-- ll : List' Integer
-- ll = fromConcreteTy [1,2,3,4,5]
-- 
-- bt : BinTree' Integer
-- bt = fromConcreteTy $ Node 1 (Node 2 (Leaf 3) (Leaf 4)) (Leaf 5)
-- 
-- rt : RoseTree' Char
-- rt = fromConcreteTy (Node 'c' [Leaf 'c', Leaf 'd'])


public export
tEx : Tensor ["i" ~~> 3, "j" ~~> 4] Integer
tEx = ># [ [1, 2, 3, 4]
         , [5, 6, 7, 8]
         , [9, 10, 11, 12] ]

public export
Ex2 : Tensor ["k" ~~> 12] Integer
Ex2 = reshape tEx

public export
Ex3 : Tensor ["i" ~~> 2, "j" ~~> 6] Integer
Ex3 = reshape Ex2

namespace IndexingByAxisNames
  --public export
  --posTypeOfAxisName : {shape : TensorShape rank} ->
  --  (indexAxis : AxisName) ->
  --  (InShape : indexAxis `InShape` shape) =>
  --  Type

  public export
  indexName : {shape : TensorShape rank} ->
    (t : Tensor shape a) ->
    (indexAxis : AxisName) ->
    IsSucc k =>
    (InShape : InShape indexAxis shape k) =>
    Type
    

namespace SetterGetter
  ||| Machinery for indexing into a Tensor based on absolute positions
  ||| It depends on shape, but also on the tensor t itself
  ||| Provides a compile-time guarantee that we won't be out of bounds
  ||| This dependency is not needed for cubical tensors
  ||| Technically, to index we only need the shapes, not the entire tensor
  public export
  data Index :
    (shape : TensorShape rank) ->
    (t : Tensor shape a) -> Type where
    Nil : {t : Tensor [] a} -> Index [] t
    (::) : {cs : TensorShape k} ->
      NewAxisConsistent c cs =>
      {t : Tensor (c :: cs) a} ->
      (p : c.cont.Pos (shapeExt (extractTopExt t))) ->
      Index cs (index (extractTopExt t) p) ->
      Index (c :: cs) t
  
  %name Index is, js

  public export
  index : {shape : TensorShape rank} ->
    (t : Tensor shape a) -> Index shape t -> a
  index {shape = []} t [] = extract t
  index {shape = (c :: cs)} t (i :: is) =
    index (index (extractTopExt t) i) is

  public export infixr 9 @@
  public export
  (@@) : {shape : TensorShape rank} ->
    (t : Tensor shape a) -> Index shape t -> a
  (@@) = index

  public export 
  set : {shape : TensorShape rank} ->
    (t : Tensor shape a) ->
    (iop : InterfaceOnPositions (Tensor (conts shape)) Eq) =>
    Index shape t -> a -> Tensor shape a
  set {shape = []} t is val = MkT $ set (GetT t) () val
  set {shape = (c :: cs)} t (i :: is) val =
    let ts = index (extractTopExt t) i
        -- tg = set ts is val
    in ?set_rhs_1 -- need to use index here... or even better phrase this using lenses?
  -- maybe InterfaceOnPositions needs a 'AllInterfaceOnPositions' counterpart?

  -- setC t [] x = MkT $ set (GetT t) () x
  -- setC {shape=(s::ss)} t (i :: is) x =
  --   let tNested : Tensor [s] (Tensor ss a) := toNestedTensor t
  --       ts : Tensor ss a := setC (indexC tNested [i]) is x
  --   in fromNestedTensor $ MkT $ set (GetT tNested) (i ** ()) ts

  -- public export
  -- t00 : CTensor [Maybe, List] ["m", "l"] Integer
  -- t00 = ># Just [10, 20, 30, 40, 50, 60, 70]

  -- public export
  -- t11 : Tensor [2, 3] ["i", "j"] Integer
  -- t11 = ># [[1,2,3], [4,5,6]]

  -- public export
  -- t22 : CTensor [BinTree, List] ["b", "l"] Integer
  -- t22 = ># Node [1,2] (Leaf [3,4]) (Leaf [5,6])

  -- t33 : CTensor [BinTree] ["b"] Integer
  -- t33 = ># Node 1 (Leaf 2) (Leaf 3)

  -- t333 : CTensor [Vect 2] ["v"] Integer
  -- t333 = ># [1, 2]
  
  -- t44 : CTensor [] [] Integer
  -- t44 = ># 13

  -- public export
  -- jj : Integer
  -- jj = index t11 [1, 1]


namespace CubicalSetterGetter
  public export
  data IndexC : Vect rank Nat -> Type where
    Nil : IndexC []
    (::) : Fin n -> IndexC ns -> IndexC (n :: ns)

  {-
  public export
  indexC : {shape : TensorShape rank} ->
    -- (ac : AllConsistent names (Vect <$> shape)) =>
    Tensor shape names a ->
    IndexC shape -> a
  indexC t [] = index (GetT t) ()
  indexC {ac=a::as} t (i :: is) = indexC (index (GetT $ toNestedTensor t) (i ** ())) is 

  public export
  setC : {shape : Vect rank Nat} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names (Vect <$> shape)) =>
    Tensor shape names a -> IndexC shape -> a -> Tensor shape names a
  setC t [] x = MkT $ set (GetT t) () x
  setC {shape=(s::ss)} {names=n::ns} {ac=aa::aas} t (i :: is) x =
    let tNested : Tensor [s] [n] (Tensor ss ns a) := toNestedTensor t
        ts : Tensor ss ns a := setC (indexC tNested [i]) is x
    in fromNestedTensor $ MkT $ set (GetT tNested) (i ** ()) ts

-- sTest : Tensor [2, 3] Integer
-- sTest = setC t11 [1, 1] 100

||| Functionality for slicing tensors
namespace Slice
  ||| Needs to be appropriated for named tensors
  namespace CubicalSlicing
    ||| Machinery for slicing cubical tensors
    ||| Crucially, different from the indexing one in the definition of (::)
    ||| Here we have Fin (S m) instead of Fin m
    public export
    data Slice : (shape : Vect rank Nat) -> Type where
      Nil : Slice []
      (::) : Fin (S m) -> Slice ms -> Slice (m :: ms)

  public export
  sliceToShape : {shape : Vect rank Nat} -> Slice shape -> Vect rank Nat
  sliceToShape [] = []
  sliceToShape (s :: ss) = finToNat s :: sliceToShape ss

  public export
  take : {shape : Vect rank Nat} ->
    (ac : AllConsistent names (Vect <$> shape)) =>
    (slice : Slice shape) ->
    (newNames : Vect rank String) ->
    (ac' : AllConsistent newNames (Vect <$> sliceToShape slice)) =>
    Tensor shape names a ->
    Tensor (sliceToShape slice) newNames a
  take {ac=[]} {ac'=[]} [] _ t = t
  take {ac=aa::aas} {ac'=aa'::aas'} (s :: ss) (n :: ns) t
    = embedTopExt $ take ss ns <$> take s (extractTopExt t)


  ||| What does it mean to slice a non-cubical tensor?
  ||| CTensor [BinTree, List] a
  namespace NonCubicalSlicing
-}


    -- namespace Index
    --   ||| Datatype for indexing into a Naperian tensor
    --   public export
    --   data IndexNaperian : (shape : TensorShape rank) ->
    --     (allNap : All IsNaperian (conts shape)) =>
    --     Type where
    --     Nil : IndexNaperian []
    --     (::) : {0 a : Axis} -> {0 as : TensorShape k} ->
    --       (rest : All IsNaperian (conts as)) =>
    --       (nap : IsNaperian a) =>
    --       Log a ->
    --       NewAxisConsistent a as =>
    --       IndexNaperian as {allNap=rest} ->
    --       IndexNaperian (a :: as) {allNap=(toContNaperian nap :: rest)}

    -- public export
    -- tensorLookup : {shape : TensorShape rank} ->
    --   All IsNaperian (conts shape) =>
    --   Tensor shape a ->
    --   (IndexNaperian shape -> a)
    -- tensorLookup {shape = []} t _ = extract t
    -- tensorLookup {shape = (_ :: as)} t ((::) {nap = (MkIsNaperian _ _)} i is)
    --   = tensorLookup (lookup (extractTopExt t) i) is

    -- public export
    -- tensorTabulate : {shape : TensorShape rank} ->
    --   (allNap : All IsNaperian (conts shape)) =>
    --   (IndexNaperian shape -> a) -> Tensor shape a
    -- tensorTabulate {shape = [], allNap = []} f = embed (f Nil)
    -- tensorTabulate {shape = ((_ ~> _) :: _), allNap = MkIsNaperian _ :: _} f
    --    = embedTopExt $ tabulate $ \i => tensorTabulate $ \is => f (i :: is)

    -- public export
    -- {shape : TensorShape rank} ->
    -- (allAppl : All TensorMonoid (conts shape)) =>
    -- (allNaperian : All IsNaperian (conts shape)) =>
    -- Naperian (Tensor shape) where
    --   Log = IndexNaperian shape
    --   lookup = tensorLookup
    --   tabulate = tensorTabulate
