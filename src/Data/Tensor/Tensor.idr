module Data.Tensor.Tensor

import public Data.DPair
import public Data.Fin.Split

import public Data.Container.Base
import public Data.Container.Applicative
import public Data.Container.Base.Object.Instances as Cont
import public Data.Num

import public Data.Layout
import public Misc

%hide Syntax.WithProof.prefix.(@@) -- used here for indexing

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
This file defines the main construction of this repository `CTensor`, and
provides instances and utilities for working with them.
`CTensor` is a datatype which is simply a wrapper around the extension of
a composition of containers.


Provided instances include:
Functor, Applicative, Foldable, Naperian, Algebra, Eq, Show, Num, Neg, Abs,
Fractional, Exp

Functionality includes:
* Converting to and from nested tensors
* Converting to and from concrete types
* Various tensor contractions
* Slicing for cubical tensors
* Getters
* Setters (TODO)
* Functionality for general reshaping such as views, traversals
* Concrete reshape for cubical tensors

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| Container Tensor: a tensor whose shape is a list of containers
||| This is merely a wrapper around `Ext (Tensor shape) a` to help type
||| inference
public export
record CTensor (shape : List Cont) (a : Type) where
  constructor MkT
  GetT : Ext (Cont.Tensor shape) a

%name CTensor t, t', t''

||| Cubical tensors. Used name 'Tensor' for backwards compatibility with
||| terminology in the numpy/pytorch ecosystem
public export
Tensor : (shape : List Nat) -> Type -> Type
Tensor shape = CTensor (Vect <$> shape)

public export
Functor (CTensor shape) where
  map f (MkT t) = MkT $ map f t

namespace NestedTensorUtils
  public export
  extract : CTensor [] a -> a
  extract (MkT t) = extract t

  public export
  embed : a -> CTensor [] a
  embed a = MkT (toScalar a)

  ||| With the added data of the wrapper around (Ext (Tensor shape) a), this
  ||| effectively states a list version of the following isomorphism
  ||| Ext c . Ext d = Ext (c . d)
  public export
  fromExtensionComposition : {shape : List Cont} ->
    composeExtensions shape a -> CTensor shape a
  fromExtensionComposition {shape = []} ce = MkT ce
  fromExtensionComposition {shape = (_ :: _)} (sh <| contentAt) = MkT $
    let rest = GetT . fromExtensionComposition . contentAt
    in (sh <| shapeExt . rest) <| \(cp ** fsh) => index (rest cp) fsh

  public export
  toExtensionComposition : {shape : List Cont} ->
    CTensor shape a -> composeExtensions shape a
  toExtensionComposition {shape = []} (MkT t) = t
  toExtensionComposition {shape = (_ :: _)} (MkT ((csh <| cpos) <| idx))
    = csh <| \d => toExtensionComposition (MkT (cpos d <| curry idx d))

  ||| For this and the function below, the commented out definition is 'cleaner'
  ||| but it requires non-erased `c` and `cs`
  public export
  extractTopExt : CTensor (c :: cs) a -> Ext c (CTensor cs a)
  extractTopExt (MkT (sh <| ind)) = shapeExt sh <| \p => MkT $ index sh p <| \p' => ind (p ** p')
  -- extractTopExt t = fromExtensionComposition <$> toExtensionComposition t

  public export
  embedTopExt : Ext c (CTensor cs a) -> CTensor (c :: cs) a
  embedTopExt e =
    let tp = GetT . index e
    in MkT $ (shapeExt e <| shapeExt . tp) <| \(p ** p') => index (tp p) p'
  --embedTopExt e = fromExtensionComposition  $ toExtensionComposition <$> e

  ||| This is useful because container composition adds non-trivial data to the
  ||| vector type (i.e. `c >@ Scalar` is not equal to `c`)
  public export
  extToVector : Ext c a -> CTensor [c] a
  extToVector e = MkT $ (shapeExt e <| \_ => ()) <| \(cp ** ()) => index e cp

  public export
  vectorToExt : CTensor [c] a -> Ext c a
  vectorToExt (MkT t) = shapeExt (shapeExt t) <| \cp => index t (cp ** ())

  public export
  toNestedTensor : CTensor (c :: cs) a -> CTensor [c] (CTensor cs a)
  toNestedTensor = extToVector . extractTopExt

  public export
  fromNestedTensor : CTensor [c] (CTensor cs a) -> CTensor (c :: cs) a
  fromNestedTensor = embedTopExt . vectorToExt

  public export
  tensorMapFirstAxis : (f : CTensor cs a -> CTensor ds a) ->
    CTensor (c :: cs) a -> CTensor (c :: ds) a
  tensorMapFirstAxis f = fromNestedTensor . map f . toNestedTensor

  public export infixr 4 <-$>
  ||| Is meant to look like infix map (i.e. `<$>`) with the added difference
  ||| that we keep the container on the left side untouched, hence the `<-$>`
  public export
  (<-$>) : (f : CTensor cs a -> CTensor ds a) ->
    CTensor (c :: cs) a -> CTensor (c :: ds) a
  (<-$>) = tensorMapFirstAxis

namespace TensorFromConcrete
  public export
  concreteTypeTensor : (shape : List Cont) ->
    (allConcrete : AllConcrete shape) =>
    Type -> Type
  concreteTypeTensor [] {allConcrete = []} = concreteType {cont=Scalar}
  concreteTypeTensor (c :: cs) {allConcrete = Cons @{fc}}
    = (concreteType @{fc}) . (concreteTypeTensor cs)

  public export
  concreteTypeFunctor : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    Functor (concreteTypeTensor shape)
  concreteTypeFunctor {shape = []} {allConcrete = []}
    = concreteFunctor {cont=Scalar}
  concreteTypeFunctor {shape = (c :: cs)} {allConcrete = Cons @{fc}}
    = Functor.Compose @{concreteFunctor @{fc} } @{concreteTypeFunctor}

  public export
  concreteToExtensions : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    concreteTypeTensor shape a -> composeExtensions shape a
  concreteToExtensions {shape = []} {allConcrete = []} ct = fromConcreteTy ct
  concreteToExtensions {shape = (_ :: _)} {allConcrete = Cons} ct =
    concreteToExtensions <$> fromConcreteTy ct

  public export
  extensionsToConcreteType : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    composeExtensions shape a -> concreteTypeTensor shape a
  extensionsToConcreteType {shape = []} {allConcrete = []} ct = toConcreteTy ct
  extensionsToConcreteType {shape = (_ :: _)} {allConcrete = Cons @{fc}} ct
    = (map @{concreteFunctor @{fc}} extensionsToConcreteType) (toConcreteTy ct)

  public export
  toTensor : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    concreteTypeTensor shape a -> CTensor shape a
  toTensor = fromExtensionComposition . concreteToExtensions

  public export
  fromTensor : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    CTensor shape a -> concreteTypeTensor shape a
  fromTensor = extensionsToConcreteType . toExtensionComposition

  ||| Many containers have a `FromConcrete` instance, allowing them to easily
  ||| be converted to and from a (usually familiar) Idris type
  ||| This works with tensors defined as a fold over contianers, but it requires
  ||| burdensome shape annotations everywhere
  ||| The decision was made to wrap that fold in `CTensor` as above, and then
  ||| (as this isn't a container anymore) provide equally named functions like
  ||| the ones `FromConcrete` provides. Idris' name resolution should be able to
  ||| detect which one needs to be used at call sites
  public export
  fromConcreteTy : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    concreteTypeTensor shape a -> CTensor shape a
  fromConcreteTy = toTensor

  public export
  toConcreteTy : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    CTensor shape a -> concreteTypeTensor shape a
  toConcreteTy = fromTensor

  public export prefix 0 >#, #>

  ||| Prefix operator for converting from a concrete type to a tensor
  ||| We read it as a map `>` going into the tensor `#`
  public export
  (>#) : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    concreteTypeTensor shape a -> CTensor shape a
  (>#) = fromConcreteTy

  ||| Prefix operator for converting from a tensor to concrete type
  ||| We read it as a map `>` going out of the tensor `#`
  public export
  (#>) : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    CTensor shape a -> concreteTypeTensor shape a
  (#>) = toConcreteTy

  public export infixr 0 >#>, #>#

  public export
  (>#>) : {shapeOld, shapeNew : List Cont} ->
    (allConcreteOld : AllConcrete shapeOld) =>
    (allConcreteNew : AllConcrete shapeNew) =>
    (CTensor shapeOld a -> CTensor shapeNew b) ->
    concreteTypeTensor shapeOld a -> concreteTypeTensor shapeNew b
  (>#>) f ct = #> (f (># ct))

  public export
  (#>#) : {shapeOld, shapeNew : List Cont} ->
    (allConcreteOld : AllConcrete shapeOld) =>
    (allConcreteNew : AllConcrete shapeNew) =>
    (concreteTypeTensor shapeOld a -> concreteTypeTensor shapeNew b) ->
    CTensor shapeOld a -> CTensor shapeNew b
  (#>#) f t = ># (f (#> t))


namespace TensorInstances
  namespace ApplicativeInstance
    public export
    tensorReplicate : {shape : List Cont} ->
      (allAppl : All TensorMonoid shape) =>
      (x : a) -> CTensor shape a
    tensorReplicate {shape = []} = embed
    tensorReplicate {shape = (_ :: _)} {allAppl = (::) _ _ }
      = fromExtensionComposition
      . pure
      . toExtensionComposition
      . tensorReplicate

    public export
    liftA2Tensor : {shape : List Cont} ->
      (allAppl : All TensorMonoid shape) =>
      CTensor shape a -> CTensor shape b -> CTensor shape (a, b)
    liftA2Tensor {allAppl=[]} (MkT t) (MkT t') = embed (index t (), index t' ())
    liftA2Tensor {allAppl=(::) _ _} t t' = embedTopExt $
      uncurry liftA2Tensor <$> liftA2 (extractTopExt t) (extractTopExt t')

    public export
    {shape : List Cont} -> (allAppl : All TensorMonoid shape) =>
    Applicative (CTensor shape) where
      pure = tensorReplicate
      fs <*> xs = uncurry ($) <$> liftA2Tensor fs xs

    ttt : {shape : List Cont} -> All TensorMonoid shape => (x : a) -> CTensor shape a
    ttt x = pure x


    -- tth : {shape : List Nat} -> All TensorMonoid (Vect <$> shape)
    -- tth = %search

    -- tttc : {shape : List Nat} -> (x : a) -> Tensor shape a
    -- tttc x = pure x


  namespace EqInstance
    public export
    data AllEq : List Cont -> Type -> Type where
      Nil : Eq a => AllEq [] a
      Cons : Eq (c `fullOf` CTensor cs a) =>
        AllEq (c :: cs) a

    public export
    tensorEq : {shape : List Cont} -> (allEq : AllEq shape a) =>
      CTensor shape a -> CTensor shape a -> Bool
    tensorEq {allEq = []} t1 t2 = extract t1 == extract t2
    tensorEq {allEq = Cons} t1 t2 = (extractTopExt t1) == (extractTopExt t2)

    public export
    {shape : List Cont} -> (allEq : AllEq shape a) =>
      Eq (CTensor shape a) where
        (==) = tensorEq {allEq = allEq}

    {n : Nat} -> Eq ((cp : Fin n ** ())) where
      x == y = fst x == fst y

    -- Turns out only this is sufficient for the setC function to work
    %hint
    public export
    interfacePosEq : {n : Nat} -> InterfaceOnPositions (Cont.Tensor [Vect n]) Eq
    interfacePosEq = MkI

    teq : {shape : List Cont} -> AllEq shape a => CTensor shape a -> Bool
    teq t = let tt = t == t in ?teq_rhs

    teqc : {shape : List Nat} -> AllEq (Vect <$> shape) a => Tensor shape a -> Bool
    teqc t = let tt = t == t in ?wuuuu

  -- public export
  -- vectInterfacePos : {n : Nat} -> InterfaceOnPositions (Vect n) DecEq
  -- vectInterfacePos = MkI

  namespace NumericInstances
    public export
    {shape : List Cont} -> Num a => All TensorMonoid shape =>
    Num (CTensor shape a) where
        fromInteger = tensorReplicate . fromInteger
        t + t' = uncurry (+) <$> liftA2Tensor t t'
        t * t' = uncurry (*) <$> liftA2Tensor t t'

    public export
    {shape : List Cont} -> Neg a => All TensorMonoid shape =>
    Neg (CTensor shape a) where
      negate = (negate <$>)
      xs - ys = (uncurry (-)) <$> liftA2 xs ys

    -- TODO this throws an error?
    negNotFound : {shape : List Nat} -> Neg a => Neg (Tensor shape a)
    negNotFound = ?interfaceProblemsAgain

    public export
    {shape : List Cont} -> Abs a => All TensorMonoid shape =>
    Abs (CTensor shape a) where
      abs = (abs <$>)

    public export
    {shape : List Cont} -> Fractional a => All TensorMonoid shape =>
    Fractional (CTensor shape a) where
      t / v = (uncurry (/)) <$> liftA2 t v

    public export
    {shape : List Cont} -> Exp a => All TensorMonoid shape => Exp (CTensor shape a) where
      exp = (exp <$>)
      log = (log <$>)
      minusInfinity = pure minusInfinity


  namespace AlgebraInstance
    ||| Unlike all other instantiations of 'AllX', `AllAlgebra` is not
    ||| stating that each container in an list has an algebra, but rather
    ||| 'cumulatively'. For instance, `AllAlgebra [c, d] a` is not defined as
    ||| `Algebra c a` and `Algebra d a`, bur rather as `Algebra c (Algebra d a)`
    ||| and `Algebra d a`.
    public export
    data AllAlgebra : (shape : List Cont) -> (dtype : Type) -> Type where
      Nil : AllAlgebra [] a
      Cons : (alg : Algebra (Ext c) (CTensor cs a)) =>
        (rest : AllAlgebra cs a) =>
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
    reduceTensor : {shape : List Cont} ->
      (allAlg : AllAlgebra shape a) =>
      CTensor shape a -> a
    reduceTensor {allAlg = []} = extract
    reduceTensor {allAlg = Cons} = reduceTensor . reduce . extractTopExt

    public export
    {shape : List Cont} -> (allAlg : AllAlgebra shape a) =>
    Algebra (CTensor shape) a where
      reduce = reduceTensor

    -- public export
    -- {c : Cont} -> Algebra (Ext c) a =>
    -- Algebra (CTensor [c]) (CTensor [] a) where
    --   reduce t = embed $ reduce $ vectorToExt $ extract <$> t

    -- So to define this:
    allalg3 : AllAlgebra [BinTree, List, List] Int
    allalg3 = %search

    -- we need to have:
    allAlg2 : Algebra (CTensor [BinTree]) (CTensor [List, List] Int)
    allAlg2 = %search

    -- we need to have:
    allAlg1 : Algebra (CTensor [List]) (CTensor [List] Int)
    allAlg1 = %search

    allAlg0 : AllAlgebra [List] Int
    allAlg0 = %search

    -- we need to have:
    alg0 : Algebra (CTensor [List]) (CTensor [] Int)
    alg0 = %search



    rrr : {shape : List Cont} -> AllAlgebra shape a => CTensor shape a -> a
    rrr t = reduce t

    rrrc : {shape : List Nat} -> AllAlgebra (Vect <$> shape) a => Tensor shape a -> a
    rrrc t = reduce t

    agtest0 : Algebra BinTreeNode Int
    agtest0 = %search

    zzn : Num (CTensor [] Int)
    zzn = %search

    zz : Algebra (Ext BinTree) (CTensor [] Int)
    zz = %search

    zz0 : Algebra (CTensor [BinTree]) Int
    zz0 = %search

    zzt : Algebra (CTensor [BinTree]) (CTensor [] Int)
    zzt = %search

    agt0 : AllAlgebra [BinTree] Int
    agt0 = %search

    agt1 : AllAlgebra [List] Int
    agt1 = %search


    -- public export
    -- {shape : List Cont} ->
    -- Algebra (CTensor shape) a => Algebra (CTensor shape) (CTensor [] a) where
    --   reduce t = embed $ reduce $ extract <$> t




  namespace FoldableInstance
    public export
    data AllFoldable : (shape : List Cont) -> Type where
        Nil : AllFoldable []
        Cons : Foldable (Ext c) =>
          AllFoldable cs =>
          AllFoldable (c :: cs)

    public export
    tensorFoldr : (allFoldable : AllFoldable shape) =>
      (a -> acc -> acc) -> acc -> CTensor shape a -> acc
    tensorFoldr {allFoldable = []} f val t = f (extract t) val
    tensorFoldr {allFoldable = Cons} f val t = foldr
      (\ct, acc => tensorFoldr f acc ct) val (extractTopExt t)

    public export
    {shape : List Cont} -> (allFoldable : AllFoldable shape) =>
    Foldable (CTensor shape) where
      foldr = tensorFoldr

    concreteWorks : Tensor [7, 2] Integer -> Integer
    concreteWorks t = foldr (+) 0 t

    parametricCTensorWorks : {shape : List Cont} -> AllFoldable shape =>
      CTensor shape Integer -> Integer
    parametricCTensorWorks t = foldr (+) 0 t

    -- parametricDoesNotWork : {shape : List Nat} ->
    --   Tensor shape Integer -> Integer
    -- parametricDoesNotWork t = foldr (+) 0 t

  namespace TraversableInstance
    public export
    data AllTraversable : (shape : List Cont) -> Type where
        Nil : AllTraversable []
        Cons : Traversable (Ext c) =>
          AllTraversable cs =>
          AllTraversable (c :: cs)

    public export
    tensorTraverse : (allTraversable : AllTraversable shape) =>
      Applicative f =>
      (a -> f b) -> CTensor shape a -> f (CTensor shape b)
    tensorTraverse {allTraversable = []} f t = pure <$> f (extract t)
    tensorTraverse {allTraversable = Cons} f t = embedTopExt <$>
      traverse (\ct => tensorTraverse f ct) (extractTopExt t)

    public export
    {shape : List Cont} ->
    (allTraversable : AllTraversable shape) =>
    (allFoldable : AllFoldable shape) =>
    Traversable (CTensor shape) where
      traverse = tensorTraverse


  namespace NaperianInstance
    public export
    data AllNaperian : (shape : List Cont) -> Type where
      Nil : AllNaperian []
      Cons : (nap : Naperian (Ext c)) =>
        (rest : AllNaperian cs) =>
        AllNaperian (c :: cs)

    namespace Index
      ||| Datatype for indexing into a tensor
      public export
      data IndexNaperian : (shape : List Cont) ->
        (allNap : AllNaperian shape) =>
        Type where
        Nil : IndexNaperian []
        (::) : (nap : Naperian (Ext c)) =>
          (rest : AllNaperian cs) =>
          Log {f=(Ext c)} ->
          IndexNaperian cs {allNap=rest} ->
          IndexNaperian (c :: cs) {allNap=Cons {rest=rest}}

    public export
    tensorLookup : {shape : List Cont} ->
      (allNaperian : AllNaperian shape) =>
      CTensor shape a ->
      (IndexNaperian shape -> a)
    tensorLookup {shape = []} t _ = extract t
    tensorLookup {shape = (c :: cs)} {allNaperian = Cons} t (i :: is)
      = tensorLookup (lookup (extractTopExt t) i) is

    public export
    tensorTabulate : {shape : List Cont} -> (allNaperian : AllNaperian shape) =>
      (IndexNaperian shape -> a) -> CTensor shape a
    tensorTabulate {shape = []} {allNaperian = []} f = embed (f Nil)
    tensorTabulate {shape = (_ :: _)} {allNaperian = Cons} f
      = embedTopExt $ tabulate $ \i => tensorTabulate $ \is => f (i :: is)

    public export
    {shape : List Cont} ->
    (allAppl : All TensorMonoid shape) => (allNaperian : AllNaperian shape) =>
    Naperian (CTensor shape) where
      Log = IndexNaperian shape
      lookup = tensorLookup
      tabulate = tensorTabulate

    -- ||| Should already have the Applicative instance for any Tensor
    -- public export
    -- [flat] {shape : List Nat} -> Applicative (Tensor shape) => Naperian (Tensor shape) where
    --   Log = ?ee
    --   lookup = ?eee
    --   tabulate = ?eeee

    public export
    transposeMatrix : {i, j : Cont} ->
      (allNaperian : AllNaperian [i, j]) =>
      CTensor [i, j] a -> CTensor [j, i] a
    transposeMatrix {allNaperian=Cons @{f} @{Cons}}
      = fromExtensionComposition
      . transpose
      . toExtensionComposition


    tm : Tensor [2, 3] a -> Tensor [3, 2] a
    tm t = transposeMatrix t

    tmp : {i, j : Nat} -> Tensor [i, j] a -> Tensor [j, i] a
    tmp t = transposeMatrix t

    ttm : {i, j : Cont} -> AllNaperian [i, j] => CTensor [i, j] a -> CTensor [j, i] a
    ttm t = transposeMatrix t

    ||| Like 'positions' from Naperian, but parametric, and not requiring the
    ||| Naperian instance here
    public export
    positions : {c : Cont} ->
      {sh : c.Shp} -> CTensor [c] (c.Pos sh)
    positions = extToVector positionsCont

  namespace ShowInstance
    ||| TODO include LayoutOrder as argument, or maybe that should be in Display
    public export
    data AllShow : List Cont -> Type -> Type where
      Nil : Show a => AllShow [] a
      -- for type below, we should be able to define what shExt is without referencing CTensor cs a?
      Cons : Show (c `fullOf` CTensor cs a) =>
       AllShow (c :: cs) a

    public export
    show' : {shape : List Cont} -> (allShow : AllShow shape a) =>
      CTensor shape a -> String
    show' {allShow = Nil} t = show (extract t)
    show' {allShow = Cons} t = show (extractTopExt t)

    public export
    {shape : List Cont} -> (allShow : AllShow shape a) =>
    Show (CTensor shape a) where
        show t = show' {allShow = allShow} t

    %hint
    public export
    allShowCubical : {shape : List Nat} -> Show a => AllShow (Vect <$> shape) a
    allShowCubical {shape=[]} = Nil
    allShowCubical {shape=(c :: cs)} = Cons @{?oibim}

    public export
    {shape : List Nat} -> Show a => Show (Tensor shape a) where
      show t = show' {allShow=allShowCubical} t
      -- show {shape=(c :: cs)} t = show' {allShow = Cons @{?oiim}} t

    -- showCubical : {shape : List Nat} -> Show a => Tensor shape a -> String
    -- showCubical {shape=[]} t = show' {allShow = Nil} t
    -- showCubical {shape=(c :: cs)} t = show' {allShow = Cons @{?oiim}} t


    sst : {shape : List Cont} -> AllShow shape a => CTensor shape a -> String
    sst t = show t

    -- sstc : {shape : List Nat} -> Show a => Tensor shape a -> String
    -- sstc t = show t

  namespace TensorContractions
    -- reduce : {c : Cont} -> Algebra (Ext c) a =>
    --   Ext c a -> Ext Scalar a
    -- reduce x = () <| \() => reduce x
    
    -- public export
    -- dotWith : {cont : Cont} -> TensorMonoid cont => Algebra (Ext cont) c =>
    --   (a -> b -> c) ->
    --   Ext cont a -> Ext cont b -> Ext Scalar c
    -- dotWith f ea eb
    --   = reduce $ extMap tensorM $ (uncurry f <$> pairExtensions ea eb)

    public export
    dotWith : {shape : List Cont} ->
      Algebra (CTensor shape) c => All TensorMonoid shape =>
      (a -> b -> c) ->
      CTensor shape a -> CTensor shape b -> CTensor [] c
    dotWith f xs ys = embed $ reduce $ uncurry f <$> liftA2Tensor xs ys

    public export
    dot : {shape : List Cont} -> Num a =>
      Algebra (CTensor shape) a => All TensorMonoid shape =>
      CTensor shape a -> CTensor shape a -> CTensor [] a
    dot xs ys = dotWith (*) xs ys

    public export
    outerWith : {i, j : Cont} ->
      (TensorMonoid i) =>
      (TensorMonoid j) =>
      (a -> b -> c) ->
      CTensor [i] a -> CTensor [j] b -> CTensor [i, j] c
    outerWith f t t' =
      let tt = (\(t, a) => strength a t) <$> strength t' t
      in uncurry f <$> fromNestedTensor tt

    public export
    outer : {i, j : Cont} -> Num a =>
      (TensorMonoid i) =>
      (TensorMonoid j) =>
      CTensor [i] a -> CTensor [j] a -> CTensor [i, j] a
    outer = outerWith (*)

    public export
    matrixVectorProduct : Num a => {f, g : Cont} -> TensorMonoid g =>
      AllAlgebra [g] a =>
      CTensor [f, g] a -> CTensor [g] a -> CTensor [f] a
    matrixVectorProduct m v = fromNestedTensor $
      dot v <$> toNestedTensor m


    public export
    vectorMatrixProduct : Num a => {f, g : Cont} ->
      (TensorMonoid f) =>
      Algebra (Ext f) (CTensor [g] a) =>
      CTensor [f] a -> CTensor [f, g] a -> CTensor [g] a
    vectorMatrixProduct v m =
      let em : Ext f (CTensor [g] a) := extractTopExt m
          ev : Ext f (CTensor [] a) := extractTopExt v
      in reduce $ (\(x, gx) => ((extract x) *) <$> gx) <$> liftA2 ev em
      --let t : CTensor [f] (CTensor [g] a) := toNestedTensor m
      --in extract $ dotWith (\x, gx => (x *) <$> gx) v t

    public export
    matMul : Num a => {f, g, h : Cont} -> TensorMonoid g =>
      Algebra (Ext g) (CTensor [h] a) =>
      CTensor [f, g] a -> CTensor [g, h] a -> CTensor [f, h] a
    matMul m1 m2 = fromNestedTensor $
      toNestedTensor m1 <&> (\row => vectorMatrixProduct row m2)

    -- "ij,kj->ki"
    public export
    matrixMatrixProduct : {f, g, h : Cont} -> Num a =>
      TensorMonoid g =>
      AllAlgebra [g] a =>
      CTensor [f, g] a -> CTensor [h, g] a -> CTensor [h, f] a
    matrixMatrixProduct m1 m2 = fromNestedTensor $
      matrixVectorProduct m1 <$> toNestedTensor m2

tt0 : CTensor [] Integer
tt0 = pure 13

fg : CTensor [Vect 7] Integer
fg = pure 5

fgh : CTensor [Vect 7, Vect 7] Integer
fgh = pure 13

sht0 : String
sht0 = show tt0

fsh0 : Show (Vect 8 `fullOf` (CTensor [] Integer))
fsh0 = %search

fsh : String
fsh = show fg

fshh : String
fshh = show fgh

ll : List' Integer
ll = fromConcreteTy [1,2,3,4,5]

bt : BinTree' Integer
bt = fromConcreteTy $ Node 1 (Node 2 (Leaf 3) (Leaf 4)) (Leaf 5)

rt : RoseTree' Char
rt = fromConcreteTy (Node 'c' [Leaf 'c', Leaf 'd'])


namespace Reshape
  ||| A wrapper around `extMap`
  ||| Allows us to define views, traversals and general reshaping
  public export
  restructure : {cs, ds : List Cont} ->
    Cont.Tensor cs =%> Cont.Tensor ds ->
    CTensor cs a -> CTensor ds a
  restructure f = MkT . extMap f . GetT

  ||| Reshape is `restructure` for cubical tensors that leaves number of 
  ||| elements unchanged.  This is currently by
  ||| 1) flattening out the entire tensor into a vector
  ||| 2) recast the type to be of the right shape
  ||| 3) unflatten the vector into the right shape
  ||| Importantly, the content of tensors is never touched, only the shape is
  ||| manipulated
  public export
  reshape : {oldShape, newShape : List Nat} ->
    CTensor (Vect <$> oldShape) a ->
    {auto prf : prod oldShape = prod newShape} ->
    CTensor (Vect <$> newShape) a
  reshape t = restructure (reshape DefaultLayoutOrder) t

  -- treeExample1 : CTensor [BinTree] Double
  -- treeExample1 = fromConcreteTy $ Node 60 (Node 7 (Leaf (-42)) (Leaf 46)) (Leaf 2)

  ||| Performs an in-order traversal of a binary tree tensor into a list tensor
  traversalExample : CTensor [BinTree] Double -> CTensor [List] Double
  traversalExample = restructure (wrapIntoVector inorder)

  -- ||| Down the line, we'll also want to adjust how we perform this 
  -- ||| transformation depending on the device we perform the computation on.




tEx : Tensor [2, 3] Integer
tEx = ># [ [1,2,3]
         , [4,5,6] ]

Ex2 : Tensor [6] Integer
Ex2 = reshape {oldShape=[2,3]} {newShape=[6]} tEx

-- Tl : List Nat
-- Tl = [6]
-- 
-- tx : foldr {t=List} (*) 1 ?oldShape = foldr (*) 1 Tl
-- tx = ?tx_rhs

-- data MyT : Nat -> Type where
--   MkMyT : {n : Nat} -> 

data MyCType : Type -> Type where
  MkMyCType : MyCType t

MyType : Nat -> Type
MyType n = MyCType (Vect n Char)


opNat : Nat -> Nat
opNat n = n * n

||| Can recast one type to another if their square is the same.
||| In other words, if they are the same up to negation
resh : {n, m : Nat} ->
  (0 x : MyType n) ->
  {auto prf : opNat n = opNat m} ->
  MyType y
resh _ = MkMyCType

mt : MyType 4
mt = MkMyCType

-- mtex : MyType (-3)
-- mtex = resh mt






namespace SetterGetter
  ||| Machinery for indexing into a CTensor
  ||| It depends on shape, but also on the tensor t itself
  ||| Provides a compile-time guarantee that we won't be out of bounds
  ||| This dependency is not needed for cubical tensors
  public export
  data Index : (shape : List Cont) -> (t : CTensor shape dtype) -> Type where
    Nil : {val : dtype} -> Index [] (embed val)
    (::) : {t : CTensor (c :: cs) dtype} ->
      (p : c.Pos (shapeExt (extractTopExt t))) ->
      Index cs (index (extractTopExt t) p) ->
      Index (c :: cs) t

  %name Index is, js

  public export
  index : {shape : List Cont} ->
    (t : CTensor shape a) -> Index shape t -> a
  index {shape = []} (embed val) [] = val
  index {shape = (c :: cs)} t (i :: is) =
    index (index (extractTopExt t) i) is

  public export infixr 9 @@
  public export
  (@@) : {shape : List Cont} ->
    (t : CTensor shape a) -> Index shape t -> a
  (@@) = index

  public export
  set : {shape : List Cont} ->
    (t : CTensor shape a) ->
    (iop : InterfaceOnPositions (Tensor shape) Eq) =>
    Index shape t -> a -> CTensor shape a
  set {shape = []} t is val = MkT $ set (GetT t) () val
  set {shape = (c :: cs)} t (i :: is) val =
    let ts = index (extractTopExt t) i
        -- tg = set ts is val
    in ?set_rhs_1
  -- maybe InterfaceOnPositions needs a 'AllInterfaceOnPositions' counterpart?

  -- setC t [] x = MkT $ set (GetT t) () x
  -- setC {shape=(s::ss)} t (i :: is) x =
  --   let tNested : Tensor [s] (Tensor ss a) := toNestedTensor t
  --       ts : Tensor ss a := setC (indexC tNested [i]) is x
  --   in fromNestedTensor $ MkT $ set (GetT tNested) (i ** ()) ts

  public export
  t00 : CTensor [Maybe, List] Integer
  t00 = ># Just [10, 20, 30, 40, 50, 60, 70]

  public export
  t11 : Tensor [2, 3] Integer
  t11 = ># [[1,2,3], [4,5,6]]

  public export
  t22 : CTensor [BinTree, List] Integer
  t22 = ># Node [1,2] (Leaf [3,4]) (Leaf [5,6])

  t33 : CTensor [BinTree] Integer
  t33 = ># Node 1 (Leaf 2) (Leaf 3)

  t333 : CTensor [Vect 2] Integer
  t333 = ># [1, 2]

  t44 : CTensor [] Integer
  t44 = ># 13

  public export
  jj : Integer
  jj = index t11 [1, 1]

namespace CubicalSetterGetter
  public export
  data IndexC : List Nat -> Type where
    Nil : IndexC []
    (::) : Fin n -> IndexC ns -> IndexC (n :: ns)

  public export
  indexC : {shape : List Nat} -> Tensor shape a -> IndexC shape -> a
  indexC t [] = index (GetT t) ()
  indexC t (i :: is) = indexC (index (GetT $ toNestedTensor t) (i ** ())) is

  public export
  setC : {shape : List Nat} ->
    Tensor shape a -> IndexC shape -> a -> Tensor shape a
  setC t [] x = MkT $ set (GetT t) () x
  setC {shape=(s::ss)} t (i :: is) x =
    let tNested : Tensor [s] (Tensor ss a) := toNestedTensor t
        ts : Tensor ss a := setC (indexC tNested [i]) is x
    in fromNestedTensor $ MkT $ set (GetT tNested) (i ** ()) ts

-- sTest : Tensor [2, 3] Integer
-- sTest = setC t11 [1, 1] 100

||| Functionality for slicing tensors
namespace Slice
  namespace CubicalSlicing
    ||| Machinery for slicing cubical tensors
    ||| Crucially, different from the indexing one in the definition of (::)
    ||| Here we have Fin (S m) instead of Fin m
    public export
    data Slice : (shape : List Nat) -> Type where
      Nil : Slice []
      (::) : Fin (S m) -> Slice ms -> Slice (m :: ms)

  public export
  sliceToShape : {shape : List Nat} -> Slice shape -> List Nat
  sliceToShape [] = []
  sliceToShape (s :: ss) = finToNat s :: sliceToShape ss

  public export
  take : {shape : List Nat} ->
    (slice : Slice shape) ->
    Tensor shape a ->
    Tensor (sliceToShape slice) a
  take [] t = t
  take (s :: ss) t = embedTopExt $ take ss <$> take s (extractTopExt t)


  ||| What does it mean to slice a non-cubical tensor?
  ||| CTensor [BinTree, List] a
  namespace NonCubicalSlicing

namespace Concatenate
  ||| Concatenate two tensors along an existing axis, the first one
  ||| TODO extend to allow concatenation along an arbitrary axis
  public export
  concat : {x : Nat} ->
    Tensor (x :: shape) a -> Tensor (y :: shape) a -> Tensor (x + y :: shape) a
  concat t t' = embedTopExt $ extractTopExt t ++ extractTopExt t'
