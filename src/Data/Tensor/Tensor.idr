module Data.Tensor.Tensor

import Data.Fin
import Data.Nat
import Data.Vect
import Data.Vect.Quantifiers
import Data.Vect.Elem
import Data.DPair
import public Decidable.Equality
import public Data.Fin.Split
import Data.HashMap

import public Data.Container
import public Data.Container.Object.Instances as Cont

import public Data.Layout
import public Misc
import public Data.Unique.Vect

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

-- todo do a pass where you add zeros/make things implicit
-- clean up the various 'drop' functions

data NewElemConsistent : String -> Cont -> Vect n String -> Vect n Cont -> Type where
  ||| Adding a binding `s->c` not already in `AllConsistent ss cs`
  NewElem : NotElem s ss ->
    NewElemConsistent s c ss cs
  ||| Adding a binding `s->c` already in `AllConsistent ss cs`
  ExistingElem : (e : Elem s ss) ->
    index (elemToFin e) cs = c ->
    NewElemConsistent s c ss cs


||| Type-level predicate: For all pairs of positions where names match,
||| the corresponding containers must be equal
public export
data AllConsistent : Vect n String -> Vect n Cont -> Type where
  Nil : AllConsistent [] []
  (::) : NewElemConsistent s c ss cs ->
    AllConsistent ss cs ->
    AllConsistent (s :: ss) (c :: cs)

||| Container Tensor: a tensor whose shape is a list of containers
||| This is merely a wrapper around `Ext (Tensor shape) a` to help type
||| inference
public export
record CTensor
  (shape : Vect n Cont)
  (names : Vect n String)
  {auto 0 ac : AllConsistent names shape}
  (a : Type) where
  constructor MkT
  GetT : Ext (Cont.Tensor (toList' shape)) a

%name CTensor t, t', t''

||| Cubical tensors. Used name 'Tensor' for backwards compatibility with
||| terminology in the numpy/pytorch ecosystem
public export
Tensor : (shape : Vect n Nat) ->
  (names : Vect n String) ->
  AllConsistent names (Vect <$> shape) =>
  Type -> Type
Tensor shape names = CTensor (Vect <$> shape) names

testBinding0 : Tensor [] [] Double


testBinding1 : Tensor [2] ["i"] Double

testBinding2 : Tensor [2, 3] ["i", "j"] Double

testBinding3 : Tensor [2, 3, 2] ["i", "j", "i"] Double

testBinding4 : Tensor [2, 3, 3, 4] ["i", "j", "j", "k"] Double


failing
  failBinding0 : Tensor [] ["i"] Double
failing
  failBinding1 : Tensor [2] ["i", "j"] Double
failing
  failBinding2 : Tensor [2, 3] ["i", "i"] Double


public export
(ac : AllConsistent names shape) => Functor (CTensor shape names {ac=ac}) where
  map f (MkT t) = MkT $ map f t

namespace NestedTensorUtils
  public export
  extract : CTensor [] [] a -> a
  extract (MkT t) = extract t

  public export
  embed : a -> CTensor [] [] a
  embed a = MkT (toScalar a)

  ||| With the added data of the wrapper around (Ext (Tensor shape) a), this
  ||| effectively states a list version of the following isomorphism
  ||| Ext c . Ext d = Ext (c . d)
  public export
  fromExtensionComposition : {shape : Vect n Cont} ->
    {names : Vect n String} ->
    (ac : AllConsistent names shape) =>
    composeExtensions shape a -> CTensor shape names a
  fromExtensionComposition {shape = []} ce = MkT ce
  fromExtensionComposition {shape = (c :: cs)} {names = (n :: ns)} {ac=(a :: as)} (sh <| contentAt)
    =  MkT $
    let rest = GetT . fromExtensionComposition {names=ns} . contentAt
    in (sh <| shapeExt . rest) <| \(cp ** fsh) => index (rest cp) fsh

  public export
  toExtensionComposition : {shape : Vect n Cont} ->
    {names : Vect n String} ->
    (ac : AllConsistent names shape) =>
    CTensor shape names a -> composeExtensions shape a
  toExtensionComposition {shape = []} (MkT t) = t
  toExtensionComposition {shape = (_ :: _)} {names = (n :: ns)} {ac=(a :: as)} (MkT ((csh <| cpos) <| idx))
    = csh <| \d => toExtensionComposition {names=ns} (MkT (cpos d <| curry idx d))

  ||| For this and the function below, the commented out definition is 'cleaner'
  ||| but it requires non-erased `c` and `cs`
  public export
  extractTopExt : {0 ns : Vect k String} ->
    NewElemConsistent n c ns cs =>
    AllConsistent ns cs =>
    CTensor (c :: cs) (n :: ns) a -> Ext c (CTensor cs ns a)
  extractTopExt (MkT (sh <| ind))
    = shapeExt sh <| \p => MkT $ index sh p <| \p' => ind (p ** p')

  public export
  embedTopExt : {0 ns : Vect k String} ->
    NewElemConsistent n c ns cs =>
    AllConsistent ns cs =>
    Ext c (CTensor cs ns a) -> CTensor (c :: cs) (n :: ns) a
  embedTopExt e =
    let tp = GetT . index e
    in MkT $ (shapeExt e <| shapeExt . tp) <| \(p ** p') => index (tp p) p'

  ||| This is useful because container composition adds non-trivial data to the
  ||| vector type (i.e. `c >@ Scalar` is not equal to `c`)
  public export
  extToVector : Ext c a -> CTensor [c] [n] a
  extToVector e = MkT $ (shapeExt e <| \_ => ()) <| \(cp ** ()) => index e cp

  public export
  vectorToExt : CTensor [c] [n] a -> Ext c a
  vectorToExt (MkT t) = shapeExt (shapeExt t) <| \cp => index t (cp ** ())

  public export
  toNestedTensor : {n : String} -> {ns : Vect k String} ->
    {c : Cont} -> {cs : Vect k Cont} -> 
    NewElemConsistent n c ns cs =>
    AllConsistent ns cs =>
    CTensor (c :: cs) (n :: ns) a -> CTensor [c] [n] (CTensor cs ns a)
  toNestedTensor = extToVector . extractTopExt

  public export
  fromNestedTensor : {n : String} -> {ns : Vect k String} ->
    {c : Cont} -> {cs : Vect k Cont} -> 
    NewElemConsistent n c ns cs =>
    AllConsistent ns cs =>
    CTensor [c] [n] (CTensor cs ns a) -> CTensor (c :: cs) (n :: ns) a
  fromNestedTensor = embedTopExt . vectorToExt 

  public export
  tensorMapFirstAxis :
    {n : String} -> {ns : Vect k String} -> {ms : Vect k' String} ->
    {c : Cont} -> {cs : Vect k Cont} -> {ds : Vect k' Cont} ->
    NewElemConsistent n c ns cs =>
    NewElemConsistent n c ms ds =>
    AllConsistent ns cs =>
    AllConsistent ms ds =>
    (f : CTensor cs ns a -> CTensor ds ms a) ->
    CTensor (c :: cs) (n :: ns) a -> CTensor (c :: ds) (n :: ms) a
  tensorMapFirstAxis f = fromNestedTensor . map f . toNestedTensor

  public export infixr 4 <-$>
  ||| Is meant to look like infix map (i.e. `<$>`) with the added difference
  ||| that we keep the container on the left side untouched, hence the `<-$>`
  public export
  (<-$>) : 
    {n : String} -> {ns : Vect k String} -> {ms : Vect k' String} ->
    {c : Cont} -> {cs : Vect k Cont} -> {ds : Vect k' Cont} ->
    NewElemConsistent n c ns cs =>
    NewElemConsistent n c ms ds =>
    AllConsistent ns cs =>
    AllConsistent ms ds =>
    (f : CTensor cs ns a -> CTensor ds ms a) ->
    CTensor (c :: cs) (n :: ns) a -> CTensor (c :: ds) (n :: ms) a
  (<-$>) = tensorMapFirstAxis

namespace TensorFromConcrete
  public export
  concreteTypeTensor : (shape : Vect rank Cont) ->
    (allConcrete : AllConcrete (toList' shape)) =>
    Type -> Type
  concreteTypeTensor [] {allConcrete = []} = concreteType {cont=Scalar}
  concreteTypeTensor (c :: cs) {allConcrete = Cons @{fc}}
    = (concreteType @{fc}) . (concreteTypeTensor cs)

  public export
  concreteTypeFunctor : {shape : Vect rank Cont} ->
    (allConcrete : AllConcrete (toList' shape)) =>
    Functor (concreteTypeTensor shape)
  concreteTypeFunctor {shape = []} {allConcrete = []}
    = concreteFunctor {cont=Scalar}
  concreteTypeFunctor {shape = (c :: cs)} {allConcrete = Cons @{fc}}
    = Functor.Compose @{concreteFunctor @{fc} } @{concreteTypeFunctor}

  public export
  concreteToExtensions : {shape : Vect rank Cont} ->
    (allConcrete : AllConcrete (toList' shape)) =>
    concreteTypeTensor shape a -> composeExtensions shape a
  concreteToExtensions {shape = []} {allConcrete = []} ct = fromConcreteTy ct
  concreteToExtensions {shape = (_ :: _)} {allConcrete = Cons} ct =
    concreteToExtensions <$> fromConcreteTy ct

  public export
  extensionsToConcreteType : {shape : Vect rank Cont} ->
    (allConcrete : AllConcrete (toList' shape)) =>
    composeExtensions shape a -> concreteTypeTensor shape a
  extensionsToConcreteType {shape = []} {allConcrete = []} ct = toConcreteTy ct
  extensionsToConcreteType {shape = (_ :: _)} {allConcrete = Cons @{fc}} ct
    = (map @{concreteFunctor @{fc}} extensionsToConcreteType) (toConcreteTy ct)

  public export
  toTensor : {shape : Vect rank Cont} ->
    {ns : Vect rank String} ->
    (allConcrete : AllConcrete (toList' shape)) =>
    AllConsistent ns shape =>
    concreteTypeTensor shape a -> CTensor shape ns a
  toTensor = fromExtensionComposition . concreteToExtensions

  public export
  fromTensor : {shape : Vect rank Cont} ->
    {ns : Vect rank String} ->
    (allConcrete : AllConcrete (toList' shape)) =>
    AllConsistent ns shape =>
    CTensor shape ns a -> concreteTypeTensor shape a
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
  fromConcreteTy : {shape : Vect rank Cont} ->
    {ns : Vect rank String} ->
    (allConcrete : AllConcrete (toList' shape)) =>
    AllConsistent ns shape =>
    concreteTypeTensor shape a -> CTensor shape ns a
  fromConcreteTy = toTensor

  public export
  toConcreteTy : {shape : Vect rank Cont} ->
    {ns : Vect rank String} ->
    (allConcrete : AllConcrete (toList' shape)) =>
    AllConsistent ns shape =>
    CTensor shape ns a -> concreteTypeTensor shape a
  toConcreteTy = fromTensor

  public export prefix 0 >#, #>

  ||| Prefix operator for converting from a concrete type to a tensor
  ||| We read it as a map `>` going into the tensor `#`
  public export
  (>#) : {shape : Vect rank Cont} ->
    {ns : Vect rank String} ->
    (allConcrete : AllConcrete (toList' shape)) =>
    AllConsistent ns shape =>
    concreteTypeTensor shape a -> CTensor shape ns a
  (>#) = fromConcreteTy

  ||| Prefix operator for converting from a tensor to concrete type
  ||| We read it as a map `>` going out of the tensor `#`
  public export
  (#>) : {shape : Vect rank Cont} ->
    {ns : Vect rank String} ->
    (allConcrete : AllConcrete (toList' shape)) =>
    AllConsistent ns shape =>
    CTensor shape ns a -> concreteTypeTensor shape a
  (#>) = toConcreteTy

namespace TensorInstances
  namespace ApplicativeInstance
    public export
    tensorReplicate : {shape : Vect rank Cont} ->
      {names : Vect rank String} ->
      (allAppl : All TensorMonoid (toList' shape)) =>
      (ac : AllConsistent names shape) =>
      (x : a) -> CTensor shape names a
    tensorReplicate {shape = []} {names = []} {ac = []} = embed
    tensorReplicate {shape = (_ :: _)} {names = (n :: ns)} {ac = (a :: as)} {allAppl = (::) _ _}
      = fromExtensionComposition
      . pure
      . toExtensionComposition {names=ns}
      . tensorReplicate

    public export
    liftA2Tensor : {shape : Vect rank Cont} ->
      {names : Vect rank String} ->
      (allAppl : All TensorMonoid (toList' shape)) =>
      (ac : AllConsistent names shape) =>
      CTensor shape names a -> CTensor shape names b -> CTensor shape names (a, b)
    liftA2Tensor {shape = []} {names = []} {ac = []} {allAppl=[]} (MkT t) (MkT t') = embed (index t (), index t' ())
    liftA2Tensor {shape = (s :: ss)} {names = (n :: ns)} {ac = (a :: as)} {allAppl = (::) _ _} t t'
      = embedTopExt $ uncurry liftA2Tensor <$>
          liftA2 (extractTopExt t) (extractTopExt t')

    public export
    {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    (allAppl : All TensorMonoid (toList' shape)) =>
    (ac : AllConsistent names shape) =>
    Applicative (CTensor shape names) where
      pure = tensorReplicate
      fs <*> xs = uncurry ($) <$> liftA2Tensor fs xs

  namespace EqInstance
    public export
    data AllEq : (shape : Vect rank Cont) ->
      (names : Vect rank String) ->
      AllConsistent names shape =>
      (a : Type) -> Type where
      Nil : Eq a => AllEq [] [] a
      Cons :  {n : String} -> {ns : Vect k String} -> 
        {c : Cont} -> {cs : Vect k Cont} ->
        (ac : AllConsistent ns cs) =>
        (eq : Eq (c `fullOf` CTensor cs ns a)) => -- hmm, can be simplified? this would cause unification regarding AllConsistent to become much simpler?
        (ne : NewElemConsistent n c ns cs) =>
        AllEq (c :: cs) (n :: ns) a


    public export
    tensorEq : {shape : Vect rank Cont} ->
      {names : Vect rank String} ->
      (ac : AllConsistent names shape) =>
      (allEq : AllEq shape names a) =>
      CTensor shape names a -> CTensor shape names a -> Bool
    tensorEq {ac=[]} {allEq = []} t1 t2 = extract t1 == extract t2
    tensorEq {ac=(a :: as)} {allEq = Cons} t1 t2
      = (extractTopExt t1) == (extractTopExt t2)

    public export
    {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names shape) =>
    (allEq : AllEq shape names a) =>
      Eq (CTensor shape names a) where
        (==) = tensorEq {allEq = allEq}

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
    {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names shape) =>
    Num a => All TensorMonoid (toList' shape) =>
    Num (CTensor shape names a) where
        fromInteger = tensorReplicate . fromInteger
        t + t' = uncurry (+) <$> liftA2Tensor t t'
        t * t' = uncurry (*) <$> liftA2Tensor t t'

    public export
    {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names shape) =>
    Neg a => All TensorMonoid (toList' shape) =>
    Neg (CTensor shape names a) where
      negate = (negate <$>)
      xs - ys = (uncurry (-)) <$> liftA2 xs ys

    -- TODO this throws an error?
    negNotFound : {shape : Vect rank Nat} ->
      AllConsistent names (Vect <$> shape) =>
      Neg a => Neg (Tensor shape names a)
    negNotFound = ?interfaceProblemsAgain

    public export
    {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names shape) =>
    Abs a => All TensorMonoid (toList' shape) =>
    Abs (CTensor shape names a) where
      abs = (abs <$>)

    public export
    {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    AllConsistent names shape =>
    Fractional a => All TensorMonoid (toList' shape) =>
    Fractional (CTensor shape names a) where
      t / v = (uncurry (/)) <$> liftA2 t v

    public export
    {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    AllConsistent names shape =>
    Exp a =>
    All TensorMonoid (toList' shape) =>
    Exp (CTensor shape names a) where
      exp = (exp <$>)
      minusInfinity = pure minusInfinity

  namespace AlgebraInstance
    ||| Unlike all other instantiations of 'AllX', `AllAlgebra` is not
    ||| stating that each container in an list has an algebra, but rather
    ||| 'cumulatively'. For instance, `AllAlgebra [c, d] a` is not defined as
    ||| `Algebra c a` and `Algebra d a`, bur rather as `Algebra c (Algebra d a)`
    ||| and `Algebra d a`.
    public export
    data AllAlgebra : (shape : Vect rank Cont) ->
      (names : Vect rank String) ->
      AllConsistent names shape =>
      (dtype : Type) -> Type where
      Nil : AllAlgebra [] [] a
      Cons : {n : String} -> {ns : Vect k String} ->
        {c : Cont} -> {cs : Vect k Cont} ->
        AllConsistent ns cs =>
        (alg : Algebra (Ext c) (CTensor cs ns a)) =>
        (rest : AllAlgebra cs ns a) =>
        NewElemConsistent n c ns cs =>
        AllAlgebra (c :: cs) (n :: ns) a

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
    reduceTensor : {shape : Vect rank Cont} ->
      {names : Vect rank String} ->
      AllConsistent names shape =>
      (allAlg : AllAlgebra shape names a) =>
      CTensor shape names a -> a
    reduceTensor {allAlg = []} = extract
    reduceTensor {allAlg = Cons} = reduceTensor . reduce . extractTopExt


    public export
    {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    AllConsistent names shape =>
    (allAlg : AllAlgebra shape names a) =>
    Algebra (CTensor shape names) a where
      reduce = reduceTensor

    -- public export
    -- {c : Cont} -> Algebra (Ext c) a =>
    -- Algebra (CTensor [c]) (CTensor [] a) where
    --   reduce t = embed $ reduce $ vectorToExt $ extract <$> t

    ||| Since we have non-unique axis labels, this likely needs to be 
    ||| implemented after `dot`
    namespace ReduceAxis

{-
      public export
      allConsistentAfterDropElems : {rank : Nat} ->
        {shape : Vect (S rank) Cont} ->
        {names : Vect (S rank) String} ->
        AllConsistent names shape =>
        (inAxes : Elem toDelete names) =>
        AllConsistent (DropElem.drop names inAxes)
                      (drop (FS (elemToFin inAxes)) shape)
      allConsistentAfterDropElems = ?todo

      allConsistentAfterDropOneElem : {rank : Nat} ->
        {shape : Vect (S rank) Cont} ->
        {names : Vect (S rank) String} ->
        AllConsistent names shape =>
        {toDelete : String} ->
        (inAxes : Elem toDelete names) =>
        AllConsistent (dropElem names inAxes)
                      (deleteAt (elemToFin inAxes) shape)
      allConsistentAfterDropOneElem = ?todo2
      public export
      reduce : {rank : Nat} ->
        {shape : Vect (S rank) Cont} ->
        {names : Vect (S rank) String} ->
        (ac : AllConsistent names shape) =>
        CTensor shape names a ->
        (toDelete : String) ->
        (inAxes : Elem toDelete names) =>
        (alg : Algebra (Ext (index (elemToFin inAxes) shape))
          (CTensor (drop (FS (elemToFin inAxes)) shape)
                   (DropElem.drop names inAxes)
                   {ac=allConsistentAfterDropElems {toDelete=toDelete} {names=names} {shape=shape}}
                   a)
        ) => -- have to increase `index inAxes` by 1 because we're not indexing, but counting
        CTensor (deleteAt (elemToFin inAxes) shape)
                (dropElem names inAxes)
                {ac=allConsistentAfterDropOneElem {toDelete=toDelete} {names=names} {shape=shape}}
                a
      reduce {ac=aa::ac} t _ {shape = (s :: ss)} {inAxes = Here {xs=ns}} {alg}
        = let algRewr : Ext s (CTensor ss ns a) -> CTensor ss ns a
              algRewr = rewrite sym (minusZeroRight rank) in reduce
          in algRewr (extractTopExt t)
      reduce {rank = (S k)} t toDelete {shape = (s :: ss)} {names = (n :: ns)} {inAxes = There later}
        = let th : Ext s (CTensor (deleteAt (indexOf later) ss) (removeIndex ns (indexOf later)) a) 
              th = (\t' => ReduceAxis.reduce t' toDelete {inAxes=later}) <$> extractTopExt t
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



    rrr : {shape : Vect rank Cont} ->
      {names : UniqueVect rank String} ->
      AllAlgebra shape names a => CTensor shape names a -> a
    rrr t = reduce t

    rrrc : {shape : Vect rank Nat} ->
      {names : UniqueVect rank String} ->
      AllAlgebra (Vect <$> shape) names a => Tensor shape names a -> a
    rrrc t = reduce t

    agtest0 : Algebra BinTreeNode Int
    agtest0 = %search

    zzn : Num (CTensor [] [] Int)
    zzn = %search

    zz : Algebra (Ext BinTree) (CTensor [] [] Int)
    zz = %search

    zz0 : Algebra (CTensor [BinTree] ["o"]) Int
    zz0 = %search

    zzt : Algebra (CTensor [BinTree] ["p"]) (CTensor [] [] Int)
    zzt = %search

    agt0 : AllAlgebra [BinTree] ["o"] Int
    agt0 = %search

    agt1 : AllAlgebra [List] ["x"] Int
    agt1 = %search


    -- public export
    -- {shape : List Cont} ->
    -- Algebra (CTensor shape) a => Algebra (CTensor shape) (CTensor [] a) where
    --   reduce t = embed $ reduce $ extract <$> t

t1 : Tensor [4] ["features"] Double
t1 = reduce t0 "batch"

-}

namespace FoldableInstance
  public export
  data AllFoldable : (shape : Vect rank Cont) -> Type where
      Nil : AllFoldable []
      Cons : Foldable (Ext c) =>
        AllFoldable cs =>
        AllFoldable (c :: cs)

  public export
  tensorFoldr : (allFoldable : AllFoldable shape) =>
    {names : Vect rank String} ->
    (ac : AllConsistent names shape) =>
    (a -> acc -> acc) -> acc -> CTensor shape names a -> acc
  tensorFoldr {names=[]} {ac=[]} {allFoldable = []} f val t = f (extract t) val
  tensorFoldr {names=(n :: ns)} {ac=a::as} {allFoldable = Cons} f val t = foldr
    (\ct, acc => tensorFoldr f acc ct) val (extractTopExt t)

  public export
  {shape : Vect rank Cont} ->
  {names : Vect rank String} ->
  (ac : AllConsistent names shape) =>
  (allFoldable : AllFoldable shape) =>
  Foldable (CTensor shape names) where
    foldr = tensorFoldr

  concreteWorks : Tensor [7, 2] ["a", "b"] Integer -> Integer
  concreteWorks t = foldr (+) 0 t

  parametricCTensorWorks : {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names shape) =>
    AllFoldable shape =>
    CTensor shape names Integer -> Integer
  parametricCTensorWorks t = foldr (+) 0 t

  -- parametricDoesNotWork : {shape : List Nat} ->
  --   Tensor shape Integer -> Integer
  -- parametricDoesNotWork t = foldr (+) 0 t

  namespace TraversableInstance
    public export
    data AllTraversable : (shape : Vect rank Cont) -> Type where
        Nil : AllTraversable []
        Cons : Traversable (Ext c) =>
          AllTraversable cs =>
          AllTraversable (c :: cs)

    public export
    tensorTraverse : (allTraversable : AllTraversable shape) =>
      Applicative f =>
      {names : Vect rank String} ->
      (ac : AllConsistent names shape) =>
      (a -> f b) -> CTensor shape names a -> f (CTensor shape names b)
    tensorTraverse {allTraversable = []} {names = []} {ac=[]} f t = pure <$> f (extract t)
    tensorTraverse {allTraversable = Cons} {names=(n :: ns)} {ac=a::as} f t = embedTopExt <$> 
      traverse (\ct => tensorTraverse f ct) (extractTopExt t)

    public export
    {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names shape) =>
    (allTraversable : AllTraversable shape) =>
    (allFoldable : AllFoldable shape) =>
    Traversable (CTensor shape names) where
      traverse = tensorTraverse

  namespace NaperianInstance
    public export
    data AllNaperian : (shape : Vect rank Cont) -> Type where
      Nil : AllNaperian []
      Cons : (nap : Naperian (Ext c)) =>
        (rest : AllNaperian cs) =>
        AllNaperian (c :: cs)


    namespace Index
      ||| Datatype for indexing into a tensor
      public export
      data IndexNaperian : (shape : Vect rank Cont) ->
        (allNap : AllNaperian shape) =>
        Type where
        Nil : IndexNaperian []
        (::) : (nap : Naperian (Ext c)) =>
          (rest : AllNaperian cs) =>
          Log {f=(Ext c)} ->
          IndexNaperian cs {allNap=rest} ->
          IndexNaperian (c :: cs) {allNap=Cons {rest=rest}}

    public export
    tensorLookup : {shape : Vect rank Cont} ->
      {names : Vect rank String} ->
      (ac : AllConsistent names shape) =>
      (allNaperian : AllNaperian shape) =>
      CTensor shape names a ->
      (IndexNaperian shape -> a)
    tensorLookup {shape = []} {names = []} {ac=[]} t _ = extract t
    tensorLookup {shape = (c :: cs)} {names = (n :: ns)} {ac=a::as} {allNaperian = Cons} t (i :: is)
      = tensorLookup (lookup (extractTopExt t) i) is

    public export
    tensorTabulate : {shape : Vect rank Cont} ->
      {names : Vect rank String} ->
      (ac : AllConsistent names shape) =>
      (allNaperian : AllNaperian shape) =>
      (IndexNaperian shape -> a) -> CTensor shape names a
    tensorTabulate {shape = []} {names = []} {ac=[]} {allNaperian = []} f
      = embed (f Nil)
    tensorTabulate {shape = (_ :: _)} {names = (n :: ns)} {ac=a::as} {allNaperian = Cons} f
      = embedTopExt $ tabulate $ \i => tensorTabulate $ \is => f (i :: is)

    public export
    {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names shape) =>
    (allAppl : All TensorMonoid (toList' shape)) =>
    (allNaperian : AllNaperian shape) =>
    Naperian (CTensor shape names) where
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
      {ni, nj : String} ->
      AllConsistent [ni, nj] [i, j] =>
      AllConsistent [nj, ni] [j, i] => -- should get rid of one of these?
      --Either (IsNo (decEq ni nj)) ((ni = nj), (i = j)) =>
      (allNaperian : AllNaperian [i, j]) =>
      CTensor [i, j] [ni, nj] a -> CTensor [j, i] [nj, ni] a
    transposeMatrix {allNaperian=Cons @{f} @{Cons}}
      = fromExtensionComposition
      . transpose
      . toExtensionComposition

    
    tm : Tensor [2, 3] ["i", "j"] a -> Tensor [3, 2] ["j", "i"] a
    tm t = transposeMatrix t

    tmp : {i, j : Nat} ->
      Tensor [i, j] ["i", "j"] a -> Tensor [j, i] ["j", "i"] a 
    tmp t = transposeMatrix t

    ttm : {i, j : Cont} -> AllNaperian [i, j] =>
      CTensor [i, j] ["i", "j"] a -> CTensor [j, i] ["j", "i"] a
    ttm t = transposeMatrix t

    ||| Like 'positions' from Naperian, but parametric, and not requiring the
    ||| Naperian instance here
    public export
    positions : {c : Cont} ->
      {sh : c.Shp} -> CTensor [c] [n] (c.Pos sh)
    positions = extToVector positionsCont


namespace ShowInstance
  public export
  data AllShow : (shape : Vect rank Cont) ->
    (names : Vect rank String) ->
    AllConsistent names shape =>
    (a :Type) -> Type where
    Nil : Show a => AllShow [] [] a
    -- for type below, we should be able to define what shExt is without referencing CTensor cs a? 
    Cons : {0 n : String} -> {0 ns : Vect k String} ->
      AllConsistent ns cs =>
      Show (c `fullOf` CTensor cs ns a) =>
      NewElemConsistent n c ns cs =>
      AllShow (c :: cs) (n :: ns) a

  public export
  show' : {0 rank : Nat} ->
    {shape : Vect rank Cont} ->
    {0 names : Vect rank String} ->
    AllConsistent names shape =>
    (allShow : AllShow shape names a) =>
    CTensor shape names a -> String
  show' {allShow = Nil} t = show (extract t)
  show' {allShow = Cons @{sh}} t = show (extractTopExt t)

  public export
  {shape : Vect rank Cont} ->
  AllConsistent names shape =>
  (allShow : AllShow shape names a) =>
  Show (CTensor shape names a) where
      show t = show' {allShow = allShow} t

  %hint
  public export
  allShowCubical : {shape : Vect rank Nat} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names (Vect <$> shape)) =>
    Show a =>
    AllShow (Vect <$> shape) names a
  allShowCubical {shape=[]} {names=[]} {ac = []} = Nil
  allShowCubical {shape=(c :: cs)} {names=(n :: ns)} {ac = a::as}
    = ?allShowCubical_rhs -- Cons @{?oibim}

  public export
  {shape : Vect rank Nat} ->
  {names : Vect rank String} ->
  (ac : AllConsistent names (Vect <$> shape)) =>
  Show a =>
  Show (Tensor shape names a) where
    show t = show' {allShow=allShowCubical} t
    -- show {shape=(c :: cs)} t = show' {allShow = Cons @{?oiim}} t

  -- showCubical : {shape : List Nat} -> Show a => Tensor shape a -> String
  -- showCubical {shape=[]} t = show' {allShow = Nil} t
  -- showCubical {shape=(c :: cs)} t = show' {allShow = Cons @{?oiim}} t


  sst : {shape : Vect rank Cont} ->
    AllConsistent names shape =>
    AllShow shape names a => CTensor shape names a -> String
  sst t = show t

  -- sstc : {shape : List Nat} -> Show a => Tensor shape a -> String
  -- sstc t = show t


t0 : Tensor [3, 4] ["batch", "features"] Double
t0 = ># [ [0, 1, 2, 3]
        , [4, 5, 6, 7]
        , [8, 9, 10, 11]]


t1 : Tensor [2, 3, 2] ["i", "j", "i"] Double
t1 = ># [ [[0, 1], [2, 3], [4, 5]]
        , [[6, 7], [8, 9], [10, 11]] ]



namespace TensorContractions
  public export
  dotWith : {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names shape) =>
    Algebra (CTensor shape names) c => All TensorMonoid (toList' shape) =>
    (a -> b -> c) ->
    CTensor shape names a -> CTensor shape names b -> CTensor [] [] c
  dotWith f xs ys = embed $ Algebra.reduce $ uncurry f <$> liftA2Tensor xs ys

  public export
  dot : {shape : Vect rank Cont} ->
    {names : Vect rank String} ->
    (ac : AllConsistent names shape) =>
    Num a =>
    Algebra (CTensor shape names) a => All TensorMonoid (toList' shape) =>
    CTensor shape names a -> CTensor shape names a -> CTensor [] [] a
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

    ||| Combines the labels of two axes
    ||| Given    ["i", "j", "i"]
    ||| and      ["i", "k"]
    ||| produces ["i", "j", "k"] (or should it produce ["j", "i", "k"])
    ||| Using 'reverse' because we're dealing with cons instead of snoc lists
    public export
    combineNames :
      (names1 : Vect n String) ->
      (names2 : Vect m String) ->
      Vect (fst (UniqueVect.fromVect ((reverse names2) ++ (reverse names1)))) String
    combineNames names1 names2 with (UniqueVect.fromVect ((reverse names2) ++ (reverse names1)))
      _ | (_ ** res) = reverse $ toVect res

    ||| Given a list of axes, the names of these axes, and a subset of their 
    ||| names, return the axes corresponding to that subset
    public export
    selectAxes : (shape : Vect rank Cont) ->
      (names : Vect rank String) ->
      AllConsistent names shape =>
      (toSelect : Vect m String) -> -- technically should be UniqueVect
      (al : All (\x => Elem x names) toSelect) =>
      Vect m Cont
    -- selectAxes _ _ [] = []
    -- selectAxes shape names (s :: ss) @{(p :: ps)} 
    --   = (index (indexOf p) shape) :: selectAxes shape names ss @{ps}

    public export
    N1 : Vect 3 String
    N1 = ["i", "j", "i"]

    public export
    N2 : Vect 3 String
    N2 = ["i", "k", "l"]

    ||| Generalised dot product which contracts over shared axes
    ||| For instance, given 
    ||| Given    [2, 3, 2] ["i", "j", "i"]
    ||| and      [2, 4]    ["i", "k"]
    ||| produces [2, 3, 4] ["i", "j", "k"]
    public export
    dot : {shape1 : Vect rank1 Cont} ->
      {shape2 : Vect rank2 Cont} ->
      {names1 : Vect rank1 String} ->
      {names2 : Vect rank2 String} ->
      AllConsistent names1 shape1 => -- t1 is consistently bound
      AllConsistent names2 shape2 => -- t2 to
      AllConsistent (names1 ++ names2) (shape1 ++ shape2) => -- but the result should too
      Num a =>
      CTensor shape1 names1 a -> CTensor shape2 names2 a ->
      CTensor (selectAxes (shape1 ++ shape2) (names1 ++ names2) (combineNames names1 names2))
              (combineNames names1 names2)
              a
    -- dot {rank1 = 0} {shape1 = []} {names1 = []} t t' = (extract t * ) <$> t'
    -- dot {rank1 = (S k)} {shape1 = (s :: ss)} {names1 = (n :: ns)} t t'
    --   with (decElemInUniqueVect n names2)
    --   _ | (Yes prf) = ?dot_rhs_1
    --   _ | (No nprf) = ?dot_rhs_2

    
{-
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

-}
