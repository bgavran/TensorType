module Data.Tensor.Shape.Shape

import public Decidable.Equality
import Data.Vect.Elem
import Data.Vect.Quantifiers

import Data.Container.Base
import Data.Tensor.Shape.Axis
import Misc

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------

~~~~~~~~~~~~~~~
Design choices:
~~~~~~~~~~~~~~~

1) Persistent axis names.

Instead of transient axis names - where the names are bound within a function such as `np.einsum("ij->ji", m)` and erased after the said function is evaluated - axis names are a part of the tensor shape, and persist with the lifetime of the said tensor.

2) Axis declarations persist globally, but are only checked for consistency at call sites.

In a proper tensor programming language we'd prevent declaration of inconsistent/duplicate axis names to begin with.
Here we opt for a more pragmatic approach: checking consistency locally at each call site, rather than at declaration sites. 

3) Duplicate axis names within a tensor are allowed, as long as the names are consistent.

Otherwise it would not be clear how to take the diagonal/trace of a matrix while referring only to the axes: they'd have to have different names.

4) Tensor contractions allow duplicate names both in the input and in the output, again, as long as they're consistent. Names in output which haven't appeared in the input are also allowed.

Duplicate input means zipping/reduction, duplicate output means diagonalisation.
This is different from what standard `einsum` allows: it does not permit duplicate names in the output. It also does not not allow names to appear in output which haven't appeared in the input, because their size wouldn't be known. Becuase for us `Axis` refers to both name and size, this works.

~~~~~~~~~~~~~~~
Design choices:
~~~~~~~~~~~~~~~

Two axes are consistent if they either have different names, or same name and same underlying container. Conversely, they're inconsistent if they're called the same, but refer to the different underlying container.

It is possible to have inconsistent axes bound declared within the same scope.
Consistency is checked only at call sites.

Alternatively if we were building a programming languge we'd check consistency with each declaration. That is, writing something like:
```idris
BatchSize1 : Axis
BatchSize1 = "batchSize" ~> Vect 128

BatchSize2 : Axis
BatchSize2 = "batchSize" ~> Vect 129
```
would throw an error on the line `BatchSize2 = ...` because we're redeclaring "batchSize" which already exists.

------------------------------------------- 

Similar projects/ideas:
* XArray: https://docs.xarray.dev/en/stable/ (persistent axis names)
* Haliax: https://github.com/marin-community/haliax

Useful documentation:
* https://obilaniu6266h16.wordpress.com/2016/02/04/einstein-summation-in-numpy/
* https://nlp.seas.harvard.edu/NamedTensor
* https://einsum.joelburget.com/


-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}


mutual
  ||| Datatype defining the shape of a tensor
  ||| It is a vector of consistently named axes
  public export
  data TensorShape : (rank : Nat) ->Type where
    Nil : TensorShape 0
    (::) : (a : Axis) -> (as : TensorShape k) ->
      (axisConsistent : a `ConsistentWith` as) =>
      TensorShape (S k)

  ||| An axis is named consistently with respect to an existing tensor shape
  ||| if its name does not appear in the shape, or it if it appears and
  ||| references the same container
  public export
  data ConsistentWith : Axis -> TensorShape k -> Type where
    NewAxis : {0 a : Axis} -> {0 as : TensorShape k} ->
      NotElem a.name as ->
      a `ConsistentWith` as
    ExistingAxis : {0 a : Axis} -> {0 as : TensorShape k} ->
      (e : Elem a.name as) ->
      index as a.name = a.cont ->
      a `ConsistentWith` as
 
  ||| A proof that an axis name `a` is found in a tensor shape `as`
  ||| Notably this could have been implemented to check whether the 
  ||| *entire axis* is in vector, and not just the name.
  ||| But since a tensor shape is more akin to a dictionary, keeping this form
  public export
  data Elem : (axisName : AxisName) -> (as : TensorShape rank) -> Type where
    Here : {0 as : TensorShape rank} ->
      a `ConsistentWith` as =>
      axisName = a.name =>
      Elem axisName (a :: as)
    There : {0 a : Axis} -> {0 as : TensorShape rank} ->
      a `ConsistentWith` as =>
      (elem : Elem axisName as) =>
      Elem axisName (a :: as)

  ||| A proof that an axis name `a` is not found in a tensor shape `as`
  public export
  data NotElem : (axisElem : AxisName) -> (as : TensorShape rank) -> Type where
    NotInEmpty : NotElem axisElem []
    NotInNonEmpty : {0 axisElem : AxisName} -> {0 a : Axis} ->
      {0 as : TensorShape rank} ->
      (neq : IsNo (decEq axisElem a.name)) ->
      (notElem : NotElem axisElem as) =>
      (a `ConsistentWith` as) ->
      NotElem axisElem (a :: as)

      
  ||| Indexing into a tensor shape.
  ||| Could be many occurences - recovers the one provided by `isElem`
  public export
  index : (shape : TensorShape rank) ->
    (axisName : AxisName) -> 
    (isElem : Elem axisName shape) =>
    Cont
  index (a :: _) axisName @{Here} = a.cont
  index (_ :: as) axisName @{There} = index as axisName

||| to get rid of believe_me this might need to be put in a mutual block too
public export
rename : (shape : TensorShape rank) ->
  (axisName : AxisName) ->
  (newAxisName : AxisName) ->
  TensorShape rank
rename [] _ _ = []
rename (a :: as) axisName newAxisName
  = (::) (applyWhen (axisName == a.name) (flip rename newAxisName) a) (rename as axisName newAxisName) @{believe_me "consistentAfterRenaming"}

namespace RenameByIndex
  ||| to get rid of believe_me this might need to be put in a mutual block too
  public export
  rename : (shape : TensorShape rank) ->
    (axisIndex : Fin rank) ->
    (newAxisName : AxisName) ->
    TensorShape rank
  rename (a :: as) FZ newAxisName
    = (::) (newAxisName ~> a.cont) as @{believe_me "consistentAfterRenamingByIndex"}
  rename (a :: as) (FS axisIndex) newAxisName
    = (::) a (rename as axisIndex newAxisName) @{believe_me "consistentAfterRenamingByIndex"}

||| These are quantifiers for the axes
||| Sometimes we need to explicitly quantify over something involving a name
namespace Quantifiers
  public export
  data All : (p : Axis -> Type) -> TensorShape k -> Type where
    Nil : All p []
    (::) : {0 a : Axis} -> {0 as : TensorShape k} ->
      p a -> All p as ->
      a `ConsistentWith` as =>
      All p (a :: as)

  public export
  data Any : (p : Axis -> Type) -> TensorShape k -> Type where
    Here : {0 a : Axis} -> {0 as : TensorShape k} ->
      a `ConsistentWith` as =>
      p a -> Any p (a :: as)
    There : {0 a : Axis} -> {0 as : TensorShape k} ->
      a `ConsistentWith` as =>
      Any p as -> Any p (a :: as)
  
  ||| These quantifiers are specifically for underlying containers, not axes
  ||| In theory we should be able to overload, but what do we do with 
  ||| purposefully overloaded instances `IsCubical`, `IsNaperian` whose
  ||| existence will prevent elaboration?
  namespace QuantifierOnContainers
    public export
    data AllC : (p : Cont -> Type) -> TensorShape k -> Type where
      Nil : AllC p []
      (::) : {0 a : Axis} -> {0 as : TensorShape k} ->
        p a.cont -> AllC p as ->
        a `ConsistentWith` as =>
        AllC p (a :: as)

    public export
    data AnyC : (p : Cont -> Type) -> TensorShape k -> Type where
      Here : {0 a : Axis} -> {0 as : TensorShape k} ->
        a `ConsistentWith` as =>
        p a.cont -> AnyC p (a :: as)
      There : {0 a : Axis} -> {0 as : TensorShape k} ->
        a `ConsistentWith` as =>
        AnyC p as -> AnyC p (a :: as)

public export
tensorShapesConsistent : TensorShape k -> TensorShape k' -> Type
tensorShapesConsistent s1 s2 = All (\a => a `ConsistentWith` s2) s1

||| (::) here pattern matches on the proof `axisConsistent` and discards it
public export
toVect : TensorShape k -> Vect k Axis
toVect [] = []
toVect (a :: as) = a :: toVect as

public export
toList : TensorShape k -> List Axis
toList [] = []
toList (a :: as) = a :: toList as

||| Convenience function, turns it also into a list
||| Because `Tensor` from `Data.Container` uses lists with tensors
public export
conts : TensorShape k -> List Cont
conts ts = cont <$> toList ts

||| Renaming the shape preserves the underlying data
public export
renamePreservesConts : (shape : TensorShape rank) ->
  (axisName : AxisName) ->
  (newAxisName : AxisName) ->
  conts (rename shape axisName newAxisName) = conts shape
renamePreservesConts [] _ _ = Refl
renamePreservesConts (a :: as) axisName newAxisName with (axisName == a.name)
  _ | True = cong (a.cont ::) (renamePreservesConts as axisName newAxisName)
  _ | False = cong (a.cont ::) (renamePreservesConts as axisName newAxisName)

namespace RenameByIndex
  ||| Renaming a shape at a specific index preserves the underlying containers.
  public export
  renamePreservesConts : (shape : TensorShape rank) ->
    (axisIndex : Fin rank) ->
    (newAxisName : AxisName) ->
    conts (rename shape axisIndex newAxisName) = conts shape
  renamePreservesConts (a :: as) FZ newAxisName = Refl
  renamePreservesConts (a :: as) (FS axisIndex) newAxisName
    = cong (a.cont ::) (renamePreservesConts as axisIndex newAxisName)

||| Names of the axes in a tensor shape
public export
axisNames : TensorShape k -> Vect k AxisName
axisNames ts = name <$> toVect ts

||| Sizes of the axes in a tensor shape
public export
axisSizes : TensorShape k -> Vect k Cont
axisSizes ts = cont <$> toVect ts

||| Size of a tensor shape, i.e. its number of elements
public export
size : (shape : TensorShape k) -> All IsCubical (conts shape) => Nat
size shape = size (conts shape)

||| Cubicality evidence for a tensor shape, using `Either` so that
||| auto-search tries `Left prf` (positive evidence) before `Right ()`
||| (fallback). Standard `Maybe` can't be used because `Nothing` is
||| listed first in its definition and auto-search would always pick it.
public export
0 TensorCubEvidence : TensorShape k -> Type
TensorCubEvidence shape = Either (All IsCubical shape) ()
      




namespace Unique
  ||| A proof that an axis name only appears once in the tensor shape
  public export
  data UniqueElem : AxisName -> TensorShape rank -> Type where
    Here : {0 as : TensorShape rank} ->
      axisName = ax.name =>
      NotElem axisName as =>
      ax `ConsistentWith` as =>
      UniqueElem axisName (ax :: as)
    There : {0 ax : Axis} -> {0 as : TensorShape rank} ->
      IsSucc rank =>
      (uniqueElem : UniqueElem axisName as) =>
      (neq : IsNo (decEq axisName ax.name)) =>
      ax `ConsistentWith` as =>
      UniqueElem axisName (ax :: as)

  ||| Forgets that the axis name only appears once in the tensor shape
  public export
  forgetUnique : {as : TensorShape rank} ->
    UniqueElem axisName as ->
    Elem axisName as
  forgetUnique {as = (a :: as)} Here = Here 
  forgetUnique {as = (a :: as)} (There {uniqueElem=elem})
    = There {elem=forgetUnique elem}

  public export
  index : (shape : TensorShape rank) ->
    (axisName : AxisName) ->
    (uniqueElem : UniqueElem axisName shape) =>
    Cont
  index (a :: _) axisName @{Here} = a.cont
  index (_ :: as) axisName @{There} = index as axisName

  mutual
    public export
    removeAxis : {rank : Nat} ->
      (toRemove : AxisName) ->
      (shape : TensorShape (S rank)) ->
      (is : UniqueElem toRemove shape) =>
      TensorShape rank
    removeAxis toRemove (_ :: as) @{Here} = as
    removeAxis toRemove (a :: as) @{There @{ItIsSucc}}
      = let cProof = consistentAfterRemoving a as toRemove
        in a :: removeAxis toRemove as

    public export
    consistentAfterRemoving : {rank : Nat} ->
      (a : Axis) -> (as : TensorShape (S rank)) ->
      a `ConsistentWith` as =>
      (toRemove : AxisName) ->
      (uElem : UniqueElem toRemove as) =>
      a `ConsistentWith` (removeAxis toRemove as)
    consistentAfterRemoving = believe_me "consistentAfterRemoving" 
    
notElemExample1 : NotElem "i" ["g" ~> List, "j" ~> BinTree]
notElemExample1 = %search

tensorShapeTest1 : TensorShape 2
tensorShapeTest1 = ["batchSize" ~> Vect 128, "seqLen" ~> List]

tensorShapeTest2 : TensorShape 3
tensorShapeTest2
  = ["batchSize" ~> Vect 128, "seqLen" ~> List, "batchSize" ~> Vect 128]

failing
  tensorShapeTest3 : TensorShape 2
  tensorShapeTest3 = ["batchSize" ~> Vect 128, "batchSize" ~> Vect 13]

uniqueElemExample1 : UniqueElem "j" ["i" ~> List, "j" ~> BinTree, "i" ~> List]
uniqueElemExample1 = %search

failing
  uniqueElemExampleFail : UniqueElem "x" ["i" ~> List, "j" ~> BinTree]
  uniqueElemExampleFail = %search

  uniqueElemExampleFail2 : UniqueElem "i" [ "i" ~> List
                                          , "j" ~> BinTree
                                          , "i" ~> List]
  uniqueElemExampleFail2 = %search

public export
TensorTest1 : TensorShape 3
TensorTest1 = ["batchSize" ~> Vect 128, "seqLen" ~> List, "feat" ~> Vect 64]

-- Here proof search does not work (via keycommand), but `%search` does
public export
TensorTest2 : (i : Axis) -> ConsistentWith i [i]
TensorTest2 i = %search

failing
  TensorElemTest2 : Elem "asdf" TensorTest1
  TensorElemTest2 = %search

{-
public export
countOccurence : AxisName -> TensorShape rank -> Nat
countOccurence str [] = 0
countOccurence str (a :: as) = case str == a.name of 
  True => 1 + countOccurence str as
  False => countOccurence str as

public export
countAfterRemoving : AxisName -> TensorShape rank -> Nat
countAfterRemoving str [] = 0
countAfterRemoving str (a :: as) with (decEq str a.name)
  _ | (Yes _) = countAfterRemoving str as
  _ | (No _) = 1 + countAfterRemoving str as

public export
countLessThanRank : (axisN : AxisName) ->
  (shape : TensorShape rank) ->
  LTE (countOccurence axisN shape) rank
countLessThanRank axisN [] = LTEZero
countLessThanRank axisN ((name ~> _) :: as) with (axisN == name)
  _ | True = LTESucc (countLessThanRank axisN as)
  _ | False = lteSuccRight (countLessThanRank axisN as)

-- mutual
--   public export
--   removeAxis : (toRemove : AxisName) ->
--     (shape : TensorShape rank) ->
--     TensorShape (countAfterRemoving toRemove shape)
--   removeAxis toRemove [] = []
--   removeAxis toRemove (a :: as) with (decEq toRemove a.name)
--     _ | (Yes prf) = removeAxis toRemove as
--     _ | (No contra) = let cProof = consistentAfterRemoving a as toRemove
--                       in a :: removeAxis toRemove as
--     
--   ||| Proof that, if `a` is consistent with the shape `as`, then removing any
--   ||| axis from `ss` will still keep `s` consistent with the result
--   public export
--   consistentAfterRemoving : (a : Axis) -> (as : TensorShape rank) ->
--     a `ConsistentWith` as =>
--     (toRemove : AxisName) ->
--     a `ConsistentWith` (removeAxis toRemove as)
--   consistentAfterRemoving _ [] _ = NewAxis NotInEmpty
--   consistentAfterRemoving a (ax :: as) @{(NewAxis (NotInNonEmpty neq axisConsistent))} toRemove = ?eifhh_2
--   consistentAfterRemoving a (ax :: as) @{(ExistingAxis e prf)} toRemove = ?eifhh_1
-}




{-
||| Proof that an axis name appears in a tensor shape
||| The proof indirectly carries data of the first index of the occurence
public export
data InShape : AxisName -> TensorShape rank -> Type where
  Here : {as : TensorShape rank} ->
    (axisName ~> c) `ConsistentWith` as => -- todo add maybe inshape?
    -- isno?
    -- implement Elem and NotElem, and use them here?
    InShape axisName ((axisName ~> c) :: as)
  There : {as : TensorShape rank} -> (is : InShape axisName as) =>
    a `ConsistentWith` as =>
    InShape axisName (a :: as)

-- ||| TODO rethink this function?
-- ||| In a tensor shape removes all but the first occurence of an axis
-- ||| removeDuplicates ["x" ~> 1, "y" ~> 3, "x" ~> 1] "x" = ["x" ~> 1, "y" ~> 1]
-- public export
-- removeDuplicates : {n, rank : Nat} -> LTE n rank =>
--   (shape : TensorShape rank) ->
--   (axisName : AxisName) ->
--   (inShape : InShape axisName shape n) =>
--   IsSucc n =>
--   (m : Nat ** TensorShape m)
-- removeDuplicates shape axisName {inShape} {n = 1}
--   = (rank ** shape)
-- removeDuplicates ((_ ~> a) :: as) axisName {inShape = Here @{is}} {n = (S (S k))}
--   = removeDuplicates as axisName {inShape=is}
-- removeDuplicates (s :: as) axisName {inShape = There @{is}} {n = (S (S k))}
--   = let (m ** as') = removeDuplicates as axisName {inShape=is}
--     in (S m ** (::) {axisConsistent=(believe_me ())} s as')

-- Does tensor contraction allow duplicate axis names
--   * in the input (yes, this is what Einsum also allows)
--   * in the output (no, because otherwise its not clear what should happen)
--     * this means that we can't write `einsum("i,i->ii")`
-- 3) How does contraction work?
--   3.1) Given `t : Tensor [BatchSize, BatchSize] Double`, what is `dotGeneral t`?
-- 
-- Need to figure out how `reduce name t` acts when:
-- 1) `name="BatchSize"` and `t : Tensor [BatchSize, BatchSize] Double`
--   - Should sum up the diagonal?
-- 2) `name="BatchSize"` and `t : Tensor [BatchSize] Double`
--   - Should sum up the vector?
-- 3) `name="BatchSize"` and `t : Tensor [BatchSize, SeqLen, BatchSize] Double`
--   - Should sum up the diagonal slices of SeqLen
-- 
-- I suppose this is about iterators
-- iterating through 


  -- ||| If an axis `i` can be added into a singleton list `[j]`, then
  -- ||| the axis `j` can be added into a singleton list `[i]`
  -- public export
  -- axisConsistentSym : {i, j : Axis} ->
  --   ConsistentWith i [j] -> ConsistentWith j [i]
  -- axisConsistentSym (NewAxis ne) = NewAxis (notElemSym ne)
  -- -- For some reason we can't pattern match on `Here`? The proof should still 
  -- -- be fine... 
  -- axisConsistentSym (ExistingAxis (There Here) _) impossible
  -- axisConsistentSym (ExistingAxis (There (There later)) _) impossible



--  public export
--  data InShape : AxisName -> TensorShape rank -> (n : Nat) ->
--    (ltee : LTE n rank) => Type where
--    Here : {0 n, rank : Nat} -> (lte : LTE n rank) =>
--      {as : TensorShape rank} -> InShape axisName as n =>
--      (axisName ~> c) `ConsistentWith` as =>
--      InShape {rank=S rank} axisName ((axisName ~> c) :: as) (S n) @{LTESucc lte}
--    There : {0 n, rank : Nat} -> (lte : LTE n rank) =>
--      {as : TensorShape rank} -> (is : InShape axisName as n) =>
--      a `ConsistentWith` as =>
--      InShape {rank=S rank} axisName (a :: as) n @{lteSuccRight lte}
--
--
--  tensorShapeTest11 : TensorShape 2
--  tensorShapeTest11 = ["batchSize" ~> Vect 128, "seqLen" ~> List]
--
--  -- ttt : (n : Nat ** InShape "batchSize" tensorShapeTest11 n @{LTEZero})
--
--  mutual
--    public export
--    removeAxis : {n, rank : Nat} -> (lte : LTE n rank) =>
--      (shape : TensorShape rank) ->
--      (toRemove : AxisName) ->
--      (inShape : InShape {rank=rank} toRemove shape n @{lte}) =>
--      TensorShape (rank `minus` n)
--    removeAxis {rank = 0} shape _ = shape
--    removeAxis {n=S _, rank = S _} ((toRemove ~> c) :: as) toRemove {inShape=Here @{lte} @{is}}
--      = removeAxis as toRemove
--    removeAxis {rank = (S rank')} (a :: as) toRemove {inShape=There @{lte} @{is}}
--      = rewrite minusSuccLTE lte in
--        (let consistencyProof = consistentAfterRemoving a as toRemove {is=is}
--         in a :: removeAxis as toRemove)