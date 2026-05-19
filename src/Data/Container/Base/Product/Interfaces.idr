module Data.Container.Base.Product.Interfaces

import public Data.List.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Product.Definitions
import Data.Container.Base.Object.Instances
import Data.Container.Base.Morphism.Instances

||| Its extension is an applicative functor
||| All Naperian containers, BinTree, BinTreeLeaf, List, Maybe,...
public export
interface TensorMonoid (0 c : Cont) where
  tensorN : Scalar =%> c
  tensorM : c >< c =%> c

public export
interface TensorComonoid (0 c : Cont) where
  tensorCounit : c =%> Scalar
  tensorComult : c =%> c >< c

||| Its extension is a monad
||| Just as Applicative => Monad, here TensorMonoid => SeqMonoid
public export
interface TensorMonoid c => SeqMonoid (0 c : Cont) where
  seqM : c >@ c =%> c

||| These are directed containers, a.k.a. categories
||| Does this interface constraint follow analogously?
public export
interface TensorComonoid c => SeqComonoid (0 c : Cont) where
  seqComult : c =%> c >@ c

public export
interface CoprodMonoid (0 c : Cont) where
  plusN : Empty =%> c
  plusM : c >+< c =%> c

||| Its extension is an Alternative?
public export
interface ProdMonoid (0 c : Cont) where
  prodN : UnitCont =%> c
  prodM : c >*< c =%> c

public export
pairExtensions : Ext c a -> Ext d b -> Ext (c >< d) (a, b)
pairExtensions (shapeC <| indexC) (shapeD <| indexD)
  = (shapeC, shapeD) <| \(posC, posD) => (indexC posC, indexD posD)

public export
liftA2Ext : TensorMonoid c => Ext c a -> Ext c b -> Ext c (a, b)
liftA2Ext aExt bExt = extMap tensorM $ pairExtensions aExt bExt

public export
TensorMonoid c => Applicative (Ext c) where
  pure x = tensorN.fwd () <| const x
  fExt <*> aExt = uncurry ($) <$> liftA2Ext fExt aExt

public export
[FromSeq] SeqMonoid c => Applicative (Ext c) where
  pure x = tensorN.fwd () <| const x
  (f <| f') <*> (x <| x') = ?notAThing

public export
SeqMonoid c => Monad (Ext c) using FromSeq where
  join (a <| b) = let (q1 ** q2) = (%! seqM) (a <| shapeExt . b)
                  in q1 <| ((\xx => (b xx.fst).index xx.snd) . q2)

public export
[FromProd] ProdMonoid c => Applicative (Ext c) where
  pure x = prodN.fwd () <| const x
  (<*>) = ?notAThing2

public export
ProdMonoid c => Alternative (Ext c) using FromProd where
  empty = let (p1 ** p2) = (%! prodN) () in p1 <| absurd . p2
  (<|>) (a <| a') (b <| b') =
    let (m1 ** m2) = (%! prodM) (a, b) in m1 <| either a' b' . m2
