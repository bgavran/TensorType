module Data.Container.Base.Product.Interfaces

import public Data.List.Quantifiers

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Object.Instances
import Data.Container.Base.Product.Definitions


public export
interface TensorMonoid (0 c : Cont) where
  tensorN : Scalar =%> c
  tensorM : (c >< c) =%> c

public export
interface SeqMonoid (0 c : Cont) where
  seqN : Scalar =%> c
  seqM : (c >@ c) =%> c

public export
interface CoprodMonoid (0 c : Cont) where
  plusN : Empty =%> c
  plusM : (c >+< c) =%> c

public export
interface ProdMonoid (0 c : Cont) where
  prodN : UnitCont =%> c
  prodM : (c >*< c) =%> c

public export
TensorMonoid c => Applicative (Ext c) where
  pure x = tensorN.fwd () <| const x
  (f <| f') <*> (x <| x') =
    let (q1 ** qq) = (%! tensorM) (f, x)
    in q1 <| (\z => let (p1, p2) = qq z in f' p1 (x' p2))

public export
[FromSeq] SeqMonoid c => Applicative (Ext c) where
  pure x = seqN.fwd () <| (const x)
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
