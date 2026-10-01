module Data.Container.Base.Endofunctor.Instances

import Data.Vect

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Product.Definition
import Data.Container.Base.Endofunctor.Definition
import Data.Container.Base.Properties.Definition

import Data.Container.Base.Object.Instances

import Misc

{-------------------------------------------------------------------------------
Distributive laws between endofunctors and other stuff
-------------------------------------------------------------------------------}

public export
compositionBangPos : Functor m => m <!> (c >@ d) =%> c >@ (m <!> d)
compositionBangPos = !% \ex => (ex ** \(cp ** md) => (\dp => (cp ** dp)) <$> md)

||| Composition product analogue of `joinBw`
||| On the backward pass, it flattens an `m` of (position, `m` of positions)
||| pairs into a single `m` of full positions.
public export
joinBwComp : {0 c, d : Cont} -> {m : Type -> Type} -> Monad m =>
  m <!> (c >@ d) =%> m <!> (c >@ (m <!> d))
joinBwComp = joinBw {c = c >@ d} %>> (m <!> compositionBangPos)

public export
coproductBang : m <!> (c >+< d) =%> (m <!> c) >+< (m <!> d)
coproductBang = !% \case
  Left x => (Left x ** id)
  Right y => (Right y ** id)

public export
tensorBang : Applicative m => m <!> (c >< d) =%> (m <!> c) >< (m <!> d)
tensorBang = !% \(x, y) => ((x, y) ** \(mx', my') => [| (mx', my') |])

public export
compositionBang : Monoid d.Shp => !! (c >@ d) =%> !! c >@ !! d
compositionBang = !% \(cShp <| cPosTodShp) => (cShp <| ?extract **
  \(ma ** mb) => do
    ?fifif)

public export
compositionBangBack : Monad m => (m <!> c) >@ (m <!> d) =%> m <!> (c >@ d)
compositionBangBack = !% \ex => (shapeExt ex <| (index ex) . pure **
  \mdp => ?hmm)


-- public export
-- unplug : IsDecidable c =>
--   Pointed c =%> Scalar >*< Deriv c
-- unplug @{MkI dec} = !% \(s ** p) => (((), (s ** p)) ** \case
--   Left () => p
--   Right (p' ** _) => p')
-- 
-- 
-- public export
-- plug : IsDecidable c =>
--   Scalar >*< Deriv c =%> Pointed c
-- plug @{MkI dec} = !% \((), (s ** p)) => ((s ** p) **
--   \p' => case decEq @{dec s} p p' of
--     Yes _ => Left ()
--     No contra => Right (p' ** proofIneqIsNo @{dec s} contra))


||| Can also be written in terms of unplug and plug
public export
setLens : IsDecidable c => Pointed c >*< Scalar =%> c
setLens @{MkI dec} = !% \((s ** p), ()) => (s **
  \p' => case decEq @{dec s} p p' of 
        No _ => Left p'
        Yes _ => Right ())

||| The `index` field of an extension defines a "getter" for a container
||| This is the container setter
public export
set : IsDecidable c =>
  (e : Ext c x) -> -- container filled with data
  c.Pos (shapeExt e) -> -- a specific position
  x -> -- new value
  Ext c x -- updated container where the specific position contains new value
set e i v = setLens.ext $
  ((shapeExt e ** i), ()) <| either (index e) (const v)