module Data.Container.Base.Endofunctor.Instances

import Data.Vect

import Data.Container.Base.Object.Definition
import Data.Container.Base.Morphism.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Product.Definition
import Data.Container.Base.Endofunctor.Definition

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
compositionBang : Monoid d.Shp => !! (c >@ d) =%> (!! c) >@ (!! d)
compositionBang = !% \(cShp <| cPosTodShp) => (cShp <| ?extract **
  \(ma ** mb) => do
    ?fifif)

public export
compositionBangBack : Monad m => (m <!> c) >@ (m <!> d) =%> m <!> (c >@ d)
compositionBangBack = !% \ex => (shapeExt ex <| (index ex) . pure **
  \mdp => ?hmm)