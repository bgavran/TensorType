module Data.Container.Applicative.Concrete.Instances

import Data.Container.Base
import Data.Container.Applicative.Object.Instances
import Data.Container.Applicative.Extension.Instances
import Data.Container.Applicative.TreeUtils

public export
fromRoseTreeSame : RoseTreeSame a -> RoseTree' a
fromRoseTreeSame (Leaf a) = LeafS <| \_ => a
fromRoseTreeSame (Node a rts) =
  let t = fromRoseTreeSame <$> fromList rts
  in NodeS (shapeExt <$> t) <| \case
    AtNode => a
    SubTree ps posSt =>
      let rw1 : (shapeExt t = shapeExt (shapeExt <$> t)) := sym (mapShapeExt t)
          rw2 : (shapeExt (index t (rewrite sym (mapShapeExt {f=shapeExt} t) in ps)) = index (shapeExt <$> t) ps) := mapIndexCont {c=List} {f=shapeExt} t ps
      in index
      (index t (rewrite rw1 in ps))
      (rewrite rw2 in posSt)
      -- for some reason all the explicit type annotations above are needed
      -- to convince the typechecker

public export
toRoseTreeSame : RoseTree' a -> RoseTreeSame a
toRoseTreeSame (LeafS <| contentAt) = Leaf (contentAt AtLeaf)
toRoseTreeSame (NodeS (len <| content) <| contentAt)
  = Node (contentAt AtNode)
         (toList $ toRoseTreeSame 
                <$> (\i => content i <| contentAt . SubTree i)
                <$> positionsCont)


public export
FromConcrete RoseTree where
  concreteType = RoseTreeSame
  concreteFunctor = %search
  fromConcreteTy = fromRoseTreeSame
  toConcreteTy = toRoseTreeSame
