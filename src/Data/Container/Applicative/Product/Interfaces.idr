module Data.Container.Applicative.Product.Interfaces

import Data.Container.Base
import Data.Container.Applicative.Object.Instances
import Data.Container.Applicative.Extension.Instances
import Data.Container.Applicative.TreeUtils

||| In `Data.Tree` we have analogos maps that need to be translated here
public export
TensorMonoid c => TensorMonoid (ApplicativeRoseTree {c=c}) where
  tensorN = !% \() => (LeafS ** \_ => ())
  tensorM = !% \(lt, rt) => ?applicativeRoseTree_tensorM

public export
TensorMonoid c => TensorMonoid (ApplicativeRoseTreeLeaf {c=c}) where
  tensorN = ?applicativeRoseTreeLeaf_tensorN
  tensorM = ?applicativeRoseTreeLeaf_tensorM

-- Node version likely does not exist?
public export
TensorMonoid c => TensorMonoid (ApplicativeRoseTreeNode {c=c}) where
  tensorN = ?applicativeRoseTreeNode_tensorN
  tensorM = ?applicativeRoseTreeNode_tensorM

  -- public export
  -- ApplicativeRoseTree : ContA -> ContA
  -- ApplicativeRoseTree c = (#) (ApplicativeRoseTree c)


-- namespace RoseTreeInstances
--   -- TODO this should be superseeded by the general applicative instance above?
--   public export
--   liftA2RoseTree' : RoseTree' a -> RoseTree' b -> RoseTree' (a, b)
--   liftA2RoseTree' t1 t2 = fromRoseTreeSame $
--     liftA2RoseTreeSame (toRoseTreeSame t1) (toRoseTreeSame t2)
-- 
--   public export
--   Applicative RoseTree' where
--     pure a = LeafS <| \_ => a
--     fs <*> vs = uncurry ($) <$> liftA2RoseTree' fs vs