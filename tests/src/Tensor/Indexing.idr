module Tensor.Indexing

import Hedgehog
import Data.Tensor

%hide Syntax.WithProof.prefix.(@@) -- (@@) is used here for indexing

t1 : Tensor ["i" ~~> 3, "j" ~~> 4] Double
t1 = reshape $ arange {stop="l" ~~> 12}

export
cubicalIndexingGroup : Group
cubicalIndexingGroup = MkGroup "Cubical tensor indexing"
  [ ("Cubical indexing example 1", property1 $ t1 @@ [0, 0] === 0)
  , ("Cubical indexing example 2", property1 $ t1 @@ [1, 2] === 6)
  , ("Cubical indexing example 3", property1 $ t1 @@ [2, 3] === 11) ]



treeTensor1 : Tensor ["binTree" ~> BinTreeLeaf, "v" ~~> 2] Double
treeTensor1 = ># Node' (Node' (Leaf [1, 2]) (Leaf [3, 4])) (Leaf [5, 6])

export
indexingGroup : Group
indexingGroup = MkGroup "Tree tensor indexing"
  [ ("Tree indexing example 1", property1 $
    treeTensor1 @@ [GoLeft (GoLeft AtLeaf), 0] === 1)
  , ("Tree indexing example 2", property1 $
    treeTensor1 @@ [GoLeft (GoLeft AtLeaf), 1] === 2)
  , ("Tree indexing example 3", property1 $
    treeTensor1 @@ [GoRight AtLeaf, 1] === 6)
  , ("Tree indexing example 3", property1 $
    treeTensor1 @@ [GoLeft (GoRight AtLeaf), 0] === 3)
  , ("Tree indexing example 4", property1 $
    treeTensor1 @@ [GoLeft (GoRight AtLeaf), 1] === 6) ]