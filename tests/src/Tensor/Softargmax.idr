module Tensor.Softargmax

import Hedgehog

import Data.Tensor

logits : Tensor ["d" ~~> 4] Double
logits = ># [1.0, 2.0, 3.0, 4.0]

probs : Tensor ["d" ~~> 4] Double
probs = softargmaxImpl logits

export
softargmaxGroup : Group
softargmaxGroup = MkGroup "Softargmax"
  [ ("Probabilities sum to 1", property1 $
      assert (isClose (reduce probs) 1.0))
  , ("Uniform logits give the uniform distribution", property1 $
      assert (allClose (softargmaxImpl (fill {shape=["d" ~~> 4]} 0)) (fill 0.25)))
  , ("Test on known values: softargmax [0, log 3] = [1/4, 3/4]", property1 $ do
      let t : Tensor ["d" ~~> 2] Double
          t = ># [0.0, log 3.0]
      assert (allClose (softargmaxImpl t) (># [0.25, 0.75])))
  , ("Invariant under shifting logits", property1 $
      assert (allClose probs (softargmaxImpl (logits <&> (+ 1000.0)))))
  , ("Preserves argmax", property1 $
      argmax probs === argmax logits)
  , ("Evaluates correctly concretely", property1 $
      assert (allClose {atol=1.0e-12} {rtol=0.0} probs
        (># [ 0.032058603280084974
            , 0.08714431874203253
            , 0.23688281808991005
            , 0.643914259887972 ])))
  ]
