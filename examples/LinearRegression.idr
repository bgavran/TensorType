module LinearRegression

import Data.Tensor
import NN.Architectures

public export
multiLayerPerceptronExample : Tensor [2] Double -\-> Tensor [2] Double
multiLayerPerceptronExample = multiLayerPerceptron {ieva=Vect 2} 1 id

  

