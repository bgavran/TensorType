module Data.Container.Object.Implementations

import Data.Container.Interfaces
import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Fin
import Data.Fin.Split

export
TensorMonoid List where
  tensorN = !% \x => (0 ** absurd)
  tensorM = !% \(x1, x2) => (x1 * x2 ** splitProd)

export
TensorMonoid (Vect n) where
  tensorN = !% \x => (() ** const ())
  tensorM = !% \x => (() ** (\x => (x, x)))
