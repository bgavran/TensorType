module Data.Container.Base

-- some imports that are likely needed for everything to function
import public Data.Fin
import public Data.Vect

-- main container definitions and instances, and products
import public Data.Container.Base.Definitions
import public Data.Container.Base.Instances

-- for manipulating concrete tree instances
import public Data.Trees
import public Data.Functor.Algebra
-- import public Data.Functor.Naperian
import public Data.Container.Base.TreeUtils

import public Data.Container.Base.Display2D.Display2D -- where to put

-- temp/misc
import public Data.Container.SubTerm
