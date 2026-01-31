module Data.CT.DependentPara.Instances

import Data.CT.Category.Definition
import Data.CT.Functor.Definition
import Data.CT.DependentAction.Definition
import Data.CT.DependentPara.Definition
import Data.CT.Category.Instances
import Data.CT.Functor.Instances
import Data.CT.DependentAction.Instances

import Data.Container

||| Parametric functions
||| "Usual" dependent para on sets and functions
public export
Para : (a, b : Type) -> Type 
Para = DepParaMor DepActOnType

||| Parametric dependent lenses
public export
ParaDLens : (a, b : Cont) -> Type
ParaDLens = DepParaMor DepActOnCont