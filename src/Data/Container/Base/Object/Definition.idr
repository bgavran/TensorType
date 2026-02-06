module Data.Container.Base.Object.Definition

||| Containers capture the idea that datatypes consist of groups of memory 
||| locations where data can be stored. Locations for a particular group are 
||| referred to as 'positions' and a particular group is referred to as a
||| 'shape'.
public export
record Cont where
  constructor (!>)
  ||| A type of shapes
  Shp : Type
  ||| For each shape, a set of positions
  Pos : Shp -> Type

export typebind infixr 0 !>

%name Cont c, c', c''

||| Convenience datatype storing the property that
||| a container `c` has an interface `i` on its positions
public export
data InterfaceOnPositions : (c : Cont) -> (i : Type -> Type) -> Type where
  ||| For every shape s the set of positions c.Pos s has that interface
  MkI : (p : (s : c.Shp) -> i (c.Pos s)) =>
    InterfaceOnPositions c i



||| Used in learning, where we want to know that the tangent space over a
||| particular parameter is equal to the parameter space itself
public export
data IsFlat : Cont -> Type where
  MkIsFlat : (p : Type) -> IsFlat ((_ : p) !> p)