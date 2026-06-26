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

||| Thought of as a choice of a shape, and a sequence of choices one
||| needs to make to reach a particular position. 
||| For contianers that are not defined as fixpoints, this "choices" are not
||| made using container machinery, but directly in Idris
||| Nonetheless, even for `List`, to define a value of `Fin n` we have to 
||| recursively go through a "path"
public export
Path : Cont -> Type
Path c = (x : c.Shp ** c.Pos x)
