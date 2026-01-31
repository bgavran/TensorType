module Data.CT.Category.Definition

public export
record Cat where
  constructor MkCat
  0 Obj : Type
  0 Hom : Obj -> Obj -> Type