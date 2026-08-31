module Data.Materialise

||| Used for `Data.Tensor` and structures thereof: directly evaluates the tensor
||| instead of keeping it tabulated form
||| There's probably a more principled solution
public export
interface Materialise a where
  constructor MkMaterialise
  materialise : a -> a
  ||| Extensionally the data is equivalent
  materialiseIsId : {x : a} -> materialise x = x

public export
Materialise Double where
  materialise = id
  materialiseIsId = Refl

public export
Materialise Integer where
  materialise = id
  materialiseIsId = Refl

public export
Materialise Nat where
  materialise = id
  materialiseIsId = Refl

public export
Materialise Unit where
  materialise = id
  materialiseIsId = Refl

public export
Materialise a => Materialise b => Materialise (a, b) where
  materialise (x, y) = (materialise x, materialise y)
  materialiseIsId {x=(a, b)} = cong2 (,) materialiseIsId materialiseIsId