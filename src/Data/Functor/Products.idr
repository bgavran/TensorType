module Data.Functor.Products

public export infixr 3 ><  -- Day convolution product
public export infixr 3 >*< -- Categorical product
public export infixr 3 >+< -- Categorical coproduct
-- Composition of functors is simply `.`

public export
(>*<) : (Type -> Type) -> (Type -> Type) -> (Type -> Type)
(>*<) f g a = (f a, g a)

public export
(>+<) : (Type -> Type) -> (Type -> Type) -> (Type -> Type)
(>+<) f g a = Either (f a) (g a)

public export
(><) : (Type -> Type) -> (Type -> Type) -> (Type -> Type)
(><) f g a = ?dayConvolutionProduct 
