module Data.Autodiff.MLens

import Data.Container
import Data.Vect.Quantifiers

export prefix 0 !%%

||| Similar to a monadic dependent lens, but not quite
public export
data MLens : {m : Type -> Type} -> Monad m => (c1, c2 : Cont) -> Type where
    (!%%) : {m : Type -> Type} -> Monad m => 
      {c1, c2 : Cont} ->
      ((x : c1.Shp) -> m (y : c2.Shp ** (c2.Pos y -> c1.Pos x))) ->
      MLens {m} c1 c2

public export
(%%!) : {m : Type -> Type} -> Monad m =>
  MLens {m} c1 c2 -> (x : c1.Shp) -> m (y : c2.Shp ** (c2.Pos y -> c1.Pos x))
(%%!) (!%% f) x = f x