module Data.Layout

import Data.Fin.Split
import Data.List.Quantifiers
import Language.Reflection
import Derive.Prelude

%language ElabReflection

||| We often deal with the 'logical' representation of tensors, but for
||| performance characteristics we need to be cognisant of how these tensors
||| are stored in the physical memory, which is in 1D linear order.
||| There are two options: row-major and column-major format
||| NumPy, PyTorch, TensorFlow and JAX use row-major indexing
||| The idea is that once linearised:
||| - row-major the last index of the array varies fastest
||| - column-major the first index of the array varies fastest
public export
data LayoutOrder = RowMajor
                 | ColumnMajor

%runElab derive "LayoutOrder" [Eq, Show]
%name LayoutOrder lo


||| Following most popular conventions, we use row-major ordering by default
public export
DefaultLayoutOrder : LayoutOrder
DefaultLayoutOrder = RowMajor

||| Layout-aware version of splitProd from Data.Fin.Split.
||| 
||| Row-major (splitProd): index k in a m×n matrix maps to (k/n, k%n)
|||   - goes through all columns before moving to next row
||| Column-major (splitProdColumnMajor): index k maps to (k%m, k/m)  
|||   - goes through all rows before moving to next column
|||
||| For a 2×3 matrix:
|||   Row-major order:    (0,0), (0,1), (0,2), (1,0), (1,1), (1,2)
|||   Column-major order: (0,0), (1,0), (0,1), (1,1), (0,2), (1,2)
public export
splitFinProd : {m, n : Nat} ->
  LayoutOrder ->
  Fin (m * n) ->
  (Fin m, Fin n)
splitFinProd RowMajor p = splitProd p
splitFinProd ColumnMajor p = swap (splitProd {m=n} {n=m}
  (replace {p = Fin} (multCommutative m n) p))

||| Layout-aware version of indexProd from Data.Fin.Split.
||| Inverse of splitFinProd: given (row, col) indices, compute linear index.
|||
||| Row-major: linear index = row * n + col
||| Column-major: linear index = col * m + row
|||
||| For a 2×3 matrix with (row=1, col=2):
|||   Row-major:    1 * 3 + 2 = 5
|||   Column-major: 2 * 2 + 1 = 5
public export
indexFinProd : {m, n : Nat} ->
  LayoutOrder ->
  Fin m ->
  Fin n ->
  Fin (m * n)
indexFinProd RowMajor row col = indexProd row col
indexFinProd ColumnMajor row col = 
  replace {p = Fin} (sym $ multCommutative m n) (indexProd {m=n} {n=m} col row)

||| Possibly not needed anymore?
||| Convert a linear index into a multi-dimensional index.
||| Generalizes splitFinProd to arbitrary dimensions.
|||
||| For a tensor of shape [2, 3, 4] with 24 elements:
|||   - Row-major: last dimension varies fastest
|||   - Column-major: first dimension varies fastest
|||
||| @ shape the shape of the tensor
||| @ lo    the memory layout order
||| @ idx   a linear index into the flattened tensor
public export
splitShape : {shape : List Nat} ->
  (lo : LayoutOrder) ->
  Fin (foldr (*) 1 shape) ->
  All Fin shape
splitShape {shape = []} _ _ = []
splitShape {shape = (n :: ns)} lo idx =
  let (i, rest) = splitFinProd {m=n} {n=foldr (*) 1 ns} lo idx
  in i :: splitShape lo rest
