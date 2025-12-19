module Attention

import Data.Tensor
import NN.Architectures

{-------------------------------------------------------------------------------
Attention example

Will run self attention as usual, on matrices, and then on trees
-------------------------------------------------------------------------------}

||| We'll first instantiate self attention as a parametric map on matrices
||| `n` here represents the length of sequence
||| `d` here represents the dimension of the features
SelfAttentionMat : {n, d : Nat} ->
  {default False causalMask : Bool} ->
  Tensor [n, d] Double -\-> Tensor [n, d] Double
SelfAttentionMat {causalMask} = case causalMask of
  False => SelfAttention softargmaxImpl
  True => SelfAttention {causalMask=Attention.causalMask} softargmaxImpl


||| Let's fix a simple input matrix
inputMatrix : Tensor [3, 2] Double
inputMatrix = ># [ [1, 3]
                 , [2, -3]
                 , [0, 0.3]]

||| Let's fix attention parameters for the query, key and value matrices.
||| For instance, a matrix of ones, a triangular matrix, and a matrix of threes
params : {d : Nat} -> CSelfAttentionParams (Vect d) {a=Double}
params = MkCSAParams ones tri (ones <&> (*3))

||| Now we can run self attention on the input matrix
||| This value can be inspected in REPL, or otherwise
outputMatrix : Tensor [3, 2] Double
outputMatrix = Run (SelfAttentionMat {causalMask=True}) inputMatrix params


||| Now we'll instantiate self attention as a parametric map on trees and use
||| container tensors for this. Here we'll study attention where the input
||| structure isn't a sequence, but a tree, but we'll keep the feature structure
||| as a sequence
||| That is, instead of `CTensor [Vect n, Vect d] Double`
||| we'll have `CTensor [BinTreeLeaf, Vect d] Double`
SelfAttentionTree : {d : Nat} ->
  CTensor [BinTreeLeaf, Vect d] Double -\->
  CTensor [BinTreeLeaf, Vect d] Double
SelfAttentionTree = SelfAttention softargmaxImpl

||| We fix a simple input tree
||| Notably, the set of parameters can be the same as the one for matrices
inputTree : CTensor [BinTreeLeaf, Vect 2] Double
inputTree = ># Node' (Node' (Leaf [1, -1])
                            (Leaf [0.5, 1.2]))
                     (Leaf [-0.3, 1.2])

||| We can run self attention on the tree, and inspect the result
outputTree : CTensor [BinTreeLeaf, Vect 2] Double
outputTree = Run SelfAttentionTree inputTree params