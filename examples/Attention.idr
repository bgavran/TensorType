module Attention

import Data.Tensor
import NN.Architectures

{-------------------------------------------------------------------------------
Attention example

Will run self attention as usual, on matrices, and then on trees
-------------------------------------------------------------------------------}

||| We start by dealing with ordinary matrices, and define the matrix axes

||| The length of the input sequence
SeqLen : Axis
SeqLen = "seqLen" ~~> 3

||| The number of tokens for each element in the sequence
NumTokens : Axis
NumTokens = "numTokens" ~~> 4

||| We'll first instantiate self attention as a parametric map on matrices
SelfAttentionMat : {default False causalMask : Bool} ->
  Tensor [SeqLen, NumTokens] Double -\->
  Tensor [SeqLen, NumTokens] Double
SelfAttentionMat {causalMask} = case causalMask of
  False => SelfAttention softargmaxImpl
  True => SelfAttention {causalMask=Attention.causalMask} softargmaxImpl

||| Let's fix a simple input matrix
inputMatrix : Tensor [SeqLen, NumTokens] Double
inputMatrix = ># [ [1, 3, 3, 2]
                 , [2, -3, 2, 1]
                 , [0, 0.3, 10, 9]]

||| Let's fix attention parameters for the query, key and value matrices.
||| For instance, a matrix of ones, a triangular matrix, and a matrix of threes
params : SelfAttentionParams NumTokens {a=Double}
params = MkSAParams ones tri (ones <&> (*3))

||| Now we can run self attention on the input matrix
||| This value can be inspected in REPL via `:exec printLn outputMatrix`
outputMatrix : Tensor [SeqLen, NumTokens] Double
outputMatrix = Run (SelfAttentionMat {causalMask=True}) inputMatrix params


||| Now we instantiate self attention not operating on a vector of vectors
||| (i.e. a matrix), but a *tree* of vectors. We'll first define the axis
InputStructure : Axis
InputStructure = "inputStructure" ~> BinTreeLeaf

||| We keep features as a vector, and define the self-attention map
||| Notably, we do not use any causal mask
SelfAttentionTree : Tensor [InputStructure, NumTokens] Double -\->
  Tensor [InputStructure, NumTokens] Double
SelfAttentionTree = SelfAttention softargmaxImpl

||| We fix a simple input tree
||| Notably, the set of parameters can be the same as the one for matrices
inputTree : Tensor [InputStructure, NumTokens] Double
inputTree = ># Node' (Node' (Leaf [1, -1, 3, 2])
                            (Node' (Leaf [0.5, 1.2, 2, 1])
                                   (Leaf [0.3, 4, 10, 9])))
                     (Leaf [-0.3, 1.2, -13, -0.3])

||| We can run self attention on the tree, and inspect the result
outputTree : Tensor [InputStructure, NumTokens] Double
outputTree = Run SelfAttentionTree inputTree params