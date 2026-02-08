module NN.Architectures.RNN

import Data.Tensor
import Data.Para

||| Defines the type of a RNN cell as a parametric map
||| @ x the type of the input
||| @ s the type of the state
||| @ y the type of the output
public export
RNNCell : (x, s, y : Type) -> Type
RNNCell x s y = (x, s) -\-> (y, s)

||| Defines the type of the unrolled RNN as a parametric map
||| @ n the number of unroll steps
public export
RNN : (x, s, y : Type) -> (n : Nat) ->Type
RNN x s y n = (Vect n x, s) -\-> (Vect n y, s)

||| Given a rnn cell, implement the full RNN by iterating that cell
||| Helper function for `RNNPara`
public export
RNNImpl : (cell : DPair (x, s) (const p) -> (y, s)) ->
  DPair (Vect n x, s) (const p) -> (Vect n y, s)
RNNImpl _ (([], s) ** _) = ([], s)
RNNImpl cell (((x :: xs), s) ** p) =
  let (y, s') = cell ((x, s) ** p)
      (ys, s'') = RNNImpl cell ((xs, s') ** p)
  in (y :: ys, s'')

||| Parametric map for the full RNN
public export
RNNPara : (cell : RNNCell x s y) ->
  IsNotDependent cell =>
  RNN x s y n
RNNPara (MkPara (const p) cell) @{MkNonDep p cell} = MkPara
  (\_ => p)
  (RNNImpl cell)


public export
runRNN : (rnn : RNN x s y n) ->
  (xs : Vect n x) ->
  (initialState : s) ->
  (p : Param rnn (xs, initialState)) ->
  Vect n y
runRNN rnn xs initialState p = fst $ Run rnn (xs, initialState) p

public export
exampleRNN : RNNCell Double Double Double
exampleRNN = MkPara (\_ => ()) (\((x, s) ** ()) => (if s > 4 then x else 0, s + 1))

public export
exampleInput : Vect 10 Double
exampleInput = [1,2,3,4,5,6,7,8,9,10]

public export
exampleOutput : Vect 10 Double
exampleOutput = runRNN (RNNPara exampleRNN) exampleInput 0 ()


