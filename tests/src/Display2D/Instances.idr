module Display2D.Instances

import Data.Tensor

namespace CubicalTensors
  public export
  tensorVector : Tensor ["l" ~~> 6] Double
  tensorVector = arange

  public export
  tensorMatrix : Tensor ["j" ~~> 3, "k" ~~> 4] Double
  tensorMatrix = reshape $ arange {stop="total" ~~> 12}
  
  public export
  tensor3D : Tensor ["i" ~~> 2, "j" ~~> 3, "k" ~~> 2] Double
  tensor3D = reshape $ arange {stop="total" ~~> 12}

  public export
  tensor4D : Tensor ["i" ~~> 2, "j" ~~> 3, "k" ~~> 4, "l" ~~> 5] Double
  tensor4D = reshape $ arange {stop="total" ~~> 120}

  public export
  tensor5D : Tensor ["i" ~~> 2, "j" ~~> 3, "k" ~~> 4, "l" ~~> 5, "m" ~~> 6] Double
  tensor5D = reshape $ arange {stop="total" ~~> 720}


namespace LongTensors
  public export
  vectTest : Vect 156 Double
  vectTest = replicate 156 3

  public export
  longVector : Tensor ["i" ~~> 156] Double
  longVector = ># vectTest

  public export
  longVectorReshaped : Tensor ["j" ~~> 2, "k" ~~> 78] Double
  longVectorReshaped = reshape longVector

  public export
  longVector2 : Tensor ["i" ~~> 300] Double
  longVector2 = arange

namespace CubicalTensorsDecimal
  public export
  vectorDecimal : Tensor ["i" ~~> 3] Double
  vectorDecimal = ># [0.000, 1.23456, 0.0000001]

  public export
  matrixDecimal : Tensor ["j" ~~> 2, "k" ~~> 5] Double
  matrixDecimal = ># [ [ 0.01, 0.001, 0.0001, 0.00001, 0.000001]
                     , [ 10, 20, 30, 40, 50] ]

  public export
  matrixDecimal2 : Tensor ["j" ~~> 2, "k" ~~> 5] Double
  matrixDecimal2 = ># [ [1000, 10000, 100000, 1000000, 10000000]
                      , [40, 50, 60, 70, 80]]


namespace TreeTensors
  public export
  treeExample1 : Tensor ["myTree" ~> BinTree] Double
  treeExample1 = ># Node 60 (Node 7 (Leaf (-42)) (Leaf 46)) (Leaf 2)
  
  public export
  treeExample2 : Tensor ["myTree" ~> BinTree] Double
  treeExample2 = ># Node 5 (Leaf 100) (Leaf 4)
  
  public export
  treeExample3 : Tensor ["myTree" ~> BinTreeNode, "j" ~> Vect 2] Double
  treeExample3 = ># Node [4,1] (Node [17, 4] Leaf' Leaf') Leaf'
  
  public export
  treeExample4 : Tensor ["myTree"     ~> BinTreeNode,
                         "myTreeLeaf" ~> BinTreeLeaf,
                         "k"          ~> Vect 3] Double
  treeExample4 = >#
    Node (Node'
            (Leaf [1,2,3])
            (Leaf [4,5,6]))
      Leaf'
      (Node (Leaf [178, -43, 63]) Leaf' Leaf')
  
  public export
  treeExample5 : Tensor ["myTree" ~> BinTreeLeaf, "v" ~~> 2] Double
  treeExample5 = ># Node' (Node' (Leaf [1, -1])
                                 (Node' (Leaf [0.5, 1.2])
                                        (Leaf [0.3, -0.2])))
                          (Leaf [-0.3, 1.2])

  public export
  treeExample6 : Tensor ["myTree" ~> BinTree, "j" ~~> 300] Double
  treeExample6 = ># Node (replicate 300 3) (Leaf $ replicate 300 1) (Leaf $ replicate 300 2)
  
  public export
  treeExample7 : Tensor ["myTree" ~> BinTreeLeaf] Double
  treeExample7 = ># Node' (Node' (Leaf (-42)) (Leaf 46)) (Leaf 2)
  
  public export
  treeExample8 : Tensor ["myTree" ~> BinTreeNode] Double
  treeExample8 = ># Node 60 (Node 7 Leaf' Leaf')  Leaf'


namespace ListTensors
  public export
  listExample1 : Tensor ["i" ~> List, "i" ~> List] Double
  listExample1 = ># [ [1,2,3]
                    , [4,5,6] ]

  public export
  listExample2 : Tensor ["i" ~~> 3, "j" ~> List] Double
  listExample2 = ># [ [1,2,3]
                    , [4]
                    , [5,6,7,8] ]

  public export
  listExample3 : Tensor ["i" ~> List, "j" ~~> 2] Double
  listExample3 = ># [ [1,2]
                    , [3,4]
                    , [5,6]
                    , [7,8] ]


  public export
  listExample4 : Tensor ["i" ~> List, "j" ~> List, "k" ~> List] Double
  listExample4 = ># [ [[1,2,3,4], [6], [7,8,9]]
                    , [[4,5], [9,9,9,9,9], [4,2,0], [999]]]

  public export
  listExample5 : Tensor ["i" ~> List, "j" ~> BinTreeLeaf] Double
  listExample5 = ># [ Leaf 4
                    , Node' (Leaf 3) (Leaf 4)
                    , Node' (Node' (Leaf 5) (Leaf 6)) (Leaf 7)
                    , Node' (Leaf 7) (Leaf 8) ]


separator : String
separator = "-------------------------------------------------------"


public export
printAllTestInstances : IO ()
printAllTestInstances = do
  printLn tensorVector
  putStrLn separator
  printLn tensorMatrix
  putStrLn separator
  printLn tensor3D
  putStrLn separator
  printLn tensor4D
  putStrLn separator
  printLn tensor5D
  putStrLn separator
  printLn longVector
  putStrLn separator
  printLn longVectorReshaped
  putStrLn separator
  printLn longVector2
  putStrLn separator
  printLn vectorDecimal
  putStrLn separator
  printLn matrixDecimal
  putStrLn separator
  printLn matrixDecimal2
  putStrLn separator
  printLn treeExample1
  putStrLn separator
  printLn treeExample2
  putStrLn separator
  printLn treeExample3
  putStrLn separator
  printLn treeExample4
  putStrLn separator
  printLn treeExample5
  putStrLn separator
  printLn treeExample6
  putStrLn separator
  printLn treeExample7
  putStrLn separator
  printLn treeExample8
  putStrLn separator
  printLn listExample1
  putStrLn separator
  printLn listExample2
  putStrLn separator
  printLn listExample3
  putStrLn separator
  printLn listExample4
  putStrLn separator
  printLn listExample5
