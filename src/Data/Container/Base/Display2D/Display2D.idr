module Data.Container.Base.Display2D.Display2D

import Data.Fin
import Data.List
import Data.Vect


import Data.Container.Base.Object.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Product.Definitions

import Data.Container.Base.Instances

import public Data.Container.Base.Display2D.CharacterMap
import Data.ScientificNotation

import Data.Container.Base.TreeUtils
import Misc

%hide Syntax.WithProof.prefix.(@@)

{-------------------------------------------------------------------------------
Machinery for rendering values as rectangular 2D character grids.

Layout combinators (`besideAllGap`, `aboveAllSep`, `addBorderToGrid`, ...)
build new grids by (1) computing the output shape from the inputs at the data
level, and (2) building a new index function that dispatches into the inputs.
Both steps are O(1).  Lookup cost in a deeply composed grid is proportional
to the composition depth; `gridRows` (used by `showGrid`) is the one-shot
materialisation point that walks each cell exactly once.

As tensor utilities are added, functionality within this file will be rewritten
-------------------------------------------------------------------------------}

||| Approximate line-width budget for printed cubical tensors.  When a row of
||| fixed-width cells does not fit on a single line, the renderer breaks it
||| onto continuation lines so output stays within roughly this many columns.
||| Matches NumPy's default `linewidth = 75`.
public export
defaultLineWidth : Nat
defaultLineWidth = 75

{-------------------------------------------------------------------------------
Core: Grid type, accessors, basic constructors
-------------------------------------------------------------------------------}

||| A `Grid a` is a rectangular 2D matrix. Unlike `List >@ List`, which 
||| produces ragged arrays, this produces rectangular ones
public export
Grid : Type -> Type
Grid = Ext (List >< List)

public export
gridHeight : Grid a -> Nat
gridHeight ((h, _) <| _) = h

public export
gridWidth : Grid a -> Nat
gridWidth ((_, w) <| _) = w

||| Look up a cell.  Cost depends on how `g` was built; for grids made from
||| chained combinators the cost is proportional to the composition depth.
public export
gridIndex : (g : Grid a) -> Fin (gridHeight g) -> Fin (gridWidth g) -> a
gridIndex ((_, _) <| f) i j = f (i, j)

||| Build a grid from a height, width, and 2D index function.  O(1).
public export
mkGrid : (h, w : Nat) -> (Fin h -> Fin w -> a) -> Grid a
mkGrid h w f = (h, w) <| uncurry f


{-------------------------------------------------------------------------------
Materialisation
-------------------------------------------------------------------------------}

||| Convert a `Grid` into a list-of-rows view.  Walks the grid once, so this
||| is the natural one-shot materialisation point for delayed grids.
public export
gridRows : Grid a -> List (List a)
gridRows g =
  toList' $ Fin.tabulate {len = gridHeight g} $ \i =>
    toList' $ Fin.tabulate {len = gridWidth  g} $ \j =>
      gridIndex g i j

||| Format a `Grid Char` as a multi-line string.  Trailing pad characters on
||| each line are stripped, matching NumPy's printing conventions.
public export
showGrid : Grid Char -> String
showGrid =
  concat . intersperse "\n" . map (pack . dropFromEnd padCharacter) . gridRows


{-------------------------------------------------------------------------------
Primitive constructors
-------------------------------------------------------------------------------}

public export
emptyGrid : Grid a
emptyGrid = mkGrid 0 0 absurd

public export
singleValue : a -> Grid a
singleValue v = mkGrid 1 1 (\_, _ => v)

public export
uniformCol : a -> Nat -> Grid a
uniformCol v h = mkGrid h 1 (\_, _ => v)

public export
blankCol : Nat -> Grid Char
blankCol = uniformCol padCharacter

||| One-row grid built from a list of cells.
public export
rowGrid : List a -> Grid a
rowGrid xs = mkGrid 1 (length xs) (\_, j => index j (fromList xs))

||| 1-wide column carrying `marker` on its top row and `padCharacter` elsewhere.
||| `emptyGrid` if the height is zero.
public export
topMarkerCol : (marker : Char) -> (h : Nat) -> Grid Char
topMarkerCol _ Z = emptyGrid
topMarkerCol c (S k) = mkGrid (S k) 1 $ \i, _ => case i of
  FZ => c
  _  => padCharacter

||| 1-wide column carrying `marker` on its bottom row and `padCharacter`
||| elsewhere. `emptyGrid` if the height is zero.
public export
bottomMarkerCol : (marker : Char) -> (h : Nat) -> Grid Char
bottomMarkerCol _ Z = emptyGrid
bottomMarkerCol c (S k) = mkGrid (S k) 1 $ \i, _ => case i == last of
  True => c
  False => padCharacter


{-------------------------------------------------------------------------------
Multiway layout combinators

Each takes O(1) to construct and produces a delayed grid whose index function
linearly scans the inputs.  For typical fan-outs (2..16) this is plenty fast.
-------------------------------------------------------------------------------}

||| Locate global position `i` in a sequence of items each of width `size g`,
||| with `gap` blank positions between consecutive items.  Returns the item
||| together with a properly bounded local index, or `Nothing` if `i` lands in
||| a gap or past the end.
|||
||| Total: recursion is structural on the list of grids.
locateChunk : (size : Grid a -> Nat) ->
  (gap : Nat) ->
  (gs : List (Grid a)) ->
  Nat ->
  Maybe (g : Grid a ** Fin (size g))
locateChunk _ _ [] _ = Nothing
locateChunk size gap (g :: gs) i = case natToFin i (size g) of
  Just j  => Just (g ** j)
  Nothing => let sz = size g
             in case i < sz + gap of
               True => Nothing
               False => locateChunk size gap gs (minus i (sz + gap))

||| Place grids side-by-side with `gap` blank columns between each pair.  The
||| row dimension is the max of the children's heights; shorter children are
||| padded on the missing rows.
public export
besideAllGap : (padValue : a) -> (gap : Nat) -> List (Grid a) -> Grid a
besideAllGap _ _ [] = emptyGrid
besideAllGap _ _ [g] = g
besideAllGap pad gap grids@(_ :: _) =
  let maxHeight = max (gridHeight <$> grids)
      sumWidths = List.sum (gridWidth <$> grids) + gap * pred (length grids)
  in mkGrid maxHeight sumWidths $ \i, j => fromMaybe pad $ do
       (g ** j') <- locateChunk gridWidth gap grids (finToNat j)
       i' <- natToFin (finToNat i) (gridHeight g)
       pure (gridIndex g i' j')

||| Place grids side-by-side with no gap.
public export
besideAll : (padValue : a) -> List (Grid a) -> Grid a
besideAll pad = besideAllGap pad 0

||| Stack grids vertically, inserting `sep` blank rows between successive items.
||| The column dimension is the max of the children's widths; narrower children
||| are padded on the missing columns.
public export
aboveAllSep : (padValue : a) -> (sep : Nat) -> List (Grid a) -> Grid a
aboveAllSep _ _ [] = emptyGrid
aboveAllSep _ _ [g] = g
aboveAllSep pad sep grids@(_ :: _) =
  let sumHeights = List.sum (gridHeight <$> grids) + sep * pred (length grids)
      maxWidth = max (gridWidth <$> grids)
  in mkGrid sumHeights maxWidth $ \i, j => fromMaybe pad $ do
       (g ** i') <- locateChunk gridHeight sep grids (finToNat i)
       j' <- natToFin (finToNat j) (gridWidth g)
       pure (gridIndex g i' j')

||| Stack grids vertically with no separator.
public export
aboveAll : (padValue : a) -> List (Grid a) -> Grid a
aboveAll pad = aboveAllSep pad 0

||| Left-pad a grid with `padCharacter` columns to reach total width `w`.
||| No-op if `gridWidth g >= w`.
public export
padGridLeft : (w : Nat) -> Grid Char -> Grid Char
padGridLeft w g = besideAll padCharacter
  [mkGrid (gridHeight g) (w `minus` gridWidth g) (\_, _ => padCharacter), g]

{-------------------------------------------------------------------------------
Borders
-------------------------------------------------------------------------------}

||| Given a `k : Nat`, models a three-way classification of `Fin (S (S k))` into
||| first, last, or middle.
data Side : (k : Nat) -> Type where
  AtStart : Side k
  AtEnd   : Side k
  AtMid   : Fin k -> Side k

side : {k : Nat} -> Fin (S (S k)) -> Side k
side FZ     = AtStart
side (FS x) = maybe AtEnd AtMid (strengthen x)

||| Wrap a grid in a 1-character border specified by `box`.
public export
addBorderToGrid : (box : Box) => Grid Char -> Grid Char
addBorderToGrid g = mkGrid (2 + gridHeight g) (2 + gridWidth g) $ \i, j =>
  case (side i, side j) of
    (AtMid i', AtMid j') => gridIndex g i' j'
    (AtMid _,  _)        => box.vertical
    (_,        AtMid _)  => box.horizontal
    (AtStart,  AtStart)  => box.topLeft
    (AtStart,  AtEnd)    => box.topRight
    (AtEnd,    AtStart)  => box.bottomLeft
    (AtEnd,    AtEnd)    => box.bottomRight

||| Wrap a grid in a border if it has more than one row
public export
wrapNonEmpty : Box => Grid Char -> Grid Char
wrapNonEmpty g = applyWhen (gridHeight g > 1) addBorderToGrid g

||| Given a list of grids, make a function that wraps a grid in a border if
||| any of the grids in the list has more than one row
public export
wrapAllIfAnyNonEmpty : Box =>
  List (Grid Char) -> (Grid Char -> Grid Char)
wrapAllIfAnyNonEmpty grids =
  applyWhen (any (\g => gridHeight g > 1) grids) addBorderToGrid


{-------------------------------------------------------------------------------
List/pair brackets and joins
-------------------------------------------------------------------------------}

||| Join a list of grids horizontally with a separator between them
public export
horizontalListJoin : (listSyntax : ListSyntax) => List (Grid Char) -> Grid Char
horizontalListJoin []  = emptyGrid
horizontalListJoin [g] = g
horizontalListJoin gs  = besideAll padCharacter (intersperse sep gs)
  where sep = besideAll padCharacter
              [singleValue listSyntax.separator, singleValue padCharacter]

||| Wrap a list of grids vertically in `[` ... `]` brackets with `,` markers in 
||| front of subsequent items, as follows:
|||
|||     [item1
|||     ,item2
|||     ,item3]
||| 
||| `nSep` is the number of blank rows between items:
public export
wrapListBrackets : (listSyntax : ListSyntax) =>
  (nSep : Nat) -> List (Grid Char) -> Grid Char
wrapListBrackets _ [] = besideAll padCharacter
  [singleValue listSyntax.left, singleValue listSyntax.right]
wrapListBrackets nSep (x :: xs) =
  let body     = aboveAllSep padCharacter nSep (x :: xs)
      leftCol  = aboveAll padCharacter $
                   topMarkerCol listSyntax.left (gridHeight x) ::
                   concatMap (\g => [ blankCol nSep
                                    , topMarkerCol listSyntax.separator (gridHeight g)
                                    ]) xs
      rightCol = bottomMarkerCol listSyntax.right (gridHeight body)
  in besideAll padCharacter [leftCol, body, rightCol]


{-------------------------------------------------------------------------------
NumPy-style row wrapping for long innermost rows
-------------------------------------------------------------------------------}

||| Render a list of equal-width cells as `[ c0 c1 ... cN ]`, breaking the
||| output onto continuation lines when the single-line layout would exceed
||| `lineBudget` columns.  Continuation lines are indented by one space so
||| wrapped cells align under `c0`; the closing `]` sits next to the last cell
||| of the final chunk, so a shorter final chunk leaves trailing whitespace on
||| its line (NumPy-style).
|||
||| The single-line layout falls out automatically when `cellsPerLine >= length
||| children`, so no separate "flat" code path is needed.
public export
wrappedInnerRow : (listSyntax : ListSyntax) =>
  (lineBudget, gap : Nat) -> List (Grid Char) -> Grid Char
wrappedInnerRow _ _ [] = besideAll padCharacter
  [singleValue listSyntax.left, singleValue listSyntax.right]
wrappedInnerRow lineBudget gap children@(c :: _) =
  let cellsPerLine = max 1 $ (lineBudget `minus` 2 + gap) `div` (gridWidth c + gap)
      chunks       = chunksOf cellsPerLine children
      nChunks      = length chunks
      chunkRow : Nat -> List (Grid Char) -> Grid Char
      chunkRow i cs =
        let leftC  = if i == 0         then listSyntax.left  else padCharacter
            rightC = if S i == nChunks then listSyntax.right else padCharacter
        in besideAll padCharacter
             [ singleValue leftC
             , besideAllGap padCharacter gap cs
             , singleValue rightC ]
  in aboveAll padCharacter (mapWithIndex chunkRow chunks)


{-------------------------------------------------------------------------------
Display2D interface: rendering types as 2D character grids
-------------------------------------------------------------------------------}

||| Display a type as a 2D grid of characters.
||| For `a` being an extension of a container, this can be expresse in terms of
||| a container morphism... if we use `Maybe <!>`
public export
interface Display2D (0 a : Type) where
  constructor MkDisplay2D
  display2D : a -> Grid Char

public export
Display2D (Grid Char) where
  display2D = id

||| One-row grid from a `Show` instance.
public export
display2DFromShow : Show a => a -> Grid Char
display2DFromShow x = rowGrid (unpack (show x))

||| One-row grid from a `ScientificDisplay` instance.
public export
display2DFromSci : ScientificDisplay a => a -> Grid Char
display2DFromSci x = rowGrid (unpack (showSci x))

public export Display2D Int     where display2D = display2DFromShow
public export Display2D Integer where display2D = display2DFromSci
public export Display2D Double  where display2D = display2DFromSci
public export Display2D Nat     where display2D = display2DFromSci
public export Display2D Bool    where display2D = display2DFromShow
public export Display2D ()      where display2D = display2DFromShow
public export Display2D Char    where display2D = singleValue
public export Display2D String  where display2D s = rowGrid (unpack s)


{-------------------------------------------------------------------------------
Display2D instances for container extensions
-------------------------------------------------------------------------------}

public export
Display2D a => Display2D (Scalar' a) where
  display2D (() <| index) = display2D (index ())

public export
Display2D a => Display2D (Pair' a) where
  display2D (() <| index) = besideAll padCharacter
    [ singleValue (left AsciiPairSyntax)
    , display2D (index False)
    , singleValue (separator AsciiPairSyntax)
    , display2D (index True)
    , singleValue (right AsciiPairSyntax) ]

public export
Display2D a => Display2D (List' a) where
  display2D (_ <| index) = besideAll padCharacter
    [ singleValue (left AsciiListSyntax)
    , horizontalListJoin {listSyntax = AsciiListSyntax}
        (display2D <$> toList' (tabulate index))
    , singleValue (right AsciiListSyntax) ]


{-------------------------------------------------------------------------------
Tree helpers
-------------------------------------------------------------------------------}

||| 2-column tree-branch prefix: first row is `connector` + `treeHorizontal`;
||| subsequent rows are `continuation` + `treeGap`.
treeBranchPrefix : (tree : Tree) =>
  (connector, continuation : Char) -> (height : Nat) -> Grid Char
treeBranchPrefix _ _ Z = emptyGrid
treeBranchPrefix conn cont (S k) = mkGrid (S k) 2 $ \i, j =>
  case (i, j) of
    (FZ, FZ) => conn
    (FZ, _ ) => tree.horizontal
    (_ , FZ) => cont
    (_ , _ ) => tree.gap

||| Prepend a tree-branch prefix and a 1-column gap to a grid.
addBranch : Tree =>
  (connector, continuation : Char) -> Grid Char -> Grid Char
addBranch conn cont g = besideAll padCharacter
  [treeBranchPrefix conn cont (gridHeight g), blankCol (gridHeight g), g]

||| Full-width row between sibling subtrees: `vertical` then spaces.
treeSiblingGapRow : (tree : Tree) => (w : Nat) -> Grid Char
treeSiblingGapRow Z = emptyGrid
treeSiblingGapRow (S k) = mkGrid 1 (S k) $ \_, j => case j of
  FZ => tree.vertical
  _  => padCharacter

||| Lay out a tree node: root above, then left/right subtrees with branches.
displayNodeWithBranches : (tree : Tree) =>
  (root, left, right : Grid Char) -> Grid Char
displayNodeWithBranches root left right =
  let leftB  = addBranch tree.branchMid  tree.vertical left
      rightB = addBranch tree.branchLast tree.gap      right
      top    = aboveAll padCharacter
                 [root, treeSiblingGapRow (maximum (gridWidth root) (gridWidth leftB)), leftB]
  in aboveAll padCharacter [top, treeSiblingGapRow (gridWidth top), rightB]


{-------------------------------------------------------------------------------
BinTree (values on both nodes and leaves)
-------------------------------------------------------------------------------}

collectBinTreeValues : Display2D a =>
  BinTree' a ->
  (List (Grid Char), List (Grid Char))
collectBinTreeValues (LeafS <| index) = ([], [display2D (index AtLeaf)])
collectBinTreeValues (NodeS l r <| index) =
  case collectBinTreeValues (l <| (index . GoLeft)) of
    (ln, ll) => case collectBinTreeValues (r <| (index . GoRight)) of
      (rn, rl) => (display2D (index AtNode) :: (ln ++ rn), ll ++ rl)

displayBinTreeWith : Display2D a => (tree : Tree) =>
  (nodeBox, leafBox : Grid Char -> Grid Char) ->
  BinTree' a -> Grid Char
displayBinTreeWith _ leafBox (LeafS <| index)
  = leafBox (display2D (index AtLeaf))
displayBinTreeWith nodeBox leafBox (NodeS l r <| index) =
  displayNodeWithBranches (nodeBox (display2D (index AtNode)))
    (displayBinTreeWith nodeBox leafBox (l <| (index . GoLeft)))
    (displayBinTreeWith nodeBox leafBox (r <| (index . GoRight)))

displayBinTree : Display2D a => (tree : Tree) => (box : Box) =>
  BinTree' a -> Grid Char
displayBinTree t =
  let (nodeEGs, leafEGs) = collectBinTreeValues t 
  in displayBinTreeWith (wrapAllIfAnyNonEmpty nodeEGs)
                        (wrapAllIfAnyNonEmpty leafEGs) t 

public export
Display2D a => Display2D (BinTree' a) where
  display2D = displayBinTree {tree = SingleLineTree, box = DoubleLineBox}


{-------------------------------------------------------------------------------
BinTreeLeaf (values only on leaves)
-------------------------------------------------------------------------------}

collectLeafValues : Display2D a =>
  BinTreeLeaf' a ->
  List (Grid Char)
collectLeafValues (LeafS <| index) = [display2D (index AtLeaf)]
collectLeafValues (NodeS l r <| index) =
  collectLeafValues (l <| index . GoLeft) ++
  collectLeafValues (r <| index . GoRight)

displayBinTreeLeafWith : Display2D a => (tree : Tree) =>
  (leafBox : Grid Char -> Grid Char) ->
  BinTreeLeaf' a -> Grid Char
displayBinTreeLeafWith box (LeafS <| index) = box (display2D (index AtLeaf))
displayBinTreeLeafWith box (NodeS l r <| index) =
  displayNodeWithBranches (singleValue tree.placeholder)
    (displayBinTreeLeafWith box (l <| index . GoLeft))
    (displayBinTreeLeafWith box (r <| index . GoRight))

||| Uniform boxing for BinTreeLeaf: if any leaf is multi-line, box all
displayBinTreeLeaf : Display2D a => (tree : Tree) => (box : Box) =>
  BinTreeLeaf' a -> Grid Char
displayBinTreeLeaf t =
  displayBinTreeLeafWith (wrapAllIfAnyNonEmpty (collectLeafValues t)) t 

public export
Display2D a => Display2D (Ext BinTreeLeaf a) where
  display2D = displayBinTreeLeaf {tree = SingleLineTree, box = DoubleLineBox}


{-------------------------------------------------------------------------------
BinTreeNode (values only on nodes)
-------------------------------------------------------------------------------}

collectNodeValues : Display2D a =>
  BinTreeNode' a -> List (Grid Char)
collectNodeValues (LeafS <| _) = []
collectNodeValues (NodeS l r <| index) =
  let leftValues = collectNodeValues (l <| index . GoLeft)
      rightValues = collectNodeValues (r <| index . GoRight)
  in display2D (index AtNode) :: (leftValues ++ rightValues)

displayBinTreeNodeWith : Display2D a => (tree : Tree) =>
  (nodeBox : Grid Char -> Grid Char) ->
  BinTreeNode' a -> Grid Char
displayBinTreeNodeWith _ (LeafS <| _) = singleValue tree.placeholder
displayBinTreeNodeWith box (NodeS l r <| index) =
  displayNodeWithBranches (box (display2D (index AtNode)))
    (displayBinTreeNodeWith box (l <| index . GoLeft))
    (displayBinTreeNodeWith box (r <| index . GoRight))

displayBinTreeNode : Display2D a => (tree : Tree) => (box : Box) =>
  BinTreeNode' a -> Grid Char
displayBinTreeNode t =
  displayBinTreeNodeWith (wrapAllIfAnyNonEmpty (collectNodeValues t)) t

public export
Display2D a => Display2D (Ext BinTreeNode a) where
  display2D = displayBinTreeNode {tree = SingleLineTree, box = DoubleLineBox}

public export
{n : Nat} -> Display2D a => Display2D (Ext (Vect n) a) where
  display2D (() <| index) = display2D {a = Ext List a} (n <| index)

public export
showViaDisplay2D : Display2D a => a -> String
showViaDisplay2D = showGrid . display2D

public export
Display2D a => Show (Scalar' a) where
  show = showViaDisplay2D

public export
Display2D a => Show (Pair' a) where
  show = showViaDisplay2D

public export
Display2D a => Show (List' a) where
  show = showViaDisplay2D

public export
{n : Nat} -> Display2D a => Show (Vect' n a) where
  show = showViaDisplay2D

-- Technocally should not need assert_total here, but its hard to convince
-- the typechecker
public export
Display2D a => Show (BinTree' a) where
  show t = assert_total $ showViaDisplay2D t

public export
Display2D a => Show (BinTreeLeaf' a) where
  show t = assert_total $ showViaDisplay2D t

public export
Display2D a => Show (BinTreeNode' a) where
  show t = assert_total $ showViaDisplay2D t