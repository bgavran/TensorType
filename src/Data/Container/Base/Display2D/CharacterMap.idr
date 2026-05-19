module Data.Container.Base.Display2D.CharacterMap

public export
padCharacter : Char
padCharacter = ' '

public export
record Tree where
  constructor MkTree
  horizontal : Char
  branchMid : Char
  branchLast : Char
  vertical : Char
  gap : Char
  placeholder : Char

||| Used for drawing a box border
public export
record Box where
  constructor MkBox
  topLeft : Char
  topRight : Char
  bottomLeft : Char
  bottomRight : Char
  horizontal : Char
  vertical : Char

||| Used for rendering list-like syntax
public export
record ListSyntax where
  constructor MkListSyntax
  left : Char
  right : Char
  separator : Char

||| Used for rendering pair-like syntax
public export
record PairSyntax where
  constructor MkPairSyntax
  left : Char
  right : Char
  separator : Char

public export
SingleLineTree : Tree
SingleLineTree = MkTree
  '─'
  '├'
  '└'
  '│'
  ' '
  '\x00B7'

||| Double-line, to separate from tree lines
public export
DoubleLineBox : Box
DoubleLineBox = MkBox
  '╔'
  '╗'
  '╚'
  '╝'
  '═'
  '║'

public export
AsciiListSyntax : ListSyntax
AsciiListSyntax = MkListSyntax
  '['
  ']'
  ','

public export
AsciiPairSyntax : PairSyntax
AsciiPairSyntax = MkPairSyntax
  '('
  ')'
  ','