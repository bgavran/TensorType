module Data.Autodiff.Core.SearchIssues

{-
  PROOF SEARCH LIMITATIONS IN IDRIS
  ==================================
  
  This file documents what does and doesn't work with %search and auto-implicits.
-}

-- Simple type family indexed by a function
data Diff : (f : a -> b) -> Type where
  MkDiff : (deriv : String) -> Diff f


--------------------------------------------------------------------------------
-- FINDING 1: Monomorphic hints work
--------------------------------------------------------------------------------

MyFn : Int -> Int
MyFn x = x + x

%hint myFnDiff : Diff MyFn
myFnDiff = MkDiff "2"

testMono : Diff MyFn
testMono = %search  -- WORKS


--------------------------------------------------------------------------------
-- FINDING 2: Polymorphic hints WITHOUT extra constraints work
--------------------------------------------------------------------------------

PolyCopy : a -> (a, a)
PolyCopy x = (x, x)

%hint polyCopyDiff : {a : Type} -> Diff (PolyCopy {a})
polyCopyDiff = MkDiff "copy"

testPolyNoConstraint : Diff (PolyCopy {a=Int})
testPolyNoConstraint = %search  -- WORKS


--------------------------------------------------------------------------------
-- FINDING 3: Polymorphic hints WITH constraints (like Num a) FAIL
--------------------------------------------------------------------------------

PolyMul : Num a => (a, a) -> a
PolyMul (x, y) = x * y

%hint polyMulDiff : {a : Type} -> Num a => Diff (PolyMul {a})
polyMulDiff = MkDiff "mul"

-- This FAILS:
failing "Can't find an implementation for Diff"
  testPolyWithConstraint : Diff (PolyMul {a=Int})
  testPolyWithConstraint = %search

-- Workaround: monomorphic hint
%hint polyMulDiffInt : Diff (PolyMul {a=Int})
polyMulDiffInt = MkDiff "mul int"

testPolyWithConstraintFixed : Diff (PolyMul {a=Int})
testPolyWithConstraintFixed = %search  -- WORKS with monomorphic hint


--------------------------------------------------------------------------------
-- FINDING 4: Composition hints FAIL
--------------------------------------------------------------------------------

MyInc : Int -> Int
MyInc x = x + 1

%hint myIncDiff : Diff MyInc
myIncDiff = MkDiff "1"

%hint composeDiff : {f : a -> b} -> {g : b -> c} ->
                    Diff f -> Diff g -> Diff (g . f)
composeDiff _ _ = MkDiff "chain"

-- This FAILS:
failing "Can't find an implementation for Diff"
  testComposition : Diff (MyInc . MyFn)
  testComposition = %search

-- Workaround: explicit call
testCompositionExplicit : Diff (MyInc . MyFn)
testCompositionExplicit = composeDiff myFnDiff myIncDiff  -- WORKS


--------------------------------------------------------------------------------
-- SUMMARY
--------------------------------------------------------------------------------

{-
  What works with %search:
  ✓ Monomorphic hints: `Diff MyFn` when `%hint myFnDiff : Diff MyFn`
  ✓ Polymorphic hints without constraints: `{a : Type} -> Diff (F {a})`
  
  What FAILS with %search:
  ✗ Polymorphic hints WITH constraints: `{a : Type} -> Num a => Diff (F {a})`
  ✗ Composition: search can't decompose (g . f) to find g and f
  
  Workarounds:
  - For polymorphic functions with constraints: add monomorphic hints for each concrete type
  - For composition: use explicit function application or an operator like >>>
-}
