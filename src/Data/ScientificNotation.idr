module Data.ScientificNotation

import Data.List
import Data.Nat
import Data.String

import Misc

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
This file contains custom scientific formatting for numeric types.

While Idris' `Show` for numeric primitives already exists, it:
* does not permit precise control over ranges the scientific notation is invoked
* is backend-dependent, meaning that Scheme formats differently than JS
* does not allow us to do a two-pass formatting such that global tensor 
  information dictates the render for a particular element. (I.e. if any number
  is within scientific notation range, then all numbers get rendered in scientific notation)

-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

||| Interface for displaying numeric types that dynamically switches between
||| standard and scientific notation based on magnitude
||| If `forceScientific` is `True`, then we render in scientific notation no
||| matter what the value is
public export
interface Num a => ScientificDisplay a where
  -- ideally we'd use something this: {default False forceScientific : Bool} -> 
  showSci : a -> String

||| Magnitude above which `Double` values switch to scientific notation.
public export
sciUpperM : Double
sciUpperM = 1.0e6

||| Magnitude below which `Double` values switch to scientific notation.
public export
sciLowerM : Double
sciLowerM = 1.0e-4

||| Default precision used by numeric primitives with scientific notation
||| This is maximum, trailing zeros are removed.
public export
defaultScientificPrecision : Nat
defaultScientificPrecision = 4

||| Symbol used to denote the exponent in scientific notation, i.e. `1.0e+03`
public export
sciSymbol : Char
sciSymbol = 'e'

||| True when `d` is non-zero and outside the range
public export
needsScientific : Double -> Bool
needsScientific d = d /= 0.0 && (m < sciLowerM || m >= sciUpperM)
  where m = abs d

--------------------------------------------------------------------------------
-- Formatting primitives
--------------------------------------------------------------------------------

||| Format an integer exponent as `e+XX` or `e-XX`.
||| `formatExp 5 == "e+05"`
||| `formatExp -123 == "e-123"`
public export
formatExp : Integer -> String
formatExp n = singleton sciSymbol ++ sign ++ applyWhen (length ds < 2) ("0" ++) ds
  where sign : String
        sign = if n < 0 then "-" else "+"
        ds : String
        ds = show (abs n)


||| Multiply a decimal number by `10^prec`, and round it to the nearest integer
||| `round 2 3.14159 == 314`
||| `round 3 3.14159 == 3142`
||| `round 3 3.14100 == 3141`
roundScaled : (prec : Nat) -> Double -> Integer
roundScaled prec d = cast (floor (abs d * pow 10.0 (cast prec) + 0.5))

||| Format a non-negative integer as a decimal string.
||| `prec` controls how many digits appear after the decimal point
||| Input is taken to already be multiplied by `10^prec`
||| Zero-padding is added on the left when there are not enough digits.
||| ```
||| formatDigits 5 314159 == "3.14159"
||| formatDigits 3 314159 == "314.159"
||| formatDigits 2 5      == "0.05"
||| formatDigits 0 42     == "42"
||| ```
public export
formatDigits : (prec : Nat) -> (digits : Integer) -> String
formatDigits 0 n = show n
formatDigits prec n = substr 0 nDig padded ++ "." ++ substr nDig prec padded
  where len : Nat
        len = length (show n)
        padded : String
        padded = applyWhen (len <= prec)
                   (pack (replicate (S prec `minus` len) '0') ++)
                   (show n)
        nDig : Nat -- number of digits to the left of the decimal point
        nDig = length padded `minus` prec

||| Format a Double in standard notation with a fixed number of decimal places.
||| Rounds the last decimal to the nearest digit, and possibly pads with zeros,
||| if precision is greater than the number of digits after the decimal point.
||| ```
||| showDoublePrecision 3 3.14159  == "3.142"
||| showDoublePrecision 3 3.14100  == "3.141"
||| showDoublePrecision 0 3.14159  == "3"
||| showDoublePrecision 4 100.0    == "100.0000"
||| ```
public export
showDoublePrecision : (precision : Nat) -> Double -> String
showDoublePrecision prec d = applyWhen (d < 0) ("-" ++) $
  formatDigits prec (roundScaled prec d)

||| Decompose `|d|` into `(mantissa, exponent)` with `1 ≤ mantissa < 10`,
||| correcting the "one-decade" drift that `floor . log10` can produce at
||| decade boundaries (e.g. `log10 0.999... = -1.4e-16`, not 0).
||| Pre: `d ≠ 0`.
decimalDecompose : Double -> (Double, Integer)
decimalDecompose d =
  let m  = abs d
      e  = cast (floor (log m / log 10.0))
      m0 = m / pow 10.0 (cast e)
  in if m0 >= 10.0    then (m0 / 10.0, e + 1)
     else if m0 < 1.0 then (m0 * 10.0, e - 1)
     else                  (m0,        e)

||| Format a Double in scientific notation with a fixed number of
||| decimal places in the mantissa.
|||
||| ```
||| showDoubleScientific 5 3.14159    == "3.14159e+00"
||| showDoubleScientific 5 (-0.005)   == "-5.00000e-03"
||| showDoubleScientific 5 100.0      == "1.00000e+02"
||| showDoubleScientific 5 0.0000001  == "1.00000e-07"
||| ```
public export
showDoubleScientific : (precision : Nat) -> Double -> String
showDoubleScientific prec 0.0 = formatDigits prec 0 ++ formatExp 0
showDoubleScientific prec d =
  applyWhen (d < 0) ("-" ++) $ formatDigits prec mantInt ++ formatExp expFinal
  where
    decomp : (Double, Integer)
    decomp = decimalDecompose d

    -- Round mantissa to a scaled integer with `prec` digits of precision.
    rounded : Integer
    rounded = roundScaled prec (fst decomp)

    -- If rounding pushed the mantissa to ≥ 10, carry one decade.
    overflow : Bool
    overflow = rounded >= cast (pow 10.0 (cast (S prec)))

    mantInt : Integer
    mantInt = applyWhen overflow (`div` 10) rounded

    expFinal : Integer
    expFinal = applyWhen overflow (+ 1) (snd decomp)

||| Remove trailing zeros after the decimal point, keeping at least one.
||| Handles scientific notation, i.e.`"1.0000e-07"` becomes `"1.0e-07"`
public export
trimTrailingZeros : String -> String
trimTrailingZeros s = case break (== sciSymbol) (unpack s) of
  (mant, expPart) => case break (== '.') mant of
    (_, []) => s
    (whole, _ :: frac) =>
      let trimmed : String
          trimmed = case reverse (dropWhile (== '0') (reverse frac)) of
                      [] => "0"
                      xs => pack xs
      in pack whole ++ "." ++ trimmed ++ pack expPart

--------------------------------------------------------------------------------
-- ScientificDisplay instances
--------------------------------------------------------------------------------

||| Render a value using `showDoubleScientific` after casting to `Double`.
||| Used by integer-like instances when the magnitude warrants sci notation.
showAsScientific : Cast a Double => a -> String
showAsScientific n = trimTrailingZeros $
  showDoubleScientific defaultScientificPrecision (cast n)

||| Format a Double for display: fixed notation for values in the range
||| `[scientificLowerMagnitude, scientificUpperMagnitude)`, scientific
||| notation outside that range, with redundant trailing zeros removed.
public export
ScientificDisplay Double where
  showSci d = trimTrailingZeros $ case needsScientific d of
    True => showDoubleScientific defaultScientificPrecision d
    False => showDoublePrecision  defaultScientificPrecision d

public export
ScientificDisplay Integer where
  showSci n = case cast (abs n) < sciUpperM of
    True => show n -- builtin `Show` never uses scientific notation
    False => showAsScientific n

public export
ScientificDisplay Nat where
  showSci n = case cast n < sciUpperM of
    True => show n -- builtin `Show` never uses scientific notation
    False => showAsScientific n
