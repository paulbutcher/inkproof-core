/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Float

namespace Inkproof.Core.Decimal

/-- The number written by decimal digit characters, most significant first. -/
def digitsValue (cs : List Char) : Nat :=
  cs.foldl (fun a c => 10 * a + (c.toNat - 48)) 0

/-- `m / 10 ^ p` as decimal characters: the whole digits, then if `p` is not zero a `'.'` and `p` fractional digits. The digits are zero-padded to at least `p + 1` places so that a whole digit exists. -/
def formatNat (p m : Nat) : List Char :=
  let cs := List.leftpad (p + 1) '0' (Nat.toDigits 10 m)
  cs.take (cs.length - p) ++ (if p = 0 then [] else '.' :: cs.drop (cs.length - p))

/-- `n / 10 ^ p` as decimal characters, with a leading `'-'` when `n` is negative. -/
def formatDecimal (p : Nat) (n : Int) : List Char :=
  (if n < 0 then ['-'] else []) ++ formatNat p n.natAbs

/-- Splits at the first `c`, giving what follows it if there is one. -/
def splitAtChar (c : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | x :: r =>
    if x = c then ([], some r)
    else
      let (a, b) := splitAtChar c r
      (x :: a, b)

/-- Reads characters written by `formatDecimal` back as the numerator `n` and the number of fractional digits `p`, or `none` if they are not of that form. -/
def parseDecimal (cs : List Char) : Option (Int × Nat) :=
  let (neg, rest) := match cs with
    | c :: r => if c = '-' then (true, r) else (false, cs)
    | [] => (false, [])
  let (whole, frac) := splitAtChar '.' rest
  let frac := frac.getD []
  if !whole.isEmpty && (whole ++ frac).all Char.isDigit then
    let v : Int := digitsValue (whole ++ frac)
    some (if neg then -v else v, frac.length)
  else none

/-- Drops the trailing zeros of a fractional part. -/
def trimFrac (f : List Char) : List Char := (f.reverse.dropWhile (· = '0')).reverse

/-- Removes trailing zeros after the point, and the point itself if no fractional digits remain; text without a point is unchanged. -/
def trimZeros (cs : List Char) : List Char :=
  match splitAtChar '.' cs with
  | (_, none) => cs
  | (w, some f) =>
    let t := trimFrac f
    if t.isEmpty then w else w ++ '.' :: t

/-- `q` scaled by `10 ^ p` and rounded to the nearest integer, halves upwards, so that `formatDecimal p (roundScaled p q)` writes `q` to `p` decimals. -/
def roundScaled (p : Nat) (q : Rat) : Int := (q * (10 ^ p : Nat) + 1 / 2).floor

/-- `10 ^ k` for any integer `k`, as `Rat`'s own integer power; `pow10_add` and `pow10_nat` state it. -/
def pow10 (k : Int) : Rat := (10 : Rat) ^ k

/-- The number of decimal digits of `n`, less one; zero for zero. -/
def log10 (n : Nat) : Nat := if n < 10 then 0 else log10 (n / 10) + 1
decreasing_by omega

/-- The `e` with `10 ^ e ≤ |q| < 10 ^ (e + 1)`, for `q` not zero. Comparing the digit counts of numerator and denominator is within one of it; `magnitude_spec` states it. -/
def magnitude (q : Rat) : Int :=
  let e : Int := (log10 q.num.natAbs : Int) - log10 q.den
  if pow10 e ≤ q.abs then e else e - 1

/-- `q` rounded to the nearest multiple of `10 ^ (magnitude q + 1 - digits)`, halves away from zero, which keeps `digits` significant digits; zero is unchanged. `roundSignificantRat_close` bounds the error by half a unit of the last digit kept, and `roundSignificantRat_pow10` shows powers of ten are fixed. -/
def roundSignificantRat (digits : Nat) (q : Rat) : Rat :=
  if q = 0 then 0
  else
    let scale := pow10 ((digits : Int) - 1 - magnitude q)
    let m : Int := roundScaled 0 (q.abs * scale)
    (if q < 0 then -1 else 1) * m / scale

/-- `x` rounded to `digits` significant digits, by rounding its exact value and converting the decimal result to the nearest float. Zero, NaN and the infinities are unchanged (`roundSignificant_zero`, `roundSignificant_nonFinite`). The value of the result is not proved: `Float.ofScientific` is opaque to the float model, which has no statement of its rounding, so tests check the result instead. -/
def roundSignificant (digits : Nat) (x : Float) : Float :=
  match Inkproof.Float.Float.toRat x with
  | none => x
  | some q =>
    if q = 0 then x
    else
      let r := roundSignificantRat digits q
      let e : Int := (digits : Int) - 1 - magnitude q
      let m := (r.abs * pow10 e).num.natAbs
      let y := Float.ofScientific m (decide (e ≥ 0)) e.natAbs
      if q < 0 then -y else y

end Inkproof.Core.Decimal
