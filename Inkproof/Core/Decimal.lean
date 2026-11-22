/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

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

end Inkproof.Core.Decimal
