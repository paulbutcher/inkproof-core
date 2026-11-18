/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Core.Decimal

/-- The low `w` decimal digits of `m`, least significant first. -/
def lsDigits : Nat → Nat → List Nat
  | _, 0 => []
  | m, w + 1 => m % 10 :: lsDigits (m / 10) w

/-- The number of decimal digits needed to write `m`, at least one. -/
def digitCount (m : Nat) : Nat :=
  if m < 10 then 1 else digitCount (m / 10) + 1
termination_by m
decreasing_by omega

/-- The number written by digits given least significant first. -/
def lsValue (ds : List Nat) : Nat := ds.foldr (fun d a => d + 10 * a) 0

/-- The number written by decimal digit characters, most significant first. -/
def digitsValue (cs : List Char) : Nat :=
  cs.foldl (fun a c => 10 * a + (c.toNat - 48)) 0

/-- The digits of `m` least significant first, padded with zeros to at least `p + 1` places so that `p` fractional digits and one whole digit exist. -/
def scaledDigits (p m : Nat) : List Nat := lsDigits m (max (digitCount m) (p + 1))

/-- `m / 10 ^ p` as decimal characters: the whole digits, then if `p` is not zero a `'.'` and `p` fractional digits. -/
def formatNat (p m : Nat) : List Char :=
  let ds := scaledDigits p m
  (ds.drop p).reverse.map Nat.digitChar ++
    (if p = 0 then [] else '.' :: (ds.take p).reverse.map Nat.digitChar)

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
