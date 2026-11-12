/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Core

/-- `m * 2 ^ e` as a rational. -/
def scaleTwoPow (m : Nat) (e : Int) : Rat :=
  if 0 ≤ e then ((m * 2 ^ e.toNat : Nat) : Rat) else (m : Rat) / ((2 ^ (-e).toNat : Nat) : Rat)

theorem scaleTwoPow_of_nonneg (m : Nat) {e : Int} (h : 0 ≤ e) :
    scaleTwoPow m e = (m : Rat) * ((2 ^ e.toNat : Nat) : Rat) := by
  simp [scaleTwoPow, h]

theorem scaleTwoPow_of_neg (m : Nat) {e : Int} (h : e < 0) :
    scaleTwoPow m e = (m : Rat) / ((2 ^ (-e).toNat : Nat) : Rat) := by
  simp [scaleTwoPow, Int.not_le.mpr h]

/-- The exact value of a finite binary64 float, read from its bits; `none` for NaN and the
infinities. Both zeros give `0`.

No theorem states what this computes: `Float.toBits` is opaque to the kernel, so the bit arithmetic
cannot be unfolded, and the tests check it against the platform's floats instead. -/
def Float.toRat (x : Float) : Option Rat :=
  let b := x.toBits
  let e := ((b >>> 52) &&& 0x7ff).toNat
  let m := (b &&& 0xfffffffffffff).toNat
  if e = 0x7ff then none
  else
    let mag := if e = 0 then scaleTwoPow m (-1074) else scaleTwoPow (2 ^ 52 + m) (e - 1075)
    some (if b >>> 63 = 0 then mag else -mag)

/-- `x` is neither NaN nor infinite. -/
def Float.IsFinite (x : Float) : Prop := (Float.toRat x).isSome

/-- The absolute value of a rational. -/
def ratAbs (r : Rat) : Rat := if r < 0 then -r else r

theorem ratAbs_of_nonneg {r : Rat} (h : 0 ≤ r) : ratAbs r = r := by
  simp [ratAbs, Rat.not_lt.mpr h]

theorem ratAbs_of_neg {r : Rat} (h : r < 0) : ratAbs r = -r := by
  simp [ratAbs, h]

/-- The largest finite binary64 value, `(2 ^ 53 - 1) * 2 ^ 971`. -/
def maxFloat : Rat := scaleTwoPow (2 ^ 53 - 1) 971

/-- The smallest positive normal binary64 value, `2 ^ -1022`. -/
def minNormalFloat : Rat := scaleTwoPow 1 (-1022)

/-- An exact result that is zero, or in the normal range: no overflow, no subnormal rounding. -/
def NormalRange (r : Rat) : Prop := r = 0 ∨ (minNormalFloat ≤ ratAbs r ∧ ratAbs r ≤ maxFloat)

instance (r : Rat) : Decidable (NormalRange r) := by unfold NormalRange; infer_instance

/-- `z` is finite and within a relative error of `2 ^ -53`, half an ulp, of `r`. -/
def Float.Approximates (z : Float) (r : Rat) : Prop :=
  ∃ q, Float.toRat z = some q ∧ ratAbs (q - r) ≤ ratAbs r / scaleTwoPow 1 53

end Inkproof.Core
