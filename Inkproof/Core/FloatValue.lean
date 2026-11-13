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

theorem scaleTwoPow_zero (e : Int) : scaleTwoPow 0 e = 0 := by
  unfold scaleTwoPow
  split
  · simp
  · rw [Rat.div_def]; simp

/-- The exact value of a finite binary64 float, read from its bits; `none` for NaN and the
infinities. Both zeros give `0`. `Float.toRat_eq_value` states that this is the value of the float in
Lean's model. -/
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

/-- `|x| ≤ y` exactly when `-y ≤ x ≤ y`. -/
theorem rat_abs_le_iff {x y : Rat} : x.abs ≤ y ↔ -y ≤ x ∧ x ≤ y := by
  unfold Rat.abs; grind

/-- The triangle inequality for `Rat.abs`. -/
theorem rat_abs_add_le (x y : Rat) : (x + y).abs ≤ x.abs + y.abs := by
  unfold Rat.abs; grind

/-- `Rat.abs` of a product is the product of the absolute values. -/
theorem rat_abs_mul (x y : Rat) : (x * y).abs = x.abs * y.abs := by
  unfold Rat.abs
  have h : ∀ a b : Rat, 0 ≤ a → 0 ≤ b → 0 ≤ a * b := fun _ _ => Rat.mul_nonneg
  have := h x y
  have := h (-x) y
  have := h x (-y)
  have := h (-x) (-y)
  grind

/-- The largest finite binary64 value, `(2 ^ 53 - 1) * 2 ^ 971`. -/
def maxFloat : Rat := scaleTwoPow (2 ^ 53 - 1) 971

/-- The smallest positive normal binary64 value, `2 ^ -1022`. -/
def minNormalFloat : Rat := scaleTwoPow 1 (-1022)

/-- An exact result that is zero, or in the normal range: no overflow, no subnormal rounding. -/
def NormalRange (r : Rat) : Prop := r = 0 ∨ (minNormalFloat ≤ r.abs ∧ r.abs ≤ maxFloat)

instance (r : Rat) : Decidable (NormalRange r) := by unfold NormalRange; infer_instance

/-- `z` is finite and within a relative error of `2 ^ -53`, half an ulp, of `r`. -/
def Float.Approximates (z : Float) (r : Rat) : Prop :=
  ∃ q, Float.toRat z = some q ∧ (q - r).abs ≤ r.abs / scaleTwoPow 1 53

/-- The relative form of `Float.Approximates`: the float is `r * (1 + δ)` for some `|δ| ≤ 2 ^ -53`. -/
theorem Float.Approximates.rel {z : Float} {r : Rat} (h : Float.Approximates z r) :
    ∃ q δ, Float.toRat z = some q ∧ δ.abs ≤ 1 / scaleTwoPow 1 53 ∧ q = r * (1 + δ) := by
  obtain ⟨q, hq, hb⟩ := h
  by_cases hr : r = 0
  · subst hr
    have h0 : (q - 0).abs ≤ 0 := by simpa [Rat.div_def] using hb
    have hq0 : q = 0 := by unfold Rat.abs at h0; grind
    refine ⟨q, 0, hq, ?_, by rw [hq0]; simp⟩
    have : (0 : Rat).abs = 0 := Rat.abs_of_nonneg (Rat.le_refl)
    rw [this]
    have hu : (0 : Rat) < scaleTwoPow 1 53 := by decide
    simpa [Rat.div_def] using Rat.le_of_lt (Rat.inv_pos.mpr hu)
  · have hrr : r * r⁻¹ = 1 := Rat.mul_inv_cancel _ hr
    have hpos : 0 < r.abs := Rat.abs_pos_iff.mpr hr
    refine ⟨q, (q - r) * r⁻¹, hq, ?_, by grind⟩
    have hm : ((q - r) * r⁻¹).abs * r.abs = (q - r).abs := by
      rw [← rat_abs_mul, Rat.mul_assoc, Rat.inv_mul_cancel _ hr, Rat.mul_one]
    simp only [Rat.div_def] at *
    by_cases h : ((q - r) * r⁻¹).abs ≤ 1 * (scaleTwoPow 1 53)⁻¹
    · exact h
    · have := Rat.mul_lt_mul_of_pos_right (Rat.not_le.mp h) hpos
      rw [hm] at this
      grind

/-- Error composition: if `z` approximates `r` and `r` is within `e` of `s`, then the float is
within `e + (|s| + e) / 2 ^ 53` of `s`. -/
theorem Float.Approximates.error_step {z : Float} {r s e : Rat} (h : Float.Approximates z r)
    (hs : (r - s).abs ≤ e) :
    ∃ q, Float.toRat z = some q ∧ (q - s).abs ≤ e + (s.abs + e) / scaleTwoPow 1 53 := by
  obtain ⟨q, hq, hb⟩ := h
  refine ⟨q, hq, ?_⟩
  have hu : (0 : Rat) < scaleTwoPow 1 53 := by decide
  have hi : 0 ≤ (scaleTwoPow 1 53)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hu)
  have h2 : r.abs ≤ s.abs + e := by unfold Rat.abs at *; grind
  have h3 := Rat.mul_le_mul_of_nonneg_left h2 hi
  have h4 := rat_abs_add_le (q - r) (r - s)
  simp only [Rat.div_def] at *
  have : q - s = (q - r) + (r - s) := by grind
  rw [this, Rat.mul_comm] at *
  grind

end Inkproof.Core
