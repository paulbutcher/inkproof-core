/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Binning

/-! CORE-4 and FP-4: what each binning computes. Monotonicity in general is the field
`Binning.monotone`. -/

namespace Inkproof.Core

universe u v

namespace Binning

section
variable {α : Type u} {γ : Type v} [LE α] [LE γ]

theorem comap_col (f : α → γ) (hf : ∀ {x y}, x ≤ y → f x ≤ f y) (b : Binning γ) (x : α) :
    (comap f hf b).col x = b.col (f x) := rfl

theorem comap_columns (f : α → γ) (hf : ∀ {x y}, x ≤ y → f x ≤ f y) (b : Binning γ) :
    (comap f hf b).columns = b.columns := rfl

/-- Equal points land in equal columns. -/
theorem col_eq_of_le_of_le (b : Binning α) {x y : α} (h₁ : x ≤ y) (h₂ : y ≤ x) :
    b.col x = b.col y :=
  Nat.le_antisymm (b.monotone h₁) (b.monotone h₂)

end

theorem ofInt_columns (x₀ x₁ : Int) (w : Nat) (hw : 0 < w) : (ofInt x₀ x₁ w hw).columns = w := rfl

/-- Below the range is the first column. -/
theorem ofInt_col_of_le (x₀ x₁ : Int) (w : Nat) (hw : 0 < w) {x : Int} (h : x ≤ x₀) :
    (ofInt x₀ x₁ w hw).col x = 0 := by
  have : (x - x₀).toNat = 0 := by omega
  simp [ofInt, this]

/-- Inside the range, the column is the exact floor of `(x - x₀) * w / (x₁ - x₀)`. -/
theorem ofInt_col_of_lt (x₀ x₁ : Int) (w : Nat) (hw : 0 < w) {x : Int} (h₀ : x₀ ≤ x) (h₁ : x < x₁) :
    (ofInt x₀ x₁ w hw).col x = (x - x₀).toNat * w / (x₁ - x₀).toNat := by
  have hd : 0 < (x₁ - x₀).toNat := by omega
  have hlt : (x - x₀).toNat * w / (x₁ - x₀).toNat < w := by
    rw [Nat.div_lt_iff_lt_mul hd]
    rw [Nat.mul_comm w]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hw
  simp only [ofInt]
  omega

/-- At or past the end of the range is the last column. -/
theorem ofInt_col_of_ge (x₀ x₁ : Int) (w : Nat) (hw : 0 < w) (hx : x₀ < x₁) {x : Int}
    (h : x₁ ≤ x) : (ofInt x₀ x₁ w hw).col x = w - 1 := by
  have hd : 0 < (x₁ - x₀).toNat := by omega
  have hle : w ≤ (x - x₀).toNat * w / (x₁ - x₀).toNat := by
    have h1 : (x₁ - x₀).toNat ≤ (x - x₀).toNat := by omega
    have := Nat.div_le_div_right (c := (x₁ - x₀).toNat) (Nat.mul_le_mul_right w h1)
    rw [Nat.mul_div_cancel_left _ hd] at this
    exact this
  simp only [ofInt]
  omega

theorem ofNat_columns (x₀ x₁ w : Nat) (hw : 0 < w) : (ofNat x₀ x₁ w hw).columns = w := rfl

theorem ofNat_col_of_le (x₀ x₁ w : Nat) (hw : 0 < w) {x : Nat} (h : x ≤ x₀) :
    (ofNat x₀ x₁ w hw).col x = 0 :=
  ofInt_col_of_le _ _ w hw (x := (x : Int)) (by omega)

/-- Inside the range, the column is the exact floor of `(x - x₀) * w / (x₁ - x₀)`. -/
theorem ofNat_col_of_lt (x₀ x₁ w : Nat) (hw : 0 < w) {x : Nat} (h₀ : x₀ ≤ x) (h₁ : x < x₁) :
    (ofNat x₀ x₁ w hw).col x = (x - x₀) * w / (x₁ - x₀) := by
  have := ofInt_col_of_lt (x₀ : Int) x₁ w hw (x := x) (by omega) (by omega)
  have e1 : ((x : Int) - x₀).toNat = x - x₀ := by omega
  have e2 : ((x₁ : Int) - x₀).toNat = x₁ - x₀ := by omega
  rw [e1, e2] at this
  exact this

theorem ofNat_col_of_ge (x₀ x₁ w : Nat) (hw : 0 < w) (hx : x₀ < x₁) {x : Nat} (h : x₁ ≤ x) :
    (ofNat x₀ x₁ w hw).col x = w - 1 :=
  ofInt_col_of_ge _ _ w hw (by omega) (x := (x : Int)) (by omega)

theorem ofFixed_columns {s : Nat} (x₀ x₁ : Int) (w : Nat) (hw : 0 < w) :
    (ofFixed (s := s) x₀ x₁ w hw).columns = w := rfl

/-- A fixed-point value bins as its raw integer does, so binning is exact. -/
theorem ofFixed_col {s : Nat} (x₀ x₁ : Int) (w : Nat) (hw : 0 < w) (x : Fixed s) :
    (ofFixed x₀ x₁ w hw).col x = (ofInt x₀ x₁ w hw).col x.raw := rfl

theorem ofBreaks_columns {α : Type u} [LE α] [DecidableLE α] [Std.IsPreorder α] (breaks : Array α) :
    (ofBreaks breaks).columns = breaks.size + 1 := rfl

/-- A point's column is the number of breaks at or below it. -/
theorem ofBreaks_col {α : Type u} [LE α] [DecidableLE α] [Std.IsPreorder α] (breaks : Array α)
    (x : α) : (ofBreaks breaks).col x = breaks.countP fun b => decide (b ≤ x) := by
  rw [← Array.countP_toList, List.countP_eq_length_filter]
  rfl

end Binning

end Inkproof.Core
