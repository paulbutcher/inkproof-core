/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.OrdFloat

namespace Inkproof.Core

universe u v

/-- A monotone map from the x-domain to pixel columns `0` to `columns - 1`. Monotonicity is what
lets a column's points be contiguous in a sorted series. -/
structure Binning (α : Type u) [LE α] where
  columns : Nat
  col : α → Nat
  col_lt : ∀ x, col x < columns
  monotone : ∀ {x y}, x ≤ y → col x ≤ col y

/-- A fixed-point number with `scale` decimal places, held as the integer `raw`, so its value is
`raw / 10 ^ scale`. Comparison is exact. -/
structure Fixed (scale : Nat) where
  raw : Int
  deriving DecidableEq, Repr

namespace Fixed

instance {s : Nat} : LE (Fixed s) := ⟨fun a b => a.raw ≤ b.raw⟩

instance {s : Nat} : DecidableLE (Fixed s) := fun a b => inferInstanceAs (Decidable (a.raw ≤ b.raw))

instance {s : Nat} : Std.IsLinearOrder (Fixed s) where
  le_refl a := Int.le_refl a.raw
  le_trans _ _ _ := Int.le_trans
  le_antisymm a b hab hba := by
    cases a; cases b; exact congrArg Fixed.mk (Int.le_antisymm hab hba)
  le_total a b := Int.le_total a.raw b.raw

end Fixed

namespace Binning

variable {α : Type u} {γ : Type v} [LE α] [LE γ]

/-- Bins `α` by first mapping into `γ` with a monotone `f`. -/
def comap (f : α → γ) (hf : ∀ {x y}, x ≤ y → f x ≤ f y) (b : Binning γ) : Binning α where
  columns := b.columns
  col x := b.col (f x)
  col_lt x := b.col_lt (f x)
  monotone h := b.monotone (hf h)

/-- `width` equal columns across `[x₀, x₁)` in exact integer arithmetic: below `x₀` is column `0`,
and `x₁` and above is the last column. -/
def ofInt (x₀ x₁ : Int) (width : Nat) (hw : 0 < width) : Binning Int where
  columns := width
  col x := min (width - 1) ((x - x₀).toNat * width / (x₁ - x₀).toNat)
  col_lt x := by omega
  monotone {x y} h := by
    have h1 : (x - x₀).toNat ≤ (y - x₀).toNat := by omega
    have := Nat.div_le_div_right (c := (x₁ - x₀).toNat) (Nat.mul_le_mul_right width h1)
    omega

/-- As `ofInt`, for natural numbers such as integer timestamps. -/
def ofNat (x₀ x₁ : Nat) (width : Nat) (hw : 0 < width) : Binning Nat :=
  comap (fun n : Nat => (n : Int)) (fun h => Int.ofNat_le.mpr h) (ofInt x₀ x₁ width hw)

/-- As `ofInt`, for fixed-point numbers, with the bounds given as raw integers. -/
def ofFixed {s : Nat} (x₀ x₁ : Int) (width : Nat) (hw : 0 < width) : Binning (Fixed s) :=
  comap Fixed.raw (fun h => h) (ofInt x₀ x₁ width hw)

end Binning

namespace Binning

variable {α : Type u} [LE α]

/-- Column `i` starts at `breaks[i - 1]`: a point's column is the number of breaks at or below it,
so the first column is everything below `breaks[0]`. Needs no arithmetic on `α`, so it bins
`OrdFloat` x-values with breaks chosen by the caller. -/
def ofBreaks [DecidableLE α] [Std.IsPreorder α] (breaks : Array α) : Binning α where
  columns := breaks.size + 1
  col x := (breaks.toList.filter fun b => decide (b ≤ x)).length
  col_lt x := by
    have := List.length_filter_le (fun b => decide (b ≤ x)) breaks.toList
    simp only [Array.length_toList] at this
    omega
  monotone {x y} h := by
    induction breaks.toList with
    | nil => simp
    | cons b l ih =>
      simp only [List.filter_cons]
      by_cases hx : b ≤ x
      · have hy : b ≤ y := Std.IsPreorder.le_trans _ _ _ hx h
        simp [hx, hy, ih]
      · by_cases hy : b ≤ y <;> simp [hx, hy] <;> omega

end Binning

end Inkproof.Core
