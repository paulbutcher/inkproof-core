/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.FloatOrder
import Inkproof.Core.Internal.FloatModel

namespace Inkproof.Core

/-- A float that is never NaN, with `-0.0` replaced by `0.0`, so that comparison is a linear order
(FP-2) and floats can be x-values or aggregate values. -/
structure OrdFloat where
  val : Float
  ordered : Float.IsOrdered val

namespace OrdFloat

instance : LE OrdFloat := ⟨fun a b => a.val ≤ b.val⟩

instance : DecidableLE OrdFloat := fun a b => Float.decLe a.val b.val

theorem ext {a b : OrdFloat} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

/-- From `float_le_linear`, which is proved from Lean's model of `Float`. -/
instance : Std.IsLinearOrder OrdFloat where
  le_refl a := float_le_linear.1 a.val a.ordered
  le_trans a b c := float_le_linear.2.1 a.val b.val c.val a.ordered b.ordered c.ordered
  le_antisymm a b hab hba := ext (float_le_linear.2.2.1 a.val b.val a.ordered b.ordered hab hba)
  le_total a b := float_le_linear.2.2.2 a.val b.val a.ordered b.ordered

/-- `x` as an ordered float, or `none` if `x` is NaN; `-0.0` becomes `0.0`. -/
def ofFloat? (x : Float) : Option OrdFloat :=
  let y := if x == 0 then 0 else x
  if h : y.isNaN = false ∧ y.toBits ≠ negZeroBits then some ⟨y, h⟩ else none

theorem ofFloat?_eq_none_iff (x : Float) : ofFloat? x = none ↔ x.isNaN = true := by
  unfold ofFloat?
  by_cases hx : x.isNaN = true
  · have hb := Internal.FloatModel.beq_zero_of_isNaN hx
    simp [hb, hx]
  · have hx' : x.isNaN = false := by simpa using hx
    suffices h : (if x == 0 then (0 : Float) else x).isNaN = false ∧
        (if x == 0 then (0 : Float) else x).toBits ≠ negZeroBits by simp [h, hx]
    split
    · exact ⟨by decide, by decide⟩
    · rename_i h
      refine ⟨hx', fun hb => h ?_⟩
      have : x = Float.ofBits negZeroBits :=
        Internal.FloatModel.toBits_injective (by rw [hb]; rfl)
      subst this
      decide

instance : ToString OrdFloat := ⟨fun a => toString a.val⟩

instance : Repr OrdFloat := ⟨fun a p => reprPrec a.val p⟩

end OrdFloat

end Inkproof.Core
