/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Axioms

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

/-- Rests on the FP-2 axiom `float_le_linear`, and on nothing else beyond Lean's own axioms. -/
instance : Std.IsLinearOrder OrdFloat where
  le_refl a := float_le_linear.1 a.val a.ordered
  le_trans a b c := float_le_linear.2.1 a.val b.val c.val a.ordered b.ordered c.ordered
  le_antisymm a b hab hba := ext (float_le_linear.2.2.1 a.val b.val a.ordered b.ordered hab hba)
  le_total a b := float_le_linear.2.2.2 a.val b.val a.ordered b.ordered

/-- `x` as an ordered float, or `none` if `x` is NaN; `-0.0` becomes `0.0`. That only NaN is
rejected cannot be proved, since floats are opaque to proofs; the test subproject checks it. -/
def ofFloat? (x : Float) : Option OrdFloat :=
  let y := if x == 0 then 0 else x
  if h : y.isNaN = false ∧ y.toBits ≠ negZeroBits then some ⟨y, h⟩ else none

instance : ToString OrdFloat := ⟨fun a => toString a.val⟩

instance : Repr OrdFloat := ⟨fun a p => reprPrec a.val p⟩

end OrdFloat

end Inkproof.Core
