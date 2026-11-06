/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! Every axiom the library adds to Lean's, and nothing else. A check in the test subproject fails
if a published theorem depends on an axiom that is not here or in Lean itself. -/

namespace Inkproof.Core

/-- The bits of `-0.0`, which compares equal to `0.0` but is a different value. -/
def negZeroBits : UInt64 := 0x8000000000000000

/-- A float that is not NaN and not `-0.0`: the floats on which comparison is a linear order. -/
def Float.IsOrdered (x : Float) : Prop := x.isNaN = false ∧ x.toBits ≠ negZeroBits

/-- FP-2: `Float`'s `≤` is a linear order on floats that are neither NaN nor `-0.0`. Lean's floats
are opaque to proofs, so this is assumed, not proved. IEEE 754 comparison satisfies it: it is a
total preorder on non-NaN values whose only distinct equal pair is `0.0` and `-0.0`. The test
subproject checks it on the platforms it runs on. -/
axiom float_le_linear :
    (∀ x : Float, Float.IsOrdered x → x ≤ x) ∧
    (∀ x y z : Float, Float.IsOrdered x → Float.IsOrdered y → Float.IsOrdered z →
      x ≤ y → y ≤ z → x ≤ z) ∧
    (∀ x y : Float, Float.IsOrdered x → Float.IsOrdered y → x ≤ y → y ≤ x → x = y) ∧
    (∀ x y : Float, Float.IsOrdered x → Float.IsOrdered y → x ≤ y ∨ y ≤ x)

end Inkproof.Core
