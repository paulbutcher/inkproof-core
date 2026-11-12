/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.FloatValue

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

/-- FP-3: the rounding model of Lean's `Float`, which is IEEE 754 binary64 with round to nearest even.
Three parts, all about the exact value `Float.toRat` of finite floats:
- `≤` agrees with `≤` on exact values.
- A literal `n`, for `n < 2 ^ 53`, is exactly `n`.
- Where the exact result of `+`, `-`, `*` or `/` (`y ≠ 0`) of two finite floats is zero or in the
  normal range, the computed float is finite and within half an ulp of it, which is a relative
  error of at most `2 ^ -53`.

Lean's floats are opaque to proofs, so this is assumed, not proved. It is the defining property of
IEEE 754 round to nearest, which every platform Lean and Lasm target implements for binary64. It
says nothing of binary32, whose relative error is `2 ^ -24`. The test subproject checks it on the
platforms it runs on. -/
axiom float_rounding_model :
    (∀ x y : Float, Float.IsFinite x → Float.IsFinite y →
      (x ≤ y ↔ ∃ a b, Float.toRat x = some a ∧ Float.toRat y = some b ∧ a ≤ b)) ∧
    (∀ n : Nat, n < 2 ^ 53 → Float.toRat (OfNat.ofNat n) = some (n : Rat)) ∧
    (∀ (x y : Float) (a b : Rat), Float.toRat x = some a → Float.toRat y = some b →
      (NormalRange (a + b) → Float.Approximates (x + y) (a + b)) ∧
      (NormalRange (a - b) → Float.Approximates (x - y) (a - b)) ∧
      (NormalRange (a * b) → Float.Approximates (x * y) (a * b)) ∧
      (b ≠ 0 → NormalRange (a / b) → Float.Approximates (x / y) (a / b)))

namespace Float

theorem toRat_mono {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (h : x ≤ y) : a ≤ b := by
  obtain ⟨a', b', ha, hb, hab⟩ :=
    (float_rounding_model.1 x y (by simp [IsFinite, hx]) (by simp [IsFinite, hy])).1 h
  simp_all

theorem le_of_toRat_le {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (h : a ≤ b) : x ≤ y :=
  (float_rounding_model.1 x y (by simp [IsFinite, hx]) (by simp [IsFinite, hy])).2
    ⟨a, b, hx, hy, h⟩

theorem toRat_ofNat {n : Nat} (h : n < 2 ^ 53) : Float.toRat (OfNat.ofNat n : Float) = some (n : Rat) :=
  float_rounding_model.2.1 n h

theorem approximates_add {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (h : NormalRange (a + b)) : Float.Approximates (x + y) (a + b) :=
  (float_rounding_model.2.2 x y a b hx hy).1 h

theorem approximates_sub {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (h : NormalRange (a - b)) : Float.Approximates (x - y) (a - b) :=
  (float_rounding_model.2.2 x y a b hx hy).2.1 h

theorem approximates_mul {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (h : NormalRange (a * b)) : Float.Approximates (x * y) (a * b) :=
  (float_rounding_model.2.2 x y a b hx hy).2.2.1 h

theorem approximates_div {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (hb : b ≠ 0) (h : NormalRange (a / b)) : Float.Approximates (x / y) (a / b) :=
  (float_rounding_model.2.2 x y a b hx hy).2.2.2 hb h

end Float

end Inkproof.Core
