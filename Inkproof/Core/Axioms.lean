/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.FloatValue

/-! Every axiom the library adds to Lean's, and nothing else. A check in the test subproject fails
if a published theorem depends on an axiom that is not here or in Lean itself. -/

namespace Inkproof.Core

/-- FP-3: the rounding model of Lean's `Float`, which is IEEE 754 binary64 with round to nearest even.
Three parts, all about the exact value `Float.toRat` of finite floats:
- `≤` agrees with `≤` on exact values.
- A literal `n`, for `n < 2 ^ 53`, is exactly `n`.
- Where the exact result of `+`, `-`, `*` or `/` (`y ≠ 0`) of two finite floats is zero or in the
  normal range, the computed float is finite and within half an ulp of it, which is a relative
  error of at most `2 ^ -53`.

Lean defines `Float` over a model of IEEE 754 binary64, but proves nothing about its rounding, so this
is assumed. The first two parts are provable from the model; the third needs the error theory of
round to nearest, which DESIGN.md assesses. What stays trusted is that Lean's compiled float
operations match the model. It says nothing of binary32, whose relative error is `2 ^ -24`. The test
subproject checks it against compiled code, natively and under Lasm. -/
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
