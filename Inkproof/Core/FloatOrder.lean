/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.FloatValue
import Inkproof.Core.Internal.FloatModel

/-! `Float`'s `≤` is a linear order on the floats that are neither NaN nor `-0.0`, proved from
Lean's logical model of `Float`. Each comparison is reduced to one on an integer key read from the
bits: the magnitude bits, negated when the sign bit is set. -/

namespace Inkproof.Core

open Float.Model Float.Model.UnpackedFloat Internal.FloatModel

/-- The bits of `-0.0`, which compares equal to `0.0` but is a different value. -/
def negZeroBits : UInt64 := 0x8000000000000000

/-- A float that is not NaN and not `-0.0`: the floats on which comparison is a linear order. -/
def Float.IsOrdered (x : Float) : Prop := x.isNaN = false ∧ x.toBits ≠ negZeroBits

private theorem compare_le {u v : UnpackedFloat} {i j : Int} (hu : Canon u) (hv : Canon v)
    (hi : ukey u = some i) (hj : ukey v = some j) :
    ((u.compare v).any (·.isLE) = true ↔ i ≤ j) := by
  rcases u with (_|_) | _ | (_|_) | ⟨(_|_), m, e, hm⟩ <;>
  rcases v with (_|_) | _ | (_|_) | ⟨(_|_), m', e', hm'⟩ <;>
  simp only [ukey, Canon, Option.some.injEq, reduceCtorEq] at hi hj hu hv <;>
  subst hi hj <;>
  first
  | (by_cases h1 : e < e' <;> by_cases h2 : e = e' <;> by_cases h3 : m < m' <;> by_cases h4 : m = m' <;>
      simp [UnpackedFloat.compare, Sign.apply, Ordering.then, Ordering.isLE, Ordering.swap, compare,
        compareOfLessAndEq, h1, h2, h3, h4] <;> omega)
  | (simp [UnpackedFloat.compare, Sign.apply, Ordering.isLE, compare] <;> omega)

private theorem le_iff_key {x y : Float} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x ≤ y ↔ K x.toBits.toNat ≤ K y.toBits.toNat := by
  have key : ∀ z : Float, z.isNaN = false →
      Canon z.toModel.unpack ∧ ukey z.toModel.unpack = some (K z.toBits.toNat) := by
    intro z hz
    rcases unpack_key z.toBits.toBitVec with h | h
    · have h' : UnpackedFloat.unpack Format.binary64 z.toModel.toBits.toBitVec = .notANumber := h
      simp only [Float.isNaN, Float.Model.isNaN, Float.Model.unpack, h'] at hz
      cases hz
    · exact h
  obtain ⟨cx, kx⟩ := key x hx
  obtain ⟨cy, ky⟩ := key y hy
  exact compare_le cx cy kx ky

/-- `≤` is a linear order on floats that are neither NaN nor `-0.0`. -/
theorem float_le_linear :
    (∀ x : Float, Float.IsOrdered x → x ≤ x) ∧
    (∀ x y z : Float, Float.IsOrdered x → Float.IsOrdered y → Float.IsOrdered z →
      x ≤ y → y ≤ z → x ≤ z) ∧
    (∀ x y : Float, Float.IsOrdered x → Float.IsOrdered y → x ≤ y → y ≤ x → x = y) ∧
    (∀ x y : Float, Float.IsOrdered x → Float.IsOrdered y → x ≤ y ∨ y ≤ x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [le_iff_key hx.1 hx.1]
    exact Int.le_refl _
  · intro x y z hx hy hz hxy hyz
    rw [le_iff_key hx.1 hy.1] at hxy
    rw [le_iff_key hy.1 hz.1] at hyz
    rw [le_iff_key hx.1 hz.1]
    exact Int.le_trans hxy hyz
  · intro x y hx hy hxy hyx
    rw [le_iff_key hx.1 hy.1] at hxy
    rw [le_iff_key hy.1 hx.1] at hyx
    apply toBits_injective
    have hnx := hx.2
    have hny := hy.2
    have bx := x.toBits.toNat_lt
    have by' := y.toBits.toNat_lt
    simp only [negZeroBits, ne_eq, ← UInt64.toNat_inj, UInt64.toNat_ofNat] at hnx hny
    simp only [K] at hxy hyx
    rw [← UInt64.toNat_inj]
    split at hxy <;> split at hyx <;> omega
  · intro x y hx hy
    simp only [le_iff_key hx.1 hy.1, le_iff_key hy.1 hx.1]
    exact Int.le_total _ _

end Inkproof.Core
