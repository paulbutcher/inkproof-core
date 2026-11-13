/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! Lean's logical model of `Float` unpacked into the fields of the bits: `unpack_cases` splits an
unpacked float by those fields, and `unpack_key` gives each non-NaN float an integer key whose order
is that of the floats. -/

namespace Inkproof.Core

open Float.Model Float.Model.UnpackedFloat

namespace Internal.FloatModel

/-- The sign of the float whose bits are `n`. -/
def sgn (n : Nat) : Sign := if n < 2 ^ 63 then .positive else .negative

theorem finite_exp {P : UnpackedFloat → Prop} {s m} {e e' : Int} {h h'} (he : e = e')
    (hp : P (.finite s m e h)) : P (.finite s m e' h') := by
  subst he; exact hp

theorem unpack_cases (b : BitVec 64) (P : UnpackedFloat → Prop)
    (hnan : b.toNat / 2 ^ 52 % 2 ^ 11 = 2047 → b.toNat % 2 ^ 52 ≠ 0 → P .notANumber)
    (hinf : b.toNat / 2 ^ 52 % 2 ^ 11 = 2047 → b.toNat % 2 ^ 52 = 0 → P (.infinity (sgn b.toNat)))
    (hzero : b.toNat / 2 ^ 52 % 2 ^ 11 = 0 → b.toNat % 2 ^ 52 = 0 → P (.zero (sgn b.toNat)))
    (hsub : b.toNat / 2 ^ 52 % 2 ^ 11 = 0 → ∀ h : 0 < b.toNat % 2 ^ 52,
      P (.finite (sgn b.toNat) (b.toNat % 2 ^ 52) (-1074) h))
    (hnorm : b.toNat / 2 ^ 52 % 2 ^ 11 ≠ 2047 → b.toNat / 2 ^ 52 % 2 ^ 11 ≠ 0 →
      ∀ h : 0 < 2 ^ 52 + b.toNat % 2 ^ 52,
      P (.finite (sgn b.toNat) (2 ^ 52 + b.toNat % 2 ^ 52)
        ((b.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075) h)) :
    P (UnpackedFloat.unpack Format.binary64 b) := by
  unfold UnpackedFloat.unpack
  simp only [UnpackedFloat.unpackMantissa, UnpackedFloat.unpackExponent, UnpackedFloat.unpackSign]
  have hb := b.isLt
  have hE : (BitVec.extractLsb' 52 11 b).toNat = b.toNat / 2 ^ 52 % 2 ^ 11 := by
    simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hM : (BitVec.extractLsb' 0 52 b).toNat = b.toNat % 2 ^ 52 := by
    simp [BitVec.extractLsb'_toNat]
  have hS : (BitVec.extractLsb' (52 + 11) 1 b).toNat = b.toNat / 2 ^ 63 := by
    simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  have hA : (1#1 ++ BitVec.extractLsb' 0 52 b).toNat = 2 ^ 52 + b.toNat % 2 ^ 52 := by
    rw [BitVec.toNat_append, hM]
    simp
    have := Nat.two_pow_add_eq_or_of_lt (i := 52) (Nat.mod_lt b.toNat (by decide)) 1
    simp only [Nat.mul_one] at this
    exact this.symm
  have hE1 : BitVec.extractLsb' 52 11 b = -1#11 ↔ b.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := by
    constructor
    · intro h; have := congrArg BitVec.toNat h; rw [hE] at this; simpa using this
    · intro h; apply BitVec.eq_of_toNat_eq; rw [hE, h]; simp
  have hE0 : BitVec.extractLsb' 52 11 b = 0#11 ↔ b.toNat / 2 ^ 52 % 2 ^ 11 = 0 := by
    constructor
    · intro h; have := congrArg BitVec.toNat h; rw [hE] at this; simpa using this
    · intro h; apply BitVec.eq_of_toNat_eq; rw [hE, h]; simp
  have hM0 : BitVec.extractLsb' 0 52 b = 0#52 ↔ b.toNat % 2 ^ 52 = 0 := by
    constructor
    · intro h; have := congrArg BitVec.toNat h; rw [hM] at this; simpa using this
    · intro h; apply BitVec.eq_of_toNat_eq; rw [hM, h]; simp
  have hS0 : BitVec.extractLsb' (52 + 11) 1 b = 0#1 ↔ b.toNat < 2 ^ 63 := by
    constructor
    · intro h; have := congrArg BitVec.toNat h; rw [hS] at this; simp at this; omega
    · intro h; apply BitVec.eq_of_toNat_eq; rw [hS]; simp; omega
  simp only [Sign.ofBitVec, hE1, hE0, hM0, hS0, hE, hM, hA, Format.exponentBias]
  have hsgn : (if b.toNat < 2 ^ 63 then Sign.positive else Sign.negative) = sgn b.toNat := rfl
  rw [hsgn]
  split
  · split
    · exact hinf ‹_› ‹_›
    · exact hnan ‹_› ‹_›
  · split
    · split
      · exact hzero ‹_› ‹_›
      · exact finite_exp (by omega) (hsub ‹_› (Nat.pos_of_ne_zero ‹_›))
    · exact finite_exp (by omega) (hnorm ‹_› ‹_› (by omega))

def ukey : UnpackedFloat → Option Int
  | .notANumber => none
  | .infinity s => some (s.apply (2047 * 2 ^ 52))
  | .zero _ => some 0
  | .finite s m e _ => some (s.apply (((e + 1074).toNat * 2 ^ 52 + m : Nat)))

def Canon : UnpackedFloat → Prop
  | .finite _ m e _ => -1074 ≤ e ∧ e ≤ 971 ∧ m < 2 ^ 53 ∧ (e = -1074 ∨ 2 ^ 52 ≤ m)
  | _ => True

def K (n : Nat) : Int := if n < 2 ^ 63 then (n : Int) else -((n - 2 ^ 63 : Nat) : Int)

/-- Each unpacked float is NaN, or in canonical form with the key of its bits. -/
theorem unpack_key (b : BitVec 64) :
    UnpackedFloat.unpack Format.binary64 b = .notANumber ∨
    (Canon (UnpackedFloat.unpack Format.binary64 b) ∧
      ukey (UnpackedFloat.unpack Format.binary64 b) = some (K b.toNat)) := by
  have hb := b.isLt
  refine unpack_cases b (fun u => u = .notANumber ∨ (Canon u ∧ ukey u = some (K b.toNat)))
    ?_ ?_ ?_ ?_ ?_ <;> intros <;>
  first
  | exact Or.inl rfl
  | (right; simp [sgn, Canon, ukey, K, Sign.apply] <;> split <;> simp_all <;> omega)

theorem toBits_injective {x y : Float} (h : x.toBits = y.toBits) : x = y := by
  obtain ⟨⟨a, va⟩⟩ := x
  obtain ⟨⟨b, vb⟩⟩ := y
  simp only [Float.toBits] at h
  cases h
  rfl

theorem beq_zero_of_isNaN {x : Float} (h : x.isNaN = true) : (x == 0) = false := by
  have e : (x == 0) = x.toModel.unpack.beq (0 : Float).toModel.unpack := rfl
  have h' : x.toModel.unpack.isNaN = true := by simpa [Float.isNaN, Float.Model.isNaN] using h
  rw [e]
  cases hu : x.toModel.unpack <;> simp_all [Float.Model.UnpackedFloat.isNaN]
  decide

end Internal.FloatModel

end Inkproof.Core
