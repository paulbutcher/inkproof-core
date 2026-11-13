/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.FloatValue
import Inkproof.Core.Internal.FloatModel

namespace Inkproof.Core

open Float.Model Float.Model.UnpackedFloat

/-- The value of an unpacked float, `none` for NaN and the infinities. -/
def unpackedValue : UnpackedFloat → Option Rat
  | .notANumber | .infinity _ => none
  | .zero _ => some 0
  | .finite s m e _ => some (match s with | .positive => scaleTwoPow m e | .negative => -scaleTwoPow m e)

open Internal.FloatModel in
/-- `Float.toRat` is the value of the unpacked float of Lean's model. -/
theorem Float.toRat_eq_value (x : Float) : Float.toRat x = unpackedValue x.toModel.unpack := by
  have hE : ((x.toBits >>> 52) &&& 0x7ff).toNat = x.toBits.toNat / 2 ^ 52 % 2 ^ 11 := by
    simp only [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 11
  have hM : (x.toBits &&& 0xfffffffffffff).toNat = x.toBits.toNat % 2 ^ 52 := by
    simp only [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 52
  have hS : x.toBits >>> 63 = 0 ↔ x.toBits.toNat < 2 ^ 63 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    simp
  show _ = unpackedValue (UnpackedFloat.unpack Format.binary64 x.toBits.toBitVec)
  refine unpack_cases x.toBits.toBitVec (fun u => Float.toRat x = unpackedValue u) ?_ ?_ ?_ ?_ ?_ <;>
    intros <;> simp only [Float.toRat, unpackedValue, sgn, hE, hM, hS] <;>
    simp_all [UInt64.toNat_toBitVec] <;>
    (by_cases hh : x.toBits.toNat < 2 ^ 63 <;> simp [hh, scaleTwoPow_zero])

end Inkproof.Core
