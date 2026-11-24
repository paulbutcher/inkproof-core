/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Decimal

namespace Inkproof.Core.Decimal

theorem digitsValue_toDigits (m : Nat) : digitsValue (Nat.toDigits 10 m) = m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rw [Nat.toDigits_eq_ite (by omega)]
    split
    · rename_i h
      simp [digitsValue, Nat.toNat_digitChar_sub_48_of_lt_ten h]
    · rename_i h
      have := ih (m / 10) (by omega)
      simp only [digitsValue, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.toNat_digitChar_sub_48_of_lt_ten (Nat.mod_lt m (by omega : 10 > 0))] at this ⊢
      rw [this]; omega

private theorem digitsValue_replicate_append (k : Nat) (cs : List Char) :
    digitsValue (List.replicate k '0' ++ cs) = digitsValue cs := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    simpa [digitsValue] using ih

private theorem isDigit_leftpad {n : Nat} {cs : List Char} (h : ∀ c ∈ cs, c.isDigit = true) :
    ∀ c ∈ List.leftpad n '0' cs, c.isDigit = true := by
  intro c hc
  simp only [List.leftpad, List.mem_append, List.mem_replicate] at hc
  rcases hc with ⟨_, rfl⟩ | hc
  · decide
  · exact h c hc

/-- The characters of `formatNat p m` are the whole digits, then if `p` is not zero a point and `p` fractional digits. The whole part is not empty, every other character is a digit, and the digits read as `m`. -/
theorem formatNat_spec (p m : Nat) : ∃ whole frac : List Char,
    formatNat p m = whole ++ (if p = 0 then [] else '.' :: frac) ∧ whole ≠ [] ∧ frac.length = p ∧
      (∀ c ∈ whole ++ frac, c.isDigit = true) ∧ digitsValue (whole ++ frac) = m := by
  generalize hcs : List.leftpad (p + 1) '0' (Nat.toDigits 10 m) = cs
  have hlen : p + 1 ≤ cs.length := by
    rw [← hcs, List.length_leftpad]; omega
  have hjoin : cs.take (cs.length - p) ++ cs.drop (cs.length - p) = cs := List.take_append_drop _ _
  refine ⟨cs.take (cs.length - p), cs.drop (cs.length - p), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [formatNat, hcs]
  · intro h
    have := congrArg List.length h
    simp at this; omega
  · simp; omega
  · rw [hjoin, ← hcs]
    exact isDigit_leftpad fun c hc => Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc
  · rw [hjoin, ← hcs, List.leftpad, digitsValue_replicate_append, digitsValue_toDigits]

/-- The characters of `formatDecimal p n` have a leading `'-'` exactly when `n` is negative, then those of `formatNat p |n|`. -/
theorem formatDecimal_spec (p : Nat) (n : Int) :
    formatDecimal p n = (if n < 0 then ['-'] else []) ++ formatNat p n.natAbs := rfl

/-- The length of `formatDecimal p n`: the sign if any, at least one whole digit and the `p` fractional digits with their point, and no leading zeros beyond that. -/
theorem formatDecimal_length (p : Nat) (n : Int) :
    (formatDecimal p n).length =
      (if n < 0 then 1 else 0) + max (Nat.toDigits 10 n.natAbs).length (p + 1) +
        (if p = 0 then 0 else 1) := by
  have h0 : 0 < (Nat.toDigits 10 n.natAbs).length := Nat.length_toDigits_pos
  unfold formatDecimal formatNat
  simp only [List.length_append, List.length_take, List.length_leftpad]
  split <;> split <;> simp <;> omega

theorem splitAtChar_none (c : Char) (a : List Char) (h : c ∉ a) : splitAtChar c a = (a, none) := by
  induction a with
  | nil => simp [splitAtChar]
  | cons x r ih =>
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self)
    simp [splitAtChar, hx, ih (fun m => h (List.mem_cons_of_mem _ m))]

theorem splitAtChar_some (c : Char) (a b : List Char) (h : c ∉ a) :
    splitAtChar c (a ++ c :: b) = (a, some b) := by
  induction a with
  | nil => simp [splitAtChar]
  | cons x r ih =>
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self)
    simp [splitAtChar, hx, ih (fun m => h (List.mem_cons_of_mem _ m))]

/-- Characters written by `formatDecimal` read back as the numerator and the number of fractional digits they were written from. -/
theorem parseDecimal_formatDecimal (p : Nat) (n : Int) :
    parseDecimal (formatDecimal p n) = some (n, p) := by
  obtain ⟨whole, frac, hf, hne, hlen, hdig, hval⟩ := formatNat_spec p n.natAbs
  have hwd : ∀ c ∈ whole, c.isDigit = true := fun c hc => hdig c (List.mem_append_left _ hc)
  have hdot : '.' ∉ whole := fun h => by have := hwd _ h; simp at this
  have hsplit : splitAtChar '.' (whole ++ (if p = 0 then [] else '.' :: frac)) =
      (whole, if p = 0 then none else some frac) := by
    split
    · rw [List.append_nil]; exact splitAtChar_none _ _ hdot
    · exact splitAtChar_some _ _ _ hdot
  have hres : ∀ neg : Bool, (neg = true → n < 0) → (neg = false → 0 ≤ n) →
      (let (w, fr) := splitAtChar '.' (whole ++ (if p = 0 then [] else '.' :: frac))
        let fr := fr.getD []
        if !w.isEmpty && (w ++ fr).all Char.isDigit then
          let v : Int := digitsValue (w ++ fr)
          some (if neg then -v else v, fr.length)
        else none) = some (n, p) := by
    intro neg h1 h2
    rw [hsplit]
    have hfr : (if p = 0 then (none : Option (List Char)) else some frac).getD [] = frac := by
      split
      · rename_i h0; subst h0; simp at hlen; simp [hlen]
      · rfl
    simp only [hfr]
    have hne' : whole.isEmpty = false := by
      cases h : whole <;> simp_all
    have hall : (whole ++ frac).all Char.isDigit = true := List.all_eq_true.2 hdig
    simp only [hne', hall, Bool.not_false, Bool.true_and, hval, hlen]
    have : (if neg = true then -((n.natAbs : Nat) : Int) else ((n.natAbs : Nat) : Int)) = n := by
      cases neg
      · have := h2 rfl; simp; omega
      · have := h1 rfl; simp; omega
    simp [this]
  unfold parseDecimal formatDecimal
  rw [hf]
  by_cases hn : n < 0
  · simp only [hn, ite_true, List.cons_append]
    exact hres true (fun _ => hn) (by simp)
  · obtain ⟨c, r, hcr⟩ := List.exists_cons_of_ne_nil hne
    have hc : c ≠ '-' := fun e => by have := hwd c (hcr ▸ List.mem_cons_self); simp [e] at this
    simp only [hn, ite_false, List.nil_append, hcr, List.cons_append, hc]
    rw [← List.cons_append, ← hcr]
    exact hres false (by simp) (fun _ => by omega)

theorem trimZeros_of_not_mem (cs : List Char) (h : '.' ∉ cs) : trimZeros cs = cs := by
  simp [trimZeros, splitAtChar_none '.' cs h]

theorem trimZeros_spec (w f : List Char) (h : '.' ∉ w) :
    trimZeros (w ++ '.' :: f) =
      if (trimFrac f).isEmpty then w else w ++ '.' :: trimFrac f := by
  simp [trimZeros, splitAtChar_some '.' w f h]

theorem trimFrac_prefix (f : List Char) : ∃ z, f = trimFrac f ++ z ∧ ∀ c ∈ z, c = '0' := by
  refine ⟨(f.reverse.takeWhile (· = '0')).reverse, ?_, ?_⟩
  · have := List.takeWhile_append_dropWhile (p := (· = '0')) (l := f.reverse)
    have h := congrArg List.reverse this
    simp only [List.reverse_append, List.reverse_reverse] at h
    exact h.symm
  · intro c hc
    have := List.all_eq_true.1 List.all_takeWhile c (List.mem_reverse.1 hc)
    simpa using this

theorem roundScaled_close (p : Nat) (q : Rat) :
    (roundScaled p q : Rat) - 1 / 2 ≤ q * (10 ^ p : Nat) ∧
      q * (10 ^ p : Nat) < (roundScaled p q : Rat) + 1 / 2 := by
  have h1 := Rat.floor_le (q * (10 ^ p : Nat) + 1 / 2)
  have h2 := Rat.lt_floor_add_one (q * (10 ^ p : Nat) + 1 / 2)
  unfold roundScaled
  rw [Rat.intCast_add] at h2
  constructor <;> grind


theorem pow10_pos (k : Int) : 0 < pow10 k := Rat.zpow_pos (by decide)

theorem pow10_succ (k : Int) : pow10 (k + 1) = 10 * pow10 k := by
  unfold pow10
  rw [Rat.zpow_add (by decide), Rat.zpow_one, Rat.mul_comm]

theorem pow10_add (k j : Int) : pow10 (k + j) = pow10 k * pow10 j :=
  Rat.zpow_add (by decide) k j

theorem pow10_nat (n : Nat) : pow10 n = (10 ^ n : Nat) := by
  unfold pow10
  rw [Rat.zpow_natCast]; push_cast; rfl

theorem log10_spec (n : Nat) (h : 0 < n) : 10 ^ log10 n ≤ n ∧ n < 10 ^ (log10 n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold log10
    split
    · simp; omega
    · have := ih (n / 10) (by omega) (by omega)
      rw [Nat.pow_succ, Nat.pow_succ]
      omega

theorem pow10_sub (a b : Nat) : pow10 ((a : Int) - b) * (10 ^ b : Nat) = (10 ^ a : Nat) := by
  rw [← pow10_nat, ← pow10_nat, ← pow10_add]; congr 1; omega

private theorem magnitude_aux (P B x n d A : Rat) (hB : 0 < B) (hx : 0 < x) (hxd : x * d = n)
    (hs : P * B = A) (h1 : A ≤ n) (h2 : n < 10 * A) (h3 : B ≤ d) (h4 : d < 10 * B) (hP : 0 < P) :
    x < 10 * P ∧ P < 10 * x := by
  have hd : 0 < d := by grind
  constructor
  · have a1 : P * B ≤ P * d := Rat.mul_le_mul_of_nonneg_left h3 (by grind)
    have : x * d < (10 * P) * d := by grind
    exact Rat.lt_of_mul_lt_mul_right this (by grind)
  · have a1 : x * d < x * (10 * B) := Rat.mul_lt_mul_of_pos_left h4 hx
    have : P * B < (10 * x) * B := by grind
    exact Rat.lt_of_mul_lt_mul_right this (by grind)

theorem magnitude_spec (q : Rat) (h : q ≠ 0) :
    pow10 (magnitude q) ≤ q.abs ∧ q.abs < pow10 (magnitude q + 1) := by
  have hn : 0 < q.num.natAbs := by
    have : q.num ≠ 0 := fun e => h (Rat.num_eq_zero.1 e)
    omega
  have hd : 0 < q.den := q.den_pos
  obtain ⟨n1, n2⟩ := log10_spec _ hn
  obtain ⟨d1, d2⟩ := log10_spec _ hd
  have hx : q.abs * (q.den : Rat) = (q.num.natAbs : Rat) := by
    have h0 : (q.den : Rat) ≠ 0 := by exact_mod_cast q.den_nz
    have h1 : q * (q.den : Rat) = (q.num : Rat) := by
      have := Rat.num_divInt_den q
      rw [Rat.divInt_eq_div] at this
      push_cast at this
      grind
    by_cases hq : 0 ≤ q
    · rw [Rat.abs_of_nonneg hq]
      have : 0 ≤ q.num := Rat.num_nonneg.2 hq
      have e : ((q.num.natAbs : Int)) = q.num := by omega
      have := congrArg (Int.cast : Int → Rat) e
      push_cast at this
      grind
    · rw [Rat.abs_of_nonpos (by grind)]
      have : q.num < 0 := by
        have : ¬ 0 ≤ q.num := fun e => hq (Rat.num_nonneg.1 e)
        omega
      have e : ((q.num.natAbs : Int)) = -q.num := by omega
      have := congrArg (Int.cast : Int → Rat) e
      push_cast at this
      grind
  have hs := pow10_sub (log10 q.num.natAbs) (log10 q.den)
  have hP := pow10_pos ((log10 q.num.natAbs : Int) - log10 q.den)
  have hxpos : 0 < q.abs := Rat.abs_pos_iff.2 h
  have c1 : (((10 ^ log10 q.num.natAbs : Nat)) : Rat) ≤ (q.num.natAbs : Rat) := by exact_mod_cast n1
  have c2 : (q.num.natAbs : Rat) < 10 * ((10 ^ log10 q.num.natAbs : Nat) : Rat) := by
    have : q.num.natAbs < 10 * 10 ^ log10 q.num.natAbs := by rw [Nat.pow_succ] at n2; omega
    exact_mod_cast this
  have c3 : (((10 ^ log10 q.den : Nat)) : Rat) ≤ (q.den : Rat) := by exact_mod_cast d1
  have c4 : (q.den : Rat) < 10 * ((10 ^ log10 q.den : Nat) : Rat) := by
    have : q.den < 10 * 10 ^ log10 q.den := by rw [Nat.pow_succ] at d2; omega
    exact_mod_cast this
  have key := magnitude_aux _ _ _ _ _ _ (by exact_mod_cast Nat.pow_pos (by omega : 0 < 10)) hxpos
    hx hs c1 c2 c3 c4 hP
  unfold magnitude
  simp only []
  split
  · rename_i hle
    rw [pow10_succ]
    exact ⟨hle, key.1⟩
  · rename_i hlt
    have := pow10_succ ((log10 q.num.natAbs : Int) - log10 q.den - 1)
    rw [show (log10 q.num.natAbs : Int) - log10 q.den - 1 + 1 = (log10 q.num.natAbs : Int) - log10 q.den by omega] at this
    have hp1 := pow10_pos ((log10 q.num.natAbs : Int) - log10 q.den - 1)
    rw [show (log10 q.num.natAbs : Int) - log10 q.den - 1 + 1 = (log10 q.num.natAbs : Int) - log10 q.den by omega]
    exact ⟨by grind, by grind⟩

theorem pow10_zero : pow10 0 = 1 := by simp [pow10]

theorem pow10_mono {j k : Int} (h : j ≤ k) : pow10 j ≤ pow10 k := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, k = j + n := ⟨(k - j).toNat, by omega⟩
  induction n with
  | zero => simp
  | succ i ih =>
    have := ih (by omega)
    rw [Int.natCast_succ, ← Int.add_assoc, pow10_succ]
    have := pow10_pos (j + i)
    grind

theorem pow10_strict {j k : Int} (h : j < k) : pow10 j < pow10 k := by
  have := pow10_mono (show j + 1 ≤ k by omega)
  rw [pow10_succ] at this
  have := pow10_pos j
  grind

theorem magnitude_pow10 (k : Int) : magnitude (pow10 k) = k := by
  have hp := pow10_pos k
  have hne : pow10 k ≠ 0 := by grind
  have hs := magnitude_spec _ hne
  rw [Rat.abs_of_nonneg (by grind)] at hs
  obtain ⟨h1, h2⟩ := hs
  rcases Int.lt_trichotomy (magnitude (pow10 k)) k with h | h | h
  · have := pow10_mono (show magnitude (pow10 k) + 1 ≤ k by omega)
    grind
  · exact h
  · have := pow10_strict h
    grind

private theorem roundSignificantRat_aux (x s m w : Rat) (hs : 0 < s) (hw : w * s = 1)
    (h1 : m - 1 / 2 ≤ x * s) (h2 : x * s < m + 1 / 2) : (m / s - x).abs ≤ w / 2 := by
  have hw0 : 0 < w := by
    by_cases h : 0 < w
    · exact h
    · have : w * s ≤ 0 := by
        have := Rat.mul_le_mul_of_nonneg_right (show w ≤ 0 by grind) (show 0 ≤ s by grind)
        grind
      grind
  have e : m / s - x = (m - x * s) * w := by
    have : w = s⁻¹ := by grind
    grind
  rw [e]
  have l1 : -(w / 2) ≤ (m - x * s) * w := by
    have := Rat.mul_le_mul_of_nonneg_right (show -(1 / 2) ≤ m - x * s by grind) (show 0 ≤ w by grind)
    grind
  have l2 : (m - x * s) * w ≤ w / 2 := by
    have := Rat.mul_le_mul_of_nonneg_right (show m - x * s ≤ 1 / 2 by grind) (show 0 ≤ w by grind)
    grind
  by_cases h : 0 ≤ (m - x * s) * w
  · rw [Rat.abs_of_nonneg h]; exact l2
  · rw [Rat.abs_of_nonpos (by grind)]; grind

theorem roundSignificantRat_close (digits : Nat) (q : Rat) (h : q ≠ 0) :
    (roundSignificantRat digits q - q).abs ≤ pow10 (magnitude q + 1 - digits) / 2 := by
  have hs := pow10_pos ((digits : Int) - 1 - magnitude q)
  have hw : pow10 (magnitude q + 1 - digits) * pow10 ((digits : Int) - 1 - magnitude q) = 1 := by
    rw [← pow10_add, show magnitude q + 1 - (digits : Int) + ((digits : Int) - 1 - magnitude q) = 0 by omega,
      pow10_zero]
  have hc := roundScaled_close 0 (q.abs * pow10 ((digits : Int) - 1 - magnitude q))
  have e1 : (((10 ^ 0 : Nat)) : Rat) = 1 := by simp
  rw [e1, Rat.mul_one] at hc
  have := roundSignificantRat_aux q.abs _ _ _ hs hw hc.1 hc.2
  unfold roundSignificantRat
  simp only [h, ite_false]
  generalize pow10 ((digits : Int) - 1 - magnitude q) = s at *
  generalize (roundScaled 0 (q.abs * s) : Rat) = m at *
  split
  · rename_i hq
    have ha : q.abs = -q := Rat.abs_of_nonpos (by grind)
    have e : (-1 * m) / s - q = -(m / s - q.abs) := by grind
    rw [e, Rat.abs_neg]; exact this
  · rename_i hq
    have ha : q.abs = q := Rat.abs_of_nonneg (by grind)
    have e : (1 * m) / s - q = m / s - q.abs := by grind
    rw [e]; exact this

theorem roundScaled_natCast (n : Nat) : roundScaled 0 (n : Rat) = n := by
  have hc := roundScaled_close 0 (n : Rat)
  have e1 : (((10 ^ 0 : Nat)) : Rat) = 1 := by simp
  rw [e1, Rat.mul_one] at hc
  have a : 2 * (roundScaled 0 (n : Rat)) ≤ 2 * (n : Int) + 1 := by
    have : (2 : Rat) * (roundScaled 0 (n : Rat) : Rat) ≤ 2 * (n : Int) + 1 := by
      have := hc.1; push_cast; grind
    exact_mod_cast this
  have b : 2 * (n : Int) < 2 * (roundScaled 0 (n : Rat)) + 1 := by
    have : (2 : Rat) * (n : Int) < 2 * (roundScaled 0 (n : Rat) : Rat) + 1 := by
      have := hc.2; push_cast; grind
    exact_mod_cast this
  omega

theorem roundSignificantRat_zero (digits : Nat) : roundSignificantRat digits 0 = 0 := by
  simp [roundSignificantRat]

/-- Powers of ten are unchanged by rounding to one or more significant digits. -/
theorem roundSignificantRat_pow10 (digits : Nat) (hd : 1 ≤ digits) (k : Int) :
    roundSignificantRat digits (pow10 k) = pow10 k := by
  have hp := pow10_pos k
  have hne : pow10 k ≠ 0 := by grind
  have hnl : ¬ pow10 k < 0 := by grind
  have hm := magnitude_pow10 k
  have hN : pow10 k * pow10 ((digits : Int) - 1 - k) = ((10 ^ (digits - 1) : Nat) : Rat) := by
    rw [← pow10_add, show k + ((digits : Int) - 1 - k) = ((digits - 1 : Nat) : Int) by omega,
      pow10_nat]
  have hs := pow10_pos ((digits : Int) - 1 - k)
  unfold roundSignificantRat
  simp only [hne, hnl, hm, ite_false, Rat.abs_of_nonneg (show 0 ≤ pow10 k by grind)]
  rw [hN, roundScaled_natCast]
  have e : ((((10 ^ (digits - 1) : Nat)) : Int) : Rat) = (((10 ^ (digits - 1) : Nat)) : Rat) := by
    exact_mod_cast rfl
  rw [e]
  generalize pow10 ((digits : Int) - 1 - k) = s at *
  generalize pow10 k = x at *
  generalize (((10 ^ (digits - 1) : Nat)) : Rat) = N at *
  grind

theorem roundSignificant_nonFinite (digits : Nat) (x : Float)
    (h : Inkproof.Float.Float.toRat x = none) : roundSignificant digits x = x := by
  simp [roundSignificant, h]

theorem roundSignificant_zero (digits : Nat) (x : Float)
    (h : Inkproof.Float.Float.toRat x = some 0) : roundSignificant digits x = x := by
  simp [roundSignificant, h]

end Inkproof.Core.Decimal
