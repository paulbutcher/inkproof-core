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

end Inkproof.Core.Decimal
