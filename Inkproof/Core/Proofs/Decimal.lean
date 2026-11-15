/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Decimal

namespace Inkproof.Core.Decimal

private theorem cases_lt_ten {d : Nat} (h : d < 10) :
    d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega

theorem digitChar_isDigit {d : Nat} (h : d < 10) : (Nat.digitChar d).isDigit = true := by
  rcases cases_lt_ten h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem digitChar_toNat {d : Nat} (h : d < 10) : (Nat.digitChar d).toNat - 48 = d := by
  rcases cases_lt_ten h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem lsDigits_lt (m w : Nat) : ∀ d ∈ lsDigits m w, d < 10 := by
  induction w generalizing m with
  | zero => simp [lsDigits]
  | succ w ih =>
    intro d hd
    simp only [lsDigits, List.mem_cons] at hd
    rcases hd with rfl | hd
    · omega
    · exact ih _ d hd

theorem lsDigits_length (m w : Nat) : (lsDigits m w).length = w := by
  induction w generalizing m with
  | zero => simp [lsDigits]
  | succ w ih => simp [lsDigits, ih]

theorem lsValue_lsDigits (m w : Nat) : lsValue (lsDigits m w) = m % 10 ^ w := by
  induction w generalizing m with
  | zero => simp [lsDigits, lsValue, Nat.mod_one]
  | succ w ih =>
    have := ih (m / 10)
    simp only [lsValue] at this
    simp only [lsDigits, lsValue, List.foldr_cons, this]
    rw [Nat.pow_succ, Nat.mul_comm (10 ^ w) 10, Nat.mod_mul]

theorem lt_pow_digitCount (m : Nat) : m < 10 ^ digitCount m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    unfold digitCount
    split
    · simpa using ‹m < 10›
    · have := ih (m / 10) (by omega)
      rw [Nat.pow_succ]
      omega

theorem digitCount_spec (m : Nat) : m < 10 ^ digitCount m ∧ (m < 10 ∨ 10 ^ (digitCount m - 1) ≤ m) := by
  refine ⟨lt_pow_digitCount m, ?_⟩
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases h : m < 10
    · exact Or.inl h
    · right
      have h1 : digitCount m = digitCount (m / 10) + 1 := by rw [digitCount]; simp [h]
      rw [h1, Nat.add_sub_cancel]
      rcases ih (m / 10) (by omega) with h2 | h2
      · have : digitCount (m / 10) = 1 := by rw [digitCount]; simp [h2]
        rw [this]; omega
      · have : 10 ^ (digitCount (m / 10) - 1) * 10 ≤ m := by omega
        have h3 : 0 < digitCount (m / 10) := by rw [digitCount]; split <;> omega
        calc 10 ^ digitCount (m / 10) = 10 ^ (digitCount (m / 10) - 1) * 10 := by
              rw [← Nat.pow_succ]; congr 1; omega
          _ ≤ m := this

theorem digitsValue_reverse (ds : List Nat) (h : ∀ d ∈ ds, d < 10) :
    digitsValue (ds.reverse.map Nat.digitChar) = lsValue ds := by
  induction ds with
  | nil => simp [digitsValue, lsValue]
  | cons d ds ih =>
    have hd : d < 10 := h d (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, digitsValue,
      List.foldl_append, List.foldl_cons, List.foldl_nil, digitChar_toNat hd] at *
    simp only [lsValue, List.foldr_cons] at *
    rw [this]; omega

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

theorem scaledDigits_length (p m : Nat) : (scaledDigits p m).length = max (digitCount m) (p + 1) :=
  lsDigits_length _ _

theorem scaledDigits_lt (p m : Nat) : ∀ d ∈ scaledDigits p m, d < 10 := lsDigits_lt _ _

theorem lsValue_scaledDigits (p m : Nat) : lsValue (scaledDigits p m) = m := by
  unfold scaledDigits
  rw [lsValue_lsDigits]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (lt_pow_digitCount _)
    (Nat.pow_le_pow_right (by omega) (by omega)))

/-- The characters of `formatNat p m` are the whole digits, then if `p` is not zero a point and `p` fractional digits. The whole part is not empty, every other character is a digit, and the digits read as `m`. -/
theorem formatNat_spec (p m : Nat) : ∃ whole frac : List Char,
    formatNat p m = whole ++ (if p = 0 then [] else '.' :: frac) ∧ whole ≠ [] ∧ frac.length = p ∧
      (∀ c ∈ whole ++ frac, c.isDigit = true) ∧ digitsValue (whole ++ frac) = m := by
  have hlt := scaledDigits_lt p m
  have hlen := scaledDigits_length p m
  generalize hds : scaledDigits p m = ds at hlt hlen
  have hval : lsValue ds = m := by rw [← hds]; exact lsValue_scaledDigits p m
  have hmax : p < ds.length := by omega
  have hjoin : (ds.drop p).reverse.map Nat.digitChar ++ (ds.take p).reverse.map Nat.digitChar =
      ds.reverse.map Nat.digitChar := by
    rw [← List.map_append, ← List.reverse_append, List.take_append_drop]
  refine ⟨(ds.drop p).reverse.map Nat.digitChar, (ds.take p).reverse.map Nat.digitChar, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [formatNat, hds]
  · intro h
    have := congrArg List.length h
    simp at this; omega
  · simp; omega
  · rw [hjoin]
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact digitChar_isDigit (hlt d (List.mem_reverse.1 hd))
  · rw [hjoin, digitsValue_reverse ds hlt, hval]

/-- The characters of `formatDecimal p n` have a leading `'-'` exactly when `n` is negative, then those of `formatNat p |n|`. -/
theorem formatDecimal_spec (p : Nat) (n : Int) :
    formatDecimal p n = (if n < 0 then ['-'] else []) ++ formatNat p n.natAbs := rfl

/-- The length of `formatDecimal p n`: the sign if any, at least one whole digit and the `p` fractional digits with their point, and no leading zeros beyond that. -/
theorem formatDecimal_length (p : Nat) (n : Int) :
    (formatDecimal p n).length = (if n < 0 then 1 else 0) + max (digitCount n.natAbs) (p + 1) +
      (if p = 0 then 0 else 1) := by
  have hl := scaledDigits_length p n.natAbs
  unfold formatDecimal formatNat
  generalize scaledDigits p n.natAbs = ds at hl
  split <;> split <;> simp <;> omega

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

end Inkproof.Core.Decimal
