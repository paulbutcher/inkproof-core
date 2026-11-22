/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Calendar
import Inkproof.Core.Proofs.Decimal

namespace Inkproof.Core.Calendar

theorem isLeap_iff (y : Int) :
    isLeap y = true ↔ (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)) := by
  simp [isLeap]

private theorem yoe_spec (doe : Int) (h0 : 0 ≤ doe) (h1 : doe < 146097) :
    let y := min (doe / 365) 399
    let yoe := if doe < 365 * y + y / 4 - y / 100 then y - 1 else y
    0 ≤ yoe ∧ yoe ≤ 399 ∧ 365 * yoe + yoe / 4 - yoe / 100 ≤ doe ∧
    (doe < 365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100 ∨ yoe = 399) := by
  intro y yoe
  obtain ⟨y', hy⟩ : ∃ y', y' = min (doe / 365) 399 := ⟨_, rfl⟩
  simp only [yoe, y, ← hy]
  have h : y' = 0 ∨ y' < 100 ∨ y' < 200 ∨ y' < 300 ∨ y' < 400 := by omega
  split
  · simp only [Int.sub_add_cancel]
    rcases h with h|h|h|h|h <;> omega
  · rcases h with h|h|h|h|h <;> omega

private def core (era doe yoe : Int) : Int × Nat × Nat :=
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m.toNat, d.toNat)

private theorem civilFromDays_eq (z : Int) :
    civilFromDays z =
      core ((z + 719468) / 146097) ((z + 719468) % 146097)
        (let doe := (z + 719468) % 146097
         let y := min (doe / 365) 399
         if doe < 365 * y + y / 4 - y / 100 then y - 1 else y) := rfl

private theorem core_valid (era doe yoe : Int) (h0 : 0 ≤ yoe) (h1 : yoe ≤ 399)
    (h2 : 365 * yoe + yoe / 4 - yoe / 100 ≤ doe)
    (h3 : doe < 365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100 ∨ yoe = 399)
    (h4 : doe < 146097) :
    1 ≤ (core era doe yoe).2.1 ∧ (core era doe yoe).2.1 ≤ 12 ∧
    1 ≤ (core era doe yoe).2.2 ∧
    (core era doe yoe).2.2 ≤ daysInMonth (core era doe yoe).1 (core era doe yoe).2.1 := by
  have hl : doe - (365 * yoe + yoe / 4 - yoe / 100) < 366 ∧
      ¬((yoe + 1) % 4 = 0 ∧ ((yoe + 1) % 100 ≠ 0 ∨ yoe + 1 = 400)) →
      doe - (365 * yoe + yoe / 4 - yoe / 100) < 365 := by omega
  have hl' : doe - (365 * yoe + yoe / 4 - yoe / 100) < 366 := by omega
  unfold core
  simp only []
  obtain ⟨doy, hd⟩ : ∃ doy, doy = doe - (365 * yoe + yoe / 4 - yoe / 100) := ⟨_, rfl⟩
  rw [← hd] at hl hl' ⊢
  have hdoy : 0 ≤ doy := by omega
  obtain ⟨mp, hmp⟩ : ∃ mp, mp = (5 * doy + 2) / 153 := ⟨_, rfl⟩
  rw [← hmp]
  have hq : 153 * mp ≤ 5 * doy + 2 ∧ 5 * doy + 2 < 153 * (mp + 1) := by omega
  have hm : 0 ≤ mp ∧ mp ≤ 11 := by omega
  obtain ⟨q, hqd⟩ : ∃ q, q = (153 * mp + 2) / 5 := ⟨_, rfl⟩
  rw [← hqd]
  obtain ⟨hm0, hm1⟩ := hm
  have hc : mp = 0 ∨ mp = 1 ∨ mp = 2 ∨ mp = 3 ∨ mp = 4 ∨ mp = 5 ∨ mp = 6 ∨ mp = 7 ∨ mp = 8 ∨
      mp = 9 ∨ mp = 10 ∨ mp = 11 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [daysInMonth, isLeap] <;> (try split) <;> omega

theorem civilFromDays_valid (z : Int) :
    1 ≤ (civilFromDays z).2.1 ∧ (civilFromDays z).2.1 ≤ 12 ∧
    1 ≤ (civilFromDays z).2.2 ∧
    (civilFromDays z).2.2 ≤ daysInMonth (civilFromDays z).1 (civilFromDays z).2.1 := by
  rw [civilFromDays_eq]
  have hs := yoe_spec ((z + 719468) % 146097) (by omega) (by omega)
  exact core_valid _ _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 (by omega)

private theorem core_days (era doe yoe : Int) (h0 : 0 ≤ yoe) (h1 : yoe ≤ 399)
    (h2 : 365 * yoe + yoe / 4 - yoe / 100 ≤ doe)
    (h3 : doe < 365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100 ∨ yoe = 399)
    (h4 : doe < 146097) :
    daysFromCivil (core era doe yoe).1 (core era doe yoe).2.1 (core era doe yoe).2.2 =
      era * 146097 + doe - 719468 := by
  have hl : doe - (365 * yoe + yoe / 4 - yoe / 100) < 366 := by omega
  unfold core daysFromCivil
  simp only []
  obtain ⟨doy, hd⟩ : ∃ doy, doy = doe - (365 * yoe + yoe / 4 - yoe / 100) := ⟨_, rfl⟩
  rw [← hd] at hl ⊢
  have hdoy : 0 ≤ doy := by omega
  obtain ⟨mp, hmp⟩ : ∃ mp, mp = (5 * doy + 2) / 153 := ⟨_, rfl⟩
  rw [← hmp]
  have hq : 153 * mp ≤ 5 * doy + 2 ∧ 5 * doy + 2 < 153 * (mp + 1) := by omega
  have hm : 0 ≤ mp ∧ mp ≤ 11 := by omega
  obtain ⟨q, hqd⟩ : ∃ q, q = (153 * mp + 2) / 5 := ⟨_, rfl⟩
  rw [← hqd]
  obtain ⟨hm0, hm1⟩ := hm
  have hc : mp = 0 ∨ mp = 1 ∨ mp = 2 ∨ mp = 3 ∨ mp = 4 ∨ mp = 5 ∨ mp = 6 ∨ mp = 7 ∨ mp = 8 ∨
      mp = 9 ∨ mp = 10 ∨ mp = 11 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp <;> omega

theorem daysFromCivil_civilFromDays (z : Int) :
    daysFromCivil (civilFromDays z).1 (civilFromDays z).2.1 (civilFromDays z).2.2 = z := by
  rw [civilFromDays_eq]
  have hs := yoe_spec ((z + 719468) % 146097) (by omega) (by omega)
  rw [core_days _ _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 (by omega)]
  omega

private theorem yoe_unique (doe a b : Int) (h1 : a ≤ 399) (h3 : b ≤ 399)
    (ha : 365 * a + a / 4 - a / 100 ≤ doe)
    (ha' : doe < 365 * (a + 1) + (a + 1) / 4 - (a + 1) / 100 ∨ a = 399)
    (hb : 365 * b + b / 4 - b / 100 ≤ doe)
    (hb' : doe < 365 * (b + 1) + (b + 1) / 4 - (b + 1) / 100 ∨ b = 399)
    : a = b := by
  have step : ∀ (k : Nat) (x : Int),
      365 * x + x / 4 - x / 100 ≤ 365 * (x + k) + (x + k) / 4 - (x + k) / 100 := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ n ih => intro x; have := ih x; omega
  have mono : ∀ x y : Int, x ≤ y →
      365 * x + x / 4 - x / 100 ≤ 365 * y + y / 4 - y / 100 := by
    intro x y hxy
    have := step (y - x).toNat x
    have e : x + ((y - x).toNat : Int) = y := by omega
    rwa [e] at this
  have key : ∀ a b : Int, a < b → b ≤ 399 → 365 * b + b / 4 - b / 100 ≤ doe →
      (doe < 365 * (a + 1) + (a + 1) / 4 - (a + 1) / 100 ∨ a = 399) → False := by
    intro a b hab hb hle hlt
    have := mono (a + 1) b (by omega)
    omega
  rcases Int.lt_trichotomy a b with h | h | h
  · exact (key a b h h3 hb ha').elim
  · exact h
  · exact (key b a h h1 ha hb').elim

theorem civilFromDays_daysFromCivil (y : Int) (m d : Nat) (hm1 : 1 ≤ m) (hm2 : m ≤ 12)
    (hd1 : 1 ≤ d) (hd2 : d ≤ daysInMonth y m) :
    civilFromDays (daysFromCivil y m d) = (y, m, d) := by
  unfold daysFromCivil
  simp only []
  obtain ⟨y', hy'⟩ : ∃ y', y' = if m ≤ 2 then y - 1 else y := ⟨_, rfl⟩
  obtain ⟨doy, hdy⟩ : ∃ doy : Int,
      doy = (153 * (if m > 2 then (m : Int) - 3 else (m : Int) + 9) + 2) / 5 + d - 1 := ⟨_, rfl⟩
  rw [← hy', ← hdy]
  obtain ⟨era, hera⟩ : ∃ era, era = y' / 400 := ⟨_, rfl⟩
  obtain ⟨yoe, hyoe⟩ : ∃ yoe, yoe = y' % 400 := ⟨_, rfl⟩
  rw [← hera, ← hyoe]
  have hb1 : 0 ≤ doy ∧ doy ≤ 365 ∧ (doy = 365 → m = 2 ∧ d = 29) := by
    have hmc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
        m = 10 ∨ m = 11 ∨ m = 12 := by omega
    rcases hmc with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      simp [daysInMonth] at hd2 hdy <;> (try split at hd2) <;> omega
  have hb : 0 ≤ doy ∧ doy < 366 ∧
      (doy < 365 ∨ (yoe + 1) % 4 = 0 ∧ ((yoe + 1) % 100 ≠ 0 ∨ yoe + 1 = 400)) := by
    refine ⟨hb1.1, by omega, ?_⟩
    by_cases h : doy = 365
    · obtain ⟨hm, _⟩ := hb1.2.2 h
      subst hm
      have hl : isLeap y = true := by
        simp [daysInMonth] at hd2
        split at hd2 <;> simp_all
      simp [isLeap] at hl
      right
      simp at hy'
      omega
    · omega
  have hyb : 0 ≤ yoe ∧ yoe ≤ 399 ∧ y' = 400 * era + yoe := by omega
  obtain ⟨doe, hdoe⟩ : ∃ doe, doe = yoe * 365 + yoe / 4 - yoe / 100 + doy := ⟨_, rfl⟩
  rw [← hdoe]
  have hd0 : 365 * yoe + yoe / 4 - yoe / 100 ≤ doe := by omega
  have hd1 : doe < 365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100 ∨ yoe = 399 := by omega
  have hd2' : doe < 146097 := by omega
  have e : era * 146097 + doe - 719468 + 719468 = era * 146097 + doe := by omega
  have e1 : (era * 146097 + doe) / 146097 = era := by omega
  have e2 : (era * 146097 + doe) % 146097 = doe := by omega
  have hs := yoe_spec doe (by omega) hd2'
  have hu := yoe_unique doe _ yoe hs.2.1 hyb.2.1 hs.2.2.1 hs.2.2.2 hd0 hd1
  rw [civilFromDays_eq]
  simp only [e, e1, e2]
  rw [show (let y := min (doe / 365) 399
      if doe < 365 * y + y / 4 - y / 100 then y - 1 else y) = yoe from hu]
  have hdy2 : doe - (365 * yoe + yoe / 4 - yoe / 100) = doy := by omega
  unfold core
  simp only [hdy2]
  obtain ⟨mp, hmp⟩ : ∃ mp, mp = (5 * doy + 2) / 153 := ⟨_, rfl⟩
  rw [← hmp]
  obtain ⟨q, hqd⟩ : ∃ q, q = (153 * mp + 2) / 5 := ⟨_, rfl⟩
  rw [← hqd]
  have hq : 153 * mp ≤ 5 * doy + 2 ∧ 5 * doy + 2 < 153 * (mp + 1) := by omega
  clear hs hu e e1 e2 hd0 hd1 hd2' hdy2 hera hyoe hb hb1 hdoe hmp
  have hmc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
      m = 10 ∨ m = 11 ∨ m = 12 := by omega
  rcases hmc with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp [Prod.ext_iff, daysInMonth] at hdy hy' hd2 ⊢ <;> (repeat' split) <;>
      (repeat' (first | split at hd2 | split at hlt)) <;> omega

theorem daysInMonth_february (y : Int) : daysInMonth y 2 = if isLeap y then 29 else 28 := by
  simp [daysInMonth]

theorem daysInMonth_thirty (y : Int) (m : Nat) (h : m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11) :
    daysInMonth y m = 30 := by
  rcases h with h | h | h | h <;> subst h <;> simp [daysInMonth]

theorem daysInMonth_thirty_one (y : Int) (m : Nat) (h : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 8 ∨ m = 10 ∨ m = 12) :
    daysInMonth y m = 31 := by
  rcases h with h | h | h | h | h | h | h <;> subst h <;> simp [daysInMonth]

theorem daysInMonth_bounds (y : Int) (m : Nat) : 28 ≤ daysInMonth y m ∧ daysInMonth y m ≤ 31 := by
  unfold daysInMonth
  split <;> (try split) <;> (try split) <;> omega

theorem nextDay_valid (y : Int) (m d : Nat) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) :
    1 ≤ (nextDay (y, m, d)).2.1 ∧ (nextDay (y, m, d)).2.1 ≤ 12 ∧ 1 ≤ (nextDay (y, m, d)).2.2 ∧
    (nextDay (y, m, d)).2.2 ≤ daysInMonth (nextDay (y, m, d)).1 (nextDay (y, m, d)).2.1 := by
  have hb := daysInMonth_bounds y (m + 1)
  have hb' := daysInMonth_bounds (y + 1) 1
  simp only [nextDay]
  split
  · dsimp only; omega
  · split
    · dsimp only; omega
    · dsimp only; simp [daysInMonth]

theorem daysFromCivil_nextDay (y : Int) (m d : Nat) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d)
    (hd2 : d ≤ daysInMonth y m) :
    daysFromCivil (nextDay (y, m, d)).1 (nextDay (y, m, d)).2.1 (nextDay (y, m, d)).2.2 =
      daysFromCivil y m d + 1 := by
  simp only [nextDay]
  by_cases hlt : d < daysInMonth y m
  · simp only [hlt, ite_true]
    unfold daysFromCivil
    simp only []
    split <;> omega
  · simp only [hlt, ite_false]
    have hmc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
        m = 10 ∨ m = 11 ∨ m = 12 := by omega
    rcases hmc with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      simp [daysInMonth, isLeap, daysFromCivil] at hd2 hlt ⊢ <;>
      (repeat' (first | split at hd2 | split at hlt)) <;> omega

theorem daysFromCivil_epoch : daysFromCivil 1970 1 1 = 0 := by decide

theorem civilFromDays_zero : civilFromDays 0 = (1970, 1, 1) := by decide

theorem civilFromDays_succ (z : Int) :
    civilFromDays (z + 1) = nextDay (civilFromDays z) := by
  have hz := civilFromDays_valid z
  have hd := daysFromCivil_civilFromDays z
  rcases hc : civilFromDays z with ⟨y, m, d⟩
  rw [hc] at hz hd
  obtain ⟨hm1, hm2, hd1, hd2⟩ := hz
  have hv := nextDay_valid y m d hm1 hm2
  have hn := daysFromCivil_nextDay y m d hm1 hm2 hd1 hd2
  have hr := civilFromDays_daysFromCivil _ _ _ hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  simp only at hd
  rw [hd] at hn
  rw [← hn]
  exact hr

theorem isoDate_zero : isoDate 0 = "1970-01-01" := by decide +kernel

local notation "pad " w:max n:max => List.leftpad w '0' (Nat.toDigits 10 n)

private theorem pad_length (w n : Nat) (hw : 0 < w) (h : n < 10 ^ w) : (pad w n).length = w := by
  have := (Nat.length_toDigits_le_iff (b := 10) (by omega) hw).2 h
  simp only [List.length_leftpad]
  omega

theorem isoChars_length (y : Int) (m d : Nat) (hy : 0 ≤ y) (hy' : y < 10000) (hm : m < 100)
    (hd : d < 100) : (isoChars (y, m, d)).length = 10 := by
  have h1 := pad_length 4 y.natAbs (by omega) (by omega)
  have h2 := pad_length 2 m (by omega) (by omega)
  have h3 := pad_length 2 d (by omega) (by omega)
  simp only [isoChars, List.length_append, List.length_cons, h1, h2, h3]
  simp [Int.not_lt.2 hy]

/-- For a year in 0 to 9999 and a month and day below 100, the first four characters of the text are the year padded to four digits, then a hyphen, the month padded to two, a hyphen, and the day padded to two. -/
theorem isoChars_fields (y : Int) (m d : Nat) (hy : 0 ≤ y) (hy' : y < 10000) (hm : m < 100)
    (hd : d < 100) :
    (isoChars (y, m, d)).take 4 = pad 4 y.natAbs ∧ (isoChars (y, m, d))[4]? = some '-' ∧
      ((isoChars (y, m, d)).drop 5).take 2 = pad 2 m ∧ (isoChars (y, m, d))[7]? = some '-' ∧
      (isoChars (y, m, d)).drop 8 = pad 2 d := by
  have h1 := pad_length 4 y.natAbs (by omega) (by omega)
  have h2 := pad_length 2 m (by omega) (by omega)
  have h3 := pad_length 2 d (by omega) (by omega)
  have he : isoChars (y, m, d) = pad 4 y.natAbs ++ '-' :: (pad 2 m ++ '-' :: pad 2 d) := by
    simp [isoChars, Int.not_lt.2 hy]
  rw [he]
  generalize pad 4 y.natAbs = A at *
  generalize pad 2 m = B at *
  generalize pad 2 d = C at *
  match A, h1, B, h2, C, h3 with
  | [_, _, _, _], _, [_, _], _, [_, _], _ => simp

/-- For a day whose year is in 0 to 9999, the first four characters of `isoDate z` are the year of `civilFromDays z` padded to four digits, then a hyphen, the month padded to two, a hyphen, and the day padded to two. -/
theorem isoDate_fields (z : Int) (hy : 0 ≤ (civilFromDays z).1) (hy' : (civilFromDays z).1 < 10000) :
    (isoDate z).toList.take 4 = pad 4 (civilFromDays z).1.natAbs ∧
      (isoDate z).toList[4]? = some '-' ∧
      ((isoDate z).toList.drop 5).take 2 = pad 2 (civilFromDays z).2.1 ∧
      (isoDate z).toList[7]? = some '-' ∧
      (isoDate z).toList.drop 8 = pad 2 (civilFromDays z).2.2 := by
  have hv := civilFromDays_valid z
  have hb := daysInMonth_bounds (civilFromDays z).1 (civilFromDays z).2.1
  have := isoChars_fields (civilFromDays z).1 (civilFromDays z).2.1 (civilFromDays z).2.2 hy hy'
    (by omega) (by omega)
  simpa [isoDate] using this

/-- The text of `isoDate z` is, for every day, the sign of the year of `civilFromDays z` when negative, the magnitude padded to four digits, a hyphen, the month padded to two, a hyphen, and the day padded to two. -/
theorem isoDate_spec (z : Int) :
    (isoDate z).toList =
      (if (civilFromDays z).1 < 0 then ['-'] else []) ++ pad 4 (civilFromDays z).1.natAbs ++
        '-' :: pad 2 (civilFromDays z).2.1 ++ '-' :: pad 2 (civilFromDays z).2.2 := by
  simp [isoDate, isoChars]

end Inkproof.Core.Calendar
