/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Calendar
import Inkproof.Core.Proofs.Decimal

namespace Inkproof.Core.Calendar

open Std.Time

private theorem tmod_zero_iff (y n : Int) : y.tmod n = 0 ↔ y % n = 0 := by
  rw [← Int.dvd_iff_tmod_eq_zero, Int.dvd_iff_emod_eq_zero]

private theorem isLeap_eq (y : Int) : isLeap y = (y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)) := by
  simp [isLeap, Year.Offset.isLeap, Year.Offset.ofInt, Year.Offset.toInt, tmod_zero_iff]
  rfl

private theorem daysInMonth_eq (y : Int) (m : Nat) : daysInMonth y m =
    if m = 2 then (if isLeap y then 29 else 28)
    else if m = 4 || m = 6 || m = 9 || m = 11 then 30 else 31 := by
  unfold daysInMonth
  have hc : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
      m = 10 ∨ m = 11 ∨ m = 12 ∨ 13 ≤ m := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals try subst h
  all_goals try (simp [Month.Ordinal.days, Internal.Bounded.LE.clip]; first | rfl | (split <;> rfl))
  · have h0 : 1 ≤ (m : Int) := by omega
    have h1 : ¬ (m : Int) ≤ 12 := by omega
    have h2 : m ≠ 2 := by omega
    have h3 : m ≠ 4 := by omega
    have h4 : m ≠ 6 := by omega
    have h5 : m ≠ 9 := by omega
    have h6 : m ≠ 11 := by omega
    simp [Month.Ordinal.days, Internal.Bounded.LE.clip, h0, h1, h2, h3, h4, h5, h6]
    rfl

theorem isLeap_iff (y : Int) :
    isLeap y = true ↔ (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)) := by
  simp [isLeap_eq]

private def yearOf (n : Int) : Int := (n - n / 1460 + n / 36524 - n / 146096) / 365

private def daysBefore (y : Int) : Int := 365 * y + y / 4 - y / 100

private theorem yearOf_mono (a b : Int) (h : a ≤ b) : yearOf a ≤ yearOf b := by
  have m1 : a - a / 1460 ≤ b - b / 1460 := by omega
  have m2 : a / 36524 - a / 146096 ≤ b / 36524 - b / 146096 := by
    have e1 : a / 146096 = a / 36524 / 4 := by omega
    have e2 : b / 146096 = b / 36524 / 4 := by omega
    omega
  unfold yearOf
  omega

private theorem daysBefore_pred : ∀ y : Nat, y < 400 → 1 ≤ y → yearOf (daysBefore y - 1) < y := by
  decide +kernel

private theorem daysBefore_self : ∀ y : Nat, y < 400 → y ≤ yearOf (daysBefore y) := by
  decide +kernel

private theorem yoe_spec (doe yoe : Int) (h0 : 0 ≤ doe) (h1 : doe < 146097)
    (hy : yoe = yearOf doe) :
    0 ≤ yoe ∧ yoe ≤ 399 ∧ 365 * yoe + yoe / 4 - yoe / 100 ≤ doe ∧
    (doe < 365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100 ∨ yoe = 399) := by
  have hlo : 0 ≤ yoe := by unfold yearOf at hy; omega
  have hhi : yoe ≤ 399 := by
    have := yearOf_mono doe 146096 (by omega)
    have h : yearOf 146096 = 399 := by decide
    omega
  refine ⟨hlo, hhi, ?_, ?_⟩
  · by_cases h : yoe = 0
    · subst h; omega
    · by_cases hc : 365 * yoe + yoe / 4 - yoe / 100 ≤ doe
      · exact hc
      exfalso
      have e := Int.toNat_of_nonneg hlo
      have h1 := daysBefore_pred yoe.toNat (by omega) (by omega)
      rw [e] at h1
      have h2 := yearOf_mono doe (daysBefore yoe - 1) (by unfold daysBefore; omega)
      omega
  · by_cases h : yoe = 399
    · exact Or.inr h
    · left
      by_cases hc : doe < 365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100
      · exact hc
      exfalso
      have e := Int.toNat_of_nonneg (show 0 ≤ yoe + 1 by omega)
      have h1 := daysBefore_self (yoe + 1).toNat (by omega)
      rw [e] at h1
      have h2 := yearOf_mono (daysBefore (yoe + 1)) doe (by unfold daysBefore; omega)
      omega

private def core (era doe yoe : Int) : Int × Nat × Nat :=
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m.toNat, d.toNat)

private theorem tdiv_floor (a : Int) {_ : Decidable (a ≥ 0)} :
    (if a ≥ 0 then a else a - 146096).tdiv 146097 = a / 146097 := by
  split
  · exact Int.tdiv_eq_ediv_of_nonneg ‹_›
  · have h : a - 146096 = -(146096 - a) := by omega
    rw [h, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    omega

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
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [daysInMonth_eq, isLeap_eq] <;> (try split) <;> omega

private theorem dim_eq (y M : Int) (h1 : 1 ≤ M) (h2 : M ≤ 12) :
    (Month.Ordinal.days (Year.Offset.ofInt y).isLeap (Internal.Bounded.LE.clip M (by decide))).val =
      (daysInMonth y M.toNat : Int) := by
  unfold daysInMonth
  have e : ((M.toNat : Nat) : Int) = M := Int.toNat_of_nonneg (by omega)
  rw [e]
  exact (Int.toNat_of_nonneg (by have := (Month.Ordinal.days (Year.Offset.ofInt y).isLeap
    (Internal.Bounded.LE.clip M (by decide))).property; omega)).symm

theorem daysInMonth_bounds (y : Int) (m : Nat) : 28 ≤ daysInMonth y m ∧ daysInMonth y m ≤ 31 := by
  rw [daysInMonth_eq]
  split <;> (try split) <;> (try split) <;> omega

private theorem clip_val {lo hi : Int} (h : lo ≤ hi) (v : Int) (h1 : lo ≤ v) (h2 : v ≤ hi) :
    (Internal.Bounded.LE.clip v h).val = v := by
  simp [Internal.Bounded.LE.clip, h1, h2]

private theorem civil_eq (d : Day.Offset) :
    ((PlainDate.ofEpochDay d).year.toInt, (PlainDate.ofEpochDay d).month.val.toNat,
      (PlainDate.ofEpochDay d).day.val.toNat) =
      core ((d.toInt + 719468) / 146097) ((d.toInt + 719468) % 146097)
        (yearOf ((d.toInt + 719468) % 146097)) := by
  simp only [PlainDate.ofEpochDay, PlainDate.ofYearMonthDayClip, tdiv_floor]
  generalize Internal.UnitVal.toInt d = x
  obtain ⟨doe, hdoe⟩ : ∃ doe, doe = x + 719468 - (x + 719468) / 146097 * 146097 := ⟨_, rfl⟩
  have hd0 : 0 ≤ doe := by omega
  have hd1 : doe < 146097 := by omega
  have hd2 : (x + 719468) % 146097 = doe := by omega
  rw [← hdoe]
  rw [hd2]
  simp only [Int.tdiv_eq_ediv_of_nonneg hd0]
  obtain ⟨yoe, hyoe⟩ : ∃ yoe, yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 := ⟨_, rfl⟩
  have hs := yoe_spec doe yoe hd0 hd1 hyoe
  rw [show yearOf doe = yoe from hyoe.symm]
  have hy0 : 0 ≤ doe - doe / 1460 + doe / 36524 - doe / 146096 := by omega
  simp only [Int.tdiv_eq_ediv_of_nonneg hy0]
  rw [← hyoe]
  have hv := core_valid ((x + 719468) / 146097) doe yoe hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hd1
  simp only [Int.tdiv_eq_ediv_of_nonneg hs.1]
  have hdoy : 0 ≤ doe - (365 * yoe + yoe / 4 - yoe / 100) := by omega
  have hq : 0 ≤ 5 * (doe - (365 * yoe + yoe / 4 - yoe / 100)) + 2 := by omega
  simp only [Int.tdiv_eq_ediv_of_nonneg hq]
  have hq2 : 0 ≤ 153 * ((5 * (doe - (365 * yoe + yoe / 4 - yoe / 100)) + 2) / 153) + 2 := by omega
  simp only [Int.tdiv_eq_ediv_of_nonneg hq2]
  have hdl : doe - (365 * yoe + yoe / 4 - yoe / 100) < 366 := by omega
  unfold core at hv ⊢
  simp only [] at hv ⊢
  generalize doe - (365 * yoe + yoe / 4 - yoe / 100) = doy at *
  generalize hmp : (5 * doy + 2) / 153 = mp at *
  generalize hq : (153 * mp + 2) / 5 = q at *
  generalize (x + 719468) / 146097 = era at *
  obtain ⟨hm1, hm2, hd1, hd2⟩ := hv
  have hm : mp + (if mp < 10 then 3 else -9) = if mp < 10 then mp + 3 else mp - 9 := by split <;> omega
  rw [hm] at *
  generalize hM : (if mp < 10 then mp + 3 else mp - 9) = M at *
  generalize hD : doy - q + 1 = D at *
  have hM1 : 1 ≤ M := by omega
  have hM2 : M ≤ 12 := by omega
  have hdim := dim_eq (yoe + era * 400 + if M ≤ 2 then 1 else 0) M hM1 hM2
  have hb := daysInMonth_bounds (yoe + era * 400 + if M ≤ 2 then 1 else 0) M.toNat
  have hD1 : 1 ≤ D := by omega
  have hD2 : D ≤ ((Month.Ordinal.days
      (Year.Offset.ofInt (yoe + era * 400 + if M ≤ 2 then 1 else 0)).isLeap
      (Internal.Bounded.LE.clip M (by decide))).val) := by
    rw [hdim]; omega
  rw [clip_val (by decide) M hM1 hM2]
  simp only [Month.Ordinal.clipDay]
  rw [clip_val (by decide) D hD1 (by omega)]
  have hn : ¬ (D > ((Month.Ordinal.days
      (Year.Offset.isLeap ((yoe + era * 400 + if M ≤ 2 then 1 else 0 : Int) : Year.Offset))
      (Internal.Bounded.LE.clip M (by decide))).val)) := by
    show ¬ (D > ((Month.Ordinal.days
      (Year.Offset.ofInt (yoe + era * 400 + if M ≤ 2 then 1 else 0)).isLeap
      (Internal.Bounded.LE.clip M (by decide))).val))
    omega
  simp only [hn, ↓reduceIte]
  rw [clip_val (lo := 1) (hi := 31) (by decide) D hD1 (by omega)]
  rfl

private theorem civilFromDays_eq (z : Int) :
    civilFromDays z = core ((z + 719468) / 146097) ((z + 719468) % 146097)
      (yearOf ((z + 719468) % 146097)) :=
  civil_eq (Day.Offset.ofInt z)

private def rawDays (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y % 400
  let doy := (153 * (if m > 2 then (m : Int) - 3 else (m : Int) + 9) + 2) / 5 + d - 1
  era * 146097 + (yoe * 365 + yoe / 4 - yoe / 100 + doy) - 719468

private theorem tdiv_floor_400 (a : Int) {_ : Decidable (a ≥ 0)} :
    (if a ≥ 0 then a else a - 399).tdiv 400 = a / 400 := by
  split
  · exact Int.tdiv_eq_ediv_of_nonneg ‹_›
  · have h : a - 399 = -(399 - a) := by omega
    rw [h, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    omega

private theorem clip_toInt {lo hi : Int} (h : lo ≤ hi) (v : Int) (h1 : lo ≤ v) (h2 : v ≤ hi) :
    (Internal.Bounded.LE.clip v h).toInt = v := clip_val h v h1 h2

private theorem clipDay_id (leap : Bool) (M : Month.Ordinal) (D : Day.Ordinal)
    (h : D.val ≤ (M.days leap).val) : Month.Ordinal.clipDay leap M D = D := by
  simp only [Month.Ordinal.clipDay]
  split <;> first | rfl | omega

private theorem days_eq (y : Int) (m d : Nat) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d)
    (hd2 : d ≤ daysInMonth y m) : daysFromCivil y m d = rawDays y m d := by
  have hb := daysInMonth_bounds y m
  have hdim := dim_eq y m (by omega) (by omega)
  rw [Int.toNat_natCast] at hdim
  have hmv : (Internal.Bounded.LE.clip (m : Int) (by decide : (1 : Int) ≤ 12)).toInt = m :=
    clip_toInt (lo := 1) (hi := 12) _ _ (by omega) (by omega)
  have hdv : (Internal.Bounded.LE.clip (d : Int) (by decide : (1 : Int) ≤ 31)).toInt = d :=
    clip_toInt (lo := 1) (hi := 31) _ _ (by omega) (by omega)
  have hday : Month.Ordinal.clipDay (Year.Offset.isLeap y)
      (Internal.Bounded.LE.clip (m : Int) (by decide)) (Internal.Bounded.LE.clip (d : Int) (by decide)) =
      Internal.Bounded.LE.clip (d : Int) (by decide) := by
    apply clipDay_id
    have : (Internal.Bounded.LE.clip (d : Int) (by decide : (1 : Int) ≤ 31)).val = d := hdv
    show _ ≤ (Month.Ordinal.days (Year.Offset.ofInt y).isLeap (Internal.Bounded.LE.clip (m : Int) (by decide))).val
    rw [this, hdim]
    omega
  unfold daysFromCivil
  simp only [PlainDate.ofYearMonthDayClip, PlainDate.toEpochDay, hday, hmv, hdv,
    Year.Offset.toInt, Year.Offset.ofInt, tdiv_floor_400]
  obtain ⟨y', hy'⟩ : ∃ y', y' = if (m : Int) > 2 then y else y - 1 := ⟨_, rfl⟩
  rw [← hy']
  simp only [Internal.UnitVal.toInt, Day.Offset.ofInt, rawDays]
  have h1 : 0 ≤ y' - y' / 400 * 400 := by omega
  have h2 : 0 ≤ 153 * ((m : Int) + if (m : Int) > 2 then -3 else 9) + 2 := by split <;> omega
  simp only [Int.tdiv_eq_ediv_of_nonneg h1, Int.tdiv_eq_ediv_of_nonneg h2]
  have hy2 : (if m ≤ 2 then y - 1 else y) = y' := by
    rw [hy']; split <;> split <;> omega
  rw [hy2]
  split <;> omega

theorem civilFromDays_valid (z : Int) :
    1 ≤ (civilFromDays z).2.1 ∧ (civilFromDays z).2.1 ≤ 12 ∧
    1 ≤ (civilFromDays z).2.2 ∧
    (civilFromDays z).2.2 ≤ daysInMonth (civilFromDays z).1 (civilFromDays z).2.1 := by
  rw [civilFromDays_eq]
  have hs := yoe_spec ((z + 719468) % 146097) _ (by omega) (by omega) rfl
  exact core_valid _ _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 (by omega)

private theorem core_days (era doe yoe : Int) (h0 : 0 ≤ yoe) (h1 : yoe ≤ 399)
    (h2 : 365 * yoe + yoe / 4 - yoe / 100 ≤ doe)
    (h3 : doe < 365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100 ∨ yoe = 399)
    (h4 : doe < 146097) :
    rawDays (core era doe yoe).1 (core era doe yoe).2.1 (core era doe yoe).2.2 =
      era * 146097 + doe - 719468 := by
  have hl : doe - (365 * yoe + yoe / 4 - yoe / 100) < 366 := by omega
  unfold core rawDays
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
  have hv := civilFromDays_valid z
  rw [days_eq _ _ _ hv.1 hv.2.1 hv.2.2.1 hv.2.2.2, civilFromDays_eq]
  have hs := yoe_spec ((z + 719468) % 146097) _ (by omega) (by omega) rfl
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
  rw [days_eq y m d hm1 hm2 hd1 hd2]
  unfold rawDays
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
      simp [daysInMonth_eq] at hd2 hdy <;> (try split at hd2) <;> omega
  have hb : 0 ≤ doy ∧ doy < 366 ∧
      (doy < 365 ∨ (yoe + 1) % 4 = 0 ∧ ((yoe + 1) % 100 ≠ 0 ∨ yoe + 1 = 400)) := by
    refine ⟨hb1.1, by omega, ?_⟩
    by_cases h : doy = 365
    · obtain ⟨hm, _⟩ := hb1.2.2 h
      subst hm
      have hl : isLeap y = true := by
        simp [daysInMonth_eq] at hd2
        split at hd2 <;> simp_all
      simp [isLeap_eq] at hl
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
  have hs := yoe_spec doe _ (by omega) hd2' rfl
  have hu := yoe_unique doe _ yoe hs.2.1 hyb.2.1 hs.2.2.1 hs.2.2.2 hd0 hd1
  rw [civilFromDays_eq]
  simp only [e, e1, e2]
  rw [hu]
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
    simp [Prod.ext_iff, daysInMonth_eq] at hdy hy' hd2 ⊢ <;> (repeat' split) <;>
      (repeat' (first | split at hd2 | split at hlt)) <;> omega

theorem daysInMonth_february (y : Int) : daysInMonth y 2 = if isLeap y then 29 else 28 := by
  simp [daysInMonth_eq]

theorem daysInMonth_thirty (y : Int) (m : Nat) (h : m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11) :
    daysInMonth y m = 30 := by
  rcases h with h | h | h | h <;> subst h <;> simp [daysInMonth_eq]

theorem daysInMonth_thirty_one (y : Int) (m : Nat) (h : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 8 ∨ m = 10 ∨ m = 12) :
    daysInMonth y m = 31 := by
  rcases h with h | h | h | h | h | h | h <;> subst h <;> simp [daysInMonth_eq]

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
    · dsimp only; simp [daysInMonth_eq]

theorem daysFromCivil_nextDay (y : Int) (m d : Nat) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d)
    (hd2 : d ≤ daysInMonth y m) :
    daysFromCivil (nextDay (y, m, d)).1 (nextDay (y, m, d)).2.1 (nextDay (y, m, d)).2.2 =
      daysFromCivil y m d + 1 := by
  have hv := nextDay_valid y m d hm1 hm2
  rw [days_eq _ _ _ hv.1 hv.2.1 hv.2.2.1 hv.2.2.2, days_eq y m d hm1 hm2 hd1 hd2]
  simp only [nextDay]
  by_cases hlt : d < daysInMonth y m
  · simp only [hlt, ite_true]
    unfold rawDays
    simp only []
    split <;> omega
  · simp only [hlt, ite_false]
    have hmc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
        m = 10 ∨ m = 11 ∨ m = 12 := by omega
    rcases hmc with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      simp [daysInMonth_eq, isLeap_eq, rawDays] at hd2 hlt ⊢ <;>
      (repeat' (first | split at hd2 | split at hlt)) <;> omega

theorem daysFromCivil_epoch : daysFromCivil 1970 1 1 = 0 := by decide +kernel

theorem civilFromDays_zero : civilFromDays 0 = (1970, 1, 1) := by decide +kernel

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
