/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Series

namespace Inkproof.Core

universe u v

private theorem zip_map_fst_snd {α : Type u} {β : Type v} (l : List (α × β)) :
    (l.map (·.1)).zip (l.map (·.2)) = l := by
  have := List.zip_unzip l
  rwa [List.unzip_eq_map] at this

namespace Series

variable {α : Type u} {β : Type v} [LE α]

section Validated

variable [DecidableLE α] [Std.IsPreorder α] {xs : Array α} {vs : Array (Option β)}

/-- An accepted series holds exactly the arrays it was given. -/
theorem ofArrays?_eq_ok {s : Series α β} (h : ofArrays? xs vs = .ok s) :
    s.xs = xs ∧ s.values = vs := by
  unfold ofArrays? at h
  split at h
  · split at h
    · contradiction
    · cases h; exact ⟨rfl, rfl⟩
  · contradiction

/-- `ofArrays?` accepts exactly the arrays of equal size whose x-values never decrease. -/
theorem ofArrays?_ok_iff : (∃ s : Series α β, ofArrays? xs vs = .ok s) ↔
    vs.size = xs.size ∧ Sorted xs := by
  constructor
  · rintro ⟨s, h⟩
    obtain ⟨hx, hv⟩ := ofArrays?_eq_ok h
    exact ⟨hv ▸ hx ▸ s.size_eq, hx ▸ s.sorted⟩
  · rintro ⟨hs, hsorted⟩
    have hnone : Internal.firstAdjacentFailure (fun a b => decide (a ≤ b)) xs 0 = none :=
      Internal.firstAdjacentFailure_eq_none_of fun i _ hi => by
        simpa using hsorted i (i + 1) (by omega) hi
    unfold ofArrays?
    simp only [hs, dite_true]
    split
    · simp_all
    · exact ⟨_, rfl⟩

/-- A reported descent is the first index whose successor's x-value is smaller. -/
theorem ofArrays?_eq_error_unsorted {i : Nat} (h : ofArrays? xs vs = .error (.unsorted i)) :
    ∃ hi : i + 1 < xs.size, ¬ xs[i] ≤ xs[i + 1] ∧
      ∀ j (hj : j < i), xs[j]'(by omega) ≤ xs[j + 1]'(by omega) := by
  unfold ofArrays? at h
  split at h
  · split at h
    · rename_i k hk
      cases h
      obtain ⟨hi, hfalse, -, hbefore⟩ := Internal.firstAdjacentFailure_eq_some hk
      exact ⟨hi, by simpa using hfalse, fun j hj => by simpa using hbefore j (Nat.zero_le j) hj⟩
    · contradiction
  · simp at h

/-- A size mismatch is reported only when the sizes differ, and reports both. -/
theorem ofArrays?_eq_error_sizeMismatch {a b : Nat}
    (h : ofArrays? xs vs = .error (.sizeMismatch a b)) :
    a = xs.size ∧ b = vs.size ∧ vs.size ≠ xs.size := by
  unfold ofArrays? at h
  split at h
  · split at h <;> simp_all
  · rename_i hs
    cases h
    exact ⟨rfl, rfl, hs⟩

/-- An accepted series holds exactly the points it was given. -/
theorem ofPoints?_eq_ok {ps : Array (α × Option β)} {s : Series α β}
    (h : ofPoints? ps = .ok s) : s.points = ps := by
  obtain ⟨hx, hv⟩ := ofArrays?_eq_ok h
  apply Array.toList_inj.mp
  simp [points, hx, hv, Array.toList_zip, zip_map_fst_snd]

/-- `ofPoints?` accepts exactly the points whose x-values never decrease. -/
theorem ofPoints?_ok_iff {ps : Array (α × Option β)} :
    (∃ s : Series α β, ofPoints? ps = .ok s) ↔ Sorted (ps.map (·.1)) := by
  simp [ofPoints?, ofArrays?_ok_iff]

end Validated

section Sorting

variable [DecidableLE α] [Std.IsLinearOrder α] {ps : Array (α × Option β)}

theorem points_ofUnsorted :
    (ofUnsorted ps).points.toList = ps.toList.mergeSort (fun p q => decide (p.1 ≤ q.1)) := by
  simp [ofUnsorted, points, zip_map_fst_snd]

private theorem le_trans_bool (a b c : α × Option β) :
    decide (a.1 ≤ b.1) = true → decide (b.1 ≤ c.1) = true → decide (a.1 ≤ c.1) = true := by
  simp only [decide_eq_true_eq]
  exact Std.IsPreorder.le_trans _ _ _

private theorem le_total_bool (a b : α × Option β) :
    (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Std.IsLinearPreorder.le_total _ _

/-- `ofUnsorted` keeps every point, rearranging but neither adding nor dropping any. -/
theorem ofUnsorted_perm : (ofUnsorted ps).points.toList.Perm ps.toList := by
  rw [points_ofUnsorted]
  exact List.mergeSort_perm _ _

/-- `ofUnsorted` is stable: two points already in x-order keep their relative order, so points with
equal x-values stay in input order. -/
theorem ofUnsorted_stable {p q : α × Option β} (hpq : p.1 ≤ q.1) (h : [p, q].Sublist ps.toList) :
    [p, q].Sublist (ofUnsorted ps).points.toList := by
  rw [points_ofUnsorted]
  exact List.pair_sublist_mergeSort le_trans_bool le_total_bool (by simpa using hpq) h

end Sorting

end Series

end Inkproof.Core
