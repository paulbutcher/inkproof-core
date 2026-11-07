/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Segmented
import Inkproof.Core.Proofs.Series

namespace Inkproof.Core

universe u v

namespace Series

variable {α : Type u} {β : Type v} [LE α]

theorem points_slice (s : Series α β) (lo hi : Nat) :
    (s.slice lo hi).points = s.points.extract lo hi := by
  apply Array.ext
  · simp [points, slice, s.size_eq]
  · intro i h₁ h₂
    simp [points, slice]

theorem size_points (s : Series α β) : s.points.size = s.size := by
  simp [points, size, s.size_eq]

end Series

namespace Segmented

variable {α : Type u} {β : Type v} [LE α]

theorem segmentStart_zero (g : Segmented α β) : g.segmentStart 0 = 0 := rfl

theorem segmentStart_succ (g : Segmented α β) (k : Nat) :
    g.segmentStart (k + 1) = g.segmentStop k := rfl

theorem segmentStop_le_size (g : Segmented α β) (k : Nat) : g.segmentStop k ≤ g.series.size := by
  unfold segmentStop
  by_cases h : k < g.breaks.size
  · simp [h, Nat.le_of_lt (g.breaks_bounded k h).2]
  · simp [h]

theorem segmentStart_le_segmentStop (g : Segmented α β) (k : Nat) :
    g.segmentStart k ≤ g.segmentStop k := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    rw [segmentStart_succ]
    unfold segmentStop
    by_cases h : k + 1 < g.breaks.size
    · simp [h, Nat.lt_of_succ_lt h, Nat.le_of_lt (g.breaks_increasing k h)]
    · by_cases h' : k < g.breaks.size
      · simp [h, h', Nat.le_of_lt (g.breaks_bounded k h').2]
      · simp [h, h']

/-- Every segment below `numSegments` holds at least one point. -/
theorem segmentStart_lt_segmentStop (g : Segmented α β) {k : Nat} (hk : k < g.numSegments) :
    g.segmentStart k < g.segmentStop k := by
  unfold numSegments at hk
  split at hk
  · omega
  · rename_i hsize
    cases k with
    | zero =>
      unfold segmentStart segmentStop
      by_cases h : 0 < g.breaks.size
      · simp [h, (g.breaks_bounded 0 h).1]
      · simp [h]; omega
    | succ k =>
      rw [segmentStart_succ]
      unfold segmentStop
      by_cases h : k + 1 < g.breaks.size
      · simp [h, Nat.lt_of_succ_lt h, g.breaks_increasing k h]
      · have h' : k < g.breaks.size := by omega
        simp [h, h', (g.breaks_bounded k h').2]

private theorem flatten_extract_chain {γ : Type u} (a : Array γ) (f : Nat → Nat) (h0 : f 0 = 0)
    (hmono : ∀ k, f k ≤ f (k + 1)) (n : Nat) :
    ((List.range n).map fun k => (a.extract (f k) (f (k + 1))).toList).flatten =
      (a.extract 0 (f n)).toList := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hle : f 0 ≤ f n := by
      clear ih
      induction n with
      | zero => exact Nat.le_refl _
      | succ m ihm => exact Nat.le_trans ihm (hmono m)
    rw [List.range_succ, List.map_append, List.flatten_append, ih]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [← Array.toList_append, Array.extract_append_extract]
    simp [Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right (hmono n)]

/-- The segments, in order, hold exactly the points of the series: nothing is lost, repeated or
reordered by segmenting. -/
theorem flatten_segments (g : Segmented α β) :
    (g.segments.toList.map (·.points.toList)).flatten = g.series.points.toList := by
  have hchain := flatten_extract_chain g.series.points g.segmentStart (segmentStart_zero g)
    (fun k => by rw [segmentStart_succ]; exact segmentStart_le_segmentStop g k) g.numSegments
  simp only [segments, Array.toList_map, Array.toList_range]
  have : (fun k => (g.segment k).points.toList) =
      (fun k => (g.series.points.extract (g.segmentStart k) (g.segmentStart (k + 1))).toList) := by
    funext k
    simp only [segment]
    rw [Series.points_slice, segmentStart_succ]
  rw [List.map_map, Function.comp_def, this, hchain]
  unfold numSegments
  split
  · rename_i h
    rw [Array.extract_eq_self_of_le (by simp [Series.size_points, h, segmentStart_zero])]
  · rw [segmentStart_succ]
    unfold segmentStop
    simp only [Array.getElem?_eq_none (Nat.le_refl _), Option.getD_none]
    rw [Array.extract_eq_self_of_le (by simp [Series.size_points])]

/-- `splitWherePoints` breaks exactly before each point that `gap` separates from its
predecessor. -/
theorem mem_breaks_splitWherePoints (s : Series α β)
    (gap : (α × Option β) → (α × Option β) → Bool) (b : Nat) :
    b ∈ (splitWherePoints s gap).breaks ↔
      ∃ h : 0 < b ∧ b < s.size,
        gap (s.xs[b - 1]'(by unfold Series.size at h; omega),
            s.values[b - 1]'(by rw [s.size_eq]; unfold Series.size at h; omega))
          (s.xs[b]'h.2, s.values[b]'(by rw [s.size_eq]; exact h.2)) = true := by
  simp only [splitWherePoints, List.mem_toArray, List.mem_filter, List.mem_range']
  constructor
  · rintro ⟨⟨i, hi, hb⟩, hgap⟩
    have h : 0 < b ∧ b < s.size := by omega
    rw [dite_eq_left_of_eq_true (eq_true ⟨h.2, h.1⟩)] at hgap
    exact ⟨h, hgap⟩
  · rintro ⟨h, hgap⟩
    exact ⟨⟨b - 1, by omega, by omega⟩, by rw [dite_eq_left_of_eq_true (eq_true ⟨h.2, h.1⟩)]; exact hgap⟩

/-- `splitWhere` breaks exactly before each point whose x-value `gap` separates from its
predecessor's. -/
theorem mem_breaks_splitWhere (s : Series α β) (gap : α → α → Bool) (b : Nat) :
    b ∈ (splitWhere s gap).breaks ↔
      ∃ h : 0 < b ∧ b < s.size,
        gap (s.xs[b - 1]'(by unfold Series.size at h; omega)) (s.xs[b]'h.2) = true :=
  mem_breaks_splitWherePoints s _ b

/-- An accepted segmentation holds exactly the series and breaks it was given. -/
theorem ofBreaks?_eq_ok {s : Series α β} {bs : Array Nat} {g : Segmented α β}
    (h : ofBreaks? s bs = .ok g) : g.series = s ∧ g.breaks = bs := by
  unfold ofBreaks? at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · cases h; exact ⟨rfl, rfl⟩

/-- `ofBreaks?` accepts exactly the breaks that increase strictly and lie strictly inside the
series. -/
theorem ofBreaks?_ok_iff {s : Series α β} {bs : Array Nat} :
    (∃ g, ofBreaks? s bs = .ok g) ↔
      (∀ i (h : i + 1 < bs.size), bs[i] < bs[i + 1]) ∧
      (∀ i (h : i < bs.size), 0 < bs[i] ∧ bs[i] < s.size) := by
  constructor
  · rintro ⟨g, h⟩
    obtain ⟨rfl, rfl⟩ := ofBreaks?_eq_ok h
    exact ⟨g.breaks_increasing, g.breaks_bounded⟩
  · rintro ⟨hinc, hbound⟩
    have hnone : Internal.firstAdjacentFailure (fun a b => decide (a < b)) bs 0 = none :=
      Internal.firstAdjacentFailure_eq_none_of fun i _ hi => by simpa using hinc i hi
    have hfind : bs.find? (fun b => !(0 < b && b < s.size)) = none := by
      rw [Array.find?_eq_none]
      intro b hb
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hb
      have := hbound i hi
      simp; omega
    unfold ofBreaks?
    split
    · simp_all
    · split
      · rename_i hsome
        rw [hfind] at hsome
        contradiction
      · exact ⟨_, rfl⟩

end Segmented

end Inkproof.Core
