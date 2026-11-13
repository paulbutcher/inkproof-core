/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Query
import Inkproof.Core.Proofs.Segmented
import Inkproof.Core.Proofs.Pyramid

/-! PROOF-1 over x-ranges (`Pyramid.query_lowerBound`) and PROOF-3
(`SegmentedPyramid.getElem_query`, `SegmentedPyramid.queryOverlapping_eq`,
`Segmented.flatten_filter_segments`). -/

namespace Inkproof.Core

universe u v w

private theorem list_filter_eq_extract {γ : Type u} (p : γ → Bool) :
    ∀ (l : List γ) (a b : Nat),
      (∀ i (hi : i < l.length), p l[i] = decide (a ≤ i ∧ i < b)) →
      l.filter p = (l.drop a).take (b - a)
  | [], _, _, _ => by simp
  | y :: l, a, b, h => by
    have hy := h 0 (by simp)
    have htail := fun i (hi : i < l.length) => h (i + 1) (by simp; omega)
    simp only [List.getElem_cons_zero] at hy
    simp only [List.getElem_cons_succ] at htail
    rw [List.filter_cons]
    cases a with
    | zero =>
      cases b with
      | zero =>
        have hy' : p y = false := by rw [hy]; simp
        simp only [hy', Bool.false_eq_true, ite_false]
        rw [list_filter_eq_extract p l 0 0 (fun i hi => by
          rw [htail i hi]; exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩)]
        simp
      | succ b =>
        have hy' : p y = true := by rw [hy]; simp
        simp only [hy', ite_true, List.drop_zero, Nat.sub_zero, List.take_succ_cons]
        rw [list_filter_eq_extract p l 0 b (fun i hi => by
          rw [htail i hi]; exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩)]
        simp
    | succ a =>
      have hy' : p y = false := by rw [hy]; simp
      simp only [hy', Bool.false_eq_true, ite_false, List.drop_succ_cons]
      rw [list_filter_eq_extract p l a (b - 1) (fun i hi => by
        rw [htail i hi]; exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩)]
      congr 1
      omega

namespace Series

variable {α : Type u} {β : Type v} [LE α] [DecidableLE α] [Std.IsPreorder α]

theorem lowerBoundFrom_spec {xs : Array α} (hs : Sorted xs) (x : α) (lo hi : Nat)
    (hle : lo ≤ hi) (hhi : hi ≤ xs.size)
    (hbelow : ∀ i (h : i < xs.size), i < lo → ¬ x ≤ xs[i])
    (habove : ∀ i (h : i < xs.size), hi ≤ i → x ≤ xs[i]) :
    lowerBoundFrom xs x lo hi ≤ hi ∧
      ∀ i (h : i < xs.size), i < lowerBoundFrom xs x lo hi ↔ ¬ x ≤ xs[i] := by
  unfold lowerBoundFrom
  induction lo, hi using lowerBoundFromBy.induct xs.size (fun i h => xs[i]) x with
  | case1 lo hi hlt mid hmid hx ih =>
    rw [lowerBoundFromBy]
    simp only [hlt, ite_true, mid, hmid, dite_true, hx]
    have := ih (by omega) (by omega) hbelow (fun i h hi => by
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt'
      · exact hx
      · exact Std.IsPreorder.le_trans _ _ _ hx (hs _ _ hlt' h))
    exact ⟨Nat.le_trans this.1 (by omega), this.2⟩
  | case2 lo hi hlt mid hmid hx ih =>
    rw [lowerBoundFromBy]
    simp only [hlt, ite_true, mid, hmid, dite_true, hx, ite_false]
    exact ih (by omega) hhi (fun i h hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt' | rfl
      · by_cases hlo : i < lo
        · exact hbelow i h hlo
        · intro hxi
          exact hx (Std.IsPreorder.le_trans _ _ _ hxi (hs _ _ (by omega) hmid))
      · exact hx) habove
  | case3 lo hi hlt mid hmid =>
    exact absurd hhi (by omega)
  | case4 lo hi hlt =>
    rw [lowerBoundFromBy]
    simp only [hlt, ite_false]
    refine ⟨hle, fun i h => ⟨hbelow i h, fun hx => ?_⟩⟩
    by_cases hi : i < lo
    · exact hi
    · exact absurd (habove i h (by omega)) hx

omit [DecidableLE α] [Std.IsPreorder α] in
/-- Point `i` pairs the `i`th x-value with the `i`th value. -/
theorem getElem_points (s : Series α β) {i : Nat} (h : i < s.points.size) :
    s.points[i] = (s.xs[i]'(by simpa [size_points, size] using h),
      s.values[i]'(by simpa [size_points, size, s.size_eq] using h)) := by
  simp [points]

/-- The points before `lowerBound s x` are exactly those whose x-value is below `x`. -/
theorem lt_lowerBound_iff (s : Series α β) (x : α) {i : Nat} (h : i < s.size) :
    i < s.lowerBound x ↔ ¬ x ≤ s.xs[i] :=
  (lowerBoundFrom_spec s.sorted x 0 s.size (Nat.zero_le _) (Nat.le_refl _)
    (fun _ _ hi => absurd hi (Nat.not_lt_zero _)) (fun _ h hi => absurd h (by
      unfold Series.size at hi; omega))).2 i h

theorem lowerBound_le_size (s : Series α β) (x : α) : s.lowerBound x ≤ s.size :=
  (lowerBoundFrom_spec s.sorted x 0 s.size (Nat.zero_le _) (Nat.le_refl _)
    (fun _ _ hi => absurd hi (Nat.not_lt_zero _)) (fun _ h hi => absurd h (by
      unfold Series.size at hi; omega))).1

private theorem inRange_getElem_points (s : Series α β) (x₀ x₁ : α) {i : Nat}
    (hi : i < s.points.size) :
    inRange x₀ x₁ s.points[i] = decide (s.lowerBound x₀ ≤ i ∧ i < s.lowerBound x₁) := by
  have hi' : i < s.size := by simpa [size_points] using hi
  rw [getElem_points]
  simp only [inRange]
  have h₀ := lt_lowerBound_iff s x₀ hi'
  have h₁ := lt_lowerBound_iff s x₁ hi'
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨Nat.not_lt.mp fun h => h₀.mp h ha, h₁.mpr hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨Decidable.of_not_not fun hn => absurd (h₀.mpr hn) (Nat.not_lt.mpr ha), h₁.mp hb⟩

/-- In a sorted series, the points with x-values in `[x₀, x₁)` are exactly those between the two
lower bounds. -/
theorem filter_inRange (s : Series α β) (x₀ x₁ : α) :
    s.points.filter (inRange x₀ x₁) = s.points.extract (s.lowerBound x₀) (s.lowerBound x₁) := by
  apply Array.toList_inj.mp
  rw [Array.toList_filter, Array.toList_extract, List.extract_eq_take_drop]
  apply list_filter_eq_extract
  intro i hi
  simp only [Array.getElem_toList]
  exact inRange_getElem_points s x₀ x₁ hi

end Series

namespace Pyramid

variable {α : Type u} {β : Type v} {M : Type w} [LE α] [DecidableLE α] [Std.IsPreorder α]
  [Aggregate M] [LawfulAggregate M]

/-- PROOF-1 over x-ranges: querying between the lower bounds of `x₀` and `x₁` merges exactly the
points with x-values in `[x₀, x₁)`, in order. -/
theorem query_lowerBound (s : Series α β) (b : Nat) (h : 2 ≤ b) (m : α × Option β → M)
    (x₀ x₁ : α) :
    (ofMeasure b h m s.points).query (s.lowerBound x₀) (s.lowerBound x₁) =
      Aggregate.fold m (s.points.filter (Series.inRange x₀ x₁)) := by
  rw [query_ofMeasure, Series.filter_inRange]

end Pyramid

namespace SegmentedPyramid

variable {α : Type u} {β : Type v} {M : Type w} [LE α] [DecidableLE α] [Aggregate M]

omit [DecidableLE α] in
theorem size_query [DecidableLE α] (sp : SegmentedPyramid α β M) (x₀ x₁ : α) :
    (sp.query x₀ x₁).size = sp.segmented.numSegments := by
  simp [query, sp.size_pyramids]

/-- PROOF-3: result `k` merges exactly the points of segment `k` with x-values in `[x₀, x₁)`, so no
result combines points from two segments. -/
theorem getElem_query [Std.IsPreorder α] [LawfulAggregate M] (sp : SegmentedPyramid α β M)
    (x₀ x₁ : α) {k : Nat} (hk : k < (sp.query x₀ x₁).size) :
    (sp.query x₀ x₁)[k] =
      Aggregate.fold sp.measure ((sp.segmented.segment k).points.filter (Series.inRange x₀ x₁)) := by
  have hk' : k < sp.pyramids.size := by simpa [query] using hk
  simp only [query, Array.getElem_mapIdx]
  rw [sp.pyramids_eq k hk', Pyramid.query_lowerBound]

private theorem map_filter_eq_filterMap {γ : Type u} {δ : Type v} (p : γ → Bool) (f : γ → δ) :
    ∀ l : List γ, (l.filter p).map f = l.filterMap fun k => if p k then some (f k) else none
  | [] => rfl
  | y :: l => by
    rw [List.filter_cons, List.filterMap_cons]
    cases p y <;> simp [map_filter_eq_filterMap p f l]

private theorem filterMap_congr {γ : Type u} {δ : Type v} {f g : γ → Option δ} :
    ∀ {l : List γ}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | y :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h y (by simp),
      filterMap_congr fun x hx => h x (by simp [hx])]

/-- Restricts a `filterMap` over `range n` to the indices where `f` may be `some`. -/
private theorem filterMap_range_eq {γ : Type u} (f : Nat → Option γ) {n first last : Nat}
    (hlo : ∀ k, k < first → f k = none) (hhi : ∀ k, last ≤ k → f k = none)
    (hn : ∀ k, n ≤ k → f k = none) :
    (List.range n).filterMap f = (List.range' first (last - first)).filterMap f := by
  by_cases hlf : last < first
  · rw [show last - first = 0 by omega, List.range'_zero, List.filterMap_nil]
    exact List.filterMap_eq_nil_iff.mpr fun k _ => by
      by_cases hk : k < first
      · exact hlo k hk
      · exact hhi k (by omega)
  have hfl : first ≤ last := by omega
  have split (s m k : Nat) : List.range' s (m + k) = List.range' s m ++ List.range' (s + m) k := by
    simp
  obtain ⟨N, hN₁, hN₂⟩ : ∃ N, n ≤ N ∧ last ≤ N := ⟨n + last, by omega, by omega⟩
  have e₁ : List.range N = List.range n ++ List.range' n (N - n) := by
    have h := split 0 n (N - n)
    rw [Nat.zero_add, Nat.add_sub_cancel' hN₁] at h
    rw [List.range_eq_range', List.range_eq_range', h]
  have e₂ : List.range N =
      List.range' 0 first ++ List.range' first (last - first) ++ List.range' last (N - last) := by
    have h₁ := split 0 first (last - first)
    rw [Nat.zero_add, Nat.add_sub_cancel' hfl] at h₁
    have h₂ := split 0 last (N - last)
    rw [Nat.zero_add, Nat.add_sub_cancel' hN₂] at h₂
    rw [List.range_eq_range', h₂, h₁]
  have none_of {s m : Nat} (h : ∀ k, s ≤ k → k < s + m → f k = none) :
      (List.range' s m).filterMap f = [] :=
    List.filterMap_eq_nil_iff.mpr fun k hk => by
      rw [List.mem_range'_1] at hk
      exact h k hk.1 hk.2
  have h₁ := congrArg (List.filterMap f) e₁
  have h₂ := congrArg (List.filterMap f) e₂
  simp only [List.filterMap_append] at h₁ h₂
  rw [none_of (fun k hk _ => hn k hk), List.append_nil] at h₁
  rw [none_of (fun k _ hk => hlo k (by omega)), none_of (fun k hk _ => hhi k hk), List.nil_append,
    List.append_nil] at h₂
  rw [← h₁, h₂]

omit [DecidableLE α] [Aggregate M] in
private theorem sorted_breaks (g : Segmented α β) : Sorted g.breaks :=
  sorted_of_le_succ fun i h => Nat.le_of_lt (g.breaks_increasing i h)

omit [DecidableLE α] [Aggregate M] in
private theorem lowerBoundFrom_breaks (g : Segmented α β) (x : Nat) :
    Series.lowerBoundFrom g.breaks x 0 g.breaks.size ≤ g.breaks.size ∧
      ∀ i (h : i < g.breaks.size),
        i < Series.lowerBoundFrom g.breaks x 0 g.breaks.size ↔ ¬ x ≤ g.breaks[i] :=
  Series.lowerBoundFrom_spec (sorted_breaks g) x 0 _ (Nat.zero_le _) (Nat.le_refl _)
    (fun _ _ hi => absurd hi (Nat.not_lt_zero _)) (fun _ h hi => absurd h (by omega))

variable [Std.IsPreorder α]

omit [Aggregate M] [DecidableLE α] [Std.IsPreorder α] in
private theorem size_points_segment (g : Segmented α β) (k : Nat) :
    (g.segment k).points.size = g.segmentStop k - g.segmentStart k := by
  have hstop := g.segmentStop_le_size k
  simp [Segmented.segment, Series.points_slice, Series.size_points]; omega

omit [Aggregate M] in
/-- Point `i` of segment `k` is in range exactly when `i` lies between the series' lower bounds,
shifted to the segment's start. -/
private theorem inRange_getElem_segment (g : Segmented α β) (x₀ x₁ : α) (k : Nat) {i : Nat}
    (hi : i < (g.segment k).points.size) :
    Series.inRange x₀ x₁ (g.segment k).points[i] =
      decide (max (g.series.lowerBound x₀) (g.segmentStart k) - g.segmentStart k ≤ i ∧
        i < min (g.series.lowerBound x₁) (g.segmentStop k) - g.segmentStart k) := by
  have hstop := g.segmentStop_le_size k
  have hss := g.segmentStart_le_segmentStop k
  have hsize := size_points_segment g k
  simp only [Segmented.segment, Series.points_slice, Array.getElem_extract]
  rw [Series.inRange_getElem_points]
  exact decide_eq_decide.mpr (by omega)

omit [Aggregate M] in
private theorem filter_inRange_segment (g : Segmented α β) (x₀ x₁ : α) (k : Nat) :
    (g.segment k).points.filter (Series.inRange x₀ x₁) =
      (g.segment k).points.extract
        (max (g.series.lowerBound x₀) (g.segmentStart k) - g.segmentStart k)
        (min (g.series.lowerBound x₁) (g.segmentStop k) - g.segmentStart k) := by
  apply Array.toList_inj.mp
  rw [Array.toList_filter, Array.toList_extract, List.extract_eq_take_drop]
  apply list_filter_eq_extract
  intro i hi
  simp only [Array.getElem_toList]
  exact inRange_getElem_segment g x₀ x₁ k (by simpa using hi)

omit [Aggregate M] in
private theorem any_inRange_segment (g : Segmented α β) (x₀ x₁ : α) (k : Nat) :
    (g.segment k).points.any (Series.inRange x₀ x₁) =
      decide (max (g.series.lowerBound x₀) (g.segmentStart k) - g.segmentStart k <
        min (g.series.lowerBound x₁) (g.segmentStop k) - g.segmentStart k) := by
  have hsize := size_points_segment g k
  rw [Bool.eq_iff_iff, Array.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [inRange_getElem_segment, decide_eq_true_iff] at h
    omega
  · intro h
    refine ⟨max (g.series.lowerBound x₀) (g.segmentStart k) - g.segmentStart k, by omega, ?_⟩
    rw [inRange_getElem_segment, decide_eq_true_iff]
    omega

/-- `queryOverlapping` is `query` with the segments holding no point in `[x₀, x₁)` left out, and
each result paired with its segment index. -/
theorem queryOverlapping_eq [LawfulAggregate M] (sp : SegmentedPyramid α β M) (x₀ x₁ : α) :
    sp.queryOverlapping x₀ x₁ =
      ((List.range sp.segmented.numSegments).filter fun k =>
          (sp.segmented.segment k).points.any (Series.inRange x₀ x₁)).toArray.map fun k =>
        (k, Aggregate.fold sp.measure
          ((sp.segmented.segment k).points.filter (Series.inRange x₀ x₁))) := by
  have hfirst := lowerBoundFrom_breaks sp.segmented (sp.segmented.series.lowerBound x₀ + 1)
  have hlast := lowerBoundFrom_breaks sp.segmented (sp.segmented.series.lowerBound x₁)
  apply Array.toList_inj.mp
  unfold queryOverlapping
  simp only [Array.toList_filterMap, Array.toList_range', Array.toList_map]
  rw [map_filter_eq_filterMap]
  refine Eq.trans (filterMap_range_eq (n := sp.segmented.numSegments) _ ?_ ?_ ?_).symm ?_
  · intro k hk
    have hkb : k < sp.segmented.breaks.size := by omega
    have hstop := (hfirst.2 k hkb).mp hk
    split
    · split
      · simp only [Segmented.segmentStop, Array.getElem?_eq_getElem hkb, Option.getD_some] at *
        omega
      · rfl
    · rfl
  · intro k hk
    split
    · rename_i hkp
      have hkb : k - 1 < sp.segmented.breaks.size := by
        rw [sp.size_pyramids] at hkp; unfold Segmented.numSegments at hkp; split at hkp <;> omega
      have hstart := Decidable.of_not_not ((not_congr (hlast.2 (k - 1) hkb)).mp (by omega))
      split
      · simp only [Segmented.segmentStart, show k ≠ 0 by omega, ite_false,
          Array.getElem?_eq_getElem hkb, Option.getD_some] at *
        omega
      · rfl
    · rfl
  · intro k hk
    split
    · rename_i hkp; rw [sp.size_pyramids] at hkp; omega
    · rfl
  · apply filterMap_congr
    intro k hk
    have hkp : k < sp.pyramids.size := by rw [sp.size_pyramids]; simpa using hk
    rw [dite_eq_left_of_eq_true (eq_true hkp), any_inRange_segment, filter_inRange_segment, sp.pyramids_eq k hkp,
      Pyramid.query_ofMeasure]
    by_cases h : max (sp.segmented.series.lowerBound x₀) (sp.segmented.segmentStart k) -
        sp.segmented.segmentStart k <
      min (sp.segmented.series.lowerBound x₁) (sp.segmented.segmentStop k) -
        sp.segmented.segmentStart k <;> simp [h]

end SegmentedPyramid

namespace Segmented

variable {α : Type u} {β : Type v} [LE α] [DecidableLE α]

/-- The in-range points of the segments, in order, are exactly the in-range points of the series:
each lies in one segment's result and no other. -/
theorem flatten_filter_segments (g : Segmented α β) (x₀ x₁ : α) :
    (g.segments.toList.map fun s => (s.points.filter (Series.inRange x₀ x₁)).toList).flatten =
      (g.series.points.filter (Series.inRange x₀ x₁)).toList := by
  rw [Array.toList_filter, ← flatten_segments, List.filter_flatten, List.map_map]
  simp [Function.comp_def]

end Segmented

end Inkproof.Core
