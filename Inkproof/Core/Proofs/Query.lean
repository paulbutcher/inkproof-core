/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Query
import Inkproof.Core.Proofs.Segmented
import Inkproof.Core.Proofs.Pyramid

/-! PROOF-1 over x-ranges (`Pyramid.query_lowerBound`) and PROOF-3
(`SegmentedPyramid.getElem_query`, `Segmented.flatten_filter_segments`). -/

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
  induction lo, hi using lowerBoundFrom.induct xs x with
  | case1 lo hi hlt mid hmid hx ih =>
    rw [lowerBoundFrom]
    simp only [hlt, ite_true, mid, hmid, dite_true, hx]
    have := ih (by omega) (by omega) hbelow (fun i h hi => by
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt'
      · exact hx
      · exact Std.IsPreorder.le_trans _ _ _ hx (hs _ _ hlt' h))
    exact ⟨Nat.le_trans this.1 (by omega), this.2⟩
  | case2 lo hi hlt mid hmid hx ih =>
    rw [lowerBoundFrom]
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
    rw [lowerBoundFrom]
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

/-- In a sorted series, the points with x-values in `[x₀, x₁)` are exactly those between the two
lower bounds. -/
theorem filter_inRange (s : Series α β) (x₀ x₁ : α) :
    s.points.filter (inRange x₀ x₁) = s.points.extract (s.lowerBound x₀) (s.lowerBound x₁) := by
  apply Array.toList_inj.mp
  rw [Array.toList_filter, Array.toList_extract, List.extract_eq_take_drop]
  apply list_filter_eq_extract
  intro i hi
  have hi' : i < s.size := by simpa [size_points] using hi
  simp only [Array.getElem_toList]
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
