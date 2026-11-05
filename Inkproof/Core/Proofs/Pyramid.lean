/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Pyramid
import Inkproof.Core.Proofs.Aggregate

/-! PROOF-1 (`Pyramid.query_eq`, `Pyramid.query_ofMeasure`) and PROOF-2
(`Pyramid.mem_node_iff`, `Pyramid.div_lt_size_levels`, `Pyramid.getElem_levels`,
`Pyramid.getElem_levels_succ`). -/

namespace Inkproof.Core

universe u v

open Aggregate (empty merge foldRange)

namespace Aggregate

variable {M : Type u} [Aggregate M]

theorem foldRange_eq_extract (a : Array M) (lo hi : Nat) :
    foldRange a lo hi = (a.extract lo hi).foldl merge empty :=
  Array.foldl_eq_foldl_extract

theorem foldRange_of_le (a : Array M) {lo hi : Nat} (h : hi ≤ lo) : foldRange a lo hi = empty := by
  rw [foldRange_eq_extract, Array.extract_eq_empty_of_le (by omega)]
  rfl

theorem foldRange_of_size_le (a : Array M) {lo hi : Nat} (h : a.size ≤ lo) :
    foldRange a lo hi = empty := by
  rw [foldRange_eq_extract, Array.extract_eq_empty_of_le (by omega)]
  rfl

variable [LawfulAggregate M]

private theorem foldl_merge_from (a : M) (l : List M) :
    l.foldl merge a = merge a (l.foldl merge empty) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, LawfulAggregate.empty_merge]
    rw [ih, ih x, LawfulAggregate.merge_assoc]

theorem foldl_merge_append (xs ys : Array M) :
    (xs ++ ys).foldl merge empty = merge (xs.foldl merge empty) (ys.foldl merge empty) := by
  rw [Array.foldl_append, ← Array.foldl_toList (xs := ys), foldl_merge_from, Array.foldl_toList]

theorem foldRange_single (a : Array M) {j : Nat} (h : j < a.size) : foldRange a j (j + 1) = a[j] := by
  rw [foldRange_eq_extract, Array.extract_succ_right (Nat.lt_succ_self j) h, Array.extract_eq_empty_of_le
    (by omega)]
  simp [LawfulAggregate.empty_merge]

/-- A range splits at any point inside it. -/
theorem foldRange_split (a : Array M) {lo mid hi : Nat} (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
    foldRange a lo hi = merge (foldRange a lo mid) (foldRange a mid hi) := by
  simp only [foldRange_eq_extract]
  rw [← foldl_merge_append, Array.extract_append_extract, Nat.min_eq_left h₁, Nat.max_eq_right h₂]

end Aggregate

namespace Pyramid

variable {M : Type u} [Aggregate M] [LawfulAggregate M]

theorem foldRange_coarsen {b : Nat} (hb : 0 < b) (a : Array M) (c d : Nat) :
    foldRange (coarsen b a) c d = foldRange a (c * b) (d * b) := by
  induction d with
  | zero =>
    rw [Aggregate.foldRange_of_le _ (Nat.zero_le c), Nat.zero_mul,
      Aggregate.foldRange_of_le _ (Nat.zero_le _)]
  | succ d ih =>
    by_cases hcd : d + 1 ≤ c
    · rw [Aggregate.foldRange_of_le _ hcd,
        Aggregate.foldRange_of_le _ (Nat.mul_le_mul_right b hcd)]
    · have hcd' : c ≤ d := by omega
      rw [Aggregate.foldRange_split _ hcd' (Nat.le_succ d), ih,
        Aggregate.foldRange_split a (Nat.mul_le_mul_right b hcd')
          (Nat.mul_le_mul_right b (Nat.le_succ d))]
      congr 1
      by_cases hd : d < (coarsen b a).size
      · rw [Aggregate.foldRange_single _ hd]
        simp [coarsen, Nat.succ_mul]
      · rw [Aggregate.foldRange_of_size_le _ (by omega)]
        have hsize : (coarsen b a).size = (a.size + b - 1) / b := by simp [coarsen]
        rw [hsize, Nat.not_lt, Nat.div_le_iff_le_mul_add_pred hb] at hd
        rw [Aggregate.foldRange_of_size_le _ (by
          have : d * b + (b - 1) = b * d + (b - 1) := by rw [Nat.mul_comm]
          omega)]

theorem foldRange_levelAt {b : Nat} (hb : 0 < b) (a : Array M) (k c d : Nat) :
    foldRange (levelAt b a k) c d = foldRange a (c * b ^ k) (d * b ^ k) := by
  induction k generalizing c d with
  | zero => simp [levelAt]
  | succ k ih =>
    show foldRange (coarsen b (levelAt b a k)) c d = _
    rw [foldRange_coarsen hb, ih, Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm b]

theorem queryFrom_eq (p : Pyramid M) (k lo hi : Nat) (hk : k < p.levels.size) :
    queryFrom p.levels p.branching k lo hi = foldRange (levelAt p.branching p.leaves k) lo hi := by
  have hb : 0 < p.branching := by have := p.two_le_branching; omega
  induction k, lo, hi using queryFrom.induct p.levels p.branching with
  | case1 k lo hi hk' hk1 lo' hi' hlt ih =>
    rw [queryFrom]
    simp only [hk', hk1, dite_true, ite_true, lo', hi', hlt]
    rw [ih hk1, p.levels_eq k hk', levelAt, foldRange_coarsen hb]
    have hlo : lo ≤ (lo + p.branching - 1) / p.branching * p.branching := by
      have := Nat.lt_mul_div_succ (lo + p.branching - 1) hb
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at this
      omega
    have hmid : (lo + p.branching - 1) / p.branching * p.branching ≤
        hi / p.branching * p.branching := Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
    have hhi : hi / p.branching * p.branching ≤ hi := Nat.div_mul_le_self hi p.branching
    rw [Aggregate.foldRange_split _ hlo (Nat.le_trans hmid hhi),
      Aggregate.foldRange_split _ hmid hhi]
  | case2 k lo hi hk' hk1 lo' hi' hlt =>
    rw [queryFrom]
    simp only [hk', hk1, dite_true, ite_true, lo', hi', hlt, ite_false]
    rw [p.levels_eq k hk']
  | case3 k lo hi hk' hk1 =>
    rw [queryFrom]
    simp only [hk', hk1, dite_true, ite_false]
    rw [p.levels_eq k hk']
  | case4 k lo hi hk' => exact absurd hk hk'

/-- PROOF-1: a query merges exactly the leaves in its range, in order, as merging them one by one
would. -/
theorem query_eq (p : Pyramid M) (lo hi : Nat) : p.query lo hi = foldRange p.leaves lo hi := by
  unfold query
  split
  · rfl
  · rw [queryFrom_eq p 0 lo hi (by omega)]
    rfl

/-- PROOF-1 for raw data: a query over a pyramid of measures equals the fold of the measure over
the items in the range. -/
theorem query_ofMeasure {γ : Type v} (b : Nat) (h : 2 ≤ b) (m : γ → M) (xs : Array γ)
    (lo hi : Nat) : (ofMeasure b h m xs).query lo hi = Aggregate.fold m (xs.extract lo hi) := by
  rw [query_eq]
  simp only [ofMeasure, build]
  rw [Aggregate.foldRange_eq_extract]
  unfold Aggregate.fold
  rw [← Array.map_extract, Array.foldl_map]

omit [LawfulAggregate M] in
/-- PROOF-2, adjacent levels: each node merges its `branching` children, the last taking whatever
remains. -/
theorem getElem_levels_succ (p : Pyramid M) {k j : Nat} (hk : k + 1 < p.levels.size)
    (hj : j < p.levels[k + 1].size) :
    p.levels[k + 1][j] = foldRange (p.levels[k]'(by omega)) (j * p.branching)
      (j * p.branching + p.branching) := by
  have hl := p.levels_eq (k + 1) hk
  have hl' := p.levels_eq k (by omega)
  simp only [hl, levelAt] at hj ⊢
  simp [coarsen, hl']

/-- PROOF-2, each node: node `j` of level `k` merges exactly leaves `j * branching ^ k` to
`(j + 1) * branching ^ k - 1`, its bucket. -/
theorem getElem_levels (p : Pyramid M) {k j : Nat} (hk : k < p.levels.size)
    (hj : j < p.levels[k].size) :
    p.levels[k][j] = foldRange p.leaves (j * p.branching ^ k) ((j + 1) * p.branching ^ k) := by
  have hb : 0 < p.branching := by have := p.two_le_branching; omega
  have hl := p.levels_eq k hk
  simp only [hl] at hj ⊢
  rw [← Aggregate.foldRange_single _ hj, foldRange_levelAt hb]

omit [LawfulAggregate M] in
/-- PROOF-2, buckets: leaf `i` lies in the bucket of node `j` at level `k` exactly when
`j = i / branching ^ k`, so in exactly one bucket per level. -/
theorem mem_node_iff (p : Pyramid M) (i j k : Nat) :
    j * p.branching ^ k ≤ i ∧ i < (j + 1) * p.branching ^ k ↔ i / p.branching ^ k = j := by
  have hB : 0 < p.branching ^ k := Nat.pow_pos (by have := p.two_le_branching; omega)
  constructor
  · rintro ⟨h₁, h₂⟩
    exact Nat.div_eq_of_lt_le h₁ h₂
  · rintro rfl
    refine ⟨Nat.div_mul_le_self i _, ?_⟩
    have := Nat.lt_mul_div_succ i hB
    rw [Nat.mul_comm] at this
    exact this

omit [LawfulAggregate M] in
theorem div_lt_size_levelAt {b : Nat} (hb : 0 < b) (a : Array M) {i : Nat} (hi : i < a.size)
    (k : Nat) : i / b ^ k < (levelAt b a k).size := by
  induction k with
  | zero => simpa [levelAt] using hi
  | succ k ih =>
    show i / b ^ (k + 1) < (coarsen b (levelAt b a k)).size
    simp only [coarsen, Array.size_map, Array.size_range]
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.lt_div_iff_mul_lt hb]
    have := Nat.div_mul_le_self (i / b ^ k) b
    omega

omit [LawfulAggregate M] in
/-- PROOF-2, every leaf has its node: the node `i / branching ^ k` exists at every level. -/
theorem div_lt_size_levels (p : Pyramid M) {i : Nat} (hi : i < p.leaves.size) {k : Nat}
    (hk : k < p.levels.size) : i / p.branching ^ k < p.levels[k].size := by
  rw [p.levels_eq k hk]
  exact div_lt_size_levelAt (by have := p.two_le_branching; omega) _ hi k

end Pyramid

end Inkproof.Core
