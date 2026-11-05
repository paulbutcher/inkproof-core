/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Aggregate

namespace Inkproof.Core

universe u v

open Aggregate (empty merge)

namespace Aggregate

variable {M : Type u} [Aggregate M]

/-- Merges `a[lo]` to `a[hi - 1]` in order. Indices past the end of `a` contribute nothing. -/
def foldRange (a : Array M) (lo hi : Nat) : M :=
  a.foldl merge empty lo hi

end Aggregate

open Aggregate (foldRange)

namespace Pyramid

variable {M : Type u} [Aggregate M]

/-- The level above `a`: node `j` merges `a[j * b]` to `a[j * b + b - 1]`, the last node taking
whatever remains. -/
def coarsen (b : Nat) (a : Array M) : Array M :=
  (Array.range ((a.size + b - 1) / b)).map fun j => foldRange a (j * b) (j * b + b)

/-- Level `k` of a pyramid over `leaves`: the specification the stored levels meet. -/
def levelAt (b : Nat) (leaves : Array M) : Nat → Array M
  | 0 => leaves
  | k + 1 => coarsen b (levelAt b leaves k)

theorem size_coarsen_lt {b : Nat} (hb : 2 ≤ b) {a : Array M} (ha : 2 ≤ a.size) :
    (coarsen b a).size < a.size := by
  simp only [coarsen, Array.size_map, Array.size_range]
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have : a.size * 2 ≤ a.size * b := Nat.mul_le_mul_left _ hb
  have : 2 * b ≤ a.size * b := Nat.mul_le_mul_right _ ha
  omega

/-- `a` and every coarser level, down to one node. -/
def buildLevels (b : Nat) (hb : 2 ≤ b) (a : Array M) : List (Array M) :=
  if ha : 2 ≤ a.size then
    have := size_coarsen_lt hb ha
    a :: buildLevels b hb (coarsen b a)
  else [a]
termination_by a.size

end Pyramid

/-- An aggregation pyramid: the measures of a run of points, and coarser levels in which each node
merges `branching` consecutive nodes of the level below. Build one per segment, so no node merges
points from two segments. -/
structure Pyramid (M : Type u) [Aggregate M] where
  branching : Nat
  two_le_branching : 2 ≤ branching
  leaves : Array M
  levels : Array (Array M)
  levels_eq : ∀ k (h : k < levels.size), levels[k] = Pyramid.levelAt branching leaves k

namespace Pyramid

variable {M : Type u} [Aggregate M]

theorem levelAt_succ' (b : Nat) (a : Array M) (k : Nat) :
    levelAt b a (k + 1) = levelAt b (coarsen b a) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (coarsen b) ih

theorem buildLevels_getElem? (b : Nat) (hb : 2 ≤ b) (n : Nat) :
    ∀ (a : Array M), a.size ≤ n → ∀ k x, (buildLevels b hb a)[k]? = some x → x = levelAt b a k := by
  induction n with
  | zero =>
    intro a hn k x h
    rw [buildLevels.eq_def] at h
    split at h
    · omega
    · cases k <;> simp_all [levelAt]
  | succ n ih =>
    intro a hn k x h
    rw [buildLevels.eq_def] at h
    split at h
    · rename_i ha
      cases k with
      | zero => simp_all [levelAt]
      | succ k =>
        simp only [List.getElem?_cons_succ] at h
        rw [levelAt_succ']
        exact ih _ (by have := size_coarsen_lt hb ha; omega) k x h
    · cases k <;> simp_all [levelAt]

theorem buildLevels_getElem (b : Nat) (hb : 2 ≤ b) (a : Array M) (k : Nat)
    (h : k < (buildLevels b hb a).length) : (buildLevels b hb a)[k] = levelAt b a k :=
  buildLevels_getElem? b hb a.size a (Nat.le_refl _) k _ (List.getElem?_eq_getElem h)

/-- Builds the pyramid over `leaves`, with nodes merging `branching` children. Levels shrink until
the top has at most one node (`two_le_size_levels_build`, `size_top_levels_build`). -/
def build (branching : Nat) (h : 2 ≤ branching) (leaves : Array M) : Pyramid M :=
  { branching, two_le_branching := h, leaves
    levels := (buildLevels branching h leaves).toArray
    levels_eq := fun k hk => by
      simp only [List.getElem_toArray]
      exact buildLevels_getElem branching h leaves k (by simpa using hk) }

/-- Builds the pyramid over the measures of `xs`. -/
def ofMeasure {γ : Type v} (branching : Nat) (h : 2 ≤ branching) (measure : γ → M)
    (xs : Array γ) : Pyramid M :=
  build branching h (xs.map measure)

/-- Merges nodes `lo` to `hi - 1` of level `k`, taking whole groups from the level above. -/
def queryFrom (levels : Array (Array M)) (b k lo hi : Nat) : M :=
  if hk : k < levels.size then
    if k + 1 < levels.size then
      let lo' := (lo + b - 1) / b
      let hi' := hi / b
      if lo' < hi' then
        merge (foldRange levels[k] lo (lo' * b))
          (merge (queryFrom levels b (k + 1) lo' hi') (foldRange levels[k] (hi' * b) hi))
      else foldRange levels[k] lo hi
    else foldRange levels[k] lo hi
  else empty
termination_by levels.size - k

/-- Merges the measures of points `lo` to `hi - 1`, with the same result as merging them one by one
(`Pyramid.query_eq`). Each level contributes only its nodes before the first and after the last
whole group in the range; the groups between come from the level above. -/
def query (p : Pyramid M) (lo hi : Nat) : M :=
  if p.levels.size = 0 then foldRange p.leaves lo hi
  else queryFrom p.levels p.branching 0 lo hi

end Pyramid

end Inkproof.Core
