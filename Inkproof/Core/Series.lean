/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Internal.Adjacent

namespace Inkproof.Core

universe u v

/-- Every element is at most every later one. Stated over indices with `<`, so it needs no
reflexivity and reads directly in proofs about positions. -/
def Sorted {α : Type u} [LE α] (xs : Array α) : Prop :=
  ∀ (i j : Nat) (hij : i < j) (hj : j < xs.size), xs[i]'(by omega) ≤ xs[j]

/-- Points ordered by x-value, each with a value that may be missing (`none`). Repeated x-values
are allowed. -/
structure Series (α : Type u) (β : Type v) [LE α] where
  xs : Array α
  values : Array (Option β)
  size_eq : values.size = xs.size
  sorted : Sorted xs

/-- Why `Series.ofArrays?` or `Series.ofPoints?` rejected its input. -/
inductive SeriesError where
  | sizeMismatch (xs values : Nat)
  /-- The x-value at `index + 1` is not at least the one at `index`. -/
  | unsorted (index : Nat)
  deriving Repr, DecidableEq

section
variable {α : Type u} [LE α]

theorem sorted_of_pairwise {xs : Array α} (h : xs.toList.Pairwise (· ≤ ·)) : Sorted xs := by
  intro i j hij hj
  have := List.pairwise_iff_getElem.mp h i j (by simp; omega) (by simpa using hj) hij
  simpa using this

theorem sorted_empty : Sorted (#[] : Array α) := fun _ _ _ hj => absurd hj (by simp)

theorem sorted_of_le_succ [Std.IsPreorder α] {xs : Array α}
    (h : ∀ i (hi : i + 1 < xs.size), xs[i] ≤ xs[i + 1]) : Sorted xs := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hij) with rfl | hlt
    · exact h i hj
    · exact Std.IsPreorder.le_trans _ _ _ (ih hlt (by omega)) (h j hj)

end

namespace Series

variable {α : Type u} {β : Type v} [LE α]

def size (s : Series α β) : Nat := s.xs.size

instance : EmptyCollection (Series α β) := ⟨⟨#[], #[], rfl, sorted_empty⟩⟩

instance : Inhabited (Series α β) := ⟨{}⟩

def x (s : Series α β) (i : Fin s.size) : α := s.xs[i]'i.isLt

def value (s : Series α β) (i : Fin s.size) : Option β := s.values[i]'(s.size_eq ▸ i.isLt)

def points (s : Series α β) : Array (α × Option β) := s.xs.zip s.values

/-- Checks that the arrays have equal sizes and the x-values never decrease; see `ofArrays?_ok_iff`,
`ofArrays?_eq_ok` and `ofArrays?_eq_error_unsorted`. -/
def ofArrays? [DecidableLE α] [Std.IsPreorder α] (xs : Array α) (values : Array (Option β)) :
    Except SeriesError (Series α β) :=
  if hs : values.size = xs.size then
    match hd : Internal.firstAdjacentFailure (fun a b => decide (a ≤ b)) xs 0 with
    | some i => .error (.unsorted i)
    | none =>
      .ok ⟨xs, values, hs, sorted_of_le_succ fun i hi => by
        simpa using Internal.adjacent_of_firstAdjacentFailure hd i (Nat.zero_le i) hi⟩
  else .error (.sizeMismatch xs.size values.size)

/-- Checks that the x-values never decrease; see `ofPoints?_ok_iff` and `ofPoints?_eq_ok`. -/
def ofPoints? [DecidableLE α] [Std.IsPreorder α] (points : Array (α × Option β)) :
    Except SeriesError (Series α β) :=
  ofArrays? (points.map (·.1)) (points.map (·.2))

/-- Sorts the points by x-value. The sort is stable: points with equal x-values keep their input
order (`ofUnsorted_stable`), and no point is added or lost (`ofUnsorted_perm`). -/
def ofUnsorted [DecidableLE α] [Std.IsLinearOrder α] (points : Array (α × Option β)) :
    Series α β :=
  let sorted := points.toList.mergeSort (fun p q => decide (p.1 ≤ q.1))
  { xs := (sorted.map (·.1)).toArray
    values := (sorted.map (·.2)).toArray
    size_eq := by simp
    sorted := sorted_of_pairwise <| by
      have h := List.pairwise_mergeSort (le := fun (p q : α × Option β) => decide (p.1 ≤ q.1))
        (fun a b c hab hbc => by
          simp only [decide_eq_true_eq] at *
          exact Std.IsPreorder.le_trans _ _ _ hab hbc)
        (fun a b => by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Std.IsLinearPreorder.le_total _ _)
        points.toList
      simpa [List.pairwise_map] using h }

/-- The points at indices `lo` to `hi - 1`, clamped to the series. -/
def slice (s : Series α β) (lo hi : Nat) : Series α β :=
  { xs := s.xs.extract lo hi
    values := s.values.extract lo hi
    size_eq := by simp [s.size_eq]
    sorted := by
      intro i j hij hj
      simp only [Array.size_extract] at hj
      simp only [Array.getElem_extract]
      exact s.sorted (lo + i) (lo + j) (by omega) (by omega) }

end Series

end Inkproof.Core
