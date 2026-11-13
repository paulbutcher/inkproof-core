/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Indexed
import Inkproof.Core.Proofs.Query

/-! CORE-8: algorithms that read through `IndexedSeries` compute what they compute on the
corresponding array, so PROOF-1 to PROOF-3 apply to data supplied by any indexed container. -/

namespace Inkproof.Core

universe u v w

namespace IndexedSeries

variable {σ : Type u} {α : Type v} [IndexedSeries σ α]

@[simp] theorem size_toArray (s : σ) : (toArray s).size = size s := by simp [toArray]

theorem getElem_toArray (s : σ) {i : Nat} (h : i < (toArray s).size) :
    (toArray s)[i] = get s i (by simpa using h) := by simp [toArray]

/-- For an ordinary array, `toArray` changes nothing. -/
@[simp] theorem toArray_array (a : Array α) : toArray a = a := by
  apply Array.ext
  · simp [toArray, size]
  · intro i h₁ h₂
    simp [toArray, get]

end IndexedSeries

namespace Pyramid

variable {σ : Type u} {γ : Type v} {M : Type w} [Aggregate M] [IndexedSeries σ γ]

theorem ofIndexed_eq_ofMeasure (b : Nat) (h : 2 ≤ b) (m : γ → M) (s : σ) :
    ofIndexed b h m s = ofMeasure b h m (IndexedSeries.toArray s) := by
  simp only [ofIndexed, ofMeasure, IndexedSeries.toArray]
  congr 1
  apply Array.ext
  · simp
  · intro i h₁ h₂
    simp

/-- PROOF-1 for indexed data: querying a pyramid built through the interface merges the measures
of the elements in the range, in order. -/
theorem query_ofIndexed [LawfulAggregate M] (b : Nat) (h : 2 ≤ b) (m : γ → M) (s : σ)
    (lo hi : Nat) :
    (ofIndexed b h m s).query lo hi =
      Aggregate.fold m ((IndexedSeries.toArray s).extract lo hi) := by
  rw [ofIndexed_eq_ofMeasure, query_ofMeasure]

end Pyramid

namespace Series

variable {σ : Type u} {α : Type v} [LE α] [DecidableLE α] [IndexedSeries σ α]

theorem lowerBoundFromBy_eq (n : Nat) (a : Array α) (hn : n = a.size) (x : α) (lo hi : Nat) :
    lowerBoundFromBy n (fun i h => a[i]'(hn ▸ h)) x lo hi = lowerBoundFrom a x lo hi := by
  subst hn
  rfl

/-- Searching an indexed container finds what `Series.lowerBound` finds on its elements, so the
index range for an x-range, and with it PROOF-1 over x-ranges, is unchanged. -/
theorem lowerBoundIndexed_eq (xs : σ) (x : α) :
    lowerBoundIndexed xs x = lowerBoundFrom (IndexedSeries.toArray xs) x 0 (IndexedSeries.size xs) := by
  rw [lowerBoundIndexed, ← lowerBoundFromBy_eq (IndexedSeries.size xs) (IndexedSeries.toArray xs)
    (by simp)]
  congr 1
  funext i h
  simp [IndexedSeries.getElem_toArray]

end Series

end Inkproof.Core
