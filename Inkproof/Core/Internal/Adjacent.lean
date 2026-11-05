/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Core.Internal

universe u

/-- The first index `i ≥ start` at which `r xs[i] xs[i + 1]` fails. -/
def firstAdjacentFailure {γ : Type u} (r : γ → γ → Bool) (xs : Array γ) (start : Nat) :
    Option Nat :=
  if h : start + 1 < xs.size then
    if r xs[start] xs[start + 1] then firstAdjacentFailure r xs (start + 1) else some start
  else none
termination_by xs.size - start

theorem adjacent_of_firstAdjacentFailure {γ : Type u} {r : γ → γ → Bool} {xs : Array γ}
    {start : Nat} (h : firstAdjacentFailure r xs start = none) :
    ∀ i, start ≤ i → ∀ (hi : i + 1 < xs.size), r xs[i] xs[i + 1] = true := by
  induction start using firstAdjacentFailure.induct r xs with
  | case1 start hlt hr ih =>
    rw [firstAdjacentFailure] at h
    simp only [hlt, hr, dite_true, ite_true] at h
    intro i hs hi
    rcases Nat.eq_or_lt_of_le hs with rfl | hlt'
    · exact hr
    · exact ih h i hlt' hi
  | case2 start hlt hr =>
    rw [firstAdjacentFailure] at h
    simp [hlt, hr] at h
  | case3 start hlt =>
    intro i hs hi
    omega

theorem firstAdjacentFailure_eq_none_of {γ : Type u} {r : γ → γ → Bool} {xs : Array γ}
    {start : Nat} (h : ∀ i, start ≤ i → ∀ (hi : i + 1 < xs.size), r xs[i] xs[i + 1] = true) :
    firstAdjacentFailure r xs start = none := by
  induction start using firstAdjacentFailure.induct r xs with
  | case1 start hlt hr ih =>
    rw [firstAdjacentFailure]
    simp only [hlt, hr, dite_true, ite_true]
    exact ih fun i hs hi => h i (by omega) hi
  | case2 start hlt hr =>
    exact absurd (h start (Nat.le_refl _) hlt) (by simpa using hr)
  | case3 start hlt =>
    rw [firstAdjacentFailure]
    simp [hlt]

/-- A reported failure is the first one at or after `start`. -/
theorem firstAdjacentFailure_eq_some {γ : Type u} {r : γ → γ → Bool} {xs : Array γ}
    {start i : Nat} (h : firstAdjacentFailure r xs start = some i) :
    ∃ hi : i + 1 < xs.size, r xs[i] xs[i + 1] = false ∧ start ≤ i ∧
      ∀ j, start ≤ j → ∀ (hj : j < i), r (xs[j]'(by omega)) (xs[j + 1]'(by omega)) = true := by
  induction start using firstAdjacentFailure.induct r xs with
  | case1 start hlt hr ih =>
    rw [firstAdjacentFailure] at h
    simp only [hlt, hr, dite_true, ite_true] at h
    obtain ⟨hi, hri, hs, hbefore⟩ := ih h
    refine ⟨hi, hri, by omega, fun j hj hji => ?_⟩
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt'
    · exact hr
    · exact hbefore j hlt' hji
  | case2 start hlt hr =>
    rw [firstAdjacentFailure] at h
    simp only [hlt, hr, dite_true] at h
    simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at h
    subst h
    exact ⟨hlt, by simpa using hr, Nat.le_refl _, fun j hj hji => by omega⟩
  | case3 start hlt =>
    rw [firstAdjacentFailure] at h
    simp [hlt] at h

end Inkproof.Core.Internal
