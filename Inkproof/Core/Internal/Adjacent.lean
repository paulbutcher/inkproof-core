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

end Inkproof.Core.Internal
