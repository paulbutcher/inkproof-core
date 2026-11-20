/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Stack

namespace Inkproof.Core.Series

universe u v

variable {α : Type u} {β : Type v} [LE α] [Add β] [Zero β] [LT β] [DecidableLT β]

theorem size_stack (ss : Array (Series α β)) : (stack ss).size = ss.size := by
  simp [stack]

theorem stack_xs (ss : Array (Series α β)) (k : Nat) (hk : k < ss.size) :
    ((stack ss)[k]'(by rwa [size_stack])).xs = ss[k].xs := by
  simp [stack]

theorem stack_value (ss : Array (Series α β)) (k : Nat) (hk : k < ss.size) (i : Nat)
    (hi : i < ss[k].size) :
    ((stack ss)[k]'(by rwa [size_stack])).values[i]? = some (stackAt ss k i) := by
  simp [stack, hi]

/-- Without negative values, a stacked value is the sum of the present values of the series up to it. -/
theorem stackAt_eq_sum (ss : Array (Series α β)) (k i : Nat) (v : β)
    (hk : valueAt ss k i = some v)
    (hnn : ∀ j w, j ≤ k → valueAt ss j i = some w → ¬ w < 0) :
    stackAt ss k i = some ((List.range (k + 1)).foldl
      (fun a j => match valueAt ss j i with | some w => a + w | none => a) 0) := by
  have hv := hnn k v (Nat.le_refl _) hk
  simp only [stackAt, hk, Option.map_some, signSum, decide_eq_false hv]
  congr 1
  suffices ∀ n, n ≤ k + 1 → (List.range n).foldl
      (fun a j => match valueAt ss j i with
        | some w => if decide (w < 0) = false then a + w else a
        | none => a) 0 = (List.range n).foldl
      (fun a j => match valueAt ss j i with | some w => a + w | none => a) 0 from this _ (Nat.le_refl _)
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    cases h : valueAt ss n i with
    | none => rfl
    | some w => simp [decide_eq_false (hnn n w (by omega) h)]

theorem signSum_succ (ss : Array (Series α β)) (i : Nat) (neg : Bool) (n : Nat) :
    signSum ss i neg (n + 1) = match valueAt ss n i with
      | some w => if decide (w < 0) = neg then signSum ss i neg n + w else signSum ss i neg n
      | none => signSum ss i neg n := by
  simp only [signSum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  cases valueAt ss n i <;> simp

/-- With no negative values, stacking never decreases a point as `k` grows, wherever both are present. -/
theorem stackAt_mono [LE β] (ss : Array (Series α β)) (k i : Nat) (a b : β)
    (hadd : ∀ x w : β, ¬ w < 0 → x ≤ x + w)
    (hnn : ∀ j w, j ≤ k + 1 → valueAt ss j i = some w → ¬ w < 0)
    (ha : stackAt ss k i = some a) (hb : stackAt ss (k + 1) i = some b) : a ≤ b := by
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 ha
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hv' := hnn k v (by omega) hv
  have hw' := hnn (k + 1) w (by omega) hw
  simp only [decide_eq_false hv', decide_eq_false hw'] at ha hb ⊢
  have := signSum_succ ss i false (k + 1)
  simp only [hw, decide_eq_false hw', ite_true] at this
  rw [this]
  exact hadd _ _ hw'

end Inkproof.Core.Series
