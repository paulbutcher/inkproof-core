/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Aggregate

/-! What each provided aggregate computes. The laws in `Inkproof.Core.Aggregate` make aggregation
independent of grouping; these theorems say the result is the one the aggregate's name promises. -/

namespace Inkproof.Core

universe u v w

open Aggregate (empty merge fold)

namespace Aggregate

variable {M : Type u} [Aggregate M] {γ : Type v}

private theorem foldl_merge_eq [LawfulAggregate M] (a : M) (l : List M) :
    l.foldl merge a = merge a (l.foldr merge empty) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, LawfulAggregate.merge_assoc]

/-- For a lawful aggregate, folding from the left equals folding from the right, so a fold can be
read as `merge (measure x₀) (merge (measure x₁) …)`. -/
theorem fold_eq_foldr [LawfulAggregate M] (m : γ → M) (xs : Array γ) :
    fold m xs = (xs.toList.map m).foldr merge empty := by
  rw [fold, ← Array.foldl_toList, ← List.foldl_map, foldl_merge_eq, LawfulAggregate.empty_merge]

private theorem foldl_prod {A : Type u} {B : Type w} [Aggregate A] [Aggregate B] (m₁ : γ → A)
    (m₂ : γ → B) (l : List γ) (a : A) (b : B) :
    l.foldl (fun acc x => merge acc (m₁ x, m₂ x)) (a, b) =
      (l.foldl (fun acc x => merge acc (m₁ x)) a, l.foldl (fun acc x => merge acc (m₂ x)) b) := by
  induction l generalizing a b with
  | nil => rfl
  | cons x l ih => exact ih _ _

/-- Aggregating pairs aggregates each component on its own, so first/max/min/last gives the first,
maximum, minimum and last values. Needs no laws. -/
theorem fold_prod {A : Type u} {B : Type w} [Aggregate A] [Aggregate B] (m₁ : γ → A)
    (m₂ : γ → B) (xs : Array γ) : fold (fun x => (m₁ x, m₂ x)) xs = (fold m₁ xs, fold m₂ xs) := by
  simp only [fold, ← Array.foldl_toList]
  exact foldl_prod m₁ m₂ xs.toList empty empty

end Aggregate

variable {γ : Type v}

/-- `First` gives the first item's value, skipping items whose measure is `none`. -/
theorem First.fold_get {α : Type u} (m : γ → First α) (xs : Array γ) :
    (fold m xs).get = xs.toList.findSome? (fun x => (m x).get) := by
  rw [Aggregate.fold_eq_foldr]
  induction xs.toList with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.foldr_cons, List.findSome?_cons]
    show ((m x).get <|> _) = _
    rw [ih]
    cases (m x).get <;> rfl

/-- `Last` gives the last item's value, skipping items whose measure is `none`. -/
theorem Last.fold_get {α : Type u} (m : γ → Last α) (xs : Array γ) :
    (fold m xs).get = xs.toList.reverse.findSome? (fun x => (m x).get) := by
  rw [Aggregate.fold_eq_foldr]
  induction xs.toList with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.foldr_cons, List.reverse_cons, List.findSome?_append]
    show (_ <|> (m x).get) = _
    rw [ih]
    simp only [List.findSome?_cons, List.findSome?_nil]
    cases (m x).get <;> simp

/-- `Count` adds up the measures; measuring each item as one counts the items. -/
theorem Count.fold_get (m : γ → Count) (xs : Array γ) :
    (fold m xs).get = (xs.toList.map fun x => (m x).get).sum := by
  rw [Aggregate.fold_eq_foldr]
  induction xs.toList with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.foldr_cons, List.map_cons, List.sum_cons, ← ih]
    rfl

/-- `Total` adds up the measures, from the first item to the last. -/
theorem Total.fold_get {α : Type u} [Add α] [OfNat α 0] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] (m : γ → Total α) (xs : Array γ) :
    (fold m xs).get = (xs.toList.map fun x => (m x).get).foldr (· + ·) 0 := by
  rw [Aggregate.fold_eq_foldr]
  induction xs.toList with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.foldr_cons, List.map_cons, List.foldr_cons, ← ih]
    rfl

namespace Occupancy

theorem contains_singleton (i j : Nat) : (singleton j).contains i = true ↔ i = j := by
  simp [singleton, contains, Nat.one_shiftLeft, Nat.testBit_two_pow, eq_comm]

theorem contains_merge (a b : Occupancy) (i : Nat) :
    (merge a b).contains i = (a.contains i || b.contains i) :=
  Nat.testBit_or a.bits b.bits i

/-- `Occupancy` contains exactly the indices some item's measure contains. -/
theorem fold_contains (m : γ → Occupancy) (xs : Array γ) (i : Nat) :
    (fold m xs).contains i = true ↔ ∃ x ∈ xs, (m x).contains i = true := by
  rw [Aggregate.fold_eq_foldr]
  simp only [← Array.mem_toList_iff]
  induction xs.toList with
  | nil => simp [contains, empty]
  | cons x l ih => simp [contains_merge, ih]

end Occupancy

section Order

variable {α : Type u} [LE α] [DecidableLE α] [Std.IsLinearOrder α]

omit [DecidableLE α] in
private theorem le_of_not_le {a b : α} (h : ¬ a ≤ b) : b ≤ a :=
  (Std.IsLinearPreorder.le_total a b).resolve_left h

namespace Minimum

private def run (m : γ → Minimum α) (l : List γ) : Minimum α := (l.map m).foldr merge empty

omit [Std.IsLinearOrder α] in
private theorem run_cons (m : γ → Minimum α) (x : γ) (l : List γ) :
    run m (x :: l) = merge (m x) (run m l) := rfl

omit [Std.IsLinearOrder α] in
private theorem merge_get (a b : Minimum α) :
    (merge a b).get = match a.get, b.get with
      | some x, some y => some (if x ≤ y then x else y)
      | none, y => y
      | x, none => x := by
  rcases a with ⟨_ | x⟩ <;> rcases b with ⟨_ | y⟩ <;> rfl

omit [Std.IsLinearOrder α] in
private theorem run_eq_none (m : γ → Minimum α) (l : List γ) :
    (run m l).get = none ↔ ∀ x ∈ l, (m x).get = none := by
  induction l with
  | nil => simp [run, empty]
  | cons x l ih =>
    rw [run_cons, merge_get, List.forall_mem_cons, ← ih]
    cases (m x).get <;> cases (run m l).get <;> simp

private theorem run_eq_some (m : γ → Minimum α) (l : List γ) {a : α}
    (h : (run m l).get = some a) :
    (∃ x ∈ l, (m x).get = some a) ∧ ∀ x ∈ l, ∀ b, (m x).get = some b → a ≤ b := by
  induction l generalizing a with
  | nil => simp [run, empty] at h
  | cons x l ih =>
    rw [run_cons, merge_get] at h
    simp only [List.mem_cons, exists_eq_or_imp, forall_eq_or_imp]
    cases hx : (m x).get with
    | none =>
      rw [hx] at h
      cases hr : (run m l).get <;> rw [hr] at h
      · contradiction
      · cases h
        obtain ⟨hex, hall⟩ := ih hr
        exact ⟨Or.inr hex, fun b hb => absurd hb (by simp), hall⟩
    | some c =>
      rw [hx] at h
      cases hr : (run m l).get with
      | none =>
        rw [hr] at h
        cases h
        have hnone := (run_eq_none m l).mp hr
        refine ⟨Or.inl rfl, fun b hb => ?_, fun y hy b hb => ?_⟩
        · cases hb; exact Std.IsPreorder.le_refl _
        · simp [hnone y hy] at hb
      | some d =>
        rw [hr] at h
        obtain ⟨hex, hall⟩ := ih hr
        simp only [Option.some.injEq] at h
        split at h
        · rename_i hcd
          subst h
          refine ⟨Or.inl rfl, fun b hb => ?_, fun y hy b hb => ?_⟩
          · cases hb; exact Std.IsPreorder.le_refl _
          · exact Std.IsPreorder.le_trans _ _ _ hcd (hall y hy b hb)
        · rename_i hcd
          subst h
          refine ⟨Or.inr hex, fun b hb => ?_, hall⟩
          cases hb; exact le_of_not_le hcd

/-- The minimum is missing exactly when every item's value is. -/
theorem fold_get_eq_none (m : γ → Minimum α) (xs : Array γ) :
    (fold m xs).get = none ↔ ∀ x ∈ xs, (m x).get = none := by
  rw [Aggregate.fold_eq_foldr]
  simp only [← Array.mem_toList_iff]
  exact run_eq_none m xs.toList

/-- The minimum is `a` exactly when some item's value is `a` and no item's value is below it. -/
theorem fold_get_eq_some (m : γ → Minimum α) (xs : Array γ) (a : α) :
    (fold m xs).get = some a ↔
      (∃ x ∈ xs, (m x).get = some a) ∧ ∀ x ∈ xs, ∀ b, (m x).get = some b → a ≤ b := by
  rw [Aggregate.fold_eq_foldr]
  simp only [← Array.mem_toList_iff]
  change (run m xs.toList).get = some a ↔ _
  constructor
  · exact run_eq_some m xs.toList
  · rintro ⟨⟨x, hx, hxa⟩, hall⟩
    cases hr : (run m xs.toList).get with
    | none => simp [(run_eq_none m _).mp hr x hx] at hxa
    | some r =>
      obtain ⟨⟨y, hy, hyr⟩, hrall⟩ := run_eq_some m xs.toList hr
      exact congrArg some (Std.IsPartialOrder.le_antisymm _ _ (hrall x hx a hxa) (hall y hy r hyr))

end Minimum

namespace Maximum

private def run (m : γ → Maximum α) (l : List γ) : Maximum α := (l.map m).foldr merge empty

omit [Std.IsLinearOrder α] in
private theorem run_cons (m : γ → Maximum α) (x : γ) (l : List γ) :
    run m (x :: l) = merge (m x) (run m l) := rfl

omit [Std.IsLinearOrder α] in
private theorem merge_get (a b : Maximum α) :
    (merge a b).get = match a.get, b.get with
      | some x, some y => some (if y ≤ x then x else y)
      | none, y => y
      | x, none => x := by
  rcases a with ⟨_ | x⟩ <;> rcases b with ⟨_ | y⟩ <;> rfl

omit [Std.IsLinearOrder α] in
private theorem run_eq_none (m : γ → Maximum α) (l : List γ) :
    (run m l).get = none ↔ ∀ x ∈ l, (m x).get = none := by
  induction l with
  | nil => simp [run, empty]
  | cons x l ih =>
    rw [run_cons, merge_get, List.forall_mem_cons, ← ih]
    cases (m x).get <;> cases (run m l).get <;> simp

private theorem run_eq_some (m : γ → Maximum α) (l : List γ) {a : α}
    (h : (run m l).get = some a) :
    (∃ x ∈ l, (m x).get = some a) ∧ ∀ x ∈ l, ∀ b, (m x).get = some b → b ≤ a := by
  induction l generalizing a with
  | nil => simp [run, empty] at h
  | cons x l ih =>
    rw [run_cons, merge_get] at h
    simp only [List.mem_cons, exists_eq_or_imp, forall_eq_or_imp]
    cases hx : (m x).get with
    | none =>
      rw [hx] at h
      cases hr : (run m l).get <;> rw [hr] at h
      · contradiction
      · cases h
        obtain ⟨hex, hall⟩ := ih hr
        exact ⟨Or.inr hex, fun b hb => absurd hb (by simp), hall⟩
    | some c =>
      rw [hx] at h
      cases hr : (run m l).get with
      | none =>
        rw [hr] at h
        cases h
        have hnone := (run_eq_none m l).mp hr
        refine ⟨Or.inl rfl, fun b hb => ?_, fun y hy b hb => ?_⟩
        · cases hb; exact Std.IsPreorder.le_refl _
        · simp [hnone y hy] at hb
      | some d =>
        rw [hr] at h
        obtain ⟨hex, hall⟩ := ih hr
        simp only [Option.some.injEq] at h
        split at h
        · rename_i hdc
          subst h
          refine ⟨Or.inl rfl, fun b hb => ?_, fun y hy b hb => ?_⟩
          · cases hb; exact Std.IsPreorder.le_refl _
          · exact Std.IsPreorder.le_trans _ _ _ (hall y hy b hb) hdc
        · rename_i hdc
          subst h
          refine ⟨Or.inr hex, fun b hb => ?_, hall⟩
          cases hb; exact le_of_not_le hdc

/-- The maximum is missing exactly when every item's value is. -/
theorem fold_get_eq_none (m : γ → Maximum α) (xs : Array γ) :
    (fold m xs).get = none ↔ ∀ x ∈ xs, (m x).get = none := by
  rw [Aggregate.fold_eq_foldr]
  simp only [← Array.mem_toList_iff]
  exact run_eq_none m xs.toList

/-- The maximum is `a` exactly when some item's value is `a` and no item's value is above it. -/
theorem fold_get_eq_some (m : γ → Maximum α) (xs : Array γ) (a : α) :
    (fold m xs).get = some a ↔
      (∃ x ∈ xs, (m x).get = some a) ∧ ∀ x ∈ xs, ∀ b, (m x).get = some b → b ≤ a := by
  rw [Aggregate.fold_eq_foldr]
  simp only [← Array.mem_toList_iff]
  change (run m xs.toList).get = some a ↔ _
  constructor
  · exact run_eq_some m xs.toList
  · rintro ⟨⟨x, hx, hxa⟩, hall⟩
    cases hr : (run m xs.toList).get with
    | none => simp [(run_eq_none m _).mp hr x hx] at hxa
    | some r =>
      obtain ⟨⟨y, hy, hyr⟩, hrall⟩ := run_eq_some m xs.toList hr
      exact congrArg some (Std.IsPartialOrder.le_antisymm _ _ (hall y hy r hyr) (hrall x hx a hxa))

end Maximum

end Order

end Inkproof.Core
