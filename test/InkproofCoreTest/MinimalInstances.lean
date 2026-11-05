/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import Inkproof.Core.Proofs

/-! Deliberately impoverished types (VAL-1). If the library came to need more than these offer, this
module would stop compiling. -/

namespace InkproofCoreTest.Minimal

open Inkproof.Core

/-- An x-type with a decidable linear order and nothing else: no arithmetic, equality test, hashing
or `Ord`. -/
structure OrderOnly where
  rank : Nat

instance : LE OrderOnly := ⟨fun a b => a.rank ≤ b.rank⟩

instance : DecidableLE OrderOnly := fun a b => inferInstanceAs (Decidable (a.rank ≤ b.rank))

instance : Std.IsLinearOrder OrderOnly where
  le_refl a := Nat.le_refl a.rank
  le_trans _ _ _ := Nat.le_trans
  le_antisymm a b hab hba := by
    cases a; cases b
    exact congrArg _ (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total a.rank b.rank

/-- A value type with no instances at all. -/
structure Opaque where
  secret : Unit

example (ps : Array (OrderOnly × Option Opaque)) : Series OrderOnly Opaque := Series.ofUnsorted ps

example (ps : Array (OrderOnly × Option Opaque)) : Except SeriesError (Series OrderOnly Opaque) :=
  Series.ofPoints? ps

/-- The gap predicate can only compare x-values, since that is all the type offers. -/
example (s : Series OrderOnly Opaque) : Segmented OrderOnly Opaque :=
  Segmented.splitWhere s fun a b => decide (b ≤ a)

example (s : Series OrderOnly Opaque) (bs : Array Nat) :
    Except SegmentError (Segmented OrderOnly Opaque) :=
  Segmented.ofBreaks? s bs

/-- Order-based aggregates need only the order. -/
example : LawfulAggregate (Minimum OrderOnly) := inferInstance
example : LawfulAggregate (Maximum OrderOnly) := inferInstance

/-- Non-commutative aggregates need nothing of the value type, alone or in products. -/
example : LawfulAggregate (First Opaque × Last Opaque) := inferInstance

example : LawfulAggregate (Total Nat × Total Int × Count × Occupancy) := inferInstance

/-! The published theorems apply to these types, with every hypothesis discharged (VAL-2). -/

example (ps : Array (OrderOnly × Option Opaque)) :
    (Series.ofUnsorted ps).points.toList.Perm ps.toList :=
  Series.ofUnsorted_perm

example (p q : OrderOnly × Option Opaque) (ps : Array (OrderOnly × Option Opaque))
    (hpq : p.1 ≤ q.1) (h : [p, q].Sublist ps.toList) :
    [p, q].Sublist (Series.ofUnsorted ps).points.toList :=
  Series.ofUnsorted_stable hpq h

example (ps : Array (OrderOnly × Option Opaque)) :
    (∃ s : Series OrderOnly Opaque, Series.ofPoints? ps = .ok s) ↔ Sorted (ps.map (·.1)) :=
  Series.ofPoints?_ok_iff

example (s : Series OrderOnly Opaque) (b : Nat) :
    b ∈ (Segmented.splitWhere s fun x y => decide (y ≤ x)).breaks ↔
      ∃ h : 0 < b ∧ b < s.size, decide (s.xs[b]'h.2 ≤ s.xs[b - 1]'(by
        unfold Series.size at h; omega)) = true :=
  Segmented.mem_breaks_splitWhere s _ b

example (g : Segmented OrderOnly Opaque) :
    (g.segments.toList.map (·.points.toList)).flatten = g.series.points.toList :=
  Segmented.flatten_segments g

example (m : Nat → Minimum OrderOnly) (xs : Array Nat) (a : OrderOnly) :
    (Aggregate.fold m xs).get = some a ↔
      (∃ x ∈ xs, (m x).get = some a) ∧ ∀ x ∈ xs, ∀ b, (m x).get = some b → a ≤ b :=
  Minimum.fold_get_eq_some m xs a

example (m : Nat → Maximum OrderOnly) (xs : Array Nat) :
    (Aggregate.fold m xs).get = none ↔ ∀ x ∈ xs, (m x).get = none :=
  Maximum.fold_get_eq_none m xs

/-- First/last over a value type with no instances, through the product. -/
example (m : Nat → Option Opaque) (xs : Array Nat) :
    Aggregate.fold (fun x => (First.mk (m x), Last.mk (m x))) xs =
      (Aggregate.fold (First.mk ∘ m) xs, Aggregate.fold (Last.mk ∘ m) xs) :=
  Aggregate.fold_prod _ _ xs

example (m : Nat → Option Opaque) (xs : Array Nat) :
    (Aggregate.fold (First.mk ∘ m) xs).get = xs.toList.findSome? m :=
  First.fold_get _ xs

end InkproofCoreTest.Minimal
