/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core

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

end InkproofCoreTest.Minimal
