/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import Inkproof.Core.Proofs

/-! FP-1 instantiated: `OrdFloat` serves as an x-type and as a value type, and the published theorems
apply to it with every hypothesis discharged. -/

namespace InkproofCoreTest.FloatInstance

open Inkproof.Core

example : Std.IsLinearOrder OrdFloat := inferInstance
example : LawfulAggregate (Minimum OrdFloat × Maximum OrdFloat) := inferInstance

example (ps : Array (OrdFloat × Option Float)) (p q : OrdFloat × Option Float)
    (hpq : p.1 ≤ q.1) (h : [p, q].Sublist ps.toList) :
    [p, q].Sublist (Series.ofUnsorted ps).points.toList :=
  Series.ofUnsorted_stable hpq h

example (m : Nat → Option OrdFloat) (xs : Array Nat) (a : OrdFloat) :
    (Aggregate.fold (fun x => Minimum.mk (m x)) xs).get = some a ↔
      (∃ x ∈ xs, m x = some a) ∧ ∀ x ∈ xs, ∀ b, m x = some b → a ≤ b :=
  Minimum.fold_get_eq_some _ xs a

end InkproofCoreTest.FloatInstance
