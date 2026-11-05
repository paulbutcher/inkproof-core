/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import InkproofCoreTest.Harness

namespace InkproofCoreTest.AggregateTests

open Inkproof.Core

/-- Sizes 0 to 15, values below 50 so ties are common, roughly one in three missing. -/
def genValues (g : Rng) : Array (Option Nat) × Rng :=
  let (n, g) := g.below 16
  g.array n fun g =>
    let (m, g) := g.below 3
    let (v, g) := g.below 50
    (if m == 0 then none else some v, g)

def present (vs : Array (Option Nat)) : List Nat := vs.toList.filterMap id

def foldAgrees {M : Type} [Aggregate M] [BEq M] [Repr M] (name : String)
    (measure : Option Nat → M) (naive : Array (Option Nat) → M) : TestCase :=
  .mk s!"{name} folds to the naive result" <| forAll 300 genValues fun vs => do
    let got := Aggregate.fold measure vs
    let want := naive vs
    check (got == want) s!"got {reprStr got}, expected {reprStr want}"

def tests : List TestCase := [
  foldAgrees "Minimum" (Minimum.mk ·) fun vs => ⟨(present vs).min?⟩,
  foldAgrees "Maximum" (Maximum.mk ·) fun vs => ⟨(present vs).max?⟩,
  foldAgrees "First" (First.mk ·) fun vs => ⟨(present vs).head?⟩,
  foldAgrees "Last" (Last.mk ·) fun vs => ⟨(present vs).getLast?⟩,
  foldAgrees "Count of present values" (fun v => Count.mk (if v.isSome then 1 else 0))
    fun vs => ⟨(present vs).length⟩,
  foldAgrees "Total" (fun v => Total.mk (v.getD 0)) fun vs => ⟨(present vs).sum⟩,
  .mk "Occupancy holds exactly the indices seen" <| forAll 300 genValues fun vs => do
    let o := Aggregate.fold (fun v => v.elim ⟨0⟩ Occupancy.singleton) vs
    for i in [0:60] do
      check (o.contains i == (present vs).contains i) s!"index {i} wrong",
  foldAgrees "First, maximum, minimum and last together"
    (fun v => (First.mk v, Maximum.mk v, Minimum.mk v, Last.mk v))
    fun vs => let p := present vs; (⟨p.head?⟩, ⟨p.max?⟩, ⟨p.min?⟩, ⟨p.getLast?⟩)
]

end InkproofCoreTest.AggregateTests
