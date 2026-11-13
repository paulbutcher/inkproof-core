/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import Plausible

/-! Properties over generic `Nat` inputs, with a fixed seed so failures reproduce. -/

namespace InkproofCoreTest.PlausibleTests

open Plausible Inkproof.Core

def cfg : Configuration := { numInst := 1000, randomSeed := some 1, quiet := true }

abbrev col (x₀ span w₀ x : Nat) : Nat :=
  (Binning.ofNat x₀ (x₀ + span + 1) (w₀ + 1) (Nat.succ_pos _)).col x

abbrev exactColumnsProp : Prop :=
  NamedBinder "x₀" (∀ x₀ : Nat, NamedBinder "span" (∀ span : Nat, NamedBinder "w₀" (∀ w₀ : Nat, NamedBinder "x" (∀ x : Nat,
    (x < x₀ → col x₀ span w₀ x = 0) ∧
    (x₀ + span + 1 ≤ x → col x₀ span w₀ x = w₀) ∧
    (x₀ ≤ x → x < x₀ + span + 1 →
      col x₀ span w₀ x * (span + 1) ≤ (x - x₀) * (w₀ + 1) ∧
      (x - x₀) * (w₀ + 1) < (col x₀ span w₀ x + 1) * (span + 1))))))

abbrev fixedBinningProp : Prop :=
  NamedBinder "x₀" (∀ x₀ : Nat, NamedBinder "span" (∀ span : Nat, NamedBinder "w" (∀ w : Nat, NamedBinder "x" (∀ x : Nat,
    ((Binning.ofFixed (s := 3) x₀ (x₀ + span + 1) (w + 1) (Nat.succ_pos _)).col ⟨x⟩ ==
      (Binning.ofNat x₀ (x₀ + span + 1) (w + 1) (Nat.succ_pos _)).col x) = true))))

def report {p : Prop} (name : String) (r : TestResult p) : IO Bool :=
  match r with
  | .success _ => pure true
  | .gaveUp n => do IO.eprintln s!"FAIL {name}: gave up after {n} discards"; pure false
  | .failure _ xs n => do
    IO.eprintln s!"FAIL {name}: counterexample after {n} shrinks: {xs}"; pure false

def run : IO UInt32 := do
  let results := [
    ← report "timestamp binning has no rounding error" (← Testable.checkIO exactColumnsProp cfg),
    ← report "fixed-point binning agrees with its raw integers" (← Testable.checkIO fixedBinningProp cfg)]
  return if results.all id then 0 else 1

end InkproofCoreTest.PlausibleTests
