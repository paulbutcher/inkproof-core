/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core

open Inkproof.Core

abbrev Stats := Minimum Int × Maximum Int × Count × Total Int

def stat (x : Int) : Stats := (⟨some x⟩, ⟨some x⟩, ⟨1⟩, ⟨x⟩)

def time (name : String) (reps : Nat) (act : Nat → Nat) : IO Unit := do
  let t₀ ← IO.monoNanosNow
  let mut sink := 0
  for i in [0:reps] do
    sink := sink + act i
  let t₁ ← IO.monoNanosNow
  IO.println s!"{name}: {(t₁ - t₀) / reps / 1000} us per run (checksum {sink})"

def main : IO Unit := do
  let n := 1000000
  let xs : Array Int := (Array.range n).map fun i => ((i * 7919) % 10007 : Nat)
  time "build pyramid, 1M points" 5 fun i =>
    let p := Pyramid.ofMeasure 4 (by omega) stat (xs.extract i xs.size)
    p.levels.size
  let p := Pyramid.ofMeasure 4 (by omega) stat xs
  time "query pyramid, 1000 ranges" 20 fun i => Id.run do
    let mut s := 0
    for j in [0:1000] do
      let lo := (j * 997 + i) % (n / 2)
      s := s + (p.query lo (lo + 1 + (j * 7919) % (n / 2))).2.2.2.get.toNat
    return s
  time "fold, 1M points" 5 fun i =>
    (Aggregate.fold stat (xs.extract i xs.size)).2.2.2.get.toNat
