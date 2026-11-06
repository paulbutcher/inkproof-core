/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import InkproofCoreTest.Harness

/-! What proofs cannot reach because floats are opaque to them: `OrdFloat.ofFloat?`, and the FP-2
axiom itself, checked against the platform's floats natively and under Lasm. -/

namespace InkproofCoreTest.FloatTests

open Inkproof.Core

def specials : Array Float :=
  #[0.0, -0.0, 1.0, -1.0, 0.5, 1e308, -1e308, 5e-324, -5e-324, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0,
    Float.ofBits 0x7ff8000000000001, Float.ofBits 0xfff0000000000001]

/-- Arbitrary bit patterns (NaN payloads, subnormals, infinities) half the time, and otherwise a
special value or one of a few small numbers, so equal pairs are common. -/
def genFloat (g : Rng) : Float × Rng :=
  let (kind, g) := g.below 3
  match kind with
  | 0 =>
    let (hi, g) := g.below (2 ^ 32)
    let (lo, g) := g.below (2 ^ 32)
    (Float.ofBits (UInt64.ofNat (hi * 2 ^ 32 + lo)), g)
  | 1 =>
    let (i, g) := g.below specials.size
    (specials[i]!, g)
  | _ =>
    let (n, g) := g.below 7
    (Float.ofInt (n - 3 : Int) / 2, g)

instance : Repr Float := ⟨fun x _ => s!"{x} ({x.toBits})"⟩

def ofFloatRejectsOnlyNaN : TestCase := .mk "ofFloat? rejects exactly NaN and removes -0.0" <|
  forAll 2000 genFloat fun x =>
    match OrdFloat.ofFloat? x with
    | none => check x.isNaN "rejected a float that is not NaN"
    | some y => do
      check (!x.isNaN) "accepted NaN"
      check (y.val == x) s!"changed the value to {y.val}"
      check (y.val.toBits != negZeroBits) "kept -0.0"

def ordered (g : Rng) : Option OrdFloat × Rng :=
  let (x, g) := genFloat g
  (OrdFloat.ofFloat? x, g)

def triple (g : Rng) : (Option OrdFloat × Option OrdFloat × Option OrdFloat) × Rng :=
  let (a, g) := ordered g
  let (b, g) := ordered g
  let (c, g) := ordered g
  ((a, b, c), g)

/-- The four parts of `float_le_linear`, with equality checked on the bits. -/
def axiomHolds : TestCase := .mk "the FP-2 axiom holds on this platform's floats" <|
  forAll 5000 triple fun
    | (some a, some b, some c) => do
      check (a ≤ a) s!"not reflexive at {a}"
      check (!(a ≤ b && b ≤ c) || decide (a ≤ c)) s!"not transitive at {a}, {b}, {c}"
      check (!(a ≤ b && b ≤ a) || a.val.toBits == b.val.toBits) s!"not antisymmetric at {a}, {b}"
      check (decide (a ≤ b) || decide (b ≤ a)) s!"not total at {a}, {b}"
    | _ => pure ()

def tests : List TestCase := [ofFloatRejectsOnlyNaN, axiomHolds]

end InkproofCoreTest.FloatTests
