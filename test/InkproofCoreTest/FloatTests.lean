/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import InkproofCoreTest.Harness

/-! What proofs do not cover: that `OrdFloat.ofFloat?` keeps the value, and Lean's model of `Float` (`float_le_linear`
and `float_rounding_model`) checked against the compiled float operations, natively and under Lasm. -/

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
def orderHolds : TestCase := .mk "float_le_linear holds of the compiled floats" <|
  forAll 5000 triple fun
    | (some a, some b, some c) => do
      check (a ≤ a) s!"not reflexive at {a}"
      check (!(a ≤ b && b ≤ c) || decide (a ≤ c)) s!"not transitive at {a}, {b}, {c}"
      check (!(a ≤ b && b ≤ a) || a.val.toBits == b.val.toBits) s!"not antisymmetric at {a}, {b}"
      check (decide (a ≤ b) || decide (b ≤ a)) s!"not total at {a}, {b}"
    | _ => pure ()

def finitePair (g : Rng) : (Float × Float) × Rng :=
  let (x, g) := genFloat g
  let (y, g) := genFloat g
  ((x, y), g)

/-- Exponents near 1 make sums and differences cancel and products stay in range. -/
def genNearOne (g : Rng) : Float × Rng :=
  let (hi, g) := g.below (2 ^ 20)
  let (lo, g) := g.below (2 ^ 32)
  let (e, g) := g.below 40
  let (sign, g) := g.below 2
  let bits := (sign * 2 ^ 63 + (1003 + e) * 2 ^ 52 + hi * 2 ^ 32 + lo)
  (Float.ofBits (UInt64.ofNat bits), g)

def nearPair (g : Rng) : (Float × Float) × Rng :=
  let (x, g) := genNearOne g
  let (y, g) := genNearOne g
  ((x, y), g)

def toRatValues : TestCase := .mk "toRat reads exact values" do
  check (Float.toRat 1.0 == some 1) "1.0"
  check (Float.toRat (-0.75) == some (-3 / 4)) "-0.75"
  check (Float.toRat 0.0 == some 0 && Float.toRat (-0.0) == some 0) "zeros"
  check (Float.toRat (Float.ofBits 1) == some (scaleTwoPow 1 (-1074))) "least subnormal"
  check (Float.toRat (Float.ofBits 0x7fefffffffffffff) == some maxFloat) "largest finite"
  check (Float.toRat (0.0 / 0.0) == none && Float.toRat (1.0 / 0.0) == none) "NaN and infinity"

def roundingModel : (Float × Float) → Except String Unit := fun (x, y) =>
  match Float.toRat x, Float.toRat y with
  | some a, some b => do
    let within (name : String) (z : Float) (r : Rat) : Except String Unit :=
      if decide (NormalRange r) then
        match Float.toRat z with
        | none => check false s!"{name} of {x} and {y} is not finite"
        | some q => check (ratAbs (q - r) ≤ ratAbs r / scaleTwoPow 1 53) s!"{name} of {x} and {y} is off"
      else pure ()
    within "sum" (x + y) (a + b)
    within "difference" (x - y) (a - b)
    within "product" (x * y) (a * b)
    if b != 0 then within "quotient" (x / y) (a / b)
    check (decide (x ≤ y) == decide (a ≤ b)) s!"order of {x} and {y} disagrees with their values"
  | _, _ => pure ()

def roundingModelHolds : TestCase := .mk "the rounding model holds of the compiled floats" do
  forAll 5000 finitePair roundingModel
  forAll 5000 nearPair roundingModel

def literalsExact : TestCase := .mk "integer literals are exact" <|
  forAll 2000 (fun g => g.below (2 ^ 53)) fun n =>
    check (Float.toRat (Float.ofNat n) == some (n : Rat)) s!"{n}"

def tests : List TestCase :=
  [ofFloatRejectsOnlyNaN, orderHolds, toRatValues, roundingModelHolds, literalsExact]

end InkproofCoreTest.FloatTests
