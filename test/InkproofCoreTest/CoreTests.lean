/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import InkproofCoreTest.Harness

/-! Binning, indexed containers and tiled queries on generated data, natively and under Lasm.
Monotonicity, exactness over every `Nat` and `Int`, and tiled equal to untiled are proved; these
check the instances on the platform's floats and bytes, and the compiled code against the
proved specification. -/

namespace InkproofCoreTest.CoreTests

open Inkproof.Core

def genBounds (g : Rng) : (Nat × Nat × Nat × Nat) × Rng :=
  let (x₀, g) := g.below 1000000
  let (span, g) := g.below 2000000000
  let (w, g) := g.below 2000
  let (x, g) := g.below 3000000000
  ((x₀, x₀ + span + 1, w, x), g)

/-- Column `k` is where `k * (x₁ - x₀) ≤ (x - x₀) * w < (k + 1) * (x₁ - x₀)`, with no rounding. -/
def exactColumns : TestCase := .mk "timestamp binning has no rounding error" <|
  forAll 3000 genBounds fun (x₀, x₁, w₀, x) =>
    let w := w₀ + 1
    let k := (Binning.ofNat x₀ x₁ w (Nat.succ_pos _)).col x
    if x < x₀ then check (k == 0) "below the range is not column 0"
    else if x₁ ≤ x then check (k == w - 1) "past the range is not the last column"
    else check (k * (x₁ - x₀) ≤ (x - x₀) * w && (x - x₀) * w < (k + 1) * (x₁ - x₀))
      s!"column {k} is not the exact floor"

def genFloatArray (g : Rng) : Array Float × Rng :=
  let (n, g) := g.below 40
  g.array n fun g =>
    let (v, g) := g.below 2001
    (Float.ofInt ((v : Int) - 1000) / 8, g)

def floatBinningMonotone : TestCase := .mk "binning ordered floats by breaks is monotone" <|
  forAll 500 genFloatArray fun raw => do
    let some breaks := (raw.qsort (· < ·)).mapM OrdFloat.ofFloat? | throw "NaN"
    let b := Binning.ofBreaks breaks
    let probes := (raw.qsort (· < ·)).filterMap OrdFloat.ofFloat?
    let cols := probes.map b.col
    check (cols.all (· < b.columns)) "column out of range"
    check ((cols.zip (cols.extract 1 cols.size)).all fun (a, c) => a ≤ c) "not monotone"

def fixedBinning : TestCase := .mk "fixed-point binning agrees with its raw integers" <|
  forAll 1000 genBounds fun (x₀, x₁, w, x) =>
    check ((Binning.ofFixed (s := 3) x₀ x₁ (w + 1) (Nat.succ_pos _)).col ⟨x⟩ ==
      (Binning.ofNat x₀ x₁ (w + 1) (Nat.succ_pos _)).col x) "differs from the integer binning"

abbrev Probe := First Nat × Last Nat × Count

def probe (v : Nat) : Probe := (⟨some v⟩, ⟨some v⟩, ⟨1⟩)

def genQuery (g : Rng) : (Array UInt8 × Nat × Nat × Nat × Nat) × Rng :=
  let (n, g) := g.below 300
  let (bytes, g) := g.array n fun g => let (v, g) := g.below 256; (UInt8.ofNat v, g)
  let (b, g) := g.below 6
  let (tile, g) := g.below 9
  let (lo, g) := g.below (n + 5)
  let (hi, g) := g.below (n + 5)
  ((bytes, b, tile, lo, hi), g)

def sameAsNaive (p : Probe) (xs : Array Nat) (lo hi : Nat) : Bool :=
  let slice := xs.extract lo hi
  p.1.get == slice[0]? && p.2.1.get == slice.back? && p.2.2.get == slice.size

def indexedAndTiled : TestCase := .mk "byte buffers and tiled reads query as the plain array does" <|
  forAll 600 genQuery fun (bytes, b₀, tile₀, lo, hi) => do
    let b := b₀ + 2
    let tile := tile₀ + 1
    let ref := bytes.map UInt8.toNat
    let buf := ByteArray.mk bytes
    let p := Pyramid.ofIndexed b (Nat.le_add_left 2 b₀) (fun (v : UInt8) => probe v.toNat) buf
    check (sameAsNaive (p.query lo hi) ref lo hi) "byte buffer query differs"
    let q := Pyramid.ofIndexed b (Nat.le_add_left 2 b₀) (fun (v : UInt8) => probe v.toNat) bytes
    check (sameAsNaive (q.query lo hi) ref lo hi) "array query differs"
    check (sameAsNaive (Pyramid.queryTiled tile (Nat.succ_pos _) b q.levels.size (q.tile tile) lo hi)
      ref lo hi) "tiled query differs"

def floatBuffer : TestCase := .mk "float buffers search as the plain array does" <|
  forAll 500 genFloatArray fun raw => do
    let sorted := raw.qsort (· < ·)
    let buf : FloatArray := ⟨sorted⟩
    for x in raw do
      check (Series.lowerBoundIndexed buf x == (sorted.filter (· < x)).size)
        s!"lower bound of {x} differs"

def tests : List TestCase :=
  [exactColumns, floatBinningMonotone, fixedBinning, indexedAndTiled, floatBuffer]

end InkproofCoreTest.CoreTests
