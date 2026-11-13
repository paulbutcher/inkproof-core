/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import InkproofTools.Test.Harness

/-! Binning, indexed containers and tiled queries on generated data, natively and under Lasm.
Monotonicity, exactness over every `Nat` and `Int`, and tiled equal to untiled are proved; these
check the instances on the platform's floats and bytes, and the compiled code against the
proved specification. -/

namespace InkproofCoreTest.CoreTests

open InkproofTools.Test Inkproof.Core

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
  [floatBinningMonotone, indexedAndTiled, floatBuffer]

end InkproofCoreTest.CoreTests
