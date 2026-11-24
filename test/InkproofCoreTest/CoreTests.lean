/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import Inkproof.Float
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
    let some breaks := (raw.qsort (· < ·)).mapM Inkproof.Float.OrdFloat.ofFloat? | throw "NaN"
    let b := Binning.ofBreaks breaks
    let probes := (raw.qsort (· < ·)).filterMap Inkproof.Float.OrdFloat.ofFloat?
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

def tiledColumns : TestCase := .mk "tiled columns fetch each tile once and match the naive columns" <|
  forAll 600 genQuery fun (bytes, b₀, tile₀, lo, hi) => do
    let b := b₀ + 2
    let tile := tile₀ + 1
    let cols := (lo + hi) % 7
    let ref := bytes.map UInt8.toNat
    let q := Pyramid.ofIndexed b (Nat.le_add_left 2 b₀) (fun (v : UInt8) => probe v.toNat) bytes
    let fetch (k t : Nat) : StateM (Array (Nat × Nat)) (Array Probe) := do
      modify (·.push (k, t))
      pure (q.tile tile k t)
    let (got, fetched) := (Pyramid.columnsM tile (Nat.succ_pos _) b q.levels.size fetch (pure ())
      lo hi cols).run #[]
    check (got.size == cols) "wrong number of columns"
    for (col, c) in got.zipIdx do
      let a := Pyramid.columnBound lo hi cols c
      let e := Pyramid.columnBound lo hi cols (c + 1)
      check (sameAsNaive col ref a e) s!"column {c} differs"
    check (fetched.all fun f => (fetched.filter (· == f)).size == 1) "a tile was fetched twice"
    let k := b₀ % q.levels.size
    let (snapped, _) := (Pyramid.columnsFromM tile (Nat.succ_pos _) b q.levels.size fetch (pure ()) k
      lo hi cols).run #[]
    let w := b ^ k
    for (col, c) in snapped.zipIdx do
      let a := Pyramid.columnBound lo hi cols c * w
      let e := Pyramid.columnBound lo hi cols (c + 1) * w
      check (sameAsNaive col ref a e) s!"snapped column {c} differs"

def floatBuffer : TestCase := .mk "float buffers search as the plain array does" <|
  forAll 500 genFloatArray fun raw => do
    let sorted := raw.qsort (· < ·)
    let buf : FloatArray := ⟨sorted⟩
    for x in raw do
      check (Series.lowerBoundIndexed buf x == (sorted.filter (· < x)).size)
        s!"lower bound of {x} differs"

def calendarKnownDates : TestCase := .mk "calendar leap days and century boundaries" <| do
  let cases : List (Int × Nat × Nat × Int) :=
    [(1970, 1, 1, 0), (1969, 12, 31, -1), (2000, 2, 29, 11016), (2000, 3, 1, 11017),
     (1900, 2, 28, -25509), (1900, 3, 1, -25508), (2100, 2, 28, 47540), (2100, 3, 1, 47541),
     (2024, 2, 29, 19782)]
  for (y, m, d, z) in cases do
    check (Calendar.daysFromCivil y m d == z) s!"daysFromCivil {y}-{m}-{d}"
    check (Calendar.civilFromDays z == (y, m, d)) s!"civilFromDays {z}"

def calendarRoundTrip : TestCase := .mk "calendar days are consecutive dates" <| do
  for i in [1:1600000:31] do
    let z : Int := (i : Int) - 800000
    let c := Calendar.civilFromDays z
    check (Calendar.daysFromCivil c.1 c.2.1 c.2.2 == z) s!"round trip {z}"
    let n := Calendar.civilFromDays (z - 1)
    check (Calendar.nextDay n == c) s!"successor of day {z - 1}"

def roundSignificantKnown : TestCase := .mk "roundSignificant on known values" <| do
  let cases : List (Nat × Float × Float) :=
    [(3, 99.99999999, 100.0), (4, 1234567.0, 1235000.0), (3, -0.00123456, -0.00123),
     (2, 0.125, 0.13), (1, 9.5, 10.0), (3, 1e300, 1e300)]
  for (d, x, y) in cases do
    check (Decimal.roundSignificant d x == y) s!"roundSignificant {d} {x}"
  for d in [1, 3, 17] do
    for k in [0:41] do
      let p := Float.ofScientific 1 true k
      check (Decimal.roundSignificant d p == p) s!"10^-{k} with {d} digits"
      let q := Float.ofScientific 1 false k
      check (Decimal.roundSignificant d q == q) s!"10^{k} with {d} digits"
  check (Decimal.roundSignificant 3 0.0 == 0.0) "zero"
  check (Decimal.roundSignificant 3 (1.0 / 0.0) == 1.0 / 0.0) "infinity"
  check (Decimal.roundSignificant 3 (-1.0 / 0.0) == -1.0 / 0.0) "negative infinity"
  check (Decimal.roundSignificant 3 (0.0 / 0.0)).isNaN "nan"

def roundSignificantClose : TestCase := .mk "roundSignificant is idempotent and within half a unit" <|
  forAll 500 (fun g =>
    let (m, g) := g.below 1000000000
    let (e, g) := g.below 40
    (Float.ofScientific (m + 1) true e, g)) fun x => do
    for d in [1, 2, 5] do
      let y := Decimal.roundSignificant d x
      check (Decimal.roundSignificant d y == y) s!"{d} digits of {x} not idempotent"
      check ((y - x).abs ≤ x.abs * 0.5 * Float.pow 10 (1 - d.toFloat) * (1 + 1e-9))
        s!"{d} digits of {x} is {y}"

def tests : List TestCase :=
  [floatBinningMonotone, indexedAndTiled, tiledColumns, floatBuffer, calendarKnownDates,
   calendarRoundTrip, roundSignificantKnown, roundSignificantClose]

end InkproofCoreTest.CoreTests
