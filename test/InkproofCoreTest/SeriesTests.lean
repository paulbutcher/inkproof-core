/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import InkproofCoreTest.Harness

namespace InkproofCoreTest.SeriesTests

open Inkproof.Core

abbrev Point := Nat × Option Nat

/-- Small x-values, so repeats are common, and roughly one value in three missing. -/
def genPoint (g : Rng) : Point × Rng :=
  let (x, g) := g.below 10
  let (m, g) := g.below 3
  let (v, g) := g.below 100
  ((x, if m == 0 then none else some v), g)

/-- Sizes 0 to 12, so empty and single-point inputs come up often. -/
def genPoints (g : Rng) : Array Point × Rng :=
  let (n, g) := g.below 13
  g.array n genPoint

/-- Mostly sorted inputs, so the accepting path is exercised as often as the rejecting one. -/
def genMaybeSorted (g : Rng) : Array Point × Rng :=
  let (ps, g) := genPoints g
  let (k, g) := g.below 2
  (if k == 0 then ps.qsort (·.1 < ·.1) else ps, g)

def naiveFirstDescent (xs : List Nat) : Option Nat :=
  (List.range (xs.length - 1)).find? fun i => xs.getD (i + 1) 0 < xs.getD i 0

/-- Insertion sort that places each point after any already placed with an equal x-value. -/
def naiveStableSort (ps : List Point) : List Point :=
  let rec insert (p : Point) : List Point → List Point
    | [] => [p]
    | q :: qs => if p.1 < q.1 then p :: q :: qs else q :: insert p qs
  ps.foldl (fun acc p => insert p acc) []

def ofPointsAgreesWithNaive : TestCase := .mk "ofPoints? accepts exactly the sorted inputs" <|
  forAll 500 genMaybeSorted fun ps => do
    let xs := ps.toList.map (·.1)
    match Series.ofPoints? ps, naiveFirstDescent xs with
    | .ok s, none => check (s.points == ps) "accepted series changed its points"
    | .error (.unsorted i), some j => check (i == j) s!"reported descent at {i}, expected {j}"
    | .ok _, some j => throw s!"accepted an input that descends at {j}"
    | .error e, _ => throw s!"unexpected error: {repr e}"

def ofArraysRejectsSizeMismatch : TestCase := .mk "ofArrays? rejects arrays of different sizes" <|
  forAll 100 genPoints fun ps =>
    match Series.ofArrays? (ps.map (·.1)) (ps.map (·.2) |>.push none) with
    | .error (.sizeMismatch a b) => check (a == ps.size && b == ps.size + 1) "wrong sizes reported"
    | _ => throw "accepted arrays of different sizes"

def ofUnsortedIsStableSort : TestCase := .mk "ofUnsorted is a stable sort by x-value" <|
  forAll 500 genPoints fun ps =>
    check ((Series.ofUnsorted ps).points.toList == naiveStableSort ps.toList) "differs from naive"

def gapAt (a b : Nat) : Bool := b ≥ a + 3

def splitWhereSplitsAtGaps : TestCase := .mk "splitWhere breaks exactly where the predicate holds" <|
  forAll 500 genPoints fun ps => do
    let seg := Segmented.splitWhere (Series.ofUnsorted ps) gapAt
    let segs := seg.segments.toList.map (·.points.toList)
    let all := (Series.ofUnsorted ps).points.toList
    check (segs.flatten == all) "segments do not reassemble the series"
    check (segs.all (!·.isEmpty)) "a segment is empty"
    for s in segs do
      check ((s.zip s.tail).all fun (p, q) => !gapAt p.1 q.1) "a gap inside a segment"
    for (s, t) in segs.zip segs.tail do
      match s.getLast?, t.head? with
      | some p, some q => check (gapAt p.1 q.1) "segments split where there is no gap"
      | _, _ => throw "a segment is empty"

def genBreaks (g : Rng) : (Array Point × Array Nat) × Rng :=
  let (ps, g) := genPoints g
  let (n, g) := g.below 4
  let (bs, g) := g.array n (·.below (ps.size + 1))
  let (k, g) := g.below 2
  ((ps, if k == 0 then (bs.qsort (· < ·)).toList.eraseDups.toArray else bs), g)

def ofBreaksAgreesWithNaive : TestCase := .mk "ofBreaks? accepts exactly the valid breaks" <|
  forAll 500 genBreaks fun (ps, bs) => do
    let s := Series.ofUnsorted ps
    let l := bs.toList
    let valid := (l.zip l.tail).all (fun (a, b) => a < b) && l.all (fun b => 0 < b && b < s.size)
    match Segmented.ofBreaks? s bs with
    | .ok g =>
      check valid "accepted invalid breaks"
      let starts := (List.range g.numSegments).map g.segmentStart
      check (starts == (if s.size == 0 then [] else 0 :: l)) "segments do not start at the breaks"
    | .error _ => check (!valid) "rejected valid breaks"

def tests : List TestCase :=
  [ofPointsAgreesWithNaive, ofArraysRejectsSizeMismatch, ofUnsortedIsStableSort,
   splitWhereSplitsAtGaps, ofBreaksAgreesWithNaive]

end InkproofCoreTest.SeriesTests
