/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Series

namespace Inkproof.Core

universe u v

/-- A series divided into segments at explicit gaps. Each break is the index of the first point of
a segment after the first, so no segment is empty and nothing may join points across a break. -/
structure Segmented (α : Type u) (β : Type v) [LE α] where
  series : Series α β
  breaks : Array Nat
  breaks_increasing : ∀ i (h : i + 1 < breaks.size), breaks[i] < breaks[i + 1]
  breaks_bounded : ∀ i (h : i < breaks.size), 0 < breaks[i] ∧ breaks[i] < series.size

/-- Why `Segmented.ofBreaks?` rejected its breaks. -/
inductive SegmentError where
  /-- The break at `index + 1` is not greater than the one at `index`. -/
  | unsortedBreaks (index : Nat)
  /-- A break must lie strictly inside the series, or it would leave a segment empty. -/
  | breakOutOfRange (break_ : Nat) (size : Nat)
  deriving Repr, DecidableEq

namespace Segmented

variable {α : Type u} {β : Type v} [LE α]

/-- A series with no gaps: one segment, or none if the series is empty. -/
def single (s : Series α β) : Segmented α β :=
  ⟨s, #[], fun _ h => absurd h (by simp), fun _ h => absurd h (by simp)⟩

/-- Checks that the breaks increase strictly and lie strictly inside the series. -/
def ofBreaks? (s : Series α β) (breaks : Array Nat) : Except SegmentError (Segmented α β) :=
  match hd : Internal.firstAdjacentFailure (fun a b => decide (a < b)) breaks 0 with
  | some i => .error (.unsortedBreaks i)
  | none =>
    match hf : breaks.find? (fun b => !(0 < b && b < s.size)) with
    | some b => .error (.breakOutOfRange b s.size)
    | none =>
      .ok ⟨s, breaks,
        fun i h => by simpa using Internal.adjacent_of_firstAdjacentFailure hd i (Nat.zero_le i) h,
        fun i h => by
          have := Array.find?_eq_none.mp hf _ (Array.getElem_mem h)
          simp at this
          omega⟩

/-- Splits the series wherever `gap` holds between the x-values of adjacent points. The library
never decides on its own where a gap is. -/
def splitWhere (s : Series α β) (gap : α → α → Bool) : Segmented α β :=
  let isBreak (i : Nat) : Bool :=
    if h : i < s.size ∧ 0 < i then gap (s.xs[i - 1]'(by unfold Series.size at h; omega)) (s.xs[i]'h.1)
    else false
  let candidates := List.range' 1 (s.size - 1)
  have hsorted : (candidates.filter isBreak).Pairwise (· < ·) :=
    (List.pairwise_lt_range' 1 (by omega)).filter _
  have hmem : ∀ b ∈ candidates.filter isBreak, 0 < b ∧ b < s.size := by
    intro b hb
    rw [List.mem_filter, List.mem_range'] at hb
    omega
  { series := s
    breaks := (candidates.filter isBreak).toArray
    breaks_increasing := fun i h => by
      exact List.pairwise_iff_getElem.mp hsorted i (i + 1) (by simp at h; omega) (by simpa using h)
        (by omega)
    breaks_bounded := fun i h => by
      exact hmem _ (List.getElem_mem (by simpa using h)) }

/-- The number of segments: none for an empty series, otherwise one more than the breaks. -/
def numSegments (g : Segmented α β) : Nat :=
  if g.series.size = 0 then 0 else g.breaks.size + 1

/-- The index of the first point of segment `k`. -/
def segmentStart (g : Segmented α β) (k : Nat) : Nat :=
  if k = 0 then 0 else g.breaks[k - 1]?.getD g.series.size

/-- One past the index of the last point of segment `k`. -/
def segmentStop (g : Segmented α β) (k : Nat) : Nat :=
  g.breaks[k]?.getD g.series.size

/-- Segment `k` as a series of its own; empty when `k` is not below `numSegments`. -/
def segment (g : Segmented α β) (k : Nat) : Series α β :=
  g.series.slice (g.segmentStart k) (g.segmentStop k)

def segments (g : Segmented α β) : Array (Series α β) :=
  (Array.range g.numSegments).map g.segment

end Segmented

end Inkproof.Core
