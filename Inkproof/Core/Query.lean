/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Segmented
import Inkproof.Core.Pyramid

namespace Inkproof.Core

universe u v w

namespace Series

variable {α : Type u} {β : Type v} [LE α] [DecidableLE α]

/-- Binary search between `lo` and `hi` for the first index whose x-value is at least `x`. -/
def lowerBoundFrom (xs : Array α) (x : α) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if h : mid < xs.size then
      if x ≤ xs[mid] then lowerBoundFrom xs x lo mid else lowerBoundFrom xs x (mid + 1) hi
    else lo
  else lo
termination_by hi - lo

/-- The index of the first point whose x-value is at least `x`, or `size` if there is none. The
points before it are exactly those below `x` (`Series.lt_lowerBound_iff`). -/
def lowerBound (s : Series α β) (x : α) : Nat := lowerBoundFrom s.xs x 0 s.size

/-- Whether a point's x-value lies in `[x₀, x₁)`. -/
def inRange (x₀ x₁ : α) (p : α × Option β) : Bool := decide (x₀ ≤ p.1) && !decide (x₁ ≤ p.1)

end Series

/-- One pyramid per segment of a segmented series, each over the measures of its segment's points,
so no node merges points from two segments. -/
structure SegmentedPyramid (α : Type u) (β : Type v) (M : Type w) [LE α] [Aggregate M] where
  segmented : Segmented α β
  measure : α × Option β → M
  branching : Nat
  two_le_branching : 2 ≤ branching
  pyramids : Array (Pyramid M)
  size_pyramids : pyramids.size = segmented.numSegments
  pyramids_eq : ∀ k (h : k < pyramids.size),
    pyramids[k] = Pyramid.ofMeasure branching two_le_branching measure (segmented.segment k).points

namespace SegmentedPyramid

variable {α : Type u} {β : Type v} {M : Type w} [LE α] [Aggregate M]

/-- Builds a pyramid for every segment of `g`. -/
def build (g : Segmented α β) (measure : α × Option β → M) (branching : Nat)
    (h : 2 ≤ branching) : SegmentedPyramid α β M :=
  { segmented := g, measure, branching, two_le_branching := h
    pyramids := (Array.range g.numSegments).map fun k =>
      Pyramid.ofMeasure branching h measure (g.segment k).points
    size_pyramids := by simp
    pyramids_eq := fun k hk => by simp }

/-- One result per segment: the merge of the measures of that segment's points with x-values in
`[x₀, x₁)`, never of points from two segments (`SegmentedPyramid.getElem_query`). -/
def query [DecidableLE α] (sp : SegmentedPyramid α β M) (x₀ x₁ : α) : Array M :=
  sp.pyramids.mapIdx fun k p =>
    let s := sp.segmented.segment k
    p.query (s.lowerBound x₀) (s.lowerBound x₁)

/-- The results of `query` for just the segments with points in `[x₀, x₁)`, each paired with its
segment index, in segment order (`SegmentedPyramid.queryOverlapping_eq`). Its cost grows with the
number of those segments, not with `numSegments`. -/
def queryOverlapping [DecidableLE α] (sp : SegmentedPyramid α β M) (x₀ x₁ : α) :
    Array (Nat × M) :=
  let g := sp.segmented
  let lo := g.series.lowerBound x₀
  let hi := g.series.lowerBound x₁
  -- Segments before `first` end at or before `lo`, and those from `last` on start at or after `hi`.
  let first := Series.lowerBoundFrom g.breaks (lo + 1) 0 g.breaks.size
  let last := Series.lowerBoundFrom g.breaks hi 0 g.breaks.size + 1
  (Array.range' first (last - first)).filterMap fun k =>
    if h : k < sp.pyramids.size then
      let start := g.segmentStart k
      let a := max lo start - start
      let b := min hi (g.segmentStop k) - start
      if a < b then some (k, sp.pyramids[k].query a b) else none
    else none

end SegmentedPyramid

end Inkproof.Core
