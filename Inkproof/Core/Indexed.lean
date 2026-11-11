/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Query
import Inkproof.Core.Segmented

namespace Inkproof.Core

universe u v w

/-- A container read by position, so algorithms accept float arrays, byte buffers or ordinary
arrays without first converting them. -/
class IndexedSeries (σ : Type u) (α : outParam (Type v)) where
  size : σ → Nat
  get : (s : σ) → (i : Nat) → i < size s → α

namespace IndexedSeries

variable {σ : Type u} {α : Type v} [IndexedSeries σ α]

/-- The elements as an array, for stating what an algorithm over `σ` computes. -/
def toArray (s : σ) : Array α :=
  Array.ofFn fun i : Fin (size s) => get s i i.isLt

instance : IndexedSeries (Array α) α := ⟨Array.size, fun a i h => a[i]⟩

instance : IndexedSeries ByteArray UInt8 := ⟨ByteArray.size, fun a i h => a[i]⟩

instance : IndexedSeries FloatArray Float := ⟨FloatArray.size, fun a i h => a[i]⟩

end IndexedSeries

namespace Pyramid

variable {M : Type w} [Aggregate M]

/-- Builds the pyramid over the measures of the elements of `s`, reading them by index. -/
def ofIndexed {σ : Type u} {γ : Type v} [IndexedSeries σ γ] (branching : Nat) (h : 2 ≤ branching)
    (measure : γ → M) (s : σ) : Pyramid M :=
  build branching h (Array.ofFn fun i : Fin (IndexedSeries.size s) =>
    measure (IndexedSeries.get s i i.isLt))

end Pyramid

namespace Series

variable {α : Type u} [LE α] [DecidableLE α]

/-- `lowerBoundFrom` reading x-values through `get`, which is defined below `n`. -/
def lowerBoundFromBy (n : Nat) (get : (i : Nat) → i < n → α) (x : α) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if h : mid < n then
      if x ≤ get mid h then lowerBoundFromBy n get x lo mid else lowerBoundFromBy n get x (mid + 1) hi
    else lo
  else lo
termination_by hi - lo

/-- `Series.lowerBound` for x-values held in any indexed container: the index of the first
x-value at least `x` (`Series.lowerBoundIndexed_eq`). -/
def lowerBoundIndexed {σ : Type v} [IndexedSeries σ α] (xs : σ) (x : α) : Nat :=
  lowerBoundFromBy (IndexedSeries.size xs) (IndexedSeries.get xs) x 0 (IndexedSeries.size xs)

end Series

end Inkproof.Core
