/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Series

namespace Inkproof.Core.Series

universe u v

variable {α : Type u} {β : Type v} [LE α]

/-- The value of series `j` at index `i`, `none` if it is missing or out of range. -/
def valueAt (ss : Array (Series α β)) (j i : Nat) : Option β :=
  match ss[j]? with
  | some s => (s.values[i]?).getD none
  | none => none

theorem valueAt_eq (ss : Array (Series α β)) (j i : Nat) (hj : j < ss.size)
    (hi : i < ss[j].values.size) : valueAt ss j i = ss[j].values[i] := by
  simp [valueAt, hj, hi]

/-- The sum of the present values at index `i` of series `0` to `n - 1` that are negative (`neg`) or not. -/
def signSum [Add β] [Zero β] [LT β] [DecidableLT β] (ss : Array (Series α β)) (i : Nat)
    (neg : Bool) (n : Nat) : β :=
  (List.range n).foldl
    (fun a j => match valueAt ss j i with
      | some w => if decide (w < 0) = neg then a + w else a
      | none => a)
    0

/-- Series `k` stacked at index `i`: `none` if its own value is missing, otherwise the sum of the present values of series `0` to `k` with the same sign as its own. Missing values add nothing. -/
def stackAt [Add β] [Zero β] [LT β] [DecidableLT β] (ss : Array (Series α β)) (k i : Nat) :
    Option β :=
  (valueAt ss k i).map fun v => signSum ss i (decide (v < 0)) (k + 1)

/-- Stacks series that share their x-values: series `k` of the result has the x-values of series `k` and, at each point, the running sum of series `0` to `k` there. Positive and negative values accumulate separately, so a negative value stacks downward from zero. A missing value contributes nothing and its stacked point is missing. -/
def stack [Add β] [Zero β] [LT β] [DecidableLT β] (ss : Array (Series α β)) :
    Array (Series α β) :=
  ss.mapFinIdx fun k s _ =>
    { xs := s.xs
      values := (Array.range s.size).map (stackAt ss k)
      size_eq := by simp [size]
      sorted := s.sorted }

end Inkproof.Core.Series
