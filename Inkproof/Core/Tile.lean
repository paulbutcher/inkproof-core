/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Pyramid

namespace Inkproof.Core

universe u

open Aggregate (empty merge foldRange)

namespace Aggregate

variable {M : Type u} [Aggregate M]

/-- Merges nodes `lo` to `hi - 1` of a level stored as tiles of `n` nodes, where `tile t` holds
nodes `t * n` to `t * n + n - 1`, fetching only the tiles the range touches
(`Aggregate.foldTiles_eq`). -/
def foldTiles (n : Nat) (hn : 0 < n) (tile : Nat → Array M) (lo hi : Nat) : M :=
  if lo < hi then
    let stop := min hi ((lo / n + 1) * n)
    merge (foldRange (tile (lo / n)) (lo - lo / n * n) (stop - lo / n * n))
      (foldTiles n hn tile stop hi)
  else empty
termination_by hi - lo
decreasing_by
  have := Nat.lt_mul_div_succ lo hn
  rw [Nat.mul_comm] at this
  omega

end Aggregate

open Aggregate (foldTiles)

namespace Pyramid

variable {M : Type u} [Aggregate M]

/-- Tile `t` of level `k` when levels are cut into runs of `n` nodes: nodes `t * n` to
`t * n + n - 1`, fewer in the last tile, none past the end or in a level that does not exist. -/
def tile (p : Pyramid M) (n k t : Nat) : Array M :=
  (p.levels.getD k #[]).extract (t * n) ((t + 1) * n)

/-- How many tiles level `k` is cut into. -/
def numTiles (p : Pyramid M) (n k : Nat) : Nat :=
  ((p.levels.getD k #[]).size + n - 1) / n

/-- `Pyramid.queryFrom` over levels held as tiles of `n` nodes, where `tile k t` is tile `t` of
level `k` and `numLevels` is the number of levels. Only the tiles the query's partial groups
touch are read (`Pyramid.queryTiled_eq`). -/
def queryFromTiled (n : Nat) (hn : 0 < n) (b numLevels : Nat) (tile : Nat → Nat → Array M)
    (k lo hi : Nat) : M :=
  if k < numLevels then
    if k + 1 < numLevels then
      let lo' := (lo + b - 1) / b
      let hi' := hi / b
      if lo' < hi' then
        merge (foldTiles n hn (tile k) lo (lo' * b))
          (merge (queryFromTiled n hn b numLevels tile (k + 1) lo' hi')
            (foldTiles n hn (tile k) (hi' * b) hi))
      else foldTiles n hn (tile k) lo hi
    else foldTiles n hn (tile k) lo hi
  else empty
termination_by numLevels - k

/-- Merges the measures of points `lo` to `hi - 1` from a pyramid with `branching` and `numLevels`
whose levels are fetched as tiles, with the same result as `Pyramid.query` on the whole pyramid
(`Pyramid.queryTiled_eq`). -/
def queryTiled (n : Nat) (hn : 0 < n) (branching numLevels : Nat) (tile : Nat → Nat → Array M)
    (lo hi : Nat) : M :=
  queryFromTiled n hn branching numLevels tile 0 lo hi

end Pyramid

end Inkproof.Core
