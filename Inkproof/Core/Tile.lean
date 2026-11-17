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
@[specialize] def foldTiles (n : Nat) (hn : 0 < n) (tile : Nat → Array M) (lo hi : Nat) : M :=
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

/-- `foldTiles` with the tiles fetched in a monad. Only the tiles the range touches are fetched, one at a
time, and `yield` runs after each so that a long range can hand control back to its host
(`Aggregate.foldTilesM_id`). -/
@[specialize] def foldTilesM {m : Type u → Type u} [Monad m] (n : Nat) (hn : 0 < n)
    (fetch : Nat → m (Array M)) (yield : m PUnit) (lo hi : Nat) : m M :=
  if lo < hi then do
    let stop := min hi ((lo / n + 1) * n)
    let tile ← fetch (lo / n)
    let here := foldRange tile (lo - lo / n * n) (stop - lo / n * n)
    yield
    let rest ← foldTilesM n hn fetch yield stop hi
    pure (merge here rest)
  else pure empty
termination_by hi - lo
decreasing_by
  have := Nat.lt_mul_div_succ lo hn
  rw [Nat.mul_comm] at this
  omega

end Aggregate

open Aggregate (foldTiles foldTilesM)

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
@[specialize]
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
@[specialize]
def queryTiled (n : Nat) (hn : 0 < n) (branching numLevels : Nat) (tile : Nat → Nat → Array M)
    (lo hi : Nat) : M :=
  queryFromTiled n hn branching numLevels tile 0 lo hi

/-- `Pyramid.queryFromTiled` with the tiles fetched in a monad, where `fetch k t` is tile `t` of level
`k`. Only the tiles the query touches are fetched, and `yield` runs after each
(`Pyramid.queryFromTiledM_id`). -/
@[specialize]
def queryFromTiledM {m : Type u → Type u} [Monad m] (n : Nat) (hn : 0 < n) (b numLevels : Nat)
    (fetch : Nat → Nat → m (Array M)) (yield : m PUnit) (k lo hi : Nat) : m M :=
  if k < numLevels then
    if k + 1 < numLevels then
      let lo' := (lo + b - 1) / b
      let hi' := hi / b
      if lo' < hi' then do
        let left ← foldTilesM n hn (fetch k) yield lo (lo' * b)
        let mid ← queryFromTiledM n hn b numLevels fetch yield (k + 1) lo' hi'
        let right ← foldTilesM n hn (fetch k) yield (hi' * b) hi
        pure (merge left (merge mid right))
      else foldTilesM n hn (fetch k) yield lo hi
    else foldTilesM n hn (fetch k) yield lo hi
  else pure empty
termination_by numLevels - k

/-- `Pyramid.queryTiled` with the tiles fetched in a monad (`Pyramid.queryTiledM_id`). -/
@[specialize]
def queryTiledM {m : Type u → Type u} [Monad m] (n : Nat) (hn : 0 < n) (branching numLevels : Nat)
    (fetch : Nat → Nat → m (Array M)) (yield : m PUnit) (lo hi : Nat) : m M :=
  queryFromTiledM n hn branching numLevels fetch yield 0 lo hi

/-- Boundary `c` when the range `lo` to `hi` is cut into `cols` columns of equal length, rounding down.
Consecutive boundaries are the ends of a column, so the columns partition the range
(`Pyramid.exists_unique_columnBound`). -/
def columnBound (lo hi cols c : Nat) : Nat := lo + (hi - lo) * c / cols

/-- The merge of each of `cols` columns, column `c` being nodes `columnBound lo hi cols c` to
`columnBound lo hi cols (c + 1) - 1` of level `k` (`Pyramid.getElem_columnsFrom`). With `k = 0` these
are leaves, the exact columns of `Pyramid.columns`; with a higher `k` the boundaries are nodes of level
`k`, so each column covers whole nodes of that level, the columns partition them, and no level below
`k` is read. -/
@[specialize]
def columnsFrom (n : Nat) (hn : 0 < n) (b numLevels : Nat) (tile : Nat → Nat → Array M)
    (k lo hi cols : Nat) : Array M :=
  Array.ofFn (n := cols) fun c =>
    queryFromTiled n hn b numLevels tile k (columnBound lo hi cols c) (columnBound lo hi cols (c + 1))

/-- The merge of each of `cols` equal columns of leaves `lo` to `hi - 1`, column `c` being
`Pyramid.queryTiled` over `columnBound lo hi cols c` to `columnBound lo hi cols (c + 1)`
(`Pyramid.getElem_columns`). Column ends fall anywhere, so at full zoom-out each column reads the
finest level's tile at both ends, up to `2 * cols` of them; use `Pyramid.columnsFrom` with a higher
level to read none. -/
@[specialize]
def columns (n : Nat) (hn : 0 < n) (b numLevels : Nat) (tile : Nat → Nat → Array M)
    (lo hi cols : Nat) : Array M :=
  columnsFrom n hn b numLevels tile 0 lo hi cols

/-- `Pyramid.columnsFrom` with the tiles fetched in a monad. Each tile is fetched at most once, because
a level's nodes are read in increasing order across columns, so only the latest tile of each level is
kept; `yield` runs after each fetch (`Pyramid.columnsFromM_id`). -/
@[specialize]
def columnsFromM {m : Type u → Type u} [Monad m] (n : Nat) (hn : 0 < n) (b numLevels : Nat)
    (fetch : Nat → Nat → m (Array M)) (yield : m PUnit) (k lo hi cols : Nat) : m (Array M) :=
  let cached (k t : Nat) : StateT (Array (Option (Nat × Array M))) m (Array M) := do
    let hit := match (← get)[k]? with
      | some (some (t', a)) => if t' = t then some a else none
      | _ => none
    match hit with
    | some a => pure a
    | none => do
      let a ← fetch k t
      modify (·.setIfInBounds k (some (t, a)))
      pure a
  (Array.ofFnM (n := cols) (fun c => queryFromTiledM n hn b numLevels cached (liftM yield) k
    (columnBound lo hi cols c) (columnBound lo hi cols (c + 1)))).run' (Array.replicate numLevels none)

/-- `Pyramid.columns` with the tiles fetched in a monad (`Pyramid.columnsM_id`). -/
@[specialize]
def columnsM {m : Type u → Type u} [Monad m] (n : Nat) (hn : 0 < n) (b numLevels : Nat)
    (fetch : Nat → Nat → m (Array M)) (yield : m PUnit) (lo hi cols : Nat) : m (Array M) :=
  columnsFromM n hn b numLevels fetch yield 0 lo hi cols

end Pyramid

end Inkproof.Core
