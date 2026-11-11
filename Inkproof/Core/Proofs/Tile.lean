/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Tile
import Inkproof.Core.Proofs.Pyramid

/-! CORE-7: a query that reads levels tile by tile equals the untiled query (`queryTiled_eq`), so
PROOF-1 holds for a pyramid fetched in pieces. -/

namespace Inkproof.Core

universe u

open Aggregate (empty merge foldRange foldTiles)

namespace Aggregate

variable {M : Type u} [Aggregate M] [LawfulAggregate M]

omit [LawfulAggregate M] in
/-- A window of an array merges as the matching nodes of the whole. -/
theorem foldRange_extract {a : Array M} {s e lo hi : Nat} (h₁ : s ≤ lo) (h₂ : hi ≤ e) (h₃ : lo ≤ hi) :
    foldRange (a.extract s e) (lo - s) (hi - s) = foldRange a lo hi := by
  rw [foldRange_eq_extract, foldRange_eq_extract, Array.extract_extract]
  have e₁ : s + (lo - s) = lo := by omega
  have e₂ : min (s + (hi - s)) e = hi := by omega
  rw [e₁, e₂]

/-- Reading a level tile by tile merges the same nodes as reading it whole. -/
theorem foldTiles_eq (n : Nat) (hn : 0 < n) (a : Array M) (tile : Nat → Array M)
    (htile : ∀ t, tile t = a.extract (t * n) ((t + 1) * n)) (lo hi : Nat) :
    foldTiles n hn tile lo hi = foldRange a lo hi := by
  induction lo using foldTiles.induct n hn hi with
  | case1 lo hlt stop ih =>
    rw [foldTiles]
    simp only [hlt, ite_true]
    have hs := Nat.lt_mul_div_succ lo hn
    rw [Nat.mul_comm] at hs
    have hd := Nat.div_mul_le_self lo n
    rw [ih, htile, foldRange_extract hd (Nat.min_le_right _ _) (by omega),
      foldRange_split a (Nat.le_of_lt (by omega : lo < min hi ((lo / n + 1) * n)))
        (Nat.min_le_left _ _)]
  | case2 lo hlt =>
    rw [foldTiles]
    simp only [hlt, ite_false]
    rw [foldRange_of_le a (by omega)]

end Aggregate

namespace Pyramid

variable {M : Type u} [Aggregate M]

theorem size_tile (p : Pyramid M) (n k t : Nat) :
    (p.tile n k t).size = min ((t + 1) * n) (p.levels.getD k #[]).size - t * n := by
  simp [tile]

/-- Node `j` of tile `t` is node `t * n + j` of the level. -/
theorem getElem_tile (p : Pyramid M) (n k t : Nat) {j : Nat} (hj : j < (p.tile n k t).size)
    (h : t * n + j < (p.levels.getD k #[]).size) :
    (p.tile n k t)[j] = (p.levels.getD k #[])[t * n + j] := by
  simp [tile]

/-- A tile exists exactly when its first node does. -/
theorem lt_numTiles_iff (p : Pyramid M) {n : Nat} (hn : 0 < n) (k t : Nat) :
    t < p.numTiles n k ↔ t * n < (p.levels.getD k #[]).size := by
  unfold numTiles
  rw [← Nat.not_le, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hn, Nat.not_lt, Nat.succ_mul]
  omega

theorem tile_eq_empty (p : Pyramid M) (n k t : Nat) (h : (p.levels.getD k #[]).size ≤ t * n) :
    p.tile n k t = #[] := by
  simp only [tile]
  apply Array.eq_empty_of_size_eq_zero
  simp only [Array.size_extract]
  omega

variable [LawfulAggregate M]

theorem queryFromTiled_eq (p : Pyramid M) (n : Nat) (hn : 0 < n) (k lo hi : Nat)
    (hk : k < p.levels.size) :
    queryFromTiled n hn p.branching p.levels.size (p.tile n) k lo hi =
      queryFrom p.levels p.branching k lo hi := by
  have hf : ∀ k (hk : k < p.levels.size) lo hi,
      foldTiles n hn (p.tile n k) lo hi = foldRange p.levels[k] lo hi := fun k hk lo hi =>
    Aggregate.foldTiles_eq n hn p.levels[k] (p.tile n k) (fun t => by simp [tile, hk]) lo hi
  induction k, lo, hi using queryFrom.induct p.levels p.branching with
  | case1 k lo hi hk' hk1 lo' hi' hlt ih =>
    rw [queryFromTiled, queryFrom]
    simp only [hk', hk1, dite_true, ite_true, lo', hi', hlt, hf k hk']
    rw [ih hk1]
  | case2 k lo hi hk' hk1 lo' hi' hlt =>
    rw [queryFromTiled, queryFrom]
    simp only [hk', hk1, dite_true, ite_true, lo', hi', hlt, ite_false, hf k hk']
  | case3 k lo hi hk' hk1 =>
    rw [queryFromTiled, queryFrom]
    simp [hk', hk1, hf k hk']
  | case4 k lo hi hk' => exact absurd hk hk'

/-- CORE-7 with PROOF-1: reading the pyramid tile by tile, with any tile size, merges exactly the
leaves in the range, as `Pyramid.query` does. -/
theorem queryTiled_eq (p : Pyramid M) (n : Nat) (hn : 0 < n) (hl : 0 < p.levels.size)
    (lo hi : Nat) : queryTiled n hn p.branching p.levels.size (p.tile n) lo hi = p.query lo hi := by
  rw [queryTiled, queryFromTiled_eq p n hn 0 lo hi hl, query]
  simp [Nat.pos_iff_ne_zero.mp hl]

/-- A pyramid from `Pyramid.build` has levels to read tile by tile. -/
theorem queryTiled_build (b : Nat) (h : 2 ≤ b) (a : Array M) (n : Nat) (hn : 0 < n) (lo hi : Nat) :
    queryTiled n hn b (build b h a).levels.size ((build b h a).tile n) lo hi =
      foldRange a lo hi := by
  have := queryTiled_eq (build b h a) n hn (levels_build_size_pos b h a) lo hi
  rw [query_eq] at this
  exact this

end Pyramid

end Inkproof.Core
