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

open Aggregate (empty merge foldRange foldTiles foldTilesM)

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

omit [LawfulAggregate M] in
/-- Fetching tile by tile in `Id` gives what `foldTiles` computes from the same tiles. -/
theorem foldTilesM_id (n : Nat) (hn : 0 < n) (tile : Nat → Array M) (lo hi : Nat) :
    foldTilesM (m := Id) n hn tile (pure PUnit.unit) lo hi = foldTiles n hn tile lo hi := by
  rw [foldTilesM, foldTiles]
  by_cases h : lo < hi
  · have ih := foldTilesM_id n hn tile (min hi ((lo / n + 1) * n)) hi
    simp only [h, ite_true, bind_pure_comp] at ih ⊢
    simp [ih]
    rfl
  · simp [h]
    rfl
termination_by hi - lo
decreasing_by
  have := Nat.lt_mul_div_succ lo hn
  rw [Nat.mul_comm] at this
  omega

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

omit [LawfulAggregate M] in
/-- Fetching tile by tile in `Id` gives what `queryFromTiled` computes from the same tiles. -/
theorem queryFromTiledM_id (n : Nat) (hn : 0 < n) (b numLevels : Nat) (tile : Nat → Nat → Array M)
    (k lo hi : Nat) :
    queryFromTiledM (m := Id) n hn b numLevels tile (pure PUnit.unit) k lo hi =
      queryFromTiled n hn b numLevels tile k lo hi := by
  rw [queryFromTiledM, queryFromTiled]
  by_cases hk : k < numLevels
  · by_cases hk1 : k + 1 < numLevels
    · by_cases hlt : (lo + b - 1) / b < hi / b
      · have ih := queryFromTiledM_id n hn b numLevels tile (k + 1) ((lo + b - 1) / b) (hi / b)
        simp only [hk, hk1, hlt, ite_true, Aggregate.foldTilesM_id]
        rw [← ih]
        rfl
      · simp only [hk, hk1, hlt, ite_true, ite_false, Aggregate.foldTilesM_id]
    · simp only [hk, hk1, ite_true, ite_false, Aggregate.foldTilesM_id]
  · simp only [hk, ite_false]
    rfl
termination_by numLevels - k

omit [LawfulAggregate M] in
theorem queryTiledM_id (n : Nat) (hn : 0 < n) (b numLevels : Nat) (tile : Nat → Nat → Array M)
    (lo hi : Nat) :
    queryTiledM (m := Id) n hn b numLevels tile (pure PUnit.unit) lo hi =
      queryTiled n hn b numLevels tile lo hi :=
  queryFromTiledM_id n hn b numLevels tile 0 lo hi

omit [LawfulAggregate M] in
theorem size_columnsFrom (n : Nat) (hn : 0 < n) (b numLevels : Nat) (tile : Nat → Nat → Array M)
    (k lo hi cols : Nat) : (columnsFrom n hn b numLevels tile k lo hi cols).size = cols := by
  simp [columnsFrom]

omit [LawfulAggregate M] in
theorem size_columns (n : Nat) (hn : 0 < n) (b numLevels : Nat) (tile : Nat → Nat → Array M)
    (lo hi cols : Nat) : (columns n hn b numLevels tile lo hi cols).size = cols :=
  size_columnsFrom n hn b numLevels tile 0 lo hi cols

omit [LawfulAggregate M] in
theorem getElem_columnsFrom (n : Nat) (hn : 0 < n) (b numLevels : Nat) (tile : Nat → Nat → Array M)
    (k lo hi cols c : Nat) (h : c < (columnsFrom n hn b numLevels tile k lo hi cols).size) :
    (columnsFrom n hn b numLevels tile k lo hi cols)[c] =
      queryFromTiled n hn b numLevels tile k (columnBound lo hi cols c)
        (columnBound lo hi cols (c + 1)) := by
  simp [columnsFrom]

/-- Column `c` of the tiled columns merges the same leaves as `Pyramid.query` over its range. -/
theorem getElem_columns (p : Pyramid M) (n : Nat) (hn : 0 < n) (hl : 0 < p.levels.size)
    (lo hi cols c : Nat)
    (h : c < (columns n hn p.branching p.levels.size (p.tile n) lo hi cols).size) :
    (columns n hn p.branching p.levels.size (p.tile n) lo hi cols)[c] =
      p.query (columnBound lo hi cols c) (columnBound lo hi cols (c + 1)) := by
  refine (getElem_columnsFrom n hn _ _ _ 0 lo hi cols c h).trans ?_
  rw [queryFromTiled_eq p n hn 0 _ _ hl, query]
  simp [Nat.pos_iff_ne_zero.mp hl]

/-- With a higher start level, column `c` merges the leaves under its nodes of level `k`. -/
theorem getElem_columnsFrom_leaves (p : Pyramid M) (n : Nat) (hn : 0 < n) (k lo hi cols c : Nat)
    (hk : k < p.levels.size)
    (h : c < (columnsFrom n hn p.branching p.levels.size (p.tile n) k lo hi cols).size) :
    (columnsFrom n hn p.branching p.levels.size (p.tile n) k lo hi cols)[c] =
      foldRange p.leaves (columnBound lo hi cols c * p.branching ^ k)
        (columnBound lo hi cols (c + 1) * p.branching ^ k) := by
  have hb : 0 < p.branching := by have := p.two_le_branching; omega
  rw [getElem_columnsFrom, queryFromTiled_eq p n hn k _ _ hk, queryFrom_eq p k _ _ hk,
    foldRange_levelAt hb]

omit [Aggregate M] [LawfulAggregate M] in
theorem columnBound_mono (lo hi cols : Nat) {c d : Nat} (h : c ≤ d) :
    columnBound lo hi cols c ≤ columnBound lo hi cols d := by
  unfold columnBound
  have := Nat.div_le_div_right (c := cols) (Nat.mul_le_mul_left (hi - lo) h)
  omega

omit [Aggregate M] [LawfulAggregate M] in
theorem columnBound_zero (lo hi cols : Nat) : columnBound lo hi cols 0 = lo := by
  simp [columnBound]

omit [Aggregate M] [LawfulAggregate M] in
theorem columnBound_cols (lo hi cols : Nat) (hc : 0 < cols) (h : lo ≤ hi) :
    columnBound lo hi cols cols = hi := by
  simp [columnBound, Nat.mul_div_cancel _ hc]
  omega

omit [Aggregate M] [LawfulAggregate M] in
/-- The columns of `columnsFrom` (and so of `columns`, at width one) partition the nodes: with a node
width `w`, every position from `lo * w` up to `hi * w` lies in exactly one column. -/
theorem exists_unique_columnBound (lo hi cols w i : Nat) (hcols : 0 < cols) (hw : 0 < w)
    (hlo : lo * w ≤ i) (hhi : i < hi * w) :
    ∃ c, (c < cols ∧ columnBound lo hi cols c * w ≤ i ∧ i < columnBound lo hi cols (c + 1) * w) ∧
      ∀ d, (d < cols ∧ columnBound lo hi cols d * w ≤ i ∧
        i < columnBound lo hi cols (d + 1) * w) → d = c := by
  have hj : i / w < hi := (Nat.div_lt_iff_lt_mul hw).2 hhi
  have hj' : lo ≤ i / w := (Nat.le_div_iff_mul_le hw).2 hlo
  have hlh : lo ≤ hi := by omega
  have key : ∀ c, columnBound lo hi cols c * w ≤ i ↔ columnBound lo hi cols c ≤ i / w :=
    fun c => (Nat.le_div_iff_mul_le hw).symm
  have key' : ∀ c, i < columnBound lo hi cols c * w ↔ i / w < columnBound lo hi cols c :=
    fun c => (Nat.div_lt_iff_lt_mul hw).symm
  have hex : ∀ e, i / w < columnBound lo hi cols e →
      ∃ c, c < e ∧ columnBound lo hi cols c ≤ i / w ∧ i / w < columnBound lo hi cols (c + 1) := by
    intro e
    induction e with
    | zero => intro h; rw [columnBound_zero] at h; omega
    | succ e ih =>
      intro h
      by_cases hl : i / w < columnBound lo hi cols e
      · obtain ⟨c, hc, h1, h2⟩ := ih hl
        exact ⟨c, by omega, h1, h2⟩
      · exact ⟨e, by omega, by omega, h⟩
  obtain ⟨c, hc, h1, h2⟩ := hex cols (by rw [columnBound_cols _ _ _ hcols hlh]; exact hj)
  refine ⟨c, ⟨hc, (key c).2 h1, (key' _).2 h2⟩, ?_⟩
  rintro d ⟨hd, hd1, hd2⟩
  rw [key] at hd1
  rw [key'] at hd2
  rcases Nat.lt_trichotomy d c with hlt | heq | hlt
  · have := columnBound_mono lo hi cols (by omega : d + 1 ≤ c)
    omega
  · exact heq
  · have := columnBound_mono lo hi cols (by omega : c + 1 ≤ d)
    omega

/-- `x` run from any state satisfying `inv` returns `v` and leaves a state satisfying `inv`. -/
private def Good {σ α : Type u} (inv : σ → Prop) (x : StateT σ Id α) (v : α) : Prop :=
  ∀ s, inv s → (x.run s).1 = v ∧ inv (x.run s).2

private theorem Good.pure {σ α : Type u} {inv : σ → Prop} (v : α) :
    Good inv (pure v : StateT σ Id α) v := fun _ hs => ⟨rfl, hs⟩

private theorem Good.bind {σ α β : Type u} {inv : σ → Prop} {x : StateT σ Id α} {a : α}
    {f : α → StateT σ Id β} {w : β} (hx : Good inv x a) (hf : Good inv (f a) w) :
    Good inv (x >>= f) w := fun s hs => by
  obtain ⟨h1, h2⟩ := hx s hs
  show (f (x s).1 (x s).2).1 = w ∧ inv (f (x s).1 (x s).2).2
  change (x s).1 = a at h1
  change inv (x s).2 at h2
  rw [h1]
  exact hf _ h2

omit [LawfulAggregate M] in
private theorem foldTilesM_good {σ : Type u} {inv : σ → Prop} (n : Nat) (hn : 0 < n)
    (tile : Nat → Array M) (fetch : Nat → StateT σ Id (Array M))
    (hf : ∀ t, Good inv (fetch t) (tile t)) {yield : StateT σ Id PUnit}
    (hy : Good inv yield PUnit.unit) (lo hi : Nat) :
    Good inv (foldTilesM n hn fetch yield lo hi) (foldTiles n hn tile lo hi) := by
  rw [foldTilesM, foldTiles]
  by_cases h : lo < hi
  · simp only [h, ite_true]
    refine (hf _).bind ?_
    refine hy.bind ?_
    exact (foldTilesM_good n hn tile fetch hf hy _ hi).bind (Good.pure _)
  · simp only [h, ite_false]
    exact Good.pure _
termination_by hi - lo
decreasing_by
  have := Nat.lt_mul_div_succ lo hn
  rw [Nat.mul_comm] at this
  omega

omit [LawfulAggregate M] in
private theorem queryFromTiledM_good {σ : Type u} {inv : σ → Prop} (n : Nat) (hn : 0 < n)
    (b numLevels : Nat) (tile : Nat → Nat → Array M) (fetch : Nat → Nat → StateT σ Id (Array M))
    (hf : ∀ k t, Good inv (fetch k t) (tile k t)) {yield : StateT σ Id PUnit}
    (hy : Good inv yield PUnit.unit) (k lo hi : Nat) :
    Good inv (queryFromTiledM n hn b numLevels fetch yield k lo hi)
      (queryFromTiled n hn b numLevels tile k lo hi) := by
  rw [queryFromTiledM, queryFromTiled]
  by_cases hk : k < numLevels
  · by_cases hk1 : k + 1 < numLevels
    · by_cases hlt : (lo + b - 1) / b < hi / b
      · simp only [hk, hk1, hlt, ite_true]
        refine (foldTilesM_good n hn (tile k) (fetch k) (hf k) hy _ _).bind ?_
        refine (queryFromTiledM_good n hn b numLevels tile fetch hf hy (k + 1) _ _).bind ?_
        exact (foldTilesM_good n hn (tile k) (fetch k) (hf k) hy _ _).bind (Good.pure _)
      · simp only [hk, hk1, hlt, ite_true, ite_false]
        exact foldTilesM_good n hn (tile k) (fetch k) (hf k) hy _ _
    · simp only [hk, hk1, ite_true, ite_false]
      exact foldTilesM_good n hn (tile k) (fetch k) (hf k) hy _ _
  · simp only [hk, ite_false]
    exact Good.pure _
termination_by numLevels - k

private theorem ofFnM_good {σ α : Type u} {inv : σ → Prop} (f : Nat → StateT σ Id α) (g : Nat → α)
    (hf : ∀ c, Good inv (f c) (g c)) (i : Nat) :
    Good inv (Array.ofFnM (n := i) fun c => f c) (Array.ofFn (n := i) fun c => g c) := by
  induction i with
  | zero => simpa using Good.pure _
  | succ i ih =>
    rw [Array.ofFnM_succ, Array.ofFn_succ]
    exact ih.bind ((hf i).bind (Good.pure _))

/-- Every tile in the cache is the tile the fetcher would return. -/
private def CacheOk (tile : Nat → Nat → Array M) (s : Array (Option (Nat × Array M))) : Prop :=
  ∀ k t a, s[k]? = some (some (t, a)) → a = tile k t

omit [LawfulAggregate M] in
private theorem columnsFromM_id_aux (n : Nat) (hn : 0 < n) (b numLevels : Nat)
    (tile : Nat → Nat → Array M) (k lo hi cols : Nat)
    (cached : Nat → Nat → StateT (Array (Option (Nat × Array M))) Id (Array M))
    (hc : ∀ k t, Good (CacheOk tile) (cached k t) (tile k t)) :
    (Array.ofFnM (n := cols) (fun c => queryFromTiledM n hn b numLevels cached
      (liftM (pure PUnit.unit : Id PUnit)) k (columnBound lo hi cols c)
      (columnBound lo hi cols (c + 1)))).run' (Array.replicate numLevels none) =
      columnsFrom n hn b numLevels tile k lo hi cols := by
  have hy : Good (CacheOk tile) (liftM (pure PUnit.unit : Id PUnit) : StateT _ Id PUnit)
      PUnit.unit := fun _ hs => ⟨rfl, hs⟩
  exact (ofFnM_good (inv := CacheOk tile) _ (fun c => queryFromTiled n hn b numLevels tile k
    (columnBound lo hi cols c) (columnBound lo hi cols (c + 1)))
    (fun c => queryFromTiledM_good n hn b numLevels tile cached hc hy k _ _) cols
    (Array.replicate numLevels none) (by
      intro k t a h
      simp [Array.getElem?_replicate] at h)).1

omit [LawfulAggregate M] in
/-- The cache returns the tile the fetcher would, so the monadic columns run in `Id` equal the pure
ones. -/
theorem columnsFromM_id (n : Nat) (hn : 0 < n) (b numLevels : Nat) (tile : Nat → Nat → Array M)
    (k lo hi cols : Nat) :
    columnsFromM (m := Id) n hn b numLevels (fun k t => pure (tile k t)) (pure PUnit.unit) k lo hi
        cols = columnsFrom n hn b numLevels tile k lo hi cols := by
  unfold columnsFromM
  dsimp only
  refine columnsFromM_id_aux n hn b numLevels tile k lo hi cols _ ?_
  intro k t s hs
  have miss : CacheOk tile (s.setIfInBounds k (some (t, tile k t))) := by
    intro k2 t2 a2 h
    rw [Array.getElem?_setIfInBounds] at h
    split at h
    · rename_i hk
      split at h
      · injection h with h
        injection h with h
        injection h with h1 h2
        rw [← h2, ← h1, hk]
      · cases h
    · exact hs k2 t2 a2 h
  rcases h : s[k]? with _ | _ | ⟨t', a⟩
  all_goals simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, MonadState.get,
    StateT.get, pure, StateT.pure, h]
  · exact ⟨rfl, miss⟩
  · exact ⟨rfl, miss⟩
  · by_cases ht : t' = t
    · subst ht
      simp only [ite_true]
      exact ⟨hs k t' a h, hs⟩
    · simp only [ht, ite_false]
      exact ⟨rfl, miss⟩

omit [LawfulAggregate M] in
theorem columnsM_id (n : Nat) (hn : 0 < n) (b numLevels : Nat) (tile : Nat → Nat → Array M)
    (lo hi cols : Nat) :
    columnsM (m := Id) n hn b numLevels (fun k t => pure (tile k t)) (pure PUnit.unit) lo hi cols =
      columns n hn b numLevels tile lo hi cols :=
  columnsFromM_id n hn b numLevels tile 0 lo hi cols

end Pyramid

end Inkproof.Core
