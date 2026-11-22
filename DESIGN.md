# Inkproof.Core design

Inkproof.Core holds sorted series with explicit missing data and gaps, mergeable aggregates, and aggregation pyramids whose queries are proved exact. It knows about ordered domains and monoids, never about what the data measures. Requirement IDs refer to `REQUIREMENTS.md` in `inkproof-coordination`.

## Packages and modules

- The package `inkproof-core` depends on `inkproof-float`, at a release tag, and otherwise on nothing but Lean, at the toolchain Lasm supports (`lean-toolchain`); it builds natively and under Lasm from the same source.
- Runtime modules live under `Inkproof.Core`, and `import Inkproof.Core` brings in all of them; this is what a browser build links. They may hold the proofs their own definitions need, which compile to nothing.
- Published theorems live under `Inkproof.Core.Proofs`, which runtime modules never import, so a proof-only dependency never reaches a browser build (PROC-5, PLAT-3).
- Core declares no axiom of its own (PROC-1); the tests fail if a published theorem depends on any beyond Lean's `propext`, `Classical.choice` and `Quot.sound`.
- Development tooling (`api-lock`, the test harness and driver, the axiom check) comes from `inkproof-tools`, required only by the `test` subproject, so `import Inkproof.Core` never reaches it or Plausible.

## Generic foundations

- Algorithms and theorems are stated over any type with a linear order and any monoid (FP-1), and concrete types enter only as instances.
- The library does not use Mathlib, which would add its build to every consumer's. Orders use Lean core's `LE`, `LT` and `Std.IsLinearOrder`, and a monoid is an associative operation with an identity, stated with core's `Std.Associative` and `Std.LawfulIdentity`. A proof that seems to need Mathlib goes to the human for a decision rather than adding it.
- A hypothesis appears only where a proof needs it. Commutativity, decidable equality and arithmetic on the x-domain are never assumed by default; VAL-1 instances in the test subproject check this.

## Series, missing data and gaps

- A series stores x-values and values as two parallel arrays, with a proof that the x-values are non-decreasing (CORE-1). Repeated x-values are allowed, since data often has them.
- Values have type `Option β`: a missing value is `none`, never NaN or a sentinel (CORE-2). Aggregation sees the `none` and decides what it contributes.
- A validated constructor checks sortedness and reports the first offending index. A second constructor establishes it with a stable sort, so equal x-values keep their input order (CORE-1).
- A segmented series is one series plus strictly increasing break indices, each the first point of a new segment, so no segment is empty (CORE-3). It is built from explicit breaks, or by splitting at every adjacent pair a caller-supplied predicate marks as a gap. The library never infers a gap.
- Algorithms read points through index access, never a particular container, so the indexable-series interface (CORE-8) can supply float arrays or byte buffers without copying.

## Aggregates

- `Aggregate` gives an aggregate type `empty` and an order-preserving `merge`. `LawfulAggregate` adds the monoid laws, stated with core's `Std.Associative` and `Std.LawfulIdentity`, and every exactness theorem assumes it (CORE-5).
- Data enters through a measure from a point to the aggregate. The provided aggregates wrap `Option`, so a missing value measures as `empty` with no special case.
- Provided: `Minimum` and `Maximum` (ties keep the earliest), `First` and `Last` (not commutative), `Count`, `Total`, `Occupancy` (a set of pixel indices as a bitmask; merging is union), and pairs of any of these, such as first/max/min/last.
- `Minimum` and `Maximum` merge with `Option.merge (minOn id)` and `Option.merge (maxOn id)`, so core supplies their laws. `First` and `Last` keep `<|>`, which is `Option.merge` with a projection that core has no instances for.
- `Inkproof.Core.Proofs.Aggregate` proves what each aggregate computes (the minimum, the first present value, the union and so on), and that a fold of pairs is the pair of folds. The laws alone would not show that an aggregate called `Maximum` is the maximum.
- `Total` is lawful only where addition is associative with `0` as identity, such as `Nat` and `Int`. Float sums get `Aggregate` but not `LawfulAggregate`, so they carry no exactness theorem; error bounds belong with FP-3.

## Pyramids

- A pyramid over one segment stores level 0 as the measure of each point, and each level above as the product of consecutive groups of `b ≥ 2` nodes from the level below, in order. Point `i` belongs to node `i / b^k` at level `k`.
- A query takes whole groups from the level above wherever it can; a built pyramid's levels shrink to one node. Index ranges are primary; `Series.lowerBound` turns an x-range into an index range by binary search, which is correct because the series is sorted. `lowerBoundFrom` and `lowerBoundFromBy` are written by hand because Lean core's `Array.binSearch` returns an equivalent element rather than the first index at or above `x`, which is what the range needs, and has no lemmas, so using it would mean proving a lower-bound specification over it anyway.
- PROOF-1: for every monoid and every index or x-range, the query equals the monoid fold over the raw points in that range, in order. Order matters because the monoid need not be commutative.
- PROOF-2: each point lies in exactly one node per level, and each node equals the product of its children.
- PROOF-3: `SegmentedPyramid` holds one pyramid per segment. Its query returns one result per segment, `empty` where no point is in range, each equal to the fold over that segment's in-range points alone, so no value combines points from two segments. `queryOverlapping` returns the same results for just the segments with points in range, tagged with their indices; it finds the first and last by binary search over the breaks, so its cost follows the segments in range rather than all of them. Levels are flat arrays so CORE-7 tiles can be fixed ranges of nodes per level.

## Binning, indexed data and tiles

- `Binning` holds a column count and a monotone map from the x-domain to columns below it (CORE-4). `ofInt`, `ofNat` and `ofFixed` split a range into equal columns in exact integer arithmetic (FP-4), `Fixed` being an integer with a decimal scale. `ofBreaks` counts the breaks at or below a point, so it needs only an order and bins `OrdFloat` x-values with breaks the caller computed; a float formula's monotonicity would rest on the rounding axiom, so it is left to the caller.
- `IndexedSeries` is size plus index access, with instances for `Array`, `ByteArray` and `FloatArray` (CORE-8). `Pyramid.ofIndexed` and `Series.lowerBoundIndexed` read through it and are proved equal to the array versions on `IndexedSeries.toArray`, so PROOF-1 and the lower-bound specification carry over unchanged.
- A tile is a fixed run of `n` nodes of one level (CORE-7). `Pyramid.queryTiled` takes the branching, the number of levels and a tile fetcher, and is proved equal to `Pyramid.query` for any tile size; it touches only the tiles holding the partial groups at each level. Wire encoding is out of scope.

## Calendar

- `Calendar` is Std.Time.Date's `PlainDate.ofEpochDay`, `toEpochDay`, `Year.Offset.isLeap` and `Month.Ordinal.days` behind `Int × Nat × Nat` signatures, with Core's proofs restated over them; only `Std.Time.Date.PlainDate` is imported, since the `Std.Time` umbrella brings native code.
- Checked under Lasm: a program using only `PlainDate.ofEpochDay` and `toEpochDay` builds for the browser and prints the dates the previous definitions did. Size: 104.3 KiB brotli with Core's own definitions and 105.0 KiB with Std's, the bounded-type machinery being the difference.
- Std's day-of-era formula is proved right by comparing it at the boundaries of each of the 400 years with monotonicity in between, because `omega` cannot close it over all 146097 days.

## Decimal text

- `parseDecimal` reads a `List Char` and accepts only digits, one optional sign and one point. `String.toNat?` also accepts `_` separators, so it would admit text `formatDecimal` never writes.

## Floats

The float model (`OrdFloat`, `Float.toRat`, `Float.Approximates`, the rounding axiom and the discussion of proving it) lives in `inkproof-float`. Core uses its `OrdFloat` as an x-type, for example with `Binning.ofBreaks`.

## Testing

- Tests live in the `test` subproject (CLAUDE.md's Test layout). `lake test` builds it, runs `Main.lean` natively, then compiles and runs the same `Main.lean` with Lasm. A check inside the program confirms that the Lasm run executes as wasm.
- Lasm is pinned exactly in `test/package.json` and installed with `npm ci` in `test/`. Without it the Lasm step is skipped with a warning; with `INKPROOF_REQUIRE_LASM=1` the skip fails instead.
- Theorems that only validate the specification, such as VAL-1 instances (an order-only x-type, a non-commutative monoid) and VAL-2 hypothesis discharges, live in the test library, where compiling is passing.
- Where optimised code is not yet proved equal to its naive reference, a property compares them over VAL-4's edge cases, with the obstacle recorded beside it.

## API lock

- `scripts/api-lock.sh` runs inkproof-tools' `api-lock` and prints one line per public declaration of `Inkproof.Core`: kind, full name and type, sorted. Theorem statements are the theorem's type. CI compares the output with `API.lock`, and CODEOWNERS sends changes to the human.
- Private names, modules with an `Internal` component (which no consumer may import), compiler auxiliaries (matchers, recursors, `noConfusion`, equation lemmas) and other declarations derived from a listed one are left out.
