# Inkproof.Core design

Inkproof.Core holds sorted series with explicit missing data and gaps, mergeable aggregates, and aggregation pyramids whose queries are proved exact. It knows about ordered domains and monoids, never about what the data measures. Requirement IDs refer to `REQUIREMENTS.md` in `inkproof-coordination`.

## Packages and modules

- The package `inkproof-core` depends on nothing but Lean, at the toolchain Lasm supports (`lean-toolchain`); it builds natively and under Lasm from the same source.
- Runtime modules live under `Inkproof.Core`, and `import Inkproof.Core` brings in all of them; this is what a browser build links. They may hold the proofs their own definitions need, which compile to nothing.
- Published theorems live under `Inkproof.Core.Proofs`, which runtime modules never import, so a proof-only dependency never reaches a browser build (PROC-5, PLAT-3).
- Every axiom is declared in `Inkproof.Core.Axioms` and nowhere else (PROC-1). The tests fail if a published theorem depends on any other axiom beyond Lean's `propext`, `Classical.choice` and `Quot.sound`.
- `InkproofTools` holds development tooling, currently the `api-lock` executable. It ships in this package so other Inkproof libraries can run it through their dependency on Core, and `import Inkproof.Core` never reaches it.

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
- `Total` is lawful only where addition is associative with `0` as identity, such as `Nat` and `Int`. Float sums get `Aggregate` but not `LawfulAggregate`, so they carry no exactness theorem; error bounds belong with FP-3.

## Pyramids

- A pyramid over one segment stores level 0 as the measure of each point, and each level above as the product of consecutive groups of `b ≥ 2` nodes from the level below, in order. Point `i` belongs to node `i / b^k` at level `k`.
- A range query combines `O(b log n)` nodes. Index ranges are primary; an x-range is turned into an index range by binary search, which is correct because the series is sorted.
- PROOF-1: for every monoid and every index or x-range, the query equals the monoid fold over the raw points in that range, in order. Order matters because the monoid need not be commutative.
- PROOF-2: each point lies in exactly one node per level, and each node equals the product of its children.
- PROOF-3: a segmented series has one pyramid per segment. A segmented query returns one result per segment overlapping the range, each equal to the fold over that segment's points alone, so no value combines points from two segments. Levels are flat arrays so CORE-7 tiles can be fixed ranges of nodes per level.

## Floats

- `OrdFloat` wraps a `Float` with a proof that it is not NaN, and its constructor turns `-0.0` into `0.0`, so equal values have one representation (FP-2).
- The FP-2 axiom states that `Float`'s `≤` is a linear order on non-NaN floats other than `-0.0`. It is the only axiom the library adds, and `OrdFloat`'s order instance rests on it.

## Testing

- Tests live in the `test` subproject (CLAUDE.md's Test layout). `lake test` builds it, runs `Main.lean` natively, checks `api-lock` against a fixture, then compiles and runs the same `Main.lean` with Lasm. A check inside the program confirms that the Lasm run executes as wasm.
- Lasm is pinned exactly in `test/package.json` and installed with `npm ci` in `test/`. Without it the Lasm step is skipped with a warning; with `INKPROOF_REQUIRE_LASM=1` the skip fails instead.
- Theorems that only validate the specification, such as VAL-1 instances (an order-only x-type, a non-commutative monoid) and VAL-2 hypothesis discharges, live in the test library, where compiling is passing.
- Where optimised code is not yet proved equal to its naive reference, a property compares them over VAL-4's edge cases, with the obstacle recorded beside it.

## API lock

- `scripts/api-lock.sh` prints one line per public declaration of `Inkproof.Core`: kind, full name and type, sorted. Theorem statements are the theorem's type. CI compares the output with `API.lock`, and CODEOWNERS sends changes to the human.
- Private names, modules with an `Internal` component (which no consumer may import), compiler auxiliaries (matchers, recursors, `noConfusion`, equation lemmas) and other declarations derived from a listed one are left out.
- Every Inkproof library uses this generator through its dependency on Core, `lake exe api-lock <its root module>` after `lake build`, so its command line and line format are a contract with all of them: changing either changes every library's `API.lock`.
