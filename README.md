# Inkproof.Core

Sorted series with explicit missing data and gaps, mergeable aggregates, and aggregation pyramids whose queries are proved exact. Part of the Inkproof charting libraries; it knows about ordered domains and monoids, never about what the data measures.

## What it does

- Keep a series of sorted x values with explicit missing data, and build one from arrays, points or unsorted input: `Series`, `Series.ofArrays?`, `Series.ofPoints?`, `Series.ofUnsorted`.
- Take the points of a series within an x range, or find where an x value falls: `Series.slice`, `Series.inRange`, `Series.lowerBound`.
- Search and aggregate a byte, float or plain array without copying it: `IndexedSeries`, `Series.lowerBoundIndexed`.
- Split a series into segments at gaps or at chosen breaks: `Segmented`, `Segmented.splitWhere`, `Segmented.ofBreaks?`.
- Map x values to a fixed number of bins, with equal widths or chosen breaks: `Binning`, `Binning.ofNat`, `Binning.ofInt`, `Binning.ofFixed`, `Binning.ofBreaks`.
- Merge summaries of ranges with an associative aggregate: `Aggregate`, `LawfulAggregate`, `Aggregate.fold`, `Aggregate.foldRange`.
- Use ready-made aggregates: `Count`, `Total`, `Minimum`, `Maximum`, `First`, `Last`, `Occupancy`, and pairs of any two.
- Build a pyramid of coarser and coarser aggregates and query any range exactly: `Pyramid.build`, `Pyramid.ofIndexed`, `Pyramid.ofMeasure`, `Pyramid.query`.
- Store a pyramid's levels as tiles of n nodes and query a range, fetching only the tiles it touches: `Pyramid.tile`, `Pyramid.numTiles`, `Pyramid.queryTiled`, `Pyramid.queryTiledM`.
- Aggregate each of `cols` equal columns of a tiled range, fetching each tile once: `Pyramid.columnsM`, `Pyramid.columns`.
- Do the same with column boundaries snapped to the nodes of one level, so the columns partition the nodes and no finer tile is read: `Pyramid.columnsFromM`, `Pyramid.columnsFrom`.
- Query a segmented series, including the segments an x range overlaps: `SegmentedPyramid.build`, `SegmentedPyramid.query`, `SegmentedPyramid.queryOverlapping`.
- Store decimal numbers as scaled integers, and parse and print them: `Fixed`, `Decimal.parseDecimal`, `Decimal.formatDecimal`, `Decimal.formatNat`.
- Write a decimal without trailing zeros, or round a rational to a number of decimals: `Decimal.trimZeros`, `Decimal.roundScaled`.
- Find out what went wrong building a series or segmented series: `SeriesError`, returned by `Series.ofArrays?` and `Series.ofPoints?`, and `SegmentError`, returned by `Segmented.ofBreaks?`.

## Supported versions

| Inkproof.Core | Lean | Lasm (`@lasm/cli`) |
| --- | --- | --- |
| `main` | `leanprover/lean4:v4.35.0` | 0.8.0 |
| `v0.10.1` | `leanprover/lean4:v4.35.0` | 0.8.0 |

The library depends only on `inkproof-float`, and builds natively and under Lasm from the same source.

## Using it

```lean
require «inkproof-core» from git "https://github.com/paulbutcher/inkproof-core" @ "v0.10.1"
```

`import Inkproof.Core` brings in everything a program runs. `import Inkproof.Core.Proofs` adds the published theorems, which a browser build need not link. Each definition's docstring names the theorems about it.

## Guarantees

The theorems hold for any linearly ordered x-type and any lawful aggregate, commutative or not. Core adds no axiom; the float model and its rounding axiom are in `inkproof-float`, and a check in the tests fails if Core declares one. [DESIGN.md](DESIGN.md) describes the design, and `API.lock` lists every public declaration and theorem statement.

## Trusted computing base

The proofs cover the Lean source. These are trusted beneath them:

| Component | Why trusted | Mitigation |
| --- | --- | --- |
| Lean compiler and runtime | Compiles the proved source | Pinned in `lean-toolchain`; the same test program runs natively and under Lasm |
| Lasm compiler, runtime and Emscripten | Compiles Lean to Wasm | Pinned exactly in the test subproject; the same test program runs natively and under Lasm |

The library has no generated code and no hand-written JavaScript.
