# Changelog

## [0.16.1]

- The README names no version in its `require` example and has no supported-versions table.

## [0.16.0]

- `Calendar.civilFromDays`, `daysFromCivil`, `isLeap` and `daysInMonth` are defined by Std.Time.Date's `PlainDate`, with every theorem statement unchanged.
- `Calendar.isoDate` writes a day count since 1970-01-01 as `YYYY-MM-DD`.
- `Minimum` and `Maximum` merge with core's `Option.merge`, `minOn` and `maxOn`.
- The private fold lemmas and `Binning.ofBreaks` use core's `List.foldl_eq_apply_foldr` and `List.countP`.
- `Decimal.formatNat` builds on `Nat.toDigits` and `List.leftpad`; `Decimal.digitCount`, `lsDigits`, `lsValue`, `scaledDigits`, `lt_pow_digitCount`, `digitCount_spec`, `digitChar_isDigit`, `digitChar_toNat`, `digitsValue_reverse` and `Calendar.zeroPad` are removed in favour of the Lean core ones, and `digitsValue_toDigits` is added.

## [0.14.0]

- `Series.stack` stacks series that share x-values into running sums, with missing values and negatives handled by stated rules.

## [0.13.0]

- `Calendar.civilFromDays` and `Calendar.daysFromCivil` convert between days since 1970-01-01 and a proleptic Gregorian date, proved mutually inverse and valid.

## [0.12.0]

- `Decimal.trimZeros` drops trailing zeros from a decimal, and `Decimal.roundScaled` rounds a rational to a number of decimals.

## [0.11.0]

- `Pyramid.columnsM` and `Pyramid.columns` aggregate equal columns of a range over a tiled pyramid, fetching each tile once, and `Pyramid.columnsFromM` and `Pyramid.columnsFrom` snap the columns to the nodes of one level.

## [0.10.1]

- Lasm tests run under `@lasm/cli` 0.8.0.

## [0.10.0]

- `Pyramid.queryTiledM` and `Pyramid.queryFromTiledM` query a pyramid whose tiles are fetched in a monad, with `queryTiledM_id` and `queryFromTiledM_id` showing they agree with the pure versions in `Id`.

## [0.9.1]

- Hot generic aggregation, pyramid, query and tiling code is specialised per instance.

## [0.9.0]

- `Aggregate.foldTilesM` folds tiles fetched in a monad, with `foldTilesM_id` showing it agrees with `foldTiles` in `Id`.

## [0.8.1]

- Depends on inkproof-float v0.5.0.

## [0.8.0]

- `Inkproof.Core.Decimal` formats a scaled integer as locale-free decimal characters (`formatDecimal`) and parses them back, with proofs of the digits, sign, point and length.

## [0.7.0]

- The float model (`OrdFloat`, `Float.toRat`, `Float.Approximates`, the rounding axiom and the `rat_abs` lemmas) moved to inkproof-float v0.1.0, which Core now depends on; Core declares no axiom.

## [0.6.1]

- The development tooling, api-lock, test driver and axiom check come from inkproof-tools v0.1.0, and Core no longer ships `InkproofTools`.

## [0.6.0]

- `ratAbs` is replaced by Lean core's `Rat.abs`.
- `rat_abs_add_le`, `rat_abs_mul` and `rat_abs_le_iff` state the absolute value lemmas that consumers reuse.
- `Float.Approximates.rel` and `Float.Approximates.error_step` state the float error lemmas that consumers reuse.

## [0.5.1]

- `Series.lowerBoundFrom` is defined through `Series.lowerBoundFromBy`, leaving one binary search.
- `InkproofTools.Test` provides the test harness, platform test and Lasm driver as a development library, and Core's tests use it with Plausible.

## [0.5.0]

- `float_le_linear` is now a theorem proved from Lean's model of `Float`, no longer an axiom.
- `Float.toRat_eq_value` states what `Float.toRat` computes.
- `OrdFloat.ofFloat?_eq_none_iff` states that `ofFloat?` rejects exactly NaN.

## [0.4.0]

- `Float.toRat`, the exact value of a finite float, and `float_rounding_model`, an axiom that `+`, `-`, `*` and `/` round to within half an ulp (relative error `2 ^ -53`, binary64).

## [0.3.0]

- `Binning`, a monotone map from x-values to pixel columns, with integer, fixed-point and break-based (ordered float) instances.
- `IndexedSeries`, so pyramids and lower-bound searches read float arrays, byte buffers and arrays without copying.
- `Pyramid.tile` and `Pyramid.queryTiled`, which read a pyramid tile by tile with the result of the untiled query.

## [0.2.0]

- `SegmentedPyramid.queryOverlapping` queries only the segments that overlap a range.
- `Segmented.splitWherePoints` splits a series where a gap predicate on adjacent points holds.

## [0.1.0]

- First release: sorted series with missing data and gaps, mergeable aggregates, and aggregation pyramids with proved-exact queries.
