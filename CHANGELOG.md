# Changelog

## [Unreleased]

## [0.3.0]

- `Binning`, a monotone map from x-values to pixel columns, with integer, fixed-point and break-based (ordered float) instances.
- `IndexedSeries`, so pyramids and lower-bound searches read float arrays, byte buffers and arrays without copying.
- `Pyramid.tile` and `Pyramid.queryTiled`, which read a pyramid tile by tile with the result of the untiled query.

## [0.2.0]

- `SegmentedPyramid.queryOverlapping` queries only the segments that overlap a range.
- `Segmented.splitWherePoints` splits a series where a gap predicate on adjacent points holds.

## [0.1.0]

- First release: sorted series with missing data and gaps, mergeable aggregates, and aggregation pyramids with proved-exact queries.
