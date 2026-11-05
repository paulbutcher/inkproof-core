# Inkproof.Core

Sorted series with explicit missing data and gaps, mergeable aggregates, and aggregation pyramids whose queries are proved exact. Part of the Inkproof charting libraries; it knows about ordered domains and monoids, never about what the data measures.

## Supported versions

| Inkproof.Core | Lean | Lasm (`@lasm/cli`) |
| --- | --- | --- |
| `main` | `leanprover/lean4:v4.35.0` | 0.3.5 |

The library has no dependencies and builds natively and under Lasm from the same source.

## Using it

```lean
require «inkproof-core» from git "https://github.com/tentenths/inkproof-core" @ "v0.1.0"
```

`import Inkproof.Core` brings in everything a program runs. `import Inkproof.Core.Proofs` adds the published theorems, which a browser build need not link. Each definition's docstring names the theorems about it.

## Guarantees

The theorems hold for any linearly ordered x-type and any lawful aggregate, commutative or not. The only axiom beyond Lean's own is the float-order axiom in `Inkproof.Core.Axioms`, and a check in the tests fails if any other creeps in. [DESIGN.md](DESIGN.md) describes the design, and `API.lock` lists every public declaration and theorem statement.
