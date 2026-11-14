# Inkproof.Core

Sorted series with explicit missing data and gaps, mergeable aggregates, and aggregation pyramids whose queries are proved exact. Part of the Inkproof charting libraries; it knows about ordered domains and monoids, never about what the data measures.

## Supported versions

| Inkproof.Core | Lean | Lasm (`@lasm/cli`) |
| --- | --- | --- |
| `main` | `leanprover/lean4:v4.35.0` | 0.3.5 |
| `v0.1.0` | `leanprover/lean4:v4.35.0` | 0.3.5 |

The library has no dependencies and builds natively and under Lasm from the same source.

## Using it

```lean
require «inkproof-core» from git "https://github.com/paulbutcher/inkproof-core" @ "v0.1.0"
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
