/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-core» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

@[default_target]
lean_lib InkproofCore where
  roots := #[`Inkproof.Core]
  globs := #[.andSubmodules `Inkproof.Core]

-- Development tooling, shipped so every Inkproof library can run it from its
-- dependency on this package rather than keeping a copy.
lean_lib InkproofTools where
  globs := #[.andSubmodules `InkproofTools]

@[default_target]
lean_exe «api-lock» where
  root := `InkproofTools.ApiLockMain
  supportInterpreter := true

@[test_driver]
script tests do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait
