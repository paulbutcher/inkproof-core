/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-core-test» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

require «inkproof-core» from ".."
require «inkproof-tools» from git "https://github.com/paulbutcher/inkproof-tools" @ "v0.2.1"
require plausible from git "https://github.com/leanprover-community/plausible" @ "v4.35.0"

-- Compile-time tests: compiling is passing.
@[default_target]
lean_lib InkproofCoreTest where
  globs := #[.submodules `InkproofCoreTest]

-- Runtime tests. `Main.lean` must stay buildable by Lasm, so it imports nothing that needs Lean's
-- compiler at run time.
@[default_target]
lean_exe tests where
  root := `Main

@[test_driver]
script test do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["exe", "inkproof-test-driver"], cwd := __dir__ }
  child.wait
