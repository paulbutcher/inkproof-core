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

def apiLockMatches (dir : System.FilePath) : IO Bool := do
  IO.println "== api-lock on a fixture"
  let out ← IO.Process.output
    { cmd := "lake", args := #["exe", "api-lock", "InkproofCoreTest.ApiLockFixture"], cwd := dir }
  if out.exitCode != 0 then
    IO.eprintln s!"FAILED: api-lock (exit {out.exitCode})\n{out.stderr}"
    return false
  let expected ← IO.FS.readFile (dir / "ApiLockFixture.expected")
  if out.stdout != expected then
    IO.eprintln s!"FAILED: api-lock output differs from ApiLockFixture.expected:\n{out.stdout}"
    return false
  return true

@[test_driver]
script test do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["exe", "inkproof-test-driver"], cwd := __dir__ }
  let code ← child.wait
  let apiLock ← apiLockMatches __dir__
  return if code == 0 && apiLock then 0 else 1
