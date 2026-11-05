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

-- Compile-time tests: compiling is passing.
@[default_target]
lean_lib InkproofCoreTest where
  globs := #[.submodules `InkproofCoreTest]

-- Runtime tests. `Main.lean` must stay buildable by Lasm, so it imports nothing that needs Lean's
-- compiler at run time.
@[default_target]
lean_exe tests where
  root := `Main

def runStep (name cmd : String) (args : Array String) (cwd : System.FilePath)
    (env : Array (String × Option String) := #[]) : IO Bool := do
  IO.println s!"== {name}"
  let child ← IO.Process.spawn { cmd, args, cwd, env }
  let code ← child.wait
  if code != 0 then IO.eprintln s!"FAILED: {name} (exit {code})"
  return code == 0

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

/-- Runs the same `Main.lean` compiled by Lasm. Lasm comes from `package.json`; without it the step
is skipped with a warning, unless `INKPROOF_REQUIRE_LASM=1` makes that an error. `LASM_EDITOR=0`
stops Lasm making its own toolchain the elan override here, which would switch the native steps to it. -/
def lasmStep (dir : System.FilePath) : IO Bool := do
  let lasm := dir / "node_modules" / ".bin" / "lasm"
  if ← lasm.pathExists then
    runStep "tests under Lasm" lasm.toString #["Main.lean", "--", "--expect-wasm"] dir
      #[("LASM_EDITOR", some "0")]
  else if (← IO.getEnv "INKPROOF_REQUIRE_LASM") == some "1" then
    IO.eprintln "FAILED: Lasm is required but not installed; run `npm ci` in test/"
    return false
  else
    IO.eprintln "::warning::Lasm tests skipped: run `npm ci` in test/ to install Lasm"
    return true

@[test_driver]
script test do
  let dir := __dir__
  let mut ok := true
  ok := ok && (← runStep "build" "lake" #["build"] dir)
  if ok then
    ok := (← runStep "tests, native" (dir / ".lake" / "build" / "bin" / "tests").toString #[] dir)
      && ok
    ok := (← apiLockMatches dir) && ok
    ok := (← lasmStep dir) && ok
  return if ok then 0 else 1
