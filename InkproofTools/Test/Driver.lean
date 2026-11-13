/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace InkproofTools.Test

def runStep (name cmd : String) (args : Array String) (cwd : System.FilePath)
    (env : Array (String × Option String) := #[]) : IO Bool := do
  IO.println s!"== {name}"
  let child ← IO.Process.spawn { cmd, args, cwd, env }
  let code ← child.wait
  if code != 0 then IO.eprintln s!"FAILED: {name} (exit {code})"
  return code == 0

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

/-- Builds the test subproject in `dir`, then runs its `tests` executable natively and under Lasm. -/
def runAll (dir : System.FilePath) : IO Bool := do
  if !(← runStep "build" "lake" #["build"] dir) then return false
  let native ← runStep "tests, native" (dir / ".lake" / "build" / "bin" / "tests").toString #[] dir
  let lasm ← lasmStep dir
  return native && lasm

end InkproofTools.Test
