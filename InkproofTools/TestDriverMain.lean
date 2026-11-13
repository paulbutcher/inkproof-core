/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofTools.Test.Driver

/-- `lake exe inkproof-test-driver` in a test subproject: build, run natively, run under Lasm. -/
def main : IO UInt32 := do
  return if ← InkproofTools.Test.runAll (← IO.currentDir) then 0 else 1
