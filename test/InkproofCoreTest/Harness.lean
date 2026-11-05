/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace InkproofCoreTest

structure TestCase where
  name : String
  run : Except String Unit

def check (cond : Bool) (msg : String) : Except String Unit :=
  if cond then .ok () else .error msg

/-- Runs every case, reports each failure, and returns the process exit code. -/
def runTests (cases : List TestCase) : IO UInt32 := do
  let mut failed := 0
  for c in cases do
    if let .error msg := c.run then
      failed := failed + 1
      IO.eprintln s!"FAIL {c.name}: {msg}"
  IO.println s!"{cases.length - failed}/{cases.length} passed"
  return if failed == 0 then 0 else 1

end InkproofCoreTest
