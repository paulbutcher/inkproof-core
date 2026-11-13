/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core
import InkproofTools.Test.Harness
import InkproofTools.Test.Platform
import InkproofCoreTest.FloatTests
import InkproofCoreTest.CoreTests
import InkproofCoreTest.PlausibleTests

open InkproofTools.Test InkproofCoreTest

def main (args : List String) : IO UInt32 := do
  let code ← runTests (platformTest (args.contains "--expect-wasm") :: FloatTests.tests ++ CoreTests.tests)
  let plausible ← PlausibleTests.run
  return if code == 0 && plausible == 0 then 0 else 1
