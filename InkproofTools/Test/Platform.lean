/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofTools.Test.Harness

namespace InkproofTools.Test

/-- Guards against the Lasm step silently running a native build. -/
def platformTest (expectWasm : Bool) : TestCase :=
  .mk "runs on the expected platform" do
    check (System.Platform.isEmscripten == expectWasm)
      s!"isEmscripten = {System.Platform.isEmscripten}, target {System.Platform.target}"

end InkproofTools.Test
