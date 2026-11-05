/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofTools.ApiLock

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake exe api-lock <root module>...\n\
      Prints the public API of each root module and its submodules, which must already be built."
    return 2
  InkproofTools.ApiLock.run (args.map String.toName).toArray
  return 0
