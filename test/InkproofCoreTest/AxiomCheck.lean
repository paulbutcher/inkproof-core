/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofTools.AxiomCheck
import Inkproof.Core
import Inkproof.Core.Proofs

/-! PROC-1: compiling this module fails if any declaration of the library depends on an axiom other
than Lean's own, or if an axiom is declared anywhere in the library. -/

open Lean Elab Command

run_cmd liftCoreM (InkproofTools.AxiomCheck.check `Inkproof.Core)
