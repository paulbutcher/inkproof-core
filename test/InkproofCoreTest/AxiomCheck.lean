/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Inkproof.Core
import Inkproof.Core.Proofs

/-! PROC-1: compiling this module fails if any declaration of the library depends on an axiom other
than Lean's own and those in `Inkproof.Core.Axioms`, or if an axiom is declared anywhere else. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).bind (env.allImportedModuleNames[·.toNat]?)
  let inLibrary (n : Name) : Bool := (moduleOf n).any (`Inkproof.Core).isPrefixOf
  let axiomsModule := `Inkproof.Core.Axioms
  let mut listed : NameSet := ({} : NameSet).insert `propext |>.insert `Classical.choice
    |>.insert `Quot.sound
  let mut library : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless inLibrary n do continue
    library := library.push n
    if ci matches .axiomInfo _ then
      unless moduleOf n == some axiomsModule do
        throwError "axiom {n} is declared outside {axiomsModule}"
      listed := listed.insert n
  for n in library do
    for a in ← collectAxioms n do
      unless listed.contains a do
        throwError "{n} depends on axiom {a}, which is not listed in {axiomsModule}"
