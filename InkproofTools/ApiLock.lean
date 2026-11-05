/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

open Lean Meta

namespace InkproofTools.ApiLock

/-- Last name components of declarations Lean derives from a public declaration. They change only
when that declaration does, which its own line already records. -/
private def derivedSuffixes : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ibelow", "noConfusion",
   "noConfusionType", "inj", "injEq", "sizeOf_spec", "ctorIdx", "ctorElim", "ctorElimType",
   "eq_def", "eq_unfold", "congr_simp"]

private def isDerivedName (n : Name) : Bool :=
  match n with
  | .str _ s => derivedSuffixes.contains s || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  | _ => false

private def isApi (env : Environment) (n : Name) : MetaM Bool := do
  if n.isInternalDetail || isPrivateName n || isDerivedName n then return false
  if isAuxRecursor env n || isNoConfusion env n || (← isMatcher n) then return false
  return true

private def kind (env : Environment) (n : Name) : ConstantInfo → MetaM String
  | .axiomInfo _ => pure "axiom"
  | .thmInfo _ => pure "theorem"
  | .opaqueInfo _ => pure "opaque"
  | .quotInfo _ => pure "quot"
  | .recInfo _ => pure "recursor"
  | .ctorInfo _ => pure "constructor"
  | .inductInfo _ =>
    pure <| if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | .defnInfo _ => do
    if ← isInstance n then return "instance"
    if (env.getProjectionFnInfo? n).isSome then return "field"
    return "def"

/-- Collapses a pretty-printed type to one line, so each declaration is exactly one line. -/
private def oneLine (s : String) : String :=
  " ".intercalate (s.splitToList Char.isWhitespace |>.filter (!·.isEmpty))

/-- The public API of every module whose name starts with one of `roots`, except modules with an
`Internal` component, which no consumer may import: one line per public declaration giving its
kind, name and type, sorted by name. -/
def apiLines (roots : Array Name) : MetaM (Array String) := do
  let env ← getEnv
  let inScope (n : Name) : Bool :=
    (env.getModuleIdxFor? n >>= (env.allImportedModuleNames[·.toNat]?)).any
      fun m => roots.any (·.isPrefixOf m) && !m.components.contains `Internal
  let mut lines : Array (Name × String) := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless inScope n do continue
    unless ← isApi env n do continue
    let ty ← withOptions (fun o => o.set `format.width (100000 : Nat) |>.set `pp.fullNames true) do
      ppExpr ci.type
    lines := lines.push (n, s!"{← kind env n ci} {n} : {oneLine (toString ty)}")
  return lines.qsort (fun a b => a.1.toString < b.1.toString) |>.map (·.2)

/-- Imports `roots` and prints their API lines. -/
def run (roots : Array Name) : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules (roots.map ({ module := · })) {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<api-lock>", fileMap := default }
  let (lines, _) ← (apiLines roots).run' |>.toIO ctx { env }
  for line in lines do IO.println line

end InkproofTools.ApiLock
