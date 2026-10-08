import Lambert
import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms

/-!
# Library admission audit

Run from `formalization/` after `lake build`. Check every source module is
imported by the root, and inspect declarations by their defining module, including
private declarations and declarations outside the Lambert namespace.
-/

open Lean Elab Command

set_option autoImplicit false

run_cmd do
  let env ← getEnv
  let sourceDir : System.FilePath := "Lambert"
  let mut sources : Array System.FilePath := #["Lambert.lean"]
  if ← sourceDir.pathExists then
    sources := sources ++ (← sourceDir.walkDir).filter (·.extension == some "lean")
  let mut modules : Array Name := #[]
  for source in sources do
    let mod := (source.withExtension "").components.foldl Name.str .anonymous
    unless env.header.moduleNames.contains mod do
      throwError "{source} is missing from the imports of Lambert.lean"
    modules := modules.push mod

  let requested := (← IO.getEnv "LAMBERT_CHECK_MODULES").getD ""
  let selected := if requested.isEmpty then modules else
    ((requested.splitOn " ").filter (· != "")).toArray.map String.toName
  if selected.isEmpty then
    throwError "No project modules selected for the axiom audit"
  for mod in selected do
    unless modules.contains mod do
      throwError "Not a project source module: {mod}"

  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless modules.contains mod do continue
    if info.isAxiom then
      logError m!"Project axiom is forbidden: {name} (module {mod})"
      rejected := rejected + 1
    unless selected.contains mod do continue
    checked := checked + 1
    let unexpected := (← collectAxioms name).filter (!allowed.contains ·)
    unless unexpected.isEmpty do
      logError m!"{name} depends on forbidden axioms: {unexpected}"
      rejected := rejected + 1
  if rejected != 0 then
    throwError "Axiom audit failed with {rejected} violations"
  logInfo m!"Axiom audit passed: {checked} declarations across {selected.size} project modules"
