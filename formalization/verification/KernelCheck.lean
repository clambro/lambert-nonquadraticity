import LeanChecker

/-!
# Bounded parallel kernel replay

The pinned `leanchecker` CLI launches one task per matching module. Reuse its
`replayFromImports` routine with three workers instead. Each worker replays one
module at a time, including private declaration bodies, so at most three import
environments are being replayed concurrently within the shared memory limit.
-/

namespace Lambert.Verification

unsafe def replayProjectBounded : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let sourceDir : System.FilePath := "Lambert"
  let sources := #[("Lambert.lean" : System.FilePath)] ++
    (← sourceDir.walkDir).filter (·.extension == some "lean")
  let modules := sources.map fun source =>
    (source.withExtension "").components.foldl Lean.Name.str .anonymous
  let requested := (← IO.getEnv "LAMBERT_CHECK_MODULES").getD ""
  let selected := if requested.isEmpty then modules else
    ((requested.splitOn " ").filter (· != "")).toArray.map String.toName
  if selected.isEmpty then
    throw <| IO.userError "No project modules selected for kernel replay"
  for mod in selected do
    unless modules.contains mod do
      throw <| IO.userError s!"Not a project source module: {mod}"
  let mut workers := #[]
  for worker in [:3] do
    workers := workers.push (← IO.asTask do
      for i in [:selected.size] do
        if i % 3 == worker then
          let mod := selected[i]!
          IO.println s!"Replaying {mod}"
          replayFromImports mod)
  for worker in workers do
    if let .error e := worker.get then
      throw e
  IO.println s!"Kernel replay passed: {selected.size} project modules"

#eval replayProjectBounded

end Lambert.Verification
