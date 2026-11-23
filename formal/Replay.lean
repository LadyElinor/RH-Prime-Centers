import Lean.Replay

open Lean

/-- Replay the local proof declarations against their imported dependencies. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Expected a compiled WindowCertificate.olean path")
  initSearchPath (← findSysroot)
  let (data, _) ← readModuleData path
  for target in [`PrimeWindowCertificate.doubling_floor, `PrimeWindowCertificate.recorded_floors] do
    unless data.constNames.contains target do
      throw (IO.userError s!"Missing target {target}")
  let mut localDecls : Std.HashMap Name ConstantInfo := {}
  for ci in data.constants do
    if ci.isUnsafe || ci.isPartial || ci.getUsedConstantsAsSet.contains `sorryAx then
      throw (IO.userError s!"Unexpected declaration or placeholder in {ci.name}")
    if let .axiomInfo _ := ci then
      throw (IO.userError s!"Unexpected local axiom {ci.name}")
    localDecls := localDecls.insert ci.name ci
  let base ← importModules data.imports {}
  let _ ← Environment.replay localDecls base
  IO.println s!"Kernel replay accepted {localDecls.size} local declarations."
