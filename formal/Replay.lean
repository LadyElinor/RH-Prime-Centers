import Lean.Replay

open Lean

/-- Replay the local proof declarations against their imported dependencies. -/
def main (args : List String) : IO Unit := do
  let (path, targets) ← match args with
    | [path] => pure (path, [`PrimeWindowCertificate.doubling_floor, `PrimeWindowCertificate.recorded_floors])
    | ["tent", path] => pure (path, [`PrimeWindowTransfer.tent_uniform, `PrimeWindowTransfer.tent_sharp,
        `PrimeWindowTransfer.tent_model, `PrimeWindowTransfer.finite_formula_transfer,
        `PrimeWindowTransfer.core3_uniform_vanishing, `PrimeWindowTransfer.finite_formula_vanishing])
    | ["core3", path] => pure (path, [`PrimeWindowCore3.conductor_one, `PrimeWindowCore3.zeros_finite, `PrimeWindowCore3.lowMass_nonneg,
        `PrimeWindowCore3.smoothed_bound, `PrimeWindowCore3.smoothed_vanishing])
    | _ => throw (IO.userError "Usage: Replay.lean [tent|core3] MODULE.olean")
  initSearchPath (← findSysroot)
  let (data, _) ← readModuleData path
  for target in targets do
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
