/-
  Verify that proofs in CellularAutomatas use only allowed axioms.
  Usage: lake build verify_proofs

  Configuration is in scripts/VerifyConfig.lean.
  Fails if any module uses disallowed axioms or if config references non-existent modules.
-/
import Lean
import CellularAutomatas.all
import CellularAutomatas.scripts.VerifyConfig

open Lean Elab Command

partial def collectAxiomsFromEnv (env : Environment) (constName : Name) : NameSet :=
  let rec visit (name : Name) (visited : NameSet) (axioms : NameSet) : NameSet × NameSet :=
    if visited.contains name then (visited, axioms)
    else
      let visited := visited.insert name
      match env.find? name with
      | some (.axiomInfo _) => (visited, axioms.insert name)
      | some info =>
        let usedConsts := info.getUsedConstantsAsSet.toArray
        usedConsts.foldl (init := (visited, axioms)) fun (visited, axioms) depName =>
          visit depName visited axioms
      | none => (visited, axioms)
  (visit constName {} {}).2

def getModuleConstants (env : Environment) (moduleName : Name) : Array Name :=
  let moduleIdx := env.getModuleIdx? moduleName
  match moduleIdx with
  | some idx =>
    env.constants.fold (init := #[]) fun acc name _ =>
      if env.getModuleIdxFor? name == some idx then acc.push name else acc
  | none => #[]

def getModuleAxioms (env : Environment) (moduleName : Name) : NameSet :=
  let consts := getModuleConstants env moduleName
  consts.foldl (init := NameSet.empty) fun acc constName =>
    let axioms := collectAxiomsFromEnv env constName
    axioms.toArray.foldl (init := acc) fun acc ax => acc.insert ax

-- Get all modules that are part of CellularAutomatas (filter by prefix)
def getCellularAutomatasModules (env : Environment) : List Name :=
  let allModules := env.header.moduleNames.toList
  allModules.filter fun name => `CellularAutomatas |>.isPrefixOf name

structure VerificationError where
  module : Name
  message : String
  details : List String := []

def analyzeAndVerify (env : Environment) (config : List (Name × List Name)) : IO (List VerificationError) := do
  let modules := getCellularAutomatasModules env
  let mut errors : List VerificationError := []

  -- Check for non-existent modules in config
  for (configModule, _) in config do
    if configModule ∉ modules then
      errors := errors ++ [{
        module := configModule,
        message := "Config references non-existent module",
        details := [s!"Available modules: {modules}"]
      }]

  -- Verify each module against config
  for m in modules do
    match config.find? (·.1 == m) with
    | some (_, allowedAxioms) =>
      let axiomList := (getModuleAxioms env m).toList
      let disallowed := axiomList.filter (· ∉ allowedAxioms)
      if !disallowed.isEmpty then
        errors := errors ++ [{
          module := m,
          message := "Uses disallowed axioms",
          details := disallowed.map toString
        }]
    | none => pure ()

  return errors

#eval show CommandElabM Unit from do
  let env ← getEnv
  let errors ← analyzeAndVerify env verifyConfig
  if errors.isEmpty then
    IO.println s!"✓ All {verifyConfig.length} configured module(s) verified successfully"
  else
    for err in errors do
      IO.eprintln s!"ERROR [{err.module}]: {err.message}"
      for detail in err.details do
        IO.eprintln s!"  • {detail}"
    throwError s!"Verification failed with {errors.length} error(s)"
