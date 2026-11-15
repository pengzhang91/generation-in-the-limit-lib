import GenLimit.NoRegretLanguageGeneration
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Audit every public and private project theorem, including nested namespaces.
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "PredictionToGeneration." ||
        name.toString.startsWith "_private.GenLimit.NoRegretLanguageGeneration." then
      match info with
      | .axiomInfo _ => throwError "Forbidden project declaration: {name}"
      | .thmInfo _ =>
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected dependency {ax} in {name}"
        logInfo m!"{name}: {axioms}"
        count := count + 1
      | _ => pure ()
  if count == 0 then throwError "No project theorems found"
  logInfo m!"AUDIT PASSED: {count} project theorems; only standard logical axioms."

