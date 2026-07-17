import GenLimit
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt

/-- Fail unless a declaration uses exactly the project's allowed logical dependencies. -/
elab "assert_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let actual := (← Lean.collectAxioms name).qsort Name.lt
  unless actual == allowedAxioms do
    throwError m!"unexpected axioms for {name}: {actual.toList}; expected {allowedAxioms.toList}"
  logInfo m!"{name}: {actual.toList}"

assert_axioms GenLimit.KM.Semantic.kleinbergMullainathan_main
assert_axioms GenLimit.OracleFamily.kleinbergMullainathan_main
assert_axioms GenLimit.PatientMachine.patient_validity
assert_axioms GenLimit.PatientMachine.settledChargingCertificate
assert_axioms GenLimit.PatientMachine.patientScope_lowerDensity_half
assert_axioms GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
