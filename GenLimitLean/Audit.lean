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
assert_axioms GenLimit.PartialEnumeration.Counterexample.output_not_mem_trueLanguage
assert_axioms GenLimit.PartialEnumeration.lemma_3_16_generation
assert_axioms GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17
assert_axioms GenLimit.PartialEnumeration.theorem_3_17_lowerDensity
assert_axioms GenLimit.PartialEnumeration.theorem_3_17
assert_axioms GenLimit.Gold.Abstract.gold_theorem_7_1
assert_axioms GenLimit.Gold.Text.finiteLanguages_identifiableWith
assert_axioms GenLimit.Gold.Text.finiteLanguages_maximal_semanticallyIdentifiable
assert_axioms GenLimit.Gold.Text.enumerationLearner_identifiesFamily_of_isInclusionAntichain
assert_axioms GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily
assert_axioms GenLimit.Gold.Text.exists_locking_of_identifiesLanguage
assert_axioms GenLimit.Gold.Text.superfinite_not_semanticallyIdentifiable
assert_axioms GenLimit.Gold.identifier_implies_fresh_generation
assert_axioms GenLimit.GoldKMSeparation.generation_without_identification
assert_axioms GenLimit.GoldDenseSeparation.dense_generation_without_identification
