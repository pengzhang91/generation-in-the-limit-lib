import GenLimit.Paper11_LearningAlgorithmsInTheLimit
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt

elab "assert_allowed_axioms " n:ident : command => do
  let name ← liftCoreM <|
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let actual := (← Lean.collectAxioms name).qsort Name.lt
  unless actual.all fun ax => allowedAxioms.contains ax do
    throwError m!"unexpected axioms for {name}: {actual.toList}"

assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.enumeration_stabilizes_to_least
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.enumeration_learnsInLimit
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.theorem_12_timeRestrictedIOO_core
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.corollary_13_parametrizedTMClass_core
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.theorem_14_universalTBO_core
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.corollary_15_turingTBO
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.theorem_12_minIndex_claim_not_justified
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.theorem_16_recursiveToRational_behavior
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.theorem_16_rationalEnumeration_core
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.lemma_9_distinguishability
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.theorem_17_lateSplit_characteristic_obstruction
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.theorem_17_mass_lower_bound_core
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.corollary_18_forgetting_preserves_indistinguishability
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.corollary_18_characteristic_bound_lifts_to_richer_observations
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.theorem_21_tagged_two_step
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.taggedMachine_runFrom
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.theorem_21_transition_cover_core
assert_allowed_axioms
  GenLimit.LearningAlgorithmsLimit.theorem_21_msm_merge_order_core
