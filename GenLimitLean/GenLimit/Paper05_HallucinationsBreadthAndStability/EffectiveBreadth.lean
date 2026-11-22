import GenLimit.Paper05_HallucinationsBreadthAndStability.StableAndUnambiguous
import GenLimit.Paper03_HallucinationAndModeCollapse.OnlineBreadthConstruction

/-! # Sampling exact and stable whole-target supports from tell-tale training -/

namespace GenLimit.BreadthCharacterizations

open GenLimit.HallucinationModeCollapse

/-- Support of the distribution trained on the ordered positive history. -/
def lawSupport (G : StatisticalGenerator) : SupportAlgorithm ℕ := fun xs => (G xs).support

/-- Theorems 3.3, 3.15, 4.3 and 4.5 share the same tell-tale training program.
The two sampling modes respectively remove and retain the training set.
The computability assumptions refer to the two oracles actually used. -/
theorem certified_breadth_of_conditionTwo (O : OracleFamily) (hc : Angluin.ConditionTwo O.language) :
    ∃ emit : ℕ → ℕ → Option ℕ,
      (∀ i, Angluin.IsEnumeratedTellTale O.language i (Angluin.enumeratedSet emit i)) ∧
      let A := identificationProgram.run (identificationOracle (familyMembership O) emit)
      let fresh := identifiedBreadth O A
      let whole := identifiedRepeatingBreadth O A
      IsExactBreadthGenerator (lawSupport fresh) O.language ∧
      IsStableGenerator (lawSupport whole) O.language ∧
      IsApproximateBreadthGenerator (lawSupport whole) O.language ∧
      GeneratesUnambiguously (lawSupport whole) O.language ∧
      OracleMOP (generationOracle O) fresh ∧ OracleMOP (generationOracle O) whole ∧
      (Computable₂ O.query → DecidableMOP fresh ∧ DecidableMOP whole) ∧
      (Computable₂ O.query → Computable₂ emit →
        HasComputableSampler fresh ∧ UniformDecidableMOP fresh ∧
        HasComputableSampler whole ∧ UniformDecidableMOP whole) := by
  obtain ⟨emit,ht,hf,hw,hfm,hwm,hm,hcpt⟩ := certifiedOnlineBreadth_of_identifiable O
    ((Angluin.semanticallyInferrable_iff_conditionTwo O.language).mpr hc)
  let A := identificationProgram.run (identificationOracle (familyMembership O) emit)
  have fresh : IsExactBreadthGenerator (lawSupport (identifiedBreadth O A)) O.language := by
    intro i s hp
    obtain ⟨T,hT⟩ := hf i s hp
    exact ⟨T, fun t h => by simpa only [ExactBreadthCorrectAt, supportAt, lawSupport,
      statisticalSupportView_supportAt] using hT t h⟩
  have whole : IsWholeTargetGenerator (lawSupport (identifiedRepeatingBreadth O A)) O.language := by
    intro i s hp
    obtain ⟨T,hT⟩ := hw i s hp
    exact ⟨T,fun t h => by simpa only [WholeTargetCorrectAt, supportAt, lawSupport,
      statisticalSupportView_supportAt] using hT t h⟩
  exact ⟨emit, ht, fresh, wholeTargetGenerator_isStable whole, wholeTargetGenerator_implies_approximate whole,
    whole_unambiguous whole, hfm, hwm, hm, hcpt⟩

end GenLimit.BreadthCharacterizations
