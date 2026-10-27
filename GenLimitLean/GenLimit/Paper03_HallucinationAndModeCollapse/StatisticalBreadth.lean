import GenLimit.Paper03_HallucinationAndModeCollapse.BreadthIdentification
import GenLimit.Paper03_HallucinationAndModeCollapse.BreadthConstruction

/-!
# Theorem 3.3: statistical breadth and consistency

The source's infinite-language generation regime is explicit in `OracleFamily`.
The negative branch covers Definition 6's pointwise decidable-MOP class, and
its proof actually applies to every semantic PMF generator. The consistent
generator and randomized optimality bound reuse Theorem 3.2.

The identifiable branch uses the same tell-tale oracle interpretation as
Theorem 3.1. It supplies certified sampling and pointwise oracle-MOP procedures;
ordinary computability is asserted only when the relevant membership and
tell-tale procedures are computable. In particular nonuniform `ConditionTwo`
is not silently replaced by effective `ConditionOne`.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit GenLimit.Support

noncomputable def tellTaleBreadthGenerator (O : OracleFamily)
    (emit : ℕ → ℕ → Option ℕ) : StatisticalGenerator :=
  identifiedBreadth O (identificationProgram.run (identificationOracle (familyMembership O) emit))

/-- One distribution-independent oracle program supplies every admissible
almost-exponential rate, with a stronger exponential upper bound. Its support
decider needs only family membership once the trained hypothesis is fixed.
Uniform ordinary computation additionally requires a computable tell-tale
enumerator, exactly as for the identification procedure. -/
def CertifiedBreadthPositiveBranch (O : OracleFamily) : Prop :=
  ∃ emit : ℕ → ℕ → Option ℕ,
    (∀ i, GenLimit.Angluin.IsEnumeratedTellTale O.language i (GenLimit.Angluin.enumeratedSet emit i)) ∧
    OracleMOP (generationOracle O) (tellTaleBreadthGenerator O emit) ∧
    ExponentialBreadth O.language (tellTaleBreadthGenerator O emit) ∧
    (∀ g : ℕ → ℝ, AdmissibleSublinearExponent g →
      AchievesBreadthRate O.language (tellTaleBreadthGenerator O emit) (fun n => Real.exp (-g n))) ∧
    (Computable₂ O.query → DecidableMOP (tellTaleBreadthGenerator O emit)) ∧
    (Computable₂ O.query → Computable₂ emit →
      HasComputableSampler (tellTaleBreadthGenerator O emit) ∧
      UniformDecidableMOP (tellTaleBreadthGenerator O emit))

theorem certifiedBreadth_of_identifiable (O : OracleFamily)
    (hID : IdentifiableInLimit O.language) : CertifiedBreadthPositiveBranch O := by
  have hTell := (GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo O.language).mp hID
  obtain ⟨emit, hE, hA⟩ := oracle_exponentialIdentifies_of_conditionTwo O.language (familyMembership O) hTell
  refine ⟨emit, hE, identifiedBreadth_oracleMOP O _, identifiedBreadth_exponential O _ hA, ?_, ?_, ?_⟩
  · intro g hg
    exact identifiedBreadth_rate O _ _ (exponential_rate_implies_sublinear_rate O.language _ hA g hg)
  · intro hO
    exact identifiedBreadth_decidableMOP O hO _
  · intro hO hemit
    have hcomp := oracleIdentifier_computable O hO emit hemit
    exact ⟨identifiedBreadth_computableSampler O hO _ hcomp,
      identifiedBreadth_uniformMOP O hO _ hcomp⟩

theorem deterministic_decidableMOP (A : GenLimit.Learner ℕ ℕ) : DecidableMOP (deterministicIdentifier A) :=
  (deterministic_oracleMOP (fun _ => 0) A).ordinary (Computable.const 0)

/-- The positive ordinary-computation specialization under effective Angluin
Condition 1. This is a certificate for one actual sampler and one uniform
support decider, not a claim of effectivity from bare finite tell-tales. -/
theorem computable_breadth_of_conditionOne (F : GenLimit.Angluin.EffectiveIndexedFamily)
    (hinf : ∀ i, (F.language i).Infinite) (hF : GenLimit.Angluin.ConditionOne F) :
    ∃ G : StatisticalGenerator, HasComputableSampler G ∧ UniformDecidableMOP G ∧
      ExponentialBreadth F.language G := by
  obtain ⟨emit, hemit, hTell⟩ := hF
  let O : OracleFamily := ⟨F.language, hinf, F.membership, F.membership_spec⟩
  let A := identificationProgram.run (identificationOracle (familyMembership O) emit)
  have hA : Computable A := oracleIdentifier_computable O F.membership_computable emit hemit
  exact ⟨identifiedBreadth O A,
    identifiedBreadth_computableSampler O F.membership_computable A hA,
    identifiedBreadth_uniformMOP O F.membership_computable A hA,
    oracle_identifiedBreadth_exponential O emit hTell⟩

/-- Theorem 3.3, with Definition 6's pointwise MOP quantifiers and explicit
oracle/ordinary computation boundaries. Generation nontriviality is used only
for the matching exponential lower bound. -/
theorem theorem_3_3 (O : OracleFamily) (hC : GenerationNontrivial O.language) :
    (¬IdentifiableInLimit O.language → ∀ G : StatisticalGenerator, DecidableMOP G →
      NoBreadthRate O.language G) ∧
    (∃ G : StatisticalGenerator, DecidableMOP G ∧ OracleMOP (generationOracle O) G ∧
      ExponentialGenerates O.language G ∧ (Computable₂ O.query → HasComputableSampler G)) ∧
    (IdentifiableInLimit O.language → CertifiedBreadthPositiveBranch O) ∧
    (∀ G : StatisticalGenerator, ∃ i p, ValidDistribution O.language i p ∧
      ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
        ∃ᶠ n : ℕ in Filter.atTop, D * Real.exp (-c * n) ≤ generationError O.language G p i n) := by
  refine ⟨?_, ?_, certifiedBreadth_of_identifiable O, lemma_5_10 O.language hC⟩
  · intro hnot G _hMOP
    exact noBreadthRate_of_not_identifiable O.language (familyMembership O) hnot G
  · refine ⟨deterministicIdentifier (certifiedKM O), deterministic_decidableMOP _,
      deterministic_oracleMOP _ _, certifiedKM_exponential O, ?_⟩
    intro hO
    exact deterministic_computableSampler _ (certifiedKM_computable O hO)

end GenLimit.HallucinationModeCollapse
