import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalBreadth
import GenLimit.Paper03_HallucinationAndModeCollapse.OnlineComputation

/-!
# Certified positive online breadth (Theorem 3.5)

The existing full-support sampler realizes both fresh and repetition-allowing
breadth after an identifier stabilizes. Infinite candidate languages ensure
that every finite training input, including an incorrect conjecture, has a
nonempty fresh output law. Oracle training and ordinary computation remain
separate. Pointwise MOP needs computable membership; uniform MOP and uniform
sampling additionally need computable training.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit GenLimit.Support GenLimit.Generic

theorem identifiedBreadth_online (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ)
    (hA : GenLimit.Angluin.SemanticallyIdentifies A O.language) :
    FreshBreadthInLimit (statisticalSupportView (identifiedBreadth O A)) O.language := by
  intro i stream hP
  obtain ⟨j, hj, T, hT⟩ := hA i stream hP
  refine ⟨T, ?_⟩
  intro t ht
  have hAt : A (GenLimit.textPrefix stream t) = j := by simpa only using hT t ht
  rw [statisticalSupportView_supportAt, identifiedBreadth_support, hAt, hj, observedPrefix_set]

/-- Keep the entire conjectured language as support, allowing repetitions. -/
noncomputable def identifiedRepeatingBreadth (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ) :
    StatisticalGenerator :=
  fun xs => exactFreshSampler O [] (A xs)

theorem identifiedRepeatingBreadth_support (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ) (xs : List ℕ) :
    (identifiedRepeatingBreadth O A xs).support = O.language (A xs) := by
  simp [identifiedRepeatingBreadth, exactFreshSampler_support]

theorem identifiedRepeatingBreadth_online (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ)
    (hA : GenLimit.Angluin.SemanticallyIdentifies A O.language) :
    RepeatingBreadthInLimit (statisticalSupportView (identifiedRepeatingBreadth O A)) O.language := by
  intro i stream hP
  obtain ⟨j, hj, T, hT⟩ := hA i stream hP
  refine ⟨T, ?_⟩
  intro t ht
  have hAt : A (GenLimit.textPrefix stream t) = j := by simpa only using hT t ht
  rw [statisticalSupportView_supportAt, identifiedRepeatingBreadth_support, hAt, hj]

theorem identifiedRepeatingBreadth_oracleMOP (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ) :
    OracleMOP (generationOracle O) (identifiedRepeatingBreadth O A) := by
  intro xs
  exact ⟨freshMOPProgram [] (A xs), freshMOPProgram_correct O [] (A xs)⟩

theorem identifiedRepeatingBreadth_decidableMOP (O : OracleFamily)
    (hO : Computable₂ O.query) (A : GenLimit.Learner ℕ ℕ) :
    DecidableMOP (identifiedRepeatingBreadth O A) :=
  (identifiedRepeatingBreadth_oracleMOP O A).ordinary (generationOracle_computable O hO)

theorem identifiedRepeatingBreadth_uniformMOP (O : OracleFamily) (hO : Computable₂ O.query)
    (A : GenLimit.Learner ℕ ℕ) (hA : Computable A) :
    UniformDecidableMOP (identifiedRepeatingBreadth O A) := by
  refine ⟨fun xs x => O.query (A xs) x, (hO.comp (hA.comp Computable.fst) Computable.snd).to₂, ?_⟩
  intro xs x
  rw [identifiedRepeatingBreadth_support]
  exact O.query_spec _ _

theorem identifiedRepeatingBreadth_computableSampler (O : OracleFamily) (hO : Computable₂ O.query)
    (A : GenLimit.Learner ℕ ℕ) (hA : Computable A) :
    HasComputableSampler (identifiedRepeatingBreadth O A) := by
  refine ⟨fun z => seededFreshSample O [] (A z.1) z.2, ?_, fun _ => rfl⟩
  exact Computable.comp
    (f := fun z : (List ℕ × ℕ) × ℕ => seededFreshSample O z.1.1 z.1.2 z.2)
    (g := fun z : List ℕ × ℕ => (([], A z.1), z.2)) (seededFreshSample_computable O hO)
    (Computable.pair (Computable.pair (Computable.const []) (hA.comp Computable.fst)) Computable.snd)

/-- The certified tell-tale program stabilizes to one fixed correct index
on every positive presentation, in addition to its statistical rate. -/
theorem oracleIdentifier_identifies (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ)
    (hTell : ∀ i, GenLimit.Angluin.IsEnumeratedTellTale O.language i
      (GenLimit.Angluin.enumeratedSet emit i)) :
    GenLimit.Angluin.SemanticallyIdentifies
      (identificationProgram.run (identificationOracle (familyMembership O) emit)) O.language := by
  rw [identificationProgram_eq_angluin]
  exact GenLimit.Angluin.semanticLearner_semanticallyIdentifies
    (GenLimit.Angluin.tellTaleApproximation_of_enumeration hTell)

/-- Two actual PMF generators with certified membership-only sampling after
training. The identifier is the same certified membership/tell-tale procedure
as Theorems 3.1 and 3.3. Correct tell-tale enumerations need not be ordinarily
computable; that additional hypothesis is stated in the last conjunct. -/
def CertifiedOnlineBreadthPositiveBranch (O : OracleFamily) : Prop :=
  ∃ emit : ℕ → ℕ → Option ℕ,
    (∀ i, GenLimit.Angluin.IsEnumeratedTellTale O.language i (GenLimit.Angluin.enumeratedSet emit i)) ∧
    let A := identificationProgram.run (identificationOracle (familyMembership O) emit)
    FreshBreadthInLimit (statisticalSupportView (identifiedBreadth O A)) O.language ∧
    RepeatingBreadthInLimit (statisticalSupportView (identifiedRepeatingBreadth O A)) O.language ∧
    OracleMOP (generationOracle O) (identifiedBreadth O A) ∧
    OracleMOP (generationOracle O) (identifiedRepeatingBreadth O A) ∧
    (Computable₂ O.query → DecidableMOP (identifiedBreadth O A) ∧
      DecidableMOP (identifiedRepeatingBreadth O A)) ∧
    (Computable₂ O.query → Computable₂ emit →
      HasComputableSampler (identifiedBreadth O A) ∧
      UniformDecidableMOP (identifiedBreadth O A) ∧
      HasComputableSampler (identifiedRepeatingBreadth O A) ∧
      UniformDecidableMOP (identifiedRepeatingBreadth O A))

theorem certifiedOnlineBreadth_of_identifiable (O : OracleFamily)
    (hID : IdentifiableInLimit O.language) : CertifiedOnlineBreadthPositiveBranch O := by
  have hcond := (GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo O.language).mp hID
  obtain ⟨emit, hTell, _⟩ := oracle_exponentialIdentifies_of_conditionTwo O.language (familyMembership O) hcond
  let A := identificationProgram.run (identificationOracle (familyMembership O) emit)
  have hA : GenLimit.Angluin.SemanticallyIdentifies A O.language := oracleIdentifier_identifies O emit hTell
  refine ⟨emit, hTell, identifiedBreadth_online O A hA, identifiedRepeatingBreadth_online O A hA,
    identifiedBreadth_oracleMOP O A, identifiedRepeatingBreadth_oracleMOP O A, ?_, ?_⟩
  · intro hO
    exact ⟨identifiedBreadth_decidableMOP O hO A, identifiedRepeatingBreadth_decidableMOP O hO A⟩
  · intro hO hemit
    have hcomp : Computable A := oracleIdentifier_computable O hO emit hemit
    exact ⟨identifiedBreadth_computableSampler O hO A hcomp, identifiedBreadth_uniformMOP O hO A hcomp,
      identifiedRepeatingBreadth_computableSampler O hO A hcomp,
      identifiedRepeatingBreadth_uniformMOP O hO A hcomp⟩

end GenLimit.HallucinationModeCollapse
