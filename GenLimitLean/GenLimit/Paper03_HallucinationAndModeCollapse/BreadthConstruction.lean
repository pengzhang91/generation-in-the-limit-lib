import GenLimit.Paper03_HallucinationAndModeCollapse.SupportMembership
import GenLimit.Paper03_HallucinationAndModeCollapse.OracleIdentification

/-!
# Statistical identification gives exact fresh breadth

The generator samples with full support from the currently identified language
after removing the training sample. Its breadth error is bounded by the
identifier's wrong-language error at every sample size. The chosen language
is infinite, so even an incorrect hypothesis always gives a terminating
numerical-seed sampler. Support-membership certificates are pointwise; ordinary
uniform sampler and MOP certificates additionally require computable training.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit GenLimit.Support GenLimit.DiscreteIID

def familyMembership (O : OracleFamily) : MembershipOracle O.language :=
  ⟨O.query, fun {i x} => O.query_spec i x⟩

noncomputable def identifiedBreadth (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ) : StatisticalGenerator :=
  fun xs => exactFreshSampler O xs (A xs)

theorem identifiedBreadth_support (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ) (xs : List ℕ) :
    (identifiedBreadth O A xs).support = O.language (A xs) \ {x | x ∈ xs} :=
  exactFreshSampler_support O xs (A xs)

theorem identifiedBreadth_error_le (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ)
    (p : PMF ℕ) (i n : ℕ) :
    breadthError O.language (identifiedBreadth O A) p i n ≤
      identificationError O.language (deterministicIdentifier A) p i n := by
  rw [identificationError_deterministic]
  apply probability_mono
  intro xs hbad heq
  apply hbad
  rw [identifiedBreadth_support, heq]

theorem identifiedBreadth_rate (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ)
    (R : ℕ → ℝ) (hA : AchievesIdentificationRate O.language (deterministicIdentifier A) R) :
    AchievesBreadthRate O.language (identifiedBreadth O A) R := by
  intro i p hp
  obtain ⟨D, hD, hb⟩ := hA i p hp
  exact ⟨D, hD, fun n => (identifiedBreadth_error_le O A p i n).trans (hb n)⟩

theorem identifiedBreadth_exponential (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ)
    (hA : ExponentialIdentifies O.language (deterministicIdentifier A)) :
    ExponentialBreadth O.language (identifiedBreadth O A) := by
  intro i p hp
  obtain ⟨c, hc, D, hD, hb⟩ := hA i p hp
  exact ⟨c, hc, D, hD, fun n => (identifiedBreadth_error_le O A p i n).trans (hb n)⟩

theorem identifiedBreadth_oracleMOP (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ) :
    OracleMOP (generationOracle O) (identifiedBreadth O A) :=
  exactFreshSampler_oracleMOP O A

theorem generationOracle_computable (O : OracleFamily) (hO : Computable₂ O.query) :
    Computable (generationOracle O) :=
  (Computable.cond (hO.comp (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp) (Computable.const 1) (Computable.const 0)).of_eq
    (fun code => by dsimp [generationOracle]; cases O.query code.unpair.1 code.unpair.2 <;> simp)

theorem identifiedBreadth_decidableMOP (O : OracleFamily) (hO : Computable₂ O.query)
    (A : GenLimit.Learner ℕ ℕ) : DecidableMOP (identifiedBreadth O A) :=
  (identifiedBreadth_oracleMOP O A).ordinary (generationOracle_computable O hO)

theorem identifiedBreadth_uniformMOP (O : OracleFamily) (hO : Computable₂ O.query)
    (A : GenLimit.Learner ℕ ℕ) (hA : Computable A) : UniformDecidableMOP (identifiedBreadth O A) := by
  let query := fun xs x => O.query (A xs) x && !(listContains xs x)
  have hq : Computable₂ query := (Primrec.and.to_comp.comp
    (hO.comp (hA.comp Computable.fst) Computable.snd)
    (Primrec.not.to_comp.comp (listContains_computable.comp Computable.fst Computable.snd))).to₂
  exact ⟨query, hq, fun xs x => exactFreshSampler_query_spec O xs (A xs) x⟩

theorem identifiedBreadth_computableSampler (O : OracleFamily) (hO : Computable₂ O.query)
    (A : GenLimit.Learner ℕ ℕ) (hA : Computable A) : HasComputableSampler (identifiedBreadth O A) := by
  refine ⟨fun z => seededFreshSample O z.1 (A z.1) z.2, ?_, ?_⟩
  · have hi : Computable (fun z : List ℕ × ℕ => ((z.1, A z.1), z.2)) :=
      Computable.pair (Computable.pair Computable.fst (hA.comp Computable.fst)) Computable.snd
    exact Computable.comp
      (f := fun z : (List ℕ × ℕ) × ℕ => seededFreshSample O z.1.1 z.1.2 z.2)
      (g := fun z : List ℕ × ℕ => ((z.1, A z.1), z.2))
      (seededFreshSample_computable O hO) hi
  · intro xs
    rfl

theorem deterministic_computableSampler (A : GenLimit.Learner ℕ ℕ) (hA : Computable A) :
    HasComputableSampler (deterministicIdentifier A) := by
  refine ⟨fun z => A z.1, hA.comp Computable.fst, ?_⟩
  intro xs
  exact (PMF.map_const (p := positiveGeometric) (b := A xs)).symm

theorem oracleIdentifier_computable (O : OracleFamily) (hO : Computable₂ O.query)
    (emit : ℕ → ℕ → Option ℕ) (hemit : Computable₂ emit) :
    Computable (identificationProgram.run (identificationOracle (familyMembership O) emit)) := by
  let F : GenLimit.Angluin.EffectiveIndexedFamily := {
    language := O.language
    membership := O.query
    membership_spec := O.query_spec
    membership_computable := hO
    nonempty := fun i => (O.infinite' i).nonempty }
  exact identificationProgram_computable F emit hemit

theorem oracle_identifiedBreadth_exponential (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ)
    (hTell : ∀ i, GenLimit.Angluin.IsEnumeratedTellTale O.language i
      (GenLimit.Angluin.enumeratedSet emit i)) :
    ExponentialBreadth O.language (identifiedBreadth O
      (identificationProgram.run (identificationOracle (familyMembership O) emit))) :=
  identifiedBreadth_exponential O _
    (oracle_exponentialIdentifies_of_enumeration O.language (familyMembership O) emit hTell)

theorem oracle_identifiedBreadth_rate (O : OracleFamily) (emit : ℕ → ℕ → Option ℕ)
    (hTell : ∀ i, GenLimit.Angluin.IsEnumeratedTellTale O.language i
      (GenLimit.Angluin.enumeratedSet emit i))
    (g : ℕ → ℝ) (hg : AdmissibleSublinearExponent g) :
    AchievesBreadthRate O.language (identifiedBreadth O
      (identificationProgram.run (identificationOracle (familyMembership O) emit)))
      (fun n => Real.exp (-g n)) :=
  identifiedBreadth_rate O _ _ (exponential_rate_implies_sublinear_rate O.language _
    (oracle_exponentialIdentifies_of_enumeration O.language (familyMembership O) emit hTell) g hg)

end GenLimit.HallucinationModeCollapse
