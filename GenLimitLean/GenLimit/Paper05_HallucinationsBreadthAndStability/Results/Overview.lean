import GenLimit.Paper05_HallucinationsBreadthAndStability.CriticalSampler
import GenLimit.Paper05_HallucinationsBreadthAndStability.DiagonalEnumeration
import GenLimit.Paper05_HallucinationsBreadthAndStability.ExhaustiveGeneration
import GenLimit.Paper05_HallucinationsBreadthAndStability.FrozenCoverage
import GenLimit.Paper05_HallucinationsBreadthAndStability.SharedSupport
import GenLimit.Paper05_HallucinationsBreadthAndStability.StatisticalRates

/-!
# P05 main theorems and corollaries

Kalavasis, Mehrotra and Velegkas, *On Characterizations for Language Generation:
Interplay of Hallucinations, Breadth, and Stability*, arXiv:2412.18530v2.

Theorems 3.3, 3.8 and 3.15 are the three headline characterizations.
Their necessity statements allow arbitrary support-valued generators. Their
constructions train by finite oracle queries on words encoded by natural numbers.
For proofs on arbitrary countable alphabets see `ExactBreadth`, `Uniqueness`
and `StableAndUnambiguous`. For the Section 7 lemmas, propositions, examples
and the cited Appendix B theorem see `Results.Supporting`.

Remark 8.5 calls the subset-oracle construction a function. The tell-tale
construction reads an enumeration one stage per query. Ordinary computability
of each sampler requires computability of the indicated query procedures.
-/

namespace GenLimit.BreadthCharacterizations.Results

open GenLimit.Generic

/-! ## Section 3. Exact, approximate and stable breadth -/

open HallucinationModeCollapse in
/-- Theorem 3.3 on encoded words. Necessity applies to arbitrary supports.
Given any valid strong tell-tale enumeration, the membership/tell-tale training
program yields a sampler supported on precisely the unseen target words in
the limit. After training, membership queries decide support membership. -/
theorem theorem_3_3 (O : OracleFamily) :
    (ExactBreadthGeneratable O.language ↔ Angluin.ConditionTwo O.language) ∧
    (∀ emit : ℕ → ℕ → Option ℕ,
      (∀ i, Angluin.IsEnumeratedTellTale O.language i (Angluin.enumeratedSet emit i)) →
      let A := identificationProgram.run (identificationOracle (familyMembership O) emit)
      let G := identifiedBreadth O A
      IsExactBreadthGenerator (lawSupport G) O.language ∧ OracleMOP (generationOracle O) G ∧
        (Computable₂ O.query → Computable₂ emit → HasComputableSampler G ∧ UniformDecidableMOP G)) := by
  refine ⟨exactBreadthGeneratable_iff_conditionTwo O.language, ?_⟩
  intro emit he
  let A := identificationProgram.run (identificationOracle (familyMembership O) emit)
  refine ⟨?_, identifiedBreadth_oracleMOP O A, ?_⟩
  · intro i s hp
    obtain ⟨T, hT⟩ := identifiedBreadth_online O A (oracleIdentifier_identifies O emit he) i s hp
    exact ⟨T, fun t ht ↦ by simpa only [statisticalSupportView_supportAt] using hT t ht⟩
  · intro ho hem
    have hA : Computable A := oracleIdentifier_computable O ho emit hem
    exact ⟨identifiedBreadth_computableSampler O ho A hA, identifiedBreadth_uniformMOP O ho A hA⟩

/-- Theorem 3.5. A criterion compatible with at most one target at each history
requires strong tell-tales. -/
theorem theorem_3_5 [Countable α] {F : Generic.LanguageFamily α}
    (hne : ∀ i, (F i).Nonempty) {P : List α → Set α → Prop}
    (unique : ∀ xs i j, P xs (F i) → P xs (F j) → F i = F j)
    (hP : EventuallyGeneratesWith P F) : Angluin.ConditionTwo F :=
  GenLimit.BreadthCharacterizations.theorem_3_5 hne unique hP

open HallucinationModeCollapse in
/-- Theorem 3.8 on encoded words. The equivalence quantifies over arbitrary
supports. Lemma 7.1 realizes sufficiency with membership and subset queries.
Lemma 7.3 realizes it with membership queries and any valid weak tell-tale
enumeration. Each sampler has the indicated computability guarantees. -/
theorem theorem_3_8 (O : OracleFamily) :
    (ApproximateBreadthGeneratable O.language ↔ WeakAngluinCondition O.language) ∧
    (∀ S : SubsetOracle O.language, WeakAngluinCondition O.language →
      let G := criticalSampler O S
      IsApproximateBreadthGenerator (lawSupport G) O.language ∧ OracleMOP (generationOracle O) G ∧
        (Computable₂ O.query → Computable₂ S.query → HasComputableSampler G ∧ UniformDecidableMOP G)) ∧
    (∀ emit : ℕ → ℕ → Option ℕ,
      (∀ i, CharikarPabbaraju.IsEnumeratedWeakTellTale O.language i (Angluin.enumeratedSet emit i)) →
      let G := weakLaw O emit
      IsApproximateBreadthGenerator (lawSupport G) O.language ∧ OracleMOP (generationOracle O) G ∧
        (Computable₂ O.query → Computable₂ emit → HasComputableSampler G ∧ UniformDecidableMOP G)) :=
  ⟨GenLimit.BreadthCharacterizations.theorem_3_8_semantic (fun i ↦ (O.infinite' i).nonempty),
    fun S hw ↦ ⟨GenLimit.BreadthCharacterizations.lemma_7_1 O S hw, criticalSampler_oracles O S⟩,
    GenLimit.BreadthCharacterizations.lemma_7_3 O⟩

open scoped symmDiff in
/-- Theorem 3.10 with the symmetric-difference criterion from Definition 3.9. -/
theorem theorem_3_10 [Countable α] {F : Generic.LanguageFamily α} (hi : ∀ i, (F i).Infinite)
    {P : List α → Set α → Prop}
    (hfinite : ∀ xs i j, P xs (F i) → P xs (F j) → (F i ∆ F j).Finite)
    (hP : EventuallyGeneratesWith P F) : WeakAngluinCondition F := by
  apply GenLimit.BreadthCharacterizations.theorem_3_10 (fun i ↦ (hi i).nonempty) _ hP
  intro xs i j _ _ h₁ h₂
  have h := hfinite xs i j h₁ h₂
  rw [Set.symmDiff_def] at h
  exact h.subset Set.subset_union_left

open HallucinationModeCollapse in
/-- Theorem 3.15 on encoded words. Stable approximate breadth characterizes
strong tell-tales. Under footnote 3 the sampler may repeat observations and
its support stabilizes on the entire target. Under literal Definition 3.1
the support must equal the unseen target, which precludes raw stability. -/
theorem theorem_3_15 (O : OracleFamily) :
    ((∃ G, IsStableGenerator G O.language ∧ IsApproximateBreadthGenerator G O.language) ↔
      Angluin.ConditionTwo O.language) ∧
    ((∃ G, IsWholeTargetGenerator G O.language ∧ IsStableGenerator G O.language) ↔
      Angluin.ConditionTwo O.language) ∧
    (¬ ∃ G, IsStableGenerator G O.language ∧ IsExactBreadthGenerator G O.language) ∧
    (∀ emit : ℕ → ℕ → Option ℕ,
      (∀ i, Angluin.IsEnumeratedTellTale O.language i (Angluin.enumeratedSet emit i)) →
      let A := identificationProgram.run (identificationOracle (familyMembership O) emit)
      let G := identifiedRepeatingBreadth O A
      IsWholeTargetGenerator (lawSupport G) O.language ∧ IsStableGenerator (lawSupport G) O.language ∧
        IsApproximateBreadthGenerator (lawSupport G) O.language ∧ OracleMOP (generationOracle O) G ∧
        (Computable₂ O.query → Computable₂ emit → HasComputableSampler G ∧ UniformDecidableMOP G)) := by
  refine ⟨theorem_3_15_approximate_countable O.language (fun i ↦ (O.infinite' i).nonempty),
    stableWholeTargetGeneratable_iff_conditionTwo O.language,
    no_stable_exactBreadth_for_infinite_family O.language O.infinite', ?_⟩
  intro emit he
  let A := identificationProgram.run (identificationOracle (familyMembership O) emit)
  have whole : IsWholeTargetGenerator (lawSupport (identifiedRepeatingBreadth O A)) O.language := by
    intro i s hp
    obtain ⟨T, hT⟩ := identifiedRepeatingBreadth_online O A (oracleIdentifier_identifies O emit he) i s hp
    exact ⟨T, fun t ht ↦ by simpa only [statisticalSupportView_supportAt] using hT t ht⟩
  refine ⟨whole, wholeTargetGenerator_isStable whole, wholeTargetGenerator_implies_approximate whole,
    identifiedRepeatingBreadth_oracleMOP O A, ?_⟩
  intro ho hem
  have hA : Computable A := oracleIdentifier_computable O ho emit hem
  exact ⟨identifiedRepeatingBreadth_computableSampler O ho A hA, identifiedRepeatingBreadth_uniformMOP O ho A hA⟩

/-! ## Section 4. Breadth, stability, and hallucinations -/

/-- Theorem 4.3. Exact and unambiguous breadth require strong tell-tales.
Approximate and exhaustive breadth require weak tell-tales. The exact and
approximate samplers are given in Theorems 3.3 and 3.8. Lemmas 7.5 and 7.7
give exhaustive enumerators with their respective oracles. -/
theorem theorem_4_3 [Nonempty α] [Countable α] (F : Generic.LanguageFamily α)
    (hi : ∀ i, (F i).Infinite) :
    (ExactBreadthGeneratable F ↔ Angluin.ConditionTwo F) ∧
    ((∃ G, GeneratesUnambiguously G F) ↔ Angluin.ConditionTwo F) ∧
    (ApproximateBreadthGeneratable F ↔ WeakAngluinCondition F) ∧
    ((∃ A, EnumeratesExhaustively A F) ↔ WeakAngluinCondition F) :=
  ⟨exactBreadthGeneratable_iff_conditionTwo F, theorem_4_3_unambiguous F (fun i ↦ (hi i).nonempty),
    GenLimit.BreadthCharacterizations.theorem_3_8_semantic (fun i ↦ (hi i).nonempty),
    theorem_4_3_exhaustive F hi⟩

/-- Theorem 4.5 on encoded words. The first three equivalences use footnote 3
for stable exact breadth. With literal Definition 3.1 stable exact breadth
is impossible. For exhaustive generation Equation (2) gives the weak
tell-tale criterion. The co-singleton family witnesses failure of the
printed strong criterion (see `theorem_4_5_stable_exhaustive_counterexample`). -/
theorem theorem_4_5 (O : OracleFamily) :
    ((∃ G, IsStableGenerator G O.language ∧ IsApproximateBreadthGenerator G O.language) ↔
      Angluin.ConditionTwo O.language) ∧
    ((∃ G, IsWholeTargetGenerator G O.language ∧ IsStableGenerator G O.language) ↔
      Angluin.ConditionTwo O.language) ∧
    ((∃ G, IsStableGenerator G O.language ∧ GeneratesUnambiguously G O.language) ↔
      Angluin.ConditionTwo O.language) ∧
    (¬ ∃ G, IsStableGenerator G O.language ∧ IsExactBreadthGenerator G O.language) ∧
    ((∃ B, IsStableGenerator (enumeratorSupport B) O.language ∧ EnumeratesExhaustively B O.language) ↔
      WeakAngluinCondition O.language) :=
  ⟨(theorem_3_15 O).1, (theorem_3_15 O).2.1,
    theorem_4_5_unambiguous O.language (fun i ↦ (O.infinite' i).nonempty),
    (theorem_3_15 O).2.2.1, stable_exhaustive_iff_weak O⟩

/-! ## Section 5. Statistical rates -/

open HallucinationModeCollapse DiscreteIID Support Filter in
/-- Theorem 5.2. Statistical rates for exact breadth under IID sampling. -/
theorem theorem_5_2 (O : OracleFamily) :
    (NontrivialCollection O.language → ∀ G : StatisticalGenerator,
      ∃ i p, ValidDistribution O.language i p ∧ ∃ᶠ n : ℕ in atTop,
        Real.exp (-2 * (n : ℝ)) ≤ breadthError O.language G p i n) ∧
    (IdentifiableInLimit O.language → ∃ G, ExponentialBreadth O.language G) ∧
    (¬IdentifiableInLimit O.language → ∀ G, NoBreadthRate O.language G) :=
  GenLimit.BreadthCharacterizations.theorem_5_2 O

open HallucinationModeCollapse DiscreteIID Support Filter in
/-- Theorem 5.3. Statistical rates for approximate breadth. The last clause
uses exact-breadth error, as printed. -/
theorem theorem_5_3 (O : OracleFamily) :
    (GenerationNontrivial O.language → ∀ G : StatisticalGenerator,
      ∃ i p, ValidDistribution O.language i p ∧ ∃ᶠ n : ℕ in atTop,
        Real.exp (-2 * (n : ℝ)) ≤ approximateBreadthError O.language G p i n) ∧
    (WeakAngluinCondition O.language → ∃ G, AchievesScaledApproximateBreadthRate O.language G
      (fun r => Real.exp (-r))) ∧
    (¬WeakAngluinCondition O.language → ∀ G, NoBreadthRate O.language G) :=
  GenLimit.BreadthCharacterizations.theorem_5_3 O

/-! ## Sections 6 and 7. Diagonal enumeration and oracle generation -/

/-- Corollary 6.1. On one complete presentation, strictly later rounds
witness pairwise distinct proper sublanguages. -/
theorem corollary_6_1 [Countable α] {F : Generic.LanguageFamily α}
    (hi : ∀ i, (F i).Infinite) (hnot : ¬ Angluin.SemanticallyInferrable F)
    {G : SupportAlgorithm α} (hg : IsApproximateBreadthGenerator G F) :
    ∃ (z : ℕ) (s : ℕ → α) (j t : ℕ → ℕ), Generic.Presents s (F z) ∧ Function.Injective (fun n : ℕ ↦ F (j n)) ∧
      StrictMono t ∧ ∀ n, F (j n) ⊂ F z ∧ ApproximateBreadthCorrectAt G (F (j n)) s (t n) :=
  GenLimit.BreadthCharacterizations.corollary_6_1 hi hnot hg

open HallucinationModeCollapse in
/-- Corollary 7.2. One subset-oracle sampler gives all three guarantees. -/
theorem corollary_7_2 (O : OracleFamily) (S : SubsetOracle O.language) :
    let G := lawSupport (criticalSampler O S)
    (Angluin.ConditionTwo O.language → IsExactBreadthGenerator G O.language) ∧
    (WeakAngluinCondition O.language → IsApproximateBreadthGenerator G O.language) ∧
    IsInfiniteCoverageGenerator G O.language :=
  GenLimit.BreadthCharacterizations.corollary_7_2 O S

/-! ## Section 8. Infinite coverage -/

open CharikarPabbaraju in
/-- Theorem 8.7. The co-singleton family has weak tell-tales and precludes
stable infinite coverage under both conventions for repeated samples. -/
theorem theorem_8_7 :
    WeakAngluinCondition coSingletonNatFamily ∧
    (¬ ∃ G, IsStableGenerator G coSingletonNatFamily ∧ IsInfiniteCoverageGenerator G coSingletonNatFamily) ∧
    (¬ ∃ G, IsStableGenerator G coSingletonNatFamily ∧ SampleAllowingInfiniteCoverage G coSingletonNatFamily) :=
  ⟨GenLimit.BreadthCharacterizations.theorem_8_7.1, GenLimit.BreadthCharacterizations.theorem_8_7.2,
    theorem_8_7_sampleAllowing.2⟩

open HallucinationModeCollapse in
/-- Corollary 8.11 for a finite collection. Allowing repetitions gives stable
whole-target sampling and stable infinite coverage. A finite list of language
indices implements the version-space queries for the latter. Both literal
fresh-output clauses are impossible on infinite targets. -/
theorem corollary_8_11 (O : OracleFamily) (hfin : (Set.range O.language).Finite) :
    (let A := finiteVersionSpaceLearner (familyMembership O)
     let G := identifiedRepeatingBreadth O A
     IsWholeTargetGenerator (lawSupport G) O.language ∧ IsStableGenerator (lawSupport G) O.language ∧
       (Computable₂ O.query → HasComputableSampler G)) ∧
    (∀ (m : ℕ) (covers : ∀ i, ∃ j < m, O.language j = O.language i),
      ∃ d, HasClosureDimension (Set.range O.language) d ∧ ∀ i (xs : List ℕ),
        (∀ x ∈ xs, x ∈ O.language i) → d < xs.toFinset.card →
        ∃ U : Set ℕ, U.Infinite ∧ U ⊆ O.language i ∧ ∀ ys : List ℕ,
          (frozenCoverageLaw (finiteVSI O m covers) d (xs ++ ys)).support = U) ∧
    (¬ ∃ G, IsStableGenerator G O.language ∧ IsExactBreadthGenerator G O.language) ∧
    (¬ ∃ G, IsStableGenerator G O.language ∧ IsInfiniteCoverageGenerator G O.language) :=
  ⟨finite_stableWhole_membership O hfin, finite_stableCoverage_membership O,
    no_stable_exactBreadth_for_infinite_family O.language O.infinite',
    no_stable_infiniteCoverage_for_infinite_family O.language O.infinite'⟩

end GenLimit.BreadthCharacterizations.Results
