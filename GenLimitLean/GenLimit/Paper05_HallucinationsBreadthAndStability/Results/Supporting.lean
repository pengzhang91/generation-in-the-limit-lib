import GenLimit.Paper05_HallucinationsBreadthAndStability.ConsistentExhaustive
import GenLimit.Paper05_HallucinationsBreadthAndStability.HallucinationTables
import GenLimit.Paper05_HallucinationsBreadthAndStability.FrozenCoverage
import GenLimit.Paper00A_PositiveDataInference.Effective.Necessity

/-! # P05 supporting results

Section 7 constructions, propositions, examples, figure and appendix results,
and the literal finite-family counterexample used to interpret Corollary 8.11.
-/

namespace GenLimit.BreadthCharacterizations.Results

open GenLimit.Generic

alias figures_3_4_finite_hallucinations := GenLimit.BreadthCharacterizations.figures_3_4_finite_hallucinations
alias figures_3_4_unrestricted := GenLimit.BreadthCharacterizations.figures_3_4_unrestricted
alias figures_3_4_literal_infinite_errors_counterexample := GenLimit.BreadthCharacterizations.infinite_errors_impossible_on_full_target
alias figure_3_infinite_present := GenLimit.BreadthCharacterizations.figure_3_infinite_present

open HallucinationModeCollapse in
/-- Finite oracle access during training (Sections 7.1–7.2). At history `xs`,
two answer functions agreeing on the program's query list select the same
language index. In Lemma 7.1 the list contains membership and subset queries.
In Lemma 7.3 it contains membership queries and stages of tell-tale enumeration. -/
theorem finite_query_training (xs : List ℕ) (q₁ q₂ : ℕ → ℕ) :
    ((∀ k ∈ subsetIdentificationQueries xs, q₁ k = q₂ k) →
      subsetIdentificationProgram.run q₁ xs = subsetIdentificationProgram.run q₂ xs) ∧
    ((∀ k ∈ identificationQueries xs, q₁ k = q₂ k) →
      identificationProgram.run q₁ xs = identificationProgram.run q₂ xs) := by
  have agree (P : Support.TruthTableProgram) (h : ∀ k ∈ P.queries xs, q₁ k = q₂ k) :
      P.run q₁ xs = P.run q₂ xs := by
    exact congrArg (fun answers ↦ P.output (xs, answers)) (List.map_congr_left h)
  exact ⟨agree subsetIdentificationProgram, agree identificationProgram⟩

/-- Membership and subset queries give the function used in Theorem 3.8. -/
alias lemma_7_1 := GenLimit.BreadthCharacterizations.lemma_7_1
/-- Sampling and support decisions for the subset-oracle construction. -/
alias corollary_7_2_oracles := GenLimit.BreadthCharacterizations.criticalSampler_oracles
/-- Membership and weak tell-tale enumeration give the algorithm used in Theorem 3.8. -/
alias lemma_7_3 := GenLimit.BreadthCharacterizations.lemma_7_3
/-- For Theorem 4.3, membership, subset and nested finite-difference queries
give exhaustive generation with an eventually valid, fresh range. -/
alias lemma_7_5 := GenLimit.BreadthCharacterizations.lemma_7_5
/-- For Theorem 4.3, membership and weak tell-tale enumeration give an
exhaustive enumerator, computable when both inputs are computable. -/
alias lemma_7_7 := GenLimit.BreadthCharacterizations.lemma_7_7

/-- Membership queries suffice for infinite fresh coverage on encoded words. -/
alias proposition_8_4 := GenLimit.BreadthCharacterizations.proposition_8_4

theorem example_8_6 :
    WeakAngluinCondition CharikarPabbaraju.coSingletonNatFamily ∧
      ¬ Angluin.ConditionTwo CharikarPabbaraju.coSingletonNatFamily :=
  ⟨GenLimit.BreadthCharacterizations.theorem_8_7.1, theorem_4_5_stable_exhaustive_counterexample.2⟩

/-- The same literal support/stability conflict applies to Proposition 8.10
and Corollary 8.11(2), independently of their additional closure-dimension
and oracle assumptions. -/
theorem proposition_8_10_literal_specification_inconsistent
    [Countable α]
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    ¬∃ G : SupportAlgorithm α,
      IsStableGenerator G F ∧ IsInfiniteCoverageGenerator G F :=
  no_stable_infiniteCoverage_for_infinite_family F hInfinite

/-- A version-space-intersection membership oracle and the closure dimension
give stable sample-allowing coverage after enough distinct observations. -/
alias proposition_8_10_sampleAllowing := GenLimit.BreadthCharacterizations.proposition_8_10_sampleAllowing

/-- Both literal conclusions of Corollary 8.11 already fail on the single
language ℕ. A constant indexing exhibits a finite collection of infinite languages. -/
theorem corollary_8_11_literal_counterexample :
    let F : Generic.LanguageFamily ℕ := fun _ ↦ Set.univ
    (Set.range F).Finite ∧ (∀ i, (F i).Infinite) ∧
    (¬ ∃ G, IsStableGenerator G F ∧ IsExactBreadthGenerator G F) ∧
    (¬ ∃ G, IsStableGenerator G F ∧ IsInfiniteCoverageGenerator G F) := by
  dsimp only
  exact ⟨by simp, fun _ ↦ Set.infinite_univ, no_stable_exactBreadth_for_infinite_family _ (fun _ ↦ Set.infinite_univ),
    no_stable_infiniteCoverage_for_infinite_family _ (fun _ ↦ Set.infinite_univ)⟩

alias example_8_12 := GenLimit.BreadthCharacterizations.example_8_12
alias example_8_12_printed_support_fails := GenLimit.BreadthCharacterizations.example_8_12_printed_support_fails
alias proposition_8_14_sampleAllowing := GenLimit.BreadthCharacterizations.proposition_8_14_sampleAllowing
alias proposition_8_14_literal_incompatible := GenLimit.BreadthCharacterizations.increasing_literal_incompatible
alias increasing_approximate_requires_conditionTwo := GenLimit.BreadthCharacterizations.increasing_approximate_requires_conditionTwo

/-! ## Appendix observations and the cited Angluin characterization -/

theorem observation_A_1 {F : Generic.LanguageFamily α} {U : Set α} {i j : ℕ}
    (hi : UnambiguousFor F U (F i)) (hj : UnambiguousFor F U (F j)) : F i = F j := by
  by_contra h
  exact lt_asymm (hi j (Ne.symm h)) (hj i h)

open scoped symmDiff in
/-- In Equation (2), E consists of the observations and previous first outputs.
The observation works for any finite E shared by the two target tests. -/
theorem observation_A_2 {E R K L : Set α} (hE : E.Finite)
    (hK : (R \ K).Finite ∧ K ⊆ E ∪ R) (hL : (R \ L).Finite ∧ L ⊆ E ∪ R) :
    (K ∆ L).Finite := by
  have one {U V : Set α} (hu : U ⊆ E ∪ R) (hv : (R \ V).Finite) : (U \ V).Finite := by
    apply (hE.union hv).subset
    intro x hx
    exact (hu hx.1).elim Or.inl (fun hr ↦ Or.inr ⟨hr,hx.2⟩)
  rw [Set.symmDiff_def]
  exact (one hK.2 hL.1).union (one hL.2 hK.1)

/-- Appendix B.2, identification given membership and enumerated tell-tales. -/
theorem theorem_B_2_oracle {F : Generic.LanguageFamily ℕ} (O : MembershipOracle F)
    (emit : ℕ → ℕ → Option ℕ) (h : ∀ i, Angluin.IsEnumeratedTellTale F i (Angluin.enumeratedSet emit i)) :
    Angluin.SemanticallyIdentifies
      (HallucinationModeCollapse.identificationProgram.run (HallucinationModeCollapse.identificationOracle O emit)) F := by
  rw [HallucinationModeCollapse.identificationProgram_eq_angluin]
  exact Angluin.semanticLearner_semanticallyIdentifies (Angluin.tellTaleApproximation_of_enumeration h)

/-- Appendix B.2 on uniformly decidable indexed families, including effective necessity. -/
alias theorem_B_2_effective := GenLimit.Angluin.theoremOne

end GenLimit.BreadthCharacterizations.Results
