import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Paper05_HallucinationsBreadthAndStability.Definitions

/-!
# Exact breadth

This file proves the semantic form of Theorem 3.3 in
Kalavasis--Mehrotra--Velegkas, arXiv:2412.18530v2. Literal fresh-output
breadth is first related to whole-target support by explicitly removing or
restoring the observed sample. The characterization then reuses the
canonical Angluin semantic theorem rather than duplicating its tell-tale
construction.

No effectiveness or membership-oracle claim is made here.
-/

namespace GenLimit.BreadthCharacterizations

open GenLimit.Generic

@[simp] theorem historySet_textPrefix
    (stream : Generic.Stream α) (t : ℕ) :
    historySet (GenLimit.textPrefix stream t) =
      (↑(Generic.sample stream t) : Set α) := by
  classical
  ext x
  simp [historySet, GenLimit.mem_textPrefix_iff,
    Generic.mem_sample_iff]

@[simp] theorem supportAt_removeObserved
    (G : SupportAlgorithm α) (stream : Generic.Stream α) (t : ℕ) :
    supportAt (removeObserved G) stream t =
      supportAt G stream t \ (↑(Generic.sample stream t) : Set α) := by
  classical
  simp [supportAt, removeObserved]

@[simp] theorem supportAt_restoreObserved
    (G : SupportAlgorithm α) (stream : Generic.Stream α) (t : ℕ) :
    supportAt (restoreObserved G) stream t =
      supportAt G stream t ∪ (↑(Generic.sample stream t) : Set α) := by
  classical
  simp [supportAt, restoreObserved]

/-! ## Elementary implications and convention changes -/

/-- Literal exact breadth includes ordinary generation correctness. -/
theorem exactBreadthCorrectAt_implies_generation
    {G : SupportAlgorithm α} {K : Generic.Language α}
    {stream : Generic.Stream α} {t : ℕ}
    (h : ExactBreadthCorrectAt G K stream t) :
    GeneratesInLimitCorrectAt G K stream t := by
  rw [GeneratesInLimitCorrectAt, h]

/-- Literal exact breadth implies approximate breadth at the same stage. -/
theorem exactBreadthCorrectAt_implies_approximate
    {G : SupportAlgorithm α} {K : Generic.Language α}
    {stream : Generic.Stream α} {t : ℕ}
    (h : ExactBreadthCorrectAt G K stream t) :
    ApproximateBreadthCorrectAt G K stream t := by
  classical
  rw [ApproximateBreadthCorrectAt, h]
  constructor
  · exact Set.diff_subset
  · apply (Generic.sample stream t).finite_toSet.subset
    intro x hx
    by_contra hxSample
    exact hx.2 ⟨hx.1, hxSample⟩

theorem exactBreadth_implies_limitGeneration
    {G : SupportAlgorithm α} {F : Generic.LanguageFamily α}
    (hG : IsExactBreadthGenerator G F) :
    IsLimitGenerator G F := by
  intro z stream hP
  obtain ⟨T, hT⟩ := hG z stream hP
  exact ⟨T, fun t ht => exactBreadthCorrectAt_implies_generation (hT t ht)⟩

theorem exactBreadth_implies_approximateBreadth
    {G : SupportAlgorithm α} {F : Generic.LanguageFamily α}
    (hG : IsExactBreadthGenerator G F) :
    IsApproximateBreadthGenerator G F := by
  intro z stream hP
  obtain ⟨T, hT⟩ := hG z stream hP
  exact ⟨T, fun t ht => exactBreadthCorrectAt_implies_approximate (hT t ht)⟩

/-- Removing the observed sample converts whole-target support into literal
Definition 3.1. -/
theorem removeObserved_exact_of_whole
    {G : SupportAlgorithm α} {K : Generic.Language α}
    {stream : Generic.Stream α} {t : ℕ}
    (h : WholeTargetCorrectAt G K stream t) :
    ExactBreadthCorrectAt (removeObserved G) K stream t := by
  rw [ExactBreadthCorrectAt, supportAt_removeObserved, h]

/-- Restoring the observed sample converts literal Definition 3.1 into
whole-target support on a genuine target presentation. -/
theorem restoreObserved_whole_of_exact
    {G : SupportAlgorithm α} {K : Generic.Language α}
    {stream : Generic.Stream α} {t : ℕ}
    (hP : Generic.Presents stream K)
    (h : ExactBreadthCorrectAt G K stream t) :
    WholeTargetCorrectAt (restoreObserved G) K stream t := by
  classical
  rw [WholeTargetCorrectAt, supportAt_restoreObserved, h]
  apply Set.diff_union_of_subset
  intro x hx
  exact Generic.mem_language_of_mem_sample_of_presents hP hx

theorem wholeTarget_implies_literalExact
    {G : SupportAlgorithm α} {F : Generic.LanguageFamily α}
    (hG : IsWholeTargetGenerator G F) :
    IsExactBreadthGenerator (removeObserved G) F := by
  intro z stream hP
  obtain ⟨T, hT⟩ := hG z stream hP
  exact ⟨T, fun t ht => removeObserved_exact_of_whole (hT t ht)⟩

theorem literalExact_implies_wholeTarget
    {G : SupportAlgorithm α} {F : Generic.LanguageFamily α}
    (hG : IsExactBreadthGenerator G F) :
    IsWholeTargetGenerator (restoreObserved G) F := by
  intro z stream hP
  obtain ⟨T, hT⟩ := hG z stream hP
  exact ⟨T, fun t ht => restoreObserved_whole_of_exact hP (hT t ht)⟩

theorem literalExactGeneratable_iff_wholeTargetGeneratable
    (F : Generic.LanguageFamily α) :
    ExactBreadthGeneratable F ↔ WholeTargetGeneratable F := by
  constructor
  · rintro ⟨G, hG⟩
    exact ⟨restoreObserved G, literalExact_implies_wholeTarget hG⟩
  · rintro ⟨G, hG⟩
    exact ⟨removeObserved G, wholeTarget_implies_literalExact hG⟩

/-! ## Exact breadth implies semantic identification -/

/-- The least family index denoting the target language at index `z`. -/
noncomputable def leastTargetIndex
    (F : Generic.LanguageFamily α) (z : ℕ) : ℕ := by
  classical
  exact Nat.find (⟨z, rfl⟩ : ∃ i, F z = F i)

theorem leastTargetIndex_spec
    (F : Generic.LanguageFamily α) (z : ℕ) :
    F (leastTargetIndex F z) = F z := by
  classical
  exact (Nat.find_spec (⟨z, rfl⟩ : ∃ i, F z = F i)).symm

/-- On a finite history, conjecture the least family index denoting the
current whole-target support. -/
noncomputable def wholeTargetIdentifier
    (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) :
    GenLimit.Angluin.SemanticIdentifier α := by
  classical
  exact fun history =>
    if h : ∃ i, G history = F i then Nat.find h else 0

theorem wholeTargetIdentifier_eq_leastTarget
    (G : SupportAlgorithm α) (F : Generic.LanguageFamily α)
    (stream : Generic.Stream α) (z t : ℕ)
    (hWhole : WholeTargetCorrectAt G (F z) stream t) :
    wholeTargetIdentifier G F (GenLimit.textPrefix stream t) =
      leastTargetIndex F z := by
  classical
  have hsupport : G (GenLimit.textPrefix stream t) = F z := by
    simpa [WholeTargetCorrectAt, supportAt] using hWhole
  let hex : ∃ i, G (GenLimit.textPrefix stream t) = F i := ⟨z, hsupport⟩
  have hfind : Nat.find hex = leastTargetIndex F z := by
    have hle₁ : Nat.find hex ≤ leastTargetIndex F z :=
      Nat.find_min' hex
        (hsupport.trans (leastTargetIndex_spec F z).symm)
    have hfound : F z = F (Nat.find hex) :=
      hsupport.symm.trans (Nat.find_spec hex)
    have hle₂ : leastTargetIndex F z ≤ Nat.find hex := by
      unfold leastTargetIndex
      exact Nat.find_min' (⟨z, rfl⟩ : ∃ i, F z = F i) hfound
    exact Nat.le_antisymm hle₁ hle₂
  rw [wholeTargetIdentifier, dif_pos hex]
  exact hfind

/-- Eventual whole-target support induces semantic positive-data
identification, with syntactic convergence to a fixed least index. -/
theorem wholeTargetGenerator_semanticallyIdentifies
    {G : SupportAlgorithm α} {F : Generic.LanguageFamily α}
    (hG : IsWholeTargetGenerator G F) :
    GenLimit.Angluin.SemanticallyIdentifies
      (wholeTargetIdentifier G F) F := by
  intro z stream hP
  obtain ⟨T, hT⟩ := hG z stream hP
  refine ⟨leastTargetIndex F z, leastTargetIndex_spec F z, T, ?_⟩
  intro t ht
  exact wholeTargetIdentifier_eq_leastTarget G F stream z t (hT t ht)

theorem literalExact_implies_semanticallyInferrable
    {F : Generic.LanguageFamily α}
    (h : ExactBreadthGeneratable F) :
    GenLimit.Angluin.SemanticallyInferrable F := by
  obtain ⟨G, hG⟩ := h
  exact ⟨wholeTargetIdentifier (restoreObserved G) F,
    wholeTargetGenerator_semanticallyIdentifies
      (literalExact_implies_wholeTarget hG)⟩

theorem literalExact_implies_conditionTwo
    [Nonempty α] [Countable α]
    {F : Generic.LanguageFamily α}
    (h : ExactBreadthGeneratable F) :
    GenLimit.Angluin.ConditionTwo F :=
  GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable F
    (literalExact_implies_semanticallyInferrable h)

/-! ## Angluin's condition implies exact breadth -/

/-- Literal exact-breadth support obtained from the canonical Angluin
semantic learner by removing the observed history. -/
noncomputable def exactBreadthFromConditionTwo
    {F : Generic.LanguageFamily α}
    (h : GenLimit.Angluin.ConditionTwo F) :
    SupportAlgorithm α :=
  fun history =>
    F (GenLimit.Angluin.semanticLearner F
      (GenLimit.Angluin.constantTellTaleApproximation F h) history) \
        historySet history

theorem conditionTwo_implies_literalExact
    {F : Generic.LanguageFamily α}
    (h : GenLimit.Angluin.ConditionTwo F) :
    IsExactBreadthGenerator (exactBreadthFromConditionTwo h) F := by
  classical
  have hA : GenLimit.Angluin.IsTellTaleApproximation F
      (GenLimit.Angluin.constantTellTaleApproximation F h) :=
    GenLimit.Angluin.constantTellTaleApproximation_spec F h
  have hIdentify :=
    GenLimit.Angluin.semanticLearner_semanticallyIdentifies hA
  intro z stream hP
  obtain ⟨j, hj, T, hT⟩ := hIdentify z stream hP
  refine ⟨T, ?_⟩
  intro t ht
  have hout :
      GenLimit.Angluin.semanticLearner F
          (GenLimit.Angluin.constantTellTaleApproximation F h)
          (GenLimit.textPrefix stream t) = j := by
    simpa only using hT t ht
  rw [ExactBreadthCorrectAt, supportAt, exactBreadthFromConditionTwo,
    hout, hj, historySet_textPrefix]

theorem conditionTwo_implies_literalExactGeneratable
    {F : Generic.LanguageFamily α}
    (h : GenLimit.Angluin.ConditionTwo F) :
    ExactBreadthGeneratable F :=
  ⟨exactBreadthFromConditionTwo h, conditionTwo_implies_literalExact h⟩

/-- Semantic form of source Theorem 3.3. -/
theorem exactBreadthGeneratable_iff_conditionTwo
    [Nonempty α] [Countable α]
    (F : Generic.LanguageFamily α) :
    ExactBreadthGeneratable F ↔ GenLimit.Angluin.ConditionTwo F := by
  constructor
  · exact literalExact_implies_conditionTwo
  · exact conditionTwo_implies_literalExactGeneratable

end GenLimit.BreadthCharacterizations
