import GenLimit.Paper03_HallucinationAndModeCollapse.FiniteWitnessRates
import GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency

/-!
# Statistical rates from Angluin's stage learner

The explicit Angluin learner has more structure than an arbitrary online
identifier. For each fixed target, finitely many tell-tales and positive
counterexamples to earlier candidates give a finite witness and cutoff.
Consequently Lemma 8.1 yields an exponential upper bound directly. This is a
stronger upper bound than the almost-exponential conclusion needed in P03
Theorem 3.1. The effective version retains an actual computability witness;
the semantic version keeps the tell-tale choice explicit.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic

theorem angluinLearner_finiteWitness
    (C : Generic.LanguageFamily ℕ) (B : ℕ → ℕ → Finset ℕ)
    (hB : GenLimit.Angluin.IsTellTaleApproximation C B) :
    FiniteWitnessIdentifies C (GenLimit.Angluin.semanticLearner C B) := by
  classical
  let T : ℕ → Finset ℕ := fun j => (hB.2 j).choose
  have hT (j : ℕ) : GenLimit.Angluin.IsTellTale C j (T j) := (hB.2 j).choose_spec.1
  let N : ℕ → ℕ := fun j => (hB.2 j).choose_spec.2.choose
  have hstable (j n : ℕ) (hn : N j ≤ n) : B j n = T j :=
    (hB.2 j).choose_spec.2.choose_spec n hn
  intro i
  let bad := (Finset.range (i + 1)).filter (fun j => ¬C i ⊆ C j)
  have hex (j : {j // j ∈ bad}) : ∃ x, x ∈ C i ∧ x ∉ C j.1 :=
    Set.not_subset.mp (Finset.mem_filter.mp j.2).2
  let w := fun j : {j // j ∈ bad} => Classical.choose (hex j)
  let W := T i ∪ bad.attach.image w
  let cutoff := max i ((Finset.range (i + 1)).sup N)
  refine ⟨W, ?_, cutoff, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (hT i).1 hx
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact (Classical.choose_spec (hex j)).1
  · intro xs hn hxs hobs
    have hNi (j : ℕ) (hj : j ≤ i) : N j ≤ xs.length :=
      (Finset.le_sup (f := N) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans
        ((le_max_right _ _).trans hn)
    have hi : GenLimit.Angluin.StageEligible C B xs i := by
      refine ⟨(le_max_left _ _).trans hn, ?_, ?_⟩
      · rw [hstable i xs.length (hNi i le_rfl)]
        intro x hx
        simpa [GenLimit.Angluin.historySample] using hobs x (Finset.mem_union_left _ hx)
      · intro x hx
        exact hxs x (by simpa [GenLimit.Angluin.historySample] using hx)
    let j := GenLimit.Angluin.semanticLearner C B xs
    have hjle : j ≤ i := GenLimit.Angluin.semanticLearner_le_of_eligible hi
    have hj : GenLimit.Angluin.StageEligible C B xs j :=
      GenLimit.Angluin.semanticLearner_eligible ⟨i, hi⟩
    by_cases hsub : C i ⊆ C j
    · apply Set.Subset.antisymm _ hsub
      apply (hT j).2 i _ hsub
      intro x hx
      have hxB : x ∈ B j xs.length := by rw [hstable j xs.length (hNi j hjle)]; exact hx
      exact hxs x (by simpa [GenLimit.Angluin.historySample] using hj.2.1 hxB)
    · have hjbad : j ∈ bad := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjle), hsub⟩
      let b : {j // j ∈ bad} := ⟨j, hjbad⟩
      have hw := Classical.choose_spec (hex b)
      have hwW : w b ∈ W := Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨b, Finset.mem_attach _ _, rfl⟩)
      exact False.elim (hw.2 (hj.2.2 (by
        simpa [GenLimit.Angluin.historySample] using hobs (w b) hwW)))

theorem exponentialIdentifies_of_conditionTwo
    (C : Generic.LanguageFamily ℕ) (hC : GenLimit.Angluin.ConditionTwo C) :
    ∃ A : GenLimit.Learner ℕ ℕ, ExponentialIdentifies C (deterministicIdentifier A) := by
  let B := GenLimit.Angluin.constantTellTaleApproximation C hC
  exact ⟨GenLimit.Angluin.semanticLearner C B,
    lemma_8_1 C _ (angluinLearner_finiteWitness C B
      (GenLimit.Angluin.constantTellTaleApproximation_spec C hC))⟩

/-- When the membership and tell-tale procedures are computable, the same
exponential conclusion has a uniformly computable deterministic learner. -/
theorem computable_exponentialIdentifies_of_conditionOne
    (F : GenLimit.Angluin.EffectiveIndexedFamily) (hF : GenLimit.Angluin.ConditionOne F) :
    ∃ A : GenLimit.Learner ℕ ℕ, Computable A ∧
      ExponentialIdentifies F.language (deterministicIdentifier A) := by
  obtain ⟨emit, hemit, hTell⟩ := hF
  refine ⟨GenLimit.Angluin.effectiveLearner F emit,
    GenLimit.Angluin.effectiveLearner_computable F hemit, ?_⟩
  have heq : GenLimit.Angluin.effectiveLearner F emit =
      GenLimit.Angluin.semanticLearner F.language (GenLimit.Angluin.stageContents emit) := by
    funext xs
    simpa using GenLimit.Angluin.effectiveLearner_eq_semanticLearner F emit xs.length xs.get
  rw [heq]
  exact lemma_8_1 F.language _ (angluinLearner_finiteWitness _ _
    (GenLimit.Angluin.tellTaleApproximation_of_enumeration hTell))

end GenLimit.HallucinationModeCollapse
