import GenLimit.Support.PredicateLock
import GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions
import GenLimit.Paper05_HallucinationsBreadthAndStability.ApproximateBreadth

/-! # The uniqueness and finite non-uniqueness lower bounds -/

namespace GenLimit.BreadthCharacterizations

/-- A trained generator can be folded into the predicate by evaluating it on
the history. The predicate can also depend on the observed sample itself. -/
def EventuallyGeneratesWith (P : List α → Set α → Prop) (F : Generic.LanguageFamily α) : Prop :=
  ∀ i s, Generic.Presents s (F i) → ∃ T, ∀ t ≥ T, P (textPrefix s t) (F i)

private theorem compatible [Countable α] {F : Generic.LanguageFamily α}
    (hne : ∀ i, (F i).Nonempty) {P : List α → Set α → Prop} (hP : EventuallyGeneratesWith P F)
    (i : ℕ) :
    ∃ T : Finset α, (T : Set α) ⊆ F i ∧ ∀ j, (T : Set α) ⊆ F j → F j ⊆ F i →
      ∃ xs, Angluin.ListWithin xs (F j) ∧ P xs (F i) ∧ P xs (F j) := by
  obtain ⟨T, hT, h⟩ := Support.finite_witness_compatible (Set.range F)
    (fun _ ⟨j, e⟩ => e ▸ hne j) P (fun _ ⟨j, e⟩ => e ▸ hP j) (Set.mem_range_self i)
  exact ⟨T, hT, fun j => h _ (Set.mem_range_self j)⟩

/-- Theorem 3.5. A trained generator compatible with at most one target
forces Angluin's finite tell-tale condition. -/
theorem theorem_3_5 [Countable α] {F : Generic.LanguageFamily α}
    (hne : ∀ i, (F i).Nonempty) {P : List α → Set α → Prop}
    (unique : ∀ xs i j, P xs (F i) → P xs (F j) → F i = F j)
    (hP : EventuallyGeneratesWith P F) : Angluin.ConditionTwo F := by
  intro i
  obtain ⟨T, hT, hc⟩ := compatible hne hP i
  refine ⟨T, hT, fun j hj hji => ?_⟩
  obtain ⟨xs, _, hi, hj'⟩ := hc j hj hji
  exact (unique xs i j hi hj').le

/-- Theorem 3.10. It suffices to test the finite non-uniqueness criterion
on nested targets and on histories consistent with the smaller target. -/
theorem theorem_3_10 [Countable α] {F : Generic.LanguageFamily α}
    (hne : ∀ i, (F i).Nonempty) {P : List α → Set α → Prop}
    (finite : ∀ xs i j, Angluin.ListWithin xs (F j) → F j ⊆ F i →
      P xs (F i) → P xs (F j) → (F i \ F j).Finite)
    (hP : EventuallyGeneratesWith P F) : WeakAngluinCondition F := by
  intro i
  obtain ⟨T, hT, hc⟩ := compatible hne hP i
  refine ⟨T, hT, fun j hj hji => ?_⟩
  obtain ⟨xs, hs, hi, hj'⟩ := hc j hj hji.subset
  exact finite xs i j hs hji.subset hi hj'

/-- Both directions of the semantic support formulation of Theorem 3.8. -/
theorem theorem_3_8_semantic [Countable α] {F : Generic.LanguageFamily α}
    (hne : ∀ i, (F i).Nonempty) : ApproximateBreadthGeneratable F ↔ WeakAngluinCondition F := by
  refine ⟨?_, weakAngluin_implies_approximateBreadthGeneratable⟩
  rintro ⟨G, hG⟩
  apply theorem_3_10 hne (P := fun xs K => G xs ⊆ K ∧ (K \ G xs).Finite) _ hG
  intro xs i j _ _ hi hj
  exact hi.2.subset (Set.diff_subset_diff_right hj.1)

end GenLimit.BreadthCharacterizations
