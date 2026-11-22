import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import Mathlib.Data.Finset.Lattice.Fold

/-! # Remark 4.2. Identification for the full language and finite initial segments -/
namespace GenLimit.UnionClosedness

open GenLimit.Angluin

def initialSegmentFamily (i : ℕ) : Set ℕ := {x | x ≤ i}

def initialSegmentUnion : ℕ → Set ℕ
  | 0 => Set.univ
  | i + 1 => initialSegmentFamily i

/-- Each component is identifiable. In the union every finite sample from
the full language is also contained in a proper initial segment. -/
theorem remark_4_2 :
    SemanticallyInferrable (fun _ : ℕ ↦ (Set.univ : Set ℕ)) ∧
    SemanticallyInferrable initialSegmentFamily ∧ ¬ SemanticallyInferrable initialSegmentUnion := by
  classical
  refine ⟨(semanticallyInferrable_iff_conditionTwo _).2 (fun _ ↦
    ⟨∅, by simp, fun _ _ _ ↦ Set.Subset.rfl⟩), ?_, ?_⟩
  · apply (semanticallyInferrable_iff_conditionTwo _).2
    intro i
    refine ⟨{i}, ?_, ?_⟩
    · simp [initialSegmentFamily]
    · intro j ht _ x hx
      have hi : i ≤ j := ht (by simp)
      exact hx.trans hi
  · intro h
    obtain ⟨T, _, hmin⟩ := (semanticallyInferrable_iff_conditionTwo _).1 h 0
    let b := T.sup id
    have hsub : (T : Set ℕ) ⊆ initialSegmentUnion (b + 1) :=
      fun x hx ↦ Finset.le_sup (f := id) hx
    have hle : b + 1 ≤ b := hmin (b + 1) hsub (Set.subset_univ _)
      (show b + 1 ∈ initialSegmentUnion 0 from Set.mem_univ _)
    omega

/-- The singleton component needs no observations. The initial-segment
learner guesses the largest observation. For target [0,i], i+1 distinct
observations force that guess to be i on every subsequent prefix. -/
theorem remark_4_2_component_thresholds :
    (∃ M : SemanticIdentifier ℕ, ∀ xs, M xs = 0) ∧
    ∃ M : SemanticIdentifier ℕ, ∀ i s, Generic.StreamIn s (initialSegmentFamily i) →
      ∀ t, (Generic.sample s t).card = i+1 → ∀ u ≥ t, M (textPrefix s u) = i := by
  refine ⟨⟨fun _ ↦ 0,fun _ ↦ rfl⟩,fun xs ↦ xs.toFinset.sup id,?_⟩
  intro i s hs t hcard u hu
  have hsub (n : ℕ) : Generic.sample s n ⊆ Finset.range (i+1) := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := Generic.mem_sample_iff.mp hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hs ⟨j,rfl⟩))
  have hfull : Generic.sample s t = Finset.range (i+1) :=
    Finset.eq_of_subset_of_card_le (hsub t) (by simp [hcard])
  have hi : i ∈ Generic.sample s u := Generic.sample_mono hu (by rw [hfull]; simp)
  change (textPrefix s u).toFinset.sup id = i
  have he : sample s u = Generic.sample s u := by ext; simp [mem_sample_iff, Generic.mem_sample_iff]
  rw [textPrefix_toFinset,he]
  apply le_antisymm
  · apply Finset.sup_le
    intro x hx
    exact Nat.le_of_lt_succ (Finset.mem_range.mp (hsub u hx))
  · exact Finset.le_sup (f := id) hi

end GenLimit.UnionClosedness
