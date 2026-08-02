import GenLimit.HallucinationDetection.AngluinCondition
import Mathlib.Tactic.NormNum

/-!
# The multiples example

This module formalizes Example 1 of Karbasi--Montasser--Sous--Velegkas.
Positive integers are encoded by their predecessor, so paper language
`L_i = {i, 2i, 3i, ...}` is Lean index `i - 1`.

The two containment calculations in the example are correct.  The sentence
immediately after the example, however, says that Theorem 2.1 and Angluin's
characterization imply that this collection has no hallucination detector.
That sentence is false: the singleton `{i}` is a tell-tale for `L_i`.
Consequently the collection is identifiable and hallucination-detectable.
The declarations below kernel-check both the displayed calculations and this
counterdiagnosis.
-/

namespace GenLimit.HallucinationDetection

open GenLimit.Generic

/-- Example 1's family of positive-integer multiples, using zero-based
predecessor encodings for both language indices and domain elements. -/
def multiplesFamily : GenLimit.Generic.LanguageFamily ℕ :=
  fun i => {x | i + 1 ∣ x + 1}

@[simp] theorem mem_multiplesFamily {i x : ℕ} :
    x ∈ multiplesFamily i ↔ i + 1 ∣ x + 1 :=
  Iff.rfl

/-- Every language in Example 1 is nonempty. -/
theorem multiplesFamily_allNonempty :
    GenLimit.Angluin.AllNonempty multiplesFamily := by
  intro i
  exact ⟨i, by simp [multiplesFamily]⟩

/-- The target's least positive multiple is a one-point Angluin tell-tale. -/
theorem singleton_index_isTellTale (i : ℕ) :
    GenLimit.Angluin.IsTellTale multiplesFamily i {i} := by
  constructor
  · intro x hx
    have hxi : x = i := by simpa using hx
    subst x
    simp [multiplesFamily]
  · intro j hcontains _hsubset x hx
    have hji : j + 1 ∣ i + 1 := by
      have hi : i ∈ (↑({i} : Finset ℕ) : Set ℕ) := by simp
      simpa [multiplesFamily] using hcontains hi
    have hix : i + 1 ∣ x + 1 := by
      simpa [multiplesFamily] using hx
    simpa [multiplesFamily] using dvd_trans hji hix

/-- Contrary to the prose sentence after Example 1, the multiples family
satisfies Angluin's condition. -/
theorem example_1_angluinCondition :
    GenLimit.Angluin.ConditionTwo multiplesFamily := by
  intro i
  exact ⟨{i}, singleton_index_isTellTale i⟩

/-- Paper `L_4` is contained in paper `L_2`. -/
theorem example_1_L4_subset_L2 :
    multiplesFamily 3 ⊆ multiplesFamily 1 := by
  intro x hx
  have h24 : 2 ∣ 4 := by norm_num
  exact dvd_trans h24 hx

/-- Paper `L_3` is not contained in paper `L_2`. -/
theorem example_1_L3_not_subset_L2 :
    ¬multiplesFamily 2 ⊆ multiplesFamily 1 := by
  intro h
  have hthree : 2 ∈ multiplesFamily 2 := by
    norm_num [multiplesFamily]
  have := h hthree
  norm_num [multiplesFamily] at this

/-- Formal counterdiagnosis of the prose claim following Example 1: the
collection has a hallucination detector. -/
theorem example_1_hallucinationDetectable :
    HallucinationDetectable multiplesFamily :=
  (corollary_2_2 multiplesFamily).2
    example_1_angluinCondition

end GenLimit.HallucinationDetection
