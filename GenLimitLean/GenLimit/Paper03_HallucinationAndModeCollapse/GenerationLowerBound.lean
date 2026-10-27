import GenLimit.Paper03_HallucinationAndModeCollapse.GenerationModel
import GenLimit.Support.DiscreteSampleAtoms
import GenLimit.Support.FullSupportDistribution
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Lemma 5.10: the generation exponential lower bound

A hard sample covers the finite intersection of a finite subfamily. Every
output is then wrong for at least one target: an output inside the intersection
is repeated, and an output outside it misses some target. A finite pigeonhole
argument fixes one target infinitely often. Only afterwards do we choose a
full-support distribution for that target and lower-bound these sample atoms.
Unlike the printed proof, common atom masses across the targets are unnecessary.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.DiscreteIID Filter

private theorem finite_frequently_choice (I : Finset ℕ) (P : ℕ → ℕ → Prop)
    (h : ∃ᶠ n : ℕ in atTop, ∃ i ∈ I, P i n) :
    ∃ i ∈ I, ∃ᶠ n : ℕ in atTop, P i n := by
  classical
  induction I using Finset.induction_on with
  | empty => simp at h
  | @insert i I hi ih =>
    have hh : ∃ᶠ n : ℕ in atTop, P i n ∨ ∃ j ∈ I, P j n := by
      simpa only [Finset.mem_insert, exists_eq_or_imp] using h
    rcases frequently_or_distrib.mp hh with hf | hf
    · exact ⟨i, Finset.mem_insert_self _ _, hf⟩
    · obtain ⟨j, hj, hf⟩ := ih hf
      exact ⟨j, Finset.mem_insert_of_mem hj, hf⟩

theorem generation_conditional_error (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (I : Finset ℕ) (hI : I.Nonempty) (xs : List ℕ)
    (hcover : ∀ x, (∀ i ∈ I, x ∈ C i) → x ∈ xs) :
    ∃ i ∈ I, (1 / (I.card : ℝ)) ≤ probability (G xs) {y | y ∉ C i ∨ y ∈ xs} := by
  classical
  have heq : (⋃ i ∈ I, {y | y ∉ C i ∨ y ∈ xs}) = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases hy : y ∈ xs
    · obtain ⟨i, hi⟩ := hI
      exact ⟨i, hi, Or.inr hy⟩
    · have hn : ¬∀ i ∈ I, y ∈ C i := fun h => hy (hcover y h)
      push_neg at hn
      obtain ⟨i, hi, hnot⟩ := hn
      exact ⟨i, hi, Or.inl hnot⟩
  have hsum := probability_biUnion_le (G xs) I (fun i => {y | y ∉ C i ∨ y ∈ xs})
  rw [heq, probability_univ] at hsum
  have hk : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
  by_contra! hnot
  have hs : (∑ i ∈ I, probability (G xs) {y | y ∉ C i ∨ y ∈ xs}) <
      ∑ _i ∈ I, (1 / (I.card : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty hI hnot
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have he : (I.card : ℝ) * (1 / (I.card : ℝ)) = 1 := by field_simp
  linarith

/-- Lemma 5.10, allowing arbitrary randomized generators. The target and
distribution are fixed before the infinitely many sample sizes. -/
theorem lemma_5_10 (C : Generic.LanguageFamily ℕ) (hC : GenerationNontrivial C)
    (G : StatisticalGenerator) :
    ∃ i p, ValidDistribution C i p ∧
      ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
        ∃ᶠ n : ℕ in atTop, D * Real.exp (-c * n) ≤ generationError C G p i n := by
  classical
  obtain ⟨I, hI, ⟨x₀, hx₀⟩, hfin⟩ := hC
  let T := hfin.toFinset
  have hxT : x₀ ∈ T := by simpa [T] using hx₀
  let hard := fun n => T.toList ++ List.replicate (n - T.card) x₀
  have hcover (n : ℕ) : ∀ x, (∀ i ∈ I, x ∈ C i) → x ∈ hard n := by
    intro x hx
    exact List.mem_append_left _ (by simpa [T] using hx)
  have hf : ∃ᶠ n : ℕ in atTop,
      ∃ i ∈ I, (1 / (I.card : ℝ)) ≤ probability (G (hard n)) {y | y ∉ C i ∨ y ∈ hard n} :=
    Frequently.of_forall fun n => generation_conditional_error C G I hI (hard n) (hcover n)
  obtain ⟨i, hi, hf⟩ := finite_frequently_choice I _ hf
  obtain ⟨p, hp, _⟩ := exists_fullSupport_heavyAtom (C i) x₀ (hx₀ i hi)
  obtain ⟨d, hd, hmass⟩ := finite_mass_lower_bound p T (by
    intro x hx
    change x ∈ p.support
    rw [hp]
    exact (hfin.mem_toFinset.mp hx) i hi)
  let δ := min d (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min hd (by norm_num)
  have hδone : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hc : 0 < -Real.log δ := neg_pos.mpr (Real.log_neg hδ hδone)
  have hk : 0 < (1 / (I.card : ℝ)) := one_div_pos.mpr (by exact_mod_cast hI.card_pos)
  refine ⟨i, p, hp, -Real.log δ, hc, 1 / (I.card : ℝ), hk, ?_⟩
  apply (hf.and_eventually (eventually_ge_atTop T.card)).mono
  rintro n ⟨herr, hn⟩
  have hlen : (hard n).length = n := by simp [hard]; omega
  have hmem (x : ℕ) (hx : x ∈ hard n) : x ∈ T := by
    rcases List.mem_append.mp hx with hx | hx
    · exact Finset.mem_toList.mp hx
    · have he : x = x₀ := (List.mem_replicate.mp hx).2
      exact he ▸ hxT
  have hatom : δ ^ n ≤ (samples p n (hard n)).toReal := by
    simpa only [hlen] using samples_atom_lower_bound p (hard n) δ hδ.le
      (fun x hx => (min_le_left _ _).trans (hmass x (hmem x hx)))
  have hexp : Real.exp (-(-Real.log δ) * (n : ℝ)) = δ ^ n := by
    rw [neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hδ]
  rw [hexp]
  calc
    _ ≤ (samples p n (hard n)).toReal *
        probability (G (hard n)) {y | y ∉ C i ∨ y ∈ hard n} := by
      rw [mul_comm (1 / (I.card : ℝ))]
      exact mul_le_mul hatom herr hk.le ENNReal.toReal_nonneg
    _ ≤ _ := generationError_ge_atom C G p i n (hard n)

end GenLimit.HallucinationModeCollapse
