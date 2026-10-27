import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalModel
import GenLimit.Support.FullSupportDistribution

/-!
# An exponential identification lower bound

Lemma 5.1 of arXiv:2411.09642v3, for every semantic randomized learner.
Two distinct targets share one point. Each admits a full-support distribution
putting at least half its mass there. On the all-common-point sample the
learner has conditional error at least one half for one of the targets.
An infinite pigeonhole argument fixes one target and distribution.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.DiscreteIID Filter

theorem twoTarget_conditional_error (C : Generic.LanguageFamily ℕ) (A : StatisticalIdentifier)
    (i j : ℕ) (hij : C i ≠ C j) (xs : List ℕ) :
    (1 / 2 : ℝ) ≤ probability (A xs) {k | C k ≠ C i} ∨
      (1 / 2 : ℝ) ≤ probability (A xs) {k | C k ≠ C j} := by
  have heq : {k | C k ≠ C i} ∪ {k | C k ≠ C j} = Set.univ := by
    ext k
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_contra! h
    exact hij (h.1.symm.trans h.2)
  have h := probability_union_le (A xs) {k | C k ≠ C i} {k | C k ≠ C j}
  rw [heq] at h
  have hu : probability (A xs) Set.univ = 1 := by
    unfold probability
    rw [PMF.toOuterMeasure_apply]
    simp
  rw [hu] at h
  by_contra! hnot
  linarith

theorem identificationError_heavyAtom (C : Generic.LanguageFamily ℕ) (A : StatisticalIdentifier)
    (p : PMF ℕ) (i x n : ℕ) (hp : (1 / 2 : ℝ) ≤ (p x).toReal)
    (hA : (1 / 2 : ℝ) ≤ probability (A (List.replicate n x)) {k | C k ≠ C i}) :
    (1 / 2 : ℝ) ^ (n + 1) ≤ identificationError C A p i n := by
  have hmass : (1 / 2 : ℝ) ^ n ≤ (samples p n (List.replicate n x)).toReal := by
    rw [samples_replicate, ENNReal.toReal_pow]
    exact pow_le_pow_left₀ (by norm_num) hp n
  calc
    _ = (1 / 2 : ℝ) ^ n * (1 / 2) := pow_succ _ _
    _ ≤ (samples p n (List.replicate n x)).toReal *
        probability (A (List.replicate n x)) {k | C k ≠ C i} :=
      mul_le_mul hmass hA (by norm_num) ENNReal.toReal_nonneg
    _ ≤ _ := probability_bind_ge (samples p n) A {k | C k ≠ C i} (List.replicate n x)

theorem exp_neg_two_le_half_pow (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-2 * (n : ℝ)) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  have he : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    have h := Real.add_one_le_exp 1
    have hm : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1)]
  calc
    _ = Real.exp (-1) ^ (2 * n) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    _ ≤ (1 / 2 : ℝ) ^ (2 * n) := pow_le_pow_left₀ (Real.exp_nonneg _) he _
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      omega

/-- Lemma 5.1: one fixed valid distribution witnesses the exponential lower
bound infinitely often. Randomized kernels include deterministic learners. -/
theorem lemma_5_1 (C : Generic.LanguageFamily ℕ) (hC : NontrivialCollection C)
    (A : StatisticalIdentifier) :
    ∃ i p, ValidDistribution C i p ∧
      ∃ᶠ n : ℕ in atTop, Real.exp (-2 * (n : ℝ)) ≤ identificationError C A p i n := by
  obtain ⟨i, j, x, hij, hxi, hxj⟩ := hC
  obtain ⟨p, hp, hpx⟩ := exists_fullSupport_heavyAtom (C i) x hxi
  obtain ⟨q, hq, hqx⟩ := exists_fullSupport_heavyAtom (C j) x hxj
  have hf : ∃ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ^ (n + 1) ≤ identificationError C A p i n ∨
      (1 / 2 : ℝ) ^ (n + 1) ≤ identificationError C A q j n := by
    apply Frequently.of_forall
    intro n
    rcases twoTarget_conditional_error C A i j hij (List.replicate n x) with hi | hj
    · exact Or.inl (identificationError_heavyAtom C A p i x n hpx hi)
    · exact Or.inr (identificationError_heavyAtom C A q j x n hqx hj)
  rcases frequently_or_distrib.mp hf with hi | hj
  · refine ⟨i, p, hp, ?_⟩
    exact (hi.and_eventually (eventually_atTop.mpr ⟨1, fun _ h => h⟩)).mono
      (fun n h => (exp_neg_two_le_half_pow n h.2).trans h.1)
  · refine ⟨j, q, hq, ?_⟩
    exact (hj.and_eventually (eventually_atTop.mpr ⟨1, fun _ h => h⟩)).mono
      (fun n h => (exp_neg_two_le_half_pow n h.2).trans h.1)

end GenLimit.HallucinationModeCollapse
