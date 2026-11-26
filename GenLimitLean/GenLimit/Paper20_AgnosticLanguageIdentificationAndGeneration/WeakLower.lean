import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Model
import GenLimit.Paper03_HallucinationAndModeCollapse.IdentificationLowerBound

/-! # Exponential lower bound for weak identification (Theorem 2.2) -/
namespace GenLimit.AgnosticLanguage
open Generic DiscreteIID Filter
open scoped Classical ENNReal
noncomputable section

theorem idErr_ge_gap (C : Generic.LanguageFamily α) (p : PMF α) (A : Identifier α) (n : ℕ)
    (E : Set ℕ) (δ : ℝ) (h : ∀ j ∈ E, δ ≤ risk p (C j) - optimalRisk C p) :
    δ * probability ((samples p n).bind A) E ≤ idErr C A p n := by
  rw [prob_event_tsum, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ _ (weighted_summable _ (excess_unit C p))
  · intro j
    by_cases hj : j ∈ E
    · simp only [if_pos hj,mul_one,mul_comm δ]
      exact mul_le_mul_of_nonneg_left (h j hj) ENNReal.toReal_nonneg
    · simp only [if_neg hj,mul_zero]
      exact mul_nonneg ENNReal.toReal_nonneg (excess_unit ..).1
  · exact (weighted_summable _ (v := fun j ↦ if j ∈ E then 1 else 0) (fun j ↦ by by_cases hj : j ∈ E <;> simp [hj,Set.mem_Icc])).mul_left δ

private def biased (x y : α) := (PMF.bernoulli (3/4 : NNReal) (by norm_num1; exact (div_le_one (by norm_num)).mpr (by norm_num))).map (fun b ↦ if b then x else y)

private theorem biased_event (x y : α) (E : Set α) :
    probability (biased x y) E = (if x ∈ E then 3/4 else 0) + (if y ∈ E then 1/4 else 0) := by
  unfold biased probability
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply, tsum_bool]
  have hf : (3/4 : ENNReal) ≤ 1 := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]; norm_num
  have hsub : (1 - 3/4 : ENNReal).toReal = 1/4 := by
    rw [ENNReal.toReal_sub_of_le hf ENNReal.one_ne_top]; norm_num
  have hn : (1 - 3/4 : ENNReal) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hn' : (3/4 : ENNReal) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hf
  by_cases hx : x ∈ E <;> by_cases hy : y ∈ E <;>
    simp [Set.indicator, Set.preimage, hx, hy, PMF.bernoulli_apply,
      ENNReal.toReal_add hn hn', hsub]
  exact add_comm _ _

private theorem biased_risk (C : Generic.LanguageFamily α) (i j : ℕ) (x y : α)
    (hij : C i ≠ C j) (hx : ∀ k, x ∈ C k ↔ C k = C i)
    (hy : ∀ k, y ∈ C k ↔ C k = C j) :
    Optimal C (biased x y) i ∧ ∀ k, C k ≠ C i →
      (1/2 : ℝ) ≤ risk (biased x y) (C k) - optimalRisk C (biased x y) := by
  have he (k) : risk (biased x y) (C k) =
      (if C k ≠ C i then 3/4 else 0) + (if C k ≠ C j then 1/4 else 0) := by
    rw [risk, biased_event]; simp only [Set.mem_compl_iff,hx,hy]
  have hi : risk (biased x y) (C i) = 1/4 := by simp [he,hij]
  have hn (k) (hk : C k ≠ C i) : 3/4 ≤ risk (biased x y) (C k) := by
    rw [he, if_pos hk]; split <;> norm_num
  have ho : Optimal C (biased x y) i := (optimal_iff ..).mpr fun k ↦ by
    by_cases hk : C k = C i
    · rw [hk]
    · linarith [hn k hk, hi]
  refine ⟨ho,fun k hk ↦ ?_⟩
  rw [← show risk (biased x y) (C i) = _ from ho,hi]
  linarith [hn k hk]

private theorem biased_atom (x y : α) (hxy : x ≠ y) :
    (1/4 : ℝ) ≤ ((biased x y) x).toReal ∧ (1/4 : ℝ) ≤ ((biased y x) x).toReal := by
  have h (a b : α) : ((biased a b) x).toReal = probability (biased a b) {x} := by
    simp [probability, PMF.toOuterMeasure_apply_singleton]
  rw [h,h,biased_event,biased_event]
  simp [hxy.symm]; norm_num

private theorem heavy_conditional (C : Generic.LanguageFamily α) (A : Identifier α)
    (p : PMF α) (i : ℕ) (x : α) (n : ℕ) (hn : 1 ≤ n)
    (hm : (1/4 : ℝ) ≤ (p x).toReal) (hgap : ∀ k, C k ≠ C i →
      (1/2 : ℝ) ≤ risk p (C k) - optimalRisk C p)
    (hA : (1/2 : ℝ) ≤ probability (A (List.replicate n x)) {k | C k ≠ C i}) :
    Real.exp (-5 * (n:ℝ)) ≤ idErr C A p n := by
  have hmass : (1/4 : ℝ)^n ≤ ((samples p n) (List.replicate n x)).toReal := by
    rw [samples_replicate, ENNReal.toReal_pow]; exact pow_le_pow_left₀ (by norm_num) hm n
  have hprob := (mul_le_mul hmass hA (by norm_num) ENNReal.toReal_nonneg).trans
    (probability_bind_ge (samples p n) A {k | C k ≠ C i} (List.replicate n x))
  have he := HallucinationModeCollapse.exp_neg_two_le_half_pow n hn
  have hex : Real.exp (-5*(n:ℝ)) ≤ (1/2 : ℝ) * ((1/4 : ℝ)^n * (1/2)) := by
    calc
      _ ≤ Real.exp (-2*(n:ℝ)) * Real.exp (-2*(n:ℝ)) := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
      _ ≤ ((1/2 : ℝ)^(n+1)) * ((1/2 : ℝ)^(n+1)) := mul_le_mul he he (Real.exp_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ, mul_mul_mul_comm, ← mul_pow]; ring_nf
  exact hex.trans ((mul_le_mul_of_nonneg_left hprob (by norm_num : (0:ℝ) ≤ 1/2)).trans
    (idErr_ge_gap C p A n _ _ hgap))

/-- The signatures identify languages extensionally, allowing duplicate indices. -/
theorem weak_exponential_lower (C : Generic.LanguageFamily α) (i j : ℕ) (hij : C i ≠ C j)
    (x y : α) (hx : ∀ k, x ∈ C k ↔ C k = C i) (hy : ∀ k, y ∈ C k ↔ C k = C j)
    (A : Identifier α) :
    ∃ p : PMF α, (∃ k, Optimal C p k) ∧ ∃ᶠ n : ℕ in atTop, Real.exp (-5 * (n:ℝ)) ≤ idErr C A p n := by
  have hxy : x ≠ y := fun h ↦ hij ((hy i).mp (h ▸ (hx i).mpr rfl))
  obtain ⟨hm₀,hm₁⟩ := biased_atom x y hxy
  obtain ⟨ho₀,hg₀⟩ := biased_risk C i j x y hij hx hy
  obtain ⟨ho₁,hg₁⟩ := biased_risk C j i y x hij.symm hy hx
  let event := fun k ↦ {l | C l ≠ C k}
  have either (n) : (1/2 : ℝ) ≤ probability (A (List.replicate n x)) (event i) ∨
      (1/2 : ℝ) ≤ probability (A (List.replicate n x)) (event j) := by
    have hcover : event i ∪ event j = Set.univ := Set.eq_univ_of_forall fun k ↦ by
      by_cases h : C k = C i
      · exact Or.inr (fun hh ↦ hij (h.symm.trans hh))
      · exact Or.inl h
    have h := probability_union_le (A (List.replicate n x)) (event i) (event j)
    rw [hcover,probability_univ] at h
    by_contra! hbad; linarith [hbad.1,hbad.2]
  rcases frequently_or_distrib.mp (Frequently.of_forall either : ∃ᶠ n : ℕ in atTop, _) with hf | hf
  · exact ⟨_,⟨i,ho₀⟩,(hf.and_eventually (eventually_ge_atTop 1)).mono fun n h ↦
      heavy_conditional C A _ i x n h.2 hm₀ hg₀ h.1⟩
  · exact ⟨_,⟨j,ho₁⟩,(hf.and_eventually (eventually_ge_atTop 1)).mono fun n h ↦
      heavy_conditional C A _ j x n h.2 hm₁ hg₁ h.1⟩

end
end GenLimit.AgnosticLanguage
