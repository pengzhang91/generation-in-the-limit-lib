import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Model

/-! The normalized finite exponential mechanism and the score-margin
bound of Lemma 2.2. The inverse temperature is ε/(2Δ). -/

namespace GenLimit.PriceOfPrivacy.Exponential

open DiscreteIID Set
open scoped ENNReal Classical
noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private def weight (s : ι → ℝ) (a : ℝ) (i : ι) := Real.exp (a*s i)
private def normalizer (s : ι → ℝ) (a : ℝ) := ∑ i, weight s a i

omit [Fintype ι] [Nonempty ι] in
private theorem weight_pos (s : ι → ℝ) (a : ℝ) (i : ι) : 0 < weight s a i := Real.exp_pos _

private theorem norm_pos (s : ι → ℝ) (a : ℝ) : 0 < normalizer s a :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- Probability of a candidate is proportional to exp(a times its score). -/
def law (s : ι → ℝ) (a : ℝ) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (weight s a i / normalizer s a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (weight_pos s a i).le (norm_pos s a).le),
      show (∑ i, weight s a i / normalizer s a) = normalizer s a / normalizer s a by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]; rfl,
      div_self (norm_pos s a).ne',ENNReal.ofReal_one])

private theorem event_eq (s : ι → ℝ) (a : ℝ) (F : Set ι) :
    probability (law s a) F = ∑ i, if i ∈ F then weight s a i / normalizer s a else 0 := by
  rw [AgnosticLanguage.prob_event_tsum,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ F <;> simp [hi,law,ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos (a*s i)).le (norm_pos s a).le),weight]

omit [Fintype ι] [Nonempty ι] in
private theorem weight_compare {s t : ι → ℝ} {a Δ : ℝ} (ha : 0 ≤ a)
    (h : ∀ i, s i - t i ≤ Δ) (i : ι) :
    weight s a i ≤ Real.exp (a*Δ) * weight t a i := by
  rw [weight,weight,←Real.exp_add,Real.exp_le_exp]
  linarith [mul_le_mul_of_nonneg_left (h i) ha]

theorem event_private (s t : ι → ℝ) (a Δ : ℝ) (ha : 0 ≤ a)
    (diff : ∀ i, |s i-t i| ≤ Δ) (F : Set ι) :
    probability (law s a) F ≤ Real.exp (2*a*Δ) * probability (law t a) F := by
  have up := weight_compare (s := s) (t := t) ha (fun i => (abs_le.mp (diff i)).2)
  have down := weight_compare (s := t) (t := s) (Δ := Δ) ha (fun i => by linarith [(abs_le.mp (diff i)).1])
  have z : normalizer t a ≤ Real.exp (a*Δ)*normalizer s a := by
    unfold normalizer
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => down i)
  have factor : Real.exp (2*a*Δ) = Real.exp (a*Δ)*Real.exp (a*Δ) := by rw [←Real.exp_add]; congr 1; ring
  rw [event_eq,event_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ F
  · rw [if_pos hi,if_pos hi,←mul_div_assoc,div_le_div_iff₀ (norm_pos s a) (norm_pos t a),factor]
    have h := mul_le_mul (up i) z (norm_pos t a).le
      (mul_nonneg (Real.exp_pos _).le (weight_pos t a i).le)
    exact h.trans_eq (by ring)
  · simp [hi]

theorem event_margin (s : ι → ℝ) (a : ℝ) (ha : 0 ≤ a) (F : Set ι)
    (i₀ : ι) (Γ : ℝ) (gap : ∀ i ∈ F, Γ ≤ s i₀ - s i) :
    probability (law s a) F ≤ Fintype.card ι * Real.exp (-a*Γ) := by
  have z : weight s a i₀ ≤ normalizer s a :=
    Finset.single_le_sum (fun i _ => (weight_pos s a i).le) (Finset.mem_univ i₀)
  rw [event_eq]
  calc
    _ ≤ ∑ _ : ι, Real.exp (-a*Γ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ F
      · rw [if_pos hi,div_le_iff₀ (norm_pos s a)]
        apply le_trans _ (mul_le_mul_of_nonneg_left z (Real.exp_pos _).le)
        rw [weight,weight,←Real.exp_add,Real.exp_le_exp]
        linarith [mul_le_mul_of_nonneg_left (gap i hi) ha]
      · simpa [hi] using (Real.exp_pos (-a*Γ)).le
    _ = _ := by simp

/-- Pairing every member of an event with a distinct higher-score
candidate removes the cardinality factor from the exponential tail. -/
theorem event_injection (s : ι → ℝ) (a : ℝ) (ha : 0 ≤ a) (F : Set ι)
    (g : ι → ι) (inj : Set.InjOn g F) (Γ : ℝ) (gap : ∀ i ∈ F, Γ ≤ s (g i)-s i) :
    probability (law s a) F ≤ Real.exp (-a*Γ) := by
  let D := Finset.univ.filter fun i => i ∈ F
  have hd (i : ι) : i ∈ D ↔ i ∈ F := by simp [D]
  have eq : probability (law s a) F = (∑ i ∈ D, weight s a i)/normalizer s a := by
    rw [event_eq]
    simp [D,Finset.sum_filter,div_eq_mul_inv,Finset.sum_mul,ite_mul]
  rw [eq,div_le_iff₀ (norm_pos s a)]
  calc
    _ ≤ ∑ i ∈ D, Real.exp (-a*Γ)*weight s a (g i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [weight,weight,←Real.exp_add,Real.exp_le_exp]
      linarith [mul_le_mul_of_nonneg_left (gap i ((hd i).mp hi)) ha]
    _ ≤ _ := by
      rw [←Finset.mul_sum,←Finset.sum_image (f := fun j => weight s a j)
        (fun i hi j hj eq => inj ((hd i).mp hi) ((hd j).mp hj) eq)]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => (weight_pos s a i).le)) (Real.exp_pos _).le

end
end GenLimit.PriceOfPrivacy.Exponential
