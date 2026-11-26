import GenLimit.Paper30_TimeSensitiveLanguageGeneration.SparseDiagonal
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.TimelyExpectation

/-! # Randomized timely-density impossibilities (Theorems 1 and 2)

The auxiliary presentation is held fixed while passing to expectation, and
the eventual final presentation is chosen before the random tape. No uniform
burn-in, independence of rounds, or inverse deadline is needed.
-/
namespace GenLimit.TimeSensitive
open Filter MeasureTheory GenLimit.KleinbergWei
open scoped Topology

private theorem count_ratio (K : Set ℕ) {n : ℕ} (hn : n ≠ 0) :
    (targetIntersectionCount id K n : ℝ) / n = naturalNumbersOrder.prefixRatio K n := by
  classical
  simp [targetIntersectionCount,targetPrefix,sequencePrefix,OrderedLanguage.prefixRatio,
    OrderedLanguage.prefixCount,naturalNumbersOrder,hn]

private theorem pow_cofinal : Tendsto (fun m : ℕ => (3:ℕ)^m) atTop atTop :=
  Nat.tendsto_pow_atTop_atTop_of_one_lt (by decide)

namespace RandomizedGenerator
variable {Ω : Type*} [MeasurableSpace Ω] (A : RandomizedGenerator Ω)
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

private theorem obstruction_of_sparse_expectations (D : ℕ → ℕ)
    (small : ∀ j s, Generic.Presents s (markerIntervalLanguage j) →
      Tendsto (fun m => A.expectedTimely μ s D (3^m)) atTop (𝓝 0)) :
    ∃ s, Generic.Presents s (sparseFamily 0) ∧
      ∀ᵐ ω ∂μ, lowerTimelyDensity (A.run s ω) id D = 0 := by
  obtain ⟨s,hs,pos,hpos,bound⟩ := sparse_presentation_diagonal
    (fun s n => A.expectedTimely μ s D n) (timelyHorizon D)
    (fun _ _ n => A.expectedTimely_congr μ D n) small
  apply Exists.intro s
  refine ⟨hs, A.lowerTimely_zero_ae μ s D pos hpos ?_⟩
  exact squeeze_zero (fun _ => integral_nonneg fun _ => timelyDensity_nonneg ..)
    bound tendsto_one_div_add_atTop_nhds_zero_nat

theorem eventually_consistent_obstruction (D : ℕ → ℕ)
    (consistent : ∀ z s, Generic.Presents s (sparseFamily z) →
      ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, A.run s ω t ∈ sparseFamily z) :
    ∃ s, Generic.Presents s (sparseFamily 0) ∧
      ∀ᵐ ω ∂μ, lowerTimelyDensity (A.run s ω) id D = 0 := by
  apply A.obstruction_of_sparse_expectations μ D
  intro j s hs
  let K := markerIntervalLanguage j
  have ae := consistent (j+1) s hs
  have pointwise : ∀ᵐ ω ∂μ, Tendsto (fun m : ℕ => timelyDensity (A.run s ω) id D (3^m))
      atTop (𝓝 0) := by
    filter_upwards [ae] with ω hω
    obtain ⟨T,hT⟩ := eventually_atTop.mp hω
    have up (m : ℕ) : timelyDensity (A.run s ω) id D (3^m) ≤
        naturalNumbersOrder.prefixRatio K (3^m) + (T:ℝ) / ((3^m:ℕ):ℝ) := by
      let n := (3:ℕ)^m
      have hn : n ≠ 0 := pow_ne_zero _ (by decide)
      have h := (timely_credit_le_common_cutoff (A.run s ω) D n (timelyHorizon D n)
        (fun i hi => Finset.le_sup (f := D) (Finset.mem_range.mpr hi))).trans
        (prefix_credit_le_target_intersection_add_burnIn _ _ K hT)
      change timelyDensity (A.run s ω) id D n ≤ naturalNumbersOrder.prefixRatio K n + (T:ℝ) / n
      rw [← count_ratio K hn, ← add_div]
      simp only [timelyDensity, if_neg hn]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast h
    have lim := (tendsto_marker_prefixRatio_pow j).add
      ((tendsto_const_div_atTop_nhds_zero_nat (T:ℝ)).comp pow_cofinal)
    exact squeeze_zero (fun _ => timelyDensity_nonneg ..) up (by simpa [K] using lim)
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun m ω => timelyDensity (A.run s ω) id D (3^m)) (f := fun _ => (0:ℝ))
    (fun _ => (1:ℝ)) (fun _ => (A.measurable_timely ..).aestronglyMeasurable)
    (integrable_const _) (fun _ => .of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (timelyDensity_nonneg ..)]
      exact timelyDensity_le_one ..) pointwise
  simpa [expectedTimely] using h

/-- A linear deadline permits a common output horizon C*n for all of the
first n preference ranks. A finite exceptional prefix is absorbed into C. -/
private theorem linear_envelope {D : ℕ → ℕ}
    (linear : ∃ c : ℕ, ∀ᶠ j in atTop, D j ≤ c*(j+1)) :
    ∃ C : ℕ, 0 < C ∧ ∀ j, D j ≤ C*(j+1) := by
  obtain ⟨c,hc⟩ := linear
  obtain ⟨N,hN⟩ := eventually_atTop.mp hc
  let C := max 1 (max c (timelyHorizon D N))
  refine ⟨C, lt_of_lt_of_le (by decide : 0 < 1) (le_max_left ..), fun j => ?_⟩
  by_cases hj : j < N
  · exact (Finset.le_sup (f := D) (Finset.mem_range.mpr hj)).trans
      ((le_trans (le_max_right ..) (le_max_right ..)).trans (Nat.le_mul_of_pos_right C (by omega)))
  · exact (hN j (by omega)).trans (Nat.mul_le_mul_right _ ((le_max_left ..).trans (le_max_right ..)))

theorem linear_vanishing_obstruction (D : ℕ → ℕ)
    (linear : ∃ c : ℕ, ∀ᶠ j in atTop, D j ≤ c*(j+1))
    (vanish : ∀ z s, Generic.Presents s (sparseFamily z) →
      Tendsto (A.expectedRate μ s (sparseFamily z)) atTop (𝓝 0)) :
    ∃ s, Generic.Presents s (sparseFamily 0) ∧
      ∀ᵐ ω ∂μ, lowerTimelyDensity (A.run s ω) id D = 0 := by
  obtain ⟨C,hC,hD⟩ := linear_envelope linear
  apply A.obstruction_of_sparse_expectations μ D
  intro j s hs
  let K := markerIntervalLanguage j
  have time : Tendsto (fun m : ℕ => C*3^m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left _ hC) pow_cofinal
  have rate := (vanish (j+1) s hs).comp time
  have up (m : ℕ) : A.expectedTimely μ s D (3^m) ≤
      naturalNumbersOrder.prefixRatio K (3^m) + (C:ℝ)*A.expectedRate μ s K (C*3^m) := by
    let n := (3:ℕ)^m
    have hn : n ≠ 0 := pow_ne_zero _ (by decide)
    let q := naturalNumbersOrder.prefixRatio K n
    have pointwise (ω : Ω) : timelyDensity (A.run s ω) id D n ≤ q + (C:ℝ)*A.loss s K (C*n) ω := by
      have count := (timely_credit_le_common_cutoff (A.run s ω) D n (C*n)
        (fun i hi => (hD i).trans (Nat.mul_le_mul_left _ hi))).trans
        (prefix_credit_le_target_intersection_add_hallucinations _ _ K n (C*n))
      have heq : (C:ℝ)*A.loss s K (C*n) ω =
          (hallucinationCount (A.run s ω) K (C*n) : ℝ) / n := by
        unfold loss
        push_cast
        field_simp [Nat.cast_ne_zero.mpr hC.ne',Nat.cast_ne_zero.mpr hn]
      rw [heq, show q = _ from (count_ratio K hn).symm, ← add_div]
      simp only [timelyDensity,if_neg hn]
      exact div_le_div_of_nonneg_right (by exact_mod_cast count) (Nat.cast_nonneg _)
    have h := integral_mono (A.integrable_timely μ s D n)
      ((integrable_const q).add ((A.integrable_loss μ s K (C*n)).const_mul (C:ℝ))) pointwise
    simpa only [expectedTimely,expectedRate,Pi.add_apply,Pi.mul_apply,integral_add
      (integrable_const q) ((A.integrable_loss μ s K (C*n)).const_mul (C:ℝ)),
      integral_const_mul,integral_const,measureReal_univ_eq_one,one_smul,q,n] using h
  exact squeeze_zero (fun _ => integral_nonneg fun _ => timelyDensity_nonneg ..) up
    (by simpa [K,Function.comp_def] using
      (tendsto_marker_prefixRatio_pow j).add (rate.const_mul (C:ℝ)))

end RandomizedGenerator
end GenLimit.TimeSensitive
