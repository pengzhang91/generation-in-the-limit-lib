import GenLimit.Paper30_TimeSensitiveLanguageGeneration.RandomizedRuns
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Finite dependence of expected timely density and its almost-sure lower limit -/
namespace GenLimit.TimeSensitive
open Filter MeasureTheory
open scoped Topology

def timelyHorizon (D : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range n).sup D

theorem timelyDensity_congr {u v : ℕ → ℕ} (D : ℕ → ℕ) (n : ℕ)
    (agree : ∀ j < timelyHorizon D n, u j = v j) :
    timelyDensity u id D n = timelyDensity v id D n := by
  classical
  have eq : timelyElements u id D n = timelyElements v id D n := by
    ext x
    simp only [timelyElements, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
      id_eq, exists_eq_right, mem_sequencePrefix_iff]
    apply and_congr_right
    intro hx
    apply exists_congr
    intro j
    apply and_congr_right
    intro hj
    rw [agree j (lt_of_lt_of_le hj (Finset.le_sup (f := D) (Finset.mem_range.mpr hx)))]
  simp only [timelyDensity,eq]

theorem timely_credit_le_common_cutoff (u : ℕ → ℕ) (D : ℕ → ℕ) (n T : ℕ)
    (bound : ∀ j < n, D j ≤ T) :
    (timelyElements u id D n).card ≤ (prefixWiseElements u id (fun _ => T) n).card := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [timelyElements, Finset.mem_image, Finset.mem_filter, Finset.mem_range, id_eq,
    exists_eq_right] at hx
  simp only [prefixWiseElements, Finset.mem_inter]
  exact ⟨(mem_sequencePrefix_iff ..).mpr ⟨x,hx.1,rfl⟩, sequencePrefix_mono _ (bound _ hx.1) hx.2⟩

namespace RandomizedGenerator
variable {Ω : Type*} [MeasurableSpace Ω] (A : RandomizedGenerator Ω)
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def expectedTimely (s : ℕ → ℕ) (D : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∫ ω, timelyDensity (A.run s ω) id D n ∂μ

omit [IsProbabilityMeasure μ] in
theorem expectedTimely_congr {s r : ℕ → ℕ} (D : ℕ → ℕ) (n : ℕ)
    (agree : ∀ j < timelyHorizon D n, s j = r j) :
    A.expectedTimely μ s D n = A.expectedTimely μ r D n :=
  integral_congr_ae (.of_forall fun ω => timelyDensity_congr D n (fun _ hj => A.run_congr agree ω hj))

theorem measurable_timely (s : ℕ → ℕ) (D : ℕ → ℕ) (n : ℕ) :
    Measurable (fun ω => timelyDensity (A.run s ω) id D n) := by
  let extend (xs : Fin (timelyHorizon D n) → ℕ) (j : ℕ) :=
    if hj : j < timelyHorizon D n then xs ⟨j,hj⟩ else 0
  let stat (xs : Fin (timelyHorizon D n) → ℕ) := timelyDensity (extend xs) id D n
  have m : Measurable (fun ω (i : Fin (timelyHorizon D n)) => A.run s ω i.val) :=
    measurable_pi_lambda _ (fun i => A.measurable_choose i.val _)
  have hmeas := (measurable_of_countable stat).comp m
  convert hmeas using 1
  funext ω
  exact timelyDensity_congr D n (fun j hj => by simp [extend,hj])

theorem integrable_timely (s : ℕ → ℕ) (D : ℕ → ℕ) (n : ℕ) :
    Integrable (fun ω => timelyDensity (A.run s ω) id D n) μ :=
  Integrable.of_bound (A.measurable_timely ..).aestronglyMeasurable 1
    (.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (timelyDensity_nonneg ..)]
                            exact timelyDensity_le_one ..)

theorem lowerTimely_zero_ae (s : ℕ → ℕ) (D pos : ℕ → ℕ)
    (cofinal : Tendsto pos atTop atTop)
    (small : Tendsto (fun k => A.expectedTimely μ s D (pos k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, lowerTimelyDensity (A.run s ω) id D = 0 := by
  let f := fun k ω => ENNReal.ofReal (timelyDensity (A.run s ω) id D (pos k))
  have meas (k : ℕ) : Measurable (f k) := (A.measurable_timely ..).ennreal_ofReal
  have hlim : Tendsto (fun k => ∫⁻ ω, f k ω ∂μ) atTop (𝓝 0) := by
    simpa only [expectedTimely, ENNReal.ofReal_zero, Function.comp_def,
      ofReal_integral_eq_lintegral_ofReal (A.integrable_timely μ s D _)
        (.of_forall fun ω => timelyDensity_nonneg ..), f] using
      (ENNReal.continuous_ofReal.tendsto (0:ℝ)).comp small
  have zero := (lintegral_liminf_le (μ := μ) meas).trans_eq hlim.liminf_eq
  have ae := (lintegral_eq_zero_iff (Measurable.liminf meas)).mp (le_antisymm zero bot_le)
  filter_upwards [ae] with ω hω
  let u := fun n => timelyDensity (A.run s ω) id D n
  change liminf u atTop = 0
  have lb : 0 ≤ liminf u atTop := le_liminf_of_le
    (isCoboundedUnder_ge_of_le atTop (fun n => timelyDensity_le_one ..))
    (.of_forall fun n => timelyDensity_nonneg ..)
  apply le_antisymm _ lb
  by_contra! h
  let ε := liminf u atTop / 2
  have hε : 0 < ε := half_pos h
  have ev : ∀ᶠ n in atTop, ε < u n := eventually_lt_of_lt_liminf (half_lt_self h) (isBoundedUnder_of ⟨0,fun n => timelyDensity_nonneg ..⟩)
  have pos_le : ENNReal.ofReal ε ≤ liminf (fun k => f k ω) atTop :=
    le_liminf_of_le (by isBoundedDefault) ((cofinal.eventually ev).mono
      (fun k hk => ENNReal.ofReal_le_ofReal hk.le))
  change liminf (fun k => f k ω) atTop = 0 at hω
  rw [hω] at pos_le
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hε)) pos_le

end RandomizedGenerator
end GenLimit.TimeSensitive
