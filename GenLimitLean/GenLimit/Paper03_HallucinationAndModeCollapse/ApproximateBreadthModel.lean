import GenLimit.Paper03_HallucinationAndModeCollapse.UnambiguousModel

/-!
# Statistical approximate breadth: Definition 9 and equation (6)

The event is the existing `ApproximateBreadthAt`: the trained support is a
subset of the target and omits only finitely many target points. Training
examples may be repeated in the output. Failure is measured over the ordered
IID training sample, not over one random output. Stability and pointwise MOP
are reused from the existing statistical interfaces.
-/

namespace GenLimit.HallucinationModeCollapse

noncomputable section

open GenLimit.Generic GenLimit.DiscreteIID Filter
open scoped Topology

def approximateBreadthError (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : ℝ :=
  probability (samples p n) {xs | ¬ApproximateBreadthAt (G xs).support (C i)}

/-- Equation (6), retaining infinite omission as distinct from any finite
number of omitted target elements. -/
theorem approximateBreadthError_source (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) :
    approximateBreadthError C G p i n = probability (samples p n)
      {xs | ¬(G xs).support ⊆ C i ∨ (C i \ (G xs).support).Infinite} := by
  simp only [approximateBreadthError, ApproximateBreadthAt, not_and_or, Set.Infinite]

def AchievesApproximateBreadthRate (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (R : ℕ → ℝ) : Prop :=
  ∀ i p, ValidDistribution C i p → ∃ D : ℝ, 0 < D ∧
    ∀ n, approximateBreadthError C G p i n ≤ D * R n

/-- Real-domain rates give a precise interpretation of the source's `R(c*n)`,
with both positive constants allowed to depend on the target distribution. -/
def AchievesScaledApproximateBreadthRate (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (R : ℝ → ℝ) : Prop :=
  ∀ i p, ValidDistribution C i p → ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
    ∀ n, approximateBreadthError C G p i n ≤ D * R (c * (n : ℝ))

def NoApproximateBreadthRate (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator) : Prop :=
  ∃ i p, ValidDistribution C i p ∧
    0 < limsup (fun n => approximateBreadthError C G p i n) atTop

theorem approximateBreadthError_nonneg (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : 0 ≤ approximateBreadthError C G p i n := probability_nonneg _ _

theorem approximateBreadthError_le_one (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : approximateBreadthError C G p i n ≤ 1 := probability_le_one _ _

theorem approximateBreadthError_tendsto_zero_of_rate (C : Generic.LanguageFamily ℕ)
    (G : StatisticalGenerator) (R : ℕ → ℝ) (hG : AchievesApproximateBreadthRate C G R)
    (hR : Tendsto R atTop (𝓝 0)) (i : ℕ) (p : PMF ℕ) (hp : ValidDistribution C i p) :
    Tendsto (fun n => approximateBreadthError C G p i n) atTop (𝓝 0) := by
  obtain ⟨D, _, hb⟩ := hG i p hp
  apply squeeze_zero (approximateBreadthError_nonneg C G p i) hb
  simpa using tendsto_const_nhds.mul hR

theorem NoApproximateBreadthRate.excludes_rate {C : Generic.LanguageFamily ℕ} {G : StatisticalGenerator}
    (h : NoApproximateBreadthRate C G) (R : ℕ → ℝ) (hR : Tendsto R atTop (𝓝 0)) :
    ¬AchievesApproximateBreadthRate C G R := by
  intro hG
  obtain ⟨i, p, hp, hpos⟩ := h
  rw [(approximateBreadthError_tendsto_zero_of_rate C G R hG hR i p hp).limsup_eq] at hpos
  exact lt_irrefl _ hpos

theorem NoApproximateBreadthRate.excludes_scaled_rate
    {C : Generic.LanguageFamily ℕ} {G : StatisticalGenerator}
    (h : NoApproximateBreadthRate C G) (R : ℝ → ℝ) (hR : Tendsto R atTop (𝓝 0)) :
    ¬AchievesScaledApproximateBreadthRate C G R := by
  intro hG
  obtain ⟨i, p, hp, hpos⟩ := h
  obtain ⟨c, hc, D, _, hb⟩ := hG i p hp
  have hs : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n => approximateBreadthError C G p i n) atTop (𝓝 0) := by
    apply squeeze_zero (approximateBreadthError_nonneg C G p i) hb
    simpa using tendsto_const_nhds.mul (hR.comp hs)
  rw [he.limsup_eq] at hpos
  exact lt_irrefl _ hpos

end
end GenLimit.HallucinationModeCollapse
