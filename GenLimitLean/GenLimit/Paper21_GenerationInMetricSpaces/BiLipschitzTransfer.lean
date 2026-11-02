import GenLimit.Paper21_GenerationInMetricSpaces.FiniteDimensionalCorollary
import GenLimit.Paper21_GenerationInMetricSpaces.LipschitzTransfer

/-!
# Bi-Lipschitz invariance of generation

Theorem 4.4 of Li--Raman--Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v2.
Mutual global Lipschitz bounds preserve doubling and transfer UUS and
correctness at rescaled radii. Doubling scale invariance then removes the
rescaling. Only the first metric is assumed doubling, as in the source.
-/

namespace GenLimit.MetricSpaces

/-- Mutual global Lipschitz domination, with a possibly different positive
constant in each direction. -/
def MutuallyLipschitzDominated
    (ρ₁ ρ₂ : Distance α) (M₁₂ M₂₁ : ℝ) : Prop :=
  DistanceDominatedBy ρ₂ ρ₁ M₁₂ ∧
    DistanceDominatedBy ρ₁ ρ₂ M₂₁

/-- Bi-Lipschitz equivalent distance kernels inherit the doubling property.
A fixed number of refinements absorbs the product of the two Lipschitz bounds. -/
theorem isDoublingDistance_of_mutual_domination
    {ρ₁ ρ₂ : Distance α} {M₁₂ M₂₁ : ℝ}
    (hDoubling : IsDoublingDistance ρ₁)
    (hM₁₂ : 0 < M₁₂) (hM₂₁ : 0 < M₂₁)
    (hdom : MutuallyLipschitzDominated ρ₁ ρ₂ M₁₂ M₂₁) :
    IsDoublingDistance ρ₂ := by
  classical
  obtain ⟨M, hM, hrefine⟩ := hDoubling
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      (1 / 2 : ℝ) ^ n < (1 / 2) / (M₁₂ * M₂₁) :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  have hfactor : M₁₂ * M₂₁ * (1 / 2 : ℝ) ^ n ≤ 1 / 2 := by
    have := (lt_div_iff₀ (mul_pos hM₁₂ hM₂₁)).mp hn
    nlinarith
  refine ⟨M ^ n, Nat.pow_pos hM, ?_⟩
  intro x r hr
  have houter : ∀ y ∈ {y | ρ₂ x y ≤ r},
      ∃ z ∈ ({x} : Finset α), ρ₁ z y ≤ M₂₁ * r := by
    intro y hy
    exact ⟨x, by simp, (hdom.2 x y).trans (mul_le_mul_of_nonneg_left hy hM₂₁.le)⟩
  obtain ⟨centers, hcard, hcover⟩ :=
    finitePointCover_halving_iterate_with_card hrefine
      (mul_pos hM₂₁ hr) houter n
  refine ⟨centers, by simpa using hcard, ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hcover y hy
  refine ⟨z, hz, ?_⟩
  calc
    ρ₂ z y ≤ M₁₂ * ρ₁ z y := hdom.1 z y
    _ ≤ M₁₂ * (M₂₁ * r * (1 / 2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hzy hM₁₂.le
    _ = (M₁₂ * M₂₁ * (1 / 2 : ℝ) ^ n) * r := by ring
    _ ≤ (1 / 2) * r := mul_le_mul_of_nonneg_right hfactor hr.le
    _ = r / 2 := by ring

/-- Uniform generation transfers between mutually Lipschitz-dominated
metrics.  The adversary scale grows with the forward bound, while the
generator novelty scale shrinks with the reverse bound. -/
theorem uniformlyGeneratableAt_transfer_of_mutual_domination
    {ρ₁ ρ₂ : Distance α} {M₁₂ M₂₁ ε ε' : ℝ}
    (hM₁₂ : 0 < M₁₂) (hM₂₁ : 0 < M₂₁)
    (hdom₁₂ : DistanceDominatedBy ρ₂ ρ₁ M₁₂)
    (hdom₂₁ : DistanceDominatedBy ρ₁ ρ₂ M₂₁)
    {H : GenLimit.Generic.LanguageClass α}
    (hgen : UniformlyGeneratableAt ρ₁ ε ε' H) :
    UniformlyGeneratableAt ρ₂ (M₁₂ * ε) (ε' / M₂₁) H := by
  obtain ⟨gen, d, hgen⟩ := hgen
  refine ⟨gen, d, ?_⟩
  intro L hLH stream hstream t htrigger s hts
  apply metricCorrectAt_transfer_of_dominated hM₂₁ hdom₂₁
  apply hgen L hLH stream hstream t
  · have hsource :=
      coveringNumberAtLeast_transfer_of_dominated
        hM₁₂ hdom₁₂ htrigger
    simpa [mul_div_cancel_left₀ ε hM₁₂.ne'] using hsource
  · exact hts

/-- Non-uniform generation obeys the same mutual-domination transfer law,
with every target-dependent threshold preserved. -/
theorem nonuniformlyGeneratableAt_transfer_of_mutual_domination
    {ρ₁ ρ₂ : Distance α} {M₁₂ M₂₁ ε ε' : ℝ}
    (hM₁₂ : 0 < M₁₂) (hM₂₁ : 0 < M₂₁)
    (hdom₁₂ : DistanceDominatedBy ρ₂ ρ₁ M₁₂)
    (hdom₂₁ : DistanceDominatedBy ρ₁ ρ₂ M₂₁)
    {H : GenLimit.Generic.LanguageClass α}
    (hgen : NonuniformlyGeneratableAt ρ₁ ε ε' H) :
    NonuniformlyGeneratableAt ρ₂ (M₁₂ * ε) (ε' / M₂₁) H := by
  obtain ⟨gen, hgen⟩ := hgen
  refine ⟨gen, ?_⟩
  intro L hLH
  obtain ⟨d, hd⟩ := hgen L hLH
  refine ⟨d, ?_⟩
  intro stream hstream t htrigger s hts
  apply metricCorrectAt_transfer_of_dominated hM₂₁ hdom₂₁
  apply hd stream hstream t
  · have hsource :=
      coveringNumberAtLeast_transfer_of_dominated
        hM₁₂ hdom₁₂ htrigger
    simpa [mul_div_cancel_left₀ ε hM₁₂.ne'] using hsource
  · exact hts

/-- Theorem 4.4. On genuine metrics related by
mutual global Lipschitz bounds, UUS, uniform generation, and non-uniform
generation are invariant.  All radii and novelty scales may be chosen
independently and positively on the two sides. -/
theorem theorem_4_4_bilipschitz
    {ρ₁ ρ₂ : Distance α} {M₁₂ M₂₁ : ℝ}
    {r₁ r₂ ε₁ ε₁' ε₂ ε₂' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling₁ : IsDoublingDistance ρ₁)
    (hrefl₁ : ∀ x : α, ρ₁ x x = 0)
    (hsymm₁ : ∀ x y : α, ρ₁ x y = ρ₁ y x)
    (htriangle₁ : ∀ x y z : α, ρ₁ x z ≤ ρ₁ x y + ρ₁ y z)
    (hrefl₂ : ∀ x : α, ρ₂ x x = 0)
    (hsymm₂ : ∀ x y : α, ρ₂ x y = ρ₂ y x)
    (htriangle₂ : ∀ x y z : α, ρ₂ x z ≤ ρ₂ x y + ρ₂ y z)
    (hM₁₂ : 0 < M₁₂) (hM₂₁ : 0 < M₂₁)
    (hdom : MutuallyLipschitzDominated ρ₁ ρ₂ M₁₂ M₂₁)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hε₁ : 0 < ε₁) (hε₁' : 0 < ε₁')
    (hε₂ : 0 < ε₂) (hε₂' : 0 < ε₂') :
    (UniformlyUnboundedSupportAt ρ₁ r₁ H ↔
      UniformlyUnboundedSupportAt ρ₂ r₂ H) ∧
    (UniformlyGeneratableAt ρ₁ ε₁ ε₁' H ↔
      UniformlyGeneratableAt ρ₂ ε₂ ε₂' H) ∧
    (NonuniformlyGeneratableAt ρ₁ ε₁ ε₁' H ↔
      NonuniformlyGeneratableAt ρ₂ ε₂ ε₂' H) := by
  have hDoubling₂ := isDoublingDistance_of_mutual_domination hDoubling₁ hM₁₂ hM₂₁ hdom
  rcases hdom with ⟨hdom₁₂, hdom₂₁⟩
  have hUUS :
      UniformlyUnboundedSupportAt ρ₁ r₁ H ↔
        UniformlyUnboundedSupportAt ρ₂ r₂ H := by
    constructor
    · intro h
      have hscaled :=
        theorem_4_10_uus_transfer
          (ρ₁ := ρ₂) (ρ₂ := ρ₁) hM₂₁ hdom₂₁ h
      exact
        theorem_4_1_doubling_uus_scale_invariance
          hDoubling₂ hrefl₂ hsymm₂ htriangle₂ (div_pos hr₁ hM₂₁) hscaled r₂ hr₂
    · intro h
      have hscaled :=
        theorem_4_10_uus_transfer
          (ρ₁ := ρ₁) (ρ₂ := ρ₂) hM₁₂ hdom₁₂ h
      exact
        theorem_4_1_doubling_uus_scale_invariance
          hDoubling₁ hrefl₁ hsymm₁ htriangle₁ (div_pos hr₂ hM₁₂) hscaled r₁ hr₁
  have hUniform :
      UniformlyGeneratableAt ρ₁ ε₁ ε₁' H ↔
        UniformlyGeneratableAt ρ₂ ε₂ ε₂' H := by
    constructor
    · intro h
      have hscaled :=
        uniformlyGeneratableAt_transfer_of_mutual_domination
          hM₁₂ hM₂₁ hdom₁₂ hdom₂₁ h
      exact
        (doubling_generation_scale_invariance_all_positive
          hDoubling₂ hrefl₂ hsymm₂ htriangle₂
          hε₂ hε₂' (mul_pos hM₁₂ hε₁) (div_pos hε₁' hM₂₁)).1.mp
          hscaled
    · intro h
      have hscaled :=
        uniformlyGeneratableAt_transfer_of_mutual_domination
          hM₂₁ hM₁₂ hdom₂₁ hdom₁₂ h
      exact
        (doubling_generation_scale_invariance_all_positive
          hDoubling₁ hrefl₁ hsymm₁ htriangle₁
          hε₁ hε₁' (mul_pos hM₂₁ hε₂) (div_pos hε₂' hM₁₂)).1.mp
          hscaled
  have hNonuniform :
      NonuniformlyGeneratableAt ρ₁ ε₁ ε₁' H ↔
        NonuniformlyGeneratableAt ρ₂ ε₂ ε₂' H := by
    constructor
    · intro h
      have hscaled :=
        nonuniformlyGeneratableAt_transfer_of_mutual_domination
          hM₁₂ hM₂₁ hdom₁₂ hdom₂₁ h
      exact
        (doubling_generation_scale_invariance_all_positive
          hDoubling₂ hrefl₂ hsymm₂ htriangle₂
          hε₂ hε₂' (mul_pos hM₁₂ hε₁) (div_pos hε₁' hM₂₁)).2.mp
          hscaled
    · intro h
      have hscaled :=
        nonuniformlyGeneratableAt_transfer_of_mutual_domination
          hM₂₁ hM₁₂ hdom₂₁ hdom₁₂ h
      exact
        (doubling_generation_scale_invariance_all_positive
          hDoubling₁ hrefl₁ hsymm₁ htriangle₁
          hε₁ hε₁' (mul_pos hM₂₁ hε₂) (div_pos hε₂' hM₁₂)).2.mp
          hscaled
  exact ⟨hUUS, hUniform, hNonuniform⟩

end GenLimit.MetricSpaces
