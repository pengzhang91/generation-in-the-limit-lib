import GenLimit.Paper21_GenerationInMetricSpaces.FiniteDimensionalCorollary
import GenLimit.Paper21_GenerationInMetricSpaces.LipschitzTransfer

/-!
# A bi-Lipschitz repair of Theorem 4.4

The printed proof of Theorem 4.4 in Li--Raman--Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1, uses the false
inference isolated in `EquivalentMetricDiagnostic`: topological equivalence
does not compare covering numbers at a fixed numerical radius.

This module records a sound replacement.  Mutual global Lipschitz bounds do
provide the quantitative ball inclusions required by the generation
semantics.  In a doubling space, Theorems 4.1 and 4.2 then remove the scale
changes introduced by those bounds.  The conclusion matches the three
invariance conclusions of printed Theorem 4.4, under the explicitly stronger
bi-Lipschitz hypothesis.
-/

namespace GenLimit.MetricSpaces

/-- Mutual global Lipschitz domination, with a possibly different positive
constant in each direction. -/
def MutuallyLipschitzDominated
    (ρ₁ ρ₂ : Distance α) (M₁₂ M₂₁ : ℝ) : Prop :=
  DistanceDominatedBy ρ₂ ρ₁ M₁₂ ∧
    DistanceDominatedBy ρ₁ ρ₂ M₂₁

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

/-- Corrected Theorem 4.4.  On two doubling genuine metrics related by
mutual global Lipschitz bounds, UUS, uniform generation, and non-uniform
generation are invariant.  All radii and novelty scales may be chosen
independently and positively on the two sides. -/
theorem theorem_4_4_bilipschitz_repair
    {ρ₁ ρ₂ : Distance α} {M₁₂ M₂₁ : ℝ}
    {r₁ r₂ ε₁ ε₁' ε₂ ε₂' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling₁ : IsDoublingDistance ρ₁)
    (hDoubling₂ : IsDoublingDistance ρ₂)
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
          hDoubling₂ (div_pos hr₁ hM₂₁) hscaled r₂ hr₂
    · intro h
      have hscaled :=
        theorem_4_10_uus_transfer
          (ρ₁ := ρ₁) (ρ₂ := ρ₂) hM₁₂ hdom₁₂ h
      exact
        theorem_4_1_doubling_uus_scale_invariance
          hDoubling₁ (div_pos hr₂ hM₁₂) hscaled r₁ hr₁
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
