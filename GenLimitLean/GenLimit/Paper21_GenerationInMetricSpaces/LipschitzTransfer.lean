import GenLimit.Paper21_GenerationInMetricSpaces.ScaleMonotonicity
import Mathlib.Algebra.Order.Field.Basic

/-!
# Transfer under a one-sided Lipschitz change of metric

This is the exact semantic content of Theorem 4.10 in
Li--Raman--Tewari, *On Generation in Metric Spaces*,
arXiv:2602.07710v1.
-/

namespace GenLimit.MetricSpaces

/-- The source assumption `ρ₂(x,y) ≤ M ρ₁(x,y)` for all points. -/
def DistanceDominatedBy
    (ρ₂ ρ₁ : Distance α) (M : ℝ) : Prop :=
  ∀ x y, ρ₂ x y ≤ M * ρ₁ x y

/-- A radius-`r/M` closed neighbourhood for `ρ₁` is contained in the
radius-`r` closed neighbourhood for `ρ₂`.  The proof works at the infimum
boundary and does not assume that a nearest center exists. -/
theorem closedNeighborhood_subset_of_dominated
    {ρ₁ ρ₂ : Distance α} {M r : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    (A : Set α) :
    closedNeighborhood ρ₁ A (r / M) ⊆
      closedNeighborhood ρ₂ A r := by
  intro y hy η hrη
  have hrdiv : r / M < η / M :=
    div_lt_div_of_pos_right hrη hM
  obtain ⟨x, hxA, hxy⟩ := hy (η / M) hrdiv
  refine ⟨x, hxA, ?_⟩
  calc
    ρ₂ x y ≤ M * ρ₁ x y := hdom x y
    _ < M * (η / M) := mul_lt_mul_of_pos_left hxy hM
    _ = η := mul_div_cancel₀ η hM.ne'

theorem finiteCover_transfer_of_dominated
    {ρ₁ ρ₂ : Distance α} {M r : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    {A : Set α} :
    HasFiniteCover ρ₁ (r / M) A →
      HasFiniteCover ρ₂ r A := by
  rintro ⟨centers, hcover⟩
  exact
    ⟨centers,
      hcover.trans
        (closedNeighborhood_subset_of_dominated hM hdom
          (centers : Set α))⟩

/-- A lower bound on the covering number transfers contravariantly along
a one-sided Lipschitz domination, with the radius divided by the Lipschitz
constant. -/
theorem coveringNumberAtLeast_transfer_of_dominated
    {ρ₁ ρ₂ : Distance α} {M r : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    {A : Set α} {d : ℕ}
    (hlower : CoveringNumberAtLeast ρ₂ r A d) :
    CoveringNumberAtLeast ρ₁ (r / M) A d := by
  intro centers hcover
  exact hlower centers
    (hcover.trans
      (closedNeighborhood_subset_of_dominated hM hdom
        (centers : Set α)))

/-- The UUS half of Theorem 4.10. -/
theorem theorem_4_10_uus_transfer
    {ρ₁ ρ₂ : Distance α} {M r : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : UniformlyUnboundedSupportAt ρ₂ r H) :
    UniformlyUnboundedSupportAt ρ₁ (r / M) H := by
  intro L hLH hfinite
  exact hUUS L hLH
    (finiteCover_transfer_of_dominated hM hdom hfinite)

theorem metricPresentation_transfer_of_dominated
    {ρ₁ ρ₂ : Distance α} {M ε : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hpresentation : MetricPresentation ρ₁ (ε / M) stream L) :
    MetricPresentation ρ₂ ε stream L := by
  rcases hpresentation with ⟨hstream, hcover⟩
  exact
    ⟨hstream,
      hcover.trans
        (closedNeighborhood_subset_of_dominated hM hdom
          (Set.range stream))⟩

theorem metricCorrectAt_transfer_of_dominated
    {ρ₁ ρ₂ : Distance α} {M ε' : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    {gen : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ}
    (hcorrect : MetricCorrectAt ρ₂ ε' gen L stream t) :
    MetricCorrectAt ρ₁ (ε' / M) gen L stream t := by
  rcases hcorrect with ⟨hvalid, hfresh⟩
  refine ⟨hvalid, ?_⟩
  intro hnear
  exact hfresh
    (closedNeighborhood_subset_of_dominated hM hdom
      (GenLimit.Generic.sample stream t : Set α) hnear)

/-- Generator-level generation-in-the-limit half of Theorem 4.10. -/
theorem isLimitGeneratorAt_transfer_of_dominated
    {ρ₁ ρ₂ : Distance α} {M ε ε' : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α}
    (hgen : IsLimitGeneratorAt ρ₂ ε ε' gen H) :
    IsLimitGeneratorAt ρ₁ (ε / M) (ε' / M) gen H := by
  intro L hLH stream hpresentation
  obtain ⟨T, hT⟩ :=
    hgen L hLH stream
      (metricPresentation_transfer_of_dominated hM hdom hpresentation)
  exact
    ⟨T, fun t ht ↦
      metricCorrectAt_transfer_of_dominated hM hdom (hT t ht)⟩

/-- Generation-in-the-limit half of Theorem 4.10. -/
theorem theorem_4_10_limit_transfer
    {ρ₁ ρ₂ : Distance α} {M ε ε' : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    {H : GenLimit.Generic.LanguageClass α}
    (hgen : GeneratableInLimitAt ρ₂ ε ε' H) :
    GeneratableInLimitAt ρ₁ (ε / M) (ε' / M) H := by
  obtain ⟨gen, hgen⟩ := hgen
  exact
    ⟨gen,
      isLimitGeneratorAt_transfer_of_dominated hM hdom hgen⟩

/-- Theorem 4.10, packaged exactly as its two conclusions. -/
theorem theorem_4_10
    {ρ₁ ρ₂ : Distance α} {M r ε ε' : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : UniformlyUnboundedSupportAt ρ₂ r H)
    (hgen : GeneratableInLimitAt ρ₂ ε ε' H) :
    UniformlyUnboundedSupportAt ρ₁ (r / M) H ∧
      GeneratableInLimitAt ρ₁ (ε / M) (ε' / M) H :=
  ⟨theorem_4_10_uus_transfer hM hdom hUUS,
    theorem_4_10_limit_transfer hM hdom hgen⟩

end GenLimit.MetricSpaces
