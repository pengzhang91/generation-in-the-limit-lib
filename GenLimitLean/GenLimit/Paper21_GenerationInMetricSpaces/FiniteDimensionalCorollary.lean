import GenLimit.Paper21_GenerationInMetricSpaces.DoublingGeneration
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-dimensional scale invariance

This module formalizes Corollary 4.3 of Jiaxun Li, Vinod Raman, and
Ambuj Tewari, *On Generation in Metric Spaces*, arXiv:2602.07710v1.

The printed deduction omits two bridges.  First, Theorem 4.2 compares
coordinatewise ordered pairs of scales, whereas the corollary quantifies
over two arbitrary positive pairs.  Passing through their coordinatewise
minima repairs that step.  Second, the observation that Euclidean space is
doubling must be combined with the finite-dimensional normed-space
argument.  Here this is proved directly: compactness gives a finite
half-radius cover of the closed unit ball, and translation and positive
rescaling transport that one cover uniformly to every ball.

The scale-invariance theorem obtained from the repaired Theorem 4.2 does
not need the source's UUS premise.  The final declaration nevertheless
retains it in an exact source-facing wrapper.
-/

namespace GenLimit.MetricSpaces

/-! ## Arbitrary positive scale pairs -/

/-- The maximum scale-invariance consequence of Theorem 4.2: in a doubling
genuine metric, uniform and non-uniform generation are independent of two
arbitrary positive scale pairs. -/
theorem doubling_generation_scale_invariance_all_positive
    {ρ : Distance α} {δ δ' ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle :
      ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hε : 0 < ε) (hε' : 0 < ε') :
    (UniformlyGeneratableAt ρ ε ε' H ↔
      UniformlyGeneratableAt ρ δ δ' H) ∧
    (NonuniformlyGeneratableAt ρ ε ε' H ↔
      NonuniformlyGeneratableAt ρ δ δ' H) := by
  let η := min ε δ
  let η' := min ε' δ'
  have hη : 0 < η := by
    exact lt_min hε hδ
  have hη' : 0 < η' := by
    exact lt_min hε' hδ'
  have hηε : η ≤ ε := by
    exact min_le_left _ _
  have hηδ : η ≤ δ := by
    exact min_le_right _ _
  have hη'ε' : η' ≤ ε' := by
    exact min_le_left _ _
  have hη'δ' : η' ≤ δ' := by
    exact min_le_right _ _
  have hUniformε :
      UniformlyGeneratableAt ρ ε ε' H ↔
        UniformlyGeneratableAt ρ η η' H :=
    theorem_4_2_uniform_scale_invariance
      hDoubling hrefl hsymm htriangle
        hη hη' hε hε' hηε hη'ε'
  have hUniformδ :
      UniformlyGeneratableAt ρ δ δ' H ↔
        UniformlyGeneratableAt ρ η η' H :=
    theorem_4_2_uniform_scale_invariance
      hDoubling hrefl hsymm htriangle
        hη hη' hδ hδ' hηδ hη'δ'
  have hNonuniformε :
      NonuniformlyGeneratableAt ρ ε ε' H ↔
        NonuniformlyGeneratableAt ρ η η' H :=
    theorem_4_2_nonuniform_scale_invariance
      hDoubling hrefl hsymm htriangle
        hη hη' hε hε' hηε hη'ε'
  have hNonuniformδ :
      NonuniformlyGeneratableAt ρ δ δ' H ↔
        NonuniformlyGeneratableAt ρ η η' H :=
    theorem_4_2_nonuniform_scale_invariance
      hDoubling hrefl hsymm htriangle
        hη hη' hδ hδ' hηδ hη'δ'
  exact
    ⟨hUniformε.trans hUniformδ.symm,
      hNonuniformε.trans hNonuniformδ.symm⟩

/-! ## Finite-dimensional real normed spaces are doubling -/

/-- Every finite-dimensional real normed vector space satisfies the paper's
uniform closed-ball doubling condition. -/
theorem isDoublingDistance_dist_finiteDimensional
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    IsDoublingDistance (dist : E → E → ℝ) := by
  classical
  obtain ⟨centersSet, _hcentersSubset, hcentersFinite, hunitCover⟩ :=
    finite_cover_balls_of_compact
      (isCompact_closedBall (0 : E) 1)
      (by norm_num : (0 : ℝ) < 1 / 2)
  let centers : Finset E := hcentersFinite.toFinset
  refine ⟨centers.card + 1, Nat.succ_pos _, ?_⟩
  intro x r hr
  let scaledCenters : Finset E :=
    centers.image fun c ↦ x + r • c
  refine ⟨scaledCenters, ?_, ?_⟩
  · exact
      (Finset.card_image_le.trans
        (Nat.le_succ centers.card))
  · intro y hxy
    let u : E := (1 / r) • (y - x)
    have hyNorm : ‖y - x‖ ≤ r := by
      simpa [dist_eq_norm, norm_sub_rev] using hxy
    have huNorm : ‖u‖ ≤ 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos zero_lt_one hr)]
      have hnonneg : 0 ≤ 1 / r := (div_pos zero_lt_one hr).le
      calc
        (1 / r) * ‖y - x‖ ≤ (1 / r) * r :=
          mul_le_mul_of_nonneg_left hyNorm hnonneg
        _ = 1 := by field_simp
    have huBall : u ∈ Metric.closedBall (0 : E) 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using huNorm
    have huCover := hunitCover huBall
    simp only [Set.mem_iUnion, Metric.mem_ball] at huCover
    obtain ⟨c, hcSet, huc⟩ := huCover
    have hc : c ∈ centers := by
      exact hcentersFinite.mem_toFinset.mpr hcSet
    refine ⟨x + r • c, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    · have hy :
          y = x + r • u := by
        dsimp [u]
        simp [smul_smul, hr.ne']
      rw [hy, dist_add_left, dist_smul₀,
        Real.norm_eq_abs, abs_of_pos hr]
      have hcu : dist c u < 1 / 2 := by
        simpa [dist_comm] using huc
      nlinarith

/-! ## Finite-dimensional scale invariance -/

/-- On a finite-dimensional real normed vector space, both generation
notions are independent of arbitrary positive scale pairs.  This is the
strongest direct conclusion supported by the repaired Theorem 4.2: its
proof does not require UUS. -/
theorem finiteDimensional_generation_scale_invariance_all_positive
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : GenLimit.Generic.LanguageClass E}
    {δ δ' ε ε' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hε : 0 < ε) (hε' : 0 < ε') :
    (UniformlyGeneratableAt
        (dist : E → E → ℝ) ε ε' H ↔
      UniformlyGeneratableAt
        (dist : E → E → ℝ) δ δ' H) ∧
    (NonuniformlyGeneratableAt
        (dist : E → E → ℝ) ε ε' H ↔
      NonuniformlyGeneratableAt
        (dist : E → E → ℝ) δ δ' H) :=
  doubling_generation_scale_invariance_all_positive
    (isDoublingDistance_dist_finiteDimensional E)
    (fun x ↦ dist_self x)
    (fun x y ↦ dist_comm x y)
    (fun x y z ↦ dist_triangle x y z)
    hδ hδ' hε hε'

/-! ## Corollary 4.3 -/

/-- Corollary 4.3, with the source's finite-dimensional real normed-space,
positive-scale, and UUS hypotheses retained exactly.

The UUS premise is not used by the repaired scale-invariance argument, but
is kept here so the declaration mirrors the printed corollary. -/
theorem corollary_4_3
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : GenLimit.Generic.LanguageClass E}
    {r δ δ' ε ε' : ℝ}
    (hr : 0 < r)
    (hUUS :
      UniformlyUnboundedSupportAt
        (dist : E → E → ℝ) r H)
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hε : 0 < ε) (hε' : 0 < ε') :
    (UniformlyGeneratableAt
        (dist : E → E → ℝ) ε ε' H ↔
      UniformlyGeneratableAt
        (dist : E → E → ℝ) δ δ' H) ∧
    (NonuniformlyGeneratableAt
        (dist : E → E → ℝ) ε ε' H ↔
      NonuniformlyGeneratableAt
        (dist : E → E → ℝ) δ δ' H) := by
  have _hUUSAtEveryPositiveScale :=
    theorem_4_1_doubling_uus_scale_invariance
      (isDoublingDistance_dist_finiteDimensional E)
      hr hUUS
  exact
    finiteDimensional_generation_scale_invariance_all_positive
      E hδ hδ' hε hε'

end GenLimit.MetricSpaces
