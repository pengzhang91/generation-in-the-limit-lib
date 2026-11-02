import GenLimit.Paper21_GenerationInMetricSpaces.DoublingUUS
import GenLimit.Paper21_GenerationInMetricSpaces.NonuniformCharacterization
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Uniform and non-uniform generation in doubling spaces

Theorem 4.2 of Li--Raman--Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v2.
Quantitative doubling compares sample covering numbers. Refinement and
recentering preserve finite internal covers at every positive generator
radius, so the full closure-dimension characterizations transfer generation.
-/

namespace GenLimit.MetricSpaces

/-! ## Quantitative iteration of doubling covers -/

/-- One doubling refinement multiplies the number of point-cover centers
by at most the displayed doubling constant. -/
theorem finitePointCover_half_with_card
    {ρ : Distance α} {M : ℕ} {r : ℝ} {A : Set α}
    {outer : Finset α}
    (hrefine :
      ∀ x : α, ∀ s : ℝ, 0 < s →
        ∃ centers : Finset α,
          centers.card ≤ M ∧
            ∀ y : α, ρ x y ≤ s →
              ∃ z ∈ centers, ρ z y ≤ s / 2)
    (hr : 0 < r)
    (houter :
      ∀ y ∈ A, ∃ x ∈ outer, ρ x y ≤ r) :
    ∃ centers : Finset α,
      centers.card ≤ outer.card * M ∧
        ∀ y ∈ A, ∃ z ∈ centers, ρ z y ≤ r / 2 := by
  classical
  choose inner hinnerCard hinner using
    fun x : α ↦ hrefine x r hr
  refine
    ⟨outer.biUnion inner,
      Finset.card_biUnion_le_card_mul
        outer inner M (fun x _hx ↦ hinnerCard x),
      ?_⟩
  intro y hy
  obtain ⟨x, hxOuter, hxy⟩ := houter y hy
  obtain ⟨z, hzInner, hzy⟩ := hinner x y hxy
  exact
    ⟨z, Finset.mem_biUnion.mpr
      ⟨x, hxOuter, hzInner⟩, hzy⟩

/-- After `n` doubling refinements, the radius is multiplied by
`(1/2)^n` and the number of centers by at most `M^n`. -/
theorem finitePointCover_halving_iterate_with_card
    {ρ : Distance α} {M : ℕ} {r : ℝ} {A : Set α}
    {outer : Finset α}
    (hrefine :
      ∀ x : α, ∀ s : ℝ, 0 < s →
        ∃ centers : Finset α,
          centers.card ≤ M ∧
            ∀ y : α, ρ x y ≤ s →
              ∃ z ∈ centers, ρ z y ≤ s / 2)
    (hr : 0 < r)
    (houter :
      ∀ y ∈ A, ∃ x ∈ outer, ρ x y ≤ r) :
    ∀ n : ℕ,
      ∃ centers : Finset α,
        centers.card ≤ outer.card * M ^ n ∧
          ∀ y ∈ A, ∃ z ∈ centers,
            ρ z y ≤ r * (1 / 2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero =>
      exact ⟨outer, by simp, by simpa using houter⟩
  | succ n ih =>
      obtain ⟨previous, hpreviousCard, hprevious⟩ := ih
      have hrn :
          0 < r * (1 / 2 : ℝ) ^ n := by
        positivity
      obtain ⟨centers, hcentersCard, hcenters⟩ :=
        finitePointCover_half_with_card
          hrefine hrn hprevious
      refine ⟨centers, ?_, ?_⟩
      · calc
          centers.card ≤ previous.card * M :=
            hcentersCard
          _ ≤ (outer.card * M ^ n) * M :=
            Nat.mul_le_mul_right M hpreviousCard
          _ = outer.card * M ^ (n + 1) := by
            simp [pow_succ, Nat.mul_assoc]
      · intro y hy
        obtain ⟨z, hz, hzy⟩ := hcenters y hy
        refine ⟨z, hz, ?_⟩
        convert hzy using 1
        rw [pow_succ]
        ring

/-- A doubling constant gives a uniform multiplicative comparison between
covering numbers at any two positive radii.  The conclusion is phrased in
the exact/lower-bound predicates used by the source-facing definitions. -/
theorem exists_coveringNumber_comparison_constant_of_doubling
    {ρ : Distance α} {ε δ : ℝ}
    (hDoubling : IsDoublingDistance ρ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ K : ℕ, 0 < K ∧
      ∀ (A : Set α) (d e : ℕ),
        CoveringNumberEq ρ ε A e →
          CoveringNumberAtLeast ρ δ A d →
            d ≤ e * K := by
  classical
  obtain ⟨M, hM, hrefine⟩ := hDoubling
  let R := ε + δ
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hεR : ε < R := by
    dsimp [R]
    linarith
  obtain ⟨n, hn⟩ :
      ∃ n : ℕ,
        (1 / 2 : ℝ) ^ n < δ / R :=
    exists_pow_lt_of_lt_one
      (div_pos hδ hR) (by norm_num)
  have hscale :
      R * (1 / 2 : ℝ) ^ n ≤ δ := by
    have :=
      (lt_div_iff₀ hR).mp hn
    nlinarith
  refine ⟨M ^ n, Nat.pow_pos hM, ?_⟩
  intro A d e hEq hLower
  obtain ⟨outer, houterCard, houterCover⟩ := hEq.2
  have hpointR :
      ∀ y ∈ A, ∃ x ∈ outer, ρ x y ≤ R := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ :=
      houterCover hy R hεR
    exact ⟨x, hx, hxy.le⟩
  obtain ⟨centers, hcentersCard, hcenters⟩ :=
    finitePointCover_halving_iterate_with_card
      hrefine hR hpointR n
  have hpointδ :
      ∀ y ∈ A, ∃ x ∈ centers, ρ x y ≤ δ := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hcenters y hy
    exact ⟨x, hx, hxy.trans hscale⟩
  have hclosedδ :
      A ⊆ closedNeighborhood ρ (centers : Set α) δ := by
    intro y hy η hδη
    obtain ⟨x, hx, hxy⟩ := hpointδ y hy
    exact ⟨x, hx, hxy.trans_lt hδη⟩
  calc
    d ≤ centers.card := hLower centers hclosedδ
    _ ≤ outer.card * M ^ n := hcentersCard
    _ = e * M ^ n := by rw [houterCard]

/-! ## Internalizing ambient covers in a doubling metric -/

/-! ## Scale-closure dimension transport -/

/-- A finite closure-dimension bound at smaller positive scales remains a
bound when both scales are enlarged. -/
theorem finiteScaleClosureDimension_to_larger_scales_of_doubling
    {ρ : Distance α} {δ δ' ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle : ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hε' : 0 < ε')
    (hδε : δ ≤ ε)
    (hdim :
      HasFiniteScaleClosureDimension ρ δ δ' H) :
    HasFiniteScaleClosureDimension ρ ε ε' H := by
  obtain ⟨D, hD⟩ := hdim
  refine ⟨D, ?_⟩
  intro d hDd
  rintro ⟨S, hversion, hEqε, hcoreε'⟩
  obtain ⟨e, hEqδ⟩ :=
    finset_exists_coveringNumberEq
      (ρ := ρ) hrefl hδ.le S
  have hde : d ≤ e := by
    obtain ⟨centers, hcard, hcover⟩ := hEqδ.2
    have hlowerδ :
        CoveringNumberAtLeast ρ δ (S : Set α) d :=
      coveringNumberAtLeast_anti_radius hδε hEqε.1
    rw [← hcard]
    exact hlowerδ centers hcover
  have hcoreδ' :
      HasFiniteInternalCover ρ δ' (commonCore H S) :=
    finiteCover_internalize_at_positive_scale_of_doubling
      hDoubling hsymm htriangle hε' hδ' hcoreε'.toFiniteCover
  exact
    hD e (hDd.trans_le hde)
      ⟨S, hversion, hEqδ, hcoreδ'⟩

/-- A finite closure-dimension bound at larger positive scales remains
finite when both scales are decreased.  The sample-side bound is multiplied
by the uniform doubling comparison constant. -/
theorem finiteScaleClosureDimension_to_smaller_scales_of_doubling
    {ρ : Distance α} {δ δ' ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hδ'ε' : δ' ≤ ε')
    (hdim :
      HasFiniteScaleClosureDimension ρ ε ε' H) :
    HasFiniteScaleClosureDimension ρ δ δ' H := by
  obtain ⟨K, _hK, hcompare⟩ :=
    exists_coveringNumber_comparison_constant_of_doubling
      hDoubling hε hδ
  obtain ⟨D, hD⟩ := hdim
  refine ⟨D * K, ?_⟩
  intro d hDKd
  rintro ⟨S, hversion, hEqδ, hcoreδ'⟩
  obtain ⟨e, hEqε⟩ :=
    finset_exists_coveringNumberEq
      (ρ := ρ) hrefl hε.le S
  have hdeK : d ≤ e * K :=
    hcompare (S : Set α) d e hEqε hEqδ.1
  have hDe : D < e := by
    by_contra hnot
    have heD : e ≤ D := Nat.le_of_not_gt hnot
    have heKDK : e * K ≤ D * K :=
      Nat.mul_le_mul_right K heD
    exact (Nat.not_le_of_gt hDKd)
      (hdeK.trans heKDK)
  have hcoreε' :
      HasFiniteInternalCover ρ ε' (commonCore H S) :=
    finiteInternalCover_mono_radius hδ'ε' hcoreδ'
  exact hD e hDe ⟨S, hversion, hEqε, hcoreε'⟩

/-- In a doubling metric, finiteness of the scale-closure dimension is
independent of the ordered pair of positive scales. -/
theorem finiteScaleClosureDimension_iff_of_doubling
    {ρ : Distance α} {δ δ' ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle : ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hε : 0 < ε) (hε' : 0 < ε')
    (hδε : δ ≤ ε) (hδ'ε' : δ' ≤ ε') :
    HasFiniteScaleClosureDimension ρ ε ε' H ↔
      HasFiniteScaleClosureDimension ρ δ δ' H := by
  constructor
  · exact
      finiteScaleClosureDimension_to_smaller_scales_of_doubling
        hDoubling hrefl hε hδ hδ'ε'
  · exact
      finiteScaleClosureDimension_to_larger_scales_of_doubling
        hDoubling hrefl hsymm htriangle hδ hδ' hε' hδε

/-! ## Theorem 4.2 -/

/-- Uniform half of Theorem 4.2.  The UUS premise used by the printed
characterization is unnecessary after the doubling-metric internalization
argument is made explicit. -/
theorem theorem_4_2_uniform_scale_invariance
    {ρ : Distance α} {δ δ' ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle :
      ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hε : 0 < ε) (hε' : 0 < ε')
    (hδε : δ ≤ ε) (hδ'ε' : δ' ≤ ε') :
    UniformlyGeneratableAt ρ ε ε' H ↔
      UniformlyGeneratableAt ρ δ δ' H := by
  have hdimIff :=
    finiteScaleClosureDimension_iff_of_doubling
      (H := H) hDoubling hrefl hsymm htriangle hδ hδ'
        hε hε' hδε hδ'ε'
  constructor
  · intro hUniform
    obtain ⟨gen, threshold, hgen⟩ := hUniform
    letI : Nonempty α := ⟨gen 0 Fin.elim0⟩
    apply
      finite_scaleClosureDimension_implies_uniform
        hrefl hδ.le
    apply hdimIff.mp
    exact uniform_implies_finite_scaleClosureDimension ⟨gen, threshold, hgen⟩
  · intro hUniform
    obtain ⟨gen, threshold, hgen⟩ := hUniform
    letI : Nonempty α := ⟨gen 0 Fin.elim0⟩
    apply
      finite_scaleClosureDimension_implies_uniform
        hrefl hε.le
    apply hdimIff.mpr
    exact uniform_implies_finite_scaleClosureDimension ⟨gen, threshold, hgen⟩

/-- Non-uniform half of Theorem 4.2, obtained by transporting every member
of the checked nondecreasing uniform cover characterization. -/
theorem theorem_4_2_nonuniform_scale_invariance
    {ρ : Distance α} {δ δ' ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle :
      ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hε : 0 < ε) (hε' : 0 < ε')
    (hδε : δ ≤ ε) (hδ'ε' : δ' ≤ ε') :
    NonuniformlyGeneratableAt ρ ε ε' H ↔
      NonuniformlyGeneratableAt ρ δ δ' H := by
  have hUniformIff :
      ∀ K : GenLimit.Generic.LanguageClass α,
        UniformlyGeneratableAt ρ ε ε' K ↔
          UniformlyGeneratableAt ρ δ δ' K :=
    fun K ↦
      theorem_4_2_uniform_scale_invariance
        (H := K) hDoubling hrefl hsymm htriangle
          hδ hδ' hε hε' hδε hδ'ε'
  constructor
  · intro hNonuniform
    obtain ⟨classes, hcover, hUniform⟩ :=
      nonuniform_implies_nondecreasing_uniform_cover
        hNonuniform
    apply
      nondecreasing_uniform_cover_implies_nonuniform
        (fun x ↦ by rw [hrefl x]; exact hδ.le)
        hcover
    intro n
    exact (hUniformIff (classes n)).mp (hUniform n)
  · intro hNonuniform
    obtain ⟨classes, hcover, hUniform⟩ :=
      nonuniform_implies_nondecreasing_uniform_cover
        hNonuniform
    apply
      nondecreasing_uniform_cover_implies_nonuniform
        (fun x ↦ by rw [hrefl x]; exact hε.le)
        hcover
    intro n
    exact (hUniformIff (classes n)).mpr (hUniform n)

/-- Theorem 4.2 (`thm:doubling-eps-uniformgen`), with the source's strict
positive scale inequalities and UUS premise retained.

The proof above establishes the stronger fact that UUS is not needed for
this scale-invariance conclusion. -/
theorem theorem_4_2_doubling_generation_scale_invariance
    {ρ : Distance α} {δ δ' ε ε' r : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle :
      ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (_hr : 0 < r)
    (_hUUS : UniformlyUnboundedSupportAt ρ r H)
    (hδ : 0 < δ) (hδε : δ < ε)
    (hδ' : 0 < δ') (hδ'ε' : δ' < ε') :
    (UniformlyGeneratableAt ρ ε ε' H ↔
      UniformlyGeneratableAt ρ δ δ' H) ∧
    (NonuniformlyGeneratableAt ρ ε ε' H ↔
      NonuniformlyGeneratableAt ρ δ δ' H) := by
  have hε : 0 < ε := hδ.trans hδε
  have hε' : 0 < ε' := hδ'.trans hδ'ε'
  exact
    ⟨theorem_4_2_uniform_scale_invariance
        hDoubling hrefl hsymm htriangle
          hδ hδ' hε hε' hδε.le hδ'ε'.le,
      theorem_4_2_nonuniform_scale_invariance
        hDoubling hrefl hsymm htriangle
          hδ hδ' hε hε' hδε.le hδ'ε'.le⟩

end GenLimit.MetricSpaces
