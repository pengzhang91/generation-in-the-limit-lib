import GenLimit.Paper21_GenerationInMetricSpaces.Definitions
import Mathlib.Data.Finset.Union
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Ring

/-!
# Unbounded support is scale-invariant in doubling spaces

This module formalizes Theorem 4.1 (`thm:doubling-UUS`) of
Jiaxun Li, Vinod Raman, and Ambuj Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1.

The source defines a doubling metric space by a uniform finite cover of
every radius-`r` ball by radius-`r / 2` balls.  Iterating those finite
refinements shows that a finite cover at one positive radius yields a finite
cover at every other positive radius.  Consequently infinite covering
number, and hence uniformly unbounded support, is independent of the
positive scale.

The definitions below use closed balls, matching the paper's explicit
closed-neighbourhood convention.  The proof only needs the displayed
doubling-cover property; the surrounding paper assumption that `ρ` is a
genuine metric is therefore not repeated theorem-by-theorem.
-/

namespace GenLimit.MetricSpaces

/-- A finite pointwise radius-`r` cover.  Unlike `HasFiniteCover`, this
records an actual center whose distance is at most `r`. -/
def HasFinitePointCover
    (ρ : Distance α) (r : ℝ) (A : Set α) : Prop :=
  ∃ centers : Finset α,
    ∀ y ∈ A, ∃ x ∈ centers, ρ x y ≤ r

/-- Definition 4.1's doubling condition, stated with the paper's closed
balls: one uniform finite bound covers every positive-radius ball by balls
of half the radius. -/
def IsDoublingDistance (ρ : Distance α) : Prop :=
  ∃ M : ℕ, 0 < M ∧
    ∀ x : α, ∀ r : ℝ, 0 < r →
      ∃ centers : Finset α,
        centers.card ≤ M ∧
          ∀ y : α, ρ x y ≤ r →
            ∃ z ∈ centers, ρ z y ≤ r / 2

/-- A pointwise cover is a cover in the paper's closed-neighbourhood
encoding. -/
theorem finitePointCover_implies_finiteCover
    {ρ : Distance α} {r : ℝ} {A : Set α}
    (hcover : HasFinitePointCover ρ r A) :
    HasFiniteCover ρ r A := by
  obtain ⟨centers, hcenters⟩ := hcover
  refine ⟨centers, ?_⟩
  intro y hy η hrη
  obtain ⟨x, hx, hxy⟩ := hcenters y hy
  exact ⟨x, hx, hxy.trans_lt hrη⟩

/-- Enlarging the radius turns a finite closed-neighbourhood cover into a
pointwise cover.  The strict enlargement avoids choosing a nearest center
from the infimum-style definition of `closedNeighborhood`. -/
theorem finiteCover_implies_finitePointCover_of_lt
    {ρ : Distance α} {r R : ℝ} {A : Set α}
    (hrR : r < R)
    (hcover : HasFiniteCover ρ r A) :
    HasFinitePointCover ρ R A := by
  obtain ⟨centers, hcenters⟩ := hcover
  refine ⟨centers, ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hcenters hy R hrR
  exact ⟨x, hx, hxy.le⟩

/-- Pointwise finite covers are monotone in the radius. -/
theorem finitePointCover_mono_radius
    {ρ : Distance α} {r R : ℝ} {A : Set α}
    (hrR : r ≤ R)
    (hcover : HasFinitePointCover ρ r A) :
    HasFinitePointCover ρ R A := by
  obtain ⟨centers, hcenters⟩ := hcover
  exact
    ⟨centers, fun y hy ↦
      let ⟨x, hx, hxy⟩ := hcenters y hy
      ⟨x, hx, hxy.trans hrR⟩⟩

/-- One application of doubling refines a pointwise finite cover to half
its radius. -/
theorem finitePointCover_half_of_doubling
    {ρ : Distance α} {r : ℝ} {A : Set α}
    (hDoubling : IsDoublingDistance ρ)
    (hr : 0 < r)
    (hcover : HasFinitePointCover ρ r A) :
    HasFinitePointCover ρ (r / 2) A := by
  classical
  obtain ⟨_M, _hM, hrefine⟩ := hDoubling
  obtain ⟨outer, houter⟩ := hcover
  choose inner _hinnerCard hinner using
    fun x : α ↦ hrefine x r hr
  refine ⟨outer.biUnion inner, ?_⟩
  intro y hy
  obtain ⟨x, hxOuter, hxy⟩ := houter y hy
  obtain ⟨z, hzInner, hzy⟩ := hinner x y hxy
  exact
    ⟨z, Finset.mem_biUnion.mpr
      ⟨x, hxOuter, hzInner⟩, hzy⟩

/-- Iterating the half-radius refinement produces a finite cover at radius
`r * (1 / 2)^n`. -/
theorem finitePointCover_halving_iterate
    {ρ : Distance α} {r : ℝ} {A : Set α}
    (hDoubling : IsDoublingDistance ρ)
    (hr : 0 < r)
    (hcover : HasFinitePointCover ρ r A) :
    ∀ n : ℕ,
      HasFinitePointCover ρ
        (r * (1 / 2 : ℝ) ^ n) A := by
  intro n
  induction n with
  | zero =>
      simpa using hcover
  | succ n ih =>
      have hrn :
          0 < r * (1 / 2 : ℝ) ^ n := by
        positivity
      have hhalf :=
        finitePointCover_half_of_doubling
          hDoubling hrn ih
      convert hhalf using 1
      rw [pow_succ]
      ring

/-- In a doubling space, a finite cover at any positive radius can be
refined to a finite cover at every other positive radius. -/
theorem finiteCover_all_positive_scales_of_doubling
    {ρ : Distance α} {r δ : ℝ} {A : Set α}
    (hDoubling : IsDoublingDistance ρ)
    (hr : 0 < r) (hδ : 0 < δ)
    (hcover : HasFiniteCover ρ r A) :
    HasFiniteCover ρ δ A := by
  let R := r + δ
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hrR : r < R := by
    dsimp [R]
    linarith
  have hpoint :
      HasFinitePointCover ρ R A :=
    finiteCover_implies_finitePointCover_of_lt
      hrR hcover
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
  apply finitePointCover_implies_finiteCover
  exact
    finitePointCover_mono_radius hscale
      (finitePointCover_halving_iterate
        hDoubling hR hpoint n)

/-- Theorem 4.1 (`thm:doubling-UUS`): on a doubling metric space, uniformly
unbounded support at one positive radius implies uniformly unbounded support
at every positive radius. -/
theorem theorem_4_1_doubling_uus_scale_invariance
    {ρ : Distance α}
    {H : GenLimit.Generic.LanguageClass α}
    {r : ℝ}
    (hDoubling : IsDoublingDistance ρ)
    (hr : 0 < r)
    (hUUS : UniformlyUnboundedSupportAt ρ r H) :
    ∀ r' : ℝ, 0 < r' →
      UniformlyUnboundedSupportAt ρ r' H := by
  intro r' hr' L hLH hfinite
  exact
    hUUS L hLH
      (finiteCover_all_positive_scales_of_doubling
        hDoubling hr' hr hfinite)

end GenLimit.MetricSpaces
