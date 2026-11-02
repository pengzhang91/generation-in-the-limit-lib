import GenLimit.Paper21_GenerationInMetricSpaces.CoveringGeometry
import Mathlib.Data.Finset.Union
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Ring

/-!
# UUS is scale-invariant in doubling spaces

Theorem 4.1 of Li--Raman--Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v2.
Doubling refines finite ambient covers to arbitrarily small radii. Replacing
used centers by covered points then gives a finite internal cover. Such a
cover contradicts UUS. Conversely, failure of a finite cover at three times
the presentation radius forces unbounded prefix covering numbers.
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

/-- In a doubling genuine metric, every finite ambient cover can be
internalized at any requested positive radius.

We first refine to radius `R/4`, strictly enlarge to a pointwise `R/3`
cover, and replace every used ambient center by a point of `A` in its ball.
The resulting internal centers cover `A` at radius `2R/3 < R`. -/
theorem finiteCover_internalize_at_positive_scale_of_doubling
    {ρ : Distance α} {r R : ℝ} {A : Set α}
    (hDoubling : IsDoublingDistance ρ)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle :
      ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (hr : 0 < r) (hR : 0 < R)
    (hcover : HasFiniteCover ρ r A) :
    HasFiniteInternalCover ρ R A := by
  classical
  let q := R / 4
  let p := R / 3
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hqp : q < p := by
    dsimp [q, p]
    linarith
  have hcoverQ :
      HasFiniteCover ρ q A :=
    finiteCover_all_positive_scales_of_doubling
      hDoubling hr hq hcover
  obtain ⟨outer, houter⟩ :=
    finiteCover_implies_finitePointCover_of_lt
      hqp hcoverQ
  let used : Finset α :=
    outer.filter fun z ↦
      ∃ y ∈ A, ρ z y ≤ p
  let representative : α → α :=
    fun z ↦
      if hz : ∃ y ∈ A, ρ z y ≤ p then
        Classical.choose hz
      else z
  let internal := used.image representative
  refine ⟨internal, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hzUsed, rfl⟩ :=
      Finset.mem_image.mp hx
    have hz :
        ∃ y ∈ A, ρ z y ≤ p :=
      (Finset.mem_filter.mp hzUsed).2
    change representative z ∈ A
    simp only [representative, dif_pos hz]
    exact (Classical.choose_spec hz).1
  · intro y hy η hRη
    obtain ⟨z, hzOuter, hzy⟩ := houter y hy
    have hz :
        ∃ a ∈ A, ρ z a ≤ p :=
      ⟨y, hy, hzy⟩
    have hzUsed : z ∈ used := by
      exact Finset.mem_filter.mpr ⟨hzOuter, hz⟩
    have hzrep :
        ρ z (representative z) ≤ p := by
      simp only [representative, dif_pos hz]
      exact (Classical.choose_spec hz).2
    have hrepz :
        ρ (representative z) z ≤ p := by
      rw [hsymm]
      exact hzrep
    have hrepY :
        ρ (representative z) y ≤ R := by
      calc
        ρ (representative z) y ≤
            ρ (representative z) z + ρ z y :=
          htriangle _ _ _
        _ ≤ p + p := add_le_add hrepz hzy
        _ ≤ R := by
          dsimp [p]
          linarith
    refine
      ⟨representative z,
        Finset.mem_image.mpr
          ⟨z, hzUsed, rfl⟩,
        hrepY.trans_lt hRη⟩

/-- Theorem 4.1: UUS at one positive radius implies UUS at every positive
radius in a doubling metric. The proof works with explicit metric laws and
does not need a separate separability premise. -/
theorem theorem_4_1_doubling_uus_scale_invariance
    {ρ : Distance α}
    {H : GenLimit.Generic.LanguageClass α} {r : ℝ}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle : ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (hr : 0 < r) (hUUS : UniformlyUnboundedSupportAt ρ r H) :
    ∀ r' : ℝ, 0 < r' → UniformlyUnboundedSupportAt ρ r' H := by
  intro r' hr'
  apply uus_of_no_finite_cover_triple hrefl hsymm htriangle hr'.le
  intro L hL hcover
  apply hUUS.not_finiteInternalCover hL
  exact finiteCover_internalize_at_positive_scale_of_doubling
    hDoubling hsymm htriangle (by positivity : 0 < 3 * r') hr hcover

end GenLimit.MetricSpaces
