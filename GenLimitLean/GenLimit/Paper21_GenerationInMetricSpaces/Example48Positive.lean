import GenLimit.Paper21_GenerationInMetricSpaces.HilbertAxisReservoir
import Mathlib.Tactic

/-!
# Example 4.8: the repaired causal positive path

Source: Jiaxun Li, Vinod Raman, and Ambuj Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1, Example 4.8 and
Appendix C.3, Case 1.

This file closes the deterministic positive construction left open by
`HilbertAxisReservoir`:

* it defines the source support
  `{0} ∪ U_{I₁} ∪ O_{I₂} ∪ D_{I₃}`;
* it proves that every point of that support lies on a standard axis;
* it proves that the even marker `a_(2k)` is isolated at radius `ε`;
* it defines one causal finite-history generator, which first recognizes a
  nondegenerate marker and then chooses a fresh point from its power
  reservoir;
* it proves generation in the limit whenever
  `0 < γ < ε` and `0 < γ' < ε'`.

The repair is explicit.  The printed proof chooses an arbitrary observed
marker, although its reservoir is a singleton when `k = 1`.  Here the
generator waits for a marker with `2 ≤ k`; every source index set is
infinite, so such a marker is forced into every sufficiently fine
presentation.

The two negative regimes are not asserted here.  They still depend on the
paper's defective infinite-row lemma, whose hypotheses do not make the
revealed rows target-valued.
-/

namespace GenLimit.MetricSpaces
namespace HilbertAxisReservoir

noncomputable section

/-! ## The exact source support -/

/-- The source origin, represented on the zeroth standard axis. -/
def example48Zero : Hilbert2 :=
  axisPoint 0 0

/-- The source set `U_I = {u_k | k ∈ I}`. -/
def example48USet (r : ℝ) (I : Set ℕ) : Set Hilbert2 :=
  {x | ∃ k ∈ I, x = example48U r k}

/-- The source disturbing set `D_I = {g_(2k+1) | k ∈ I}`. -/
def example48Disturbing (ε' : ℝ) (I : Set ℕ) : Set Hilbert2 :=
  {x | ∃ k ∈ I, x = example48G ε' (2 * k + 1)}

/-- The literal support of `h_(I₁,I₂,I₃)` from Example 4.8. -/
def example48Language
    (r ε ε' : ℝ) (I₁ I₂ I₃ : Set ℕ) : Set Hilbert2 :=
  {example48Zero} ∪
    (example48USet r I₁ ∪
      (example48Optimal ε ε' I₂ ∪
        example48Disturbing ε' I₃))

/-- The Example 4.8 class, with the source's infinitude requirement on all
three index sets. -/
def example48LanguageClass
    (r ε ε' : ℝ) : GenLimit.Generic.LanguageClass Hilbert2 :=
  {L | ∃ I₁ I₂ I₃ : Set ℕ,
    I₁.Infinite ∧ I₂.Infinite ∧ I₃.Infinite ∧
      L = example48Language r ε ε' I₁ I₂ I₃}

/-! ## Axis geometry and exact marker isolation -/

/-- Equality of two standard-axis points with nonzero left amplitude
determines both amplitude and coordinate. -/
theorem axisPoint_eq_axisPoint_of_left_ne_zero
    {c d : ℝ} (hc : c ≠ 0) {i j : ℕ}
    (h : axisPoint c i = axisPoint d j) :
    c = d ∧ i = j := by
  have hij : i = j := by
    by_contra hne
    have happ :=
      congrArg (fun x : Hilbert2 ↦ x i) h
    have hc0 : c = 0 := by
      simpa [axisPoint_apply_ne d hne] using happ
    exact hc hc0
  subst j
  have happ :=
    congrArg (fun x : Hilbert2 ↦ x i) h
  exact ⟨by simpa using happ, rfl⟩

/-- Looking at the common coordinate gives the same-axis amplitude lower
bound. -/
theorem abs_sub_amplitude_le_dist_axisPoint
    (c d : ℝ) (k : ℕ) :
    |c - d| ≤
      hilbertDistance (axisPoint c k) (axisPoint d k) := by
  change |c - d| ≤ dist (axisPoint c k) (axisPoint d k)
  rw [dist_eq_norm]
  have hcoordinate :
      ‖(axisPoint c k - axisPoint d k) k‖ = |c - d| := by
    rw [show
      (axisPoint c k - axisPoint d k) k =
        axisPoint c k k - axisPoint d k k by rfl]
    simp [Real.norm_eq_abs]
  rw [← hcoordinate]
  exact
    lp.norm_apply_le_norm
      (by norm_num : (2 : ENNReal) ≠ 0)
      (axisPoint c k - axisPoint d k) k

/-- Every point of the source support lies on a standard coordinate. -/
theorem example48Language_axisSupported
    (r ε ε' : ℝ) (I₁ I₂ I₃ : Set ℕ) :
    AxisSupported (example48Language r ε ε' I₁ I₂ I₃) := by
  intro x hx
  rcases hx with hx | hx
  · have hx0 : x = example48Zero := by simpa using hx
    exact ⟨0, 0, by simpa [example48Zero] using hx0⟩
  · rcases hx with hx | hx
    · obtain ⟨k, -, rfl⟩ := hx
      exact ⟨2 * r, k, rfl⟩
    · rcases hx with hx | hx
      · rcases hx with hx | hx
        · obtain ⟨k, -, rfl⟩ := hx
          exact ⟨ε, 2 * k, rfl⟩
        · obtain ⟨k, -, n, rfl⟩ := hx
          exact ⟨ε', 2 * k ^ n + 1, rfl⟩
      · obtain ⟨k, -, rfl⟩ := hx
        exact ⟨ε', 2 * k + 1, rfl⟩

/-! ## Uniformly unbounded support -/

/-- Every `ℓ²` point has only finitely many coordinates whose norm is at
least a fixed positive threshold. -/
theorem eventually_norm_apply_lt
    (x : Hilbert2) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k : ℕ in Filter.cofinite, ‖x k‖ < c := by
  have hsummable :
      Summable (fun k : ℕ ↦ ‖x k‖ ^ (2 : ℝ)) := by
    simpa using
      (lp.memℓp x).summable
        (by norm_num : 0 < (2 : ENNReal).toReal)
  have heventually :
      ∀ᶠ k : ℕ in Filter.cofinite,
        ‖x k‖ ^ (2 : ℝ) < c ^ (2 : ℝ) :=
    hsummable.tendsto_cofinite_zero.eventually_lt_const
      (by positivity)
  filter_upwards [heventually] with k hk
  have hnorm : 0 ≤ ‖x k‖ := norm_nonneg _
  simp only [Real.rpow_two] at hk
  nlinarith

/-- One remote axis point from an infinite index set escapes the closed
radius-`r` neighbourhood of any prescribed finite set of ambient centers. -/
theorem exists_example48U_outside_finite_neighborhood
    {r : ℝ} (hr : 0 < r) {I : Set ℕ} (hI : I.Infinite)
    (centers : Finset Hilbert2) :
    ∃ k ∈ I,
      example48U r k ∉
        closedNeighborhood hilbertDistance (centers : Set Hilbert2) r := by
  have hsmall :
      ∀ᶠ k : ℕ in Filter.cofinite,
        ∀ x ∈ centers, ‖x k‖ < r / 2 := by
    rw [Filter.eventually_all_finset]
    intro x _hx
    exact eventually_norm_apply_lt x (half_pos hr)
  have hbadFinite :
      {k : ℕ | ¬ ∀ x ∈ centers, ‖x k‖ < r / 2}.Finite :=
    Filter.eventually_cofinite.mp hsmall
  obtain ⟨k, hkI, hkGood⟩ :=
    hI.exists_notMem_finset hbadFinite.toFinset
  have hkSmall : ∀ x ∈ centers, ‖x k‖ < r / 2 := by
    by_contra hbad
    exact hkGood (hbadFinite.mem_toFinset.mpr hbad)
  refine ⟨k, hkI, ?_⟩
  intro hnear
  obtain ⟨x, hxCenters, hxNear⟩ :=
    hnear (3 * r / 2) (by linarith)
  have hxSmallNorm : ‖x k‖ < r / 2 := hkSmall x hxCenters
  have hxSmallAbs : |x k| < r / 2 := by
    simpa [Real.norm_eq_abs] using hxSmallNorm
  have hreverse := abs_sub_abs_le_abs_sub (2 * r) (x k)
  have hlowerAbs : 2 * r - |x k| ≤ |x k - 2 * r| := by
    rw [abs_of_pos (by positivity : 0 < 2 * r), abs_sub_comm] at hreverse
    exact hreverse
  have hlowerDist :
      |x k - 2 * r| ≤
        hilbertDistance x (example48U r k) := by
    change |x k - 2 * r| ≤ ‖x - example48U r k‖
    have hcoordinate :
        ‖(x - example48U r k) k‖ = |x k - 2 * r| := by
      rw [show
        (x - example48U r k) k = x k - 2 * r by
          simp [example48U, axisPoint]]
      exact Real.norm_eq_abs _
    rw [← hcoordinate]
    exact
      lp.norm_apply_le_norm
        (by norm_num : (2 : ENNReal) ≠ 0)
        (x - example48U r k) k
  have hfar : 3 * r / 2 < hilbertDistance x (example48U r k) := by
    linarith
  exact (not_lt_of_ge hfar.le hxNear)

/-- The source class in Example 4.8 has uniformly unbounded support at
radius `r`; the remote component `U_I` supplies the escaping points. -/
theorem example_4_8_uus
    {r ε ε' : ℝ} (hr : 0 < r) :
    UniformlyUnboundedSupportAt hilbertDistance r
      (example48LanguageClass r ε ε') := by
  intro L hL
  obtain ⟨I₁, I₂, I₃, hI₁, _hI₂, _hI₃, rfl⟩ := hL
  rintro ⟨centers, hcover⟩
  obtain ⟨k, hkI₁, hkOutside⟩ :=
    exists_example48U_outside_finite_neighborhood hr hI₁ centers
  apply hkOutside
  apply hcover
  right
  left
  exact ⟨k, hkI₁, rfl⟩

/-- Every source marker belongs to the source support. -/
theorem example48_marker_mem_language
    {r ε ε' : ℝ} {I₁ I₂ I₃ : Set ℕ}
    {k : ℕ} (hk : k ∈ I₂) :
    example48A ε (2 * k) ∈
      example48Language r ε ε' I₁ I₂ I₃ := by
  right
  right
  left
  left
  exact ⟨k, hk, rfl⟩

/-- A point syntactically equal to an even `a`-marker in the full support
must use an index from the optimal-set component. -/
theorem example48_marker_mem_language_iff
    {r ε ε' : ℝ} (hε : 0 < ε) (hεr : ε ≤ r)
    {I₁ I₂ I₃ : Set ℕ} {k : ℕ} :
    example48A ε (2 * k) ∈
        example48Language r ε ε' I₁ I₂ I₃ ↔
      k ∈ I₂ := by
  constructor
  · intro hx
    rcases hx with hx | hx
    · have heq :
          example48A ε (2 * k) = example48Zero := by
        simpa using hx
      have hamp :=
        (axisPoint_eq_axisPoint_of_left_ne_zero
          (ne_of_gt hε) heq).1
      exact (ne_of_gt hε) hamp |>.elim
    · rcases hx with hx | hx
      · obtain ⟨j, -, heq⟩ := hx
        have hamp :=
          (axisPoint_eq_axisPoint_of_left_ne_zero
            (ne_of_gt hε) heq).1
        linarith
      · rcases hx with hx | hx
        · rcases hx with hx | hx
          · obtain ⟨j, hj, heq⟩ := hx
            have hcoord :=
              (axisPoint_eq_axisPoint_of_left_ne_zero
                (ne_of_gt hε) heq).2
            have hjk : j = k := by omega
            simpa [hjk] using hj
          · obtain ⟨j, -, n, heq⟩ := hx
            have hcoord :=
              (axisPoint_eq_axisPoint_of_left_ne_zero
                (ne_of_gt hε) heq).2
            omega
        · obtain ⟨j, -, heq⟩ := hx
          have hcoord :=
            (axisPoint_eq_axisPoint_of_left_ne_zero
              (ne_of_gt hε) heq).2
          omega
  · exact example48_marker_mem_language

/-- In the complete source support, `a_(2k)` is isolated by the open
radius-`ε` ball.  This discharges the geometric premise left abstract in
`example_4_8_marker_from_presentation`. -/
theorem example48_marker_isolated
    {r ε ε' : ℝ} (hε : 0 < ε) (hεr : ε ≤ r)
    {I₁ I₂ I₃ : Set ℕ} {k : ℕ} (_hk : k ∈ I₂) :
    ∀ y ∈ example48Language r ε ε' I₁ I₂ I₃,
      hilbertDistance y (example48A ε (2 * k)) < ε →
        y = example48A ε (2 * k) := by
  intro y hy hclose
  rcases hy with hy | hy
  · have hy0 : y = example48Zero := by simpa using hy
    subst y
    have hfar :
        ε ≤
          hilbertDistance example48Zero
            (example48A ε (2 * k)) := by
      by_cases hcoord : 0 = 2 * k
      · rw [← hcoord]
        have hlower :=
          abs_sub_amplitude_le_dist_axisPoint 0 ε 0
        simpa [example48Zero, example48A, abs_of_pos hε] using hlower
      · have hlower :=
          abs_amplitude_le_dist_axisPoint_of_ne
            0 ε hcoord
        simpa [example48Zero, example48A, abs_of_pos hε] using hlower
    exact (not_lt_of_ge hfar hclose).elim
  · rcases hy with hy | hy
    · obtain ⟨j, -, rfl⟩ := hy
      by_cases hcoord : j = 2 * k
      · rw [hcoord]
        have hlower :=
          abs_sub_amplitude_le_dist_axisPoint
            (2 * r) ε (2 * k)
        have habs : ε ≤ |2 * r - ε| := by
          rw [abs_of_nonneg]
          · linarith
          · linarith
        have hfar :
            ε ≤
              hilbertDistance
                (example48U r (2 * k))
                (example48A ε (2 * k)) := by
          exact habs.trans (by
            simpa [example48U, example48A] using hlower)
        have hclose' :
            hilbertDistance
                (example48U r (2 * k))
                (example48A ε (2 * k)) < ε := by
          simpa [hcoord] using hclose
        exact (not_lt_of_ge hfar hclose').elim
      · have hfar :
            ε ≤
              hilbertDistance
                (example48U r j)
                (example48A ε (2 * k)) := by
          simpa [example48U, example48A, abs_of_pos hε] using
            abs_amplitude_le_dist_axisPoint_of_ne
              (2 * r) ε hcoord
        exact (not_lt_of_ge hfar hclose).elim
    · rcases hy with hy | hy
      · rcases hy with hy | hy
        · obtain ⟨j, -, rfl⟩ := hy
          by_cases hcoord : 2 * j = 2 * k
          · have hjk : j = k := by omega
            simp [hjk]
          · have hfar :
                ε ≤
                  hilbertDistance
                    (example48A ε (2 * j))
                    (example48A ε (2 * k)) := by
              simpa [example48A, abs_of_pos hε] using
                abs_amplitude_le_dist_axisPoint_of_ne
                  ε ε hcoord
            exact (not_lt_of_ge hfar hclose).elim
        · obtain ⟨j, -, n, rfl⟩ := hy
          have hcoord : 2 * j ^ n + 1 ≠ 2 * k := by omega
          have hfar :
              ε ≤
                hilbertDistance
                  (example48G ε' (2 * j ^ n + 1))
                  (example48A ε (2 * k)) := by
            simpa [example48G, example48A, abs_of_pos hε] using
              abs_amplitude_le_dist_axisPoint_of_ne
                ε' ε hcoord
          exact (not_lt_of_ge hfar hclose).elim
      · obtain ⟨j, -, rfl⟩ := hy
        have hcoord : 2 * j + 1 ≠ 2 * k := by omega
        have hfar :
            ε ≤
              hilbertDistance
                (example48G ε' (2 * j + 1))
                (example48A ε (2 * k)) := by
          simpa [example48G, example48A, abs_of_pos hε] using
            abs_amplitude_le_dist_axisPoint_of_ne
              ε' ε hcoord
        exact (not_lt_of_ge hfar hclose).elim

/-! ## A source-facing power reservoir for arbitrary target histories -/

/-- Refinement of the earlier arbitrary-stream wrapper which retains the
actual power exponent selected from the source reservoir. -/
theorem example_4_8_axisSupported_power_fresh
    {t k : ℕ} (hk : 2 ≤ k)
    {stream : GenLimit.Generic.Stream Hilbert2}
    {L : Set Hilbert2}
    (haxis : AxisSupported L)
    (hstream : GenLimit.Generic.StreamIn stream L)
    {ε' γ' : ℝ}
    (hε' : 0 < ε') (hγ' : γ' < ε') :
    ∃ n : ℕ,
      example48G ε' (2 * k ^ (n + 1) + 1) ∉
        closedNeighborhood hilbertDistance
          (GenLimit.Generic.sample stream t : Set Hilbert2)
          γ' := by
  classical
  have hrepresentation :
      ∀ i : Fin t,
        ∃ c : ℝ, ∃ q : ℕ,
          stream i = axisPoint c q := by
    intro i
    exact haxis (stream i) (hstream ⟨i, rfl⟩)
  choose amplitudes coordinates hcoordinates using hrepresentation
  obtain ⟨n, hnFresh⟩ :=
    example_4_8_power_reservoir_fresh
      hk amplitudes coordinates hε' hγ'
  refine ⟨n, ?_⟩
  intro hyNear
  apply hnFresh
  have hcenters :
      (GenLimit.Generic.sample stream t : Set Hilbert2) =
        Set.range
          (fun i : Fin t ↦
            axisPoint (amplitudes i) (coordinates i)) := by
    ext x
    constructor
    · intro hx
      change x ∈ GenLimit.Generic.sample stream t at hx
      rw [GenLimit.Generic.mem_sample_iff] at hx
      obtain ⟨i, hi, hix⟩ := hx
      refine ⟨⟨i, hi⟩, ?_⟩
      exact (hcoordinates ⟨i, hi⟩).symm.trans hix
    · rintro ⟨i, rfl⟩
      change
        axisPoint (amplitudes i) (coordinates i) ∈
          GenLimit.Generic.sample stream t
      rw [GenLimit.Generic.mem_sample_iff]
      exact ⟨i, i.isLt, hcoordinates i⟩
  rwa [← hcenters]

/-! ## One causal generator -/

/-- A candidate visible to the finite-history generator: a nondegenerate
even marker has appeared, and the output is a fresh member of that marker's
power reservoir. -/
def IsExample48CausalCandidate
    (ε ε' γ' : ℝ) {t : ℕ}
    (xs : Fin t → Hilbert2) (y : Hilbert2) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧
    (∃ i : Fin t, xs i = example48A ε (2 * k)) ∧
    ∃ n : ℕ,
      y = example48G ε' (2 * k ^ (n + 1) + 1) ∧
      y ∉
        closedNeighborhood hilbertDistance
          (GenLimit.Generic.sequenceSample xs : Set Hilbert2)
          γ'

/-- The repaired Case-1 generator.  Before a suitable marker/reservoir
certificate exists it returns the origin; afterwards it chooses a certified
fresh power point.  The choice depends only on the observed finite history. -/
noncomputable def example48CausalGenerator
    (ε ε' γ' : ℝ) : GenLimit.Generic.Generator Hilbert2 := by
  classical
  exact fun _ xs ↦
    if h : ∃ y, IsExample48CausalCandidate ε ε' γ' xs y then
        Classical.choose h
      else
        example48Zero

theorem example48CausalGenerator_spec
    {ε ε' γ' : ℝ} {t : ℕ} {xs : Fin t → Hilbert2}
    (h : ∃ y, IsExample48CausalCandidate ε ε' γ' xs y) :
    IsExample48CausalCandidate ε ε' γ' xs
      (example48CausalGenerator ε ε' γ' t xs) := by
  rw [example48CausalGenerator, dif_pos h]
  exact Classical.choose_spec h

/-- The single causal generator above succeeds on the whole source class.
The hypotheses retain the source's positive scale assumptions, even where
positivity is not needed by an individual geometric sublemma. -/
theorem example48CausalGenerator_isLimit
    {r ε ε' γ γ' : ℝ}
    (_hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hε' : 0 < ε') (_hε'r : ε' ≤ r)
    (_hγ : 0 < γ) (hγε : γ < ε)
    (_hγ' : 0 < γ') (hγ'ε' : γ' < ε') :
    IsLimitGeneratorAt hilbertDistance γ γ'
      (example48CausalGenerator ε ε' γ')
      (example48LanguageClass r ε ε') := by
  intro L hL stream hpres
  obtain ⟨I₁, I₂, I₃, hI₁, hI₂, hI₃, rfl⟩ := hL
  have haxis :
      AxisSupported (example48Language r ε ε' I₁ I₂ I₃) :=
    example48Language_axisSupported r ε ε' I₁ I₂ I₃
  have hisolated :
      ∀ k ∈ I₂, ∀ y ∈ example48Language r ε ε' I₁ I₂ I₃,
        hilbertDistance y (example48A ε (2 * k)) < ε →
          y = example48A ε (2 * k) := by
    intro k hk
    exact example48_marker_isolated hε hεr hk
  obtain ⟨s, k, hk, hkI₂, hs⟩ :=
    example_4_8_marker_from_presentation
      hγε hI₂
      (fun q hq ↦ example48_marker_mem_language hq)
      hisolated hpres
  refine ⟨s + 1, ?_⟩
  intro t ht
  have hpower :=
    example_4_8_axisSupported_power_fresh
      (t := t) hk haxis hpres.1 hε' hγ'ε'
  obtain ⟨n, hnFresh⟩ := hpower
  have hcandidate :
      ∃ y,
        IsExample48CausalCandidate ε ε' γ'
          (fun i : Fin t ↦ stream i) y := by
    refine
      ⟨example48G ε' (2 * k ^ (n + 1) + 1),
        k, hk, ?_, n, rfl, ?_⟩
    · exact
        ⟨⟨s, lt_of_lt_of_le (Nat.lt_succ_self s) ht⟩, hs⟩
    · rw [GenLimit.Generic.sequenceSample_prefix]
      exact hnFresh
  have hspec :
      IsExample48CausalCandidate ε ε' γ'
        (fun i : Fin t ↦ stream i)
        (GenLimit.Generic.output
          (example48CausalGenerator ε ε' γ') stream t) := by
    simpa [GenLimit.Generic.output] using
      example48CausalGenerator_spec hcandidate
  obtain
    ⟨q, hq, ⟨i, hiMarker⟩, m, hout, hnovel⟩ := hspec
  constructor
  · have hmarkerTarget :
        example48A ε (2 * q) ∈
          example48Language r ε ε' I₁ I₂ I₃ := by
      apply hpres.1
      exact ⟨i, hiMarker⟩
    have hqI₂ :
        q ∈ I₂ :=
      (example48_marker_mem_language_iff hε hεr).mp
        hmarkerTarget
    rw [hout]
    right
    right
    left
    exact example48G_mem_optimal hqI₂ (m + 1)
  · rw [GenLimit.Generic.sequenceSample_prefix] at hnovel
    exact hnovel

/-- Complete repaired positive path of Example 4.8. -/
theorem example_4_8_positive
    {r ε ε' γ γ' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hε' : 0 < ε') (hε'r : ε' ≤ r)
    (hγ : 0 < γ) (hγε : γ < ε)
    (hγ' : 0 < γ') (hγ'ε' : γ' < ε') :
    GeneratableInLimitAt hilbertDistance γ γ'
      (example48LanguageClass r ε ε') := by
  exact
    ⟨example48CausalGenerator ε ε' γ',
      example48CausalGenerator_isLimit
        hr hε hεr hε' hε'r hγ hγε hγ' hγ'ε'⟩

/-- A compact source-facing package for the completed positive portion of
Example 4.8: the class has `r`-UUS, and the displayed causal generator
witnesses generation below both threshold scales. -/
theorem example_4_8_positive_package
    {r ε ε' γ γ' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hε' : 0 < ε') (hε'r : ε' ≤ r)
    (hγ : 0 < γ) (hγε : γ < ε)
    (hγ' : 0 < γ') (hγ'ε' : γ' < ε') :
    UniformlyUnboundedSupportAt hilbertDistance r
        (example48LanguageClass r ε ε') ∧
      IsLimitGeneratorAt hilbertDistance γ γ'
          (example48CausalGenerator ε ε' γ')
          (example48LanguageClass r ε ε') ∧
        GeneratableInLimitAt hilbertDistance γ γ'
          (example48LanguageClass r ε ε') := by
  have hgen :=
    example48CausalGenerator_isLimit
      hr hε hεr hε' hε'r hγ hγε hγ' hγ'ε'
  exact
    ⟨example_4_8_uus hr, hgen,
      ⟨example48CausalGenerator ε ε' γ', hgen⟩⟩

end
end HilbertAxisReservoir
end GenLimit.MetricSpaces
