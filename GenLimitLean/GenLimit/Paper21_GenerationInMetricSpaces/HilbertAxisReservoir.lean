import GenLimit.Paper21_GenerationInMetricSpaces.Definitions
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The standard-axis reservoir in Example 4.8

Source: Jiaxun Li, Vinod Raman, and Ambuj Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1, Example 4.8 and
Appendix C.3.

This file begins the source's infinite-dimensional examples inside the
actual Mathlib `ℓ²` space.  It checks the deterministic geometric ingredient
used in the positive regime of Example 4.8:

* standard-axis points really belong to `ℓ²`;
* a point of positive amplitude on a fresh coordinate is at least that
  amplitude away from every point of a finite standard-axis history;
* consequently, if `0 < γ' < ε'`, the source reservoir
  `{g_(2*k^n+1) | n ≥ 1}` always contains a member outside the closed
  radius-`γ'` neighbourhood of a finite history when `2 ≤ k`;
* when `k ∈ I`, that fresh point belongs to the source's optimal set `O_I`.
* isolated markers are extracted from arbitrary metric presentations, and
  arbitrary finite prefixes of axis-supported targets are converted to the
  standard-axis interface consumed by the reservoir theorem.

This is deliberately a deterministic presentation/reservoir wrapper, not
the full Example 4.8 separation.  Instantiating marker isolation for the
complete source class, packaging one causal generator, and repairing the
negative regimes' use of the defective infinite-row Lemma C.3 remain
outside this module.
-/

namespace GenLimit.MetricSpaces
namespace HilbertAxisReservoir

noncomputable section

/-- Mathlib's genuine real `ℓ²(ℕ)` space. -/
abbrev Hilbert2 := lp (fun _ : ℕ => ℝ) (2 : ENNReal)

/-- The point `c e_k` on the `k`-th standard axis of `ℓ²`. -/
def axisPoint (c : ℝ) (k : ℕ) : Hilbert2 :=
  lp.single (2 : ENNReal) k c

/-- The ordinary `ℓ²` distance, exposed as the paper's explicit kernel. -/
def hilbertDistance : Distance Hilbert2 :=
  fun x y ↦ dist x y

@[simp] theorem axisPoint_apply_self (c : ℝ) (k : ℕ) :
    axisPoint c k k = c := by
  exact
    lp.single_apply_self
      (E := fun _ : ℕ => ℝ) (2 : ENNReal) k c

@[simp] theorem axisPoint_apply_ne
    (c : ℝ) {i j : ℕ} (hji : j ≠ i) :
    axisPoint c i j = 0 := by
  exact
    lp.single_apply_ne
      (E := fun _ : ℕ => ℝ) (2 : ENNReal) i c hji

/-- Looking at the fresh coordinate alone gives the distance lower bound
needed by the source's reservoir argument. -/
theorem abs_amplitude_le_dist_axisPoint_of_ne
    (c d : ℝ) {i j : ℕ} (hij : i ≠ j) :
    |d| ≤ hilbertDistance (axisPoint c i) (axisPoint d j) := by
  change |d| ≤ dist (axisPoint c i) (axisPoint d j)
  rw [dist_eq_norm]
  have hcoordinate :
      ‖(axisPoint c i - axisPoint d j) j‖ = |d| := by
    rw [show
      (axisPoint c i - axisPoint d j) j =
        axisPoint c i j - axisPoint d j j by rfl]
    rw [axisPoint_apply_ne c hij.symm, axisPoint_apply_self]
    simp [Real.norm_eq_abs]
  rw [← hcoordinate]
  exact
    lp.norm_apply_le_norm
      (by norm_num : (2 : ENNReal) ≠ 0)
      (axisPoint c i - axisPoint d j) j

/-- An injective coordinate sequence has a value outside every finite list
of used coordinates. -/
theorem exists_injective_coordinate_not_used
    {t : ℕ} (sourceCoordinate : ℕ → ℕ)
    (hinjective : Function.Injective sourceCoordinate)
    (coordinates : Fin t → ℕ) :
    ∃ n : ℕ,
      sourceCoordinate n ∉ Finset.univ.image coordinates := by
  have hinfinite :
      (Set.range sourceCoordinate).Infinite :=
    Set.infinite_range_of_injective hinjective
  obtain ⟨x, ⟨n, rfl⟩, hx⟩ :=
    hinfinite.exists_notMem_finset (Finset.univ.image coordinates)
  exact ⟨n, hx⟩

/-- A positive-amplitude injective standard-axis sequence always has a point
outside the paper's closed neighbourhood of a finite standard-axis
history.  The history amplitudes are arbitrary. -/
theorem axisInjection_avoids_finite_history
    {t : ℕ} (sourceCoordinate : ℕ → ℕ)
    (hinjective : Function.Injective sourceCoordinate)
    (amplitudes : Fin t → ℝ) (coordinates : Fin t → ℕ)
    {γ c : ℝ} (hc : 0 < c) (hγc : γ < c) :
    ∃ n : ℕ,
      axisPoint c (sourceCoordinate n) ∉
        closedNeighborhood hilbertDistance
          (Set.range
            (fun i : Fin t ↦ axisPoint (amplitudes i) (coordinates i)))
          γ := by
  obtain ⟨n, hnFresh⟩ :=
    exists_injective_coordinate_not_used
      sourceCoordinate hinjective coordinates
  refine ⟨n, ?_⟩
  intro hnear
  let η : ℝ := (γ + c) / 2
  have hγη : γ < η := by
    dsimp [η]
    linarith
  obtain ⟨x, hxHistory, hxNear⟩ := hnear η hγη
  obtain ⟨i, rfl⟩ := hxHistory
  have hcoordinate :
      coordinates i ≠ sourceCoordinate n := by
    intro hEq
    apply hnFresh
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hEq⟩
  have hfar :
      c ≤
        hilbertDistance
          (axisPoint (amplitudes i) (coordinates i))
          (axisPoint c (sourceCoordinate n)) := by
    simpa [abs_of_pos hc] using
      abs_amplitude_le_dist_axisPoint_of_ne
        (amplitudes i) c hcoordinate
  dsimp [η] at hxNear
  linarith

section Example48

/-- The source point `u_k = 2r e_k`. -/
def example48U (r : ℝ) (k : ℕ) : Hilbert2 :=
  axisPoint (2 * r) k

/-- The source point `a_k = ε e_k`. -/
def example48A (ε : ℝ) (k : ℕ) : Hilbert2 :=
  axisPoint ε k

/-- The source point `g_k = ε' e_k`. -/
def example48G (ε' : ℝ) (k : ℕ) : Hilbert2 :=
  axisPoint ε' k

/-- The source's optimal set
`O_I = {a_(2k) | k ∈ I} ∪ {g_(2*k^n+1) | k ∈ I, n ∈ ℕ}`. -/
def example48Optimal (ε ε' : ℝ) (I : Set ℕ) : Set Hilbert2 :=
  {x | ∃ k ∈ I, x = example48A ε (2 * k)} ∪
    {x | ∃ k ∈ I, ∃ n : ℕ, x = example48G ε' (2 * k ^ n + 1)}

theorem example48G_mem_optimal
    {ε ε' : ℝ} {I : Set ℕ} {k : ℕ}
    (hkI : k ∈ I) (n : ℕ) :
    example48G ε' (2 * k ^ n + 1) ∈
      example48Optimal ε ε' I := by
  right
  exact ⟨k, hkI, n, rfl⟩

/-- Kernel-checked form of Appendix C.3's positive-case assertion that
`A_s = {g_(2*k^n+1) | n ≥ 1} \ B(history, γ')` is nonempty.

The theorem is stronger than the source use in one respect: the finite
history may contain arbitrary standard-axis amplitudes, not only points from
the constructed support.  The hypothesis `2 ≤ k` is the nondegeneracy
condition required for the displayed power sequence to be injective; the
printed source permits `k = 1`, where that assertion fails. -/
theorem example_4_8_power_reservoir_fresh
    {t k : ℕ} (hk : 2 ≤ k)
    (amplitudes : Fin t → ℝ) (coordinates : Fin t → ℕ)
    {ε' γ' : ℝ}
    (hε' : 0 < ε') (hγ' : γ' < ε') :
    ∃ n : ℕ,
      example48G ε' (2 * k ^ (n + 1) + 1) ∉
        closedNeighborhood hilbertDistance
          (Set.range
            (fun i : Fin t ↦ axisPoint (amplitudes i) (coordinates i)))
          γ' := by
  let sourceCoordinate : ℕ → ℕ :=
    fun n ↦ 2 * k ^ (n + 1) + 1
  have hinjective : Function.Injective sourceCoordinate := by
    intro n m hEq
    dsimp [sourceCoordinate] at hEq
    have hMul :
        2 * k ^ (n + 1) = 2 * k ^ (m + 1) :=
      Nat.add_right_cancel hEq
    have hPow :
        k ^ (n + 1) = k ^ (m + 1) :=
      Nat.mul_left_cancel (by norm_num) hMul
    have hSucc : n + 1 = m + 1 :=
      Nat.pow_right_injective hk hPow
    exact Nat.add_right_cancel hSucc
  obtain ⟨n, hnFresh⟩ :=
    axisInjection_avoids_finite_history
      sourceCoordinate hinjective amplitudes coordinates hε' hγ'
  exact ⟨n, by simpa [sourceCoordinate, example48G] using hnFresh⟩

/-- Optimal-set packaging of `example_4_8_power_reservoir_fresh`. -/
theorem example_4_8_optimal_reservoir_fresh
    {t k : ℕ} (hk : 2 ≤ k)
    (amplitudes : Fin t → ℝ) (coordinates : Fin t → ℕ)
    {ε ε' γ' : ℝ} {I : Set ℕ}
    (hkI : k ∈ I) (hε' : 0 < ε') (hγ' : γ' < ε') :
    ∃ y ∈ example48Optimal ε ε' I,
      y ∉
        closedNeighborhood hilbertDistance
          (Set.range
            (fun i : Fin t ↦ axisPoint (amplitudes i) (coordinates i)))
          γ' := by
  obtain ⟨n, hnFresh⟩ :=
    example_4_8_power_reservoir_fresh
      hk amplitudes coordinates hε' hγ'
  exact
    ⟨example48G ε' (2 * k ^ (n + 1) + 1),
      example48G_mem_optimal hkI (n + 1), hnFresh⟩

/-! ## Presentation and arbitrary-stream wrappers -/

/-- Every target point lies on a standard axis (zero amplitude is allowed). -/
def AxisSupported (L : Set Hilbert2) : Prop :=
  ∀ x ∈ L, ∃ c : ℝ, ∃ k : ℕ, x = axisPoint c k

/-- A point isolated inside the target at a scale strictly larger than the
presentation radius must literally occur in the presentation. -/
theorem isolated_target_point_mem_presentation
    {α : Type*} {ρ : Distance α}
    {γ δ : ℝ} (hγδ : γ < δ)
    {stream : GenLimit.Generic.Stream α} {L : Set α}
    (hpres : MetricPresentation ρ γ stream L)
    {x : α} (hxL : x ∈ L)
    (hisolated :
      ∀ y ∈ L, ρ y x < δ → y = x) :
    x ∈ Set.range stream := by
  obtain ⟨y, hyRange, hyClose⟩ :=
    hpres.2 hxL δ hγδ
  have hyL : y ∈ L := hpres.1 hyRange
  have hyx : y = x := hisolated y hyL hyClose
  exact hyx ▸ hyRange

/-- The existing axis-reservoir theorem applies to an arbitrary finite
stream prefix as soon as the containing target is axis-supported. -/
theorem example_4_8_axisSupported_reservoir_fresh
    {t k : ℕ} (hk : 2 ≤ k)
    {stream : GenLimit.Generic.Stream Hilbert2}
    {L : Set Hilbert2}
    (haxis : AxisSupported L)
    (hstream : GenLimit.Generic.StreamIn stream L)
    {ε ε' γ' : ℝ} {I : Set ℕ}
    (hkI : k ∈ I) (hε' : 0 < ε') (hγ' : γ' < ε') :
    ∃ y ∈ example48Optimal ε ε' I,
      y ∉
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
  obtain ⟨y, hyOptimal, hyFresh⟩ :=
    example_4_8_optimal_reservoir_fresh
      hk amplitudes coordinates hkI hε' hγ'
  refine ⟨y, hyOptimal, ?_⟩
  intro hyNear
  apply hyFresh
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
      exact
        ⟨i, i.isLt,
          hcoordinates i⟩
  rwa [← hcenters]

/-- Every infinite index set contains a nondegenerate marker `k ≥ 2`. -/
theorem infinite_indexSet_exists_two_le
    {I : Set ℕ} (hI : I.Infinite) :
    ∃ k ∈ I, 2 ≤ k := by
  obtain ⟨k, hkI, hkOutside⟩ :=
    hI.exists_notMem_finset (Finset.range 2)
  exact
    ⟨k, hkI,
      Nat.le_of_not_gt
        (fun hk ↦ hkOutside
          (Finset.mem_range.mpr hk))⟩

/-- Presentation-to-marker extraction for the positive regime.  The
isolation premise is the exact deterministic geometry still required from
the full Example 4.8 support definition. -/
theorem example_4_8_marker_from_presentation
    {γ ε : ℝ} (hγε : γ < ε)
    {stream : GenLimit.Generic.Stream Hilbert2}
    {L : Set Hilbert2} {I : Set ℕ}
    (hI : I.Infinite)
    (hmarkers :
      ∀ k ∈ I, example48A ε (2 * k) ∈ L)
    (hisolated :
      ∀ k ∈ I, ∀ y ∈ L,
        hilbertDistance y (example48A ε (2 * k)) < ε →
          y = example48A ε (2 * k))
    (hpres :
      MetricPresentation hilbertDistance γ stream L) :
    ∃ t k, 2 ≤ k ∧ k ∈ I ∧
      stream t = example48A ε (2 * k) := by
  obtain ⟨k, hkI, hk⟩ :=
    infinite_indexSet_exists_two_le hI
  have hmem :
      example48A ε (2 * k) ∈ Set.range stream :=
    isolated_target_point_mem_presentation hγε hpres
      (hmarkers k hkI) (hisolated k hkI)
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, k, hk, hkI, ht⟩

/-- Once a nondegenerate marker is forced to appear, every later
axis-supported finite history admits a fresh point of the source's optimal
reservoir.  This closes the deterministic presentation wrapper without yet
claiming the full history-dependent generator. -/
theorem example_4_8_presentation_reservoir
    {γ γ' ε ε' : ℝ}
    (hγε : γ < ε) (hε' : 0 < ε') (hγ' : γ' < ε')
    {stream : GenLimit.Generic.Stream Hilbert2}
    {L : Set Hilbert2} {I : Set ℕ}
    (hI : I.Infinite)
    (haxis : AxisSupported L)
    (hmarkers :
      ∀ k ∈ I, example48A ε (2 * k) ∈ L)
    (hisolated :
      ∀ k ∈ I, ∀ y ∈ L,
        hilbertDistance y (example48A ε (2 * k)) < ε →
          y = example48A ε (2 * k))
    (hpres :
      MetricPresentation hilbertDistance γ stream L) :
    ∃ T k, 2 ≤ k ∧ k ∈ I ∧
      ∀ t, T ≤ t →
        example48A ε (2 * k) ∈
            GenLimit.Generic.sample stream t ∧
          ∃ y ∈ example48Optimal ε ε' I,
            y ∉
              closedNeighborhood hilbertDistance
                (GenLimit.Generic.sample stream t : Set Hilbert2)
                γ' := by
  obtain ⟨s, k, hk, hkI, hs⟩ :=
    example_4_8_marker_from_presentation
      hγε hI hmarkers hisolated hpres
  refine ⟨s + 1, k, hk, hkI, ?_⟩
  intro t ht
  constructor
  · rw [GenLimit.Generic.mem_sample_iff]
    exact
      ⟨s, lt_of_lt_of_le (Nat.lt_succ_self s) ht, hs⟩
  · exact example_4_8_axisSupported_reservoir_fresh
      hk haxis hpres.1 hkI hε' hγ'

end Example48

end
end HilbertAxisReservoir
end GenLimit.MetricSpaces
