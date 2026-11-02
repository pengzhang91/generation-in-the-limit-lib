import GenLimit.Paper21_GenerationInMetricSpaces.CoveringGeometry
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Covering numbers of finite orthogonal samples

Appendix C.1, estimate (1), of arXiv:2602.07710v2. Centers are arbitrary
ambient points, as required by Definition 2.2. The argument works in every
real inner product space, including the weighted Hilbert space in Example 4.11.
-/

namespace GenLimit.MetricSpaces

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared norm of a sum of orthogonal points of the same norm. -/
theorem orthogonal_sum_norm_sq (S : Finset E) {R : ℝ}
    (hnorm : ∀ x ∈ S, ‖x‖ = R)
    (horth : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → inner ℝ x y = 0) :
    ‖∑ x ∈ S, x‖ ^ 2 = (S.card : ℝ) * R ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  calc
    ∑ x ∈ S, inner ℝ x (∑ y ∈ S, y) = ∑ _x ∈ S, R ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [inner_sum]
      calc
        ∑ y ∈ S, inner ℝ x y = ∑ y ∈ S, if y = x then R ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hxy : y = x
          · subst y; simp [real_inner_self_eq_norm_sq, hnorm x hx]
          · simp [hxy, horth x hx y hy (Ne.symm hxy)]
        _ = R ^ 2 := by simp [hx]
    _ = _ := by simp

/-- A radius-`η` ball contains at most `R² / (R² - η²)` mutually orthogonal
points of norm `R`. The denominator-free form also handles an empty sample. -/
theorem orthogonal_ball_card_bound (S : Finset E) {R η : ℝ} (z : E)
    (hη : 0 ≤ η) (hnorm : ∀ x ∈ S, ‖x‖ = R)
    (horth : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → inner ℝ x y = 0)
    (hball : ∀ x ∈ S, dist z x ≤ η) :
    (S.card : ℝ) * (R ^ 2 - η ^ 2) ≤ R ^ 2 := by
  classical
  by_cases hS : S.Nonempty
  · have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    have hsum : ∑ x ∈ S, ‖x - z‖ ^ 2 =
        (S.card : ℝ) * R ^ 2 - 2 * (∑ x ∈ S, inner ℝ x z) +
          (S.card : ℝ) * ‖z‖ ^ 2 := by
      simp_rw [norm_sub_sq_real]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [← Finset.mul_sum]
      congr 1
      congr 1
      calc
        ∑ x ∈ S, ‖x‖ ^ 2 = ∑ _x ∈ S, R ^ 2 :=
          Finset.sum_congr rfl (fun x hx => by rw [hnorm x hx])
        _ = _ := by simp
      all_goals simp
    have hvariance : 0 ≤ (S.card : ℝ) *
        ((∑ x ∈ S, ‖x - z‖ ^ 2) - ((S.card : ℝ) - 1) * R ^ 2) := by
      calc
        0 ≤ ‖(∑ x ∈ S, x) - (S.card : ℝ) • z‖ ^ 2 := sq_nonneg _
        _ = _ := by
          rw [norm_sub_sq_real, orthogonal_sum_norm_sq S hnorm horth,
            inner_smul_right, sum_inner, norm_smul, Real.norm_eq_abs,
            abs_of_pos hcard, hsum]
          ring
    have hlower : ((S.card : ℝ) - 1) * R ^ 2 ≤ ∑ x ∈ S, ‖x - z‖ ^ 2 := by
      have := (mul_nonneg_iff_of_pos_left hcard).mp hvariance
      linarith
    have hupper : (∑ x ∈ S, ‖x - z‖ ^ 2) ≤ (S.card : ℝ) * η ^ 2 := by
      calc
        _ ≤ ∑ _x ∈ S, η ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          have hb : ‖x - z‖ ≤ η := by simpa [dist_eq_norm, norm_sub_rev] using hball x hx
          nlinarith [norm_nonneg (x - z)]
        _ = _ := by simp
    nlinarith
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [this, sq_nonneg]

/-- Appendix C.1, estimate (1), expressed for any finite ambient cover:
`|S| (1 - η²/R²) ≤ |centers|`. -/
theorem orthogonal_covering_estimate (S centers : Finset E) {R η : ℝ}
    (hR : 0 < R) (hη : 0 ≤ η) (hηR : η < R)
    (hnorm : ∀ x ∈ S, ‖x‖ = R)
    (horth : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → inner ℝ x y = 0)
    (hcover : (S : Set E) ⊆ closedNeighborhood dist (centers : Set E) η) :
    (S.card : ℝ) * (1 - η ^ 2 / R ^ 2) ≤ centers.card := by
  classical
  let pieces := fun z : E => S.filter (fun x => dist z x ≤ η)
  have hsubset : S ⊆ centers.biUnion pieces := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := mem_closedNeighborhood_finset_iff.mp (hcover hx)
    exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_filter.mpr ⟨hx, hzx⟩⟩
  have hcardNat : S.card ≤ ∑ z ∈ centers, (pieces z).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have hcard : (S.card : ℝ) ≤ ∑ z ∈ centers, ((pieces z).card : ℝ) := by
    exact_mod_cast hcardNat
  have hweight : 0 ≤ R ^ 2 - η ^ 2 := by nlinarith
  have hbound : (S.card : ℝ) * (R ^ 2 - η ^ 2) ≤ (centers.card : ℝ) * R ^ 2 := by
    calc
      _ ≤ (∑ z ∈ centers, ((pieces z).card : ℝ)) * (R ^ 2 - η ^ 2) :=
        mul_le_mul_of_nonneg_right hcard hweight
      _ = ∑ z ∈ centers, ((pieces z).card : ℝ) * (R ^ 2 - η ^ 2) := Finset.sum_mul ..
      _ ≤ ∑ _z ∈ centers, R ^ 2 := by
        apply Finset.sum_le_sum
        intro z _
        apply orthogonal_ball_card_bound (pieces z) z hη
        · intro x hx; exact hnorm x (Finset.mem_filter.mp hx).1
        · intro x hx y hy hxy
          exact horth x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
        · intro x hx; exact (Finset.mem_filter.mp hx).2
      _ = _ := by simp
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hR)).mp
  nlinarith [div_mul_cancel₀ (η ^ 2) (ne_of_gt (sq_pos_of_pos hR))]

/-- Natural-number lower bounds obtained from the real-valued estimate. -/
theorem coveringNumberAtLeast_of_orthogonal (S : Finset E) {R η : ℝ} {d : ℕ}
    (hR : 0 < R) (hη : 0 ≤ η) (hηR : η < R)
    (hnorm : ∀ x ∈ S, ‖x‖ = R)
    (horth : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → inner ℝ x y = 0)
    (hd : (d : ℝ) ≤ (S.card : ℝ) * (1 - η ^ 2 / R ^ 2)) :
    CoveringNumberAtLeast dist η (S : Set E) d := by
  intro centers hcover
  exact_mod_cast hd.trans (orthogonal_covering_estimate S centers hR hη hηR hnorm horth hcover)

/-- Every infinite orthogonal family of fixed norm yields arbitrarily large
finite-sample covering numbers below that norm. -/
theorem infinite_orthogonal_has_large_finite_sample {A : Set E} {R η : ℝ}
    (hA : A.Infinite) (hR : 0 < R) (hη : 0 ≤ η) (hηR : η < R)
    (hnorm : ∀ x ∈ A, ‖x‖ = R)
    (horth : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → inner ℝ x y = 0) (d : ℕ) :
    ∃ S : Finset E, (S : Set E) ⊆ A ∧ CoveringNumberAtLeast dist η (S : Set E) d := by
  have hw : 0 < 1 - η ^ 2 / R ^ 2 := by
    have hsq : η ^ 2 < R ^ 2 := by nlinarith
    exact sub_pos.mpr ((div_lt_one (sq_pos_of_pos hR)).mpr hsq)
  obtain ⟨n, hn⟩ := exists_nat_gt ((d : ℝ) / (1 - η ^ 2 / R ^ 2))
  obtain ⟨S, hS, hcard⟩ := hA.exists_subset_card_eq n
  refine ⟨S, hS, coveringNumberAtLeast_of_orthogonal S hR hη hηR
    (fun x hx => hnorm x (hS hx))
    (fun x hx y hy hxy => horth x (hS hx) y (hS hy) hxy) ?_⟩
  rw [hcard]
  exact ((div_lt_iff₀ hw).mp hn).le

/-- An infinite orthogonal subfamily in a stream forces its prefix covering
numbers to diverge. No coverage assumption on the stream is necessary. -/
theorem prefix_covering_unbounded_of_infinite_orthogonal
    {A : Set E} {R η : ℝ} {stream : GenLimit.Generic.Stream E}
    (hA : A.Infinite) (hstream : A ⊆ Set.range stream)
    (hR : 0 < R) (hη : 0 ≤ η) (hηR : η < R)
    (hnorm : ∀ x ∈ A, ‖x‖ = R)
    (horth : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → inner ℝ x y = 0) (d : ℕ) :
    ∃ t, CoveringNumberAtLeast dist η (GenLimit.Generic.sample stream t : Set E) d := by
  obtain ⟨S, hS, hd⟩ := infinite_orthogonal_has_large_finite_sample hA hR hη hηR hnorm horth d
  obtain ⟨t, ht⟩ := GenLimit.Generic.finset_eventually_subset_sample rfl S (hS.trans hstream)
  exact ⟨t, coveringNumberAtLeast_mono_set ht hd⟩

/-- Infinite orthogonal target points that are forced into every covering
presentation establish the revised UUS condition. -/
theorem uus_of_infinite_isolated_orthogonal
    {H : GenLimit.Generic.LanguageClass E} {r R δ : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hrδ : r < δ)
    (hwitness : ∀ L, L ∈ H → ∃ A : Set E, A.Infinite ∧ A ⊆ L ∧
      (∀ x ∈ A, ‖x‖ = R) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → inner ℝ x y = 0) ∧
      ∀ x ∈ A, ∀ y ∈ L, dist y x < δ → y = x) :
    UniformlyUnboundedSupportAt dist r H := by
  intro L hL
  obtain ⟨A, hA, hAL, hnorm, horth, hisolated⟩ := hwitness L hL
  refine ⟨hA.nonempty.mono hAL, ?_⟩
  intro stream hp d
  apply prefix_covering_unbounded_of_infinite_orthogonal hA _
    (lt_of_le_of_lt hr hrR) hr hrR hnorm horth d
  intro x hx
  obtain ⟨y, hy, hnear⟩ := hp.2 (hAL hx) δ hrδ
  exact (hisolated x hx y (hp.1 hy) hnear) ▸ hy

end GenLimit.MetricSpaces
