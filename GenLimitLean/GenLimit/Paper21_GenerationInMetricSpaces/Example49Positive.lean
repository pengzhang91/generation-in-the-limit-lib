import GenLimit.Paper21_GenerationInMetricSpaces.Example49Geometry

/-!
# Example 4.9: positive generation from observed towers

The semantic common-core generator works in all three positive regimes.
Its choice depends only on the finite history. No executable recognition
of arbitrary real-valued observations is claimed.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.Example49

open GenLimit.Generic

noncomputable section

theorem u_mem_target_iff {r ε₁ ε₂ ε' : ℝ} (hr : 0 < r)
    {I₁ I₂ J : Set ℕ} {k : ℕ} :
    U r k ∈ target r ε₁ ε₂ ε' I₁ I₂ J ↔ k ∈ I₁ := by
  constructor
  · rintro (hzero | ((hU | hG) | (hA | hB)))
    · have heq : U r k = axisPoint 0 0 := by simpa using hzero
      have hamp := (axisPoint_eq_axisPoint_of_left_ne_zero
        (by positivity : (2 * r : ℝ) ≠ 0) heq).1
      linarith
    · obtain ⟨j, hj, heq⟩ := hU
      have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero
        (by positivity : (2 * r : ℝ) ≠ 0) heq).2
      have : k = j := by omega
      simpa only [this] using hj
    · obtain ⟨j, hj, n, heq⟩ := hG
      have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero
        (by positivity : (2 * r : ℝ) ≠ 0) heq).2
      omega
    · obtain ⟨j, hj, heq⟩ := hA
      have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero
        (by positivity : (2 * r : ℝ) ≠ 0) heq).2
      omega
    · obtain ⟨j, hj, heq⟩ := hB
      have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero
        (by positivity : (2 * r : ℝ) ≠ 0) heq).2
      omega
  · exact fun hk => Or.inr (Or.inl (Or.inl ⟨k, hk, rfl⟩))

theorem g_mem_target_iff {r ε₁ ε₂ ε' : ℝ} (hε' : 0 < ε')
    {I₁ I₂ J : Set ℕ} {k : ℕ} :
    G ε' k ∈ target r ε₁ ε₂ ε' I₁ I₂ J ↔ ∃ j ∈ I₁, ∃ n, k = j ^ (n + 1) := by
  constructor
  · rintro (hzero | ((hU | hG) | (hA | hB)))
    · have heq : G ε' k = axisPoint 0 0 := by simpa using hzero
      have hamp := (axisPoint_eq_axisPoint_of_left_ne_zero hε'.ne' heq).1
      linarith
    · obtain ⟨j, hj, heq⟩ := hU
      have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero hε'.ne' heq).2
      omega
    · obtain ⟨j, hj, n, heq⟩ := hG
      have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero hε'.ne' heq).2
      exact ⟨j, hj, n, by omega⟩
    · obtain ⟨j, hj, heq⟩ := hA
      have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero hε'.ne' heq).2
      omega
    · obtain ⟨j, hj, heq⟩ := hB
      have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero hε'.ne' heq).2
      omega
  · rintro ⟨j, hj, n, rfl⟩
    exact Or.inr (Or.inl (Or.inr ⟨j, hj, n, rfl⟩))

theorem observed_tower {r ε₁ ε₂ ε' : ℝ} (hr : 0 < r) (hε' : 0 < ε')
    {L : Set Hilbert2} (hL : L ∈ family r ε₁ ε₂ ε')
    {k : ℕ} {x : Hilbert2} (hx : x ∈ L) (hform : x = U r k ∨ x = G ε' k) (n : ℕ) :
    G ε' (k ^ (n + 1)) ∈ L := by
  obtain ⟨I₁, I₂, J, _, _, _, _, _, _, rfl⟩ := hL
  rcases hform with rfl | rfl
  · exact Or.inr (Or.inl (Or.inr ⟨k, (u_mem_target_iff hr).mp hx, n, rfl⟩))
  · obtain ⟨j, hj, b, rfl⟩ := (g_mem_target_iff hε').mp hx
    have hpos : 0 < (b + 1) * (n + 1) := Nat.mul_pos (by omega) (by omega)
    apply (g_mem_target_iff hε').mpr
    refine ⟨j, hj, (b + 1) * (n + 1) - 1, ?_⟩
    rw [Nat.sub_add_cancel (by omega : 1 ≤ (b + 1) * (n + 1))]
    exact (pow_mul j (b + 1) (n + 1)).symm

theorem optimal_point_form {r ε' : ℝ} {I : Set ℕ} (hI : I ⊆ indices)
    {x : Hilbert2} (hx : x ∈ optimal r ε' I) :
    ∃ k, 2 ≤ k ∧ (x = U r k ∨ x = G ε' k) := by
  rcases hx with ⟨k, hk, hx⟩ | ⟨j, hj, n, hx⟩
  · exact ⟨k, hI hk, Or.inl hx⟩
  · refine ⟨j ^ (n + 1), ?_, Or.inr hx⟩
    exact (hI hj).trans (le_self_pow (by have := hI hj; change 2 ≤ j at this; omega)
      (Nat.succ_ne_zero n))

theorem fresh_commonCore_of_optimal {r ε₁ ε₂ ε' γ' : ℝ}
    (hr : 0 < r) (hε' : 0 < ε') (hγ' : γ' < ε')
    {I₁ I₂ J : Set ℕ} (hI₁ : I₁ ⊆ indices) (S : Finset Hilbert2)
    (hS : (S : Set Hilbert2) ⊆ target r ε₁ ε₂ ε' I₁ I₂ J)
    (hobs : ∃ x ∈ S, x ∈ optimal r ε' I₁) :
    ∃ y, y ∈ commonCore (family r ε₁ ε₂ ε') S ∧
      y ∉ closedNeighborhood dist (S : Set Hilbert2) γ' := by
  obtain ⟨x, hxS, hxO⟩ := hobs
  obtain ⟨k, hk, hform⟩ := optimal_point_form hI₁ hxO
  have hinj : Function.Injective (fun n : ℕ => 4 * k ^ (n + 1) + 3) := by
    intro m n hmn
    dsimp only at hmn
    have hpow : k ^ (m + 1) = k ^ (n + 1) := by omega
    exact Nat.succ_injective (Nat.pow_right_injective hk hpow)
  obtain ⟨n, hn⟩ := axisInjection_avoids_finset S
    (fun y hy => target_axisSupported r ε₁ ε₂ ε' I₁ I₂ J y (hS hy)) _ hinj hε' hγ'
  refine ⟨G ε' (k ^ (n + 1)), ?_, hn⟩
  intro L hL
  exact observed_tower hr hε' hL.1 (hL.2 hxS) hform n

theorem limit_positive {r ε₁ ε₂ ε' γ γ' : ℝ}
    (hr : 0 < r) (hε' : 0 < ε') (hγr : γ ≤ r) (hγ' : γ' < ε') :
    GeneratableInLimitAt dist γ γ' (family r ε₁ ε₂ ε') := by
  refine ⟨scaleClosureGenerator dist γ' (family r ε₁ ε₂ ε'), ?_⟩
  intro L hL stream hp
  obtain ⟨I₁, I₂, J, hI₁, hI₂, hJ, hI₁K, hI₂K, hJK, rfl⟩ := hL
  obtain ⟨k, hk⟩ := hI₁.nonempty
  have hu : U r k ∈ target r ε₁ ε₂ ε' I₁ I₂ J := (u_mem_target_iff hr).mpr hk
  obtain ⟨y, hy, hnear⟩ := hp.2 hu (2 * r) (by linarith)
  have hyU : y = U r k := u_isolated hr (hp.1 hy) hnear
  obtain ⟨s, hs⟩ := hy
  refine ⟨s + 1, ?_⟩
  intro t ht
  have hTarget : target r ε₁ ε₂ ε' I₁ I₂ J ∈ family r ε₁ ε₂ ε' :=
    ⟨I₁, I₂, J, hI₁, hI₂, hJ, hI₁K, hI₂K, hJK, rfl⟩
  apply scaleClosureGenerator_correct_of_fresh hTarget hp.1 t
  apply fresh_commonCore_of_optimal hr hε' hγ' hI₁K _ (sample_subset_of_streamIn hp.1 t)
  refine ⟨U r k, ?_, Or.inl ⟨k, hk, rfl⟩⟩
  exact mem_sample_iff.mpr ⟨s, by omega, hs.trans hyU⟩

theorem optimal_of_large_sample_uniform {r ε₁ ε₂ ε' γ : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hε₁₂ : ε₁ ≤ ε₂) (hε₂γ : ε₂ ≤ γ)
    {I₁ I₂ J : Set ℕ} (S : Finset Hilbert2)
    (hS : (S : Set Hilbert2) ⊆ target r ε₁ ε₂ ε' I₁ I₂ J)
    (hCN : CoveringNumberAtLeast dist γ (S : Set Hilbert2) 2) :
    ∃ x ∈ S, x ∈ optimal r ε' I₁ := by
  classical
  by_contra! hnone
  have hγ : 0 ≤ γ := hε₂.trans hε₂γ
  have hcover : (S : Set Hilbert2) ⊆ closedNeighborhood dist ({0} : Set Hilbert2) γ := by
    intro x hx
    rw [mem_closedNeighborhood_singleton_iff]
    rcases hS hx with hzero | (hO | (hA | hB))
    · have hx0 : x = 0 := Set.mem_singleton_iff.mp hzero
      simpa [hx0] using hγ
    · exact (hnone x hx hO).elim
    · obtain ⟨k, hk, rfl⟩ := hA
      simpa [A, abs_of_nonneg hε₁] using hε₁₂.trans hε₂γ
    · obtain ⟨k, hk, rfl⟩ := hB
      simpa [B, abs_of_nonneg hε₂] using hε₂γ
  have hbad := hCN {0} (by simpa using hcover)
  simp at hbad

theorem optimal_of_large_sample_nonuniform {r ε₁ ε₂ ε' γ : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₁γ : ε₁ ≤ γ)
    {I₁ I₂ J : Set ℕ} (hJ : J.Finite) (S : Finset Hilbert2)
    (hS : (S : Set Hilbert2) ⊆ target r ε₁ ε₂ ε' I₁ I₂ J)
    (hCN : CoveringNumberAtLeast dist γ (S : Set Hilbert2) (hJ.toFinset.card + 2)) :
    ∃ x ∈ S, x ∈ optimal r ε' I₁ := by
  classical
  by_contra! hnone
  let C : Finset Hilbert2 := insert 0 (hJ.toFinset.image (B ε₂))
  have hγ : 0 ≤ γ := hε₁.trans hε₁γ
  have hcover : (S : Set Hilbert2) ⊆ closedNeighborhood dist (C : Set Hilbert2) γ := by
    intro x hx η hη
    rcases hS hx with hzero | (hO | (hA | hB))
    · have hx0 : x = 0 := Set.mem_singleton_iff.mp hzero
      exact ⟨0, Finset.mem_insert_self _ _, by simpa [hx0] using hγ.trans_lt hη⟩
    · exact (hnone x hx hO).elim
    · obtain ⟨k, hk, rfl⟩ := hA
      refine ⟨0, Finset.mem_insert_self _ _, ?_⟩
      simpa [A, abs_of_nonneg hε₁] using hε₁γ.trans_lt hη
    · obtain ⟨k, hk, rfl⟩ := hB
      refine ⟨B ε₂ k, Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨k, hJ.mem_toFinset.mpr hk, rfl⟩), ?_⟩
      simpa using hγ.trans_lt hη
  have hcard : C.card ≤ hJ.toFinset.card + 1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
  have hbad := hCN C hcover
  omega

theorem uniform_positive {r ε₁ ε₂ ε' γ γ' : ℝ}
    (hr : 0 < r) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hε₁₂ : ε₁ ≤ ε₂)
    (hε' : 0 < ε') (hε₂γ : ε₂ ≤ γ) (hγ' : γ' < ε') :
    UniformlyGeneratableAt dist γ γ' (family r ε₁ ε₂ ε') := by
  refine ⟨scaleClosureGenerator dist γ' (family r ε₁ ε₂ ε'), 2, ?_⟩
  intro L hL stream hstream t hCN s hts
  obtain ⟨I₁, I₂, J, hI₁, hI₂, hJ, hI₁K, hI₂K, hJK, rfl⟩ := hL
  have hTarget : target r ε₁ ε₂ ε' I₁ I₂ J ∈ family r ε₁ ε₂ ε' :=
    ⟨I₁, I₂, J, hI₁, hI₂, hJ, hI₁K, hI₂K, hJK, rfl⟩
  have hS := sample_subset_of_streamIn hstream s
  apply scaleClosureGenerator_correct_of_fresh hTarget hstream s
  exact fresh_commonCore_of_optimal hr hε' hγ' hI₁K _ hS
    (optimal_of_large_sample_uniform hε₁ hε₂ hε₁₂ hε₂γ _ hS
      (coveringNumberAtLeast_mono_set (sample_mono hts) hCN))

theorem nonuniform_positive {r ε₁ ε₂ ε' γ γ' : ℝ}
    (hr : 0 < r) (hε₁ : 0 ≤ ε₁) (hε' : 0 < ε')
    (hε₁γ : ε₁ ≤ γ) (hγ' : γ' < ε') :
    NonuniformlyGeneratableAt dist γ γ' (family r ε₁ ε₂ ε') := by
  refine ⟨scaleClosureGenerator dist γ' (family r ε₁ ε₂ ε'), ?_⟩
  intro L hL
  obtain ⟨I₁, I₂, J, hI₁, hI₂, hJ, hI₁K, hI₂K, hJK, rfl⟩ := hL
  refine ⟨hJ.toFinset.card + 2, ?_⟩
  intro stream hstream t hCN s hts
  have hTarget : target r ε₁ ε₂ ε' I₁ I₂ J ∈ family r ε₁ ε₂ ε' :=
    ⟨I₁, I₂, J, hI₁, hI₂, hJ, hI₁K, hI₂K, hJK, rfl⟩
  have hS := sample_subset_of_streamIn hstream s
  apply scaleClosureGenerator_correct_of_fresh hTarget hstream s
  exact fresh_commonCore_of_optimal hr hε' hγ' hI₁K _ hS
    (optimal_of_large_sample_nonuniform hε₁ hε₁γ hJ _ hS
      (coveringNumberAtLeast_mono_set (sample_mono hts) hCN))

end
end GenLimit.MetricSpaces.HilbertAxisReservoir.Example49
