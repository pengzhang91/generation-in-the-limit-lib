import GenLimit.Paper21_GenerationInMetricSpaces.Example411Geometry

/-! # Example 4.11: uniform generation for the ordinary Hilbert metric -/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.Example411

open GenLimit.Generic

noncomputable section

theorem observed_orbit_subset {r : ℝ} (hr : 0 < r) {L : Set Hilbert2}
    (hL : L ∈ family r) {m k : ℕ}
    (hx : axisPoint (amplitude r m) k ∈ L) (n : ℕ) :
    axisPoint (amplitude r m) (2 ^ (n + 1) * k) ∈ L := by
  obtain ⟨I, hI, rfl⟩ := hL
  rcases hx with hzero | ⟨l, j, hj, b, heq⟩
  · have hnorm := congrArg norm (Set.mem_singleton_iff.mp hzero)
    simp only [norm_axisPoint, abs_of_pos (amplitude_pos hr m), norm_zero] at hnorm
    exact (amplitude_pos hr m).ne' hnorm |>.elim
  · obtain ⟨hamp, hcoord⟩ := axisPoint_eq_axisPoint_of_left_ne_zero (amplitude_pos hr m).ne' heq
    have hml := amplitude_injective hr hamp
    subst l
    refine Or.inr ⟨m, j, hj, (n + 1) + b, ?_⟩
    rw [hcoord]
    congr 1
    simp only [orbit, pow_add]
    ring

theorem large_norm_of_sample_covering {ε : ℝ} (S : Finset Hilbert2)
    (hCN : CoveringNumberAtLeast dist ε (S : Set Hilbert2) 2) :
    ∃ x ∈ S, ε < ‖x‖ := by
  classical
  by_contra! hsmall
  have hcover : (S : Set Hilbert2) ⊆ closedNeighborhood dist ({0} : Set Hilbert2) ε := by
    intro x hx
    rw [mem_closedNeighborhood_singleton_iff]
    simpa using hsmall x hx
  have hbad := hCN {0} (by simpa using hcover)
  simp at hbad

theorem fresh_commonCore {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    {I : ℕ → Set ℕ} (S : Finset Hilbert2) (hS : (S : Set Hilbert2) ⊆ target r I)
    (hCN : CoveringNumberAtLeast dist ε (S : Set Hilbert2) 2) :
    ∃ y, y ∈ commonCore (family r) S ∧ y ∉ closedNeighborhood dist (S : Set Hilbert2) ε := by
  obtain ⟨x, hxS, hxnorm⟩ := large_norm_of_sample_covering S hCN
  rcases hS hxS with hzero | ⟨m, k, hk, b, hx⟩
  · have hx0 : x = 0 := Set.mem_singleton_iff.mp hzero
    simp [hx0] at hxnorm
    linarith
  · let q := orbit k b
    have hεα : ε < amplitude r m := by
      simpa only [hx, norm_axisPoint, abs_of_pos (amplitude_pos hr m)] using hxnorm
    have hinj : Function.Injective (fun n : ℕ => 2 ^ (n + 1) * q) := by
      intro n l hnl
      have hp : (2 : ℕ) ^ (n + 1) = 2 ^ (l + 1) :=
        Nat.eq_of_mul_eq_mul_right (orbit_pos k b) hnl
      exact Nat.succ_injective (Nat.pow_right_injective (by decide) hp)
    obtain ⟨n, hn⟩ := axisInjection_avoids_finset S
      (fun y hy => target_axisSupported r I y (hS hy)) _ hinj (amplitude_pos hr m) hεα
    refine ⟨axisPoint (amplitude r m) (2 ^ (n + 1) * q), ?_, hn⟩
    intro L hL
    apply observed_orbit_subset hr hL.1
    exact hx ▸ hL.2 hxS

theorem uniform_positive {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    UniformlyGeneratableAt dist ε ε (family r) := by
  refine ⟨scaleClosureGenerator dist ε (family r), 2, ?_⟩
  intro L hL stream hstream t hCN s hts
  apply scaleClosureGenerator_correct_of_fresh hL hstream s
  obtain ⟨I, hI, rfl⟩ := hL
  exact fresh_commonCore hr hε _ (sample_subset_of_streamIn hstream s)
    (coveringNumberAtLeast_mono_set (sample_mono hts) hCN)

end
end GenLimit.MetricSpaces.HilbertAxisReservoir.Example411
