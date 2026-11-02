import GenLimit.Paper21_GenerationInMetricSpaces.Example411LowerGeometry
import GenLimit.Paper21_GenerationInMetricSpaces.BlockDiagonal
import GenLimit.Paper21_GenerationInMetricSpaces.SemanticBoundary

/-!
# Example 4.11: failure of non-uniform generation for the weighted metric

In a critical layer the odd points have norm above the novelty scale,
whereas all even descendants have weighted norm at most that scale. The
diagonal construction enumerates an exact target, including the boundary
where the descendants lie on the closed novelty ball.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.Example411

open GenLimit.Generic WeightedHilbert

noncomputable section

local instance : DecidableEq Hilbert2 := Classical.decEq _

theorem exists_critical_layer {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hεr : ε < r) :
    ∃ m : ℕ, amplitude r m / 2 ≤ ε ∧ ε < amplitude r m := by
  have hex : ∃ n : ℕ, amplitude r n ≤ ε := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε (by positivity : 0 < 4 * r))
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    have hmul := (lt_div_iff₀ (by positivity : 0 < 4 * r)).mp hn
    dsimp only [amplitude]
    nlinarith
  let d := Nat.find hex
  have hd : amplitude r d ≤ ε := Nat.find_spec hex
  have hdpos : 0 < d := by
    by_contra hnot
    have hd0 : d = 0 := by omega
    rw [hd0, amplitude_zero] at hd
    linarith
  have hprev : ε < amplitude r (d - 1) :=
    lt_of_not_ge (Nat.find_min hex (by change d - 1 < d; omega))
  refine ⟨d - 1, ?_, hprev⟩
  have hstep : amplitude r (d - 1) / 2 = amplitude r d := by
    rw [← amplitude_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
  rwa [hstep]

theorem smallFamily_not_limit {r ε : ℝ} (hr : 0 < r) (m : ℕ)
    (hε : 0 ≤ ε) (hhalf : amplitude r m / 2 ≤ ε) :
    ¬ GeneratableInLimitAt weightedDistance ε ε (smallFamily r m) := by
  let blocks : ℕ → Finset Hilbert2 := fun k => {axisPoint (amplitude r m) (2 * k + 1)}
  let aux : ℕ → Stream Hilbert2 := fun k n => axisPoint (amplitude r m) (orbit k (n + 1))
  have hα := amplitude_pos hr m
  have hdisjoint : ∀ i ∈ positiveIndices, ∀ j ∈ positiveIndices, i ≠ j →
      Disjoint (blocks i : Set Hilbert2) (blocks j : Set Hilbert2) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : x = axisPoint (amplitude r m) (2 * i + 1) := by simpa [blocks] using hx
    have hy' : x = axisPoint (amplitude r m) (2 * j + 1) := by simpa [blocks] using hy
    have hc := (axisPoint_eq_axisPoint_of_left_ne_zero hα.ne' (hx'.symm.trans hy')).2
    exact hij (by omega)
  apply not_limit_of_infinite_blocks positiveIndices_infinite blocks hdisjoint
    (fun _ => 0) aux weightedDistance_self hε hε
  · rintro x ⟨n, rfl⟩
    rw [mem_closedNeighborhood_singleton_iff, weightedDistance_self]
    exact hε
  · rintro k hk x ⟨n, rfl⟩
    rw [mem_closedNeighborhood_singleton_iff]
    change weightedDistance 0 (axisPoint (amplitude r m) (orbit k (n + 1))) ≤ ε
    rw [weightedDistance_zero_axis]
    have heven : orbit k (n + 1) % 2 = 0 := by simp [orbit, pow_succ, Nat.mul_mod]
    simp only [weight, heven, Nat.reduceEqDiff, if_false]
    rw [abs_of_pos (by positivity)]
    linarith
  · intro I hI hIK
    refine ⟨I, hI, hIK, ?_⟩
    ext x
    constructor
    · rintro ((⟨n, rfl⟩ | ⟨k, hk, hx⟩) | ⟨k, hk, n, hx⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, 0, by simpa [blocks, orbit] using hx⟩
      · exact Or.inr ⟨k, hk, n + 1, hx.symm⟩
    · rintro (hzero | ⟨k, hk, n, hx⟩)
      · exact Or.inl (Or.inl ⟨0, (Set.mem_singleton_iff.mp hzero).symm⟩)
      · cases n with
        | zero => exact Or.inl (Or.inr ⟨k, hk, by simpa [blocks, orbit] using hx⟩)
        | succ n => exact Or.inr ⟨k, hk, n, hx.symm⟩

theorem not_nonuniform {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hεr : ε < r) :
    ¬ NonuniformlyGeneratableAt weightedDistance ε ε (family r) := by
  rintro ⟨gen, hgen⟩
  obtain ⟨m, hhalf, hεα⟩ := exists_critical_layer hr hε hεr
  have hsmall : IsNonuniformGeneratorAt weightedDistance ε ε gen (smallFamily r m) :=
    lemma_C_1_threshold_transfer (by decide : 0 < 2) (completion r m)
      (completions_empty hr m) (fun _ hL i => small_completions hL i) hgen
  exact smallFamily_not_limit hr m hε.le hhalf
    ⟨gen, isLimitGeneratorAt_of_nonuniform_of_uus
      (smallFamily_weighted_uus hr m hε.le hεα) le_rfl hsmall⟩

end
end GenLimit.MetricSpaces.HilbertAxisReservoir.Example411
