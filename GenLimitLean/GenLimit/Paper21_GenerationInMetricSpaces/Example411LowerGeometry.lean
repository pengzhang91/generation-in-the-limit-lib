import GenLimit.Paper21_GenerationInMetricSpaces.Example411Positive
import GenLimit.Paper21_GenerationInMetricSpaces.ThresholdTransfer

/-! # Example 4.11: disjoint completions and the critical-layer UUS bound -/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.Example411

open GenLimit.Generic WeightedHilbert

noncomputable section

def positiveIndices : Set ℕ := {k | 0 < k}

theorem positiveIndices_infinite : positiveIndices.Infinite := by
  exact (Set.infinite_range_of_injective Nat.succ_injective).mono
    (by rintro k ⟨n, rfl⟩; exact Nat.succ_pos n)

def smallTarget (r : ℝ) (m : ℕ) (I : Set ℕ) : Set Hilbert2 := {0} ∪ layer r m I

def smallFamily (r : ℝ) (m : ℕ) : LanguageClass Hilbert2 :=
  {L | ∃ I : Set ℕ, I.Infinite ∧ I ⊆ positiveIndices ∧ L = smallTarget r m I}

def completionIndices (i : Fin 2) : Set ℕ := Set.range (fun n : ℕ => 2 * n + i.val + 1)

theorem completionIndices_infinite (i : Fin 2) : (completionIndices i).Infinite := by
  apply Set.infinite_range_of_injective
  intro n l hnl
  dsimp only at hnl
  omega

theorem completionIndices_positive (i : Fin 2) : completionIndices i ⊆ positiveIndices := by
  rintro k ⟨n, rfl⟩
  change 0 < 2 * n + i.val + 1
  omega

def completion (r : ℝ) (m : ℕ) (i : Fin 2) : Set Hilbert2 :=
  {x | ∃ l, l ≠ m ∧ x ∈ layer r l (completionIndices i)}

theorem completions_disjoint {r : ℝ} (hr : 0 < r) (m : ℕ) :
    Disjoint (completion r m 0) (completion r m 1) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨l, hl, k, ⟨a, ha⟩, n, hx⟩ ⟨p, hp, j, ⟨b, hb⟩, c, hy⟩
  obtain ⟨hamp, hcoord⟩ := axisPoint_eq_axisPoint_of_left_ne_zero
    (amplitude_pos hr l).ne' (hx.symm.trans hy)
  have hlp := amplitude_injective hr hamp
  have hkj : k = j := orbit_root hcoord
  dsimp only at ha hb
  omega

theorem completions_empty {r : ℝ} (hr : 0 < r) (m : ℕ) :
    (⋂ i : Fin 2, completion r m i) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact Set.disjoint_left.mp (completions_disjoint hr m)
    (Set.mem_iInter.mp hx 0) (Set.mem_iInter.mp hx 1)

theorem small_completions {r : ℝ} {m : ℕ} {L : Set Hilbert2}
    (hL : L ∈ smallFamily r m) (i : Fin 2) : L ∪ completion r m i ∈ family r := by
  obtain ⟨I, hI, hIK, rfl⟩ := hL
  let allI : ℕ → Set ℕ := fun l => if l = m then I else completionIndices i
  have hallI : ∀ l, (allI l).Infinite ∧ ∀ k ∈ allI l, 0 < k := by
    intro l
    by_cases hl : l = m
    · simpa only [allI, if_pos hl] using And.intro hI (fun k hk => hIK hk)
    · simpa only [allI, if_neg hl] using
        And.intro (completionIndices_infinite i) (fun k hk => completionIndices_positive i hk)
  refine ⟨allI, hallI, ?_⟩
  ext x
  constructor
  · rintro ((hzero | hx) | ⟨l, hl, hx⟩)
    · exact Or.inl hzero
    · exact Or.inr ⟨m, by simpa only [allI, if_pos rfl] using hx⟩
    · exact Or.inr ⟨l, by simpa only [allI, if_neg hl] using hx⟩
  · rintro (hzero | ⟨l, hx⟩)
    · exact Or.inl (Or.inl hzero)
    · by_cases hl : l = m
      · subst l
        exact Or.inl (Or.inr (by simpa only [allI, if_pos rfl] using hx))
      · exact Or.inr ⟨l, hl, by simpa only [allI, if_neg hl] using hx⟩

theorem odd_point_isolated {r : ℝ} (hr : 0 < r) (m k : ℕ) {I : Set ℕ}
    {y : Hilbert2} (hy : y ∈ smallTarget r m I)
    (hclose : weightedDistance y (axisPoint (amplitude r m) (2 * k + 1)) < amplitude r m) :
    y = axisPoint (amplitude r m) (2 * k + 1) := by
  have hα := amplitude_pos hr m
  rcases hy with hzero | ⟨j, hj, n, rfl⟩
  · have hy0 : y = 0 := Set.mem_singleton_iff.mp hzero
    rw [hy0, weightedDistance_zero_axis] at hclose
    simp [weight, show (2 * k + 1) % 2 = 1 by omega, abs_of_pos hα] at hclose
  · by_cases hc : orbit j n = 2 * k + 1
    · exact congrArg (axisPoint (amplitude r m)) hc
    · have hfar := coordinate_le_distance (axisPoint (amplitude r m) (orbit j n))
        (amplitude r m) (2 * k + 1)
      rw [axisPoint_apply_ne (amplitude r m) (Ne.symm hc)] at hfar
      simp [weight, show (2 * k + 1) % 2 = 1 by omega, abs_of_pos hα] at hfar
      exact (not_lt_of_ge hfar hclose).elim

theorem smallFamily_weighted_uus {r ε : ℝ} (hr : 0 < r) (m : ℕ)
    (hε : 0 ≤ ε) (hεα : ε < amplitude r m) :
    UniformlyUnboundedSupportAt weightedDistance ε (smallFamily r m) := by
  classical
  rintro L ⟨I, hI, hIK, rfl⟩
  let A : Set Hilbert2 := (fun k => axisPoint (amplitude r m) (2 * k + 1)) '' I
  have hα := amplitude_pos hr m
  have hA : A.Infinite := hI.image (by
    intro k _ j _ hkj
    have hc := (axisPoint_eq_axisPoint_of_left_ne_zero hα.ne' hkj).2
    omega)
  have hAL : A ⊆ smallTarget r m I := by
    rintro x ⟨k, hk, rfl⟩
    exact Or.inr ⟨k, hk, 0, by simp [orbit]⟩
  have hnorm : ∀ x ∈ A, ‖x‖ = amplitude r m := by
    rintro x ⟨k, hk, rfl⟩
    simp [abs_of_pos hα]
  have horth : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → inner ℝ x y = 0 := by
    rintro x ⟨k, hk, rfl⟩ y ⟨j, hj, rfl⟩ hne
    exact inner_axisPoint_of_ne _ _ (fun hc => hne (congrArg (axisPoint (amplitude r m)) hc))
  refine ⟨hA.nonempty.mono hAL, ?_⟩
  intro stream hp d
  have hAstream : A ⊆ Set.range (fun n => weightedMap (stream n)) := by
    rintro x ⟨k, hk, rfl⟩
    obtain ⟨y, hy, hclose⟩ := hp.2 (hAL ⟨k, hk, rfl⟩) (amplitude r m) hεα
    have hyx := odd_point_isolated hr m k (hp.1 hy) hclose
    obtain ⟨s, hs⟩ := hy
    refine ⟨s, ?_⟩
    change weightedMap (stream s) = axisPoint (amplitude r m) (2 * k + 1)
    rw [hs, hyx]
    simp [weight, show (2 * k + 1) % 2 = 1 by omega]
  obtain ⟨t, ht⟩ := prefix_covering_unbounded_of_infinite_orthogonal hA hAstream hα hε hεα
    hnorm horth d
  have hsample : weightedMap '' (sample stream t : Set Hilbert2) =
      (sample (fun n => weightedMap (stream n)) t : Set Hilbert2) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn, hny⟩ := mem_sample_iff.mp hy
      exact mem_sample_iff.mpr ⟨n, hn, congrArg weightedMap hny⟩
    · intro hx
      obtain ⟨n, hn, hnx⟩ := mem_sample_iff.mp hx
      exact ⟨stream n, mem_sample_iff.mpr ⟨n, hn, rfl⟩, hnx⟩
  refine ⟨t, coveringNumberAtLeast_pullback (S := sample stream t) ?_⟩
  rw [hsample]
  exact ht

end
end GenLimit.MetricSpaces.HilbertAxisReservoir.Example411
