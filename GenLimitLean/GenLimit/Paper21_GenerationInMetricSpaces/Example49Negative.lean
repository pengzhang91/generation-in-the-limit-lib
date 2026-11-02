import GenLimit.Paper21_GenerationInMetricSpaces.Example49Positive
import GenLimit.Paper21_GenerationInMetricSpaces.Example48Rows
import GenLimit.Paper21_GenerationInMetricSpaces.ThresholdTransfer
import GenLimit.Paper21_GenerationInMetricSpaces.SemanticBoundary

/-!
# Example 4.9: common-part and diagonal lower bounds

Disjoint prime-power completions transfer thresholds to the adversary's
unstructured part. Infinite block selection then defeats every generator.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.Example49

open GenLimit.Generic GenLimit.Support

noncomputable section

local instance : DecidableEq Hilbert2 := Classical.decEq _

theorem indices_infinite : indices.Infinite := by
  have h := Set.infinite_range_of_injective (f := fun n : ℕ => n + 2) (by
    intro m n hmn
    dsimp only at hmn
    omega)
  exact h.mono (by rintro k ⟨n, rfl⟩; change 2 ≤ n + 2; omega)

abbrev primePowers := Example48Rows.powers

theorem primePowers_subset (i : ℕ) : primePowers i ⊆ indices := by
  rintro k ⟨n, rfl⟩
  have hp := RealLineThreshold.diagonalOddPrime_two_lt i
  change 2 ≤ RealLineThreshold.diagonalOddPrime i ^ (n + 1)
  exact (by omega : 2 ≤ RealLineThreshold.diagonalOddPrime i).trans
    (le_self_pow (by omega) (Nat.succ_ne_zero n))

def completion (r ε ε' : ℝ) (i : ℕ) : Set Hilbert2 :=
  optimal r ε' (primePowers i) ∪ {x | ∃ k ∈ primePowers i, x = A ε k}

theorem completion_form {r ε ε' : ℝ} {i : ℕ} {x : Hilbert2}
    (hx : x ∈ completion r ε ε' i) :
    ∃ k ∈ primePowers i, x = U r k ∨ x = A ε k ∨ x = G ε' k := by
  rcases hx with (⟨k, hk, hx⟩ | ⟨k, hk, n, hx⟩) | ⟨k, hk, hx⟩
  · exact ⟨k, hk, Or.inl hx⟩
  · exact ⟨k ^ (n + 1), Example48Rows.powers_pow hk (by omega), Or.inr (Or.inr hx)⟩
  · exact ⟨k, hk, Or.inr (Or.inl hx)⟩

theorem completions_disjoint {r ε ε' : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε' : 0 < ε')
    {i j : ℕ} (hij : i ≠ j) : Disjoint (completion r ε ε' i) (completion r ε ε' j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨k, hk, hx⟩ := completion_form hx
  obtain ⟨l, hl, hy⟩ := completion_form hy
  have hkl := Example48Rows.powers_ne hij hk hl
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  all_goals
    have heq := hx.symm.trans hy
    simp only [U, A, G] at heq
    obtain ⟨hamp, hcoord⟩ := axisPoint_eq_axisPoint_of_left_ne_zero (by positivity) heq
    exact hkl (by omega)

def twoCompletions (r ε ε' : ℝ) (i : Fin 2) : Set Hilbert2 := completion r ε ε' i.val

theorem twoCompletions_empty {r ε ε' : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε' : 0 < ε') :
    (⋂ i : Fin 2, twoCompletions r ε ε' i) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact Set.disjoint_left.mp (completions_disjoint hr hε hε' (by decide : 0 ≠ 1))
    (Set.mem_iInter.mp hx (0 : Fin 2)) (Set.mem_iInter.mp hx (1 : Fin 2))

def smallTarget (ε : ℝ) (I : Set ℕ) : Set Hilbert2 :=
  {0} ∪ {x | ∃ k ∈ I, x = A ε k}

def smallFamily (ε : ℝ) : LanguageClass Hilbert2 :=
  {L | ∃ I : Set ℕ, I.Infinite ∧ I ⊆ indices ∧ L = smallTarget ε I}

theorem small_completions {r ε₁ ε₂ ε' : ℝ} {L : Set Hilbert2}
    (hL : L ∈ smallFamily ε₁) (i : Fin 2) :
    L ∪ twoCompletions r ε₁ ε' i ∈ family r ε₁ ε₂ ε' := by
  obtain ⟨I, hI, hIK, rfl⟩ := hL
  refine ⟨primePowers i.val, I ∪ primePowers i.val, ∅,
    Example48Rows.powers_infinite _, hI.mono Set.subset_union_left, Set.finite_empty,
    primePowers_subset _, Set.union_subset hIK (primePowers_subset _), Set.empty_subset _, ?_⟩
  ext x
  simp only [smallTarget, twoCompletions, completion, target, Set.mem_union,
    Set.mem_setOf_eq, Set.mem_empty_iff_false, exists_false, false_and, or_false]
  aesop

theorem smallFamily_uus {ε γ : ℝ} (hγ : 0 ≤ γ) (hγε : γ < ε) :
    UniformlyUnboundedSupportAt dist γ (smallFamily ε) := by
  apply uus_of_infinite_isolated_orthogonal hγ hγε hγε
  rintro L ⟨I, hI, hIK, rfl⟩
  let C : Set Hilbert2 := (A ε) '' I
  have hε : 0 < ε := lt_of_le_of_lt hγ hγε
  have hC : C.Infinite := hI.image (by
    intro i _ j _ hij
    have hc := (axisPoint_eq_axisPoint_of_left_ne_zero hε.ne' hij).2
    omega)
  refine ⟨C, hC, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨k, hk, rfl⟩
    exact Or.inr ⟨k, hk, rfl⟩
  · rintro x ⟨k, hk, rfl⟩
    simp [A, abs_of_pos hε]
  · rintro x ⟨k, hk, rfl⟩ y ⟨j, hj, rfl⟩ hne
    exact inner_axisPoint_of_ne _ _ (fun hc => hne (congrArg (axisPoint ε) hc))
  · rintro x ⟨k, hk, rfl⟩ y (hzero | ⟨j, hj, rfl⟩) hclose
    · have hy0 : y = 0 := Set.mem_singleton_iff.mp hzero
      rw [hy0] at hclose
      simp [A, abs_of_pos hε] at hclose
    · by_cases hjk : j = k
      · simp [hjk]
      · have hfar := coordinate_dist_lower ε ε (by omega : 4 * k + 1 ≠ 4 * j + 1)
        rw [abs_of_pos hε] at hfar
        exact (not_lt_of_ge hfar hclose).elim

theorem smallFamily_not_limit {ε γ γ' : ℝ}
    (hε : 0 < ε) (hγ : 0 ≤ γ) (hγ' : 0 ≤ γ') :
    ¬ GeneratableInLimitAt dist γ γ' (smallFamily ε) := by
  let blocks : ℕ → Finset Hilbert2 := fun k => {A ε k}
  have hdisjoint : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      Disjoint (blocks i : Set Hilbert2) (blocks j : Set Hilbert2) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : x = A ε i := by simpa [blocks] using hx
    have hy' : x = A ε j := by simpa [blocks] using hy
    have hc := (axisPoint_eq_axisPoint_of_left_ne_zero hε.ne' (hx'.symm.trans hy')).2
    exact hij (by omega)
  apply not_limit_of_infinite_blocks indices_infinite blocks hdisjoint
    (fun _ => 0) (fun _ _ => 0) dist_self hγ hγ'
  · rintro x ⟨n, rfl⟩
    rw [mem_closedNeighborhood_singleton_iff, dist_self]
    exact hγ'
  · rintro i hi x ⟨n, rfl⟩
    rw [mem_closedNeighborhood_singleton_iff, dist_self]
    exact hγ'
  · intro I hI hIK
    refine ⟨I, hI, hIK, ?_⟩
    ext x
    constructor
    · rintro ((⟨n, rfl⟩ | ⟨k, hk, hx⟩) | ⟨k, hk, n, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, by simpa [blocks] using hx⟩
      · exact Or.inl rfl
    · rintro (hzero | ⟨k, hk, rfl⟩)
      · exact Or.inl (Or.inl ⟨0, (Set.mem_singleton_iff.mp hzero).symm⟩)
      · exact Or.inl (Or.inr ⟨k, hk, by simp [blocks]⟩)

theorem not_nonuniform_of_small_adversary {r ε₁ ε₂ ε' γ γ' : ℝ}
    (hr : 0 < r) (hε₁ : 0 < ε₁) (hε' : 0 < ε')
    (hγ : 0 ≤ γ) (hγε₁ : γ < ε₁) (hγ' : 0 ≤ γ') :
    ¬ NonuniformlyGeneratableAt dist γ γ' (family r ε₁ ε₂ ε') := by
  rintro ⟨gen, hgen⟩
  have hsmall : IsNonuniformGeneratorAt dist γ γ' gen (smallFamily ε₁) :=
    lemma_C_1_threshold_transfer (by decide : 0 < 2) (twoCompletions r ε₁ ε')
      (twoCompletions_empty hr hε₁ hε') (fun _ hL i => small_completions hL i) hgen
  exact smallFamily_not_limit hε₁ hγ hγ'
    ⟨gen, isLimitGeneratorAt_of_nonuniform_of_uus (smallFamily_uus hγ hγε₁) le_rfl hsmall⟩

def pairedBlock (r ε : ℝ) (p : ℕ) : Finset Hilbert2 := {U r p, A ε p}

theorem pairedBlocks_disjoint {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (pairedBlock r ε i : Set Hilbert2) (pairedBlock r ε j : Set Hilbert2) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [pairedBlock, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  all_goals
    have heq := hx.symm.trans hy
    simp only [U, A] at heq
    obtain ⟨hamp, hcoord⟩ := axisPoint_eq_axisPoint_of_left_ne_zero (by positivity) heq
    exact hij (by omega)

theorem paired_target_mem {r ε₁ ε₂ ε' : ℝ} {I : Set ℕ}
    (hI : I.Infinite) (hIK : I ⊆ indices) :
    BlockDiagonal.language (fun _ => 0) (pairedBlock r ε₁)
      (fun p n => G ε' (p ^ (n + 1))) I ∈ family r ε₁ ε₂ ε' := by
  refine ⟨I, I, ∅, hI, hI, Set.finite_empty, hIK, hIK, Set.empty_subset _, ?_⟩
  ext x
  constructor
  · rintro ((⟨n, rfl⟩ | ⟨p, hp, hblock⟩) | ⟨p, hp, n, hx⟩)
    · exact Or.inl rfl
    · simp only [pairedBlock, Finset.mem_insert, Finset.mem_singleton] at hblock
      rcases hblock with hU | hA
      · exact Or.inr (Or.inl (Or.inl ⟨p, hp, hU⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨p, hp, hA⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨p, hp, n, hx.symm⟩))
  · rintro (hzero | ((⟨p, hp, hx⟩ | ⟨p, hp, n, hx⟩) | (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)))
    · exact Or.inl (Or.inl ⟨0, (Set.mem_singleton_iff.mp hzero).symm⟩)
    · exact Or.inl (Or.inr ⟨p, hp, by simp [pairedBlock, hx]⟩)
    · exact Or.inr ⟨p, hp, n, hx.symm⟩
    · exact Or.inl (Or.inr ⟨p, hp, by simp [pairedBlock, hx]⟩)
    · exact hp.elim

theorem not_limit_of_large_generator {r ε₁ ε₂ ε' γ γ' : ℝ}
    (hr : 0 < r) (hε₁ : 0 < ε₁) (hε' : 0 < ε')
    (hγ : 0 ≤ γ) (hε'γ' : ε' ≤ γ') :
    ¬ GeneratableInLimitAt dist γ γ' (family r ε₁ ε₂ ε') := by
  apply not_limit_of_infinite_blocks Example48Negative.primeIndices_infinite (pairedBlock r ε₁)
    (fun p _ q _ hpq => pairedBlocks_disjoint hr hε₁ hpq)
    (fun _ => 0) (fun p n => G ε' (p ^ (n + 1))) dist_self hγ (hε'.le.trans hε'γ')
  · rintro x ⟨n, rfl⟩
    rw [mem_closedNeighborhood_singleton_iff, dist_self]
    exact hε'.le.trans hε'γ'
  · rintro p hp x ⟨n, rfl⟩
    rw [mem_closedNeighborhood_singleton_iff]
    simpa [G, abs_of_pos hε'] using hε'γ'
  · intro I hI hIK
    apply paired_target_mem hI
    intro p hp
    obtain ⟨i, hi⟩ := hIK hp
    have hbound := RealLineThreshold.diagonalOddPrime_two_lt i
    change 2 ≤ p
    omega

end
end GenLimit.MetricSpaces.HilbertAxisReservoir.Example49
