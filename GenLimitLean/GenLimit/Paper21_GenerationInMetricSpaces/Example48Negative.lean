import GenLimit.Paper21_GenerationInMetricSpaces.BlockDiagonal
import GenLimit.Paper21_GenerationInMetricSpaces.HilbertGeometry
import GenLimit.Paper21_GenerationInMetricSpaces.RealLineThresholdNegative

/-!
# Negative regimes of Example 4.8

Source: arXiv:2602.07710v2, Appendix C.3. All constructions are semantic;
no executable search or oracle implementation is asserted.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.Example48Negative

open GenLimit.Generic GenLimit.Support

noncomputable section

local instance : DecidableEq Hilbert2 := Classical.decEq _

def primeIndices : Set ℕ := Set.range RealLineThreshold.diagonalOddPrime

theorem primeIndices_infinite : primeIndices.Infinite :=
  Set.infinite_range_of_injective RealLineThreshold.diagonalOddPrime_injective

theorem primeIndices_pos {p : ℕ} (hp : p ∈ primeIndices) : 0 < p := by
  obtain ⟨i, rfl⟩ := hp
  exact (RealLineThreshold.diagonalOddPrime_prime i).pos

def blocks (r ε : ℝ) (p : ℕ) : Finset Hilbert2 :=
  {example48U r (2 * p), example48A ε (2 * p)}

theorem blocks_disjoint {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    {p q : ℕ} (hpq : p ≠ q) : Disjoint (blocks r ε p : Set Hilbert2) (blocks r ε q : Set Hilbert2) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [blocks, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero
      (by positivity : (4 * r : ℝ) ≠ 0) (hx.symm.trans hy)).2
    exact hpq (by omega)
  · have hamp := (axisPoint_eq_axisPoint_of_left_ne_zero
      (by positivity : (4 * r : ℝ) ≠ 0) (hx.symm.trans hy)).1
    linarith
  · have hamp := (axisPoint_eq_axisPoint_of_left_ne_zero hε.ne' (hx.symm.trans hy)).1
    linarith
  · have hcoord := (axisPoint_eq_axisPoint_of_left_ne_zero hε.ne' (hx.symm.trans hy)).2
    exact hpq (by omega)

def base (ε' : ℝ) : Stream Hilbert2 :=
  prependStream [0] (fun k => example48G ε' (2 * (k + 1) + 1))

@[simp] theorem base_zero (ε' : ℝ) : base ε' 0 = 0 := rfl

def aux (_p _n : ℕ) : Hilbert2 := 0

theorem base_g_mem (ε' : ℝ) {k : ℕ} (hk : 0 < k) :
    example48G ε' (2 * k + 1) ∈ Set.range (base ε') := by
  refine ⟨1 + (k - 1), ?_⟩
  have h := prependStream_add [0] (fun j => example48G ε' (2 * (j + 1) + 1)) (k - 1)
  simpa only [base, List.length_singleton, Nat.sub_add_cancel (by omega : 1 ≤ k)] using h

theorem selected_target_mem {r ε ε' : ℝ} {I : Set ℕ}
    (hI : I.Infinite) (hIK : I ⊆ primeIndices) :
    BlockDiagonal.language (base ε') (blocks r ε) aux I ∈ example48LanguageClass r ε ε' := by
  let I₁ := (fun p : ℕ => 2 * p) '' I
  let I₃ := Set.range Nat.succ
  have hI₁ : I₁.Infinite := hI.image (by intro i hi j hj hij; dsimp only at hij; omega)
  have hI₃ : I₃.Infinite := Set.infinite_range_of_injective Nat.succ_injective
  refine ⟨I₁, I, I₃, hI₁, hI, hI₃, ?_, ?_, ?_, ?_⟩
  · rintro k ⟨p, hp, rfl⟩
    exact Nat.mul_pos (by decide) (primeIndices_pos (hIK hp))
  · exact fun p hp => primeIndices_pos (hIK hp)
  · rintro k ⟨j, rfl⟩
    exact Nat.succ_pos j
  ext x
  constructor
  · rintro ((hx | ⟨p, hp, hblock⟩) | ⟨p, hp, n, haux⟩)
    · rw [base, range_prependStream] at hx
      rcases hx with hzero | ⟨k, rfl⟩
      · exact Or.inl (by simpa [example48Zero] using hzero)
      · exact Or.inr (Or.inr (Or.inr ⟨k + 1, ⟨k, rfl⟩, rfl⟩))
    · simp only [blocks, Finset.mem_insert, Finset.mem_singleton] at hblock
      rcases hblock with hU | hA
      · exact Or.inr (Or.inl ⟨2 * p, ⟨p, hp, rfl⟩, hU⟩)
      · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨p, hp, hA⟩)))
    · have : x = 0 := by simpa [aux] using haux.symm
      exact Or.inl (by simp [example48Zero, this])
  · rintro (hzero | hU | (hA | hG) | hD)
    · have hx0 : x = 0 := by simpa [example48Zero] using hzero
      exact Or.inl (Or.inl ⟨0, by simpa [base] using hx0.symm⟩)
    · obtain ⟨k, ⟨p, hp, rfl⟩, hx⟩ := hU
      exact Or.inl (Or.inr ⟨p, hp, by simp [blocks, hx]⟩)
    · obtain ⟨p, hp, hx⟩ := hA
      exact Or.inl (Or.inr ⟨p, hp, by simp [blocks, hx]⟩)
    · obtain ⟨p, hp, n, hx⟩ := hG
      apply Or.inl
      apply Or.inl
      rw [hx]
      exact base_g_mem ε' (pow_pos (primeIndices_pos (hIK hp)) n)
    · obtain ⟨k, ⟨j, rfl⟩, hx⟩ := hD
      apply Or.inl
      apply Or.inl
      rw [hx]
      exact base_g_mem ε' (Nat.succ_pos j)

theorem not_limit_of_large_generator_scale {r ε ε' γ γ' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r) (hε' : 0 < ε')
    (hγ : 0 ≤ γ) (hε'γ' : ε' ≤ γ') :
    ¬ GeneratableInLimitAt dist γ γ' (example48LanguageClass r ε ε') := by
  apply not_limit_of_infinite_blocks primeIndices_infinite (blocks r ε)
    (fun p _ q _ hpq => blocks_disjoint hr hε hεr hpq) (base ε') aux dist_self
    hγ (hε'.le.trans hε'γ')
  · change Set.range (base ε') ⊆ closedNeighborhood dist {0} γ'
    intro x hx
    rw [base, range_prependStream] at hx
    rw [mem_closedNeighborhood_singleton_iff]
    rcases hx with hzero | ⟨k, rfl⟩
    · have hx0 : x = 0 := by simpa using hzero
      rw [hx0, dist_self]
      exact hε'.le.trans hε'γ'
    · simpa [example48G, abs_of_pos hε'] using hε'γ'
  · intro p hp x hx
    obtain ⟨n, rfl⟩ := hx
    rw [mem_closedNeighborhood_singleton_iff]
    simpa [aux] using hε'.le.trans hε'γ'
  · exact fun I hI hIK => selected_target_mem hI hIK

end

end GenLimit.MetricSpaces.HilbertAxisReservoir.Example48Negative
