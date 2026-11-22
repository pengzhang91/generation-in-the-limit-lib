import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.IndexMinimax
import GenLimit.Support.Asymptotics.SparseSquares
import Mathlib.Data.Finset.Lattice.Fold

/-! # The zero truth index and a family attaining it -/
namespace GenLimit.KleinbergWei.DensityMeasures
open Filter TowerTopology

def VanishingBreadth (C : LanguageFamily) (z : ℕ) (O : OrderedLanguage) : Prop :=
  ∀ A, ValidIndexRule C A → ∃ s, Presents s (C z) ∧ indexBreadth C O A s = 0

/-- Theorem 4.9 with both players and the existence of its value. -/
theorem theorem_4_9 (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (z : ℕ) (O : OrderedLanguage) (hc : O.carrier = C z) :
    ∃ τ, IsTruthIndex (Set.range C) ⟨C z,z,rfl⟩ O τ ∧
      (∀ A, ValidIndexRule C A → ∃ s, Presents s (C z) ∧ indexBreadth C O A s ≤ τ) ∧
      ValidIndexRule C (breadthSelector C) ∧
      ∀ s, Presents s (C z) → τ ≤ indexBreadth C O (breadthSelector C) s := by
  obtain ⟨τ,hτ⟩ := exists_truthIndex (X := Set.range C) ⟨C z,z,rfl⟩ O hc
  exact ⟨τ,hτ,theorem_4_9_adversary C hi z O hc hτ,breadthSelector_valid C,
    fun _ hs ↦ theorem_4_9_achievability C z O hc hτ hs⟩

/-- Overview 2.4 / Theorem 4.1. -/
theorem theorem_4_1 (C : LanguageFamily) (hi : ∀ i, (C i).Infinite)
    (z : ℕ) (O : OrderedLanguage) (hc : O.carrier = C z) :
    VanishingBreadth C z O ↔ ∀ ε : ℝ, 0 < ε →
      HasPerfectTowerBound (Set.range C) ⟨C z,z,rfl⟩ O ε := by
  obtain ⟨τ,hτ,hupper,hvalid,hlower⟩ := theorem_4_9 C hi z O hc
  constructor
  · intro h
    obtain ⟨s,hs,he⟩ := h _ hvalid
    have hz : τ = 0 := le_antisymm ((hlower s hs).trans he.le) hτ.1
    have ht : HasAnyPerfectTower (Set.range C) ⟨C z,z,rfl⟩ := by
      by_contra hn
      linarith [hτ.2.2.2 hn]
    simpa [hz] using (hτ.2.2.1 ht).1
  · intro tall A hv
    obtain ⟨_,tower,ht,_⟩ := tall 1 zero_lt_one
    have hz : τ ≤ 0 := (hτ.2.2.1 ⟨tower,ht⟩).2 0 (by simpa using tall)
    obtain ⟨s,hs,hd⟩ := hupper A hv
    refine ⟨s,hs,le_antisymm (hd.trans hz) ?_⟩
    exact le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun _ ↦ O.upperDensity_le_one _))
      (Eventually.of_forall (fun _ ↦ O.upperDensity_nonneg _))

namespace SquareTower

def natOrder : OrderedLanguage := ⟨Set.univ,id,Function.injective_id,Set.range_id⟩
def squares : Language := {n | SparseSquares.IsSquare n}

theorem squares_infinite : squares.Infinite := by
  refine (Set.infinite_range_of_injective (f := fun k : ℕ ↦ k*k) ?_).mono ?_
  · intro a b he
    nlinarith
  · rintro _ ⟨k,rfl⟩
    exact ⟨k,rfl⟩

theorem squares_upperDensity : natOrder.upperDensity squares = 0 := by
  classical
  apply Tendsto.limsup_eq
  apply squeeze_zero (natOrder.prefixRatio_nonneg squares) _ SparseSquares.natSqrt_add_one_div_self_tendsto_zero
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · rw [OrderedLanguage.prefixRatio, if_neg hn]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hcount : natOrder.prefixCount squares n = Nat.count SparseSquares.IsSquare n := by
      rw [Nat.count_eq_card_filter_range]
      rfl
    rw [hcount]
    exact_mod_cast SparseSquares.count_isSquare_le_sqrt_add_one n

def layer (n : ℕ) : Language := squares ∪ (Finset.range n : Set ℕ)

def sparseFamily : LanguageFamily
  | 0 => Set.univ
  | n+1 => layer n

end SquareTower

open SquareTower

/-- Overview Theorem 2.3. Finite initial segments padded by the squares
approximate the whole domain and each has upper density zero. -/
theorem theorem_2_3 :
    ∃ (C : LanguageFamily) (z : ℕ) (O : OrderedLanguage),
      (∀ i, (C i).Infinite) ∧ O.carrier = C z ∧ VanishingBreadth C z O := by
  have hi (i : ℕ) : (sparseFamily i).Infinite := by
    cases i with
    | zero => exact Set.infinite_univ
    | succ n => exact squares_infinite.mono Set.subset_union_left
  refine ⟨sparseFamily,0,natOrder,hi,rfl,(theorem_4_1 _ hi _ _ rfl).2 ?_⟩
  intro ε hε
  apply (towerBound_iff_finite_extensions (X := Set.range sparseFamily) (K := ⟨_,0,rfl⟩) natOrder rfl (s := id) Set.range_id ε).2
  intro F _
  let n := F.sup id + 1
  have hd : natOrder.upperDensity (sparseFamily (n+1)) ≤ 0 := by
    have h := natOrder.upperDensity_union_le squares (Finset.range n : Set ℕ)
    rw [squares_upperDensity, natOrder.upperDensity_eq_zero_of_finite
      (Finset.range n).finite_toSet, add_zero] at h
    exact h
  refine ⟨_,⟨n+1,rfl⟩, Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _,?_⟩, ?_,hd.trans hε.le⟩
  · intro he
    change sparseFamily (n+1) = natOrder.carrier at he
    rw [he,natOrder.upperDensity_carrier] at hd
    norm_num at hd
  · intro x hx
    exact Or.inr (Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)))

end GenLimit.KleinbergWei.DensityMeasures
