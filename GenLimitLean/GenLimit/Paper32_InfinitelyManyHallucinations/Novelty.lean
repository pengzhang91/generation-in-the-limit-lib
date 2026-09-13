import GenLimit.Paper32_InfinitelyManyHallucinations.Exploration

/-!
# Novelty accounting

This file checks the finite-prefix arithmetic behind Definition 3.7 and
Theorem 4.9.  It separates the algorithm-specific fact that non-novel outputs
occur only on exploration rounds from the generic conclusion that a
`γ`-admissible schedule enforces `γ`-novelty.
-/

namespace GenLimit.InfinitelyManyHallucinations

theorem novelHistory_subset_stage
    (adversary guess : Exhaustion) (n : ℕ) :
    novelHistory adversary guess n ⊆ guess.stage n := by
  induction n with
  | zero => simp [novelHistory, guess.stage_zero]
  | succ n ih =>
      rw [novelHistory, guess.stage_succ_eq_stage_union_increment]
      exact Finset.union_subset_union ih Finset.sdiff_subset

theorem card_novelHistory_add_nonNovel
    (adversary guess : Exhaustion) (n : ℕ) :
    (novelHistory adversary guess n).card +
        (guess.stage n \ novelHistory adversary guess n).card =
      (guess.stage n).card := by
  rw [Finset.card_sdiff_of_subset
    (novelHistory_subset_stage adversary guess n)]
  have hcard := Finset.card_le_card
    (novelHistory_subset_stage adversary guess n)
  omega

/-- The generic finite-prefix novelty calculation used by Algorithm 4.9.
The algorithm-specific premise says that every output not counted as novel
can be charged injectively to an exploration round. -/
theorem gammaNovel_of_nonNovel_le_exploration
    {E : ExplorationSet} {γ : ℝ}
    (hadmissible : E.GammaAdmissible γ)
    (adversary guess : Exhaustion)
    (hnonNovel : ∀ n,
      (guess.stage n \ novelHistory adversary guess n).card ≤
        explorationCount E.carrier (guess.stage n).card) :
    GammaNovel γ adversary guess := by
  intro n hpositive
  let total := (guess.stage n).card
  let novel := (novelHistory adversary guess n).card
  let nonNovel :=
    (guess.stage n \ novelHistory adversary guess n).card
  have hsum : novel + nonNovel = total := by
    simpa [total, novel, nonNovel] using
      card_novelHistory_add_nonNovel adversary guess n
  have hnonNovelNat :
      nonNovel ≤ explorationCount E.carrier total := by
    simpa [total, nonNovel] using hnonNovel n
  have hnonNovelReal :
      (nonNovel : ℝ) ≤ (1 - γ) * (total : ℝ) := by
    have hcast :
        (nonNovel : ℝ) ≤
          (explorationCount E.carrier total : ℝ) := by
      exact_mod_cast hnonNovelNat
    exact hcast.trans (hadmissible total)
  have htotalPos : (0 : ℝ) < total := by
    exact_mod_cast hpositive
  have hsumReal : (novel : ℝ) + (nonNovel : ℝ) = (total : ℝ) := by
    exact_mod_cast hsum
  change γ ≤ (novel : ℝ) / (total : ℝ)
  rw [le_div_iff₀ htotalPos]
  linarith

theorem increment_sdiff_adversary_eq_self_of_novel
    {adversary guess : Exhaustion} (hnovel : Novel adversary guess)
    (n : ℕ) :
    guess.increment n \ adversary.stage n = guess.increment n := by
  exact Finset.sdiff_eq_self_of_disjoint (hnovel n)

theorem novelHistory_eq_stage_of_novel
    {adversary guess : Exhaustion} (hnovel : Novel adversary guess)
    (n : ℕ) :
    novelHistory adversary guess n = guess.stage n := by
  induction n with
  | zero => simp [novelHistory, guess.stage_zero]
  | succ n ih =>
      rw [novelHistory, ih,
        increment_sdiff_adversary_eq_self_of_novel hnovel,
        ← guess.stage_succ_eq_stage_union_increment]

/-- Strict novelty is exactly the endpoint `γ = 1` of the finite-prefix
notion. -/
theorem gammaNovel_one_of_novel
    {adversary guess : Exhaustion} (hnovel : Novel adversary guess) :
    GammaNovel 1 adversary guess := by
  intro n hpositive
  rw [novelHistory_eq_stage_of_novel hnovel]
  have hne : ((guess.stage n).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpositive)
  exact le_of_eq (div_self hne).symm

theorem GammaNovel.mono
    {γ δ : ℝ} {adversary guess : Exhaustion}
    (h : GammaNovel γ adversary guess) (hδγ : δ ≤ γ) :
    GammaNovel δ adversary guess := by
  intro n hn
  exact hδγ.trans (h n hn)

end GenLimit.InfinitelyManyHallucinations
