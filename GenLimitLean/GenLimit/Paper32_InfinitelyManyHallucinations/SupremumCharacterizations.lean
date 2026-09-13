import GenLimit.Paper32_InfinitelyManyHallucinations.NoNoveltyExploration
import GenLimit.Paper32_InfinitelyManyHallucinations.ExhaustionOperations

/-!
# Paper 32: exhaustion-supremum characterizations

This module formalizes the two optimization statements in Section 2 of
Strauss--Butoi--Cotterell.  It keeps the exhaustion-to-exhaustion quantities
separate from the canonical membership and coverage quantities, so the
suprema appearing in the source remain visible in the public statements.

Lemma 2.2 is proved directly for an arbitrary target exhaustion.  Theorem 2.1
uses the source assumption that the guess exhaustion has an infinite limit.
The proof below repairs the source's finite-guess ambiguity by making that
assumption explicit and uses a capacity-preserving sparse completion when the
valid part of the guess is infinite.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter

/-! ## Exhaustion-level metrics -/

theorem countIn_mono
    {L M : Language} (hLM : L ⊆ M) (S : Finset ℕ) :
    countIn L S ≤ countIn M S :=
  GenLimit.Generic.acceptedCount_mono (fun _ hx => hLM hx) S

theorem membershipFraction_mono
    {L M : Language} (hLM : L ⊆ M) (S : Finset ℕ) :
    membershipFraction L S ≤ membershipFraction M S :=
  GenLimit.Generic.acceptedFraction_mono (fun _ hx => hLM hx) S

/-- Definition 2.1's lower precision between a target exhaustion and a guess
exhaustion. -/
noncomputable def exhaustionLowerPrecision
    (target guess : Exhaustion) : ℝ :=
  liminf
    (fun n => membershipFraction (target.stage n : Language) (guess.stage n))
    atTop

/-- Definition 2.1's lower recall between a target exhaustion and a guess
exhaustion. -/
noncomputable def exhaustionLowerRecall
    (target guess : Exhaustion) : ℝ :=
  liminf
    (fun n => membershipFraction (guess.stage n : Language) (target.stage n))
    atTop

/-- The right side of Lemma 2.2 for an arbitrary fixed target exhaustion. -/
noncomputable def coverageLowerRecall
    (target : Exhaustion) (guess : Language) : ℝ :=
  liminf (fun n => membershipFraction guess (target.stage n)) atTop

theorem exhaustionLowerPrecision_nonneg
    (target guess : Exhaustion) :
    0 ≤ exhaustionLowerPrecision target guess := by
  unfold exhaustionLowerPrecision
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => membershipFraction_le_one
        (target.stage n : Language) (guess.stage n))
  · exact Eventually.of_forall fun n =>
      membershipFraction_nonneg (target.stage n : Language) (guess.stage n)

theorem exhaustionLowerPrecision_le_one
    (target guess : Exhaustion) :
    exhaustionLowerPrecision target guess ≤ 1 := by
  unfold exhaustionLowerPrecision
  apply liminf_le_of_frequently_le
  · exact (Eventually.of_forall fun n =>
      membershipFraction_le_one
        (target.stage n : Language) (guess.stage n)).frequently
  · exact isBoundedUnder_of ⟨0, fun n =>
      membershipFraction_nonneg (target.stage n : Language) (guess.stage n)⟩

theorem exhaustionLowerRecall_nonneg
    (target guess : Exhaustion) :
    0 ≤ exhaustionLowerRecall target guess := by
  unfold exhaustionLowerRecall
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => membershipFraction_le_one
        (guess.stage n : Language) (target.stage n))
  · exact Eventually.of_forall fun n =>
      membershipFraction_nonneg (guess.stage n : Language) (target.stage n)

theorem exhaustionLowerRecall_le_one
    (target guess : Exhaustion) :
    exhaustionLowerRecall target guess ≤ 1 := by
  unfold exhaustionLowerRecall
  apply liminf_le_of_frequently_le
  · exact (Eventually.of_forall fun n =>
      membershipFraction_le_one
        (guess.stage n : Language) (target.stage n)).frequently
  · exact isBoundedUnder_of ⟨0, fun n =>
      membershipFraction_nonneg (guess.stage n : Language) (target.stage n)⟩

theorem coverageLowerRecall_nonneg
    (target : Exhaustion) (guess : Language) :
    0 ≤ coverageLowerRecall target guess := by
  unfold coverageLowerRecall
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => membershipFraction_le_one guess (target.stage n))
  · exact Eventually.of_forall fun n =>
      membershipFraction_nonneg guess (target.stage n)

theorem coverageLowerRecall_le_one
    (target : Exhaustion) (guess : Language) :
    coverageLowerRecall target guess ≤ 1 := by
  unfold coverageLowerRecall
  apply liminf_le_of_frequently_le
  · exact (Eventually.of_forall fun n =>
      membershipFraction_le_one guess (target.stage n)).frequently
  · exact isBoundedUnder_of ⟨0, fun n =>
      membershipFraction_nonneg guess (target.stage n)⟩

/-! ## Aligned exhaustions -/

/-- A guess exhaustion synchronized with the target stages.  It immediately
contains every currently measured target element that belongs to `guess`,
while an ambient prefix ensures that its limit is all of `guess`. -/
noncomputable def recallAlignedExhaustion
    (target : Exhaustion) (guess : Language) : Exhaustion := by
  classical
  exact
    { stage := fun n =>
        (target.stage n).filter (fun x => x ∈ guess) ∪
          (ambientExhaustion guess).stage n
      stage_zero := by simp [target.stage_zero, ambientExhaustion]
      monotone_stage := by
        intro m n hmn
        apply Finset.union_subset_union
        · intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨target.monotone_stage hmn hx.1, hx.2⟩
        · exact (ambientExhaustion guess).monotone_stage hmn }

theorem recallAlignedExhaustion_exhausts
    (target : Exhaustion) (guess : Language) :
    (recallAlignedExhaustion target guess).Exhausts guess := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨n, hx⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hx).2
  · intro x hx
    exact ⟨x + 1, Finset.mem_union_right _
      (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_self x), hx⟩)⟩

theorem recallAlignedExhaustion_fraction
    (target : Exhaustion) (guess : Language) (n : ℕ) :
    membershipFraction
        ((recallAlignedExhaustion target guess).stage n : Language)
        (target.stage n) =
      membershipFraction guess (target.stage n) := by
  classical
  have hcount :
      countIn
          ((recallAlignedExhaustion target guess).stage n : Language)
          (target.stage n) =
        countIn guess (target.stage n) := by
    rw [countIn_eq_filter_card, countIn_eq_filter_card]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hxTarget, hxAligned⟩
      refine ⟨hxTarget, ?_⟩
      rcases Finset.mem_union.mp hxAligned with hx | hx
      · exact (Finset.mem_filter.mp hx).2
      · exact (Finset.mem_filter.mp hx).2
    · rintro ⟨hxTarget, hxGuess⟩
      exact ⟨hxTarget, Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hxTarget, hxGuess⟩)⟩
  simp only [membershipFraction_eq]
  rw [hcount]

/-! ## Lemma 2.2 -/

def lowerRecallValues (target : Exhaustion) (guess : Language) : Set ℝ :=
  {r | ∃ guessExhaustion : Exhaustion,
    guessExhaustion.Exhausts guess ∧
      r = exhaustionLowerRecall target guessExhaustion}

/-- The supremum over all exhaustions of the fixed guess language appearing
on the left side of Lemma 2.2. -/
noncomputable def bestExhaustionLowerRecall
    (target : Exhaustion) (guess : Language) : ℝ :=
  sSup (lowerRecallValues target guess)

theorem exhaustionLowerRecall_le_coverage
    (target guessExhaustion : Exhaustion) (guess : Language)
    (hexhausts : guessExhaustion.Exhausts guess) :
    exhaustionLowerRecall target guessExhaustion ≤
      coverageLowerRecall target guess := by
  unfold exhaustionLowerRecall coverageLowerRecall
  apply liminf_le_liminf
  · exact Eventually.of_forall fun n =>
      membershipFraction_mono
        (fun x hx => by
          rw [← hexhausts]
          exact guessExhaustion.stage_subset_limit n hx)
        (target.stage n)
  · exact isBoundedUnder_of ⟨0, fun n =>
      membershipFraction_nonneg
        (guessExhaustion.stage n : Language) (target.stage n)⟩
  · exact isCoboundedUnder_ge_of_le atTop fun n =>
      membershipFraction_le_one guess (target.stage n)

/-- Lemma 2.2: optimizing exhaustion-level lower recall over all exhaustions
of the guess language gives its coverage-based lower recall. -/
theorem lemma_2_2 (target : Exhaustion) (guess : Language) :
    bestExhaustionLowerRecall target guess =
      coverageLowerRecall target guess := by
  apply le_antisymm
  · unfold bestExhaustionLowerRecall
    apply csSup_le
    · exact ⟨exhaustionLowerRecall target
          (recallAlignedExhaustion target guess),
        ⟨recallAlignedExhaustion target guess,
          recallAlignedExhaustion_exhausts target guess, rfl⟩⟩
    · intro r hr
      obtain ⟨guessExhaustion, hexhausts, rfl⟩ := hr
      exact exhaustionLowerRecall_le_coverage
        target guessExhaustion guess hexhausts
  · unfold bestExhaustionLowerRecall
    have haligned :
        exhaustionLowerRecall target
            (recallAlignedExhaustion target guess) =
          coverageLowerRecall target guess := by
      unfold exhaustionLowerRecall coverageLowerRecall
      exact liminf_congr (Eventually.of_forall
        (recallAlignedExhaustion_fraction target guess))
    rw [← haligned]
    apply le_csSup
    · exact ⟨1, fun r hr => by
        obtain ⟨guessExhaustion, _hexhausts, rfl⟩ := hr
        exact exhaustionLowerRecall_le_one target guessExhaustion⟩
    · exact ⟨recallAlignedExhaustion target guess,
        recallAlignedExhaustion_exhausts target guess, rfl⟩

/-! ## Theorem 2.1: bounded membership precision -/

def boundedLowerPrecisionValues
    (f : ℕ → ℕ) (L : Language) (guess : Exhaustion) : Set ℝ :=
  {r | ∃ target : Exhaustion,
    target.Exhausts L ∧ target.BoundedBy f ∧
      r = exhaustionLowerPrecision target guess}

/-- The bounded-exhaustion supremum on the left side of Theorem 2.1. -/
noncomputable def bestBoundedLowerPrecision
    (f : ℕ → ℕ) (L : Language) (guess : Exhaustion) : ℝ :=
  sSup (boundedLowerPrecisionValues f L guess)

theorem exhaustionLowerPrecision_le_membership
    (target guess : Exhaustion) (L : Language)
    (hexhausts : target.Exhausts L) :
    exhaustionLowerPrecision target guess ≤
      lowerMembershipPrecision L guess := by
  unfold exhaustionLowerPrecision lowerMembershipPrecision
  apply liminf_le_liminf
  · exact Eventually.of_forall fun n =>
      membershipFraction_mono
        (fun x hx => by
          rw [← hexhausts]
          exact target.stage_subset_limit n hx)
        (guess.stage n)
  · exact isBoundedUnder_of ⟨0, fun n =>
      membershipFraction_nonneg
        (target.stage n : Language) (guess.stage n)⟩
  · exact isCoboundedUnder_ge_of_le atTop fun n =>
      membershipFraction_le_one L (guess.stage n)

theorem boundedLowerPrecisionValues_nonempty
    (f : ℕ → ℕ) (L : Language) (guess : Exhaustion)
    (hinfinite : guess.limit.Infinite) (hbounded : guess.BoundedBy f) :
    (boundedLowerPrecisionValues f L guess).Nonempty := by
  let target := cardinalityClockedExhaustion L guess
  exact ⟨exhaustionLowerPrecision target guess,
    ⟨target,
      cardinalityClockedExhaustion_exhausts L guess hinfinite,
      cardinalityClockedExhaustion_boundedBy L hbounded,
      rfl⟩⟩

theorem bestBoundedLowerPrecision_le_membership
    (f : ℕ → ℕ) (L : Language) (guess : Exhaustion)
    (hinfinite : guess.limit.Infinite) (hbounded : guess.BoundedBy f) :
    bestBoundedLowerPrecision f L guess ≤
      lowerMembershipPrecision L guess := by
  unfold bestBoundedLowerPrecision
  apply csSup_le
  · exact boundedLowerPrecisionValues_nonempty
      f L guess hinfinite hbounded
  · intro r hr
    obtain ⟨target, hexhausts, _hboundedTarget, rfl⟩ := hr
    exact exhaustionLowerPrecision_le_membership
      target guess L hexhausts

end GenLimit.InfinitelyManyHallucinations
