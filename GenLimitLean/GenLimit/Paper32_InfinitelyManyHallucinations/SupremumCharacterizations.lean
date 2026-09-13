import GenLimit.Paper32_InfinitelyManyHallucinations.NoNoveltyExploration

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
    countIn L S ≤ countIn M S := by
  classical
  unfold countIn
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hLM hx.2⟩

theorem membershipFraction_mono
    {L M : Language} (hLM : L ⊆ M) (S : Finset ℕ) :
    membershipFraction L S ≤ membershipFraction M S := by
  by_cases hS : S.card = 0
  · simp [membershipFraction, hS]
  · simp only [membershipFraction, hS, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast countIn_mono hLM S)
      (Nat.cast_nonneg _)

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

/-! ## Canonical and aligned exhaustions -/

/-- Ambient-order finite prefixes of an arbitrary language. -/
noncomputable def ambientExhaustion (L : Language) : Exhaustion := by
  classical
  exact
    { stage := fun n => (Finset.range n).filter fun x => x ∈ L
      stage_zero := by simp
      monotone_stage := by
        intro m n hmn x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
        exact ⟨hx.1.trans_le hmn, hx.2⟩ }

theorem ambientExhaustion_exhausts (L : Language) :
    (ambientExhaustion L).Exhausts L := by
  classical
  apply Set.ext
  intro x
  constructor
  · rintro ⟨n, hx⟩
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    exact ⟨x + 1, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_self x), hx⟩⟩

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
    unfold countIn
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
  simp only [membershipFraction]
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

/-! ## Capacity-preserving target exhaustions -/

/-- The elements of a finite stage belonging to a fixed language. -/
noncomputable def finiteRestriction
    (S : Finset ℕ) (L : Language) : Finset ℕ := by
  classical
  exact S.filter fun x => x ∈ L

theorem finiteRestriction_subset (S : Finset ℕ) (L : Language) :
    finiteRestriction S L ⊆ S := by
  classical
  exact Finset.filter_subset _ _

/-- Restrict every stage of an exhaustion to a fixed language. -/
noncomputable def restrictedExhaustion
    (E : Exhaustion) (L : Language) : Exhaustion := by
  classical
  exact
    { stage := fun n => finiteRestriction (E.stage n) L
      stage_zero := by simp [E.stage_zero, finiteRestriction]
      monotone_stage := by
        intro m n hmn x hx
        simp only [finiteRestriction, Finset.mem_filter] at hx ⊢
        exact ⟨E.monotone_stage hmn hx.1, hx.2⟩ }

theorem restrictedExhaustion_increment_succ
    (E : Exhaustion) (L : Language) (n : ℕ) :
    (restrictedExhaustion E L).increment (n + 1) =
      finiteRestriction (E.increment (n + 1)) L := by
  classical
  ext x
  simp only [restrictedExhaustion, finiteRestriction,
    Exhaustion.increment, Finset.mem_filter, Finset.mem_sdiff]
  tauto

theorem restrictedExhaustion_limit
    (E : Exhaustion) (L : Language) :
    (restrictedExhaustion E L).limit = E.limit ∩ L := by
  classical
  ext x
  constructor
  · rintro ⟨n, hx⟩
    exact ⟨⟨n, (Finset.mem_filter.mp hx).1⟩,
      (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨⟨n, hxStage⟩, hxL⟩
    exact ⟨n, Finset.mem_filter.mpr ⟨hxStage, hxL⟩⟩

theorem restrictedExhaustion_boundedBy
    {E : Exhaustion} {L : Language} {f : ℕ → ℕ}
    (hbounded : E.BoundedBy f) :
    (restrictedExhaustion E L).BoundedBy f := by
  intro n
  rw [restrictedExhaustion_increment_succ]
  exact (Finset.card_le_card
    (finiteRestriction_subset (E.increment (n + 1)) L)).trans
      (hbounded n)

theorem ambientExhaustion_stage_diff_card_le
    (L : Language) (a b : ℕ) :
    ((ambientExhaustion L).stage b \
      (ambientExhaustion L).stage a).card ≤ b - a := by
  classical
  have hsubset :
      (ambientExhaustion L).stage b \
          (ambientExhaustion L).stage a ⊆
        Finset.Ico a b := by
    intro x hx
    have hxb := (Finset.mem_sdiff.mp hx).1
    have hnot := (Finset.mem_sdiff.mp hx).2
    have hxb' : x < b ∧ x ∈ L := by
      simpa [ambientExhaustion] using hxb
    have hax : a ≤ x := by
      by_contra hxa
      apply hnot
      simp [ambientExhaustion, Nat.lt_of_not_ge hxa, hxb'.2]
    exact Finset.mem_Ico.mpr ⟨hax, hxb'.1⟩
  calc
    ((ambientExhaustion L).stage b \
        (ambientExhaustion L).stage a).card ≤
        (Finset.Ico a b).card := Finset.card_le_card hsubset
    _ = b - a := by simp

/-- Exhaust `L` using the cardinality growth of `clock`.  The construction
adds no more elements at a step than `clock` does. -/
noncomputable def cardinalityClockedExhaustion
    (L : Language) (clock : Exhaustion) : Exhaustion := by
  classical
  exact
    { stage := fun n => (ambientExhaustion L).stage (clock.stage n).card
      stage_zero := by simp [clock.stage_zero, ambientExhaustion]
      monotone_stage := by
        intro m n hmn
        exact (ambientExhaustion L).monotone_stage
          (Finset.card_le_card (clock.monotone_stage hmn)) }

theorem cardinalityClockedExhaustion_exhausts
    (L : Language) (clock : Exhaustion)
    (hinfinite : clock.limit.Infinite) :
    (cardinalityClockedExhaustion L clock).Exhausts L := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨n, hx⟩
    exact (Finset.mem_filter.mp hx).2
  · intro x hxL
    have heventually :=
      (clock.card_tendsto_atTop_of_limit_infinite hinfinite).eventually
        (eventually_ge_atTop (x + 1))
    obtain ⟨n, hn⟩ := heventually.exists
    exact ⟨n, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_of_lt_of_le
        (Nat.lt_succ_self x) hn), hxL⟩⟩

theorem cardinalityClockedExhaustion_boundedBy
    (L : Language) {clock : Exhaustion} {f : ℕ → ℕ}
    (hbounded : clock.BoundedBy f) :
    (cardinalityClockedExhaustion L clock).BoundedBy f := by
  intro n
  let a := (clock.stage n).card
  let b := (clock.stage (n + 1)).card
  have hclockIncrement :
      (clock.increment (n + 1)).card = b - a := by
    rw [Exhaustion.increment,
      Finset.card_sdiff_of_subset
        (clock.monotone_stage (Nat.le_succ n))]
  change ((ambientExhaustion L).stage b \
    (ambientExhaustion L).stage a).card ≤ f (n + 1)
  exact (ambientExhaustion_stage_diff_card_le L a b).trans
    (by rw [← hclockIncrement]; exact hbounded n)

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
