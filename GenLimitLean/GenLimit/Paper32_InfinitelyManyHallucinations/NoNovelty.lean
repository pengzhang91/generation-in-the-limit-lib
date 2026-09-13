import GenLimit.Paper32_InfinitelyManyHallucinations.Precision
import GenLimit.Paper32_InfinitelyManyHallucinations.Recall
import GenLimit.Paper32_InfinitelyManyHallucinations.TailPrecision

/-!
# The parrot baseline without novelty

This is the paper's appendix theorem for generation without novelty while
retaining perfect tail precision.  The generator copies the current
adversarial set.  It is deliberately separated from Theorem 4.3, whose rare
exploration rounds trade tail precision for perfect recall.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter

/-- The history-sensitive generator that copies the adversary's current
cumulative stage. -/
def parrotGenerator : BatchGenerator :=
  fun n adversaryHistory _previousGuess =>
    adversaryHistory ⟨n, Nat.lt_succ_self n⟩

@[simp] theorem generatedStages_parrotGenerator
    (adversary : Exhaustion) (n : ℕ) :
    generatedStages parrotGenerator adversary n = adversary.stage n := by
  induction n with
  | zero => simpa [generatedStages] using adversary.stage_zero.symm
  | succ n ih =>
      simp only [generatedStages, parrotGenerator]
      rw [ih]
      exact Finset.union_eq_right.mpr
        (adversary.monotone_stage (Nat.le_succ n))

theorem generatedExhaustion_parrotGenerator
    (adversary : Exhaustion) :
    generatedExhaustion parrotGenerator adversary = adversary := by
  cases adversary with
  | mk stage hzero hmono =>
      apply Exhaustion.ext
      funext n
      exact generatedStages_parrotGenerator
        ⟨stage, hzero, hmono⟩ n

theorem eventually_stage_nonempty_of_limit_infinite
    {E : Exhaustion} (hinfinite : E.limit.Infinite) :
    ∀ᶠ n : ℕ in atTop, (E.stage n).card ≠ 0 := by
  obtain ⟨x, hx⟩ := hinfinite.nonempty
  rcases hx with ⟨N, hxN⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  exact Finset.card_ne_zero.mpr
    ⟨x, E.monotone_stage hn hxN⟩

theorem invalidFraction_stage_eq_zero
    {L : Language} {E : Exhaustion}
    (hvalid : E.limit ⊆ L) (n : ℕ) :
    invalidFraction L (E.stage n) = 0 := by
  classical
  have hinvalid : invalidCount L (E.stage n) = 0 := by
    unfold invalidCount
    apply Finset.card_eq_zero.mpr
    rw [Finset.filter_eq_empty_iff]
    intro x hxStage hxNot
    exact hxNot (hvalid (E.stage_subset_limit n hxStage))
  simp [invalidFraction, hinvalid]

theorem lowerMembershipPrecision_parrotGenerator
    {L : Language} {adversary : Exhaustion}
    (hinfinite : adversary.limit.Infinite)
    (hvalid : adversary.limit ⊆ L) :
    lowerMembershipPrecision L
        (generatedExhaustion parrotGenerator adversary) = 1 := by
  rw [generatedExhaustion_parrotGenerator]
  apply lowerMembershipPrecision_eq_one_of_invalidFraction_tendsto_zero
    (eventually_stage_nonempty_of_limit_infinite hinfinite)
  simpa only [invalidFraction_stage_eq_zero hvalid] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

theorem lowerTailPrecision_parrotGenerator
    {L : Language} {adversary : Exhaustion}
    (hvalid : adversary.limit ⊆ L) :
    lowerTailPrecision L
        (generatedExhaustion parrotGenerator adversary) = 1 := by
  rw [generatedExhaustion_parrotGenerator]
  apply eventuallyValid_implies_lowerTailPrecision_one
  refine ⟨0, ?_⟩
  intro n _hn x hx
  exact hvalid (adversary.stage_subset_limit n
    (adversary.increment_subset_stage n hx))

theorem lowerRecall_parrotGenerator
    (target : GenLimit.KleinbergWei.OrderedLanguage)
    (adversary : Exhaustion) :
    lowerRecall target
        (generatedExhaustion parrotGenerator adversary).limit =
      lowerRecall target adversary.limit := by
  rw [generatedExhaustion_parrotGenerator]

theorem boundedBy_parrotGenerator
    (f : ℕ → ℕ) {adversary : Exhaustion}
    (hbounded : adversary.BoundedBy f) :
    (generatedExhaustion parrotGenerator adversary).BoundedBy f := by
  simpa [generatedExhaustion_parrotGenerator] using hbounded

/-- Exact appendix baseline: without a novelty requirement, copying the
adversary preserves its recall and batch bound and has perfect precision and
tail precision. -/
theorem valid_generation_without_novelty
    (target : GenLimit.KleinbergWei.OrderedLanguage)
    (L : Language) (f : ℕ → ℕ) (α : ℝ)
    (adversary : Exhaustion)
    (hinfinite : adversary.limit.Infinite)
    (hvalid : adversary.limit ⊆ L)
    (hbounded : adversary.BoundedBy f)
    (hrecall : α ≤ lowerRecall target adversary.limit) :
    let guess := generatedExhaustion parrotGenerator adversary
    guess.BoundedBy f ∧
      α ≤ lowerRecall target guess.limit ∧
      lowerMembershipPrecision L guess = 1 ∧
      lowerTailPrecision L guess = 1 := by
  dsimp only
  refine ⟨boundedBy_parrotGenerator f hbounded, ?_, ?_, ?_⟩
  · simpa [lowerRecall_parrotGenerator] using hrecall
  · exact lowerMembershipPrecision_parrotGenerator hinfinite hvalid
  · exact lowerTailPrecision_parrotGenerator hvalid

end GenLimit.InfinitelyManyHallucinations
