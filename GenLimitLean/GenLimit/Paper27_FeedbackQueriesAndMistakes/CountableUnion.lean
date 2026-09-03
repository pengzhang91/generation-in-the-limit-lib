import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceSetMistake
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceQuery

/-!
# Paper 27: closure under countable unions

This module formalizes Corollary 3.6 and its Appendix A.3 components.  The
mathematical core is that countably many countable inner covers can be
flattened with `Nat.pair`; Theorems 3.1 and 3.4 then transfer that closure to
the two source-faithful feedback models.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-- Flatten countably many countable inner covers into a cover of the union. -/
def CountableInnerCover.iUnion
    {classes : ℕ → LanguageClass α}
    (inner : ∀ i, CountableInnerCover (classes i)) :
    CountableInnerCover (⋃ i, classes i) where
  cover := fun n =>
    let coordinate := Nat.unpair n
    (inner coordinate.1).cover coordinate.2
  infinite_cover := by
    intro n
    exact (inner (Nat.unpair n).1).infinite_cover (Nat.unpair n).2
  contained := by
    intro L hL
    simp only [Set.mem_iUnion] at hL
    obtain ⟨i, hi⟩ := hL
    obtain ⟨j, hj⟩ := (inner i).contained L hi
    refine ⟨Nat.pair i j, ?_⟩
    dsimp
    have hfst : (Nat.unpair (Nat.pair i j)).1 = i := by
      exact congrArg Prod.fst (Nat.unpair_pair i j)
    have hsnd : (Nat.unpair (Nat.pair i j)).2 = j := by
      exact congrArg Prod.snd (Nat.unpair_pair i j)
    rw [hfst, hsnd]
    exact hj

/-- Existence-form closure of countable inner covers under countable unions. -/
theorem hasCountableInnerCover_iUnion
    {classes : ℕ → LanguageClass α}
    (hinner : ∀ i, HasCountableInnerCover (classes i)) :
    HasCountableInnerCover (⋃ i, classes i) := by
  classical
  exact ⟨CountableInnerCover.iUnion fun i => (hinner i).some⟩

/-- Appendix Corollary A.2: element-valued mistake-feedback generation is
closed under countable unions. -/
theorem corollary_A_2_countableUnion_mistake
    [Countable α] [Infinite α]
    (classes : ℕ → LanguageClass α)
    (hinfinite : ∀ i L, L ∈ classes i → L.Infinite)
    (hgenerate : ∀ i, SourceElementMistakeGeneratable (classes i)) :
    SourceElementMistakeGeneratable (⋃ i, classes i) := by
  apply countableInnerCover_implies_sourceElementMistake
  apply hasCountableInnerCover_iUnion
  intro i
  exact
    (theorem_3_1_elementMistake_characterization
      (classes i) (hinfinite i)).mp (hgenerate i)

/-- Appendix Corollary A.3: source-timed set-query generation is closed under
countable unions. -/
theorem corollary_A_3_countableUnion_query
    [Countable α] [Infinite α]
    (classes : ℕ → LanguageClass α)
    (hinfinite : ∀ i L, L ∈ classes i → L.Infinite)
    (hgenerate : ∀ i, SourceSetQueryGeneratable (classes i)) :
    SourceSetQueryGeneratable (⋃ i, classes i) := by
  apply countableInnerCover_implies_sourceSetQuery
  apply hasCountableInnerCover_iUnion
  intro i
  exact
    (theorem_3_4_sourceSetQuery_characterization
      (classes i) (hinfinite i)).mp (hgenerate i)

end GenLimit.FeedbackQueries
