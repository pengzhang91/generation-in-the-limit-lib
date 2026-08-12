import GenLimit.Paper02_LearningTheory.Common.EnumerationProgress
import Mathlib.Data.Finset.Max

/-!
# A finite race between infinite candidate sets

This is the small shared selection step used in Theorem 3.10 and Appendix
C.2.  It chooses, among a supplied finite set of active indices, the candidate
whose enumeration has made the greatest progress through the observed sample.
-/

namespace GenLimit.LiRamanTewari.Common

noncomputable def componentProgress [Countable α]
    (C : Set α) (current : Finset α) : ℕ := by
  classical
  exact if hC : C.Infinite then progress C hC current else 0

theorem componentProgress_of_infinite [Countable α]
    (C : Set α) (current : Finset α) (hC : C.Infinite) :
    componentProgress C current = progress C hC current := by
  classical
  simp [componentProgress, hC]

noncomputable def componentOutput [Nonempty α] [Countable α]
    (C : Set α) (current : Finset α) : α := by
  classical
  exact if hC : C.Infinite then
    infiniteEnumeration C hC (progress C hC current)
  else Classical.choice inferInstance

theorem componentOutput_of_infinite [Nonempty α] [Countable α]
    (C : Set α) (current : Finset α) (hC : C.Infinite) :
    componentOutput C current =
      infiniteEnumeration C hC (progress C hC current) := by
  classical
  simp [componentOutput, hC]

/-- The maximum-progress index in a supplied finite active set. -/
noncomputable def winningIndex [Countable α]
    (active : Finset ι) (candidate : ι → Set α)
    (current : Finset α) : Option ι := by
  classical
  if hactive : active.Nonempty then
    exact some (Classical.choose (Finset.exists_max_image active
      (fun i ↦ componentProgress (candidate i) current) hactive))
  else exact none

theorem winningIndex_spec [Countable α]
    (active : Finset ι) (candidate : ι → Set α)
    (current : Finset α) (hactive : active.Nonempty) :
    ∃ selected,
      winningIndex active candidate current = some selected ∧
      selected ∈ active ∧
      ∀ i, i ∈ active →
        componentProgress (candidate i) current ≤
          componentProgress (candidate selected) current := by
  classical
  let score : ι → ℕ :=
    fun i ↦ componentProgress (candidate i) current
  let chosen := Classical.choose
    (Finset.exists_max_image active score hactive)
  have hchosen := Classical.choose_spec
    (Finset.exists_max_image active score hactive)
  refine ⟨chosen, ?_, hchosen.1, ?_⟩
  · simp [winningIndex, hactive, score, chosen]
  · intro i hi
    exact hchosen.2 i hi

end GenLimit.LiRamanTewari.Common
