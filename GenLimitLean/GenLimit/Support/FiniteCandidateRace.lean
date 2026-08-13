import GenLimit.Support.EnumerationProgress
import Mathlib.Data.Finset.Max

/-!
# A finite race between infinite candidate sets

Given finitely many active candidate sets, select one whose fixed enumeration
has made maximal progress through the current finite sample.
-/

namespace GenLimit.Support

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

/-- An index of maximum score in a supplied finite active set. -/
noncomputable def winningIndexBy
    (active : Finset ι) (score : ι → ℕ) : Option ι := by
  classical
  if hactive : active.Nonempty then
    exact some (Classical.choose (Finset.exists_max_image active
      score hactive))
  else exact none

theorem winningIndexBy_spec
    (active : Finset ι) (score : ι → ℕ) (hactive : active.Nonempty) :
    ∃ selected,
      winningIndexBy active score = some selected ∧
      selected ∈ active ∧
      ∀ i, i ∈ active → score i ≤ score selected := by
  classical
  let chosen := Classical.choose
    (Finset.exists_max_image active score hactive)
  have hchosen := Classical.choose_spec
    (Finset.exists_max_image active score hactive)
  refine ⟨chosen, ?_, hchosen.1, ?_⟩
  · simp [winningIndexBy, hactive, chosen]
  · intro i hi
    exact hchosen.2 i hi

/-- The maximum-progress index in a supplied finite active set. -/
noncomputable def winningIndex [Countable α]
    (active : Finset ι) (candidate : ι → Set α)
    (current : Finset α) : Option ι :=
  winningIndexBy active (fun i ↦ componentProgress (candidate i) current)

theorem winningIndex_spec [Countable α]
    (active : Finset ι) (candidate : ι → Set α)
    (current : Finset α) (hactive : active.Nonempty) :
    ∃ selected,
      winningIndex active candidate current = some selected ∧
      selected ∈ active ∧
      ∀ i, i ∈ active →
        componentProgress (candidate i) current ≤
          componentProgress (candidate selected) current :=
  winningIndexBy_spec active
    (fun i ↦ componentProgress (candidate i) current) hactive

end GenLimit.Support
