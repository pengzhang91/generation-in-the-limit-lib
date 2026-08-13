import GenLimit.Paper02_LearningTheory.Common.EnumerationProgress
import GenLimit.Support.FiniteCandidateRace

/-!
# A finite race between infinite candidate sets

Compatibility wrappers for the paper-independent finite candidate race in
`GenLimit.Support`.
-/

namespace GenLimit.LiRamanTewari.Common

noncomputable def componentProgress [Countable α]
    (C : Set α) (current : Finset α) : ℕ :=
  GenLimit.Support.componentProgress C current

theorem componentProgress_of_infinite [Countable α]
    (C : Set α) (current : Finset α) (hC : C.Infinite) :
    componentProgress C current = progress C hC current := by
  exact GenLimit.Support.componentProgress_of_infinite C current hC

noncomputable def componentOutput [Nonempty α] [Countable α]
    (C : Set α) (current : Finset α) : α :=
  GenLimit.Support.componentOutput C current

theorem componentOutput_of_infinite [Nonempty α] [Countable α]
    (C : Set α) (current : Finset α) (hC : C.Infinite) :
    componentOutput C current =
      infiniteEnumeration C hC (progress C hC current) := by
  exact GenLimit.Support.componentOutput_of_infinite C current hC

/-- The maximum-progress index in a supplied finite active set. -/
noncomputable def winningIndex [Countable α]
    (active : Finset ι) (candidate : ι → Set α)
    (current : Finset α) : Option ι :=
  GenLimit.Support.winningIndex active candidate current

theorem winningIndex_spec [Countable α]
    (active : Finset ι) (candidate : ι → Set α)
    (current : Finset α) (hactive : active.Nonempty) :
    ∃ selected,
      winningIndex active candidate current = some selected ∧
      selected ∈ active ∧
      ∀ i, i ∈ active →
        componentProgress (candidate i) current ≤
          componentProgress (candidate selected) current := by
  exact GenLimit.Support.winningIndex_spec active candidate current hactive

end GenLimit.LiRamanTewari.Common
