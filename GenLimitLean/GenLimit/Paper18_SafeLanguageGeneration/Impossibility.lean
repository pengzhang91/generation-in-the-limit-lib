import GenLimit.Paper18_SafeLanguageGeneration.IdentificationReduction
import GenLimit.Paper28_ContrastiveGeneration.Hierarchy

/-!
# A corrected semantic/oracle form of Safe Generation Theorem 6.2

This module proves the existential impossibility asserted by Theorem 6.2 of
Anastasopoulos--Ateniese--Kornaropoulos without using the defective printed
`P*` diagonal.  The proof instead combines the already-checked safe
generation-to-identification reduction with an explicit non-identifiable
indexed family.
-/

namespace GenLimit.SafeGeneration

open GenLimit.Generic
open GenLimit.ContrastiveGeneration

/-- The explicit family used for the impossibility theorem: vertically pad
the punctured even-spine family. -/
def puncturedPaddedFamily : Generic.LanguageFamily (ℕ × ℕ) :=
  fun i => verticalPad (puncturedFamily i)

/-- Every language in the explicit family is infinite, as required by the
standing assumptions of the source. -/
theorem puncturedPaddedFamily_infinite (i : ℕ) :
    (puncturedPaddedFamily i).Infinite := by
  simpa [puncturedPaddedFamily] using
    verticalPad_infinite_of_nonempty (puncturedFamily_nonempty i)

/-- No semantic safe generator works for all target/harmful pairs and all
labeled presentations of the explicit family. -/
theorem puncturedPaddedFamily_no_safe_generator :
    ¬ ∃ G : SafeGenerator (ℕ × ℕ),
      SafelyGeneratesFamilies G
        puncturedPaddedFamily puncturedPaddedFamily := by
  rintro ⟨G, hG⟩
  apply punctured_not_textIdentifiable
  let positivePad : ℕ → Generic.Stream (ℕ × ℕ) :=
    fun i =>
      verticalPadPresentation
        (puncturedFamily i) (puncturedFamily_nonempty i)
  refine
    ⟨identificationFromSafeGenerator G puncturedFamily positivePad, ?_⟩
  apply theorem_5_1_prefix_compatible G puncturedFamily positivePad
  · intro i
    exact
      verticalPadPresentation_presents
        (puncturedFamily i) (puncturedFamily_nonempty i)
  · simpa [puncturedPaddedFamily] using hG

/-- Corrected semantic Theorem 6.2: there are two countable indexed families
of infinite languages for which no safe generator exists. -/
theorem corrected_theorem_6_2 :
    ∃ targets harmfuls : Generic.LanguageFamily (ℕ × ℕ),
      (∀ i, (targets i).Infinite) ∧
      (∀ j, (harmfuls j).Infinite) ∧
      ¬ ∃ G : SafeGenerator (ℕ × ℕ),
        SafelyGeneratesFamilies G targets harmfuls := by
  exact
    ⟨puncturedPaddedFamily, puncturedPaddedFamily,
      puncturedPaddedFamily_infinite,
      puncturedPaddedFamily_infinite,
      puncturedPaddedFamily_no_safe_generator⟩

/-! ## An extensional set-difference oracle interface -/

variable {α : Type*}

/-- An ideal oracle for differences between arbitrary sets in the example
universe, matching the source's unrestricted `O^SD(·,·)` primitive. -/
abbrev SetDifferenceOracle (α : Type*) :=
  Set α → Set α → Bool

/-- The oracle returns `true` exactly when its first input minus its second
input is empty.  Requiring correctness on all sets only strengthens the
oracle supplied to the learner. -/
def IsCorrectSetDifferenceOracle
    (O : SetDifferenceOracle α) : Prop :=
  ∀ X Y : Set α, O X Y = true ↔ X \ Y = ∅

/-- The exact semantic oracle.  No computability is asserted or needed:
Theorem 6.2 grants the learner this ideal primitive. -/
noncomputable def exactSetDifferenceOracle :
    SetDifferenceOracle α := by
  classical
  exact fun X Y => decide (X \ Y = ∅)

theorem exactSetDifferenceOracle_correct :
    IsCorrectSetDifferenceOracle
      (exactSetDifferenceOracle : SetDifferenceOracle α) := by
  classical
  intro X Y
  simp [exactSetDifferenceOracle]

/-- An oracle-augmented learner specializes to an ordinary semantic safe
generator once its oracle is supplied. -/
abbrev OracleSafeAlgorithm (α : Type*) :=
  SetDifferenceOracle α → SafeGenerator α

/-- Oracle-facing corrected Theorem 6.2.  It is stronger than necessary:
even an arbitrary (not necessarily computable) oracle-augmented algorithm
fails after specialization to every correct oracle. -/
theorem corrected_theorem_6_2_with_oracle :
    ∃ targets harmfuls : Generic.LanguageFamily (ℕ × ℕ),
      (∀ i, (targets i).Infinite) ∧
      (∀ j, (harmfuls j).Infinite) ∧
      ∀ O : SetDifferenceOracle (ℕ × ℕ),
        IsCorrectSetDifferenceOracle O →
        ∀ A : OracleSafeAlgorithm (ℕ × ℕ),
          ¬ SafelyGeneratesFamilies (A O) targets harmfuls := by
  refine
    ⟨puncturedPaddedFamily, puncturedPaddedFamily,
      puncturedPaddedFamily_infinite,
      puncturedPaddedFamily_infinite, ?_⟩
  intro O _hO A hSafe
  exact puncturedPaddedFamily_no_safe_generator ⟨A O, hSafe⟩

end GenLimit.SafeGeneration
