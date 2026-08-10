import GenLimit.Core.GenericGeneration
import GenLimit.Core.Identification

/-!
# Semantic definitions for positive-data identification and tell-tales

This file contains only the set-theoretic layer of Angluin's framework.  No
declaration here asserts that a learner, language family, or tell-tale choice
is computable.
-/

namespace GenLimit.Angluin

open GenLimit.Generic

/-- A possibly noncomputable positive-data identifier, specialized from the
paper-independent ordered-history learner in `GenLimit.Core.Identification`. -/
abbrev SemanticIdentifier (α : Type*) := GenLimit.Learner α ℕ

/-- Semantic identification of an indexed family from every positive
presentation of each member. Angluin also treats a nonempty finite guess sequence
as converging to its last guess; the total prefix learner used here normalizes that case
by repeating the last guess forever. -/
def SemanticallyIdentifies
    (M : SemanticIdentifier α) (C : Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Stream α, Generic.Presents stream (C z) →
    GenLimit.IdentifiesInLimit C M stream (C z)

/-- Existence of a possibly noncomputable positive-data identifier. -/
def SemanticallyInferrable (C : Generic.LanguageFamily α) : Prop :=
  ∃ M : SemanticIdentifier α, SemanticallyIdentifies M C

/-- The source assumes every member of the indexed family is nonempty, so that
it has a positive presentation with no pause symbol. -/
def AllNonempty (C : Generic.LanguageFamily α) : Prop :=
  ∀ i, (C i).Nonempty

/-- Angluin's finite tell-tale condition for index `i`. -/
def IsTellTale
    (C : Generic.LanguageFamily α) (i : ℕ) (T : Finset α) : Prop :=
  (↑T : Set α) ⊆ C i ∧
    ∀ j, (↑T : Set α) ⊆ C j → C j ⊆ C i → C i ⊆ C j

theorem IsTellTale.eq_of_between
    {C : Generic.LanguageFamily α} {i j : ℕ} {T : Finset α}
    (hT : IsTellTale C i T)
    (hTj : (↑T : Set α) ⊆ C j) (hji : C j ⊆ C i) :
    C j = C i := by
  exact Set.Subset.antisymm hji (hT.2 j hTj hji)

/-- Condition 2: a finite tell-tale exists for every indexed language. -/
def ConditionTwo (C : Generic.LanguageFamily α) : Prop :=
  ∀ i, ∃ T : Finset α, IsTellTale C i T

/-- The finite-stage semantic information used by the least-index learner. -/
def IsTellTaleApproximation
    (C : Generic.LanguageFamily α) (A : ℕ → ℕ → Finset α) : Prop :=
  (∀ i n m, n ≤ m → A i n ⊆ A i m) ∧
    ∀ i, ∃ T : Finset α, IsTellTale C i T ∧
      ∃ N, ∀ n, N ≤ n → A i n = T

theorem IsTellTaleApproximation.conditionTwo
    {C : Generic.LanguageFamily α} {A : ℕ → ℕ → Finset α}
    (hA : IsTellTaleApproximation C A) : ConditionTwo C := by
  intro i
  obtain ⟨T, hT, -⟩ := hA.2 i
  exact ⟨T, hT⟩

end GenLimit.Angluin
