import GenLimit.Core.GenericGeneration
import GenLimit.Core.Text

/-!
# Literal breadth and stability definitions

This module records the set-valued definitions in Kalavasis--Mehrotra--
Velegkas, *On Characterizations for Language Generation: Interplay of
Hallucinations, Breadth, and Stability*, arXiv:2412.18530v2.

The distinction between `K \ S` and `K` is intentional.  Definition 3.1 in
the pinned source requires the former.  Some later arguments switch to the
latter convention.  Keeping both predicates explicit is essential once
stability is imposed.
-/

namespace GenLimit.BreadthCharacterizations

open GenLimit.Generic

/-- The paper's set-valued generator: an ordered finite history is mapped to
a possibly infinite support.  The round is the history length. -/
abbrev SupportAlgorithm (α : Type*) :=
  List α → Set α

/-- Run a support-valued generator on the prefix strictly before time `t`. -/
def supportAt
    (G : SupportAlgorithm α) (stream : Generic.Stream α) (t : ℕ) : Set α :=
  G (GenLimit.textPrefix stream t)

/-- The finite set of observations in a finite history, coerced to a set. -/
noncomputable def historySet (history : List α) : Set α := by
  classical
  exact ↑history.toFinset

/-- Definition 2.1 at one stage: all generated strings are unseen target
strings. -/
def GeneratesInLimitCorrectAt
    (G : SupportAlgorithm α) (K : Generic.Language α)
    (stream : Generic.Stream α) (t : ℕ) : Prop :=
  supportAt G stream t ⊆ K \ (↑(Generic.sample stream t) : Set α)

/-- Definition 2.1 for an indexed collection. -/
def IsLimitGenerator
    (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Generic.Stream α, Generic.Presents stream (F z) →
    ∃ T, ∀ t, T ≤ t → GeneratesInLimitCorrectAt G (F z) stream t

/-- Literal Definition 3.1 at one stage: the support is exactly the unseen
part of the target. -/
def ExactBreadthCorrectAt
    (G : SupportAlgorithm α) (K : Generic.Language α)
    (stream : Generic.Stream α) (t : ℕ) : Prop :=
  supportAt G stream t = K \ (↑(Generic.sample stream t) : Set α)

/-- Literal generation with exact breadth in the limit. -/
def IsExactBreadthGenerator
    (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Generic.Stream α, Generic.Presents stream (F z) →
    ∃ T, ∀ t, T ≤ t → ExactBreadthCorrectAt G (F z) stream t

/-- Existence of a literal exact-breadth generator. -/
def ExactBreadthGeneratable (F : Generic.LanguageFamily α) : Prop :=
  ∃ G : SupportAlgorithm α, IsExactBreadthGenerator G F

/-- Definition 3.2 at one stage.  Unlike Definition 3.1, the printed
definition does not require removal of the observed sample. -/
def ApproximateBreadthCorrectAt
    (G : SupportAlgorithm α) (K : Generic.Language α)
    (stream : Generic.Stream α) (t : ℕ) : Prop :=
  supportAt G stream t ⊆ K ∧
    (K \ supportAt G stream t).Finite

/-- Generation with approximate breadth in the limit. -/
def IsApproximateBreadthGenerator
    (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Generic.Stream α, Generic.Presents stream (F z) →
    ∃ T, ∀ t, T ≤ t → ApproximateBreadthCorrectAt G (F z) stream t

/-- Existence of an approximate-breadth generator. -/
def ApproximateBreadthGeneratable (F : Generic.LanguageFamily α) : Prop :=
  ∃ G : SupportAlgorithm α, IsApproximateBreadthGenerator G F

/-- The alternate whole-target convention used in the source's stability
discussion.  It is equivalent to exact breadth only before stability is
added. -/
def WholeTargetCorrectAt
    (G : SupportAlgorithm α) (K : Generic.Language α)
    (stream : Generic.Stream α) (t : ℕ) : Prop :=
  supportAt G stream t = K

/-- Eventual whole-target support on every presentation. -/
def IsWholeTargetGenerator
    (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Generic.Stream α, Generic.Presents stream (F z) →
    ∃ T, ∀ t, T ≤ t → WholeTargetCorrectAt G (F z) stream t

def WholeTargetGeneratable (F : Generic.LanguageFamily α) : Prop :=
  ∃ G : SupportAlgorithm α, IsWholeTargetGenerator G F

/-- Definition 3.14: the raw support eventually becomes exactly constant. -/
def IsStableGenerator
    (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Generic.Stream α, Generic.Presents stream (F z) →
    ∃ T, ∀ n n', T ≤ n → T ≤ n' →
      supportAt G stream n = supportAt G stream n'

/-- Definition 8.3 at one stage: infinitely many valid, unseen outputs. -/
def InfiniteCoverageCorrectAt
    (G : SupportAlgorithm α) (K : Generic.Language α)
    (stream : Generic.Stream α) (t : ℕ) : Prop :=
  supportAt G stream t ⊆ K ∧
    Disjoint (supportAt G stream t) (↑(Generic.sample stream t) : Set α) ∧
    (supportAt G stream t).Infinite

/-- Definition 8.3 for an indexed family. -/
def IsInfiniteCoverageGenerator
    (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Generic.Stream α, Generic.Presents stream (F z) →
    ∃ T, ∀ t, T ≤ t → InfiniteCoverageCorrectAt G (F z) stream t

/-- Remove the observed finite history from a support. -/
noncomputable def removeObserved
    (G : SupportAlgorithm α) : SupportAlgorithm α :=
  fun history => G history \ historySet history

/-- Add the observed finite history back to a support. -/
noncomputable def restoreObserved
    (G : SupportAlgorithm α) : SupportAlgorithm α :=
  fun history => G history ∪ historySet history

/-! ## Structural conditions -/

/-- Definition 3.7 at one index. -/
def IsWeakTellTale
    (F : Generic.LanguageFamily α) (i : ℕ) (T : Finset α) : Prop :=
  (↑T : Set α) ⊆ F i ∧
    ∀ j, (↑T : Set α) ⊆ F j → F j ⊂ F i →
      (F i \ F j).Finite

/-- Definition 3.7 for an indexed family. -/
def WeakAngluinCondition (F : Generic.LanguageFamily α) : Prop :=
  ∀ i, ∃ T : Finset α, IsWeakTellTale F i T

end GenLimit.BreadthCharacterizations
