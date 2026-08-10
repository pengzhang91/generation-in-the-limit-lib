import GenLimit.Paper28_ContrastiveGeneration.DisjointHierarchy
import Mathlib.Data.Set.Card

/-!
# Corrupted contrastive and text presentations

This file formalizes Definitions 6.1 and 6.4 and Theorem 6.5 of
Li--Han--Jiang--Gao,
*Contrastive Identification and Generation in the Limit*
(arXiv:2605.06211v1).

Corruption budgets count occurrences (stream indices), not merely distinct
bad values or bad edges.  Positive-side coverage remains exact, as specified
in the source.
-/

namespace GenLimit
namespace ContrastiveGeneration

/-- Definition 6.1: at most `k` text occurrences lie outside the target,
while every target point is still covered. -/
def IsKCorruptedTextPresentation
    (k : ℕ) (stream : Generic.Stream α) (h : Set α) : Prop :=
  {n : ℕ | stream n ∉ h}.Finite ∧
    {n : ℕ | stream n ∉ h}.ncard ≤ k ∧
    h ⊆ Set.range stream

/-- Definition 6.1: at most `k` pair occurrences violate XOR, while every
positive target point remains incident to some observed pair. -/
def IsKCorruptedContrastivePresentation
    (k : ℕ) (stream : ℕ → Edge α) (h : Set α) : Prop :=
  {n : ℕ | ¬Crosses h (stream n)}.Finite ∧
    {n : ℕ | ¬Crosses h (stream n)}.ncard ≤ k ∧
    h ⊆ {x | ∃ n, Incident x (stream n)}

/-- A semantic text identifier succeeds on one `k`-corrupted presentation.
The stable index may differ from the given target index but must denote the
same support. -/
def KTextIdentifiesFrom
    (k : ℕ) (M : GenLimit.Angluin.SemanticIdentifier α)
    (F : Generic.LanguageFamily α) (z : ℕ)
    (stream : Generic.Stream α) : Prop :=
  IsKCorruptedTextPresentation k stream (F z) →
    ∃ j, F j = F z ∧
      GenLimit.StabilizesTo (fun t => M (GenLimit.textPrefix stream t)) j

/-- Membership in `k-TxtId` at the semantic level. -/
def KTextIdentifiable
    (k : ℕ) (F : Generic.LanguageFamily α) : Prop :=
  ∃ M : GenLimit.Angluin.SemanticIdentifier α,
    ∀ z stream, KTextIdentifiesFrom k M F z stream

/-- A semantic contrastive identifier succeeds on one `k`-corrupted
presentation. -/
def KContrastivelyIdentifiesFrom
    (k : ℕ) (I : ContrastiveIdentifier α)
    (F : Generic.LanguageFamily α) (z : ℕ)
    (stream : ℕ → Edge α) : Prop :=
  IsKCorruptedContrastivePresentation k stream (F z) →
    ContrastivelyIdentifiesFrom I F z stream

/-- Membership in `k-CtrId` at the semantic level. -/
def KContrastivelyIdentifiable
    (k : ℕ) (F : Generic.LanguageFamily α) : Prop :=
  ∃ I : ContrastiveIdentifier α,
    ∀ z stream, KContrastivelyIdentifiesFrom k I F z stream

/-- `Fin-CtrId`: one budget-independent identifier succeeds for every finite
corruption budget. -/
def FinitelyCorruptionContrastivelyIdentifiable
    (F : Generic.LanguageFamily α) : Prop :=
  ∃ I : ContrastiveIdentifier α,
    ∀ k z stream, KContrastivelyIdentifiesFrom k I F z stream

/-- Definition 6.4: support of the co-singleton hypothesis centered at
`s`. -/
def coSingletonSupport (s : α) : Set α := {x | x ≠ s}

/-- The co-singleton class, indexed by its missing natural number. -/
def coSingletonFamily : Generic.LanguageFamily ℕ :=
  coSingletonSupport

theorem coSingletonSupport_ne
    {s t : α} (hst : s ≠ t) :
    coSingletonSupport s ≠ coSingletonSupport t := by
  intro heq
  have hs : s ∈ coSingletonSupport t := hst
  rw [← heq] at hs
  exact hs rfl

theorem identity_is_oneCorruptedText
    (s : ℕ) :
    IsKCorruptedTextPresentation 1 (fun n : ℕ => n)
      (coSingletonSupport s) := by
  have hbad :
      {n : ℕ | (fun m : ℕ => m) n ∉ coSingletonSupport s} =
        {s} := by
    ext n
    simp [coSingletonSupport]
  constructor
  · rw [hbad]
    exact Set.finite_singleton s
  constructor
  · rw [hbad]
    simp
  · intro x _hx
    exact ⟨x, rfl⟩

/-- Theorem 6.5: the co-singleton class is not identifiable from texts with
even one corrupted occurrence. -/
theorem theorem_6_5 :
    ¬KTextIdentifiable 1 coSingletonFamily := by
  rintro ⟨M, hM⟩
  let identity : Generic.Stream ℕ := fun n => n
  obtain ⟨j₀, hj₀, T₀, hT₀⟩ :=
    hM 0 identity (identity_is_oneCorruptedText 0)
  obtain ⟨j₁, hj₁, T₁, hT₁⟩ :=
    hM 1 identity (identity_is_oneCorruptedText 1)
  have hindices : j₀ = j₁ := by
    exact
      (hT₀ (max T₀ T₁) (Nat.le_max_left _ _)).symm.trans
        (hT₁ (max T₀ T₁) (Nat.le_max_right _ _))
  have hsupports :
      coSingletonSupport 0 = coSingletonSupport 1 := by
    calc
      coSingletonSupport 0 = coSingletonFamily j₀ := hj₀.symm
      _ = coSingletonFamily j₁ := congrArg coSingletonFamily hindices
      _ = coSingletonSupport 1 := hj₁
  exact coSingletonSupport_ne (by omega) hsupports

end ContrastiveGeneration
end GenLimit
