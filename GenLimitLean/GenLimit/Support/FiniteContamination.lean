import GenLimit.Core.GenericGeneration

/-!
# Finite contamination

Paper-independent predicates for bounding a finite set difference and for
injective enumerations with finitely many values outside a target language.
-/

namespace GenLimit.Support

/-- `A` has at most `n` elements outside `B`.  The finite witness exposes the
exception set used by constructions that must enumerate those elements. -/
def MissingAtMost (A B : Set α) (n : ℕ) : Prop :=
  ∃ F : Finset α, (F : Set α) = A \ B ∧ F.card ≤ n

theorem missingAtMost_mono
    {A B : Set α} {i j : ℕ} (hij : i ≤ j)
    (h : MissingAtMost A B i) :
    MissingAtMost A B j := by
  obtain ⟨F, hF, hcard⟩ := h
  exact ⟨F, hF, hcard.trans hij⟩

theorem missingAtMost_zero_iff_subset
    (A B : Set α) :
    MissingAtMost A B 0 ↔ A ⊆ B := by
  constructor
  · rintro ⟨F, hF, hcard⟩ x hxA
    have hFempty : F = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    by_contra hxB
    have hxF : x ∈ (F : Set α) := by
      rw [hF]
      exact ⟨hxA, hxB⟩
    simp [hFempty] at hxF
  · intro hAB
    refine ⟨∅, ?_, by simp⟩
    simpa using (Set.diff_eq_empty.mpr hAB).symm

/-- An injective enumeration that covers `L` and contains at most `n`
distinct values outside `L`. -/
def EnumerationWithNoiseAtMost
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) : Prop :=
  Function.Injective stream ∧
    L ⊆ Set.range stream ∧
    MissingAtMost (Set.range stream) L n

theorem enumerationWithNoiseAtMost_mono
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {i j : ℕ}
    (hij : i ≤ j) (h : EnumerationWithNoiseAtMost stream L i) :
    EnumerationWithNoiseAtMost stream L j :=
  ⟨h.1, h.2.1, missingAtMost_mono hij h.2.2⟩

end GenLimit.Support
