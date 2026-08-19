import GenLimit.Core.GenericGeneration

/-!
# Noise, Loss, and Feedback: projection

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Definitions 2.12--2.13.

The paper works over a countably infinite universe.  Projection itself is
purely set-theoretic, so the definitions and elementary correspondence lemmas
below do not need countability.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-- Definition 2.12: projection of a language onto a smaller universe. -/
def languageProjection (L U' : Set α) : Set α :=
  L ∩ U'

/-- Definition 2.13: project every member of a class, then discard finite
projections. -/
def classProjection
    (C : LanguageClass α) (U' : Set α) : LanguageClass α :=
  {L' | ∃ L, L ∈ C ∧ L' = languageProjection L U' ∧ L'.Infinite}

theorem mem_classProjection_iff
    {C : LanguageClass α} {U' L' : Set α} :
    L' ∈ classProjection C U' ↔
      ∃ L, L ∈ C ∧ L' = L ∩ U' ∧ L'.Infinite :=
  Iff.rfl

theorem languageProjection_subset_universe
    (L U' : Set α) :
    languageProjection L U' ⊆ U' :=
  Set.inter_subset_right

theorem languageProjection_idempotent
    (L U' : Set α) :
    languageProjection (languageProjection L U') U' =
      languageProjection L U' := by
  simp [languageProjection, Set.inter_assoc]

theorem classProjection_languages_infinite
    {C : LanguageClass α} {U' L' : Set α}
    (hL' : L' ∈ classProjection C U') :
    L'.Infinite := by
  obtain ⟨_L, _hLC, _heq, hInfinite⟩ := hL'
  exact hInfinite

theorem classProjection_languages_subset
    {C : LanguageClass α} {U' L' : Set α}
    (hL' : L' ∈ classProjection C U') :
    L' ⊆ U' := by
  obtain ⟨L, _hLC, rfl, _hinfinite⟩ := hL'
  exact Set.inter_subset_right

end GenLimit.NoiseLossFeedback
