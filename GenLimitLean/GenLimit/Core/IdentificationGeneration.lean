import GenLimit.Core.ClassGeneration

/-!
# Identification implies generation

Paper-independent semantic facts turning an index learner for an enumerated
family of infinite languages into a fresh-example generator. The learner is
represented directly on finite function histories, so this module does not
depend on any paper-specific identification interface.
-/

namespace GenLimit.Generic

/-- Choose a fresh point from the language named by the learner's current
index guess. -/
noncomputable def freshFromIndexGuess
    (F : LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite)
    (M : ∀ t : ℕ, (Fin t → α) → ℕ) : Generator α := by
  classical
  exact fun t history =>
    Classical.choose
      ((hInfinite (M t history)).exists_notMem_finset
        (sequenceSample history))

theorem freshFromIndexGuess_spec
    (F : LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite)
    (M : ∀ t : ℕ, (Fin t → α) → ℕ)
    {t : ℕ} (history : Fin t → α) :
    freshFromIndexGuess F hInfinite M t history ∈ F (M t history) ∧
      freshFromIndexGuess F hInfinite M t history ∉
        sequenceSample history := by
  exact
    Classical.choose_spec
      ((hInfinite (M t history)).exists_notMem_finset
        (sequenceSample history))

/-- A learner that eventually stabilizes to an index denoting each presented
target induces generation in the limit for the extensional range of the
indexed family. No computability assumption is imposed. -/
theorem stabilizingIndexIdentifier_implies_generatableInLimit
    (F : LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite)
    (M : ∀ t : ℕ, (Fin t → α) → ℕ)
    (hM : ∀ z stream, Presents stream (F z) →
      ∃ j, F j = F z ∧ ∃ T, ∀ t, T ≤ t →
        M t (fun i : Fin t => stream i) = j) :
    GeneratableInLimit (Set.range F) := by
  refine ⟨freshFromIndexGuess F hInfinite M, ?_⟩
  intro L hL stream hP
  obtain ⟨z, rfl⟩ := hL
  obtain ⟨j, hj, T, hT⟩ := hM z stream hP
  refine ⟨T, ?_⟩
  intro t ht
  have hguess : M t (fun i : Fin t => stream i) = j := hT t ht
  have hspec :=
    freshFromIndexGuess_spec F hInfinite M
      (fun i : Fin t => stream i)
  constructor
  · change
      freshFromIndexGuess F hInfinite M t
          (fun i : Fin t => stream i) ∈ F z
    rw [hguess, hj] at hspec
    exact hspec.1
  · change
      freshFromIndexGuess F hInfinite M t
          (fun i : Fin t => stream i) ∉ sample stream t
    simpa only [sequenceSample_prefix] using hspec.2

end GenLimit.Generic
