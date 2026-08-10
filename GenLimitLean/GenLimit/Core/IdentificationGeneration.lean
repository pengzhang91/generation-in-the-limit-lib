import GenLimit.Core.ClassGeneration
import GenLimit.Core.Identification

/-!
# Identification implies generation

Paper-independent semantic facts turning an ordered-history index learner for
an enumerated family of infinite languages into a fresh-example generator.
-/

namespace GenLimit.Generic

/-- Choose a fresh point from the language named by the learner's current
index guess. -/
noncomputable def freshFromIndexGuess
    (F : LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite)
    (M : GenLimit.Learner α ℕ) : Generator α := by
  classical
  exact fun t history =>
    Classical.choose
      ((hInfinite (M (List.ofFn history))).exists_notMem_finset
        (sequenceSample history))

theorem freshFromIndexGuess_spec
    (F : LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite)
    (M : GenLimit.Learner α ℕ)
    {t : ℕ} (history : Fin t → α) :
    freshFromIndexGuess F hInfinite M t history ∈
        F (M (List.ofFn history)) ∧
      freshFromIndexGuess F hInfinite M t history ∉
        sequenceSample history := by
  exact
    Classical.choose_spec
      ((hInfinite (M (List.ofFn history))).exists_notMem_finset
        (sequenceSample history))

/-- A learner that eventually stabilizes to an index denoting each presented
target induces generation in the limit for the extensional range of the
indexed family. No computability assumption is imposed. -/
theorem stabilizingIndexIdentifier_implies_generatableInLimit
    (F : LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite)
    (M : GenLimit.Learner α ℕ)
    (hM : ∀ z stream, Presents stream (F z) →
      GenLimit.IdentifiesInLimit F M stream (F z)) :
    GeneratableInLimit (Set.range F) := by
  refine ⟨freshFromIndexGuess F hInfinite M, ?_⟩
  intro L hL stream hP
  obtain ⟨z, rfl⟩ := hL
  obtain ⟨j, hj, T, hT⟩ := hM z stream hP
  refine ⟨T, ?_⟩
  intro t ht
  have hguess : M (List.ofFn (fun i : Fin t => stream i)) = j := by
    rw [← GenLimit.textPrefix_eq_ofFn]
    exact hT t ht
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
