import GenLimit.Paper00A_PositiveDataInference.Effective.Definitions
import GenLimit.Support.Locking

/-!
# Syntactic stabilization for effective Angluin learners

The paper-facing predicate remains here, while its diagonal existence proof
delegates to the paper-independent locking-sequence theorem.
-/

namespace GenLimit.Angluin

open GenLimit.Generic

/-- A list learner makes the same *index* conjecture after every
target-consistent finite continuation. -/
def SyntacticallyStabilizing
    (M : EffectiveIdentifier) (L : Set ℕ) (history : List ℕ) : Prop :=
  ListWithin history L ∧
    ∀ extension, ListWithin extension L →
      M (history ++ extension) = M history

theorem exists_syntacticallyStabilizing
    {M : EffectiveIdentifier} {L : Set ℕ} (hL : L.Nonempty)
    (hM : ∀ stream : ℕ → ℕ, GenLimit.Presents stream L →
      ∃ guess T, ∀ t, T ≤ t →
        M (GenLimit.textPrefix stream t) = guess) :
    ∃ history, SyntacticallyStabilizing M L history := by
  let base := presentationOfNonempty L hL
  have hbase : GenLimit.Presents base L :=
    presentationOfNonempty_presents L hL
  obtain ⟨history, guess, hlock⟩ :=
    exists_lockingSequence_of_converges_with_base hbase (by
      intro stream hstream
      obtain ⟨j, T, hT⟩ := hM stream hstream
      exact ⟨j, T, hT⟩)
  refine ⟨history, hlock.1, ?_⟩
  intro extension hextension
  have hhistory : M history = guess := by
    simpa using hlock.2 [] (by simp [ListWithin])
  exact (hlock.2 extension hextension).trans hhistory.symm

end GenLimit.Angluin
