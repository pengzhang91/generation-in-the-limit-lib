import GenLimit.Core.Identification
import GenLimit.Paper26_IdentificationWithComputationalTrace.StackRadius
import GenLimit.Paper26_IdentificationWithComputationalTrace.FiniteError
import GenLimit.Paper26_IdentificationWithComputationalTrace.Diminishing

namespace GenLimit.ComputationalTrace.PDA
open Control

private def scope (cut : ℕ → ℕ) (S : Finset ℕ) :=
  let L := cut (rateIndex S)
  (L,poolSize device S.card (radius S L))

/-- The cutoff function is accessed only at a reciprocal integer rate. -/
def learner (cut : ℕ → ℕ) : List (Sample Memory) → Guess Observation Action :=
  scopedLearner device (fun e => 2*e.2.length) (scope cut)

theorem identifies_diminishing (cut : ℕ → ℕ) (P : Program ℕ) (s : ℕ → Sample Memory)
    (hs : Presentation device P.machine (DiminishingBound cut) s) :
    IdentifiesInLimit (fun H : Guess Observation Action => H.language device) (learner cut) s
      (language device P.machine) := by
  apply identifies_in_scope device _ _ P.machine s hs
  intro S ho
  let L := cut (rateIndex S)
  apply code_in_ball device P.machine S (radius S L) L
  intro n hn
  obtain ⟨ds,run,_⟩ := hs.traces n
  exact ⟨ds,run,time_bound hs S ho n (rateIndex S) hn run,cover_diminishing hs S ho hn run⟩

end GenLimit.ComputationalTrace.PDA
