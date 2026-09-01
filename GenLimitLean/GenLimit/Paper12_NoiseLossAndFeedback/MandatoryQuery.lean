import GenLimit.Paper12_NoiseLossAndFeedback.FiniteFeedback

/-!
# Noise, Loss, and Feedback: shared mandatory-query interaction

Paper12 uses the same deterministic interaction shape for generation with
unrestricted feedback and for identification with feedback.  At time `t`, a
machine sees observations through `t` and earlier Boolean membership answers,
issues one query, receives its truthful answer, and then emits an output.

`MandatoryQueryMachine α β` factors that paper-local kernel while allowing
the output type to vary: `β = α` for generation and `β = ℕ` for indexed
identification.  It deliberately remains under Paper12 rather than becoming a
Core interface; Paper04's feedback model exposes a richer adversarial history
and is not definitionally the same interaction.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

variable {α β : Type*}

/-- A deterministic machine that issues one membership query on every round
and emits an output after receiving the current Boolean answer. -/
structure MandatoryQueryMachine (α : Type*) (β : Type*) where
  query :
    (t : ℕ) →
      (Fin (t + 1) → α) →
      (Fin t → Bool) →
      α
  output :
    (t : ℕ) →
      (Fin (t + 1) → α) →
      (Fin (t + 1) → Bool) →
      β

/-- The truthful answer to the mandatory query at time `t`. -/
noncomputable def actualMandatoryQueryResponse
    (machine : MandatoryQueryMachine α β)
    (target : GenLimit.Generic.Language α)
    (stream : Stream α) (t : ℕ) : Bool :=
  membershipAnswer target
    (machine.query t
      (fun i => stream i)
      (fun i => actualMandatoryQueryResponse machine target stream i))
termination_by t
decreasing_by
  exact i.isLt

theorem actualMandatoryQueryResponse_eq
    (machine : MandatoryQueryMachine α β)
    (target : GenLimit.Generic.Language α)
    (stream : Stream α) (t : ℕ) :
    actualMandatoryQueryResponse machine target stream t =
      membershipAnswer target
        (machine.query t
          (fun i => stream i)
          (fun i =>
            actualMandatoryQueryResponse machine target stream i)) := by
  rw [actualMandatoryQueryResponse]

/-- The output after the mandatory query at time `t` has been answered. -/
noncomputable def actualMandatoryQueryOutput
    (machine : MandatoryQueryMachine α β)
    (target : GenLimit.Generic.Language α)
    (stream : Stream α) (t : ℕ) : β :=
  machine.output t
    (fun i => stream i)
    (fun i => actualMandatoryQueryResponse machine target stream i)

end GenLimit.NoiseLossFeedback
