import Mathlib.Data.List.OfFn

/-!
# Deterministic adaptive membership-query dialogues

This module factors the paper-independent operational kernel shared by the
finite adaptive membership-query lower bounds in Papers 04 and 22.  In one
round, a deterministic algorithm sees the completed earlier rounds, the
current positive input, and the answered queries accumulated so far.  It
either asks another query or returns an output.

The definitions are deliberately agnostic about what a query means and which
answers are correct.  A paper instantiates `answerCorrect` with its own oracle
semantics.  A completed round contains a finite valid trace followed by an
output.  Because `Algorithm` is a total Lean function, failure to complete a
round here represents an unbounded sequence of queries, not silent divergence
while computing the next action; modeling the latter requires a partial or
small-step extension.
-/

namespace GenLimit.Support.AdaptiveMembershipDialogue

/-- A query paired with its Boolean oracle answer. -/
abbrev AnsweredQuery (Query : Type*) := Query × Bool

/-- A dialogue step either asks another query or completes the round. -/
abbrev Action (Query Output : Type*) := Sum Query Output

/-- A completed round stores its positive input, finite answered-query trace,
and output. -/
abbrev Round (Input Query Output : Type*) :=
  Input × (List (AnsweredQuery Query) × Output)

/-- A deterministic adaptive-query algorithm.

The algorithm sees all completed earlier rounds, the current positive input,
and the answered queries in the current round. -/
abbrev Algorithm (Input Query Output : Type*) :=
  (List (Round Input Query Output) ×
      (Input × List (AnsweredQuery Query))) →
    Action Query Output

/-- A finite trace follows the algorithm's adaptive query choices and every
recorded answer satisfies the supplied oracle semantics. -/
def QueryTraceValid
    (A : Algorithm Input Query Output)
    (answerCorrect : AnsweredQuery Query → Prop)
    (history : List (Round Input Query Output)) (input : Input)
    (trace : List (AnsweredQuery Query)) : Prop :=
  ∀ (k : ℕ) (hk : k < trace.length),
    let qa := trace.get ⟨k, hk⟩
    A (history, input, trace.take k) = Sum.inl qa.1 ∧
      answerCorrect qa

/-- A completed round consists of a valid finite query trace followed by the
recorded output. -/
def RoundValid
    (A : Algorithm Input Query Output)
    (answerCorrect : AnsweredQuery Query → Prop)
    (history : List (Round Input Query Output)) (input : Input)
    (round : Round Input Query Output) : Prop :=
  round.1 = input ∧
    QueryTraceValid A answerCorrect history input round.2.1 ∧
    A (history, input, round.2.1) = Sum.inr round.2.2

/-- A chronological list of completed rounds is the deterministic execution
on the corresponding positive-input list. -/
def ExecutionValid
    (A : Algorithm Input Query Output)
    (answerCorrect : AnsweredQuery Query → Prop)
    (inputs : List Input) (rounds : List (Round Input Query Output)) : Prop :=
  rounds.length = inputs.length ∧
    ∀ (k : ℕ) (hki : k < inputs.length) (hkr : k < rounds.length),
      RoundValid A answerCorrect (rounds.take k)
        (inputs.get ⟨k, hki⟩) (rounds.get ⟨k, hkr⟩)

/-- The first `n` positive inputs, in chronological order. -/
def inputPrefix (stream : ℕ → Input) (n : ℕ) : List Input :=
  List.ofFn (fun i : Fin n => stream i)

/-- At zero-based round `t`, after seeing `t + 1` positive inputs, the
algorithm terminates after finitely many queries and returns `output`. -/
def ExecutionOutputsAt
    (A : Algorithm Input Query Output)
    (answerCorrect : AnsweredQuery Query → Prop)
    (stream : ℕ → Input) (t : ℕ) (output : Output) : Prop :=
  ∃ rounds : List (Round Input Query Output),
    ExecutionValid A answerCorrect (inputPrefix stream (t + 1)) rounds ∧
      ∃ ht : t < rounds.length,
        (rounds.get ⟨t, ht⟩).2.2 = output

end GenLimit.Support.AdaptiveMembershipDialogue
