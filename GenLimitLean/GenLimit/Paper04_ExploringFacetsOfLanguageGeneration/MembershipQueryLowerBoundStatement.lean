import GenLimit.Core.Countable
import Mathlib.Computability.Partrec
import Mathlib.Data.List.OfFn

/-!
# Charikar--Pabbaraju Theorem 7: exact source statement and machine model

This file pins the formal statement of the membership-query lower bound in
Section 4 of Charikar--Pabbaraju, *Exploring Facets of Language Generation in
the Limit*, arXiv:2411.15364v2.

The existing `Generator` API is a plain function of the positive history; it
cannot express an algorithm that may issue an adaptively chosen finite number
of membership queries before producing one output, or may fail to terminate.
The dialogue model below records precisely that missing operational layer.
An algorithm sees all completed earlier rounds, the next positive input, and
the answered queries in the current round.  It either issues another query to
one of the two named languages or outputs a word.  A valid round contains a
finite query trace followed by an output.  Consequently, absence of a valid
execution represents the paper's possible infinite query loop.

`TheoremSevenStatement` is the literal computable, deterministic,
two-language non-uniform impossibility claim (with the countable string
universe encoded by `ℕ`).  Its adversarial infinite-stage proof is not asserted
in this file; recording it as a definition prevents a weaker one-query or
oracle-as-a-total-function theorem from being mistaken for Theorem 7.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-! ## Deterministic adaptive membership-query machines -/

/-- A query names one of the two collection languages and a word.  `false`
means `L₀`, and `true` means `L₁`. -/
abbrev TwoLanguageQuery := Bool × ℕ

/-- A query paired with the Boolean answer returned by the oracle. -/
abbrev AnsweredTwoLanguageQuery := TwoLanguageQuery × Bool

/-- Either issue another query or finish the current round with an output. -/
abbrev TwoLanguageAction := Sum TwoLanguageQuery ℕ

/-- One completed round: positive input, finite answered-query trace, output. -/
abbrev TwoLanguageRound := ℕ × (List AnsweredTwoLanguageQuery × ℕ)

/-- A deterministic machine.  The product encoding keeps the exact
computability predicate in Mathlib's `Primcodable` model. -/
abbrev TwoLanguageMembershipAlgorithm :=
  (List TwoLanguageRound × (ℕ × List AnsweredTwoLanguageQuery)) →
    TwoLanguageAction

def queriedLanguage
    (L₀ L₁ : Set ℕ) (q : TwoLanguageQuery) : Set ℕ :=
  if q.1 then L₁ else L₀

/-- Correctness of one recorded oracle answer. -/
def AnsweredQueryCorrect
    (L₀ L₁ : Set ℕ) (qa : AnsweredTwoLanguageQuery) : Prop :=
  qa.2 = true ↔ qa.1.2 ∈ queriedLanguage L₀ L₁ qa.1

/-- Every entry of a current-round query trace is exactly the next query
chosen by the deterministic machine from the preceding trace, and carries
the correct oracle answer. -/
def QueryTraceValid
    (A : TwoLanguageMembershipAlgorithm) (L₀ L₁ : Set ℕ)
    (history : List TwoLanguageRound) (input : ℕ)
    (trace : List AnsweredTwoLanguageQuery) : Prop :=
  ∀ (k : ℕ) (hk : k < trace.length),
    let qa := trace.get ⟨k, hk⟩
    A (history, input, trace.take k) = Sum.inl qa.1 ∧
      AnsweredQueryCorrect L₀ L₁ qa

/-- A completed round has a valid finite query dialogue and ends when the
machine emits the recorded output. -/
def RoundValid
    (A : TwoLanguageMembershipAlgorithm) (L₀ L₁ : Set ℕ)
    (history : List TwoLanguageRound) (input : ℕ)
    (round : TwoLanguageRound) : Prop :=
  round.1 = input ∧
    QueryTraceValid A L₀ L₁ history input round.2.1 ∧
    A (history, input, round.2.1) = Sum.inr round.2.2

/-- A finite list of rounds is the deterministic execution on the
corresponding finite positive input list. -/
def ExecutionValid
    (A : TwoLanguageMembershipAlgorithm) (L₀ L₁ : Set ℕ)
    (inputs : List ℕ) (rounds : List TwoLanguageRound) : Prop :=
  rounds.length = inputs.length ∧
    ∀ (k : ℕ) (hki : k < inputs.length) (hkr : k < rounds.length),
      RoundValid A L₀ L₁ (rounds.take k)
        (inputs.get ⟨k, hki⟩) (rounds.get ⟨k, hkr⟩)

/-- The first `n` positive inputs, in chronological order. -/
def membershipInputPrefix (stream : Generic.Stream ℕ) (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => stream i)

/-- `A` terminates after finitely many queries at zero-based round `t` and
emits `z`.  There are `t+1` positive inputs at that point. -/
def MembershipExecutionOutputsAt
    (A : TwoLanguageMembershipAlgorithm) (L₀ L₁ : Set ℕ)
    (stream : Generic.Stream ℕ) (t z : ℕ) : Prop :=
  ∃ rounds : List TwoLanguageRound,
    ExecutionValid A L₀ L₁ (membershipInputPrefix stream (t + 1)) rounds ∧
      ∃ ht : t < rounds.length, (rounds.get ⟨t, ht⟩).2.2 = z

def selectedTwoLanguage (L₀ L₁ : Set ℕ) (target : Bool) : Set ℕ :=
  if target then L₁ else L₀

def selectedThreshold (d₀ d₁ : ℕ) (target : Bool) : ℕ :=
  if target then d₁ else d₀

/-! ## The exact non-uniform guarantee and Theorem 7 statement -/

/-- The two target-dependent thresholds in the printed theorem, including
termination after finitely many queries at every round of every exact
presentation and correctness once the number of distinct inputs reaches the
corresponding threshold. -/
def NonuniformTwoLanguageMembershipGuarantee
    (A : TwoLanguageMembershipAlgorithm) (L₀ L₁ : Set ℕ) : Prop :=
  ∃ d₀ d₁ : ℕ,
    ∀ target : Bool, ∀ stream : Generic.Stream ℕ,
      Generic.Presents stream (selectedTwoLanguage L₀ L₁ target) →
      ∀ t : ℕ,
        (∃ z, MembershipExecutionOutputsAt A L₀ L₁ stream t z) ∧
        ∀ z, MembershipExecutionOutputsAt A L₀ L₁ stream t z →
          selectedThreshold d₀ d₁ target ≤
              (Generic.sample stream (t + 1)).card →
            z ∈ selectedTwoLanguage L₀ L₁ target \ ↑(Generic.sample stream (t + 1))

/-- A single computable membership-query machine would have to satisfy the
non-uniform guarantee simultaneously for every pair of infinite languages. -/
def UniversalTwoLanguageMembershipGenerator
    (A : TwoLanguageMembershipAlgorithm) : Prop :=
  Computable A ∧
    ∀ L₀ L₁ : Set ℕ, L₀.Infinite → L₁.Infinite →
      NonuniformTwoLanguageMembershipGuarantee A L₀ L₁

/-- Theorem 7 (`thm:membership-query-lb`) exactly as a proposition.  A proof
requires the paper's adaptive infinite-stage assignment diagonal. -/
def TheoremSevenStatement : Prop :=
  ¬ ∃ A : TwoLanguageMembershipAlgorithm,
    UniversalTwoLanguageMembershipGenerator A

end GenLimit.CharikarPabbaraju
