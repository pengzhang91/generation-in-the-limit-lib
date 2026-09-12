import GenLimit.Paper22_LanguageGenerationWithReplay.ProperSeparation
import GenLimit.Core.Basic
import GenLimit.Support.AdaptiveMembershipDialogue
import Mathlib.Computability.Partrec

/-!
# Replay paper Theorem 7.1: exact machine statement and diagonal reduction

Source: Giorgio Racca, Michal Valko, and Amartya Sanyal,
*Language Generation with Replay: A Learning-Theoretic View of Model
Collapse*, arXiv:2603.11784v2, Theorem 7.1, Algorithm 3, and Lemma 7.2.

Theorem 7.1 is a computational lower bound in the ordinary (non-replay)
proper-generation model.  A generator may adaptively ask membership questions
`j ∈ hᵢ` before returning the index of its next proper hypothesis.  The
prefix-function generators used elsewhere in `GenLimit.Replay` do not expose
that operational interface, so this file instantiates the shared deterministic
dialogue kernel from `GenLimit.Support.AdaptiveMembershipDialogue`.

`Theorem71Statement` is the exact universal impossibility proposition over
uniformly recursive countable UUS families.  It is intentionally a
proposition, not a proved theorem.  The checked theorem
`theorem_7_1_of_universal_algorithm3` reduces it to the construction obligation
under the contradiction hypothesis that the tested algorithm is universal.

The pinned proof text has a termination gap in Lemma 7.2: its totality
argument treats a round that eventually outputs after finitely many queries
and a round that asks infinitely many queries, but not a round that asks
finitely many queries and then silently diverges.  The historical
`Algorithm3ConstructionStatement` asks for a certificate for
every computable machine, including machines that never finish a round, and is
therefore stronger than the source proof can justify.  It is retained for
compatibility.  A proof of `Algorithm3UniversalConstructionStatement` must
either use a total small-step machine model or add a clock/dovetailing repair.
This file does not assume that missing step.
-/

namespace GenLimit
namespace Replay

open GenLimit.Generic

/-! ## Deterministic adaptive proper membership-query machines -/

/-- A membership query names a family index and a word. -/
abbrev ProperMembershipQuery := ℕ × ℕ

/-- A membership query paired with the Boolean oracle answer. -/
abbrev AnsweredProperMembershipQuery :=
  Support.AdaptiveMembershipDialogue.AnsweredQuery ProperMembershipQuery

/-- A machine either asks another membership query or outputs a family
index. -/
abbrev ProperMembershipAction :=
  Support.AdaptiveMembershipDialogue.Action ProperMembershipQuery ℕ

/-- A completed round records its positive input, finite answered-query
trace, and output index. -/
abbrev ProperMembershipRound :=
  Support.AdaptiveMembershipDialogue.Round ℕ ProperMembershipQuery ℕ

/-- A deterministic adaptive membership-query machine for proper generation.

The machine sees all completed earlier rounds, the current positive input,
and the answered queries in the current round. -/
abbrev ProperMembershipAlgorithm :=
  Support.AdaptiveMembershipDialogue.Algorithm ℕ ProperMembershipQuery ℕ

/-- Correctness of one family-membership oracle answer. -/
def ProperMembershipAnswerCorrect
    (family : LanguageFamily)
    (qa : AnsweredProperMembershipQuery) : Prop :=
  qa.2 = true ↔ qa.1.2 ∈ family qa.1.1

/-- A finite current-round trace follows the machine's adaptive choices and
contains the correct membership answers. -/
def ProperMembershipQueryTraceValid
    (A : ProperMembershipAlgorithm) (family : LanguageFamily)
    (history : List ProperMembershipRound) (input : ℕ)
    (trace : List AnsweredProperMembershipQuery) : Prop :=
  Support.AdaptiveMembershipDialogue.QueryTraceValid A
    (ProperMembershipAnswerCorrect family) history input trace

/-- A completed round consists of a valid finite query trace followed by the
recorded proper output index. -/
def ProperMembershipRoundValid
    (A : ProperMembershipAlgorithm) (family : LanguageFamily)
    (history : List ProperMembershipRound) (input : ℕ)
    (round : ProperMembershipRound) : Prop :=
  Support.AdaptiveMembershipDialogue.RoundValid A
    (ProperMembershipAnswerCorrect family) history input round

/-- A chronological list of completed rounds is the deterministic execution
on the corresponding positive-input list. -/
def ProperMembershipExecutionValid
    (A : ProperMembershipAlgorithm) (family : LanguageFamily)
    (inputs : List ℕ) (rounds : List ProperMembershipRound) : Prop :=
  Support.AdaptiveMembershipDialogue.ExecutionValid A
    (ProperMembershipAnswerCorrect family) inputs rounds

/-- The first `n` positive examples, in chronological order. -/
def properMembershipInputPrefix
    (stream : Generic.Stream ℕ) (n : ℕ) : List ℕ :=
  Support.AdaptiveMembershipDialogue.inputPrefix stream n

/-- At zero-based round `t`, after seeing `t + 1` positive examples, the
machine terminates after finitely many membership queries and outputs `i`. -/
def ProperMembershipExecutionOutputsAt
    (A : ProperMembershipAlgorithm) (family : LanguageFamily)
    (stream : Generic.Stream ℕ) (t i : ℕ) : Prop :=
  Support.AdaptiveMembershipDialogue.ExecutionOutputsAt A
    (ProperMembershipAnswerCorrect family) stream t i

/-! ## Exact success and universality predicates -/

/-- The ordinary proper-generation-in-the-limit guarantee implemented using
only adaptive membership queries.

Termination is required at every round of every exact presentation.  After a
presentation-dependent finite time, every possible recorded output language
is contained in the target language. -/
def ProperlyGeneratesInLimitUsingMembership
    (A : ProperMembershipAlgorithm) (family : LanguageFamily) : Prop :=
  ∀ target : ℕ, ∀ stream : Generic.Stream ℕ,
    Generic.Presents stream (family target) →
      (∀ t : ℕ, ∃ i : ℕ,
        ProperMembershipExecutionOutputsAt A family stream t i) ∧
      ∃ T : ℕ, ∀ t : ℕ, T ≤ t → ∀ i : ℕ,
        ProperMembershipExecutionOutputsAt A family stream t i →
          family i ⊆ family target

/-- The source's effective standing assumptions: one uniformly computable
membership oracle for the indexed family, and an infinite support at every
index (UUS). -/
def IsRecursiveUUSFamily (family : LanguageFamily) : Prop :=
  ∃ oracle : MembershipOracle family,
    Computable₂ oracle.query ∧
      ∀ i : ℕ, (family i).Infinite

/-- A single computable deterministic machine succeeds, using only
membership answers, on every countably indexed recursive UUS family. -/
def UniversalProperMembershipGenerator
    (A : ProperMembershipAlgorithm) : Prop :=
  Computable A ∧
    ∀ family : LanguageFamily,
      IsRecursiveUUSFamily family →
        ProperlyGeneratesInLimitUsingMembership A family

/-- Theorem 7.1 exactly as a proposition over the source's effective
countable-family interface.  No proof declaration is asserted here. -/
def Theorem71Statement : Prop :=
  ¬ ∃ A : ProperMembershipAlgorithm,
    UniversalProperMembershipGenerator A

/-! ## Algorithm 3 certificate and checked semantic reduction -/

/-- The semantic output of Algorithm 3 once its online recursive-family
construction has been justified.

The reference row `0` encodes the source's `h₁`.  The two alternatives are
the proof's diagonalization and final-trap cases. -/
structure Algorithm3Certificate (A : ProperMembershipAlgorithm) where
  family : LanguageFamily
  oracle : MembershipOracle family
  oracle_computable : Computable₂ oracle.query
  row_infinite : ∀ i : ℕ, (family i).Infinite
  stream : Generic.Stream ℕ
  output : ℕ → ℕ
  execution :
    ∀ t : ℕ,
      ProperMembershipExecutionOutputsAt A family stream t (output t)
  bad_case :
    (Generic.Presents stream (family 0) ∧
      ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧
        ¬family (output t) ⊆ family 0) ∨
    ∃ trap start : ℕ,
      Generic.Presents stream (family trap) ∧
      (∀ t : ℕ, start ≤ t → output t = 0) ∧
      ¬family 0 ⊆ family trap

/-- Every Algorithm 3 certificate supplies the recursive UUS family required
by the universal theorem statement. -/
theorem Algorithm3Certificate.isRecursiveUUSFamily
    {A : ProperMembershipAlgorithm}
    (certificate : Algorithm3Certificate A) :
    IsRecursiveUUSFamily certificate.family :=
  ⟨certificate.oracle, certificate.oracle_computable,
    certificate.row_infinite⟩

/-- The checked tail argument of the printed proof: either unbounded
diagonal mistakes defeat target row `0`, or eventual output of row `0`
overgeneralizes the final trap target. -/
theorem algorithm3Certificate_not_properlyGenerates
    {A : ProperMembershipAlgorithm}
    (certificate : Algorithm3Certificate A) :
    ¬ProperlyGeneratesInLimitUsingMembership A certificate.family := by
  intro hsuccess
  rcases certificate.bad_case with hdiagonal | htrap
  · obtain ⟨hpresents, hmistakes⟩ := hdiagonal
    obtain ⟨_, T, hcorrect⟩ :=
      hsuccess 0 certificate.stream hpresents
    obtain ⟨t, ht, hbad⟩ := hmistakes T
    exact hbad
      (hcorrect t ht (certificate.output t)
        (certificate.execution t))
  · obtain ⟨trap, start, hpresents, href, hproper⟩ := htrap
    obtain ⟨_, T, hcorrect⟩ :=
      hsuccess trap certificate.stream hpresents
    let t := max T start
    have htT : T ≤ t := le_max_left _ _
    have htStart : start ≤ t := le_max_right _ _
    have hout : certificate.output t = 0 := href t htStart
    have hsubset :
        certificate.family (certificate.output t) ⊆
          certificate.family trap :=
      hcorrect t htT (certificate.output t)
        (certificate.execution t)
    rw [hout] at hsubset
    exact hproper hsubset

/-- One Algorithm 3 certificate refutes universality of the corresponding
machine. -/
theorem algorithm3Certificate_refutes_universal
    {A : ProperMembershipAlgorithm}
    (certificate : Algorithm3Certificate A) :
    ¬UniversalProperMembershipGenerator A := by
  intro huniversal
  exact algorithm3Certificate_not_properlyGenerates certificate
    (huniversal.2 certificate.family
      certificate.isRecursiveUUSFamily)

/-- Historical over-strong construction obligation.  This quantifies over
computable machines that may ask queries forever and hence need not have the
completed executions stored in `Algorithm3Certificate`.  New source-facing
reductions should use `Algorithm3UniversalConstructionStatement`. -/
def Algorithm3ConstructionStatement : Prop :=
  ∀ A : ProperMembershipAlgorithm,
    Computable A → Nonempty (Algorithm3Certificate A)

/-- A computable machine that asks the same query forever and never emits a
proper hypothesis. -/
def queryForeverAlgorithm : ProperMembershipAlgorithm :=
  fun _ => Sum.inl (0, 0)

theorem queryForeverAlgorithm_computable :
    Computable queryForeverAlgorithm := by
  simpa [queryForeverAlgorithm] using
    (Computable.const (α :=
      List ProperMembershipRound ×
        (ℕ × List AnsweredProperMembershipQuery))
      (Sum.inl (0, 0) : ProperMembershipAction))

theorem queryForeverAlgorithm_never_outputs
    (family : LanguageFamily) (stream : Generic.Stream ℕ)
    (t i : ℕ) :
    ¬ProperMembershipExecutionOutputsAt
      queryForeverAlgorithm family stream t i := by
  rintro ⟨rounds, hexecution, ht, _hout⟩
  have hinput :
      t < (properMembershipInputPrefix stream (t + 1)).length := by
    simp [properMembershipInputPrefix,
      Support.AdaptiveMembershipDialogue.inputPrefix]
  have hround := hexecution.2 t hinput ht
  have haction := hround.2.2
  simp [queryForeverAlgorithm] at haction

/-- The historical construction obligation is inconsistent with the machine
interface: it demands a completed execution certificate even for a computable
machine that never outputs. -/
theorem algorithm3ConstructionStatement_is_false :
    ¬Algorithm3ConstructionStatement := by
  intro hconstruction
  obtain ⟨certificate⟩ :=
    hconstruction queryForeverAlgorithm queryForeverAlgorithm_computable
  exact queryForeverAlgorithm_never_outputs
    certificate.family certificate.stream 0 (certificate.output 0)
    (certificate.execution 0)

/-- The source-faithful contradiction-context construction obligation:
Algorithm 3 is run only for a machine assumed to be a universal proper
generator.  That assumption supplies the per-round termination and success
properties used by the diagonal construction. -/
def Algorithm3UniversalConstructionStatement : Prop :=
  ∀ A : ProperMembershipAlgorithm,
    UniversalProperMembershipGenerator A →
      Nonempty (Algorithm3Certificate A)

/-- Source-facing reduction for Theorem 7.1 with the correct same-witness
universality hypothesis. -/
theorem theorem_7_1_of_universal_algorithm3
    (hconstruction : Algorithm3UniversalConstructionStatement) :
    Theorem71Statement := by
  rintro ⟨A, huniversal⟩
  obtain ⟨certificate⟩ := hconstruction A huniversal
  exact algorithm3Certificate_refutes_universal certificate huniversal

/-- Compatibility reduction from the historical stronger obligation. -/
theorem theorem_7_1_of_algorithm3
    (hconstruction : Algorithm3ConstructionStatement) :
    Theorem71Statement := by
  rintro ⟨A, huniversal⟩
  obtain ⟨certificate⟩ := hconstruction A huniversal.1
  exact algorithm3Certificate_refutes_universal certificate huniversal

end Replay
end GenLimit
