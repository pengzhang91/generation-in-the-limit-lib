import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.MembershipQueryLowerBoundStatement

/-!
# Finite shadow executions for the membership-query diagonal

This file isolates the finite invariant needed by the adaptive diagonal in
Section 4 of Charikar--Pabbaraju, *Exploring Facets of Language Generation in
the Limit*, arXiv:2411.15364v2.

The adversary in the proof of Theorem 7 records only finitely many membership
answers before a terminating output.  Any two completed language pairs that
realize those finite assignments must therefore induce exactly the same
recorded execution.  In addition, two presentations with the same finite
positive prefix induce the same execution and the same observed sample.  The
last theorem applies the non-uniform guarantee to both target languages on
such a common prefix; this is the source-faithful endgame, rather than the
insufficient inference that correctness for one target alone puts an output
in the intersection.

This module deliberately stops at the finite-shadow layer.  The completed
infinite construction is in `MembershipQueryGlobalDiagonal`; it avoids the
printed proof's unsupported inference about infinitely many distinct query
words by invoking the contradictory universal termination guarantee on a
separated infinite completion at each finite phase.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-! ## Agreement on a finite adaptive transcript -/

/-- Two pairs of languages return the same answer to a particular query. -/
def LanguagePairAgreesAt
    (L₀ L₁ K₀ K₁ : Set ℕ) (q : TwoLanguageQuery) : Prop :=
  q.2 ∈ queriedLanguage L₀ L₁ q ↔
    q.2 ∈ queriedLanguage K₀ K₁ q

/-- Two language pairs agree on every query occurring in a trace. -/
def LanguagePairAgreesOnTrace
    (L₀ L₁ K₀ K₁ : Set ℕ)
    (trace : List AnsweredTwoLanguageQuery) : Prop :=
  ∀ qa ∈ trace, LanguagePairAgreesAt L₀ L₁ K₀ K₁ qa.1

/-- Two language pairs agree on all queries in a finite execution. -/
def LanguagePairAgreesOnExecution
    (L₀ L₁ K₀ K₁ : Set ℕ)
    (rounds : List TwoLanguageRound) : Prop :=
  ∀ round ∈ rounds,
    LanguagePairAgreesOnTrace L₀ L₁ K₀ K₁ round.2.1

theorem LanguagePairAgreesAt.symm
    {L₀ L₁ K₀ K₁ : Set ℕ} {q : TwoLanguageQuery}
    (h : LanguagePairAgreesAt L₀ L₁ K₀ K₁ q) :
    LanguagePairAgreesAt K₀ K₁ L₀ L₁ q :=
  Iff.symm h

theorem LanguagePairAgreesOnTrace.symm
    {L₀ L₁ K₀ K₁ : Set ℕ} {trace : List AnsweredTwoLanguageQuery}
    (h : LanguagePairAgreesOnTrace L₀ L₁ K₀ K₁ trace) :
    LanguagePairAgreesOnTrace K₀ K₁ L₀ L₁ trace := by
  intro qa hqa
  exact (h qa hqa).symm

theorem LanguagePairAgreesOnExecution.symm
    {L₀ L₁ K₀ K₁ : Set ℕ} {rounds : List TwoLanguageRound}
    (h : LanguagePairAgreesOnExecution L₀ L₁ K₀ K₁ rounds) :
    LanguagePairAgreesOnExecution K₀ K₁ L₀ L₁ rounds := by
  intro round hround
  exact (h round hround).symm

theorem AnsweredQueryCorrect.transfer
    {L₀ L₁ K₀ K₁ : Set ℕ} {qa : AnsweredTwoLanguageQuery}
    (hcorrect : AnsweredQueryCorrect L₀ L₁ qa)
    (hagree : LanguagePairAgreesAt L₀ L₁ K₀ K₁ qa.1) :
    AnsweredQueryCorrect K₀ K₁ qa := by
  exact hcorrect.trans hagree

theorem QueryTraceValid.transfer
    {A : TwoLanguageMembershipAlgorithm}
    {L₀ L₁ K₀ K₁ : Set ℕ}
    {history : List TwoLanguageRound} {input : ℕ}
    {trace : List AnsweredTwoLanguageQuery}
    (hvalid : QueryTraceValid A L₀ L₁ history input trace)
    (hagree : LanguagePairAgreesOnTrace L₀ L₁ K₀ K₁ trace) :
    QueryTraceValid A K₀ K₁ history input trace := by
  intro k hk
  let qa := trace.get ⟨k, hk⟩
  have hstep := hvalid k hk
  refine ⟨hstep.1, hstep.2.transfer ?_⟩
  exact hagree qa (List.get_mem trace ⟨k, hk⟩)

theorem RoundValid.transfer
    {A : TwoLanguageMembershipAlgorithm}
    {L₀ L₁ K₀ K₁ : Set ℕ}
    {history : List TwoLanguageRound} {input : ℕ}
    {round : TwoLanguageRound}
    (hvalid : RoundValid A L₀ L₁ history input round)
    (hagree :
      LanguagePairAgreesOnTrace L₀ L₁ K₀ K₁ round.2.1) :
    RoundValid A K₀ K₁ history input round := by
  exact ⟨hvalid.1, hvalid.2.1.transfer hagree, hvalid.2.2⟩

theorem ExecutionValid.transfer
    {A : TwoLanguageMembershipAlgorithm}
    {L₀ L₁ K₀ K₁ : Set ℕ}
    {inputs : List ℕ} {rounds : List TwoLanguageRound}
    (hvalid : ExecutionValid A L₀ L₁ inputs rounds)
    (hagree : LanguagePairAgreesOnExecution L₀ L₁ K₀ K₁ rounds) :
    ExecutionValid A K₀ K₁ inputs rounds := by
  refine ⟨hvalid.1, ?_⟩
  intro k hki hkr
  have hround := hvalid.2 k hki hkr
  have hroundMem :
      rounds.get ⟨k, hkr⟩ ∈ rounds :=
    List.get_mem rounds ⟨k, hkr⟩
  exact hround.transfer (hagree _ hroundMem)

theorem executionValid_iff_of_agrees
    {A : TwoLanguageMembershipAlgorithm}
    {L₀ L₁ K₀ K₁ : Set ℕ}
    {inputs : List ℕ} {rounds : List TwoLanguageRound}
    (hagree : LanguagePairAgreesOnExecution L₀ L₁ K₀ K₁ rounds) :
    ExecutionValid A L₀ L₁ inputs rounds ↔
      ExecutionValid A K₀ K₁ inputs rounds := by
  constructor
  · intro hvalid
    exact hvalid.transfer hagree
  · intro hvalid
    exact hvalid.transfer hagree.symm

theorem membershipExecutionOutputsAt_of_shadow
    {A : TwoLanguageMembershipAlgorithm}
    {L₀ L₁ K₀ K₁ : Set ℕ}
    {stream : Stream ℕ} {t z : ℕ}
    (houtput : MembershipExecutionOutputsAt A L₀ L₁ stream t z)
    (hagree :
      ∀ rounds,
        ExecutionValid A L₀ L₁
            (membershipInputPrefix stream (t + 1)) rounds →
          LanguagePairAgreesOnExecution L₀ L₁ K₀ K₁ rounds) :
    MembershipExecutionOutputsAt A K₀ K₁ stream t z := by
  rcases houtput with ⟨rounds, hvalid, ht, hz⟩
  exact ⟨rounds, hvalid.transfer (hagree rounds hvalid), ht, hz⟩

/-! ## Completing a finite partial oracle assignment -/

/-- A finite-stage oracle assignment may leave most words undecided.  The
two Boolean coordinates are the intended membership values for `L₀` and
`L₁`, respectively. -/
abbrev PartialTwoLanguageAssignment := ℕ → Option (Bool × Bool)

/-- A completed pair of languages respects every decision made by a partial
oracle assignment. -/
def LanguagePairRealizes
    (assignment : PartialTwoLanguageAssignment)
    (L₀ L₁ : Set ℕ) : Prop :=
  ∀ x bits, assignment x = some bits →
    (bits.1 = true ↔ x ∈ L₀) ∧
      (bits.2 = true ↔ x ∈ L₁)

/-- Every query word in a trace has already been assigned. -/
def PartialAssignmentDecidesTrace
    (assignment : PartialTwoLanguageAssignment)
    (trace : List AnsweredTwoLanguageQuery) : Prop :=
  ∀ qa ∈ trace, ∃ bits, assignment qa.1.2 = some bits

/-- Every query word in a finite execution has already been assigned. -/
def PartialAssignmentDecidesExecution
    (assignment : PartialTwoLanguageAssignment)
    (rounds : List TwoLanguageRound) : Prop :=
  ∀ round ∈ rounds,
    PartialAssignmentDecidesTrace assignment round.2.1

theorem languagePairAgreesAt_of_realizes
    {assignment : PartialTwoLanguageAssignment}
    {L₀ L₁ K₀ K₁ : Set ℕ} {q : TwoLanguageQuery}
    (hL : LanguagePairRealizes assignment L₀ L₁)
    (hK : LanguagePairRealizes assignment K₀ K₁)
    (hassigned : ∃ bits, assignment q.2 = some bits) :
    LanguagePairAgreesAt L₀ L₁ K₀ K₁ q := by
  rcases q with ⟨side, x⟩
  rcases hassigned with ⟨bits, hbits⟩
  have hLbits := hL x bits hbits
  have hKbits := hK x bits hbits
  cases side
  · simpa [LanguagePairAgreesAt, queriedLanguage] using
      hLbits.1.symm.trans hKbits.1
  · simpa [LanguagePairAgreesAt, queriedLanguage] using
      hLbits.2.symm.trans hKbits.2

theorem languagePairAgreesOnTrace_of_realizes
    {assignment : PartialTwoLanguageAssignment}
    {L₀ L₁ K₀ K₁ : Set ℕ}
    {trace : List AnsweredTwoLanguageQuery}
    (hL : LanguagePairRealizes assignment L₀ L₁)
    (hK : LanguagePairRealizes assignment K₀ K₁)
    (hdecides : PartialAssignmentDecidesTrace assignment trace) :
    LanguagePairAgreesOnTrace L₀ L₁ K₀ K₁ trace := by
  intro qa hqa
  exact languagePairAgreesAt_of_realizes hL hK (hdecides qa hqa)

theorem languagePairAgreesOnExecution_of_realizes
    {assignment : PartialTwoLanguageAssignment}
    {L₀ L₁ K₀ K₁ : Set ℕ}
    {rounds : List TwoLanguageRound}
    (hL : LanguagePairRealizes assignment L₀ L₁)
    (hK : LanguagePairRealizes assignment K₀ K₁)
    (hdecides : PartialAssignmentDecidesExecution assignment rounds) :
    LanguagePairAgreesOnExecution L₀ L₁ K₀ K₁ rounds := by
  intro round hround
  exact languagePairAgreesOnTrace_of_realizes
    hL hK (hdecides round hround)

/-- Headline finite completion invariant: a valid deterministic adaptive
execution survives replacement of the oracle pair by any other completion of
the partial assignment that decided all queries in the execution. -/
theorem executionValid_of_partialAssignment
    {A : TwoLanguageMembershipAlgorithm}
    {assignment : PartialTwoLanguageAssignment}
    {L₀ L₁ K₀ K₁ : Set ℕ}
    {inputs : List ℕ} {rounds : List TwoLanguageRound}
    (hvalid : ExecutionValid A L₀ L₁ inputs rounds)
    (hL : LanguagePairRealizes assignment L₀ L₁)
    (hK : LanguagePairRealizes assignment K₀ K₁)
    (hdecides : PartialAssignmentDecidesExecution assignment rounds) :
    ExecutionValid A K₀ K₁ inputs rounds :=
  hvalid.transfer
    (languagePairAgreesOnExecution_of_realizes hL hK hdecides)

/-! ## Common-prefix transport and the corrected two-target endgame -/

theorem membershipInputPrefix_eq_of_eq_on_prefix
    {stream₀ stream₁ : Stream ℕ} {n : ℕ}
    (hprefix : ∀ k, k < n → stream₀ k = stream₁ k) :
    membershipInputPrefix stream₀ n =
      membershipInputPrefix stream₁ n := by
  unfold membershipInputPrefix
  apply List.ofFn_inj.mpr
  funext k
  exact hprefix k k.isLt

theorem membershipExecutionOutputsAt_of_eq_on_prefix
    {A : TwoLanguageMembershipAlgorithm}
    {L₀ L₁ : Set ℕ}
    {stream₀ stream₁ : Stream ℕ} {t z : ℕ}
    (hprefix : ∀ k, k < t + 1 → stream₀ k = stream₁ k)
    (houtput : MembershipExecutionOutputsAt A L₀ L₁ stream₀ t z) :
    MembershipExecutionOutputsAt A L₀ L₁ stream₁ t z := by
  unfold MembershipExecutionOutputsAt at houtput ⊢
  rw [← membershipInputPrefix_eq_of_eq_on_prefix hprefix]
  exact houtput

/-- The faithful finite endgame of Theorem 7.  Once two exact presentations
share a prefix whose sample is above both non-uniform thresholds, an output on
that prefix must be fresh and belong to both languages.  The two membership
conclusions come from two separate applications of the guarantee. -/
theorem nonuniformGuarantee_commonPrefix_output
    {A : TwoLanguageMembershipAlgorithm} {L₀ L₁ : Set ℕ}
    (hguarantee : NonuniformTwoLanguageMembershipGuarantee A L₀ L₁) :
    ∃ d₀ d₁ : ℕ,
      ∀ (stream₀ stream₁ : Stream ℕ) (t z : ℕ),
        Presents stream₀ L₀ →
        Presents stream₁ L₁ →
        (∀ k, k < t + 1 → stream₀ k = stream₁ k) →
        MembershipExecutionOutputsAt A L₀ L₁ stream₀ t z →
        max d₀ d₁ ≤ (Generic.sample stream₀ (t + 1)).card →
          z ∈ (L₀ ∩ L₁) \ ↑(Generic.sample stream₀ (t + 1)) := by
  rcases hguarantee with ⟨d₀, d₁, hguarantee⟩
  refine ⟨d₀, d₁, ?_⟩
  intro stream₀ stream₁ t z hpresents₀ hpresents₁ hprefix houtput hlarge
  have hsample :
      Generic.sample stream₀ (t + 1) =
        Generic.sample stream₁ (t + 1) :=
    sample_eq_of_eq_on_prefix hprefix
  have houtput₁ :
      MembershipExecutionOutputsAt A L₀ L₁ stream₁ t z :=
    membershipExecutionOutputsAt_of_eq_on_prefix hprefix houtput
  have hd₀ : d₀ ≤ (Generic.sample stream₀ (t + 1)).card :=
    Nat.le_trans (Nat.le_max_left d₀ d₁) hlarge
  have hd₁₀ : d₁ ≤ (Generic.sample stream₀ (t + 1)).card :=
    Nat.le_trans (Nat.le_max_right d₀ d₁) hlarge
  have hd₁ : d₁ ≤ (Generic.sample stream₁ (t + 1)).card := by
    rw [← hsample]
    exact hd₁₀
  have hd₀' :
      selectedThreshold d₀ d₁ false ≤
        (Generic.sample stream₀ (t + 1)).card := by
    simpa [selectedThreshold] using hd₀
  have hd₁' :
      selectedThreshold d₀ d₁ true ≤
        (Generic.sample stream₁ (t + 1)).card := by
    simpa [selectedThreshold] using hd₁
  have hz₀ :
      z ∈ L₀ \ ↑(Generic.sample stream₀ (t + 1)) := by
    simpa [selectedTwoLanguage, selectedThreshold] using
      (hguarantee false stream₀
        (by simpa [selectedTwoLanguage] using hpresents₀) t).2
          z houtput hd₀'
  have hz₁ :
      z ∈ L₁ \ ↑(Generic.sample stream₁ (t + 1)) := by
    simpa [selectedTwoLanguage, selectedThreshold] using
      (hguarantee true stream₁
        (by simpa [selectedTwoLanguage] using hpresents₁) t).2
          z houtput₁ hd₁'
  exact ⟨⟨hz₀.1, hz₁.1⟩, hz₀.2⟩

end GenLimit.CharikarPabbaraju
