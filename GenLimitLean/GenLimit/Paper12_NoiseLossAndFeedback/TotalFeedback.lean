import GenLimit.Paper12_NoiseLossAndFeedback.MandatoryQuery

/-!
# Noise, Loss, and Feedback: mandatory-query totalization

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Section 6.1,
Definitions 6.1--6.2 and Algorithm 4.

The shared `FeedbackGenerator` interface uses `Option` so that a controller
may wait without querying.  Definition 6.1 instead asks for one membership
query on every round.  This file gives that literal mandatory-query
interface and a causal adapter from the shared interface.

When the optional generator waits, the adapter queries a fixed dummy point.
`maskedFeedbackResponses` reconstructs the optional transcript and discards
exactly those dummy answers before running the original generator.  The
simulation theorem proves that truthful totalized execution has the same
outputs as the original optional execution at every round.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

variable {α : Type*}

/-- Definition 6.1's deterministic alternating generator: one mandatory
query and one generated example per round. -/
abbrev TotalFeedbackGenerator (α : Type*) :=
  MandatoryQueryMachine α α

namespace TotalFeedbackGenerator

/-- Compatibility constructor retaining the original paper-facing API. -/
abbrev mk
    (query :
      (t : ℕ) → (Fin (t + 1) → α) → (Fin t → Bool) → α)
    (output :
      (t : ℕ) → (Fin (t + 1) → α) → (Fin (t + 1) → Bool) → α) :
    TotalFeedbackGenerator α :=
  MandatoryQueryMachine.mk query output

/-- Paper-facing query projection. -/
abbrev query (gen : TotalFeedbackGenerator α) :=
  MandatoryQueryMachine.query gen

/-- Paper-facing output projection. -/
abbrev output (gen : TotalFeedbackGenerator α) :=
  MandatoryQueryMachine.output gen

end TotalFeedbackGenerator

/-- Reconstruct the response history expected by an optional-query
generator from a same-length mandatory-query history.  An answer is retained
exactly when the optional generator would have queried on that causal prefix.
-/
def maskedFeedbackResponses
    (gen : FeedbackGenerator α) :
    (n : ℕ) →
      (Fin n → α) →
      (Fin n → Bool) →
      Fin n → Option Bool
  | 0, _observations, _responses => Fin.elim0
  | n + 1, observations, responses =>
      let priorObservations : Fin n → α :=
        fun i => observations i.castSucc
      let priorResponses : Fin n → Bool :=
        fun i => responses i.castSucc
      let maskedPrior :=
        maskedFeedbackResponses gen n priorObservations priorResponses
      let currentResponse :=
        match gen.query n observations maskedPrior with
        | none => none
        | some _query => some (responses (Fin.last n))
      Fin.lastCases currentResponse maskedPrior

@[simp] theorem maskedFeedbackResponses_succ_castSucc
    (gen : FeedbackGenerator α) (n : ℕ)
    (observations : Fin (n + 1) → α)
    (responses : Fin (n + 1) → Bool)
    (i : Fin n) :
    maskedFeedbackResponses gen (n + 1) observations responses i.castSucc =
      maskedFeedbackResponses gen n
        (fun j => observations j.castSucc)
        (fun j => responses j.castSucc) i := by
  simp [maskedFeedbackResponses]

@[simp] theorem maskedFeedbackResponses_succ_last
    (gen : FeedbackGenerator α) (n : ℕ)
    (observations : Fin (n + 1) → α)
    (responses : Fin (n + 1) → Bool) :
    maskedFeedbackResponses gen (n + 1) observations responses (Fin.last n) =
      match
          gen.query n observations
            (maskedFeedbackResponses gen n
              (fun j => observations j.castSucc)
              (fun j => responses j.castSucc)) with
      | none => none
      | some _query => some (responses (Fin.last n)) := by
  simp [maskedFeedbackResponses]

/-- Causally totalize an optional-query generator.  On a wait round the
mandatory interface queries `dummy`, but its answer is masked before the
original query/output functions are evaluated. -/
def totalizeFeedbackGenerator
    (gen : FeedbackGenerator α) (dummy : α) :
    TotalFeedbackGenerator α where
  query := fun t observations responses =>
    (gen.query t observations
      (maskedFeedbackResponses gen t
        (fun i => observations i.castSucc) responses)).getD dummy
  output := fun t observations responses =>
    gen.output t observations
      (maskedFeedbackResponses gen (t + 1) observations responses)

theorem totalizeFeedbackGenerator_query
    (gen : FeedbackGenerator α) (dummy : α)
    (t : ℕ) (observations : Fin (t + 1) → α)
    (responses : Fin t → Bool) :
    (totalizeFeedbackGenerator gen dummy).query t observations responses =
      (gen.query t observations
        (maskedFeedbackResponses gen t
          (fun i => observations i.castSucc) responses)).getD dummy :=
  rfl

theorem totalizeFeedbackGenerator_output
    (gen : FeedbackGenerator α) (dummy : α)
    (t : ℕ) (observations : Fin (t + 1) → α)
    (responses : Fin (t + 1) → Bool) :
    (totalizeFeedbackGenerator gen dummy).output t observations responses =
      gen.output t observations
        (maskedFeedbackResponses gen (t + 1) observations responses) :=
  rfl

/-- Paper-facing name for the shared truthful mandatory-query response. -/
noncomputable abbrev actualTotalFeedbackResponse
    (gen : TotalFeedbackGenerator α)
    (L : GenLimit.Generic.Language α) (stream : Stream α)
    (t : ℕ) : Bool :=
  actualMandatoryQueryResponse gen L stream t

theorem actualTotalFeedbackResponse_eq
    (gen : TotalFeedbackGenerator α)
    (L : GenLimit.Generic.Language α) (stream : Stream α)
    (t : ℕ) :
    actualTotalFeedbackResponse gen L stream t =
      membershipAnswer L
        (gen.query t
          (fun i => stream i)
          (fun i => actualTotalFeedbackResponse gen L stream i)) := by
  exact actualMandatoryQueryResponse_eq gen L stream t

/-- Paper-facing name for the shared mandatory-query output execution. -/
noncomputable abbrev actualTotalFeedbackOutput
    (gen : TotalFeedbackGenerator α)
    (L : GenLimit.Generic.Language α) (stream : Stream α)
    (t : ℕ) : α :=
  actualMandatoryQueryOutput gen L stream t

/-- Correctness in the mandatory-query model at inclusive paper time `t`. -/
def TotalFeedbackCorrectAt
    (gen : TotalFeedbackGenerator α)
    (L : GenLimit.Generic.Language α) (stream : Stream α)
    (t : ℕ) : Prop :=
  actualTotalFeedbackOutput gen L stream t ∈ L ∧
    actualTotalFeedbackOutput gen L stream t ∉
      observedThrough stream t

/-- Definition 6.2 for a fixed generator in Definition 6.1's literal
mandatory-query interface. -/
def IsLimitTotalFeedbackGenerator
    (gen : TotalFeedbackGenerator α)
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∀ stream,
    ExactEnumeration stream L →
      ∃ T, ∀ t, T ≤ t →
        TotalFeedbackCorrectAt gen L stream t

/-- Existential generation in the limit with one membership query on every
round. -/
def GeneratableInLimitWithTotalFeedback
    (C : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : TotalFeedbackGenerator α,
    IsLimitTotalFeedbackGenerator gen C

/-! ## Exact simulation of the optional execution -/

/-- On a truthful execution of the totalized generator, masking the
mandatory Boolean transcript recovers the truthful optional transcript
pointwise.  In particular, answers to dummy queries never enter the original
controller state. -/
theorem maskedFeedbackResponses_actual_totalized
    (gen : FeedbackGenerator α) (dummy : α)
    (L : GenLimit.Generic.Language α) (stream : Stream α) :
    ∀ n,
      maskedFeedbackResponses gen n
          (fun i => stream i)
          (fun i =>
            actualTotalFeedbackResponse
              (totalizeFeedbackGenerator gen dummy) L stream i) =
        fun i : Fin n => actualFeedbackResponse gen L stream i := by
  intro n
  induction n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [maskedFeedbackResponses_succ_last]
        have hmasked :
            maskedFeedbackResponses gen n
                (fun j : Fin n => stream j.castSucc)
                (fun j : Fin n =>
                  actualTotalFeedbackResponse
                    (totalizeFeedbackGenerator gen dummy) L stream
                    j.castSucc) =
              fun j : Fin n =>
                actualFeedbackResponse gen L stream j := by
          simpa using ih
        rw [hmasked]
        rw [actualFeedbackResponse_eq]
        rw [actualTotalFeedbackResponse_eq]
        rw [totalizeFeedbackGenerator_query]
        simp only [Fin.val_last]
        rw [show
          maskedFeedbackResponses gen n
              (fun i : Fin n => stream i.castSucc)
              (fun i : Fin n =>
                actualTotalFeedbackResponse
                  (totalizeFeedbackGenerator gen dummy) L stream i) =
            (fun i : Fin n => actualFeedbackResponse gen L stream i) by
              simpa using ih]
        cases hquery :
            gen.query n
              (fun i : Fin (n + 1) => stream i)
              (fun i : Fin n => actualFeedbackResponse gen L stream i) with
        | none =>
            simp
        | some query =>
            simp
      · rw [maskedFeedbackResponses_succ_castSucc]
        exact congrFun ih j

/-- Totalization preserves the actual output at every time, not merely its
eventual correctness. -/
theorem actualTotalFeedbackOutput_totalized
    (gen : FeedbackGenerator α) (dummy : α)
    (L : GenLimit.Generic.Language α) (stream : Stream α)
    (t : ℕ) :
    actualTotalFeedbackOutput (totalizeFeedbackGenerator gen dummy)
        L stream t =
      actualFeedbackOutput gen L stream t := by
  unfold actualTotalFeedbackOutput actualMandatoryQueryOutput
  unfold actualFeedbackOutput
  change
    gen.output t (fun i => stream i)
        (maskedFeedbackResponses gen (t + 1)
          (fun i => stream i)
          (fun i =>
            actualTotalFeedbackResponse
              (totalizeFeedbackGenerator gen dummy) L stream i)) =
      gen.output t (fun i => stream i)
        (fun i => actualFeedbackResponse gen L stream i)
  rw [maskedFeedbackResponses_actual_totalized]

/-- Per-round correctness is preserved exactly by totalization. -/
theorem totalFeedbackCorrectAt_totalized_iff
    (gen : FeedbackGenerator α) (dummy : α)
    (L : GenLimit.Generic.Language α) (stream : Stream α)
    (t : ℕ) :
    TotalFeedbackCorrectAt (totalizeFeedbackGenerator gen dummy)
        L stream t ↔
      FeedbackCorrectAt gen L stream t := by
  simp only [TotalFeedbackCorrectAt, FeedbackCorrectAt,
    actualTotalFeedbackOutput_totalized]

/-- Any successful optional-query generator can be realized by a generator
that asks one membership query on every round. -/
theorem isLimitTotalFeedbackGenerator_totalize
    (gen : FeedbackGenerator α) (dummy : α)
    (C : GenLimit.Generic.LanguageClass α)
    (hgen :
      ∀ L, L ∈ C → ∀ stream,
        ExactEnumeration stream L →
          ∃ T, ∀ t, T ≤ t →
            FeedbackCorrectAt gen L stream t) :
    IsLimitTotalFeedbackGenerator
      (totalizeFeedbackGenerator gen dummy) C := by
  intro L hL stream henumeration
  obtain ⟨T, hT⟩ := hgen L hL stream henumeration
  refine ⟨T, ?_⟩
  intro t ht
  exact
    (totalFeedbackCorrectAt_totalized_iff gen dummy L stream t).mpr
      (hT t ht)

/-- At the class level, optional-query feedback generation implies literal
one-query-per-round feedback generation whenever a dummy point is available.
-/
theorem generatableInLimitWithTotalFeedback_of_optional
    (C : GenLimit.Generic.LanguageClass α) (dummy : α)
    (hgen :
      ∃ gen : FeedbackGenerator α,
        ∀ L, L ∈ C → ∀ stream,
          ExactEnumeration stream L →
            ∃ T, ∀ t, T ≤ t →
              FeedbackCorrectAt gen L stream t) :
    GeneratableInLimitWithTotalFeedback C := by
  obtain ⟨gen, hgen⟩ := hgen
  exact ⟨totalizeFeedbackGenerator gen dummy,
    isLimitTotalFeedbackGenerator_totalize gen dummy C hgen⟩

end GenLimit.NoiseLossFeedback
