import GenLimit.Paper27_FeedbackQueriesAndMistakes.Bridges
import GenLimit.Support.EnumerationProgress
import Mathlib.Data.Countable.Basic

/-!
# Positive-sequence wrappers for feedback generation

The paper gives its feedback algorithms both the finite positive-example
sequence seen so far and the relevant feedback transcript.  The earlier files
in this directory isolate sample-free auxiliary models.  This file restores
the positive-sequence input for those auxiliary whole-set-validity and square
batch-query models.

At round `t`, a strategy receives the literal finite sequence
`Fin t → α`.  Success is required for every exact positive presentation of
the target.  The sufficiency directions lift the checked sample-free
strategies by ignoring the positive sequence.  The necessity directions are
not aliases: they enumerate all finite positive sequences together with all
finite feedback transcripts and extract a countable inner cover from an
arbitrary successful sequence-input strategy.

It does not close correspondence to the paper by itself: the mistake bit here
tests the whole set rather than the source's first element, while the query
model uses a same-round square batch and omits the source freshness condition.
The exact source interactions are in `SourceSetMistake.lean` and
`SourceQuery.lean`.  No computability, adaptive-query, query-complexity, or
runtime statement is made here.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-! ## Mistake feedback with a positive-sequence input -/

/-- A set-valued mistake-feedback strategy with the literal finite positive
sequence supplied at each round. -/
abbrev PositiveSequenceSetMistakeStrategy (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → List Bool → Set α

/-- The truthful reply to a sequence-input set output. -/
noncomputable def positiveSequenceMistakeReply
    (strategy : PositiveSequenceSetMistakeStrategy α)
    (target : Set α) (t : ℕ) (xs : Fin t → α)
    (history : List Bool) : Bool := by
  classical
  exact if strategy t xs history ⊆ target then true else false

/-- The finite mistake-feedback history before round `t`. -/
noncomputable def positiveSequenceMistakeHistory
    (strategy : PositiveSequenceSetMistakeStrategy α)
    (target : Set α) (stream : Stream α) : ℕ → List Bool
  | 0 => []
  | t + 1 =>
      let history :=
        positiveSequenceMistakeHistory strategy target stream t
      history ++
        [positiveSequenceMistakeReply strategy target t
          (fun i => stream i) history]

@[simp] theorem positiveSequenceMistakeHistory_zero
    (strategy : PositiveSequenceSetMistakeStrategy α)
    (target : Set α) (stream : Stream α) :
    positiveSequenceMistakeHistory strategy target stream 0 = [] :=
  rfl

@[simp] theorem positiveSequenceMistakeHistory_succ
    (strategy : PositiveSequenceSetMistakeStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    positiveSequenceMistakeHistory strategy target stream (t + 1) =
      positiveSequenceMistakeHistory strategy target stream t ++
        [positiveSequenceMistakeReply strategy target t
          (fun i => stream i)
          (positiveSequenceMistakeHistory strategy target stream t)] :=
  rfl

/-- The set emitted in round `t` against the exact positive presentation. -/
noncomputable def positiveSequenceMistakeOutput
    (strategy : PositiveSequenceSetMistakeStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : Set α :=
  strategy t (fun i => stream i)
    (positiveSequenceMistakeHistory strategy target stream t)

/-- Eventual set generation for every exact positive presentation of one
target. -/
def PositiveSequenceSetMistakeSucceedsOn
    (strategy : PositiveSequenceSetMistakeStrategy α)
    (target : Set α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream target →
    ∃ T, ∀ t, T ≤ t →
      (positiveSequenceMistakeOutput strategy target stream t).Infinite ∧
        positiveSequenceMistakeOutput strategy target stream t ⊆ target

def PositiveSequenceSetMistakeGenerates
    (strategy : PositiveSequenceSetMistakeStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → PositiveSequenceSetMistakeSucceedsOn strategy L

def PositiveSequenceSetMistakeGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : PositiveSequenceSetMistakeStrategy α,
    PositiveSequenceSetMistakeGenerates strategy targets

/-- A sample-free strategy is a sequence-input strategy that ignores its
positive examples. -/
def liftSetMistakeStrategy
    (strategy : SetMistakeStrategy α) :
    PositiveSequenceSetMistakeStrategy α :=
  fun _t _xs history => strategy history

@[simp] theorem positiveSequenceMistakeReply_lift
    (strategy : SetMistakeStrategy α)
    (target : Set α) (t : ℕ) (xs : Fin t → α)
    (history : List Bool) :
    positiveSequenceMistakeReply
        (liftSetMistakeStrategy strategy) target t xs history =
      mistakeReply strategy target history := by
  simp [positiveSequenceMistakeReply, mistakeReply,
    liftSetMistakeStrategy]

@[simp] theorem positiveSequenceMistakeHistory_lift
    (strategy : SetMistakeStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    positiveSequenceMistakeHistory
        (liftSetMistakeStrategy strategy) target stream t =
      mistakeHistory strategy target t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [positiveSequenceMistakeHistory_succ, mistakeHistory_succ, ih]
      simp

@[simp] theorem positiveSequenceMistakeOutput_lift
    (strategy : SetMistakeStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    positiveSequenceMistakeOutput
        (liftSetMistakeStrategy strategy) target stream t =
      mistakeOutput strategy target t := by
  simp [positiveSequenceMistakeOutput, mistakeOutput,
    liftSetMistakeStrategy]

/-- A finite positive sequence together with a finite Boolean feedback
history.  This dependent-sum transcript type is countable. -/
abbrev PositiveSequenceMistakeTranscript (α : Type*) :=
  Σ t : ℕ, (Fin t → α) × List Bool

/-- Necessity for the literal positive-sequence mistake interface. -/
noncomputable def countableInnerCoverOfPositiveSequenceSetMistake
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (strategy : PositiveSequenceSetMistakeStrategy α)
    (hstrategy : PositiveSequenceSetMistakeGenerates strategy targets) :
    CountableInnerCover targets := by
  letI : Nonempty (PositiveSequenceMistakeTranscript α) :=
    ⟨⟨0, (fun i => Fin.elim0 i, [])⟩⟩
  let output : PositiveSequenceMistakeTranscript α → Set α :=
    fun transcript =>
      strategy transcript.1 transcript.2.1 transcript.2.2
  apply CountableInnerCover.ofCountableOutputs output
  intro L hL
  let stream : Stream α :=
    GenLimit.Support.infiniteEnumeration L (hinfinite L hL)
  have hPresents : Generic.Presents stream L :=
    GenLimit.Support.infiniteEnumeration_presents L (hinfinite L hL)
  obtain ⟨T, hT⟩ := hstrategy L hL stream hPresents
  have hgood := hT T (Nat.le_refl T)
  let transcript : PositiveSequenceMistakeTranscript α :=
    ⟨T, (fun i => stream i,
      positiveSequenceMistakeHistory strategy L stream T)⟩
  refine ⟨transcript, ?_, ?_⟩
  · simpa [output, transcript] using hgood.1
  · simpa [output, transcript] using hgood.2

theorem positiveSequenceSetMistake_implies_countableInnerCover
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (h : PositiveSequenceSetMistakeGeneratable targets) :
    HasCountableInnerCover targets := by
  obtain ⟨strategy, hstrategy⟩ := h
  exact
    ⟨countableInnerCoverOfPositiveSequenceSetMistake
      hinfinite strategy hstrategy⟩

theorem countableInnerCover_implies_positiveSequenceSetMistake
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    PositiveSequenceSetMistakeGeneratable targets := by
  obtain ⟨strategy, hstrategy⟩ :=
    countableInnerCover_implies_setMistake hinner
  refine ⟨liftSetMistakeStrategy strategy, ?_⟩
  intro L hL stream _hPresents
  obtain ⟨T, hT⟩ := hstrategy L hL
  refine ⟨T, ?_⟩
  intro t ht
  simpa using hT t ht

/-- The auxiliary whole-set-validity characterization with a literal positive
sequence input. -/
theorem positiveSequenceSetMistake_characterization
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    PositiveSequenceSetMistakeGeneratable targets ↔
      HasCountableInnerCover targets :=
  ⟨positiveSequenceSetMistake_implies_countableInnerCover hinfinite,
    countableInnerCover_implies_positiveSequenceSetMistake⟩

/-! ## Membership-query feedback with a positive-sequence input -/

/-- Square-query normal form with the literal finite positive sequence
supplied to both the query selector and output map. -/
structure PositiveSequenceSetQueryStrategy (α : Type*) where
  query :
    ∀ t, (Fin t → α) → Fin (t + 1) → Fin (t + 1) → α
  output :
    ∀ t, (Fin t → α) →
      (Fin (t + 1) → Fin (t + 1) → Bool) → Set α

noncomputable def positiveSequenceTruthfulQueryTable
    (strategy : PositiveSequenceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    Fin (t + 1) → Fin (t + 1) → Bool :=
  fun i k =>
    membershipAnswer target
      (strategy.query t (fun j => stream j) i k)

noncomputable def positiveSequenceSetQueryOutput
    (strategy : PositiveSequenceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : Set α :=
  strategy.output t (fun i => stream i)
    (positiveSequenceTruthfulQueryTable strategy target stream t)

def PositiveSequenceSetQuerySucceedsOn
    (strategy : PositiveSequenceSetQueryStrategy α)
    (target : Set α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream target →
    ∃ T, ∀ t, T ≤ t →
      (positiveSequenceSetQueryOutput strategy target stream t).Infinite ∧
        positiveSequenceSetQueryOutput strategy target stream t ⊆ target

def PositiveSequenceSetQueryGenerates
    (strategy : PositiveSequenceSetQueryStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → PositiveSequenceSetQuerySucceedsOn strategy L

def PositiveSequenceSetQueryGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : PositiveSequenceSetQueryStrategy α,
    PositiveSequenceSetQueryGenerates strategy targets

def liftSetQueryStrategy
    (strategy : SetQueryStrategy α) :
    PositiveSequenceSetQueryStrategy α where
  query := fun t _xs i k => strategy.query t i k
  output := fun t _xs table => strategy.output t table

@[simp] theorem positiveSequenceTruthfulQueryTable_lift
    (strategy : SetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    positiveSequenceTruthfulQueryTable
        (liftSetQueryStrategy strategy) target stream t =
      truthfulQueryTable strategy target t :=
  rfl

@[simp] theorem positiveSequenceSetQueryOutput_lift
    (strategy : SetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    positiveSequenceSetQueryOutput
        (liftSetQueryStrategy strategy) target stream t =
      setQueryOutput strategy target t :=
  rfl

/-- Countable coding of a query round, its finite positive sequence, and its
finite Boolean answer table. -/
abbrev PositiveSequenceQueryTranscript (α : Type*) :=
  Σ t : ℕ, (Fin t → α) × Finset (ℕ × ℕ)

noncomputable def countableInnerCoverOfPositiveSequenceSetQuery
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (strategy : PositiveSequenceSetQueryStrategy α)
    (hstrategy : PositiveSequenceSetQueryGenerates strategy targets) :
    CountableInnerCover targets := by
  letI : Nonempty (PositiveSequenceQueryTranscript α) :=
    ⟨⟨0, (fun i => Fin.elim0 i, ∅)⟩⟩
  let output : PositiveSequenceQueryTranscript α → Set α :=
    fun transcript =>
      strategy.output transcript.1 transcript.2.1
        (decodeQueryTable transcript.1 transcript.2.2)
  apply CountableInnerCover.ofCountableOutputs output
  intro L hL
  let stream : Stream α :=
    GenLimit.Support.infiniteEnumeration L (hinfinite L hL)
  have hPresents : Generic.Presents stream L :=
    GenLimit.Support.infiniteEnumeration_presents L (hinfinite L hL)
  obtain ⟨T, hT⟩ := hstrategy L hL stream hPresents
  have hgood := hT T (Nat.le_refl T)
  let answers := positiveSequenceTruthfulQueryTable strategy L stream T
  let transcript : PositiveSequenceQueryTranscript α :=
    ⟨T, (fun i => stream i, encodeQueryTable T answers)⟩
  refine ⟨transcript, ?_, ?_⟩
  · simpa [output, transcript, decode_encodeQueryTable] using hgood.1
  · simpa [output, transcript, decode_encodeQueryTable] using hgood.2

theorem positiveSequenceSetQuery_implies_countableInnerCover
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (h : PositiveSequenceSetQueryGeneratable targets) :
    HasCountableInnerCover targets := by
  obtain ⟨strategy, hstrategy⟩ := h
  exact
    ⟨countableInnerCoverOfPositiveSequenceSetQuery
      hinfinite strategy hstrategy⟩

theorem countableInnerCover_implies_positiveSequenceSetQuery
    [Countable α]
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    PositiveSequenceSetQueryGeneratable targets := by
  obtain ⟨strategy, hstrategy⟩ :=
    countableInnerCover_implies_setQuery hinner
  refine ⟨liftSetQueryStrategy strategy, ?_⟩
  intro L hL stream _hPresents
  obtain ⟨T, hT⟩ := hstrategy L hL
  refine ⟨T, ?_⟩
  intro t ht
  simpa using hT t ht

/-- The auxiliary square-query characterization with a literal finite positive
sequence supplied to the strategy. -/
theorem positiveSequenceSetQuery_characterization
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    PositiveSequenceSetQueryGeneratable targets ↔
      HasCountableInnerCover targets :=
  ⟨positiveSequenceSetQuery_implies_countableInnerCover hinfinite,
    countableInnerCover_implies_positiveSequenceSetQuery⟩

/-- On classes of infinite languages, the two auxiliary set-valued feedback
models remain equivalent after adding the same positive-sequence input. -/
theorem positiveSequenceSetMistake_iff_setQuery
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    PositiveSequenceSetMistakeGeneratable targets ↔
      PositiveSequenceSetQueryGeneratable targets := by
  rw [positiveSequenceSetMistake_characterization targets hinfinite,
    positiveSequenceSetQuery_characterization targets hinfinite]

end GenLimit.FeedbackQueries
