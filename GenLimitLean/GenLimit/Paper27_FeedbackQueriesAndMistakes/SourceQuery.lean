import GenLimit.Paper27_FeedbackQueriesAndMistakes.QueryScheduling
import GenLimit.Support.EnumerationProgress

/-!
# Source-timed one-query set generation

This file repairs the three statement-level gaps found in the Paper 27 query
audit.  It models Definition 2 with no query before the first positive
example, requires every set output to be infinite on every finite transcript,
and retains freshness from the complete observed sample.  The resulting
characterization is the literal semantic/classical content of Theorem 3.4.

Round `t` below is paper round `t + 1`: the strategy sees `t + 1` positive
examples, receives exactly `t` prior query answers, asks one membership query,
and emits its set after the current answer has been appended.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-- The part of a source-timed one-query strategy that determines the next
membership query.  Element- and set-valued generators share this interaction
kernel even though their output types and success predicates differ. -/
abbrev SourceQueryPolicy (α : Type*) :=
  ∀ t, (Fin (t + 1) → α) → List Bool → α

/-- Truthful membership-query feedback before paper round `t + 1`, shared by
all source-timed output types. -/
noncomputable def sourceQueryFeedback
    (query : SourceQueryPolicy α)
    (target : Set α) (stream : Stream α) : ℕ → List Bool
  | 0 => []
  | t + 1 =>
      let history := sourceQueryFeedback query target stream t
      history ++
        [membershipAnswer target
          (query t (fun i => stream i) history)]

@[simp] theorem sourceQueryFeedback_zero
    (query : SourceQueryPolicy α)
    (target : Set α) (stream : Stream α) :
    sourceQueryFeedback query target stream 0 = [] :=
  rfl

@[simp] theorem sourceQueryFeedback_succ
    (query : SourceQueryPolicy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    sourceQueryFeedback query target stream (t + 1) =
      sourceQueryFeedback query target stream t ++
        [membershipAnswer target
          (query t (fun i => stream i)
            (sourceQueryFeedback query target stream t))] :=
  rfl

@[simp] theorem sourceQueryFeedback_length
    (query : SourceQueryPolicy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    (sourceQueryFeedback query target stream t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [sourceQueryFeedback_succ, List.length_append,
        List.length_singleton, ih]

/-- Definition 2's source-timed set-valued query strategy.  The infinitude
field is global over all well-shaped transcripts, including answer histories
that do not arise from a truthful run.  The totalized `output` function may
behave arbitrarily on lists of the wrong length. -/
structure SourceSetQueryStrategy (α : Type*) where
  query : SourceQueryPolicy α
  output : ∀ t, (Fin (t + 1) → α) → List Bool → Set α
  output_infinite : ∀ t samples answers,
    answers.length = t + 1 → (output t samples answers).Infinite

/-- Truthful feedback before paper round `t + 1`.  In particular, round zero
has no pre-sample query. -/
noncomputable def sourceSetQueryFeedback
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) : ℕ → List Bool :=
  sourceQueryFeedback strategy.query target stream

@[simp] theorem sourceSetQueryFeedback_zero
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) :
    sourceSetQueryFeedback strategy target stream 0 = [] :=
  sourceQueryFeedback_zero strategy.query target stream

@[simp] theorem sourceSetQueryFeedback_succ
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    sourceSetQueryFeedback strategy target stream (t + 1) =
      sourceSetQueryFeedback strategy target stream t ++
        [membershipAnswer target
          (strategy.query t (fun i => stream i)
            (sourceSetQueryFeedback strategy target stream t))] :=
  sourceQueryFeedback_succ strategy.query target stream t

@[simp] theorem sourceSetQueryFeedback_length
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    (sourceSetQueryFeedback strategy target stream t).length = t := by
  exact sourceQueryFeedback_length strategy.query target stream t

/-- The set emitted in paper round `t + 1`, after the current membership
answer is available. -/
noncomputable def sourceSetQueryOutput
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : Set α :=
  strategy.output t (fun i => stream i)
    (sourceSetQueryFeedback strategy target stream (t + 1))

theorem sourceSetQueryOutput_infinite
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    (sourceSetQueryOutput strategy target stream t).Infinite :=
  strategy.output_infinite _ _ _
    (sourceSetQueryFeedback_length strategy target stream (t + 1))

/-- Source Definition 2 success: after a run-dependent threshold, the whole
infinite output is target-valid and fresh relative to all `t + 1` examples
visible in the current paper round. -/
def SourceSetQuerySucceedsOn
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream target →
    ∃ T, ∀ t, T ≤ t →
      sourceSetQueryOutput strategy target stream t ⊆
        target \ (Generic.sample stream (t + 1) : Set α)

def SourceSetQueryGenerates
    (strategy : SourceSetQueryStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ target, target ∈ targets → SourceSetQuerySucceedsOn strategy target

def SourceSetQueryGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : SourceSetQueryStrategy α,
    SourceSetQueryGenerates strategy targets

/-! ## Necessity: the range of finite source transcripts is countable -/

abbrev SourceSetQueryTranscript (α : Type*) :=
  Σ t : ℕ,
    (Fin (t + 1) → α) ×
      {answers : List Bool // answers.length = t + 1}

noncomputable def countableInnerCoverOfSourceSetQuery
    [Countable α] [Nonempty α]
    {targets : LanguageClass α}
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (strategy : SourceSetQueryStrategy α)
    (hstrategy : SourceSetQueryGenerates strategy targets) :
    CountableInnerCover targets := by
  classical
  letI : Nonempty (SourceSetQueryTranscript α) :=
    ⟨⟨0, (fun _ => Classical.choice inferInstance,
      ⟨[false], by simp⟩)⟩⟩
  let output : SourceSetQueryTranscript α → Set α := fun transcript =>
    strategy.output transcript.1 transcript.2.1 transcript.2.2.1
  apply CountableInnerCover.ofCountableFamily output
  · intro transcript
    exact strategy.output_infinite _ _ _ transcript.2.2.2
  · intro L hL
    let stream : Stream α :=
      GenLimit.Support.infiniteEnumeration L (hinfinite L hL)
    have hPresents : Generic.Presents stream L :=
      GenLimit.Support.infiniteEnumeration_presents L (hinfinite L hL)
    obtain ⟨T, hT⟩ := hstrategy L hL stream hPresents
    let transcript : SourceSetQueryTranscript α :=
      ⟨T, (fun i => stream i,
        ⟨sourceSetQueryFeedback strategy L stream (T + 1),
          sourceSetQueryFeedback_length strategy L stream (T + 1)⟩)⟩
    refine ⟨transcript, ?_⟩
    intro x hx
    have hgood := hT T (Nat.le_refl T)
    have hx' : x ∈ strategy.output T (fun i => stream i)
        (sourceSetQueryFeedback strategy L stream (T + 1)) := by
      simpa [output, transcript] using hx
    exact (hgood hx').1

theorem sourceSetQuery_implies_countableInnerCover
    [Countable α] [Nonempty α]
    {targets : LanguageClass α}
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (h : SourceSetQueryGeneratable targets) :
    HasCountableInnerCover targets := by
  obtain ⟨strategy, hstrategy⟩ := h
  exact ⟨countableInnerCoverOfSourceSetQuery hinfinite strategy hstrategy⟩

/-! ## Sufficiency: the existing fair search, retimed and made fresh -/

/-- The fair cover search in the exact source protocol.  Removing the finite
positive sample makes every output fresh and preserves infinitude. -/
noncomputable def innerCoverSourceSetQueryStrategy
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    SourceSetQueryStrategy α where
  query := fun t _samples _answers => innerCoverOneQueryPoint inner t
  output := fun t samples answers =>
    inner.cover (firstPassingOneQueryRow t answers) \
      (sequenceSample samples : Set α)
  output_infinite := by
    intro t samples answers _hanswers
    exact
      (inner.infinite_cover (firstPassingOneQueryRow t answers)).diff
        (sequenceSample samples).finite_toSet

/-- Retiming changes the positive-history length but not the fair scheduler's
truthful Boolean transcript, because its query is sample-independent. -/
theorem innerCoverSourceSetQueryFeedback_eq
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (L : Set α) (stream : Stream α) (t : ℕ) :
    sourceSetQueryFeedback
        (innerCoverSourceSetQueryStrategy inner) L stream t =
      positiveSequenceOneQueryFeedback
        (innerCoverOneQueryStrategy inner) L stream t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [sourceSetQueryFeedback_succ,
        positiveSequenceOneQueryFeedback_succ, ih]
      rfl

theorem innerCoverSourceSetQueryOutput_eq
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (L : Set α) (stream : Stream α) (t : ℕ) :
    sourceSetQueryOutput
        (innerCoverSourceSetQueryStrategy inner) L stream t =
      positiveSequenceOneQueryOutput
        (innerCoverOneQueryStrategy inner) L stream t \
        (Generic.sample stream (t + 1) : Set α) := by
  unfold sourceSetQueryOutput positiveSequenceOneQueryOutput
  change
    inner.cover
          (firstPassingOneQueryRow t
            (sourceSetQueryFeedback
              (innerCoverSourceSetQueryStrategy inner)
              L stream (t + 1))) \
        (sequenceSample (fun i : Fin (t + 1) => stream i) : Set α) =
      inner.cover
          (firstPassingOneQueryRow t
            (positiveSequenceOneQueryFeedback
              (innerCoverOneQueryStrategy inner)
              L stream (t + 1))) \
        (Generic.sample stream (t + 1) : Set α)
  rw [innerCoverSourceSetQueryFeedback_eq, sequenceSample_prefix]

theorem countableInnerCover_implies_sourceSetQuery
    [Countable α]
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    SourceSetQueryGeneratable targets := by
  classical
  let inner := Nonempty.some hinner
  refine ⟨innerCoverSourceSetQueryStrategy inner, ?_⟩
  intro L hL stream _hPresents
  let hexists : ∃ i, inner.cover i ⊆ L := inner.contained L hL
  let k := Nat.find hexists
  have hgood : inner.cover k ⊆ L := by
    simpa [k] using Nat.find_spec hexists
  have hminimal : ∀ i, i < k → ¬ inner.cover i ⊆ L := by
    intro i hi
    exact Nat.find_min hexists (by simpa [k] using hi)
  obtain ⟨T, hT⟩ :=
    countableInnerCover_oneQuery_eventually
      inner L stream k hgood hminimal
  refine ⟨T, ?_⟩
  intro t ht
  rw [innerCoverSourceSetQueryOutput_eq, hT t ht]
  intro x hx
  exact ⟨hgood hx.1, hx.2⟩

/-- Source Theorem 3.4: a class of infinite languages is set-generatable
with exactly one source-timed membership query per round iff it has a
countable inner cover. -/
theorem theorem_3_4_sourceSetQuery_characterization
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    SourceSetQueryGeneratable targets ↔ HasCountableInnerCover targets :=
  ⟨sourceSetQuery_implies_countableInnerCover hinfinite,
    countableInnerCover_implies_sourceSetQuery⟩

end GenLimit.FeedbackQueries
