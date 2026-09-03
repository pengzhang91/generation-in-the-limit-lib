import GenLimit.Paper27_FeedbackQueriesAndMistakes.PositiveSequence
import GenLimit.Support.EnumerationProgress
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Square padding and an auxiliary one-query scheduler

This module proves two auxiliary scheduling results used around Theorem 3.4 of
Hanneke--Karbasi--Mehrotra--Velegkas.

First, any positive-history-dependent nonadaptive batch containing at most
`(t+1)^2` membership queries is padded into the repository's exact square
table.  The original answer vector and output are recovered literally; the
extra coordinates query one explicit padding element and are ignored.

Second, a recursively replayed interaction asks exactly one membership query
per round.  A fair schedule tests every indexed point of every inner-cover
member.  It eventually rejects every false cover before the least true one,
giving the same countable-inner-cover characterization as the square model.
This auxiliary interaction starts with a pre-sample query, does not impose
global output infinitude on unreachable transcripts, and omits sample
freshness.  `SourceQuery.lean` retimes the search and restores all three
requirements of Definition 2.

These are semantic/classical normalizations.  They do not assert that an
arbitrary machine transformation is computable or preserves running time.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-! ## Padding a bounded batch into the exact square table -/

/-- A nonadaptive query batch whose size may vary with the round but is
bounded by the source square budget. -/
structure PositiveSequenceBoundedBatchSetQueryStrategy (α : Type*) where
  queryCount : ℕ → ℕ
  queryCount_le_square :
    ∀ t, queryCount t ≤ (t + 1) * (t + 1)
  query :
    ∀ t, (Fin t → α) → Fin (queryCount t) → α
  output :
    ∀ t, (Fin t → α) →
      (Fin (queryCount t) → Bool) → Set α

/-- Truthful answers to the unpadded bounded batch. -/
noncomputable def positiveSequenceBoundedBatchTruthfulAnswers
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    Fin (strategy.queryCount t) → Bool :=
  fun j =>
    membershipAnswer target
      (strategy.query t (fun i => stream i) j)

/-- Output of the unpadded bounded batch. -/
noncomputable def positiveSequenceBoundedBatchOutput
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : Set α :=
  strategy.output t (fun i => stream i)
    (positiveSequenceBoundedBatchTruthfulAnswers
      strategy target stream t)

/-- The square coordinate occupied by one genuine bounded-batch query. -/
def boundedBatchSquareCoordinate
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (t : ℕ) (j : Fin (strategy.queryCount t)) :
    Fin (t + 1) × Fin (t + 1) :=
  finProdFinEquiv.symm
    (Fin.castLE (strategy.queryCount_le_square t) j)

@[simp] theorem finProdFinEquiv_boundedBatchSquareCoordinate
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (t : ℕ) (j : Fin (strategy.queryCount t)) :
    finProdFinEquiv
        (boundedBatchSquareCoordinate strategy t j) =
      Fin.castLE (strategy.queryCount_le_square t) j := by
  exact Equiv.apply_symm_apply finProdFinEquiv _

/-- Pad an at-most-square batch to exactly `(t+1)^2` queries.  Coordinates
outside the genuine batch repeat `padding`; the output discards their
answers. -/
def padBoundedBatchToSquare
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (padding : α) :
    PositiveSequenceSetQueryStrategy α where
  query := fun t xs i k =>
    let flat : Fin ((t + 1) * (t + 1)) :=
      finProdFinEquiv (i, k)
    if h : flat.val < strategy.queryCount t then
      strategy.query t xs ⟨flat.val, h⟩
    else
      padding
  output := fun t xs table =>
    strategy.output t xs fun j =>
      let coordinate := boundedBatchSquareCoordinate strategy t j
      table coordinate.1 coordinate.2

/-- Reading the genuine square coordinates recovers the bounded batch's
truthful answer vector exactly. -/
theorem padBoundedBatchToSquare_recovers_truthfulAnswers
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (padding : α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    (fun j =>
      let coordinate := boundedBatchSquareCoordinate strategy t j
      positiveSequenceTruthfulQueryTable
        (padBoundedBatchToSquare strategy padding)
        target stream t coordinate.1 coordinate.2) =
      positiveSequenceBoundedBatchTruthfulAnswers
        strategy target stream t := by
  funext j
  change
    membershipAnswer target
        (if h :
            (finProdFinEquiv
              (boundedBatchSquareCoordinate strategy t j)).val <
                strategy.queryCount t
          then
            strategy.query t (fun i => stream i)
              ⟨(finProdFinEquiv
                (boundedBatchSquareCoordinate strategy t j)).val, h⟩
          else padding) =
      membershipAnswer target
        (strategy.query t (fun i => stream i) j)
  have hlt :
      (finProdFinEquiv
        (boundedBatchSquareCoordinate strategy t j)).val <
          strategy.queryCount t := by
    simp
  rw [dif_pos hlt]
  congr 2
  apply Fin.ext
  simp

/-- Exact output preservation for square padding. -/
theorem padBoundedBatchToSquare_output_eq
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (padding : α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    positiveSequenceSetQueryOutput
        (padBoundedBatchToSquare strategy padding)
        target stream t =
      positiveSequenceBoundedBatchOutput
        strategy target stream t := by
  simp only [positiveSequenceSetQueryOutput,
    positiveSequenceBoundedBatchOutput, padBoundedBatchToSquare]
  congr 1
  exact padBoundedBatchToSquare_recovers_truthfulAnswers
    strategy padding target stream t

def PositiveSequenceBoundedBatchSetSucceedsOn
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (target : Set α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream target →
    ∃ T, ∀ t, T ≤ t →
      (positiveSequenceBoundedBatchOutput
        strategy target stream t).Infinite ∧
      positiveSequenceBoundedBatchOutput
        strategy target stream t ⊆ target

def PositiveSequenceBoundedBatchSetGenerates
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ target, target ∈ targets →
    PositiveSequenceBoundedBatchSetSucceedsOn strategy target

/-- Padding preserves eventual success on every presentation, not only the
output at one fixed history. -/
theorem padBoundedBatchToSquare_succeedsOn_iff
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (padding : α) (target : Set α) :
    PositiveSequenceSetQuerySucceedsOn
        (padBoundedBatchToSquare strategy padding) target ↔
      PositiveSequenceBoundedBatchSetSucceedsOn
        strategy target := by
  constructor
  · intro h stream hPresents
    obtain ⟨T, hT⟩ := h stream hPresents
    refine ⟨T, ?_⟩
    intro t hTt
    rw [← padBoundedBatchToSquare_output_eq]
    exact hT t hTt
  · intro h stream hPresents
    obtain ⟨T, hT⟩ := h stream hPresents
    refine ⟨T, ?_⟩
    intro t hTt
    rw [padBoundedBatchToSquare_output_eq]
    exact hT t hTt

theorem padBoundedBatchToSquare_generates_iff
    (strategy : PositiveSequenceBoundedBatchSetQueryStrategy α)
    (padding : α) (targets : LanguageClass α) :
    PositiveSequenceSetQueryGenerates
        (padBoundedBatchToSquare strategy padding) targets ↔
      PositiveSequenceBoundedBatchSetGenerates
        strategy targets := by
  constructor
  · intro h target htarget
    exact
      (padBoundedBatchToSquare_succeedsOn_iff
        strategy padding target).mp (h target htarget)
  · intro h target htarget
    exact
      (padBoundedBatchToSquare_succeedsOn_iff
        strategy padding target).mpr (h target htarget)

/-! ## An auxiliary pre-sample one-membership-query interaction -/

/-- A set generator that asks exactly one membership query per round.

The query sees the current finite positive sequence and all preceding query
answers.  The output sees the same positive sequence and the transcript after
the current answer has been appended. -/
structure PositiveSequenceOneQuerySetStrategy (α : Type*) where
  query : ∀ t, (Fin t → α) → List Bool → α
  output : ∀ t, (Fin t → α) → List Bool → Set α

/-- The truthful one-query transcript after `t` rounds. -/
noncomputable def positiveSequenceOneQueryFeedback
    (strategy : PositiveSequenceOneQuerySetStrategy α)
    (target : Set α) (stream : Stream α) : ℕ → List Bool
  | 0 => []
  | t + 1 =>
      let history :=
        positiveSequenceOneQueryFeedback strategy target stream t
      history ++
        [membershipAnswer target
          (strategy.query t (fun i => stream i) history)]

@[simp] theorem positiveSequenceOneQueryFeedback_zero
    (strategy : PositiveSequenceOneQuerySetStrategy α)
    (target : Set α) (stream : Stream α) :
    positiveSequenceOneQueryFeedback strategy target stream 0 = [] :=
  rfl

@[simp] theorem positiveSequenceOneQueryFeedback_succ
    (strategy : PositiveSequenceOneQuerySetStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    positiveSequenceOneQueryFeedback strategy target stream (t + 1) =
      positiveSequenceOneQueryFeedback strategy target stream t ++
        [membershipAnswer target
          (strategy.query t (fun i => stream i)
            (positiveSequenceOneQueryFeedback
              strategy target stream t))] :=
  rfl

@[simp] theorem positiveSequenceOneQueryFeedback_length
    (strategy : PositiveSequenceOneQuerySetStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    (positiveSequenceOneQueryFeedback
      strategy target stream t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [positiveSequenceOneQueryFeedback_succ,
        List.length_append, List.length_singleton, ih]

/-- Output after the unique query in round `t` has been answered. -/
noncomputable def positiveSequenceOneQueryOutput
    (strategy : PositiveSequenceOneQuerySetStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : Set α :=
  strategy.output t (fun i => stream i)
    (positiveSequenceOneQueryFeedback
      strategy target stream (t + 1))

def PositiveSequenceOneQuerySetSucceedsOn
    (strategy : PositiveSequenceOneQuerySetStrategy α)
    (target : Set α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream target →
    ∃ T, ∀ t, T ≤ t →
      (positiveSequenceOneQueryOutput
        strategy target stream t).Infinite ∧
      positiveSequenceOneQueryOutput
        strategy target stream t ⊆ target

def PositiveSequenceOneQuerySetGenerates
    (strategy : PositiveSequenceOneQuerySetStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ target, target ∈ targets →
    PositiveSequenceOneQuerySetSucceedsOn strategy target

def PositiveSequenceOneQuerySetGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : PositiveSequenceOneQuerySetStrategy α,
    PositiveSequenceOneQuerySetGenerates strategy targets

/-! ## Necessity: finite one-query transcripts are countable -/

abbrev PositiveSequenceOneQueryTranscript (α : Type*) :=
  Σ t : ℕ, (Fin t → α) × List Bool

noncomputable def countableInnerCoverOfPositiveSequenceOneQuery
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (strategy : PositiveSequenceOneQuerySetStrategy α)
    (hstrategy :
      PositiveSequenceOneQuerySetGenerates strategy targets) :
    CountableInnerCover targets := by
  letI : Nonempty (PositiveSequenceOneQueryTranscript α) :=
    ⟨⟨0, (fun i => Fin.elim0 i, [])⟩⟩
  let output : PositiveSequenceOneQueryTranscript α → Set α :=
    fun transcript =>
      strategy.output transcript.1 transcript.2.1 transcript.2.2
  apply CountableInnerCover.ofCountableOutputs output
  intro L hL
  let stream : Stream α :=
    GenLimit.Support.infiniteEnumeration L (hinfinite L hL)
  have hPresents : Generic.Presents stream L :=
    GenLimit.Support.infiniteEnumeration_presents L (hinfinite L hL)
  obtain ⟨T, hT⟩ := hstrategy L hL stream hPresents
  have hgood := hT T (Nat.le_refl T)
  let transcript : PositiveSequenceOneQueryTranscript α :=
    ⟨T, (fun i => stream i,
      positiveSequenceOneQueryFeedback strategy L stream (T + 1))⟩
  refine ⟨transcript, ?_, ?_⟩
  · simpa [output, transcript] using hgood.1
  · simpa [output, transcript] using hgood.2

theorem positiveSequenceOneQuery_implies_countableInnerCover
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (h : PositiveSequenceOneQuerySetGeneratable targets) :
    HasCountableInnerCover targets := by
  obtain ⟨strategy, hstrategy⟩ := h
  exact
    ⟨countableInnerCoverOfPositiveSequenceOneQuery
      hinfinite strategy hstrategy⟩

/-! ## Sufficiency: one fair query per round -/

/-- The explicit square-shell schedule for cover-row/point-index pairs. -/
def oneQueryPairEnumeration : ℕ → ℕ × ℕ :=
  Nat.unpair

theorem oneQueryPairEnumeration_surjective :
    Function.Surjective oneQueryPairEnumeration :=
  Nat.surjective_unpair

@[simp] theorem oneQueryPairEnumeration_pair
    (row point : ℕ) :
    oneQueryPairEnumeration (Nat.pair row point) =
      (row, point) :=
  Nat.unpair_pair row point

/-- The pairing index lies in the first `(t+1)^2` micro-rounds exactly for
the `(t+1) × (t+1)` square of row/point coordinates. -/
theorem pair_lt_square_iff
    (row point t : ℕ) :
    Nat.pair row point < (t + 1) ^ 2 ↔
      row < t + 1 ∧ point < t + 1 := by
  constructor
  · intro hpair
    have hmaxSqLePair :
        max row point ^ 2 ≤ Nat.pair row point :=
      (Nat.le_add_right
        (max row point ^ 2) (min row point)).trans
          (Nat.max_sq_add_min_le_pair row point)
    have hmaxSq :
        max row point ^ 2 < (t + 1) ^ 2 :=
      hmaxSqLePair.trans_lt hpair
    have hmax : max row point < t + 1 := by
      exact Nat.mul_self_lt_mul_self_iff.mp
        (by simpa [Nat.pow_two] using hmaxSq)
    exact
      ⟨(le_max_left row point).trans_lt hmax,
        (le_max_right row point).trans_lt hmax⟩
  · rintro ⟨hrow, hpoint⟩
    have hmax : max row point < t + 1 :=
      (max_lt_iff.mpr ⟨hrow, hpoint⟩)
    calc
      Nat.pair row point <
          (max row point + 1) ^ 2 :=
        Nat.pair_lt_max_add_one_sq row point
      _ ≤ (t + 1) ^ 2 := by
        have hsucc : max row point + 1 ≤ t + 1 :=
          Nat.succ_le_iff.mpr hmax
        exact pow_le_pow_left' hsucc 2

/-- Every one-query micro-round before the square cutoff addresses a
coordinate of that square. -/
theorem oneQueryPairEnumeration_lt_of_lt_square
    {round t : ℕ}
    (hround : round < (t + 1) ^ 2) :
    (oneQueryPairEnumeration round).1 < t + 1 ∧
      (oneQueryPairEnumeration round).2 < t + 1 := by
  have hpair :
      Nat.pair (oneQueryPairEnumeration round).1
          (oneQueryPairEnumeration round).2 =
        round :=
    Nat.pair_unpair round
  apply (pair_lt_square_iff _ _ t).mp
  rwa [hpair]

/-- The first `(t+1)^2` one-query micro-rounds are in exact bijection with
the source square table: no coordinate is omitted or repeated. -/
def oneQuerySquareScheduleEquiv (t : ℕ) :
    Fin ((t + 1) ^ 2) ≃
      Fin (t + 1) × Fin (t + 1) where
  toFun round :=
    let h :=
      oneQueryPairEnumeration_lt_of_lt_square round.isLt
    (⟨(oneQueryPairEnumeration round).1, h.1⟩,
      ⟨(oneQueryPairEnumeration round).2, h.2⟩)
  invFun coordinate :=
    ⟨Nat.pair coordinate.1 coordinate.2,
      (pair_lt_square_iff coordinate.1 coordinate.2 t).mpr
        ⟨coordinate.1.isLt, coordinate.2.isLt⟩⟩
  left_inv round := by
    apply Fin.ext
    exact Nat.pair_unpair round
  right_inv coordinate := by
    apply Prod.ext <;> apply Fin.ext <;>
      simp [oneQueryPairEnumeration]

/-- Query the square table sequentially in the explicit one-query order. -/
def scheduledSquareQuery
    (strategy : PositiveSequenceSetQueryStrategy α)
    (t : ℕ) (xs : Fin t → α)
    (microRound : Fin ((t + 1) ^ 2)) : α :=
  let coordinate := oneQuerySquareScheduleEquiv t microRound
  strategy.query t xs coordinate.1 coordinate.2

/-- Truthful answers obtained by the sequential square schedule. -/
noncomputable def scheduledSquareTruthfulAnswers
    (strategy : PositiveSequenceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    Fin ((t + 1) ^ 2) → Bool :=
  fun microRound =>
    membershipAnswer target
      (scheduledSquareQuery strategy t
        (fun i => stream i) microRound)

/-- Reassemble a sequential square transcript into the two-dimensional
answer table expected by the batch strategy. -/
def scheduledSquareAnswerTable
    (t : ℕ)
    (answers : Fin ((t + 1) ^ 2) → Bool) :
    Fin (t + 1) → Fin (t + 1) → Bool :=
  fun row point =>
    answers ((oneQuerySquareScheduleEquiv t).symm (row, point))

/-- Sequentially asking the square coordinates gives exactly the batch
model's truthful answer table. -/
theorem scheduledSquareAnswerTable_truthful
    (strategy : PositiveSequenceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    scheduledSquareAnswerTable t
        (scheduledSquareTruthfulAnswers
          strategy target stream t) =
      positiveSequenceTruthfulQueryTable
        strategy target stream t := by
  funext row point
  change
    membershipAnswer target
        (strategy.query t (fun i => stream i)
          ((oneQuerySquareScheduleEquiv t)
            ((oneQuerySquareScheduleEquiv t).symm
              (row, point))).1
          ((oneQuerySquareScheduleEquiv t)
            ((oneQuerySquareScheduleEquiv t).symm
              (row, point))).2) =
      membershipAnswer target
        (strategy.query t (fun i => stream i) row point)
  rw [Equiv.apply_symm_apply]

/-- Hence a completed block of `(t+1)^2` one-query micro-rounds reproduces
the square strategy's round-`t` output exactly. -/
theorem scheduledSquare_output_eq
    (strategy : PositiveSequenceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    strategy.output t (fun i => stream i)
        (scheduledSquareAnswerTable t
          (scheduledSquareTruthfulAnswers
            strategy target stream t)) =
      positiveSequenceSetQueryOutput
        strategy target stream t := by
  rw [scheduledSquareAnswerTable_truthful]
  rfl

/-- The point scheduled for the unique query in one real round. -/
noncomputable def innerCoverOneQueryPoint
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (round : ℕ) : α :=
  let pair := oneQueryPairEnumeration round
  GenLimit.Support.infiniteEnumeration
    (inner.cover pair.1) (inner.infinite_cover pair.1) pair.2

theorem innerCoverOneQueryPoint_mem
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (round : ℕ) :
    innerCoverOneQueryPoint inner round ∈
      inner.cover (oneQueryPairEnumeration round).1 := by
  exact
    GenLimit.Support.infiniteEnumeration_mem
      (inner.cover (oneQueryPairEnumeration round).1)
      (inner.infinite_cover
        (oneQueryPairEnumeration round).1)
      (oneQueryPairEnumeration round).2

/-- Row `i` has received no negative answer among the transcript entries
available at real round `t`. -/
def OneQueryRowPasses
    (t : ℕ) (answers : List Bool) (i : ℕ) : Prop :=
  i < t + 1 ∧
    ∀ r, r < answers.length →
      (oneQueryPairEnumeration r).1 = i →
        answers[r]? = some true

noncomputable def firstPassingOneQueryRow
    (t : ℕ) (answers : List Bool) : ℕ := by
  classical
  exact if h : ∃ i, OneQueryRowPasses t answers i
    then Nat.find h
    else 0

theorem firstPassingOneQueryRow_spec
    {t : ℕ} {answers : List Bool}
    (hexists : ∃ i, OneQueryRowPasses t answers i) :
    OneQueryRowPasses t answers
      (firstPassingOneQueryRow t answers) := by
  classical
  simp only [firstPassingOneQueryRow, dif_pos hexists]
  exact Nat.find_spec hexists

theorem firstPassingOneQueryRow_le
    {t : ℕ} {answers : List Bool}
    (hexists : ∃ i, OneQueryRowPasses t answers i)
    {i : ℕ} (hi : OneQueryRowPasses t answers i) :
    firstPassingOneQueryRow t answers ≤ i := by
  classical
  simp only [firstPassingOneQueryRow, dif_pos hexists]
  exact Nat.find_min' hexists hi

/-- Test one fair row/point pair per round and output the least row not yet
refuted by the accumulated answers. -/
noncomputable def innerCoverOneQueryStrategy
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    PositiveSequenceOneQuerySetStrategy α where
  query := fun t _xs _history =>
    innerCoverOneQueryPoint inner t
  output := fun t _xs answers =>
    inner.cover (firstPassingOneQueryRow t answers)

/-- The independently recursive truthful transcript of the fair strategy is
the pointwise answer list for rounds `0,...,t-1`. -/
theorem innerCoverOneQueryFeedback_eq_map
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (L : Set α) (stream : Stream α) (t : ℕ) :
    positiveSequenceOneQueryFeedback
        (innerCoverOneQueryStrategy inner) L stream t =
      (List.range t).map fun r =>
        membershipAnswer L (innerCoverOneQueryPoint inner r) := by
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      rw [positiveSequenceOneQueryFeedback_succ, ih]
      simp [innerCoverOneQueryStrategy, List.range_succ]

theorem innerCoverOneQueryFeedback_get?
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (L : Set α) (stream : Stream α) (t : ℕ)
    (r : ℕ) (hr : r < t) :
    (positiveSequenceOneQueryFeedback
      (innerCoverOneQueryStrategy inner) L stream t)[r]? =
        some (membershipAnswer L
          (innerCoverOneQueryPoint inner r)) := by
  rw [innerCoverOneQueryFeedback_eq_map]
  simp [hr]

/-- A row passes the truthful one-query transcript exactly when every
scheduled query from that row so far was positive. -/
theorem innerCoverOneQuery_truthful_rowPasses_iff
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (L : Set α) (stream : Stream α) (t i : ℕ) :
    OneQueryRowPasses t
        (positiveSequenceOneQueryFeedback
          (innerCoverOneQueryStrategy inner) L stream (t + 1)) i ↔
      i < t + 1 ∧
        ∀ r, r < t + 1 →
          (oneQueryPairEnumeration r).1 = i →
            innerCoverOneQueryPoint inner r ∈ L := by
  constructor
  · rintro ⟨hi, hrow⟩
    refine ⟨hi, ?_⟩
    intro r hr hpair
    have hans := hrow r (by simpa using hr) hpair
    have hget :
        (positiveSequenceOneQueryFeedback
          (innerCoverOneQueryStrategy inner) L stream
            (t + 1))[r]? =
          some (membershipAnswer L
            (innerCoverOneQueryPoint inner r)) :=
      innerCoverOneQueryFeedback_get?
        inner L stream (t + 1) r hr
    rw [hget] at hans
    have hans' :
        membershipAnswer L
            (innerCoverOneQueryPoint inner r) =
          true :=
      Option.some.inj hans
    exact
      (membershipAnswer_eq_true_iff
        L (innerCoverOneQueryPoint inner r)).mp hans'
  · rintro ⟨hi, hrow⟩
    refine ⟨hi, ?_⟩
    intro r hr hpair
    have hr' : r < t + 1 := by
      simpa using hr
    have hmem := hrow r hr' hpair
    have hanswer :
        membershipAnswer L
            (innerCoverOneQueryPoint inner r) =
          true :=
      (membershipAnswer_eq_true_iff
        L (innerCoverOneQueryPoint inner r)).mpr hmem
    rw [innerCoverOneQueryFeedback_get?
      inner L stream (t + 1) r hr']
    exact congrArg some hanswer

/-- The fair one-query cover search eventually selects the least cover row
contained in the target.  This is public because the exact source-timed query
interface reuses the same search argument without reintroducing the old
pre-sample round. -/
theorem countableInnerCover_oneQuery_eventually
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (L : Set α) (stream : Stream α)
    (k : ℕ)
    (hgood : inner.cover k ⊆ L)
    (hminimal : ∀ i, i < k → ¬ inner.cover i ⊆ L) :
    ∃ T, ∀ t, T ≤ t →
      positiveSequenceOneQueryOutput
          (innerCoverOneQueryStrategy inner) L stream t =
        inner.cover k := by
  classical
  have hbadPointExists (i : Fin k) :
      ∃ n,
        GenLimit.Support.infiniteEnumeration
            (inner.cover i) (inner.infinite_cover i) n ∉ L := by
    obtain ⟨x, hxcover, hxL⟩ :=
      Set.not_subset.mp (hminimal i i.isLt)
    obtain ⟨n, hn⟩ :=
      GenLimit.Support.infiniteEnumeration_surjective
        (inner.cover i) (inner.infinite_cover i) hxcover
    exact ⟨n, by simpa [hn] using hxL⟩
  have hbadRoundExists (i : Fin k) :
      ∃ round,
        (oneQueryPairEnumeration round).1 = i ∧
          innerCoverOneQueryPoint inner round ∉ L := by
    obtain ⟨n, hn⟩ := hbadPointExists i
    obtain ⟨round, hround⟩ :=
      oneQueryPairEnumeration_surjective (i, n)
    refine ⟨round, ?_, ?_⟩
    · simp [hround]
    · simpa [innerCoverOneQueryPoint, hround] using hn
  let badRound : Fin k → ℕ :=
    fun i => Nat.find (hbadRoundExists i)
  have hbadPair (i : Fin k) :
      (oneQueryPairEnumeration (badRound i)).1 = i :=
    (Nat.find_spec (hbadRoundExists i)).1
  have hbadPoint (i : Fin k) :
      innerCoverOneQueryPoint inner (badRound i) ∉ L :=
    (Nat.find_spec (hbadRoundExists i)).2
  let budget : ℕ := ∑ i : Fin k, (badRound i + 1)
  let T := k + budget
  refine ⟨T, ?_⟩
  intro t hTt
  have hkt : k ≤ t :=
    le_trans (Nat.le_add_right k budget) hTt
  let answers :=
    positiveSequenceOneQueryFeedback
      (innerCoverOneQueryStrategy inner) L stream (t + 1)
  have hkPass : OneQueryRowPasses t answers k := by
    rw [innerCoverOneQuery_truthful_rowPasses_iff
      inner L stream t k]
    refine ⟨Nat.lt_succ_iff.mpr hkt, ?_⟩
    intro round _hround hrow
    exact hgood (by
      rw [← hrow]
      exact innerCoverOneQueryPoint_mem inner round)
  have hexists : ∃ i, OneQueryRowPasses t answers i :=
    ⟨k, hkPass⟩
  have hselected_le :
      firstPassingOneQueryRow t answers ≤ k :=
    firstPassingOneQueryRow_le hexists hkPass
  have hselected_not_lt :
      ¬ firstPassingOneQueryRow t answers < k := by
    intro hlt
    let i : Fin k :=
      ⟨firstPassingOneQueryRow t answers, hlt⟩
    have hibudget : badRound i + 1 ≤ budget := by
      dsimp only [budget]
      exact Finset.single_le_sum
        (f := fun j : Fin k => badRound j + 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hbadRound_lt_t : badRound i < t + 1 := by
      have hbad_lt_budget : badRound i < budget :=
        lt_of_lt_of_le
          (Nat.lt_succ_self (badRound i)) hibudget
      have hbudget_le_T : budget ≤ T :=
        Nat.le_add_left budget k
      exact lt_of_lt_of_le hbad_lt_budget
        (le_trans hbudget_le_T
          (le_trans hTt (Nat.le_succ t)))
    have hselectedPass :=
      firstPassingOneQueryRow_spec hexists
    have hselectedTruthful :=
      (innerCoverOneQuery_truthful_rowPasses_iff
        inner L stream t
          (firstPassingOneQueryRow t answers)).mp
        hselectedPass
    have hmember :
        innerCoverOneQueryPoint inner (badRound i) ∈ L :=
      hselectedTruthful.2 (badRound i) hbadRound_lt_t
        (by simpa [i] using hbadPair i)
    exact hbadPoint i hmember
  have hselected :
      firstPassingOneQueryRow t answers = k :=
    Nat.le_antisymm hselected_le
      (Nat.le_of_not_gt hselected_not_lt)
  change
    inner.cover
        (firstPassingOneQueryRow t
          (positiveSequenceOneQueryFeedback
            (innerCoverOneQueryStrategy inner)
            L stream (t + 1))) =
      inner.cover k
  exact congrArg inner.cover hselected

theorem countableInnerCover_implies_positiveSequenceOneQuery
    [Countable α]
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    PositiveSequenceOneQuerySetGeneratable targets := by
  classical
  let inner := Nonempty.some hinner
  refine ⟨innerCoverOneQueryStrategy inner, ?_⟩
  intro L hL stream _hPresents
  let hexists : ∃ i, inner.cover i ⊆ L :=
    inner.contained L hL
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
  rw [hT t ht]
  exact ⟨inner.infinite_cover k, hgood⟩

/-- The auxiliary semantic characterization remains true when only one
membership query is permitted per round.  Source Theorem 3.4, including its
timing, global-infinitude, and freshness clauses, is stated separately in
`SourceQuery.lean`. -/
theorem positiveSequenceOneQuery_characterization
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    PositiveSequenceOneQuerySetGeneratable targets ↔
      HasCountableInnerCover targets :=
  ⟨positiveSequenceOneQuery_implies_countableInnerCover hinfinite,
    countableInnerCover_implies_positiveSequenceOneQuery⟩

/-- At the semantic eventual-generation level, the auxiliary square-batch and
pre-sample one-query models have the same power.  The conversion goes through
the proved countable-inner-cover characterization; it is not a
runtime-preserving compiler or the source interaction itself. -/
theorem positiveSequenceOneQuery_iff_squareQuery
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    PositiveSequenceOneQuerySetGeneratable targets ↔
      PositiveSequenceSetQueryGeneratable targets := by
  rw [positiveSequenceOneQuery_characterization targets hinfinite,
    positiveSequenceSetQuery_characterization targets hinfinite]

end GenLimit.FeedbackQueries
