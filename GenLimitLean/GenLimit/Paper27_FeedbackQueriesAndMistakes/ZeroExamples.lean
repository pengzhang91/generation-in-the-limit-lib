import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceSetMistake
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceQuery

/-!
# Paper 27: generation with zero examples

This module formalizes Corollary 3.7 and Appendix Corollaries A.4--A.5.  The
interfaces below literally remove the adversary's positive-example input:
the element generator sees only earlier mistake bits, while the set generator
sees only earlier/current membership-query answers.

The constructions are semantic and classical.  They make no computability or
running-time claim.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-! ## Zero-example element generation with mistake feedback -/

/-- An element generator whose only input is the preceding mistake-bit
transcript. -/
abbrev ZeroExampleElementMistakeStrategy (α : Type*) :=
  List Bool → α

/-- The truthful zero-example feedback transcript before round `t`. -/
noncomputable def zeroExampleMistakeFeedback
    (strategy : ZeroExampleElementMistakeStrategy α)
    (target : Set α) : ℕ → List Bool
  | 0 => []
  | t + 1 =>
      let history := zeroExampleMistakeFeedback strategy target t
      history ++ [membershipAnswer target (strategy history)]

@[simp] theorem zeroExampleMistakeFeedback_zero
    (strategy : ZeroExampleElementMistakeStrategy α)
    (target : Set α) :
    zeroExampleMistakeFeedback strategy target 0 = [] :=
  rfl

@[simp] theorem zeroExampleMistakeFeedback_succ
    (strategy : ZeroExampleElementMistakeStrategy α)
    (target : Set α) (t : ℕ) :
    zeroExampleMistakeFeedback strategy target (t + 1) =
      zeroExampleMistakeFeedback strategy target t ++
        [membershipAnswer target
          (strategy (zeroExampleMistakeFeedback strategy target t))] :=
  rfl

@[simp] theorem zeroExampleMistakeFeedback_length
    (strategy : ZeroExampleElementMistakeStrategy α)
    (target : Set α) (t : ℕ) :
    (zeroExampleMistakeFeedback strategy target t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [ih]

/-- The element emitted in zero-example round `t`. -/
noncomputable def zeroExampleMistakeOutput
    (strategy : ZeroExampleElementMistakeStrategy α)
    (target : Set α) (t : ℕ) : α :=
  strategy (zeroExampleMistakeFeedback strategy target t)

/-- Eventual correctness when `Sₙ = ∅` at every round. -/
def ZeroExampleElementMistakeSucceedsOn
    (strategy : ZeroExampleElementMistakeStrategy α)
    (target : Set α) : Prop :=
  ∃ T, ∀ t, T ≤ t → zeroExampleMistakeOutput strategy target t ∈ target

def ZeroExampleElementMistakeGenerates
    (strategy : ZeroExampleElementMistakeStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → ZeroExampleElementMistakeSucceedsOn strategy L

def ZeroExampleElementMistakeGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : ZeroExampleElementMistakeStrategy α,
    ZeroExampleElementMistakeGenerates strategy targets

/-- Test the first canonical member of the active inner-cover row.  Repeating
an output is permitted because the zero-example freshness set is empty. -/
noncomputable def innerCoverZeroExampleMistakeStrategy
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    ZeroExampleElementMistakeStrategy α :=
  fun bits =>
    GenLimit.Support.infiniteEnumeration
      (inner.cover (bits.count false))
      (inner.infinite_cover (bits.count false)) 0

/-- The active row is the number of negative replies seen so far. -/
noncomputable def zeroExampleMistakePhase
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (t : ℕ) : ℕ :=
  (zeroExampleMistakeFeedback
    (innerCoverZeroExampleMistakeStrategy inner) target t).count false

@[simp] theorem zeroExampleMistakePhase_zero
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) :
    zeroExampleMistakePhase inner target 0 = 0 := by
  simp [zeroExampleMistakePhase]

theorem zeroExampleMistakePhase_succ
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (t : ℕ) :
    zeroExampleMistakePhase inner target (t + 1) =
      zeroExampleMistakePhase inner target t +
        [membershipAnswer target
          (GenLimit.Support.infiniteEnumeration
            (inner.cover (zeroExampleMistakePhase inner target t))
            (inner.infinite_cover
              (zeroExampleMistakePhase inner target t)) 0)].count false := by
  simp [zeroExampleMistakePhase, innerCoverZeroExampleMistakeStrategy,
    List.count_append]

/-- The active phase reaches the least row whose first canonical member is in
the target, then remains there. -/
theorem zeroExampleMistakePhase_eq_min
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α)
    (m : ℕ)
    (hgood :
      GenLimit.Support.infiniteEnumeration
        (inner.cover m) (inner.infinite_cover m) 0 ∈ target)
    (hminimal :
      ∀ i, i < m →
        GenLimit.Support.infiniteEnumeration
          (inner.cover i) (inner.infinite_cover i) 0 ∉ target) :
    ∀ t, zeroExampleMistakePhase inner target t = min t m := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      rw [zeroExampleMistakePhase_succ, ih]
      by_cases htm : t < m
      · have hfalse :
          membershipAnswer target
              (GenLimit.Support.infiniteEnumeration
                (inner.cover (min t m))
                (inner.infinite_cover (min t m)) 0) = false := by
          rw [Nat.min_eq_left (Nat.le_of_lt htm)]
          apply Bool.eq_false_iff.mpr
          exact fun htrue =>
            hminimal t htm
              ((membershipAnswer_eq_true_iff _ _).mp htrue)
        rw [hfalse]
        simp [Nat.min_eq_left (Nat.le_of_lt htm),
          Nat.min_eq_left (Nat.succ_le_iff.mpr htm)]
      · have hmt : m ≤ t := Nat.le_of_not_gt htm
        have htrue :
          membershipAnswer target
              (GenLimit.Support.infiniteEnumeration
                (inner.cover (min t m))
                (inner.infinite_cover (min t m)) 0) = true := by
          rw [Nat.min_eq_right hmt]
          exact (membershipAnswer_eq_true_iff _ _).mpr hgood
        rw [htrue]
        simp [Nat.min_eq_right hmt,
          Nat.min_eq_right (hmt.trans (Nat.le_succ t))]

/-- A countable inner cover yields a zero-example mistake-feedback
generator. -/
theorem countableInnerCover_implies_zeroExampleMistake
    [Countable α]
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    ZeroExampleElementMistakeGeneratable targets := by
  classical
  let inner := hinner.some
  refine ⟨innerCoverZeroExampleMistakeStrategy inner, ?_⟩
  intro L hL
  let hexists : ∃ i,
      GenLimit.Support.infiniteEnumeration
        (inner.cover i) (inner.infinite_cover i) 0 ∈ L := by
    obtain ⟨i, hi⟩ := inner.contained L hL
    exact
      ⟨i, hi (GenLimit.Support.infiniteEnumeration_mem
        (inner.cover i) (inner.infinite_cover i) 0)⟩
  let m := Nat.find hexists
  have hgood :
      GenLimit.Support.infiniteEnumeration
        (inner.cover m) (inner.infinite_cover m) 0 ∈ L :=
    Nat.find_spec hexists
  have hminimal : ∀ i, i < m →
      GenLimit.Support.infiniteEnumeration
        (inner.cover i) (inner.infinite_cover i) 0 ∉ L := by
    intro i hi hmem
    exact Nat.find_min hexists hi hmem
  refine ⟨m, ?_⟩
  intro t hmt
  change
    GenLimit.Support.infiniteEnumeration
        (inner.cover (zeroExampleMistakePhase inner L t))
        (inner.infinite_cover (zeroExampleMistakePhase inner L t)) 0 ∈ L
  rw [zeroExampleMistakePhase_eq_min inner L m hgood hminimal t,
    Nat.min_eq_right hmt]
  exact hgood

/-- Appendix Corollary A.4: ordinary source-faithful mistake-feedback
generability implies zero-example mistake-feedback generability. -/
theorem corollary_A_4_zeroExamples_mistake
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (hgenerate : SourceElementMistakeGeneratable targets) :
    ZeroExampleElementMistakeGeneratable targets :=
  countableInnerCover_implies_zeroExampleMistake
    ((theorem_3_1_elementMistake_characterization
      targets hinfinite).mp hgenerate)

/-! ## Zero-example set generation with query feedback -/

/-- A one-query set generator with no positive-example input.  `output`
receives the current round's answer as the final entry of its transcript. -/
structure ZeroExampleSetQueryStrategy (α : Type*) where
  query : ∀ (_t : ℕ), List Bool → α
  output : ∀ (_t : ℕ), List Bool → Set α
  output_infinite : ∀ (t : ℕ) (answers : List Bool),
    answers.length = t + 1 → (output t answers).Infinite

/-- Truthful query answers before round `t`. -/
noncomputable def zeroExampleQueryFeedback
    (strategy : ZeroExampleSetQueryStrategy α)
    (target : Set α) : ℕ → List Bool
  | 0 => []
  | t + 1 =>
      let history := zeroExampleQueryFeedback strategy target t
      history ++
        [membershipAnswer target (strategy.query t history)]

@[simp] theorem zeroExampleQueryFeedback_zero
    (strategy : ZeroExampleSetQueryStrategy α)
    (target : Set α) :
    zeroExampleQueryFeedback strategy target 0 = [] :=
  rfl

@[simp] theorem zeroExampleQueryFeedback_succ
    (strategy : ZeroExampleSetQueryStrategy α)
    (target : Set α) (t : ℕ) :
    zeroExampleQueryFeedback strategy target (t + 1) =
      zeroExampleQueryFeedback strategy target t ++
        [membershipAnswer target
          (strategy.query t
            (zeroExampleQueryFeedback strategy target t))] :=
  rfl

@[simp] theorem zeroExampleQueryFeedback_length
    (strategy : ZeroExampleSetQueryStrategy α)
    (target : Set α) (t : ℕ) :
    (zeroExampleQueryFeedback strategy target t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [ih]

noncomputable def zeroExampleQueryOutput
    (strategy : ZeroExampleSetQueryStrategy α)
    (target : Set α) (t : ℕ) : Set α :=
  strategy.output t (zeroExampleQueryFeedback strategy target (t + 1))

theorem zeroExampleQueryOutput_infinite
    (strategy : ZeroExampleSetQueryStrategy α)
    (target : Set α) (t : ℕ) :
    (zeroExampleQueryOutput strategy target t).Infinite :=
  strategy.output_infinite t _
    (zeroExampleQueryFeedback_length strategy target (t + 1))

def ZeroExampleSetQuerySucceedsOn
    (strategy : ZeroExampleSetQueryStrategy α)
    (target : Set α) : Prop :=
  ∃ T, ∀ t, T ≤ t → zeroExampleQueryOutput strategy target t ⊆ target

def ZeroExampleSetQueryGenerates
    (strategy : ZeroExampleSetQueryStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → ZeroExampleSetQuerySucceedsOn strategy L

def ZeroExampleSetQueryGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : ZeroExampleSetQueryStrategy α,
    ZeroExampleSetQueryGenerates strategy targets

/-- The already checked fair one-query cover search with its unused positive
sequence argument erased. -/
noncomputable def innerCoverZeroExampleQueryStrategy
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    ZeroExampleSetQueryStrategy α where
  query := fun t _answers => innerCoverOneQueryPoint inner t
  output := fun t answers =>
    inner.cover (firstPassingOneQueryRow t answers)
  output_infinite := by
    intro t answers _hanswers
    exact inner.infinite_cover (firstPassingOneQueryRow t answers)

/-- Erasing the unused positive sequence does not change the fair scheduler's
truthful transcript. -/
theorem innerCoverZeroExampleQueryFeedback_eq
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    zeroExampleQueryFeedback
        (innerCoverZeroExampleQueryStrategy inner) target t =
      positiveSequenceOneQueryFeedback
        (innerCoverOneQueryStrategy inner) target stream t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [zeroExampleQueryFeedback_succ,
        positiveSequenceOneQueryFeedback_succ, ih]
      rfl

theorem innerCoverZeroExampleQueryOutput_eq
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    zeroExampleQueryOutput
        (innerCoverZeroExampleQueryStrategy inner) target t =
      positiveSequenceOneQueryOutput
        (innerCoverOneQueryStrategy inner) target stream t := by
  unfold zeroExampleQueryOutput positiveSequenceOneQueryOutput
  change
    inner.cover
        (firstPassingOneQueryRow t
          (zeroExampleQueryFeedback
            (innerCoverZeroExampleQueryStrategy inner)
            target (t + 1))) =
      inner.cover
        (firstPassingOneQueryRow t
          (positiveSequenceOneQueryFeedback
            (innerCoverOneQueryStrategy inner)
            target stream (t + 1)))
  rw [innerCoverZeroExampleQueryFeedback_eq]

/-- A countable inner cover yields a zero-example one-query set generator. -/
theorem countableInnerCover_implies_zeroExampleQuery
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    ZeroExampleSetQueryGeneratable targets := by
  classical
  let inner := hinner.some
  let stream : Stream α :=
    GenLimit.Support.infiniteEnumeration Set.univ Set.infinite_univ
  refine ⟨innerCoverZeroExampleQueryStrategy inner, ?_⟩
  intro L hL
  let hexists : ∃ i, inner.cover i ⊆ L := inner.contained L hL
  let k := Nat.find hexists
  have hgood : inner.cover k ⊆ L := Nat.find_spec hexists
  have hminimal : ∀ i, i < k → ¬inner.cover i ⊆ L := by
    intro i hi
    exact Nat.find_min hexists hi
  obtain ⟨T, hT⟩ :=
    countableInnerCover_oneQuery_eventually
      inner L stream k hgood hminimal
  refine ⟨T, ?_⟩
  intro t ht
  rw [innerCoverZeroExampleQueryOutput_eq inner L stream,
    hT t ht]
  exact hgood

/-- Appendix Corollary A.5: ordinary source-timed set-query generability
implies zero-example set-query generability. -/
theorem corollary_A_5_zeroExamples_query
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (hgenerate : SourceSetQueryGeneratable targets) :
    ZeroExampleSetQueryGeneratable targets :=
  countableInnerCover_implies_zeroExampleQuery
    ((theorem_3_4_sourceSetQuery_characterization
      targets hinfinite).mp hgenerate)

end GenLimit.FeedbackQueries
