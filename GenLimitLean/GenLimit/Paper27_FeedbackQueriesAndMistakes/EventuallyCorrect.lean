import GenLimit.Paper27_FeedbackQueriesAndMistakes.CountableUnion
import GenLimit.Paper27_FeedbackQueriesAndMistakes.ZeroExamples

/-!
# Paper 27: eventually correct feedback

This module formalizes Definitions 5--7, Theorems A.6--A.7, and Corollary
3.8.  An adversary supplies an arbitrary Boolean stream, subject only to the
requirement that from some round onward each bit equals the correct bit for
the interaction that the observed prefix itself induces.  The positive
example stream is unrestricted; generators use it only to satisfy the source
freshness condition.

The checked constructions use an infinitely repeated inner cover.  Repetition
is harmless for Definition 4 and ensures that a finite prefix of false
feedback cannot permanently skip every good cover row.  In the query model,
all queried points are removed from the current output, so a falsely accepted
early counterexample cannot remain in later generated sets.  This is a
semantic/classical robustification of the paper's finite-expansion proof; no
machine-level or runtime equivalence is claimed.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-! ## Shared cover and stabilization utilities -/

/-- Repeat every row of a countable inner cover infinitely often. -/
def CountableInnerCover.repeat
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    CountableInnerCover targets where
  cover := fun n => inner.cover (Nat.unpair n).1
  infinite_cover := fun n => inner.infinite_cover (Nat.unpair n).1
  contained := by
    intro L hL
    obtain ⟨i, hi⟩ := inner.contained L hL
    refine ⟨Nat.pair i 0, ?_⟩
    have hfst : (Nat.unpair (Nat.pair i 0)).1 = i := by
      exact congrArg Prod.fst (Nat.unpair_pair i 0)
    rw [hfst]
    exact hi

theorem CountableInnerCover.repeat_cover_pair
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) (i copy : ℕ) :
    inner.repeat.cover (Nat.pair i copy) = inner.cover i := by
  have hfst : (Nat.unpair (Nat.pair i copy)).1 = i := by
    exact congrArg Prod.fst (Nat.unpair_pair i copy)
  exact congrArg inner.cover hfst

/-- A monotone natural-number sequence that is bounded from some point onward
eventually becomes constant. -/
theorem monotone_bounded_nat_eventually_constant
    (a : ℕ → ℕ) (N k : ℕ)
    (hmono : Monotone a)
    (hbound : ∀ t, N ≤ t → a t ≤ k) :
    ∃ T, N ≤ T ∧ ∀ t, T ≤ t → a t = a T := by
  classical
  let reached : Finset ℕ :=
    (Finset.range (k + 1)).filter fun i => ∃ t, N ≤ t ∧ a t = i
  have hnonempty : reached.Nonempty := by
    refine ⟨a N, ?_⟩
    simp only [reached, Finset.mem_filter, Finset.mem_range]
    exact
      ⟨Nat.lt_succ_iff.mpr (hbound N (Nat.le_refl N)),
        ⟨N, Nat.le_refl N, rfl⟩⟩
  let m := reached.max' hnonempty
  have hm : m ∈ reached := reached.max'_mem hnonempty
  obtain ⟨T, hNT, hTm⟩ : ∃ T, N ≤ T ∧ a T = m := by
    simpa [reached] using (Finset.mem_filter.mp hm).2
  refine ⟨T, hNT, ?_⟩
  intro t hTt
  have htMem : a t ∈ reached := by
    simp only [reached, Finset.mem_filter, Finset.mem_range]
    exact
      ⟨Nat.lt_succ_iff.mpr (hbound t (hNT.trans hTt)),
        ⟨t, hNT.trans hTt, rfl⟩⟩
  apply Nat.le_antisymm
  · simpa [hTm] using reached.le_max' (a t) htMem
  · simpa [hTm] using hmono hTt

/-! ## Definition 6: eventually correct mistake feedback -/

/-- The element emitted in zero-based round `t`, after `t+1` arbitrary
examples and the first `t` observed feedback bits. -/
noncomputable def eventuallyCorrectMistakeOutput
    (strategy : SourceElementMistakeStrategy α)
    (samples : Stream α) (observed : Stream Bool) (t : ℕ) : α :=
  strategy (streamPrefix samples (t + 1)) (streamPrefix observed t)

/-- The feedback stream is eventually correct for the interaction induced by
its own observed prefixes. -/
def EventuallyCorrectMistakeFeedback
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (samples : Stream α)
    (observed : Stream Bool) : Prop :=
  ∃ N, ∀ t, N ≤ t →
    observed t =
      sourceElementReply target (streamPrefix samples (t + 1))
        (eventuallyCorrectMistakeOutput strategy samples observed t)

/-- Eventual element correctness against one eventually-correct feedback
stream.  No presentation condition is placed on `samples`. -/
def EventuallyCorrectMistakeSucceedsOn
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (samples : Stream α)
    (observed : Stream Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    eventuallyCorrectMistakeOutput strategy samples observed t ∈ target ∧
      eventuallyCorrectMistakeOutput strategy samples observed t ∉
        streamPrefix samples (t + 1)

def EventuallyCorrectMistakeGenerates
    (strategy : SourceElementMistakeStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → ∀ samples observed,
    EventuallyCorrectMistakeFeedback strategy L samples observed →
      EventuallyCorrectMistakeSucceedsOn strategy L samples observed

def EventuallyCorrectMistakeGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : SourceElementMistakeStrategy α,
    EventuallyCorrectMistakeGenerates strategy targets

/-- The active repeated-cover row under the observed transcript. -/
def eventuallyCorrectMistakePhase
    (observed : Stream Bool) (t : ℕ) : ℕ :=
  (streamPrefix observed t).count false

@[simp] theorem eventuallyCorrectMistakePhase_zero
    (observed : Stream Bool) :
    eventuallyCorrectMistakePhase observed 0 = 0 := by
  simp [eventuallyCorrectMistakePhase, streamPrefix]

theorem eventuallyCorrectMistakePhase_succ
    (observed : Stream Bool) (t : ℕ) :
    eventuallyCorrectMistakePhase observed (t + 1) =
      eventuallyCorrectMistakePhase observed t +
        [observed t].count false := by
  simp [eventuallyCorrectMistakePhase, source_streamPrefix_succ,
    List.count_append]

theorem eventuallyCorrectMistakePhase_mono
    (observed : Stream Bool) :
    Monotone (eventuallyCorrectMistakePhase observed) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [eventuallyCorrectMistakePhase_succ]
  omega

theorem eventuallyCorrectMistakePhase_step_le
    (observed : Stream Bool) (t : ℕ) :
    eventuallyCorrectMistakePhase observed (t + 1) ≤
      eventuallyCorrectMistakePhase observed t + 1 := by
  rw [eventuallyCorrectMistakePhase_succ]
  cases observed t <;> simp

/-- The repeated-cover strategy's external-interaction output has the usual
cover-membership and freshness invariants. -/
theorem repeatedInnerCoverMistakeOutput_mem
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (samples : Stream α) (observed : Stream Bool) (t : ℕ) :
    eventuallyCorrectMistakeOutput
        (innerCoverSourceElementStrategy inner.repeat)
        samples observed t ∈
      inner.repeat.cover (eventuallyCorrectMistakePhase observed t) \
        ((Generic.sequenceSample
          (streamPrefix samples (t + 1)).get : Finset α) : Set α) := by
  simpa [eventuallyCorrectMistakeOutput,
    eventuallyCorrectMistakePhase] using
      innerCoverSourceElementStrategy_mem inner.repeat
        (streamPrefix samples (t + 1)) (streamPrefix observed t)

/-- Repetition makes the cover search robust to a finite prefix of corrupted
mistake bits. -/
theorem repeatedInnerCover_mistake_eventuallyCorrect
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    EventuallyCorrectMistakeGenerates
      (innerCoverSourceElementStrategy inner.repeat) targets := by
  classical
  intro L hL samples observed hcorrect
  obtain ⟨N, hN⟩ := hcorrect
  obtain ⟨base, hbase⟩ := inner.contained L hL
  let start := eventuallyCorrectMistakePhase observed N
  let k := Nat.pair base start
  have hstart : start ≤ k := by
    exact Nat.right_le_pair base start
  have hgood : inner.repeat.cover k ⊆ L := by
    rw [CountableInnerCover.repeat_cover_pair]
    exact hbase
  have hbound : ∀ t, N ≤ t →
      eventuallyCorrectMistakePhase observed t ≤ k := by
    intro t hNt
    induction t, hNt using Nat.le_induction with
    | base => exact hstart
    | succ t hNt ih =>
        by_cases hphase :
            eventuallyCorrectMistakePhase observed t = k
        · have hout :=
            repeatedInnerCoverMistakeOutput_mem
              inner samples observed t
          rw [hphase] at hout
          have hreply :
              sourceElementReply L (streamPrefix samples (t + 1))
                  (eventuallyCorrectMistakeOutput
                    (innerCoverSourceElementStrategy inner.repeat)
                    samples observed t) = true := by
            rw [sourceElementReply_eq_true_iff]
            refine ⟨hgood hout.1, ?_⟩
            intro hmem
            exact hout.2
              (source_mem_sequenceSample_list_get_iff.mpr hmem)
          have hobserved : observed t = true := by
            rw [hN t hNt, hreply]
          rw [eventuallyCorrectMistakePhase_succ, hobserved, hphase]
          simp
        · have hlt :
              eventuallyCorrectMistakePhase observed t < k :=
            lt_of_le_of_ne ih hphase
          exact
            (eventuallyCorrectMistakePhase_step_le observed t).trans
              (Nat.succ_le_iff.mpr hlt)
  obtain ⟨T, hNT, hstable⟩ :=
    monotone_bounded_nat_eventually_constant
      (eventuallyCorrectMistakePhase observed) N k
      (eventuallyCorrectMistakePhase_mono observed) hbound
  refine ⟨T, ?_⟩
  intro t hTt
  have hNt : N ≤ t := hNT.trans hTt
  have hphase := hstable t hTt
  have hphaseSucc := hstable (t + 1) (hTt.trans (Nat.le_succ t))
  have hobserved : observed t = true := by
    cases hbit : observed t with
    | false =>
        have hstep := eventuallyCorrectMistakePhase_succ observed t
        rw [hbit, hphase, hphaseSucc] at hstep
        simp at hstep
    | true => rfl
  have hreply := hN t hNt
  rw [hobserved] at hreply
  have hreplyTrue :
      sourceElementReply L (streamPrefix samples (t + 1))
          (eventuallyCorrectMistakeOutput
            (innerCoverSourceElementStrategy inner.repeat)
            samples observed t) = true :=
    hreply.symm
  exact (sourceElementReply_eq_true_iff _ _ _).mp hreplyTrue

/-- A countable inner cover suffices under eventually correct mistake
feedback, even with an arbitrary example stream. -/
theorem countableInnerCover_implies_eventuallyCorrectMistake
    [Countable α]
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    EventuallyCorrectMistakeGeneratable targets := by
  classical
  let inner := hinner.some
  exact
    ⟨innerCoverSourceElementStrategy inner.repeat,
      repeatedInnerCover_mistake_eventuallyCorrect inner⟩

/-! ### Reduction of the robust model to the noiseless source interaction -/

/-- The next truthful bit in the ordinary source interaction. -/
noncomputable def sourceTruthfulMistakeBit
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : Bool :=
  sourceElementReply target (streamPrefix stream (t + 1))
    (sourceElementOutput strategy target
      (streamPrefix stream (t + 1)))

/-- Prefixes of the truthful bit stream are exactly the recursively replayed
source transcript. -/
theorem sourceTruthfulMistakeBit_prefix
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    streamPrefix (sourceTruthfulMistakeBit strategy target stream) t =
      sourceElementFeedback strategy target
        (streamPrefix stream (t + 1)) := by
  induction t with
  | zero =>
      rw [show streamPrefix stream 1 = [stream 0] by
        simpa [streamPrefix] using source_streamPrefix_succ stream 0]
      simp [sourceElementFeedback, sourceElementFeedbackRun,
        sourceElementFeedbackStep]
  | succ t ih =>
      rw [source_streamPrefix_succ,
        show t + 1 + 1 = (t + 1) + 1 by omega,
        source_streamPrefix_succ,
        sourceElementFeedback_append, ih]
      · rfl
      · exact List.ne_nil_of_length_pos (by simp [streamPrefix])

theorem eventuallyCorrectMistakeOutput_truthful
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    eventuallyCorrectMistakeOutput strategy stream
        (sourceTruthfulMistakeBit strategy target stream) t =
      sourceElementOutput strategy target
        (streamPrefix stream (t + 1)) := by
  simp [eventuallyCorrectMistakeOutput, sourceElementOutput,
    sourceTruthfulMistakeBit_prefix]

/-- The robust premise includes the noiseless source interaction as the
special case in which every bit is correct from round zero. -/
theorem eventuallyCorrectMistake_implies_sourceMistake
    {targets : LanguageClass α}
    (hgenerate : EventuallyCorrectMistakeGeneratable targets) :
    SourceElementMistakeGeneratable targets := by
  classical
  obtain ⟨strategy, hstrategy⟩ := hgenerate
  refine ⟨strategy, ?_⟩
  intro L hL stream _hPresents
  let observed := sourceTruthfulMistakeBit strategy L stream
  have heventual :
      EventuallyCorrectMistakeFeedback strategy L stream observed := by
    refine ⟨0, ?_⟩
    intro t _ht
    simp [observed, sourceTruthfulMistakeBit,
      eventuallyCorrectMistakeOutput_truthful]
  obtain ⟨T, hT⟩ := hstrategy L hL stream observed heventual
  refine ⟨T + 1, ?_⟩
  intro t hTt
  have htpos : 0 < t := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt htpos)
  have hTr : T ≤ r := by omega
  have hout := hT r hTr
  rw [eventuallyCorrectMistakeOutput_truthful] at hout
  exact hout

/-- Appendix Theorem A.6. -/
theorem theorem_A_6_eventuallyCorrectMistake_characterization
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    EventuallyCorrectMistakeGeneratable targets ↔
      HasCountableInnerCover targets :=
  ⟨fun h =>
      (theorem_3_1_elementMistake_characterization
        targets hinfinite).mp
        (eventuallyCorrectMistake_implies_sourceMistake h),
    countableInnerCover_implies_eventuallyCorrectMistake⟩

/-! ## Definition 7: eventually correct query feedback -/

/-- The set emitted in source round `t`, using `t+1` arbitrary examples and
the first `t+1` observed answers (including the current answer). -/
noncomputable def eventuallyCorrectQueryOutput
    (strategy : SourceSetQueryStrategy α)
    (samples : Stream α) (observed : Stream Bool) (t : ℕ) : Set α :=
  strategy.output t (fun i => samples i) (streamPrefix observed (t + 1))

/-- The observed query-answer stream is eventually correct for the queries
selected from its own preceding prefixes. -/
def EventuallyCorrectQueryFeedback
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (samples : Stream α)
    (observed : Stream Bool) : Prop :=
  ∃ N, ∀ t, N ≤ t →
    observed t =
      membershipAnswer target
        (strategy.query t (fun i => samples i)
          (streamPrefix observed t))

def EventuallyCorrectQuerySucceedsOn
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (samples : Stream α)
    (observed : Stream Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    eventuallyCorrectQueryOutput strategy samples observed t ⊆
      target \ (Generic.sample samples (t + 1) : Set α)

def EventuallyCorrectQueryGenerates
    (strategy : SourceSetQueryStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → ∀ samples observed,
    EventuallyCorrectQueryFeedback strategy L samples observed →
      EventuallyCorrectQuerySucceedsOn strategy L samples observed

def EventuallyCorrectQueryGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : SourceSetQueryStrategy α,
    EventuallyCorrectQueryGenerates strategy targets

/-- The finite set of all points queried through round `t`. -/
noncomputable def queriedInnerCoverPoints
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) (t : ℕ) : Finset α := by
  classical
  exact
    (Finset.range (t + 1)).image fun r =>
      innerCoverOneQueryPoint inner r

theorem innerCoverOneQueryPoint_mem_queried
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    {r t : ℕ} (hrt : r < t + 1) :
    innerCoverOneQueryPoint inner r ∈
      queriedInnerCoverPoints inner t := by
  classical
  rw [queriedInnerCoverPoints, Finset.mem_image]
  exact ⟨r, Finset.mem_range.mpr hrt, rfl⟩

/-- Fair one-query search on a repeated cover.  Removing every queried point
prevents an early false-positive answer from leaving a bad point in a later
set output. -/
noncomputable def eventuallyCorrectInnerCoverQueryStrategy
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    SourceSetQueryStrategy α := by
  classical
  exact
    { query := fun t _samples _answers =>
        innerCoverOneQueryPoint inner.repeat t
      output := fun t samples answers =>
        inner.repeat.cover (firstPassingOneQueryRow t answers) \
          (((sequenceSample samples : Finset α) ∪
            queriedInnerCoverPoints inner.repeat t : Finset α) : Set α)
      output_infinite := by
        intro t samples answers _hanswers
        exact
          (inner.repeat.infinite_cover
            (firstPassingOneQueryRow t answers)).diff
            ((sequenceSample samples : Finset α) ∪
              queriedInnerCoverPoints inner.repeat t).finite_toSet }

/-- Output membership exposes the selected cover row and both freshness
conditions. -/
theorem eventuallyCorrectInnerCoverQueryOutput_mem
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (samples : Stream α) (observed : Stream Bool)
    (t : ℕ) {x : α}
    (hx : x ∈ eventuallyCorrectQueryOutput
      (eventuallyCorrectInnerCoverQueryStrategy inner)
      samples observed t) :
    x ∈ inner.repeat.cover
        (firstPassingOneQueryRow t
          (streamPrefix observed (t + 1))) ∧
      x ∉ (Generic.sample samples (t + 1) : Set α) ∧
      x ∉ (queriedInnerCoverPoints inner.repeat t : Set α) := by
  classical
  change x ∈
    inner.repeat.cover
        (firstPassingOneQueryRow t
          (streamPrefix observed (t + 1))) \
      (((sequenceSample (fun i : Fin (t + 1) => samples i) : Finset α) ∪
        queriedInnerCoverPoints inner.repeat t : Finset α) : Set α) at hx
  have hsample :
      sequenceSample (fun i : Fin (t + 1) => samples i) =
        Generic.sample samples (t + 1) :=
    sequenceSample_prefix samples (t + 1)
  rw [hsample] at hx
  simpa only [Set.mem_diff, Finset.coe_union, Set.mem_union,
    Finset.mem_coe, not_or] using hx

/-- Lookup in an ordered stream prefix. -/
theorem streamPrefix_get?_eq_some
    (stream : Stream α) {r t : ℕ} (hrt : r < t) :
    (streamPrefix stream t)[r]? = some (stream r) := by
  simp [streamPrefix, GenLimit.textPrefix, hrt]

/-- A post-corruption negative witness for one repeated cover row. -/
def HasPostCorruptionCounterexample
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (N i : ℕ) : Prop :=
  ∃ r, N ≤ r ∧
    (oneQueryPairEnumeration r).1 = i ∧
    innerCoverOneQueryPoint inner r ∉ target

noncomputable def postCorruptionBadRound
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (N i : ℕ) : ℕ := by
  classical
  exact if h : HasPostCorruptionCounterexample inner target N i
    then Nat.find h
    else 0

theorem postCorruptionBadRound_spec
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (N i : ℕ)
    (h : HasPostCorruptionCounterexample inner target N i) :
    N ≤ postCorruptionBadRound inner target N i ∧
      (oneQueryPairEnumeration
        (postCorruptionBadRound inner target N i)).1 = i ∧
      innerCoverOneQueryPoint inner
        (postCorruptionBadRound inner target N i) ∉ target := by
  classical
  simp only [postCorruptionBadRound, dif_pos h]
  exact Nat.find_spec h

/-- The repeated fair cover search succeeds for every eventually correct
query-answer stream and every (possibly corrupted) example stream. -/
theorem repeatedInnerCover_query_eventuallyCorrect
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    EventuallyCorrectQueryGenerates
      (eventuallyCorrectInnerCoverQueryStrategy inner) targets := by
  classical
  intro L hL samples observed hcorrect
  obtain ⟨N, hN⟩ := hcorrect
  obtain ⟨base, hbase⟩ := inner.contained L hL
  let repeated := inner.repeat
  let k := Nat.pair base N
  have hNk : N ≤ k := Nat.right_le_pair base N
  have hgood : repeated.cover k ⊆ L := by
    dsimp only [repeated, k]
    rw [CountableInnerCover.repeat_cover_pair]
    exact hbase
  let hasBad : Fin (k + 1) → Prop := fun i =>
    HasPostCorruptionCounterexample repeated L N i
  let cost : Fin (k + 1) → ℕ := fun i =>
    if hasBad i then
      postCorruptionBadRound repeated L N i + 1
    else 0
  let budget := ∑ i : Fin (k + 1), cost i
  let T := max k (max N budget)
  refine ⟨T, ?_⟩
  intro t hTt
  have hkt : k ≤ t := (Nat.le_max_left _ _).trans hTt
  have hNt : N ≤ t :=
    ((Nat.le_max_left N budget).trans
      (Nat.le_max_right k (max N budget))).trans hTt
  let answers := streamPrefix observed (t + 1)
  have hkPass : OneQueryRowPasses t answers k := by
    refine ⟨Nat.lt_succ_iff.mpr hkt, ?_⟩
    intro r hr hrow
    have hrRound : r < t + 1 := by
      simpa [answers, streamPrefix] using hr
    have hkr : k ≤ r := by
      have hpair :
          Nat.pair (oneQueryPairEnumeration r).1
              (oneQueryPairEnumeration r).2 = r :=
        Nat.pair_unpair r
      calc
        k = (oneQueryPairEnumeration r).1 := hrow.symm
        _ ≤ Nat.pair (oneQueryPairEnumeration r).1
              (oneQueryPairEnumeration r).2 :=
          Nat.left_le_pair _ _
        _ = r := hpair
    have hNr : N ≤ r := hNk.trans hkr
    have hqueryMem :
        innerCoverOneQueryPoint repeated r ∈ L := by
      apply hgood
      rw [← hrow]
      exact innerCoverOneQueryPoint_mem repeated r
    have hobs : observed r = true := by
      rw [hN r hNr]
      exact
        (membershipAnswer_eq_true_iff _ _).mpr hqueryMem
    rw [streamPrefix_get?_eq_some observed hrRound, hobs]
  have hexists : ∃ i, OneQueryRowPasses t answers i := ⟨k, hkPass⟩
  let selected := firstPassingOneQueryRow t answers
  have hselectedPass : OneQueryRowPasses t answers selected :=
    firstPassingOneQueryRow_spec hexists
  have hselectedLe : selected ≤ k :=
    firstPassingOneQueryRow_le hexists hkPass
  let selectedFin : Fin (k + 1) :=
    ⟨selected, Nat.lt_succ_iff.mpr hselectedLe⟩
  have hselectedSafe :
      repeated.cover selected \
          (queriedInnerCoverPoints repeated t : Set α) ⊆ L := by
    intro x hx
    by_contra hxL
    by_cases hbad : hasBad selectedFin
    · let r := postCorruptionBadRound repeated L N selected
      have hrspec :=
        postCorruptionBadRound_spec repeated L N selected hbad
      have hcostLe : r + 1 ≤ budget := by
        have hsingle : cost selectedFin ≤ budget := by
          dsimp only [budget]
          exact Finset.single_le_sum
            (f := cost) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ selectedFin)
        simpa [cost, hasBad, selectedFin, hbad, r] using hsingle
      have hbudgetT : budget ≤ T :=
        (Nat.le_max_right N budget).trans
          (Nat.le_max_right k (max N budget))
      have hrt : r < t + 1 := by
        omega
      have hrow : (oneQueryPairEnumeration r).1 = selected :=
        hrspec.2.1
      have hanswer := hselectedPass.2 r (by simpa [answers] using hrt) hrow
      rw [streamPrefix_get?_eq_some observed hrt] at hanswer
      have hobsTrue : observed r = true := Option.some.inj hanswer
      have hobsCorrect := hN r hrspec.1
      have hqueryEq :
          (eventuallyCorrectInnerCoverQueryStrategy inner).query r
              (fun i : Fin (r + 1) => samples i)
              (streamPrefix observed r) =
            innerCoverOneQueryPoint repeated r := rfl
      rw [hqueryEq] at hobsCorrect
      have hobsFalse : observed r = false := by
        rw [hobsCorrect]
        apply Bool.eq_false_iff.mpr
        exact fun htrue =>
          hrspec.2.2 ((membershipAnswer_eq_true_iff _ _).mp htrue)
      rw [hobsTrue] at hobsFalse
      contradiction
    · obtain ⟨point, hpoint⟩ :=
        GenLimit.Support.infiniteEnumeration_surjective
          (repeated.cover selected)
          (repeated.infinite_cover selected) hx.1
      let r := Nat.pair selected point
      have hrow : (oneQueryPairEnumeration r).1 = selected := by
        simp [r, oneQueryPairEnumeration]
      have hqueryEq : innerCoverOneQueryPoint repeated r = x := by
        simp [innerCoverOneQueryPoint, oneQueryPairEnumeration, r, hpoint]
      have hrN : r < N := by
        by_contra hnot
        have hNr : N ≤ r := Nat.le_of_not_gt hnot
        exact hbad ⟨r, hNr, hrow, by simpa [hqueryEq] using hxL⟩
      have hrt : r < t + 1 := hrN.trans_le (hNt.trans (Nat.le_succ t))
      have hqueried : x ∈ queriedInnerCoverPoints repeated t := by
        rw [← hqueryEq]
        exact innerCoverOneQueryPoint_mem_queried repeated hrt
      exact hx.2 hqueried
  intro x hx
  have hxparts :=
    eventuallyCorrectInnerCoverQueryOutput_mem
      inner samples observed t hx
  change x ∈ L ∧ x ∉ (Generic.sample samples (t + 1) : Set α)
  refine ⟨?_, hxparts.2.1⟩
  apply hselectedSafe
  simpa [selected, answers] using ⟨hxparts.1, hxparts.2.2⟩

theorem countableInnerCover_implies_eventuallyCorrectQuery
    [Countable α]
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    EventuallyCorrectQueryGeneratable targets := by
  classical
  let inner := hinner.some
  exact
    ⟨eventuallyCorrectInnerCoverQueryStrategy inner,
      repeatedInnerCover_query_eventuallyCorrect inner⟩

/-! ### Reduction of robust query feedback to the noiseless source model -/

noncomputable def sourceTruthfulQueryBit
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : Bool :=
  membershipAnswer target
    (strategy.query t (fun i => stream i)
      (sourceSetQueryFeedback strategy target stream t))

theorem sourceTruthfulQueryBit_prefix
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    streamPrefix (sourceTruthfulQueryBit strategy target stream) t =
      sourceSetQueryFeedback strategy target stream t := by
  induction t with
  | zero => simp [streamPrefix]
  | succ t ih =>
      rw [source_streamPrefix_succ, sourceSetQueryFeedback_succ, ih]
      rfl

theorem eventuallyCorrectQueryOutput_truthful
    (strategy : SourceSetQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    eventuallyCorrectQueryOutput strategy stream
        (sourceTruthfulQueryBit strategy target stream) t =
      sourceSetQueryOutput strategy target stream t := by
  simp [eventuallyCorrectQueryOutput, sourceSetQueryOutput,
    sourceTruthfulQueryBit_prefix]

theorem eventuallyCorrectQuery_implies_sourceQuery
    {targets : LanguageClass α}
    (hgenerate : EventuallyCorrectQueryGeneratable targets) :
    SourceSetQueryGeneratable targets := by
  classical
  obtain ⟨strategy, hstrategy⟩ := hgenerate
  refine ⟨strategy, ?_⟩
  intro L hL stream _hPresents
  let observed := sourceTruthfulQueryBit strategy L stream
  have heventual :
      EventuallyCorrectQueryFeedback strategy L stream observed := by
    refine ⟨0, ?_⟩
    intro t _ht
    simp [observed, sourceTruthfulQueryBit,
      sourceTruthfulQueryBit_prefix]
  obtain ⟨T, hT⟩ := hstrategy L hL stream observed heventual
  refine ⟨T, ?_⟩
  intro t hTt
  have hout := hT t hTt
  rwa [eventuallyCorrectQueryOutput_truthful] at hout

/-- Appendix Theorem A.7. -/
theorem theorem_A_7_eventuallyCorrectQuery_characterization
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    EventuallyCorrectQueryGeneratable targets ↔
      HasCountableInnerCover targets :=
  ⟨fun h =>
      (theorem_3_4_sourceSetQuery_characterization
        targets hinfinite).mp
        (eventuallyCorrectQuery_implies_sourceQuery h),
    countableInnerCover_implies_eventuallyCorrectQuery⟩

end GenLimit.FeedbackQueries
