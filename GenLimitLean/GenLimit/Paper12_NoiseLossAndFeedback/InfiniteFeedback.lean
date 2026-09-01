import GenLimit.Paper12_NoiseLossAndFeedback.TotalFeedback
import GenLimit.Paper02_LearningTheory.Closure
import GenLimit.Paper02_LearningTheory.NonuniformCharacterization
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Noise, Loss, and Feedback: the infinite-feedback closure sweep

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Section 6.1,
Definition 6.2, Algorithm 4, Theorem 6.3, and Corollary 6.4.

Algorithm 4 examines a countable sequence of uniformly generatable
collections.  On a component with closure dimension `d`, it waits for more
than `d` distinct positive examples.  If the version space is nonempty, its
common core is infinite.  The algorithm then queries and outputs the least
fresh core point at or above a persistent cursor.

This file formalizes the paper's infinite-feedback correctness predicate and
the complete causal controller and convergence argument:

* the next queried point always exists;
* it lies in the frozen common core, is fresh, and does not move the cursor
  backwards;
* the finite-prefix reconstruction agrees exactly with the truthful run;
* the outer component index is monotone and bounded by any component
  containing the target;
* once that index stabilizes and the sample is large, every output is
  certified by a positive membership response; and
* uniformly and non-uniformly generatable countable covers yield Theorem 6.3
  and Corollary 6.4.

The controller retains the printed algorithm's `v` after a positive query,
so it may repeat a fresh output until that target point appears in the
positive enumeration.  The separate strict-cursor sweep lemmas verify the
stronger progress argument stated in the source proof.  No computability or
runtime claim is made by these semantic constructions.

The convergence proof first uses the shared `FeedbackGenerator` interface,
which permits `none` on wait/skip rounds.  `TotalFeedback` then replaces each
such action by a dummy query at `0`, masks the dummy answer, and proves exact
execution equivalence.  The total-query wrappers at the end of this file
therefore match Definition 6.1's one-query-per-round syntax.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-! ## Optional-query convergence interface used internally -/

/-- Eventual correctness at a fixed deterministic feedback generator, using
the shared optional-query interface as an internal proof model.  The literal
Definition 6.2 interface is `IsLimitTotalFeedbackGenerator`. -/
def IsLimitFeedbackGenerator
    (gen : FeedbackGenerator ℕ)
    (C : GenLimit.Generic.LanguageClass ℕ) : Prop :=
  ∀ L, L ∈ C → ∀ stream,
    ExactEnumeration stream L →
      ∃ T, ∀ t, T ≤ t →
        FeedbackCorrectAt gen L stream t

/-- Existential generation in the limit with unrestricted membership
feedback. -/
def GeneratableInLimitWithFeedback
    (C : GenLimit.Generic.LanguageClass ℕ) : Prop :=
  ∃ gen : FeedbackGenerator ℕ,
    IsLimitFeedbackGenerator gen C

/-! ## Algorithm 4's frozen component -/

/-- Data fixed when Algorithm 4 enters the infinite inner loop for one
component.  `entrySample` is the positive sample at entry, and `dimension`
is that component's finite closure dimension. -/
structure FeedbackClosureStage where
  component : GenLimit.Generic.LanguageClass ℕ
  dimension : ℕ
  entrySample : Finset ℕ
  dimensionBound :
    ClosureDimensionAtMost component dimension
  large :
    dimension < entrySample.card
  consistent :
    (versionSpace component entrySample).Nonempty

/-- The frozen common core `Bᵢ` in Algorithm 4. -/
def FeedbackClosureStage.core
    (stage : FeedbackClosureStage) : Set ℕ :=
  commonCore stage.component stage.entrySample

theorem FeedbackClosureStage.core_infinite
    (stage : FeedbackClosureStage) :
    stage.core.Infinite :=
  stage.dimensionBound stage.entrySample stage.large stage.consistent

/-- If the target belongs to the current component and contains the entry
sample, the frozen core is a subset of the target.  This is the safety
argument used when Algorithm 4 reaches a covering component. -/
theorem FeedbackClosureStage.core_subset_target
    (stage : FeedbackClosureStage)
    {target : Set ℕ}
    (htarget : target ∈ stage.component)
    (hsample : (stage.entrySample : Set ℕ) ⊆ target) :
    stage.core ⊆ target :=
  commonCore_subset_of_mem_versionSpace ⟨htarget, hsample⟩

/-! ## The persistent least-fresh-point sweep -/

private theorem exists_core_point_fresh_at_or_above
    (stage : FeedbackClosureStage)
    (observed : Finset ℕ) (cursor : ℕ) :
    ∃ n, n ∈ stage.core ∧ n ∉ observed ∧ cursor ≤ n := by
  obtain ⟨n, hnCore, hnAvoid⟩ :=
    stage.core_infinite.exists_notMem_finset
      (observed ∪ Finset.range cursor)
  refine ⟨n, hnCore, ?_, ?_⟩
  · exact fun hnObserved =>
      hnAvoid (Finset.mem_union_left _ hnObserved)
  · have hnRange : n ∉ Finset.range cursor :=
      fun hn => hnAvoid (Finset.mem_union_right _ hn)
    simpa only [Finset.mem_range, not_lt] using hnRange

/-- Line `v = min {j ≥ v | j ∈ Bᵢ \ S}` of Algorithm 4.

The proof argument is retained as data so the definition is total without
silently installing a fallback value. -/
noncomputable def leastFreshCorePoint
    (stage : FeedbackClosureStage)
    (observed : Finset ℕ) (cursor : ℕ) : ℕ :=
  by
    classical
    exact Nat.find
      (exists_core_point_fresh_at_or_above stage observed cursor)

theorem leastFreshCorePoint_spec
    (stage : FeedbackClosureStage)
    (observed : Finset ℕ) (cursor : ℕ) :
    leastFreshCorePoint stage observed cursor ∈ stage.core ∧
      leastFreshCorePoint stage observed cursor ∉ observed ∧
      cursor ≤ leastFreshCorePoint stage observed cursor := by
  classical
  exact Nat.find_spec
    (exists_core_point_fresh_at_or_above stage observed cursor)

theorem leastFreshCorePoint_mem_core
    (stage : FeedbackClosureStage)
    (observed : Finset ℕ) (cursor : ℕ) :
    leastFreshCorePoint stage observed cursor ∈ stage.core :=
  (leastFreshCorePoint_spec stage observed cursor).1

theorem leastFreshCorePoint_fresh
    (stage : FeedbackClosureStage)
    (observed : Finset ℕ) (cursor : ℕ) :
    leastFreshCorePoint stage observed cursor ∉ observed :=
  (leastFreshCorePoint_spec stage observed cursor).2.1

theorem cursor_le_leastFreshCorePoint
    (stage : FeedbackClosureStage)
    (observed : Finset ℕ) (cursor : ℕ) :
    cursor ≤ leastFreshCorePoint stage observed cursor :=
  (leastFreshCorePoint_spec stage observed cursor).2.2

/-- Least-point selection cannot jump over any other eligible core point. -/
theorem leastFreshCorePoint_le
    (stage : FeedbackClosureStage)
    (observed : Finset ℕ) (cursor candidate : ℕ)
    (hcore : candidate ∈ stage.core)
    (hfresh : candidate ∉ observed)
    (hcursor : cursor ≤ candidate) :
    leastFreshCorePoint stage observed cursor ≤ candidate := by
  classical
  exact Nat.find_min'
    (exists_core_point_fresh_at_or_above stage observed cursor)
    ⟨hcore, hfresh, hcursor⟩

/-- The next persistent cursor is strictly larger than the point just
queried, exactly as in the source's global `v` sweep. -/
theorem leastFreshCorePoint_lt_nextCursor
    (stage : FeedbackClosureStage)
    (observed : Finset ℕ) (cursor : ℕ) :
    leastFreshCorePoint stage observed cursor <
      leastFreshCorePoint stage observed cursor + 1 :=
  Nat.lt_succ_self _

/-- If a fixed core point is outside the target, then it never belongs to a
positive sample contained in that target. -/
theorem counterexample_fresh_of_observed_subset
    {target : Set ℕ} {observed : Finset ℕ} {counterexample : ℕ}
    (hobserved : (observed : Set ℕ) ⊆ target)
    (hbad : counterexample ∉ target) :
    counterexample ∉ observed :=
  fun hmem => hbad (hobserved hmem)

/-- The key progress fact in the source proof: while a bad frozen-core point
`b` remains at or above the cursor, the next least query is at most `b`.
Consequently a sweep cannot skip a counterexample and then claim that the
remaining tail of its core is safe. -/
theorem leastFreshCorePoint_le_counterexample
    (stage : FeedbackClosureStage)
    {target : Set ℕ} (observed : Finset ℕ)
    (cursor counterexample : ℕ)
    (hobserved : (observed : Set ℕ) ⊆ target)
    (hbadCore : counterexample ∈ stage.core)
    (hbadTarget : counterexample ∉ target)
    (hcursor : cursor ≤ counterexample) :
    leastFreshCorePoint stage observed cursor ≤ counterexample :=
  leastFreshCorePoint_le stage observed cursor counterexample
    hbadCore
    (counterexample_fresh_of_observed_subset hobserved hbadTarget)
    hcursor

/-- On a target-containing component, every Algorithm 4 query/output is a
fresh target point.  This is the local correctness half of Theorem 6.3. -/
theorem leastFreshCorePoint_correct
    (stage : FeedbackClosureStage)
    {target : Set ℕ} (observed : Finset ℕ) (cursor : ℕ)
    (htarget : target ∈ stage.component)
    (hentry : (stage.entrySample : Set ℕ) ⊆ target) :
    leastFreshCorePoint stage observed cursor ∈ target ∧
      leastFreshCorePoint stage observed cursor ∉ observed := by
  exact ⟨stage.core_subset_target htarget hentry
      (leastFreshCorePoint_mem_core stage observed cursor),
    leastFreshCorePoint_fresh stage observed cursor⟩

/-! ## An auxiliary strict sweep cannot miss a negative answer -/

/-- Cursor before round `round` of an auxiliary frozen-core sweep.  Unlike
the printed controller, this stronger diagnostic advances to `candidate + 1`
immediately.  The observation sample may grow between rounds, but the core
remains the one fixed at stage entry.  The final convergence theorem below
does not depend on this auxiliary sweep. -/
noncomputable def closureSweepCursor
    (stage : FeedbackClosureStage)
    (observed : ℕ → Finset ℕ) (initialCursor : ℕ) :
    ℕ → ℕ
  | 0 => initialCursor
  | round + 1 =>
      leastFreshCorePoint stage (observed round)
          (closureSweepCursor stage observed initialCursor round) + 1

/-- Query/output made at one round of the frozen-core sweep. -/
noncomputable def closureSweepQuery
    (stage : FeedbackClosureStage)
    (observed : ℕ → Finset ℕ) (initialCursor round : ℕ) : ℕ :=
  leastFreshCorePoint stage (observed round)
    (closureSweepCursor stage observed initialCursor round)

@[simp] theorem closureSweepCursor_zero
    (stage : FeedbackClosureStage)
    (observed : ℕ → Finset ℕ) (initialCursor : ℕ) :
    closureSweepCursor stage observed initialCursor 0 =
      initialCursor :=
  rfl

theorem closureSweepCursor_succ
    (stage : FeedbackClosureStage)
    (observed : ℕ → Finset ℕ) (initialCursor round : ℕ) :
    closureSweepCursor stage observed initialCursor (round + 1) =
      closureSweepQuery stage observed initialCursor round + 1 :=
  rfl

theorem closureSweepCursor_lt_succ
    (stage : FeedbackClosureStage)
    (observed : ℕ → Finset ℕ) (initialCursor round : ℕ) :
    closureSweepCursor stage observed initialCursor round <
      closureSweepCursor stage observed initialCursor (round + 1) := by
  rw [closureSweepCursor_succ]
  exact (cursor_le_leastFreshCorePoint stage (observed round)
    (closureSweepCursor stage observed initialCursor round)).trans_lt
      (Nat.lt_succ_self _)

/-- Restarting the recursion after its first query gives the same cursor
sequence as shifting the observation samples by one. -/
theorem closureSweepCursor_succ_shift
    (stage : FeedbackClosureStage)
    (observed : ℕ → Finset ℕ) (initialCursor round : ℕ) :
    closureSweepCursor stage observed initialCursor (round + 1) =
      closureSweepCursor stage (fun n => observed (n + 1))
        (closureSweepQuery stage observed initialCursor 0 + 1) round := by
  induction round with
  | zero =>
      rw [closureSweepCursor_succ, closureSweepCursor_zero]
  | succ round ih =>
      rw [closureSweepCursor_succ, closureSweepCursor_succ]
      unfold closureSweepQuery
      rw [ih]
      simp only [closureSweepQuery, closureSweepCursor_zero]

theorem closureSweepQuery_succ_shift
    (stage : FeedbackClosureStage)
    (observed : ℕ → Finset ℕ) (initialCursor round : ℕ) :
    closureSweepQuery stage observed initialCursor (round + 1) =
      closureSweepQuery stage (fun n => observed (n + 1))
        (closureSweepQuery stage observed initialCursor 0 + 1) round := by
  unfold closureSweepQuery
  rw [closureSweepCursor_succ_shift]
  simp only [closureSweepQuery, closureSweepCursor_zero]

/-- A bad point in the frozen core is queried after finitely many rounds,
provided every growing observation sample is still contained in the target.

This discharges the “eventually `v` takes the value `b`” step in the source
proof, including the fact that the positive sample changes during the inner
loop. -/
theorem closureSweep_eventually_queries_counterexample
    (stage : FeedbackClosureStage)
    {target : Set ℕ}
    (observed : ℕ → Finset ℕ)
    (initialCursor counterexample : ℕ)
    (hobserved : ∀ round, (observed round : Set ℕ) ⊆ target)
    (hbadCore : counterexample ∈ stage.core)
    (hbadTarget : counterexample ∉ target)
    (hcursor : initialCursor ≤ counterexample) :
    ∃ round,
      closureSweepQuery stage observed initialCursor round =
        counterexample := by
  let query :=
    closureSweepQuery stage observed initialCursor 0
  have hqueryLe : query ≤ counterexample := by
    exact leastFreshCorePoint_le_counterexample stage
      (observed 0) initialCursor counterexample
      (hobserved 0) hbadCore hbadTarget hcursor
  have hcursorQuery : initialCursor ≤ query := by
    exact cursor_le_leastFreshCorePoint stage (observed 0) initialCursor
  by_cases hquery : query = counterexample
  · exact ⟨0, hquery⟩
  · have hqueryLt : query < counterexample :=
      Nat.lt_of_le_of_ne hqueryLe hquery
    let nextCursor := query + 1
    have hnextCursor : nextCursor ≤ counterexample := by
      exact Nat.succ_le_iff.mpr hqueryLt
    have hinitialNextCursor : initialCursor < nextCursor := by
      exact hcursorQuery.trans_lt (Nat.lt_succ_self query)
    obtain ⟨round, hround⟩ :=
      closureSweep_eventually_queries_counterexample
        stage (fun n => observed (n + 1))
        nextCursor counterexample
        (fun n => hobserved (n + 1))
        hbadCore hbadTarget hnextCursor
    refine ⟨round + 1, ?_⟩
    rw [closureSweepQuery_succ_shift]
    simpa only [query, nextCursor] using hround
termination_by counterexample - initialCursor
decreasing_by
  omega

theorem closureSweepQuery_correct
    (stage : FeedbackClosureStage)
    {target : Set ℕ}
    (observed : ℕ → Finset ℕ) (initialCursor round : ℕ)
    (htarget : target ∈ stage.component)
    (hentry : (stage.entrySample : Set ℕ) ⊆ target) :
    closureSweepQuery stage observed initialCursor round ∈ target ∧
      closureSweepQuery stage observed initialCursor round ∉
        observed round := by
  exact leastFreshCorePoint_correct stage (observed round)
    (closureSweepCursor stage observed initialCursor round)
    htarget hentry

/-! ## Countable covers -/

/-- The literal countable-cover hypothesis in Theorem 6.3. -/
def IsCountableFeedbackCover
    (C : GenLimit.Generic.LanguageClass ℕ)
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ) : Prop :=
  C = ⋃ i, components i

/-- Every target in a countable cover occurs in some component. -/
theorem target_mem_feedbackCover_component
    {C : GenLimit.Generic.LanguageClass ℕ}
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    (hcover : IsCountableFeedbackCover C components)
    {target : Set ℕ} (htarget : target ∈ C) :
    ∃ i, target ∈ components i := by
  rw [hcover] at htarget
  exact Set.mem_iUnion.mp htarget

/-- Once the sample has crossed the selected component's closure dimension,
the target itself witnesses consistency and the resulting frozen stage has a
core contained in the target. -/
def targetFeedbackClosureStage
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (componentIndex : ℕ)
    (htarget : target ∈ components componentIndex)
    (sample : Finset ℕ)
    (hsample : (sample : Set ℕ) ⊆ target)
    (hlarge : dimensions componentIndex < sample.card) :
    FeedbackClosureStage where
  component := components componentIndex
  dimension := dimensions componentIndex
  entrySample := sample
  dimensionBound := (hdimensions componentIndex).1
  large := hlarge
  consistent := ⟨target, htarget, hsample⟩

theorem targetFeedbackClosureStage_core_subset
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (componentIndex : ℕ)
    (htarget : target ∈ components componentIndex)
    (sample : Finset ℕ)
    (hsample : (sample : Set ℕ) ⊆ target)
    (hlarge : dimensions componentIndex < sample.card) :
    (targetFeedbackClosureStage components dimensions hdimensions
      target componentIndex htarget sample hsample hlarge).core ⊆
        target :=
  FeedbackClosureStage.core_subset_target _ htarget hsample

/-! ## Algorithm 4 as a causal alternating controller -/

/-- A component together with the entry sample frozen when Algorithm 4
starts its inner loop. -/
structure IndexedFeedbackClosureStage
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ) where
  index : ℕ
  entrySample : Finset ℕ
  large : dimensions index < entrySample.card
  consistent :
    (versionSpace (components index) entrySample).Nonempty

/-- Forget the component index and expose the local frozen-core stage. -/
def IndexedFeedbackClosureStage.toClosureStage
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    {dimensions : ℕ → ℕ}
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (stage : IndexedFeedbackClosureStage components dimensions) :
    FeedbackClosureStage where
  component := components stage.index
  dimension := dimensions stage.index
  entrySample := stage.entrySample
  dimensionBound := (hdimensions stage.index).1
  large := stage.large
  consistent := stage.consistent

/-- Reconstructible finite control data before the next query.  The source's
global `v` is `cursor`; `nextComponent` is the next outer-loop index when no
inner loop is active. -/
structure InfiniteFeedbackControllerState
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ) where
  nextComponent : ℕ
  cursor : ℕ
  active :
    Option (IndexedFeedbackClosureStage components dimensions)

def InfiniteFeedbackControllerState.initial
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ) :
    InfiniteFeedbackControllerState components dimensions where
  nextComponent := 0
  cursor := 0
  active := none

/-- One causal round is either waiting for enough distinct examples,
skipping an inconsistent component, or querying/outputting one frozen-core
point. -/
inductive InfiniteFeedbackControllerAction
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ) where
  | wait
  | skip
  | query
      (stage : IndexedFeedbackClosureStage components dimensions)
      (candidate : ℕ)

namespace InfiniteFeedbackControllerAction

def queryValue
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    {dimensions : ℕ → ℕ} :
    InfiniteFeedbackControllerAction components dimensions →
      Option ℕ
  | wait => none
  | skip => none
  | query _ candidate => some candidate

/-- The output on wait/skip rounds is irrelevant before stabilization. -/
def outputValue
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    {dimensions : ℕ → ℕ} :
    InfiniteFeedbackControllerAction components dimensions →
      ℕ
  | wait => 0
  | skip => 0
  | query _ candidate => candidate

end InfiniteFeedbackControllerAction

/-- The paper's control-state branch structure for the current positive
sample, represented in the shared optional-query interface.

An inconsistent component consumes one (query-free) round before the outer
loop advances.  This stuttering implementation is extensionally harmless
for an eventual-correctness theorem and makes every state change causal. -/
noncomputable def infiniteFeedbackControllerAction
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ) :
    InfiniteFeedbackControllerAction components dimensions := by
  classical
  match state.active with
  | some active =>
      exact .query active
        (leastFreshCorePoint
          (active.toClosureStage hdimensions)
          observed state.cursor)
  | none =>
      if hlarge :
          dimensions state.nextComponent < observed.card then
        if hconsistent :
            (versionSpace (components state.nextComponent)
              observed).Nonempty then
          let active :
              IndexedFeedbackClosureStage components dimensions :=
            { index := state.nextComponent
              entrySample := observed
              large := hlarge
              consistent := hconsistent }
          exact .query active
            (leastFreshCorePoint
              (active.toClosureStage hdimensions)
              observed state.cursor)
        else
          exact .skip
      else
        exact .wait

/-- Update the reconstructible controller state after the current response.
Only a negative membership answer leaves an active frozen-core sweep. -/
def infiniteFeedbackControllerNext
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    {dimensions : ℕ → ℕ}
    (state : InfiniteFeedbackControllerState components dimensions)
    (action : InfiniteFeedbackControllerAction components dimensions)
    (response : Option Bool) :
    InfiniteFeedbackControllerState components dimensions :=
  match action with
  | .wait => state
  | .skip =>
      { nextComponent := state.nextComponent + 1
        cursor := state.cursor
        active := none }
  | .query stage candidate =>
      if response = some false then
        { nextComponent := stage.index + 1
          cursor := candidate
          active := none }
      else
        { nextComponent := stage.index
          cursor := candidate
          active := some stage }

/-- Reconstruct the controller state before time `t` from exactly the causal
observation/response prefix available to a feedback generator. -/
noncomputable def infiniteFeedbackControllerState
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i)) :
    (t : ℕ) →
      (Fin (t + 1) → ℕ) →
      (Fin t → Option Bool) →
      InfiniteFeedbackControllerState components dimensions
  | 0, _observations, _responses =>
      InfiniteFeedbackControllerState.initial components dimensions
  | t + 1, observations, responses =>
      let priorObservations : Fin (t + 1) → ℕ :=
        fun i => observations i.castSucc
      let priorResponses : Fin t → Option Bool :=
        fun i => responses i.castSucc
      let priorState :=
        infiniteFeedbackControllerState components dimensions hdimensions
          t priorObservations priorResponses
      let priorObserved :=
        GenLimit.Generic.sequenceSample priorObservations
      let priorAction :=
        infiniteFeedbackControllerAction components dimensions hdimensions
          priorState priorObserved
      infiniteFeedbackControllerNext priorState priorAction
        (responses ⟨t, Nat.lt_succ_self t⟩)

/-- Algorithm 4 compiled into the shared optional-query alternating
interface.  Wait/skip rounds use `none`; a mandatory-query presentation can
instead issue and ignore a dummy natural-number query.  The controller is
semantic/noncomputable because component consistency and least points of
arbitrary common cores need not be decidable. -/
noncomputable def countableCoverFeedbackGenerator
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i)) :
    FeedbackGenerator ℕ where
  query := fun t observations responses =>
    let state :=
      infiniteFeedbackControllerState components dimensions hdimensions
        t observations responses
    let observed := GenLimit.Generic.sequenceSample observations
    (infiniteFeedbackControllerAction components dimensions hdimensions
      state observed).queryValue
  output := fun t observations responses =>
    let state :=
      infiniteFeedbackControllerState components dimensions hdimensions
        t observations (fun i => responses i.castSucc)
    let observed := GenLimit.Generic.sequenceSample observations
    (infiniteFeedbackControllerAction components dimensions hdimensions
      state observed).outputValue

/-- Algorithm 4 in Definition 6.1's literal one-query-per-round interface.
The query is the optional controller's candidate when one exists and the
dummy natural number `0` on wait/skip rounds.  Dummy answers are masked before
the original controller is evaluated. -/
noncomputable def countableCoverTotalFeedbackGenerator
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i)) :
    TotalFeedbackGenerator ℕ :=
  totalizeFeedbackGenerator
    (countableCoverFeedbackGenerator components dimensions hdimensions) 0

/-- The literal Algorithm 4 controller produces exactly the same output as
the optional controller used by the convergence proof, at every target,
stream, and round. -/
theorem actualTotalFeedbackOutput_countableCover_eq_optional
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (t : ℕ) :
    actualTotalFeedbackOutput
        (countableCoverTotalFeedbackGenerator
          components dimensions hdimensions)
        target stream t =
      actualFeedbackOutput
        (countableCoverFeedbackGenerator
          components dimensions hdimensions)
        target stream t := by
  exact actualTotalFeedbackOutput_totalized
    (countableCoverFeedbackGenerator components dimensions hdimensions)
    0 target stream t

theorem countableCoverFeedbackGenerator_query
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (t : ℕ) (observations : Fin (t + 1) → ℕ)
    (responses : Fin t → Option Bool) :
    (countableCoverFeedbackGenerator components dimensions hdimensions).query
        t observations responses =
      (infiniteFeedbackControllerAction components dimensions hdimensions
        (infiniteFeedbackControllerState components dimensions hdimensions
          t observations responses)
        (GenLimit.Generic.sequenceSample observations)).queryValue :=
  rfl

theorem countableCoverFeedbackGenerator_output
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (t : ℕ) (observations : Fin (t + 1) → ℕ)
    (responses : Fin (t + 1) → Option Bool) :
    (countableCoverFeedbackGenerator components dimensions hdimensions).output
        t observations responses =
      (infiniteFeedbackControllerAction components dimensions hdimensions
        (infiniteFeedbackControllerState components dimensions hdimensions
          t observations (fun i => responses i.castSucc))
        (GenLimit.Generic.sequenceSample observations)).outputValue :=
  rfl

theorem membershipAnswer_eq_true_iff
    (target : Set ℕ) (candidate : ℕ) :
    membershipAnswer target candidate = true ↔
      candidate ∈ target := by
  classical
  simp [membershipAnswer]

theorem membershipAnswer_eq_false_iff
    (target : Set ℕ) (candidate : ℕ) :
    membershipAnswer target candidate = false ↔
      candidate ∉ target := by
  classical
  simp [membershipAnswer]

/-- Truthful response associated with a controller action. -/
noncomputable def truthfulControllerResponse
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    {dimensions : ℕ → ℕ}
    (target : Set ℕ) :
    InfiniteFeedbackControllerAction components dimensions →
      Option Bool
  | .wait => none
  | .skip => none
  | .query _ candidate =>
      some (membershipAnswer target candidate)

theorem infiniteFeedbackControllerAction_of_active
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ)
    (active : IndexedFeedbackClosureStage components dimensions)
    (hactive : state.active = some active) :
    infiniteFeedbackControllerAction components dimensions hdimensions
        state observed =
      .query active
        (leastFreshCorePoint
          (active.toClosureStage hdimensions)
          observed state.cursor) := by
  classical
  simp [infiniteFeedbackControllerAction, hactive]

/-- While an active frozen core is contained in the target, the causal
controller's query and output are both fresh target points. -/
theorem infiniteFeedbackControllerAction_active_correct
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ)
    (active : IndexedFeedbackClosureStage components dimensions)
    (hactive : state.active = some active)
    {target : Set ℕ}
    (hcore :
      (active.toClosureStage hdimensions).core ⊆ target) :
    let action :=
      infiniteFeedbackControllerAction components dimensions hdimensions
        state observed
    action.outputValue ∈ target ∧
      action.outputValue ∉ observed := by
  rw [infiniteFeedbackControllerAction_of_active
    components dimensions hdimensions state observed active hactive]
  change
    leastFreshCorePoint (active.toClosureStage hdimensions)
        observed state.cursor ∈ target ∧
      leastFreshCorePoint (active.toClosureStage hdimensions)
        observed state.cursor ∉ observed
  exact ⟨hcore (leastFreshCorePoint_mem_core
      (active.toClosureStage hdimensions) observed state.cursor),
    leastFreshCorePoint_fresh
      (active.toClosureStage hdimensions) observed state.cursor⟩

theorem truthfulControllerResponse_active_eq_true
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ)
    (active : IndexedFeedbackClosureStage components dimensions)
    (hactive : state.active = some active)
    {target : Set ℕ}
    (hcore :
      (active.toClosureStage hdimensions).core ⊆ target) :
    truthfulControllerResponse target
        (infiniteFeedbackControllerAction components dimensions hdimensions
          state observed) =
      some true := by
  rw [infiniteFeedbackControllerAction_of_active
    components dimensions hdimensions state observed active hactive]
  simp only [truthfulControllerResponse, Option.some.injEq]
  apply (membershipAnswer_eq_true_iff target _).mpr
  exact hcore (leastFreshCorePoint_mem_core
    (active.toClosureStage hdimensions) observed state.cursor)

/-- Conversely, querying a frozen-core counterexample produces the negative
response that advances Algorithm 4 to the next component. -/
theorem truthfulControllerResponse_query_eq_false
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    {dimensions : ℕ → ℕ}
    (target : Set ℕ)
    (active : IndexedFeedbackClosureStage components dimensions)
    (candidate : ℕ) (hbad : candidate ∉ target) :
    truthfulControllerResponse target
        (.query active candidate) =
      some false := by
  simp only [truthfulControllerResponse, Option.some.injEq]
  exact (membershipAnswer_eq_false_iff target candidate).mpr hbad

/-- A positive active query keeps the frozen stage and the source's global
cursor at the queried point.  If that positive point has not yet appeared in
the example stream, the printed Algorithm 4 may query/output it again. -/
theorem infiniteFeedbackControllerNext_query_true
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    {dimensions : ℕ → ℕ}
    (state : InfiniteFeedbackControllerState components dimensions)
    (active : IndexedFeedbackClosureStage components dimensions)
    (candidate : ℕ) :
    infiniteFeedbackControllerNext state (.query active candidate)
        (some true) =
      { nextComponent := active.index
        cursor := candidate
        active := some active } := by
  rfl

/-- A negative query retires the frozen stage and advances the outer-loop
index exactly once, retaining the source's current `v`. -/
theorem infiniteFeedbackControllerNext_query_false
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    {dimensions : ℕ → ℕ}
    (state : InfiniteFeedbackControllerState components dimensions)
    (active : IndexedFeedbackClosureStage components dimensions)
    (candidate : ℕ) :
    infiniteFeedbackControllerNext state (.query active candidate)
        (some false) =
      { nextComponent := active.index + 1
        cursor := candidate
        active := none } := by
  rfl

/-! ## The truthful causal run -/

/-- State of Algorithm 4 before time `t`, when its membership queries are
answered truthfully by `target`.  Keeping this run separate from the
finite-prefix reconstruction makes the convergence argument readable; the
alignment theorem below proves that it is exactly the execution performed by
`countableCoverFeedbackGenerator`. -/
noncomputable def infiniteFeedbackRunState
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ) :
    ℕ → InfiniteFeedbackControllerState components dimensions
  | 0 => InfiniteFeedbackControllerState.initial components dimensions
  | t + 1 =>
      let state :=
        infiniteFeedbackRunState components dimensions hdimensions
          target stream t
      let action :=
        infiniteFeedbackControllerAction components dimensions hdimensions
          state (observedThrough stream t)
      infiniteFeedbackControllerNext state action
        (truthfulControllerResponse target action)

/-- Action made by the truthful run at time `t`. -/
noncomputable def infiniteFeedbackRunAction
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (t : ℕ) :
    InfiniteFeedbackControllerAction components dimensions :=
  infiniteFeedbackControllerAction components dimensions hdimensions
    (infiniteFeedbackRunState components dimensions hdimensions
      target stream t)
    (observedThrough stream t)

@[simp] theorem infiniteFeedbackRunState_zero
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ) :
    infiniteFeedbackRunState components dimensions hdimensions
        target stream 0 =
      InfiniteFeedbackControllerState.initial components dimensions :=
  rfl

theorem infiniteFeedbackRunState_succ
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (t : ℕ) :
    infiniteFeedbackRunState components dimensions hdimensions
        target stream (t + 1) =
      infiniteFeedbackControllerNext
        (infiniteFeedbackRunState components dimensions hdimensions
          target stream t)
        (infiniteFeedbackRunAction components dimensions hdimensions
          target stream t)
        (truthfulControllerResponse target
          (infiniteFeedbackRunAction components dimensions hdimensions
            target stream t)) :=
  rfl

/-- The reconstructed state used by the generator agrees with the direct
truthful run on every causal prefix. -/
theorem infiniteFeedbackControllerState_actual
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ) :
    ∀ t,
      infiniteFeedbackControllerState components dimensions hdimensions
          t (fun i => stream i)
          (fun i =>
            actualFeedbackResponse
              (countableCoverFeedbackGenerator
                components dimensions hdimensions)
              target stream i) =
        infiniteFeedbackRunState components dimensions hdimensions
          target stream t := by
  intro t
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      rw [infiniteFeedbackControllerState]
      simp only
      change
        infiniteFeedbackControllerNext
            (infiniteFeedbackControllerState components dimensions hdimensions
              t (fun i => stream i)
              (fun i =>
                actualFeedbackResponse
                  (countableCoverFeedbackGenerator
                    components dimensions hdimensions)
                  target stream i))
            (infiniteFeedbackControllerAction components dimensions hdimensions
              (infiniteFeedbackControllerState components dimensions hdimensions
                t (fun i => stream i)
                (fun i =>
                  actualFeedbackResponse
                    (countableCoverFeedbackGenerator
                      components dimensions hdimensions)
                    target stream i))
              (GenLimit.Generic.sequenceSample
                (fun i : Fin (t + 1) => stream i)))
            (actualFeedbackResponse
              (countableCoverFeedbackGenerator
                components dimensions hdimensions)
              target stream t) =
          infiniteFeedbackRunState components dimensions hdimensions
            target stream (t + 1)
      rw [ih, GenLimit.Generic.sequenceSample_prefix,
        infiniteFeedbackRunState_succ]
      congr 1
      rw [actualFeedbackResponse_eq]
      rw [countableCoverFeedbackGenerator_query,
        ih,
        GenLimit.Generic.sequenceSample_prefix]
      rw [show GenLimit.Generic.sample stream (t + 1) =
          observedThrough stream t from rfl]
      unfold infiniteFeedbackRunAction
      cases infiniteFeedbackControllerAction components dimensions
          hdimensions
          (infiniteFeedbackRunState components dimensions hdimensions
            target stream t)
          (observedThrough stream t) <;>
        rfl

/-- The actual response transcript is the truthful response of the direct
controller action. -/
theorem actualFeedbackResponse_countableCover_eq
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (t : ℕ) :
    actualFeedbackResponse
        (countableCoverFeedbackGenerator components dimensions hdimensions)
        target stream t =
      truthfulControllerResponse target
        (infiniteFeedbackRunAction components dimensions hdimensions
          target stream t) := by
  rw [actualFeedbackResponse_eq]
  rw [countableCoverFeedbackGenerator_query,
    infiniteFeedbackControllerState_actual,
    GenLimit.Generic.sequenceSample_prefix]
  rw [show GenLimit.Generic.sample stream (t + 1) =
      observedThrough stream t from rfl]
  unfold infiniteFeedbackRunAction
  cases infiniteFeedbackControllerAction components dimensions
      hdimensions
      (infiniteFeedbackRunState components dimensions hdimensions
        target stream t)
      (observedThrough stream t) <;>
    rfl

/-- The output seen in the feedback semantics is exactly the output attached
to the direct controller action. -/
theorem actualFeedbackOutput_countableCover_eq
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (t : ℕ) :
    actualFeedbackOutput
        (countableCoverFeedbackGenerator components dimensions hdimensions)
        target stream t =
      (infiniteFeedbackRunAction components dimensions hdimensions
        target stream t).outputValue := by
  unfold actualFeedbackOutput
  rw [countableCoverFeedbackGenerator_output]
  simp only [Fin.coe_castSucc]
  rw [infiniteFeedbackControllerState_actual,
    GenLimit.Generic.sequenceSample_prefix]
  change
    (infiniteFeedbackRunAction components dimensions hdimensions
      target stream t).outputValue =
      (infiniteFeedbackRunAction components dimensions hdimensions
        target stream t).outputValue
  rfl

/-! ## Run invariants and the bounded outer index -/

/-- Every active frozen stage was entered at the current outer index and
from a positive sample contained in the target. -/
def InfiniteFeedbackStateInvariant
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    {dimensions : ℕ → ℕ}
    (target : Set ℕ)
    (state : InfiniteFeedbackControllerState components dimensions) : Prop :=
  (∀ active, state.active = some active →
      active.index = state.nextComponent) ∧
    ∀ active, state.active = some active →
      (active.entrySample : Set ℕ) ⊆ target

theorem infiniteFeedbackStateInvariant_initial
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ) (target : Set ℕ) :
    InfiniteFeedbackStateInvariant target
      (InfiniteFeedbackControllerState.initial components dimensions) := by
  constructor <;> intro active hactive <;> cases hactive

/-- Any query chosen by the controller carries the current outer index, the
positive entry sample, and a fresh point of its frozen common core. -/
theorem infiniteFeedbackControllerAction_query_spec
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ)
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ)
    (hinvariant : InfiniteFeedbackStateInvariant target state)
    (hobserved : (observed : Set ℕ) ⊆ target)
    (active : IndexedFeedbackClosureStage components dimensions)
    (candidate : ℕ)
    (haction :
      infiniteFeedbackControllerAction components dimensions hdimensions
          state observed =
        .query active candidate) :
    active.index = state.nextComponent ∧
      (active.entrySample : Set ℕ) ⊆ target ∧
      candidate ∈ (active.toClosureStage hdimensions).core ∧
      candidate ∉ observed := by
  classical
  cases hstateActive : state.active with
  | none =>
      by_cases hlarge :
          dimensions state.nextComponent < observed.card
      · by_cases hconsistent :
            (versionSpace (components state.nextComponent)
              observed).Nonempty
        · simp only [infiniteFeedbackControllerAction, hstateActive,
            hlarge, hconsistent, dite_true] at haction
          cases haction
          exact ⟨rfl, hobserved,
            leastFreshCorePoint_mem_core _ observed state.cursor,
            leastFreshCorePoint_fresh _ observed state.cursor⟩
        · simp [infiniteFeedbackControllerAction, hstateActive,
            hlarge, hconsistent] at haction
      · simp [infiniteFeedbackControllerAction, hstateActive,
          hlarge] at haction
  | some current =>
      have hcurrentIndex := hinvariant.1 current hstateActive
      have hcurrentEntry := hinvariant.2 current hstateActive
      rw [infiniteFeedbackControllerAction_of_active
        components dimensions hdimensions state observed current
        hstateActive] at haction
      cases haction
      exact ⟨hcurrentIndex,
        hcurrentEntry,
        leastFreshCorePoint_mem_core _ observed state.cursor,
        leastFreshCorePoint_fresh _ observed state.cursor⟩

/-- One controller update preserves the active-stage invariant. -/
theorem infiniteFeedbackControllerNext_preserves_invariant
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ)
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ)
    (hinvariant : InfiniteFeedbackStateInvariant target state)
    (hobserved : (observed : Set ℕ) ⊆ target) :
    InfiniteFeedbackStateInvariant target
      (infiniteFeedbackControllerNext state
        (infiniteFeedbackControllerAction components dimensions hdimensions
          state observed)
        (truthfulControllerResponse target
          (infiniteFeedbackControllerAction components dimensions hdimensions
            state observed))) := by
  classical
  cases haction :
      infiniteFeedbackControllerAction components dimensions hdimensions
        state observed with
  | wait =>
      exact hinvariant
  | skip =>
      constructor <;> intro active hactive <;> cases hactive
  | query active candidate =>
      obtain ⟨hindex, hentry, _hcore, _hfresh⟩ :=
        infiniteFeedbackControllerAction_query_spec
          components dimensions hdimensions target state observed
          hinvariant hobserved active candidate haction
      by_cases hresponse :
          truthfulControllerResponse target
              (.query active candidate) =
            some false
      · rw [infiniteFeedbackControllerNext, if_pos hresponse]
        constructor <;> intro current hcurrent <;> cases hcurrent
      · rw [infiniteFeedbackControllerNext, if_neg hresponse]
        constructor
        · intro current hcurrent
          injection hcurrent with hcurrent
          subst current
          exact rfl
        · intro current hcurrent
          injection hcurrent with hcurrent
          subst current
          exact hentry

/-- The truthful run satisfies the active-stage invariant at every time. -/
theorem infiniteFeedbackRunState_invariant
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hstream : GenLimit.Generic.StreamIn stream target) :
    ∀ t,
      InfiniteFeedbackStateInvariant target
        (infiniteFeedbackRunState components dimensions hdimensions
          target stream t) := by
  intro t
  induction t with
  | zero =>
      exact infiniteFeedbackStateInvariant_initial
        components dimensions target
  | succ t ih =>
      rw [infiniteFeedbackRunState_succ]
      exact infiniteFeedbackControllerNext_preserves_invariant
        components dimensions hdimensions target
        (infiniteFeedbackRunState components dimensions hdimensions
          target stream t)
        (observedThrough stream t)
        ih
        (by
          unfold observedThrough
          exact sample_subset_of_streamIn hstream (t + 1))

/-- The outer component index either stays fixed or increases by exactly
one in a single controller round. -/
theorem infiniteFeedbackControllerNext_index_bounds
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ)
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ)
    (hinvariant : InfiniteFeedbackStateInvariant target state)
    (hobserved : (observed : Set ℕ) ⊆ target) :
    state.nextComponent ≤
        (infiniteFeedbackControllerNext state
          (infiniteFeedbackControllerAction components dimensions hdimensions
            state observed)
          (truthfulControllerResponse target
            (infiniteFeedbackControllerAction components dimensions hdimensions
              state observed))).nextComponent ∧
      (infiniteFeedbackControllerNext state
          (infiniteFeedbackControllerAction components dimensions hdimensions
            state observed)
          (truthfulControllerResponse target
            (infiniteFeedbackControllerAction components dimensions hdimensions
              state observed))).nextComponent ≤
        state.nextComponent + 1 := by
  classical
  cases haction :
      infiniteFeedbackControllerAction components dimensions hdimensions
        state observed with
  | wait =>
      exact ⟨le_rfl, Nat.le_succ _⟩
  | skip =>
      exact ⟨Nat.le_succ _, le_rfl⟩
  | query active candidate =>
      have hindex :=
        (infiniteFeedbackControllerAction_query_spec
          components dimensions hdimensions target state observed
          hinvariant hobserved active candidate haction).1
      by_cases hresponse :
          truthfulControllerResponse target
              (.query active candidate) =
            some false
      · rw [infiniteFeedbackControllerNext, if_pos hresponse, hindex]
        exact ⟨Nat.le_succ _, le_rfl⟩
      · rw [infiniteFeedbackControllerNext, if_neg hresponse, hindex]
        exact ⟨le_rfl, Nat.le_succ _⟩

/-- At an index whose component contains the target, the controller cannot
take the inconsistent-component branch. -/
theorem infiniteFeedbackControllerAction_ne_skip_of_target
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ)
    (componentIndex : ℕ)
    (hindex : state.nextComponent = componentIndex)
    {target : Set ℕ}
    (htarget : target ∈ components componentIndex)
    (hobserved : (observed : Set ℕ) ⊆ target) :
    infiniteFeedbackControllerAction components dimensions hdimensions
        state observed ≠
      .skip := by
  classical
  cases hactive : state.active with
  | some active =>
      rw [infiniteFeedbackControllerAction_of_active
        components dimensions hdimensions state observed active hactive]
      exact InfiniteFeedbackControllerAction.noConfusion
  | none =>
      by_cases hlarge :
          dimensions state.nextComponent < observed.card
      · have hconsistent :
            (versionSpace (components state.nextComponent)
              observed).Nonempty := by
          refine ⟨target, ?_, hobserved⟩
          rwa [hindex]
        simp [infiniteFeedbackControllerAction, hactive, hlarge,
          hconsistent]
      · simp [infiniteFeedbackControllerAction, hactive, hlarge]

/-- A query from a component containing the target receives `Yes`: the
frozen common core is a subset of that target. -/
theorem truthfulControllerResponse_query_true_of_target_component
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    {dimensions : ℕ → ℕ}
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ)
    (active : IndexedFeedbackClosureStage components dimensions)
    (candidate : ℕ)
    (htarget : target ∈ components active.index)
    (hentry : (active.entrySample : Set ℕ) ⊆ target)
    (hcore :
      candidate ∈ (active.toClosureStage hdimensions).core) :
    truthfulControllerResponse target (.query active candidate) =
      some true := by
  simp only [truthfulControllerResponse, Option.some.injEq]
  apply (membershipAnswer_eq_true_iff target candidate).mpr
  exact
    (FeedbackClosureStage.core_subset_target
      (active.toClosureStage hdimensions) htarget hentry) hcore

/-- The outer index cannot advance past a component containing the target. -/
theorem infiniteFeedbackControllerNext_index_eq_of_target_component
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ)
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ)
    (hinvariant : InfiniteFeedbackStateInvariant target state)
    (hobserved : (observed : Set ℕ) ⊆ target)
    (componentIndex : ℕ)
    (hindex : state.nextComponent = componentIndex)
    (htarget : target ∈ components componentIndex) :
    (infiniteFeedbackControllerNext state
      (infiniteFeedbackControllerAction components dimensions hdimensions
        state observed)
      (truthfulControllerResponse target
        (infiniteFeedbackControllerAction components dimensions hdimensions
          state observed))).nextComponent =
      componentIndex := by
  classical
  cases haction :
      infiniteFeedbackControllerAction components dimensions hdimensions
        state observed with
  | wait =>
      exact hindex
  | skip =>
      exact False.elim
        ((infiniteFeedbackControllerAction_ne_skip_of_target
          components dimensions hdimensions state observed componentIndex
          hindex htarget hobserved) haction)
  | query active candidate =>
      obtain ⟨hactiveIndex, hentry, hcore, _hfresh⟩ :=
        infiniteFeedbackControllerAction_query_spec
          components dimensions hdimensions target state observed
          hinvariant hobserved active candidate haction
      have htargetActive : target ∈ components active.index := by
        rw [hactiveIndex, hindex]
        exact htarget
      have hresponse :
          truthfulControllerResponse target
              (.query active candidate) =
            some true :=
        truthfulControllerResponse_query_true_of_target_component
          hdimensions target active candidate htargetActive hentry hcore
      rw [infiniteFeedbackControllerNext]
      simp only [hresponse]
      exact hactiveIndex.trans hindex

/-- Outer-loop index of the truthful causal run. -/
noncomputable def infiniteFeedbackRunIndex
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (t : ℕ) : ℕ :=
  (infiniteFeedbackRunState components dimensions hdimensions
    target stream t).nextComponent

theorem infiniteFeedbackRunIndex_succ_bounds
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hstream : GenLimit.Generic.StreamIn stream target)
    (t : ℕ) :
    infiniteFeedbackRunIndex components dimensions hdimensions
        target stream t ≤
      infiniteFeedbackRunIndex components dimensions hdimensions
        target stream (t + 1) ∧
    infiniteFeedbackRunIndex components dimensions hdimensions
        target stream (t + 1) ≤
      infiniteFeedbackRunIndex components dimensions hdimensions
        target stream t + 1 := by
  unfold infiniteFeedbackRunIndex
  rw [infiniteFeedbackRunState_succ]
  apply infiniteFeedbackControllerNext_index_bounds
    components dimensions hdimensions target
    (infiniteFeedbackRunState components dimensions hdimensions
      target stream t)
    (observedThrough stream t)
    (infiniteFeedbackRunState_invariant
      components dimensions hdimensions target stream hstream t)
  unfold observedThrough
  exact sample_subset_of_streamIn hstream (t + 1)

theorem infiniteFeedbackRunIndex_monotone
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hstream : GenLimit.Generic.StreamIn stream target) :
    Monotone
      (infiniteFeedbackRunIndex components dimensions hdimensions
        target stream) := by
  apply monotone_nat_of_le_succ
  intro t
  exact (infiniteFeedbackRunIndex_succ_bounds
    components dimensions hdimensions target stream hstream t).1

/-- A target-containing component is a finite upper bound for the run's
outer-loop index. -/
theorem infiniteFeedbackRunIndex_le_target_component
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hstream : GenLimit.Generic.StreamIn stream target)
    (componentIndex : ℕ)
    (htarget : target ∈ components componentIndex) :
    ∀ t,
      infiniteFeedbackRunIndex components dimensions hdimensions
        target stream t ≤ componentIndex := by
  intro t
  induction t with
  | zero =>
      simp [infiniteFeedbackRunIndex,
        InfiniteFeedbackControllerState.initial]
  | succ t ih =>
      by_cases hstrict :
          infiniteFeedbackRunIndex components dimensions hdimensions
              target stream t <
            componentIndex
      · have hstep :=
          (infiniteFeedbackRunIndex_succ_bounds
            components dimensions hdimensions target stream hstream t).2
        omega
      · have heq :
            infiniteFeedbackRunIndex components dimensions hdimensions
                target stream t =
              componentIndex :=
          Nat.le_antisymm ih (Nat.le_of_not_gt hstrict)
        unfold infiniteFeedbackRunIndex at heq ⊢
        rw [infiniteFeedbackRunState_succ]
        have hstay :=
          infiniteFeedbackControllerNext_index_eq_of_target_component
            components dimensions hdimensions target
            (infiniteFeedbackRunState components dimensions hdimensions
              target stream t)
            (observedThrough stream t)
            (infiniteFeedbackRunState_invariant
              components dimensions hdimensions target stream hstream t)
            (by
              unfold observedThrough
              exact sample_subset_of_streamIn hstream (t + 1))
            componentIndex heq htarget
        simpa only [infiniteFeedbackRunAction] using hstay.le

theorem infiniteFeedbackRunIndex_eventually_constant
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hstream : GenLimit.Generic.StreamIn stream target)
    (componentIndex : ℕ)
    (htarget : target ∈ components componentIndex) :
    ∃ T, ∀ t, T ≤ t →
      infiniteFeedbackRunIndex components dimensions hdimensions
          target stream t =
        infiniteFeedbackRunIndex components dimensions hdimensions
          target stream T :=
  by
    let f := infiniteFeedbackRunIndex components dimensions hdimensions
      target stream
    have hf : Monotone f :=
      infiniteFeedbackRunIndex_monotone
        components dimensions hdimensions target stream hstream
    have hbound : ∀ t, f t ≤ componentIndex :=
      infiniteFeedbackRunIndex_le_target_component
        components dimensions hdimensions target stream hstream
        componentIndex htarget
    obtain ⟨value, T, hconstant⟩ :=
      converges_of_monotone_of_bounded hf hbound
    refine ⟨T, ?_⟩
    intro t ht
    exact (hconstant t ht).trans (hconstant T le_rfl).symm

/-- Once the current positive sample is larger than the active component's
dimension, the controller cannot choose the waiting action. -/
theorem infiniteFeedbackControllerAction_ne_wait_of_large
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ)
    (hlarge :
      dimensions state.nextComponent < observed.card) :
    infiniteFeedbackControllerAction components dimensions hdimensions
        state observed ≠
      .wait := by
  classical
  cases hactive : state.active with
  | some active =>
      rw [infiniteFeedbackControllerAction_of_active
        components dimensions hdimensions state observed active hactive]
      exact InfiniteFeedbackControllerAction.noConfusion
  | none =>
      by_cases hconsistent :
          (versionSpace (components state.nextComponent)
            observed).Nonempty
      · simp [infiniteFeedbackControllerAction, hactive, hlarge,
          hconsistent]
      · simp [infiniteFeedbackControllerAction, hactive, hlarge,
          hconsistent]

/-- Pointwise convergence lemma.  If the sample is large enough and the
outer index does not change across this round, then the action's output is a
fresh target point.  A waiting action is impossible; a skip or negative query
would increase the index; hence the round is a positively answered fresh-core
query. -/
theorem infiniteFeedbackControllerAction_correct_of_large_of_index_eq
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (target : Set ℕ)
    (state : InfiniteFeedbackControllerState components dimensions)
    (observed : Finset ℕ)
    (hinvariant : InfiniteFeedbackStateInvariant target state)
    (hobserved : (observed : Set ℕ) ⊆ target)
    (hlarge :
      dimensions state.nextComponent < observed.card)
    (hindex :
      (infiniteFeedbackControllerNext state
        (infiniteFeedbackControllerAction components dimensions hdimensions
          state observed)
        (truthfulControllerResponse target
          (infiniteFeedbackControllerAction components dimensions hdimensions
            state observed))).nextComponent =
        state.nextComponent) :
    let action :=
      infiniteFeedbackControllerAction components dimensions hdimensions
        state observed
    action.outputValue ∈ target ∧
      action.outputValue ∉ observed := by
  classical
  dsimp only
  cases haction :
      infiniteFeedbackControllerAction components dimensions hdimensions
        state observed with
  | wait =>
      exact False.elim
        ((infiniteFeedbackControllerAction_ne_wait_of_large
          components dimensions hdimensions state observed hlarge)
          haction)
  | skip =>
      rw [haction] at hindex
      simp only [infiniteFeedbackControllerNext] at hindex
      omega
  | query active candidate =>
      obtain ⟨hactiveIndex, _hentry, _hcore, hfresh⟩ :=
        infiniteFeedbackControllerAction_query_spec
          components dimensions hdimensions target state observed
          hinvariant hobserved active candidate haction
      change candidate ∈ target ∧ candidate ∉ observed
      refine ⟨?_, hfresh⟩
      have hnotFalse :
          truthfulControllerResponse target
              (.query active candidate) ≠
            some false := by
        intro hfalse
        rw [haction] at hindex
        rw [infiniteFeedbackControllerNext, if_pos hfalse] at hindex
        have himpossible :
            active.index + 1 = active.index :=
          hindex.trans hactiveIndex.symm
        exact Nat.succ_ne_self active.index himpossible
      have hanswer :
          membershipAnswer target candidate = true := by
        cases hmembership :
            membershipAnswer target candidate with
        | false =>
            exfalso
            apply hnotFalse
            simp [truthfulControllerResponse, hmembership]
        | true =>
            rfl
      exact
        (membershipAnswer_eq_true_iff target candidate).mp hanswer

/-- Algorithm 4 with explicitly chosen finite closure dimensions generates
every target in the countable cover.  This is the complete causal convergence
theorem underlying Theorem 6.3. -/
theorem countable_finiteClosure_cover_generatable_with_feedback
    {C : GenLimit.Generic.LanguageClass ℕ}
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (hcover : IsCountableFeedbackCover C components) :
    GeneratableInLimitWithFeedback C := by
  refine ⟨countableCoverFeedbackGenerator
    components dimensions hdimensions, ?_⟩
  intro target htarget stream henumeration
  have hstream :
      GenLimit.Generic.StreamIn stream target :=
    GenLimit.Generic.streamIn_of_presents henumeration.2
  obtain ⟨componentIndex, htargetComponent⟩ :=
    target_mem_feedbackCover_component hcover htarget
  obtain ⟨T, hconstant⟩ :=
    infiniteFeedbackRunIndex_eventually_constant
      components dimensions hdimensions target stream hstream
      componentIndex htargetComponent
  let stableIndex :=
    infiniteFeedbackRunIndex components dimensions hdimensions
      target stream T
  let threshold := max T (dimensions stableIndex)
  refine ⟨threshold, ?_⟩
  intro t ht
  have hTt : T ≤ t :=
    (le_max_left T (dimensions stableIndex)).trans ht
  have hTsucc : T ≤ t + 1 :=
    hTt.trans (Nat.le_succ t)
  have htIndex :
      infiniteFeedbackRunIndex components dimensions hdimensions
          target stream t =
        stableIndex := by
    exact hconstant t hTt
  have hsuccIndex :
      infiniteFeedbackRunIndex components dimensions hdimensions
          target stream (t + 1) =
        stableIndex := by
    exact hconstant (t + 1) hTsucc
  have hindexStep :
      (infiniteFeedbackControllerNext
        (infiniteFeedbackRunState components dimensions hdimensions
          target stream t)
        (infiniteFeedbackRunAction components dimensions hdimensions
          target stream t)
        (truthfulControllerResponse target
          (infiniteFeedbackRunAction components dimensions hdimensions
            target stream t))).nextComponent =
        (infiniteFeedbackRunState components dimensions hdimensions
          target stream t).nextComponent := by
    have heq := hsuccIndex.trans htIndex.symm
    unfold infiniteFeedbackRunIndex at heq
    rw [infiniteFeedbackRunState_succ] at heq
    exact heq
  have hlarge :
      dimensions
          (infiniteFeedbackRunState components dimensions hdimensions
            target stream t).nextComponent <
        (observedThrough stream t).card := by
    have hdimensionTime : dimensions stableIndex ≤ t :=
      (le_max_right T (dimensions stableIndex)).trans ht
    have hcard :
        (observedThrough stream t).card = t + 1 :=
      observedThrough_card_of_injective stream henumeration.1 t
    unfold infiniteFeedbackRunIndex at htIndex
    rw [htIndex, hcard]
    omega
  have hcorrect :=
    infiniteFeedbackControllerAction_correct_of_large_of_index_eq
      components dimensions hdimensions target
      (infiniteFeedbackRunState components dimensions hdimensions
        target stream t)
      (observedThrough stream t)
      (infiniteFeedbackRunState_invariant
        components dimensions hdimensions target stream hstream t)
      (by
        unfold observedThrough
        exact sample_subset_of_streamIn hstream (t + 1))
      hlarge
      (by
        simpa only [infiniteFeedbackRunAction] using hindexStep)
  unfold FeedbackCorrectAt
  rw [actualFeedbackOutput_countableCover_eq]
  exact hcorrect

/-- Algorithm 4 with explicitly chosen closure dimensions, now in the
paper's literal interface that issues a membership query on every round. -/
theorem countable_finiteClosure_cover_generatable_with_total_feedback
    {C : GenLimit.Generic.LanguageClass ℕ}
    (components : ℕ → GenLimit.Generic.LanguageClass ℕ)
    (dimensions : ℕ → ℕ)
    (hdimensions :
      ∀ i, HasClosureDimension (components i) (dimensions i))
    (hcover : IsCountableFeedbackCover C components) :
    GeneratableInLimitWithTotalFeedback C := by
  have hoptional : GeneratableInLimitWithFeedback C :=
    countable_finiteClosure_cover_generatable_with_feedback
      components dimensions hdimensions hcover
  exact generatableInLimitWithTotalFeedback_of_optional C 0 hoptional

/-! ## Theorem 6.3 and Corollary 6.4 -/

/-- Every component of a feedback cover inherits uniformly unbounded support
from the covered class. -/
theorem feedbackCover_component_uus
    {C : GenLimit.Generic.LanguageClass ℕ}
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    (hUUS : UUS C)
    (hcover : IsCountableFeedbackCover C components)
    (i : ℕ) :
    UUS (components i) := by
  intro target htarget
  apply hUUS target
  rw [hcover]
  exact Set.mem_iUnion.mpr ⟨i, htarget⟩

/-- Theorem 6.3: a countable union of uniformly generatable UUS collections
is generatable in the limit with unrestricted feedback.

The chosen closure dimensions are obtained from the exact Li--Raman--Tewari
characterization; the causal convergence theorem above then verifies
Algorithm 4. -/
theorem theorem_6_3
    {C : GenLimit.Generic.LanguageClass ℕ}
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    (hUUS : UUS C)
    (hcover : IsCountableFeedbackCover C components)
    (hUniform :
      ∀ i, UniformlyGeneratable (components i)) :
    GeneratableInLimitWithFeedback C := by
  have hfinite :
      ∀ i, HasFiniteClosureDimension (components i) := by
    intro i
    exact
      (GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension
        (feedbackCover_component_uus hUUS hcover i)).mp
        (hUniform i)
  choose dimensions hdimensions using hfinite
  exact countable_finiteClosure_cover_generatable_with_feedback
    components dimensions hdimensions hcover

/-- Theorem 6.3 in Definition 6.1's literal mandatory-query interface. -/
theorem theorem_6_3_total_feedback
    {C : GenLimit.Generic.LanguageClass ℕ}
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    (hUUS : UUS C)
    (hcover : IsCountableFeedbackCover C components)
    (hUniform :
      ∀ i, UniformlyGeneratable (components i)) :
    GeneratableInLimitWithTotalFeedback C := by
  exact generatableInLimitWithTotalFeedback_of_optional C 0
    (theorem_6_3 hUUS hcover hUniform)

/-- A countable cover by non-uniformly generatable collections refines to one
countable cover by uniformly generatable collections.  `Nat.pair` flattens
the outer component index and the inner nondecreasing-cover index. -/
theorem nonuniform_feedback_cover_refines_to_uniform
    {C : GenLimit.Generic.LanguageClass ℕ}
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    (hUUS : UUS C)
    (hcover : IsCountableFeedbackCover C components)
    (hNonuniform :
      ∀ i, NonuniformlyGeneratable (components i)) :
    ∃ refined : ℕ → GenLimit.Generic.LanguageClass ℕ,
      IsCountableFeedbackCover C refined ∧
        ∀ k, UniformlyGeneratable (refined k) := by
  have hdecompose :
      ∀ i,
        ∃ inner : ℕ → GenLimit.Generic.LanguageClass ℕ,
          IsNondecreasingCover (components i) inner ∧
            ∀ n, UniformlyGeneratable (inner n) := by
    intro i
    exact GenLimit.LiRamanTewari.nonuniform_characterization_necessity
      (feedbackCover_component_uus hUUS hcover i)
      (hNonuniform i)
  choose inner hinner using hdecompose
  let refined : ℕ → GenLimit.Generic.LanguageClass ℕ :=
    fun k => inner k.unpair.1 k.unpair.2
  refine ⟨refined, ?_, ?_⟩
  · unfold IsCountableFeedbackCover
    ext target
    constructor
    · intro htarget
      have houter : target ∈ ⋃ i, components i := by
        rwa [← hcover]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp houter
      have hinnerUnion : target ∈ ⋃ n, inner i n := by
        rwa [← (hinner i).1.2]
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hinnerUnion
      apply Set.mem_iUnion.mpr
      refine ⟨Nat.pair i n, ?_⟩
      change
        target ∈
          inner (Nat.unpair (Nat.pair i n)).1
            (Nat.unpair (Nat.pair i n)).2
      simpa only [Nat.unpair_pair] using hn
    · intro hrefined
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hrefined
      have hcomponent :
          target ∈ components k.unpair.1 := by
        rw [(hinner k.unpair.1).1.2]
        exact Set.mem_iUnion.mpr ⟨k.unpair.2, hk⟩
      rw [hcover]
      exact Set.mem_iUnion.mpr ⟨k.unpair.1, hcomponent⟩
  · intro k
    exact (hinner k.unpair.1).2 k.unpair.2

/-- Corollary 6.4: a countable union of non-uniformly generatable UUS
collections is generatable in the limit with unrestricted feedback. -/
theorem corollary_6_4
    {C : GenLimit.Generic.LanguageClass ℕ}
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    (hUUS : UUS C)
    (hcover : IsCountableFeedbackCover C components)
    (hNonuniform :
      ∀ i, NonuniformlyGeneratable (components i)) :
    GeneratableInLimitWithFeedback C := by
  obtain ⟨refined, hrefinedCover, hrefinedUniform⟩ :=
    nonuniform_feedback_cover_refines_to_uniform
      hUUS hcover hNonuniform
  exact theorem_6_3 hUUS hrefinedCover hrefinedUniform

/-- Corollary 6.4 in Definition 6.1's literal mandatory-query interface. -/
theorem corollary_6_4_total_feedback
    {C : GenLimit.Generic.LanguageClass ℕ}
    {components : ℕ → GenLimit.Generic.LanguageClass ℕ}
    (hUUS : UUS C)
    (hcover : IsCountableFeedbackCover C components)
    (hNonuniform :
      ∀ i, NonuniformlyGeneratable (components i)) :
    GeneratableInLimitWithTotalFeedback C := by
  exact generatableInLimitWithTotalFeedback_of_optional C 0
    (corollary_6_4 hUUS hcover hNonuniform)

end GenLimit.NoiseLossFeedback
