import GenLimit.Paper27_FeedbackQueriesAndMistakes.ElementMistake

/-!
# Exact set-valued mistake feedback

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*Language Generation with Feedback: Queries and Mistakes*,
ICML 2026, Definition 3, Theorem 3.2, and Appendix A.1.

This file formalizes the paper's set-valued mistake interaction.  A
set-based strategy always emits an infinite set.  Its feedback bit does
**not** certify that whole set: Definition 3 evaluates only the canonical
first element of the set, using exactly the element-valued membership and
freshness bit.  Eventual success still requires the entire output set to
lie in the target minus the positive history.

The projection which replaces every set output by its canonical first
element has the same replayed transcript, as proved from equality of the two
independently defined updates.  This proves the set-to-element direction of
Theorem 3.2.  Conversely, Appendix A.1's
countable-inner-cover strategy outputs the active cover with the finitely
many observed samples removed.  Its canonical first element is exactly the
already checked cover-search element strategy, so the existing phase proof
also proves eventual correctness of the whole set output.

No computability, running-time, noisy-feedback, or corrupted-example claim
is made.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic
open GenLimit.Angluin

/-! ## Definition 3: the exact first-element set interaction -/

/-- A source-faithful set-valued strategy.  The source's term
`set-based generator` requires every output, on every finite transcript, to
be infinite. -/
structure SourceSetMistakeStrategy (α : Type*) where
  output : List α → List Bool → Set α
  infinite_output :
    ∀ samples bits, (output samples bits).Infinite

/-- The canonical first member of a set strategy's current infinite output. -/
noncomputable def sourceSetFirst
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (samples : List α) (bits : List Bool) : α :=
  sourceFirst (strategy.output samples bits)
    (strategy.infinite_output samples bits).nonempty

theorem sourceSetFirst_mem
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (samples : List α) (bits : List Bool) :
    sourceSetFirst strategy samples bits ∈
      strategy.output samples bits := by
  classical
  exact sourceFirst_mem _ _

/-- Replace every set output by the source's canonical first element. -/
noncomputable def sourceSetFirstElementStrategy
    [Countable α]
    (strategy : SourceSetMistakeStrategy α) :
    SourceElementMistakeStrategy α :=
  fun samples bits => sourceSetFirst strategy samples bits

/-- Definition 3's set-output feedback bit.  Only the canonical first
member is evaluated, using the same membership-and-freshness predicate as
for an element-valued generator. -/
noncomputable def sourceSetReply
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α)
    (bits : List Bool) : Bool :=
  sourceElementReply target samples
    (sourceSetFirst strategy samples bits)

theorem sourceSetReply_eq_sourceElementReply
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α)
    (bits : List Bool) :
    sourceSetReply strategy target samples bits =
      sourceElementReply target samples
        (sourceSetFirstElementStrategy strategy samples bits) :=
  rfl

theorem sourceSetReply_eq_true_iff
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α)
    (bits : List Bool) :
    sourceSetReply strategy target samples bits = true ↔
      sourceSetFirst strategy samples bits ∈ target ∧
        sourceSetFirst strategy samples bits ∉ samples := by
  exact sourceElementReply_eq_true_iff _ _ _

/-- One input update for the set-valued interaction.  The first positive
example arrives before any output.  At every later example, the appended bit
evaluates the canonically selected first member of the preceding set output. -/
noncomputable def sourceSetFeedbackStep
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α)
    (state : List α × List Bool) (next : α) :
    List α × List Bool := by
  classical
  if h : state.1 = [] then
    exact ([next], state.2)
  else
    exact
      (state.1 ++ [next],
        state.2 ++
          [sourceSetReply strategy target state.1 state.2])

/-- The unique truthful set-feedback replay on an ordered positive history.
Unlike the projected element interaction below, this is an independent
recursive definition of the source set interaction. -/
noncomputable def sourceSetFeedbackRun
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) :
    List α × List Bool :=
  samples.foldl
    (sourceSetFeedbackStep strategy target) ([], [])

/-- The preceding first-element feedback bits visible at this history. -/
noncomputable def sourceSetFeedback
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) : List Bool :=
  (sourceSetFeedbackRun strategy target samples).2

/-- The set step and the projected element step agree on every explicit
interaction state.  This is the local transcript invariant behind the direct
conversion in Theorem 3.2. -/
theorem sourceSetFeedbackStep_eq_sourceElementFeedbackStep
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α)
    (state : List α × List Bool) (next : α) :
    sourceSetFeedbackStep strategy target state next =
      sourceElementFeedbackStep
        (sourceSetFirstElementStrategy strategy) target state next := by
  classical
  simp only [sourceSetFeedbackStep, sourceElementFeedbackStep]
  split_ifs <;> rfl

/-- Full replay synchronization for the set-to-element conversion used in
Theorem 3.2.  This is a proved equality between independently recursive
interactions, rather than an equality obtained by defining one through the
other. -/
theorem sourceSetFeedbackRun_eq_sourceElementFeedbackRun
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) :
    sourceSetFeedbackRun strategy target samples =
      sourceElementFeedbackRun
        (sourceSetFirstElementStrategy strategy) target samples := by
  classical
  unfold sourceSetFeedbackRun sourceElementFeedbackRun
  apply congrArg (fun step => samples.foldl step ([], []))
  funext state next
  exact
    sourceSetFeedbackStep_eq_sourceElementFeedbackStep
      strategy target state next

/-- Replaying a set strategy preserves the supplied ordered positive history. -/
@[simp] theorem sourceSetFeedbackRun_fst
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) :
    (sourceSetFeedbackRun strategy target samples).1 = samples := by
  rw [sourceSetFeedbackRun_eq_sourceElementFeedbackRun]
  exact sourceElementFeedbackRun_fst _ _ _

/-- Replay synchronization for the Boolean transcript used in Theorem 3.2. -/
@[simp] theorem sourceSetFeedback_eq_sourceElementFeedback
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) :
    sourceSetFeedback strategy target samples =
      sourceElementFeedback
        (sourceSetFirstElementStrategy strategy) target samples := by
  exact congrArg Prod.snd
    (sourceSetFeedbackRun_eq_sourceElementFeedbackRun
      strategy target samples)

/-- The set transcript obeys the same causal append recurrence as the source
element transcript. -/
theorem sourceSetFeedback_append
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) (next : α)
    (hsamples : samples ≠ []) :
    sourceSetFeedback strategy target (samples ++ [next]) =
      sourceSetFeedback strategy target samples ++
        [sourceSetReply strategy target samples
          (sourceSetFeedback strategy target samples)] := by
  rw [sourceSetFeedback_eq_sourceElementFeedback,
    sourceElementFeedback_append _ _ _ _ hsamples,
    sourceSetFeedback_eq_sourceElementFeedback]
  rfl

/-- Set strategies with the same canonical first-element projection are
observationally indistinguishable to the source feedback channel. -/
theorem sourceSetFeedbackRun_eq_of_firstElementStrategy_eq
    [Countable α]
    (left right : SourceSetMistakeStrategy α)
    (hfirst :
      sourceSetFirstElementStrategy left =
        sourceSetFirstElementStrategy right)
    (target : Set α) (samples : List α) :
    sourceSetFeedbackRun left target samples =
      sourceSetFeedbackRun right target samples := by
  rw [sourceSetFeedbackRun_eq_sourceElementFeedbackRun,
    sourceSetFeedbackRun_eq_sourceElementFeedbackRun, hfirst]

theorem sourceSetFeedback_eq_of_firstElementStrategy_eq
    [Countable α]
    (left right : SourceSetMistakeStrategy α)
    (hfirst :
      sourceSetFirstElementStrategy left =
        sourceSetFirstElementStrategy right)
    (target : Set α) (samples : List α) :
    sourceSetFeedback left target samples =
      sourceSetFeedback right target samples := by
  exact congrArg Prod.snd
    (sourceSetFeedbackRun_eq_of_firstElementStrategy_eq
      left right hfirst target samples)

/-- The infinite set emitted after the given ordered positive history. -/
noncomputable def sourceSetOutput
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) : Set α :=
  strategy.output samples
    (sourceSetFeedback strategy target samples)

theorem sourceSetOutput_infinite
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) :
    (sourceSetOutput strategy target samples).Infinite :=
  strategy.infinite_output _ _

/-- The canonical first member of the actual set output on a truthful run. -/
noncomputable def sourceSetFirstOutput
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) : α :=
  sourceSetFirst strategy samples
    (sourceSetFeedback strategy target samples)

theorem sourceSetFirstOutput_mem
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) :
    sourceSetFirstOutput strategy target samples ∈
      sourceSetOutput strategy target samples := by
  exact sourceSetFirst_mem _ _ _

/-- The projected element output and the first member of the set output are
identical on the synchronized truthful transcript. -/
@[simp] theorem sourceSetFirstOutput_eq_sourceElementOutput
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) :
    sourceSetFirstOutput strategy target samples =
      sourceElementOutput
        (sourceSetFirstElementStrategy strategy) target samples :=
  rfl

/-- Definition 3's set success clause at one history: every emitted element
is both valid and unseen.  Infinitude is carried globally by the strategy. -/
def SourceSetMistakeCorrect
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) (samples : List α) : Prop :=
  sourceSetOutput strategy target samples ⊆
    target \ {x | x ∈ samples}

def SourceSetMistakeSucceedsOn
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (target : Set α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream target →
    ∃ T, ∀ t, T ≤ t →
      SourceSetMistakeCorrect strategy target
        (streamPrefix stream t)

def SourceSetMistakeGenerates
    [Countable α]
    (strategy : SourceSetMistakeStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → SourceSetMistakeSucceedsOn strategy L

def SourceSetMistakeGeneratable
    [Countable α]
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : SourceSetMistakeStrategy α,
    SourceSetMistakeGenerates strategy targets

/-! ## Theorem 3.2, set outputs imply element outputs -/

/-- Appendix A.1's direct conversion.  The preceding synchronization theorem
proves that both independently recursive models evaluate the same canonical
first element at every round. -/
theorem sourceSetMistake_implies_sourceElementMistake
    [Countable α]
    {targets : LanguageClass α}
    (hset : SourceSetMistakeGeneratable targets) :
    SourceElementMistakeGeneratable targets := by
  obtain ⟨strategy, hstrategy⟩ := hset
  refine ⟨sourceSetFirstElementStrategy strategy, ?_⟩
  intro L hL stream hPresents
  obtain ⟨T, hT⟩ := hstrategy L hL stream hPresents
  refine ⟨T, ?_⟩
  intro t hTt
  have hcorrect := hT t hTt
  have hfirst :=
    hcorrect
      (sourceSetFirstOutput_mem strategy L
        (streamPrefix stream t))
  simpa [SourceElementMistakeCorrect,
    sourceSetFirstOutput_eq_sourceElementOutput] using hfirst

/-! ## Theorem 3.2, inner-cover set strategy -/

/-- Appendix A.1's source set strategy.  The active cover index is the
number of preceding negative first-element replies; the output removes the
finite positive history from that cover. -/
noncomputable def innerCoverSourceSetStrategy
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    SourceSetMistakeStrategy α := by
  classical
  refine
    { output := fun samples bits =>
        inner.cover (bits.count false) \
          ((Generic.sequenceSample samples.get : Finset α) : Set α)
      infinite_output := ?_ }
  intro samples bits
  exact
    (inner.infinite_cover (bits.count false)).diff
      (Generic.sequenceSample samples.get).finite_toSet

/-- The implementation's finset subtraction is extensionally the literal
source output: the active cover with every element of the ordered history
removed. -/
theorem innerCoverSourceSetStrategy_output_eq_listDiff
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (samples : List α) (bits : List Bool) :
    (innerCoverSourceSetStrategy inner).output samples bits =
      inner.cover (bits.count false) \ {x | x ∈ samples} := by
  ext x
  simp only [innerCoverSourceSetStrategy, Set.mem_diff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxCover, hxFresh⟩
    exact
      ⟨hxCover, fun hxSamples =>
        hxFresh
          (source_mem_sequenceSample_list_get_iff.mpr hxSamples)⟩
  · rintro ⟨hxCover, hxFresh⟩
    exact
      ⟨hxCover, fun hxFinset =>
        hxFresh
          (source_mem_sequenceSample_list_get_iff.mp hxFinset)⟩

/-- The first-element projection of the source set strategy is exactly the
already checked Appendix A.1 element cover-search strategy. -/
theorem innerCoverSourceSet_firstElementStrategy
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    sourceSetFirstElementStrategy
        (innerCoverSourceSetStrategy inner) =
      innerCoverSourceElementStrategy inner := by
  funext samples bits
  rfl

/-- The independently recursive cover-set interaction and the checked cover
element interaction have identical full states at every ordered history. -/
theorem innerCoverSourceSet_feedbackRun_eq
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (samples : List α) :
    sourceSetFeedbackRun
        (innerCoverSourceSetStrategy inner) target samples =
      sourceElementFeedbackRun
        (innerCoverSourceElementStrategy inner) target samples := by
  rw [sourceSetFeedbackRun_eq_sourceElementFeedbackRun,
    innerCoverSourceSet_firstElementStrategy]

/-- Consequently, both cover strategies see the same truthful transcript
on every ordered history. -/
theorem innerCoverSourceSet_feedback_eq
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (samples : List α) :
    sourceSetFeedback
        (innerCoverSourceSetStrategy inner) target samples =
      sourceElementFeedback
        (innerCoverSourceElementStrategy inner) target samples := by
  rw [sourceSetFeedback_eq_sourceElementFeedback,
    innerCoverSourceSet_firstElementStrategy]

/-- On their synchronized transcripts, the canonical first member of the
cover-set witness is exactly the cover-element witness's output. -/
theorem innerCoverSourceSet_firstOutput_eq
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (samples : List α) :
    sourceSetFirstOutput
        (innerCoverSourceSetStrategy inner) target samples =
      sourceElementOutput
        (innerCoverSourceElementStrategy inner) target samples := by
  rw [sourceSetFirstOutput_eq_sourceElementOutput,
    innerCoverSourceSet_firstElementStrategy]

/-- Exact output formula for the source cover-based set strategy. -/
theorem innerCoverSourceSet_output_eq
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (samples : List α) :
    sourceSetOutput
        (innerCoverSourceSetStrategy inner) target samples =
      inner.cover
          ((sourceElementFeedback
            (innerCoverSourceElementStrategy inner)
            target samples).count false) \
        ((Generic.sequenceSample samples.get : Finset α) : Set α) := by
  unfold sourceSetOutput
  rw [innerCoverSourceSet_feedback_eq]
  rfl

/-- Appendix A.1's countable-inner-cover construction yields a faithful
set-valued mistake generator, not the stronger whole-set-feedback model. -/
theorem countableInnerCover_implies_sourceSetMistake
    [Countable α]
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    SourceSetMistakeGeneratable targets := by
  classical
  let inner := Nonempty.some hinner
  refine ⟨innerCoverSourceSetStrategy inner, ?_⟩
  intro L hL stream hPresents
  let hexists : ∃ i, inner.cover i ⊆ L :=
    inner.contained L hL
  let k := Nat.find hexists
  have hgood : inner.cover k ⊆ L := by
    simpa [k] using Nat.find_spec hexists
  have hminimal : ∀ i, i < k → ¬ inner.cover i ⊆ L := by
    intro i hi
    exact Nat.find_min hexists (by simpa [k] using hi)
  obtain ⟨T, _hTpos, hphaseT⟩ :=
    innerCoverSourceElement_eventually_reaches
      inner L stream hPresents k hgood hminimal
  refine ⟨T, ?_⟩
  intro t hTt
  have hphaseLower :
      k ≤ sourceElementPhase
        (innerCoverSourceElementStrategy inner) L stream t := by
    rw [← hphaseT]
    exact sourceElementPhase_mono
      (innerCoverSourceElementStrategy inner) L stream hTt
  have hphaseUpper :=
    innerCoverSourceElement_phase_le_good inner L stream k hgood t
  have hphase :
      sourceElementPhase
        (innerCoverSourceElementStrategy inner) L stream t = k :=
    Nat.le_antisymm hphaseUpper hphaseLower
  intro x hx
  rw [innerCoverSourceSet_output_eq] at hx
  change
    x ∈
      inner.cover
          (sourceElementPhase
            (innerCoverSourceElementStrategy inner) L stream t) \
        ((Generic.sequenceSample
          (streamPrefix stream t).get : Finset α) : Set α) at hx
  rw [hphase] at hx
  exact
    ⟨hgood hx.1,
      fun hmem =>
        hx.2
          (source_mem_sequenceSample_list_get_iff.mpr hmem)⟩

/-! ## Exact source Theorem 3.2 -/

/-- Source Theorem 3.2 at the semantic/classical boundary: for classes of
infinite languages over a countable universe, source-faithful set-valued and
element-valued mistake-feedback generation are equivalent. -/
theorem theorem_3_2_setElementMistake_equivalence
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    SourceSetMistakeGeneratable targets ↔
      SourceElementMistakeGeneratable targets := by
  constructor
  · exact sourceSetMistake_implies_sourceElementMistake
  · intro helement
    apply countableInnerCover_implies_sourceSetMistake
    exact sourceElementMistake_implies_countableInnerCover
      hinfinite helement

end GenLimit.FeedbackQueries
