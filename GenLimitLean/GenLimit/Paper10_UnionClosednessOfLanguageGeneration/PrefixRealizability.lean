import GenLimit.Core.Identification
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Definitions
import Mathlib.Data.List.OfFn
import Mathlib.Order.WellFounded

/-!
# Appendix A.2: deterministic prefix-realizability framework

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation*,
arXiv:2506.18642v1, Appendix A.2.

Appendix A.2 describes a general alternating lower-bound pattern in prose:
every finite adversarial prefix can be continued inside the next component
class while avoiding previously recorded generator outputs, and the limit of
infinitely many switches is again a language in the ambient class.

This file gives that deterministic argument a precise, universe-generic
form.  It does not model randomized generators and makes no computability or
runtime claim.  The final theorem keeps the infinite-limit membership
condition explicit; prefix realizability alone cannot imply it.
-/

namespace GenLimit.UnionClosedness.PrefixRealizability

open GenLimit.Generic
open GenLimit.UnionClosedness

variable {α : Type*}

/-- The values occurring in a finite ordered history, without imposing a
decidable-equality instance on the alphabet. -/
def historyCarrier (history : List α) : Set α :=
  Set.range history.get

theorem mem_historyCarrier_iff
    {history : List α} {x : α} :
    x ∈ historyCarrier history ↔
      ∃ i : Fin history.length, history.get i = x :=
  Iff.rfl

/-- A stream agrees with an ordered finite history on every history
coordinate. -/
def StreamExtendsHistory
    (stream : Stream α) (history : List α) : Prop :=
  ∀ i : Fin history.length, stream i = history.get i

/-- Appendix-local name for the shared ordered prefix. -/
abbrev streamPrefix (stream : Stream α) (t : ℕ) : List α :=
  GenLimit.textPrefix stream t

@[simp] theorem streamPrefix_length
    (stream : Stream α) (t : ℕ) :
    (streamPrefix stream t).length = t := by
  simp [streamPrefix]

@[simp] theorem streamPrefix_get
    (stream : Stream α) (t : ℕ) (i : Fin t) :
    (streamPrefix stream t).get
        ⟨i, by simp [streamPrefix]⟩ =
      stream i := by
  have heq := GenLimit.textPrefix_eq_ofFn stream t
  have hget := congrArg (fun xs : List α => xs[i.val]?) heq
  simpa using hget

theorem streamPrefix_nodup
    {stream : Stream α}
    (hinjective : Function.Injective stream) (t : ℕ) :
    (streamPrefix stream t).Nodup := by
  rw [streamPrefix, GenLimit.textPrefix_eq_ofFn]
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply Fin.ext
  exact hinjective hij

theorem streamPrefix_historyCarrier_subset_range
    (stream : Stream α) (t : ℕ) :
    historyCarrier (streamPrefix stream t) ⊆
      Set.range stream := by
  rintro x ⟨i, hi⟩
  refine ⟨i.val, ?_⟩
  rw [List.get_eq_getElem] at hi
  simpa [streamPrefix, GenLimit.textPrefix] using hi

theorem streamPrefix_extends
    {stream : Stream α} {history : List α}
    (hextends : StreamExtendsHistory stream history)
    {t : ℕ} (hlength : history.length ≤ t) :
    history <+: streamPrefix stream t := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by simpa using hlength, ?_⟩
  intro i hi
  have hit : i < t := lt_of_lt_of_le hi hlength
  have hprefix := GenLimit.textPrefix_eq_ofFn stream t
  have hget := congrArg (fun xs : List α => xs[i]?) hprefix
  have hvalue : (streamPrefix stream t)[i]? = some (stream i) := by
    simpa [streamPrefix, hit] using hget
  have hhistory : history[i]? = some (stream i) := by
    simpa [hi] using congrArg some (hextends ⟨i, hi⟩).symm
  simpa [hi, hit] using hhistory.trans hvalue.symm

theorem historyCarrier_prefix_subset
    {first second : List α} (hprefix : first <+: second) :
    historyCarrier first ⊆ historyCarrier second := by
  rintro x ⟨i, hi⟩
  have hilength : i.val < second.length :=
    lt_of_lt_of_le i.isLt hprefix.length_le
  refine ⟨⟨i, hilength⟩, ?_⟩
  rw [List.get_eq_getElem] at hi
  exact (hprefix.getElem i.isLt).symm.trans hi

/-- Evaluate a prefix-based generator directly on a finite list. -/
def outputOnHistory
    (G : Generator α) (history : List α) : α :=
  GenLimit.learnerOfFiniteHistory G history

theorem outputOnHistory_streamPrefix
    (G : Generator α) (stream : Stream α) (t : ℕ) :
    outputOnHistory G (streamPrefix stream t) =
      output G stream t := by
  simpa [outputOnHistory, output] using
    GenLimit.learnerOfFiniteHistory_textPrefix G stream t

/-- Ordinary prefix realizability: some injective exact presentation of a
component language extends the supplied finite ordered history. -/
def PrefixRealizable
    (C : LanguageClass α) (history : List α) : Prop :=
  ∃ stream : Stream α,
    Function.Injective stream ∧
      StreamExtendsHistory stream history ∧
      Set.range stream ∈ C

/-- The switching property needed by the diagonal: the continuation also
avoids every generator output already marked as forbidden. -/
def PrefixRealizableAvoiding
    (C : LanguageClass α) (history : List α)
    (forbidden : Set α) : Prop :=
  ∃ stream : Stream α,
    Function.Injective stream ∧
      StreamExtendsHistory stream history ∧
      Set.range stream ∈ C ∧
      Disjoint (Set.range stream) forbidden

theorem PrefixRealizableAvoiding.prefixRealizable
    {C : LanguageClass α} {history : List α}
    {forbidden : Set α}
    (h : PrefixRealizableAvoiding C history forbidden) :
    PrefixRealizable C history := by
  obtain ⟨stream, hinjective, hextends, hclass, _⟩ := h
  exact ⟨stream, hinjective, hextends, hclass⟩

/-- A valid adversarial state: its ordered history is repetition-free and
contains none of the outputs already committed to be omitted. -/
structure AvoidingPrefixState (α : Type*) where
  history : List α
  forbidden : Set α
  history_nodup : history.Nodup
  history_forbidden_disjoint :
    Disjoint (historyCarrier history) forbidden

def initialState : AvoidingPrefixState α where
  history := []
  forbidden := ∅
  history_nodup := by simp
  history_forbidden_disjoint := by simp [historyCarrier]

/-- One generator-forced extension of a realizable prefix.  The next
history is strictly longer, remains repetition-free, and records the
current generator output in its enlarged forbidden set. -/
structure ForcedPrefixTransition
    (G : Generator α) (state : AvoidingPrefixState α) where
  next : AvoidingPrefixState α
  extends_history : state.history <+: next.history
  strict_growth : state.history.length < next.history.length
  forbidden_subset : state.forbidden ⊆ next.forbidden
  omittedOutput : α
  omitted_not_old_forbidden : omittedOutput ∉ state.forbidden
  omitted_mem_next_forbidden : omittedOutput ∈ next.forbidden
  output_on_next_history :
    outputOnHistory G next.history = omittedOutput

/-- Local deterministic prefix-realizability lemma.  Eventual correctness
on one injective completion forces a strictly longer finite prefix and a
fresh valid output; adding that output to the forbidden set produces the
next valid adversarial state. -/
theorem exists_forcedPrefixTransition
    (G : Generator α) (C : LanguageClass α)
    (state : AvoidingPrefixState α)
    (hG : IsLimitGeneratorOnInjectivePresentations G C)
    (hrealizable :
      PrefixRealizableAvoiding C
        state.history state.forbidden) :
    Nonempty (ForcedPrefixTransition G state) := by
  classical
  obtain
    ⟨completion, hcompletionInjective, hcompletionExtends,
      hcompletionClass, hcompletionAvoids⟩ :=
    hrealizable
  obtain ⟨threshold, hcorrect⟩ :=
    hG (Set.range completion) hcompletionClass completion
      hcompletionInjective rfl
  let transitionTime :=
    max threshold (state.history.length + 1)
  have hthreshold : threshold ≤ transitionTime :=
    Nat.le_max_left _ _
  have hhistory_lt :
      state.history.length < transitionTime := by
    dsimp only [transitionTime]
    omega
  have hcorrectAt :
      CorrectAt G (Set.range completion)
        completion transitionTime :=
    hcorrect transitionTime hthreshold
  let nextHistory := streamPrefix completion transitionTime
  let omitted := output G completion transitionTime
  have hnextNodup : nextHistory.Nodup :=
    streamPrefix_nodup hcompletionInjective transitionTime
  have hnextExtends :
      state.history <+: nextHistory :=
    streamPrefix_extends hcompletionExtends
      (Nat.le_of_lt hhistory_lt)
  have hnextAvoidsOld :
      Disjoint (historyCarrier nextHistory)
        state.forbidden := by
    rw [Set.disjoint_left]
    intro x hxHistory hxForbidden
    exact Set.disjoint_left.mp hcompletionAvoids
      (streamPrefix_historyCarrier_subset_range
        completion transitionTime hxHistory)
      hxForbidden
  have homittedNotNext :
      omitted ∉ historyCarrier nextHistory := by
    rintro ⟨i, hi⟩
    apply hcorrectAt.2
    apply GenLimit.Generic.mem_sample_iff.mpr
    have hiTime : i.val < transitionTime := by
      simpa [nextHistory] using i.isLt
    refine ⟨i, hiTime, ?_⟩
    rw [List.get_eq_getElem] at hi
    have hprefixValue :
        (streamPrefix completion transitionTime)[i.val] =
          completion i.val := by
      exact streamPrefix_get completion transitionTime
        ⟨i.val, hiTime⟩
    simpa [nextHistory, omitted, hprefixValue] using hi
  have homittedNotOld :
      omitted ∉ state.forbidden := by
    intro homittedForbidden
    exact Set.disjoint_left.mp hcompletionAvoids
      hcorrectAt.1 homittedForbidden
  let nextForbidden := insert omitted state.forbidden
  have hnextAvoids :
      Disjoint (historyCarrier nextHistory)
        nextForbidden := by
    rw [Set.disjoint_left]
    intro x hxHistory hxForbidden
    rcases hxForbidden with rfl | hxOld
    · exact homittedNotNext hxHistory
    · exact Set.disjoint_left.mp hnextAvoidsOld
        hxHistory hxOld
  let next : AvoidingPrefixState α := {
    history := nextHistory
    forbidden := nextForbidden
    history_nodup := hnextNodup
    history_forbidden_disjoint := hnextAvoids
  }
  refine ⟨{
    next := next
    extends_history := hnextExtends
    strict_growth := by
      simpa [next, nextHistory] using hhistory_lt
    forbidden_subset := by
      intro x hx
      exact Or.inr hx
    omittedOutput := omitted
    omitted_not_old_forbidden := homittedNotOld
    omitted_mem_next_forbidden := Or.inl rfl
    output_on_next_history := by
      simpa [next, nextHistory, omitted] using
        outputOnHistory_streamPrefix
          G completion transitionTime
  }⟩

/-- Abstract Appendix A.2 data.  `phaseClass n` is the component used at
phase `n`; `Eligible` carries any construction-specific prefix invariant.
Every eligible prefix is realizable in that component while avoiding the
current forbidden set, and every forced transition preserves eligibility.
-/
structure Scheme
    (ambient : LanguageClass α) where
  phaseClass : ℕ → LanguageClass α
  phaseClass_subset :
    ∀ phase, phaseClass phase ⊆ ambient
  Eligible : ℕ → AvoidingPrefixState α → Prop
  initial_eligible : Eligible 0 initialState
  realizes :
    ∀ phase state, Eligible phase state →
      PrefixRealizableAvoiding (phaseClass phase)
        state.history state.forbidden
  preserves_eligible :
    ∀ (G : Generator α) phase state,
      Eligible phase state →
      ∀ transition : ForcedPrefixTransition G state,
        Eligible (phase + 1) transition.next

/-- A state bundled with the scheme-specific invariant for its phase. -/
structure SchemeState
    {ambient : LanguageClass α}
    (scheme : Scheme ambient) (phase : ℕ) where
  state : AvoidingPrefixState α
  eligible : scheme.Eligible phase state

def initialSchemeState
    {ambient : LanguageClass α}
    (scheme : Scheme ambient) :
    SchemeState scheme 0 where
  state := initialState
  eligible := scheme.initial_eligible

theorem exists_schemeTransition
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient)
    (phase : ℕ) (current : SchemeState scheme phase) :
    Nonempty (ForcedPrefixTransition G current.state) := by
  apply exists_forcedPrefixTransition
    G (scheme.phaseClass phase) current.state
  · intro L hL stream hinjective hpresents
    exact hG L (scheme.phaseClass_subset phase hL)
      stream hinjective hpresents
  · exact scheme.realizes phase current.state current.eligible

noncomputable def selectedTransition
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient)
    (phase : ℕ) (current : SchemeState scheme phase) :
    ForcedPrefixTransition G current.state :=
  Classical.choice
    (exists_schemeTransition G hG scheme phase current)

noncomputable def advanceSchemeState
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient)
    (phase : ℕ) (current : SchemeState scheme phase) :
    SchemeState scheme (phase + 1) := by
  let transition :=
    selectedTransition G hG scheme phase current
  exact {
    state := transition.next
    eligible :=
      scheme.preserves_eligible G phase current.state
        current.eligible transition
  }

/-- Classical dependent-choice iteration of the forced finite-prefix
transition. -/
noncomputable def stateAt
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) :
    (phase : ℕ) → SchemeState scheme phase
  | 0 => initialSchemeState scheme
  | phase + 1 =>
      advanceSchemeState G hG scheme phase
        (stateAt G hG scheme phase)

theorem stateAt_succ_state
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    (stateAt G hG scheme (phase + 1)).state =
      (selectedTransition G hG scheme phase
        (stateAt G hG scheme phase)).next := by
  rfl

theorem stateAt_history_prefix_succ
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    (stateAt G hG scheme phase).state.history <+:
      (stateAt G hG scheme (phase + 1)).state.history := by
  rw [stateAt_succ_state]
  exact
    (selectedTransition G hG scheme phase
      (stateAt G hG scheme phase)).extends_history

theorem stateAt_history_strict_succ
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    (stateAt G hG scheme phase).state.history.length <
      (stateAt G hG scheme (phase + 1)).state.history.length := by
  rw [stateAt_succ_state]
  exact
    (selectedTransition G hG scheme phase
      (stateAt G hG scheme phase)).strict_growth

theorem stateAt_history_prefix
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient)
    {first later : ℕ} (hle : first ≤ later) :
    (stateAt G hG scheme first).state.history <+:
      (stateAt G hG scheme later).state.history := by
  induction later, hle using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ later _ ih =>
      exact ih.trans
        (stateAt_history_prefix_succ G hG scheme later)

theorem stateAt_history_length_lower
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    phase ≤
      (stateAt G hG scheme phase).state.history.length := by
  induction phase with
  | zero => simp
  | succ phase ih =>
      have hgrowth :=
        stateAt_history_strict_succ G hG scheme phase
      omega

theorem stateAt_forbidden_subset_succ
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    (stateAt G hG scheme phase).state.forbidden ⊆
      (stateAt G hG scheme (phase + 1)).state.forbidden := by
  rw [stateAt_succ_state]
  exact
    (selectedTransition G hG scheme phase
      (stateAt G hG scheme phase)).forbidden_subset

theorem stateAt_forbidden_mono
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient)
    {first later : ℕ} (hle : first ≤ later) :
    (stateAt G hG scheme first).state.forbidden ⊆
      (stateAt G hG scheme later).state.forbidden := by
  induction later, hle using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ later _ ih =>
      exact fun x hx =>
        stateAt_forbidden_subset_succ G hG scheme later
          (ih hx)

/-- The output time associated with phase `n`: the length of the newly
forced history. -/
noncomputable def transitionTime
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) : ℕ :=
  (stateAt G hG scheme (phase + 1)).state.history.length

noncomputable def omittedOutput
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) : α :=
  (selectedTransition G hG scheme phase
    (stateAt G hG scheme phase)).omittedOutput

theorem transitionTime_lt_succ
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    transitionTime G hG scheme phase <
      transitionTime G hG scheme (phase + 1) := by
  exact stateAt_history_strict_succ
    G hG scheme (phase + 1)

theorem transitionTime_strictMono
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) :
    StrictMono (transitionTime G hG scheme) :=
  strictMono_nat_of_lt_succ
    (transitionTime_lt_succ G hG scheme)

theorem omittedOutput_mem_next_forbidden
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    omittedOutput G hG scheme phase ∈
      (stateAt G hG scheme (phase + 1)).state.forbidden := by
  rw [stateAt_succ_state]
  exact
    (selectedTransition G hG scheme phase
      (stateAt G hG scheme phase)).omitted_mem_next_forbidden

theorem omittedOutput_not_current_forbidden
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    omittedOutput G hG scheme phase ∉
      (stateAt G hG scheme phase).state.forbidden :=
  (selectedTransition G hG scheme phase
    (stateAt G hG scheme phase)).omitted_not_old_forbidden

theorem omittedOutput_injective
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) :
    Function.Injective (omittedOutput G hG scheme) := by
  intro first later heq
  apply Nat.le_antisymm
  · by_contra hle
    have hlaterFirst : later < first := Nat.lt_of_not_ge hle
    have hmem :
        omittedOutput G hG scheme later ∈
          (stateAt G hG scheme first).state.forbidden := by
      apply stateAt_forbidden_mono G hG scheme
        (show later + 1 ≤ first by omega)
      exact omittedOutput_mem_next_forbidden
        G hG scheme later
    apply omittedOutput_not_current_forbidden
      G hG scheme first
    rw [heq]
    exact hmem
  · by_contra hle
    have hfirstLater : first < later := Nat.lt_of_not_ge hle
    have hmem :
        omittedOutput G hG scheme first ∈
          (stateAt G hG scheme later).state.forbidden := by
      apply stateAt_forbidden_mono G hG scheme
        (show first + 1 ≤ later by omega)
      exact omittedOutput_mem_next_forbidden
        G hG scheme first
    apply omittedOutput_not_current_forbidden
      G hG scheme later
    rw [← heq]
    exact hmem

/-- Infinite stream determined by the nested eligible histories.  Strict
growth guarantees that the history at phase `k+1` already defines
coordinate `k`. -/
noncomputable def limitStream
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) :
    Stream α :=
  fun k =>
    (stateAt G hG scheme (k + 1)).state.history.get
      ⟨k, by
        have hlength :=
          stateAt_history_length_lower
            G hG scheme (k + 1)
        omega⟩

theorem limitStream_eq_state_get
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient)
    (phase k : ℕ)
    (hk :
      k < (stateAt G hG scheme phase).state.history.length) :
    limitStream G hG scheme k =
      (stateAt G hG scheme phase).state.history.get
        ⟨k, hk⟩ := by
  rw [limitStream]
  have hkShort :
      k <
        (stateAt G hG scheme (k + 1)).state.history.length := by
    have hlength :=
      stateAt_history_length_lower G hG scheme (k + 1)
    omega
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rcases le_total (k + 1) phase with hle | hge
  · exact
      (stateAt_history_prefix G hG scheme hle).getElem
        hkShort
  · exact
      ((stateAt_history_prefix G hG scheme hge).getElem
        hk).symm

theorem limitStream_injective
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) :
    Function.Injective (limitStream G hG scheme) := by
  intro first later heq
  let phase := max first later + 1
  have hfirst :
      first <
        (stateAt G hG scheme phase).state.history.length := by
    have hlength :=
      stateAt_history_length_lower G hG scheme phase
    dsimp only [phase] at hlength ⊢
    omega
  have hlater :
      later <
        (stateAt G hG scheme phase).state.history.length := by
    have hlength :=
      stateAt_history_length_lower G hG scheme phase
    dsimp only [phase] at hlength ⊢
    omega
  have hget :
      (stateAt G hG scheme phase).state.history.get
          ⟨first, hfirst⟩ =
        (stateAt G hG scheme phase).state.history.get
          ⟨later, hlater⟩ := by
    exact
      (limitStream_eq_state_get
        G hG scheme phase first hfirst).symm.trans
        (heq.trans
          (limitStream_eq_state_get
            G hG scheme phase later hlater))
  have hfin :
      (⟨first, hfirst⟩ :
          Fin
            (stateAt G hG scheme phase).state.history.length) =
        ⟨later, hlater⟩ :=
    (List.nodup_iff_injective_get.mp
      (stateAt G hG scheme phase).state.history_nodup)
        hget
  exact congrArg Fin.val hfin

theorem stateAt_historyCarrier_subset_limitRange
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    historyCarrier
        (stateAt G hG scheme phase).state.history ⊆
      Set.range (limitStream G hG scheme) := by
  rintro x ⟨i, hi⟩
  refine ⟨i, ?_⟩
  exact
    (limitStream_eq_state_get
      G hG scheme phase i i.isLt).trans hi

theorem stateAt_forbidden_disjoint_limitRange
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    Disjoint
      (stateAt G hG scheme phase).state.forbidden
      (Set.range (limitStream G hG scheme)) := by
  rw [Set.disjoint_left]
  rintro x hxForbidden ⟨k, hk⟩
  let later := max phase (k + 1)
  have hphaseLater : phase ≤ later :=
    Nat.le_max_left _ _
  have hkLater : k + 1 ≤ later :=
    Nat.le_max_right _ _
  have hxForbiddenLater :
      x ∈ (stateAt G hG scheme later).state.forbidden :=
    stateAt_forbidden_mono G hG scheme
      hphaseLater hxForbidden
  have hkLength :
      k < (stateAt G hG scheme later).state.history.length := by
    have hlength :=
      stateAt_history_length_lower G hG scheme later
    omega
  have hget :
      (stateAt G hG scheme later).state.history.get
          ⟨k, hkLength⟩ =
        x := by
    exact
      (limitStream_eq_state_get
        G hG scheme later k hkLength).symm.trans hk
  have hxHistory :
      x ∈ historyCarrier
        (stateAt G hG scheme later).state.history :=
    ⟨⟨k, hkLength⟩, hget⟩
  have hdisjoint :
      Disjoint
        (historyCarrier
          (stateAt G hG scheme later).state.history)
        (stateAt G hG scheme later).state.forbidden :=
    (stateAt G hG scheme later).state.history_forbidden_disjoint
  exact
    Set.disjoint_left.mp hdisjoint
      hxHistory hxForbiddenLater

theorem omittedOutput_omitted_forever
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    omittedOutput G hG scheme phase ∉
      Set.range (limitStream G hG scheme) := by
  exact
    Set.disjoint_left.mp
      (stateAt_forbidden_disjoint_limitRange
        G hG scheme (phase + 1))
      (omittedOutput_mem_next_forbidden
        G hG scheme phase)

theorem output_at_transition
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    output G (limitStream G hG scheme)
        (transitionTime G hG scheme phase) =
      omittedOutput G hG scheme phase := by
  let transition :=
    selectedTransition G hG scheme phase
      (stateAt G hG scheme phase)
  have hnext :
      transition.next =
        (stateAt G hG scheme (phase + 1)).state := by
    rfl
  change
    G (stateAt G hG scheme (phase + 1)).state.history.length
        (fun i => limitStream G hG scheme i) =
      transition.omittedOutput
  calc
    G (stateAt G hG scheme (phase + 1)).state.history.length
        (fun i => limitStream G hG scheme i) =
      G (stateAt G hG scheme (phase + 1)).state.history.length
        (stateAt G hG scheme (phase + 1)).state.history.get := by
          congr 1
          funext i
          exact limitStream_eq_state_get
            G hG scheme (phase + 1) i i.isLt
    _ = transition.omittedOutput := by
      rw [← hnext]
      exact transition.output_on_next_history

theorem transition_not_correct
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (phase : ℕ) :
    ¬CorrectAt G
      (Set.range (limitStream G hG scheme))
      (limitStream G hG scheme)
      (transitionTime G hG scheme phase) := by
  intro hcorrect
  apply omittedOutput_omitted_forever G hG scheme phase
  simpa [output_at_transition G hG scheme phase] using
    hcorrect.1

theorem exists_transition_after
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) (T : ℕ) :
    ∃ phase, T ≤ transitionTime G hG scheme phase := by
  refine ⟨T, ?_⟩
  exact (transitionTime_strictMono G hG scheme).id_le T

/-- The deterministic infinite-switch endgame: the nested histories form
an injective exact presentation, and the generator is wrong at unboundedly
many transition times. -/
theorem prefixRealizability_endgame
    {ambient : LanguageClass α}
    (G : Generator α)
    (hG : IsLimitGeneratorOnInjectivePresentations G ambient)
    (scheme : Scheme ambient) :
    Function.Injective (limitStream G hG scheme) ∧
      GenLimit.Generic.Presents (limitStream G hG scheme)
        (Set.range (limitStream G hG scheme)) ∧
      ∀ T, ∃ t, T ≤ t ∧
        ¬CorrectAt G
          (Set.range (limitStream G hG scheme))
          (limitStream G hG scheme) t := by
  refine ⟨limitStream_injective G hG scheme, rfl, ?_⟩
  intro T
  obtain ⟨phase, hphase⟩ :=
    exists_transition_after G hG scheme T
  exact
    ⟨transitionTime G hG scheme phase, hphase,
      transition_not_correct G hG scheme phase⟩

/-- The second independent Appendix A.2 obligation: the limit of the
forced, infinitely switching prefix construction belongs to the ambient
class. -/
def SchemeLimitInAmbient
    {ambient : LanguageClass α}
    (scheme : Scheme ambient) : Prop :=
  ∀ G : Generator α,
    ∀ hG : IsLimitGeneratorOnInjectivePresentations G ambient,
      Set.range (limitStream G hG scheme) ∈ ambient

/-- Appendix A.2's complete deterministic prefix-realizability principle.
Avoiding-prefix realizability drives every finite switch; membership of the
infinite switched limit supplies the final target.  Together they refute
every deterministic generator on injective exact presentations. -/
theorem appendix_A_2_deterministic_prefix_realizability_core
    {ambient : LanguageClass α}
    (scheme : Scheme ambient)
    (hlimit : SchemeLimitInAmbient scheme) :
    ¬GeneratableInLimitOnInjectivePresentations ambient := by
  rintro ⟨G, hG⟩
  let stream := limitStream G hG scheme
  let target : Set α := Set.range stream
  have htarget : target ∈ ambient :=
    hlimit G hG
  obtain ⟨threshold, hcorrect⟩ :=
    hG target htarget stream
      (limitStream_injective G hG scheme) rfl
  obtain ⟨time, htime, hnotCorrect⟩ :=
    (prefixRealizability_endgame G hG scheme).2.2 threshold
  exact hnotCorrect (hcorrect time htime)

/-- Corollary for the library's stronger presentation semantics, which
also quantifies over exact presentations with repetitions. -/
theorem appendix_A_2_not_generatableInLimit
    {ambient : LanguageClass α}
    (scheme : Scheme ambient)
    (hlimit : SchemeLimitInAmbient scheme) :
    ¬GenLimit.Generic.GeneratableInLimit ambient := by
  intro hgeneratable
  apply
    appendix_A_2_deterministic_prefix_realizability_core
      scheme hlimit
  obtain ⟨G, hG⟩ := hgeneratable
  exact
    ⟨G, isLimitGeneratorOnInjectivePresentations_of_isLimitGenerator hG⟩

end GenLimit.UnionClosedness.PrefixRealizability
