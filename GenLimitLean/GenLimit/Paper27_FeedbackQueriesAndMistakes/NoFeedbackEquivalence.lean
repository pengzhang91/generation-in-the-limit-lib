import GenLimit.Core.SetGeneration
import GenLimit.Core.Text
import GenLimit.Support.Fresh
import GenLimit.Support.Locking

/-!
# P27 Theorem 3.9: no-feedback set/element generation

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*Language Generation with Feedback: Queries and Mistakes*, ICML 2026,
Theorem 3.9 and Appendix A.6.1.

This module formalizes the paper's two conversion constructions.  Projection
of an infinite set output to one element is unconditional and is exposed by
Core's `setGeneratableInLimit_implies_generatableInLimit`.  The reverse
construction iterates a fresh element generator on its own hypothetical
outputs and is proved below from the exact self-locking condition used in
Lemma A.8.

The source asserts that every successful sequence generator has the required
self-locking prefix along every presentation.  That implication is kept
separate here: its quantifier strength is not supplied by the generic locking
lemma in `Support/Locking.lean`.  The public theorem in this module therefore
does not silently assume that unresolved step.  Further proof search for the
unrestricted reverse direction is deliberately deferred unless a corrected
source statement or an independent new argument becomes available.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic
open GenLimit.Angluin

/-! ## Finite-history and freshness interfaces -/

/-- Evaluate a prefix generator on a literal list history. -/
def noFeedbackOutputOnList
    (gen : Generator α) (history : List α) : α :=
  gen history.length history.get

/-- The generator is fresh on every finite history, including histories that
do not arise along a successful target presentation. -/
def EverywhereFresh (gen : Generator α) : Prop :=
  ∀ t samples, gen t samples ∉ sequenceSample samples

/-- Harmless total freshening from Appendix A.6.1.  On a history where the
original output is already unseen it is preserved; otherwise a point outside
the finite sample is selected from the infinite universe. -/
noncomputable def freshenedGenerator
    [Infinite α] (gen : Generator α) : Generator α := by
  classical
  exact fun t samples =>
    if h : gen t samples ∉ sequenceSample samples then gen t samples
    else GenLimit.Support.freshFromInfinite
      Set.univ Set.infinite_univ (sequenceSample samples)

theorem freshenedGenerator_eq_of_fresh
    [Infinite α] (gen : Generator α)
    {t : ℕ} {samples : Fin t → α}
    (h : gen t samples ∉ sequenceSample samples) :
    freshenedGenerator gen t samples = gen t samples := by
  simp [freshenedGenerator, h]

theorem freshenedGenerator_everywhereFresh
    [Infinite α] (gen : Generator α) :
    EverywhereFresh (freshenedGenerator gen) := by
  intro t samples
  by_cases h : gen t samples ∉ sequenceSample samples
  · simp [freshenedGenerator, h]
  · simp only [freshenedGenerator, h]
    exact GenLimit.Support.freshFromInfinite_not_mem
      Set.univ Set.infinite_univ (sequenceSample samples)

/-- Freshening changes only unsuccessful rounds and hence preserves ordinary
generation in the limit. -/
theorem freshenedGenerator_isLimitGenerator
    [Infinite α] {gen : Generator α} {targets : LanguageClass α}
    (hgen : IsLimitGenerator gen targets) :
    IsLimitGenerator (freshenedGenerator gen) targets := by
  intro L hL stream hpresents
  obtain ⟨T, hT⟩ := hgen L hL stream hpresents
  refine ⟨T, ?_⟩
  intro t ht
  have hcorrect := hT t ht
  have hfresh :
      gen t (fun i => stream i) ∉
        sequenceSample (fun i : Fin t => stream i) := by
    rw [sequenceSample_prefix]
    exact hcorrect.2
  have heq :
      Generic.output (freshenedGenerator gen) stream t =
        Generic.output gen stream t := by
    simpa [Generic.output] using
      (freshenedGenerator_eq_of_fresh gen hfresh)
  change
    Generic.output (freshenedGenerator gen) stream t ∈ L ∧
      Generic.output (freshenedGenerator gen) stream t ∉
        Generic.sample stream t
  rw [heq]
  exact hcorrect

/-! ## Appendix Lemma A.8's self-locking condition -/

/-- Correctness of an element generator on one literal finite history. -/
def NoFeedbackCorrectOnList
    (gen : Generator α) (L : Generic.Language α) (history : List α) : Prop :=
  noFeedbackOutputOnList gen history ∈ L ∧
    noFeedbackOutputOnList gen history ∉ history

/-- The exact self-locking property used in Appendix Lemma A.8: every finite
target continuation remains correct at its endpoint. -/
def IsSelfLockingHistory
    (gen : Generator α) (L : Generic.Language α) (history : List α) : Prop :=
  ListWithin history L ∧
    ∀ tail, ListWithin tail L →
      NoFeedbackCorrectOnList gen L (history ++ tail)

/-- Every presentation eventually reaches a self-locking prefix. -/
def SelfLocksAlongEveryPresentation
    (gen : Generator α) (targets : Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → ∀ stream : Generic.Stream α,
    Generic.Presents stream L →
    ∃ n, IsSelfLockingHistory gen L (GenLimit.textPrefix stream n)

theorem IsSelfLockingHistory.extend
    {gen : Generator α} {L : Generic.Language α} {history tail : List α}
    (hlock : IsSelfLockingHistory gen L history)
    (htail : ListWithin tail L) :
    IsSelfLockingHistory gen L (history ++ tail) := by
  refine ⟨listWithin_append hlock.1 htail, ?_⟩
  intro rest hrest
  simpa only [List.append_assoc] using
    hlock.2 (tail ++ rest) (listWithin_append htail hrest)

/-! ## The self-simulation set generator -/

/-- Histories obtained by repeatedly appending the freshened generator's own
next output. -/
noncomputable def simulatedHistory
    (gen : Generator α) (history : List α) : ℕ → List α
  | 0 => history
  | n + 1 =>
      let previous := simulatedHistory gen history n
      previous ++ [noFeedbackOutputOnList gen previous]

/-- The next element on the self-simulated continuation. -/
noncomputable def simulatedValue
    (gen : Generator α) (history : List α) (n : ℕ) : α :=
  noFeedbackOutputOnList gen (simulatedHistory gen history n)

@[simp] theorem simulatedHistory_zero
    (gen : Generator α) (history : List α) :
    simulatedHistory gen history 0 = history :=
  rfl

theorem simulatedHistory_succ
    (gen : Generator α) (history : List α) (n : ℕ) :
    simulatedHistory gen history (n + 1) =
      simulatedHistory gen history n ++ [simulatedValue gen history n] :=
  rfl

theorem simulatedHistory_length
    (gen : Generator α) (history : List α) (n : ℕ) :
    (simulatedHistory gen history n).length = history.length + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [simulatedHistory_succ, List.length_append, ih]
      simp
      omega

theorem simulatedHistory_initial_prefix
    (gen : Generator α) (history : List α) (n : ℕ) :
    history <+: simulatedHistory gen history n := by
  induction n with
  | zero => exact List.prefix_refl _
  | succ n ih =>
      rw [simulatedHistory_succ]
      exact ih.trans (List.prefix_append _ _)

theorem simulatedValue_mem_history_of_lt
    (gen : Generator α) (history : List α)
    {i j : ℕ} (hij : i < j) :
    simulatedValue gen history i ∈ simulatedHistory gen history j := by
  induction j with
  | zero => omega
  | succ j ih =>
      rw [simulatedHistory_succ, List.mem_append, List.mem_singleton]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hij) with hij' | rfl
      · exact Or.inl (ih hij')
      · exact Or.inr rfl

theorem simulatedValue_not_mem_history
    [DecidableEq α]
    {gen : Generator α} (hfresh : EverywhereFresh gen)
    (history : List α) (n : ℕ) :
    simulatedValue gen history n ∉ simulatedHistory gen history n := by
  have h := hfresh (simulatedHistory gen history n).length
    (simulatedHistory gen history n).get
  rw [sequenceSample_list_get] at h
  simpa [simulatedValue, noFeedbackOutputOnList] using h

theorem simulatedValue_not_mem_initial
    [DecidableEq α]
    {gen : Generator α} (hfresh : EverywhereFresh gen)
    (history : List α) (n : ℕ) :
    simulatedValue gen history n ∉ history := by
  intro hmem
  exact simulatedValue_not_mem_history hfresh history n
    ((simulatedHistory_initial_prefix gen history n).sublist.subset hmem)

theorem simulatedValue_injective
    [DecidableEq α]
    {gen : Generator α} (hfresh : EverywhereFresh gen)
    (history : List α) :
    Function.Injective (simulatedValue gen history) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem := simulatedValue_mem_history_of_lt gen history hlt
    rw [hij] at hmem
    exact simulatedValue_not_mem_history hfresh history j hmem
  · have hmem := simulatedValue_mem_history_of_lt gen history hgt
    rw [← hij] at hmem
    exact simulatedValue_not_mem_history hfresh history i hmem

/-- Appendix A.6.1's set generator: output the range of the infinite
self-simulated continuation. -/
noncomputable def selfSimulationSetGenerator
    (gen : Generator α) : SetGenerator α :=
  fun _ samples => Set.range (simulatedValue gen (List.ofFn samples))

theorem selfSimulationSetGenerator_infinite
    [DecidableEq α]
    {gen : Generator α} (hfresh : EverywhereFresh gen) :
    IsInfiniteSetGenerator (selfSimulationSetGenerator gen) := by
  intro t samples
  exact Set.infinite_range_of_injective
    (simulatedValue_injective hfresh (List.ofFn samples))

private theorem simulatedHistory_within_of_lock
    [DecidableEq α]
    {gen : Generator α} {L : Generic.Language α} {history : List α}
    (hlock : IsSelfLockingHistory gen L history) :
    ∀ n, ListWithin (simulatedHistory gen history n) L ∧
      simulatedValue gen history n ∈ L := by
  intro n
  induction n with
  | zero =>
      have hvalue := (hlock.2 [] (by simp [ListWithin])).1
      exact ⟨hlock.1, by simpa [simulatedValue] using hvalue⟩
  | succ n ih =>
      have hwithin :
          ListWithin (simulatedHistory gen history (n + 1)) L := by
        rw [simulatedHistory_succ]
        exact listWithin_append ih.1 (singletonWithin ih.2)
      obtain ⟨tail, htailEq⟩ :=
        simulatedHistory_initial_prefix gen history (n + 1)
      have htail : ListWithin tail L := by
        intro x hx
        exact hwithin x (by rw [← htailEq]; simp [hx])
      have hvalue := (hlock.2 tail htail).1
      exact ⟨hwithin, by
        simpa [simulatedValue, htailEq] using hvalue⟩

theorem selfSimulationSetGenerator_correct_on_lock
    [DecidableEq α]
    {gen : Generator α} {L : Generic.Language α} {history : List α}
    (hfresh : EverywhereFresh gen)
    (hlock : IsSelfLockingHistory gen L history) :
    selfSimulationSetGenerator gen history.length history.get ⊆ L ∧
      Disjoint (selfSimulationSetGenerator gen history.length history.get)
        (↑history.toFinset : Set α) := by
  constructor
  · rintro x ⟨n, rfl⟩
    simpa [selfSimulationSetGenerator] using
      (simulatedHistory_within_of_lock hlock n).2
  · rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    have hxList : simulatedValue gen history n ∈ history := by
      simpa using hx
    exact simulatedValue_not_mem_initial hfresh history n hxList

private theorem textPrefix_toFinset_generic
    [DecidableEq α] (stream : Generic.Stream α) (t : ℕ) :
    (GenLimit.textPrefix stream t).toFinset = Generic.sample stream t := by
  ext x
  rw [List.mem_toFinset, GenLimit.mem_textPrefix_iff]
  exact Generic.mem_sample_iff.symm

theorem selfSimulationSetGenerator_correctAt_of_lock
    [DecidableEq α]
    {gen : Generator α} {L : Generic.Language α}
    {stream : Generic.Stream α} {t : ℕ}
    (hfresh : EverywhereFresh gen)
    (hlock : IsSelfLockingHistory gen L (GenLimit.textPrefix stream t)) :
    SetCorrectAt (selfSimulationSetGenerator gen) L stream t := by
  rw [GenLimit.textPrefix_eq_ofFn] at hlock
  have hcorrect :=
    selfSimulationSetGenerator_correct_on_lock hfresh hlock
  have hfin :
      (List.ofFn (fun i : Fin t => stream i)).toFinset =
        Generic.sample stream t := by
    rw [← GenLimit.textPrefix_eq_ofFn]
    exact textPrefix_toFinset_generic stream t
  change
    selfSimulationSetGenerator gen t (fun i => stream i) ⊆ L ∧
      Disjoint (selfSimulationSetGenerator gen t (fun i => stream i))
        (↑(Generic.sample stream t) : Set α)
  simpa only [selfSimulationSetGenerator, List.ofFn_get, hfin] using hcorrect

/-- The element-to-set construction, assuming precisely the strong
self-locking conclusion claimed by Appendix Lemma A.8. -/
theorem selfLocking_element_implies_set
    [DecidableEq α]
    {targets : Generic.LanguageClass α} {gen : Generator α}
    (hfresh : EverywhereFresh gen)
    (hlocks : SelfLocksAlongEveryPresentation gen targets) :
    SetGeneratableInLimit targets := by
  refine ⟨selfSimulationSetGenerator gen,
    selfSimulationSetGenerator_infinite hfresh, ?_⟩
  intro L hL stream hpresents
  obtain ⟨n₀, hlock₀⟩ := hlocks L hL stream hpresents
  refine ⟨n₀, ?_⟩
  intro t ht
  have hprefix := GenLimit.textPrefix_prefix stream ht
  obtain ⟨tail, htailEq⟩ := hprefix
  have hstream : Generic.StreamIn stream L :=
    Generic.streamIn_of_presents hpresents
  have htail : ListWithin tail L := by
    intro x hx
    have hxFull : x ∈ GenLimit.textPrefix stream t := by
      rw [← htailEq]
      simp [hx]
    exact streamPrefix_listWithin hstream t x hxFull
  have hlock :
      IsSelfLockingHistory gen L (GenLimit.textPrefix stream t) := by
    rw [← htailEq]
    exact hlock₀.extend htail
  exact selfSimulationSetGenerator_correctAt_of_lock hfresh hlock

/-- Faithful Appendix A.6.1 equivalence under the explicit self-locking
normal-form premise used by the paper's reverse-direction proof. -/
theorem theorem_3_9_of_selfLocking
    [Infinite α] [DecidableEq α]
    (targets : Generic.LanguageClass α)
    (hnormal : ∀ gen, IsLimitGenerator gen targets →
      SelfLocksAlongEveryPresentation (freshenedGenerator gen) targets) :
    SetGeneratableInLimit targets ↔ GeneratableInLimit targets := by
  constructor
  · exact setGeneratableInLimit_implies_generatableInLimit
  · rintro ⟨gen, hgen⟩
    exact selfLocking_element_implies_set
      (freshenedGenerator_everywhereFresh gen)
      (hnormal gen hgen)

end GenLimit.FeedbackQueries
