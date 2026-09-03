import GenLimit.Paper27_FeedbackQueriesAndMistakes.Definitions
import GenLimit.Support.EnumerationProgress
import GenLimit.Support.Locking
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List

/-!
# Exact element-valued mistake feedback

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*Language Generation with Feedback: Queries and Mistakes*,
ICML 2026, Definition 3, Theorems 3.1--3.2, and Appendix A.1.

This file restores the source's exact element-valued mistake interaction.
At a finite ordered positive history `xs`, the generator sees precisely the
truthful bits produced after its outputs on the proper nonempty prefixes of
`xs`.  A bit is true exactly when that output was both in the target and
fresh relative to the prefix then visible.

The proof of Theorem 3.1 follows Appendix A.1.  Eventual success gives a
finite locking history by the already checked generic locking diagonal.
Starting from that history, append the generator's own output and a positive
feedback bit forever.  Locking makes these outputs pairwise distinct target
members, so the countably many finite transcript seeds form a countable
inner cover.

The converse uses a fixed injection of the countable universe into `ℕ` as
the source's canonical order.  It tests inner-cover members in order, always
emitting the least unseen member.  Every false cover has a least negative
witness and only finitely many earlier points, all of which are eventually
shown by an exact presentation.

No computability, runtime, or corrupted-feedback claim is made.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic
open GenLimit.Angluin

/-! ## Canonical order on a countable universe -/

/-- A fixed injection into `ℕ`, representing the source's canonical order
on its countable string universe. -/
noncomputable def sourceCanonicalRank [Countable α] : α → ℕ :=
  Classical.choose (Countable.exists_injective_nat α)

theorem sourceCanonicalRank_injective [Countable α] :
    Function.Injective (sourceCanonicalRank (α := α)) :=
  Classical.choose_spec (Countable.exists_injective_nat α)

private theorem sourceRankWitness [Countable α]
    (S : Set α) (hS : S.Nonempty) :
    ∃ n, ∃ x ∈ S, sourceCanonicalRank x = n := by
  obtain ⟨x, hx⟩ := hS
  exact ⟨sourceCanonicalRank x, x, hx, rfl⟩

/-- The least rank attained by a nonempty set. -/
noncomputable def sourceFirstRank [Countable α]
    (S : Set α) (hS : S.Nonempty) : ℕ := by
  classical
  exact Nat.find (sourceRankWitness S hS)

/-- The first member of a nonempty set in the fixed canonical order. -/
noncomputable def sourceFirst [Countable α]
    (S : Set α) (hS : S.Nonempty) : α := by
  classical
  exact Classical.choose (Nat.find_spec (sourceRankWitness S hS))

theorem sourceFirst_mem [Countable α]
    (S : Set α) (hS : S.Nonempty) :
    sourceFirst S hS ∈ S := by
  classical
  exact
    (Classical.choose_spec
      (Nat.find_spec (sourceRankWitness S hS))).1

theorem sourceCanonicalRank_sourceFirst [Countable α]
    (S : Set α) (hS : S.Nonempty) :
    sourceCanonicalRank (sourceFirst S hS) =
      sourceFirstRank S hS := by
  classical
  exact
    (Classical.choose_spec
      (Nat.find_spec (sourceRankWitness S hS))).2

theorem sourceFirst_rank_le [Countable α]
    (S : Set α) (hS : S.Nonempty) {x : α} (hx : x ∈ S) :
    sourceCanonicalRank (sourceFirst S hS) ≤
      sourceCanonicalRank x := by
  classical
  rw [sourceCanonicalRank_sourceFirst]
  exact Nat.find_min' (sourceRankWitness S hS) ⟨x, hx, rfl⟩

theorem sourceCanonicalRank_lt_finite [Countable α] (n : ℕ) :
    {x : α | sourceCanonicalRank x < n}.Finite := by
  apply Set.Finite.of_finite_image
  · apply (Finset.finite_toSet (Finset.range n)).subset
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  · exact (sourceCanonicalRank_injective (α := α)).injOn

/-! ## Exact interaction on ordered histories -/

/-- An element-valued generator with the ordered positive history and the
previous mistake-feedback bits as its two inputs. -/
abbrev SourceElementMistakeStrategy (α : Type*) :=
  List α → List Bool → α

/-- The source's truthful bit: the proposed element must be in the target
and absent from the positive history visible when it was proposed. -/
noncomputable def sourceElementReply
    (target : Set α) (samples : List α) (output : α) : Bool := by
  classical
  exact if output ∈ target ∧ output ∉ samples then true else false

theorem sourceElementReply_eq_true_iff
    (target : Set α) (samples : List α) (output : α) :
    sourceElementReply target samples output = true ↔
      output ∈ target ∧ output ∉ samples := by
  classical
  simp [sourceElementReply]

/-- One input update.  The first positive example arrives before any output.
Every later example arrives after the bit evaluating the preceding output. -/
noncomputable def sourceElementFeedbackStep
    (strategy : SourceElementMistakeStrategy α)
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
          [sourceElementReply target state.1
            (strategy state.1 state.2)])

/-- Replay the unique truthful interaction induced by a finite ordered
positive history. -/
noncomputable def sourceElementFeedbackRun
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (samples : List α) :
    List α × List Bool :=
  samples.foldl
    (sourceElementFeedbackStep strategy target) ([], [])

/-- The previous truthful bits supplied at the current history. -/
noncomputable def sourceElementFeedback
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (samples : List α) : List Bool :=
  (sourceElementFeedbackRun strategy target samples).2

theorem sourceElementFeedbackRun_fst
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (samples : List α) :
    (sourceElementFeedbackRun strategy target samples).1 = samples := by
  classical
  induction samples using List.reverseRecOn with
  | nil => rfl
  | append_singleton samples next ih =>
      simp only [sourceElementFeedbackRun, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have hfst :
        (List.foldl (sourceElementFeedbackStep strategy target)
          ([], []) samples).1 = samples := by
        simpa [sourceElementFeedbackRun] using ih
      rw [show
        List.foldl (sourceElementFeedbackStep strategy target)
            ([], []) samples =
          (samples,
            (List.foldl (sourceElementFeedbackStep strategy target)
              ([], []) samples).2) by
            apply Prod.ext
            · exact hfst
            · rfl]
      simp only [sourceElementFeedbackStep]
      split_ifs with h
      · subst samples
        rfl
      · rfl

theorem sourceElementFeedback_append
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (samples : List α) (next : α)
    (hsamples : samples ≠ []) :
    sourceElementFeedback strategy target (samples ++ [next]) =
      sourceElementFeedback strategy target samples ++
        [sourceElementReply target samples
          (strategy samples
            (sourceElementFeedback strategy target samples))] := by
  classical
  simp only [sourceElementFeedback, sourceElementFeedbackRun,
    List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hfst :
      (List.foldl (sourceElementFeedbackStep strategy target)
        ([], []) samples).1 = samples := by
    simpa [sourceElementFeedbackRun] using
      sourceElementFeedbackRun_fst strategy target samples
  rw [show
    List.foldl (sourceElementFeedbackStep strategy target)
        ([], []) samples =
      (samples,
        (List.foldl (sourceElementFeedbackStep strategy target)
          ([], []) samples).2) by
        apply Prod.ext
        · exact hfst
        · rfl]
  simp [sourceElementFeedbackStep, hsamples]

/-- The element emitted after the given ordered positive history. -/
noncomputable def sourceElementOutput
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (samples : List α) : α :=
  strategy samples (sourceElementFeedback strategy target samples)

/-- Correctness at one history, exactly Definition 3's element clause. -/
def SourceElementMistakeCorrect
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (samples : List α) : Prop :=
  sourceElementOutput strategy target samples ∈ target ∧
    sourceElementOutput strategy target samples ∉ samples

/-- Eventual correctness on every exact ordered presentation.  The harmless
empty-history extension is ignored by the eventual quantifier. -/
def SourceElementMistakeSucceedsOn
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream target →
    ∃ T, ∀ t, T ≤ t →
      SourceElementMistakeCorrect strategy target
        (streamPrefix stream t)

def SourceElementMistakeGenerates
    (strategy : SourceElementMistakeStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → SourceElementMistakeSucceedsOn strategy L

def SourceElementMistakeGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : SourceElementMistakeStrategy α,
    SourceElementMistakeGenerates strategy targets

/-! ## Locking and the inner-cover necessity -/

noncomputable def sourceElementCorrectnessObserver
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (samples : List α) : ℕ := by
  classical
  exact if SourceElementMistakeCorrect strategy target samples then 1 else 0

theorem sourceElementCorrectnessObserver_eq_one_iff
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (samples : List α) :
    sourceElementCorrectnessObserver strategy target samples = 1 ↔
      SourceElementMistakeCorrect strategy target samples := by
  classical
  simp [sourceElementCorrectnessObserver]

/-- Eventual element generation supplies a target-language locking history
for the exact mistake-feedback interaction. -/
theorem exists_sourceElementMistake_lock
    [Countable α]
    {strategy : SourceElementMistakeStrategy α}
    {target : Set α} (htarget : target.Infinite)
    (hstrategy : SourceElementMistakeSucceedsOn strategy target) :
    ∃ seed : List α,
      seed ≠ [] ∧ ListWithin seed target ∧
      ∀ tail : List α, ListWithin tail target →
        SourceElementMistakeCorrect strategy target (seed ++ tail) := by
  classical
  let base : Stream α :=
    GenLimit.Support.infiniteEnumeration target htarget
  have hbaseP : Generic.Presents base target := by
    simpa [base] using
      GenLimit.Support.infiniteEnumeration_presents target htarget
  let observer :=
    sourceElementCorrectnessObserver strategy target
  have hconverges :
      ∀ stream : Stream α, Generic.Presents stream target →
        ∃ j,
          GenLimit.StabilizesTo
            (fun t => observer (GenLimit.textPrefix stream t)) j := by
    intro stream hP
    obtain ⟨T, hT⟩ := hstrategy stream hP
    refine ⟨1, T, ?_⟩
    intro t ht
    apply
      (sourceElementCorrectnessObserver_eq_one_iff
        strategy target _).2
    exact hT t ht
  obtain ⟨seed, j, hlock⟩ :=
    GenLimit.Angluin.exists_lockingSequence_of_converges_with_base
      hbaseP hconverges
  have hj : j = 1 := by
    let combined := prependStream seed base
    have hcombinedP : Generic.Presents combined target :=
      prependStream_presents hlock.1 hbaseP
    obtain ⟨T, hT⟩ := hstrategy combined hcombinedP
    let tail := streamPrefix base T
    have htailWithin : ListWithin tail target :=
      streamPrefix_listWithin
        (Generic.streamIn_of_presents hbaseP) T
    have hlocked :
        observer (seed ++ tail) = j :=
      hlock.2 tail htailWithin
    have hprefix :
        streamPrefix combined (seed.length + T) =
          seed ++ tail := by
      simpa [combined, tail] using
        streamPrefix_prependStream seed base T
    have hone : observer (seed ++ tail) = 1 := by
      rw [← hprefix]
      apply
        (sourceElementCorrectnessObserver_eq_one_iff
          strategy target _).2
      exact hT _ (Nat.le_add_left T seed.length)
    exact hlocked.symm.trans hone
  let firstSample := base 0
  let lockedSeed := seed ++ [firstSample]
  have hfirst : firstSample ∈ target :=
    Generic.streamIn_of_presents hbaseP ⟨0, rfl⟩
  have hlockedSeedWithin : ListWithin lockedSeed target :=
    listWithin_append hlock.1 (singletonWithin hfirst)
  refine ⟨lockedSeed, by simp [lockedSeed], hlockedSeedWithin, ?_⟩
  intro tail htail
  apply
    (sourceElementCorrectnessObserver_eq_one_iff
      strategy target _).1
  have hcombinedWithin :
      ListWithin ([firstSample] ++ tail) target :=
    listWithin_append (singletonWithin hfirst) htail
  simpa [lockedSeed, List.append_assoc] using
    (hlock.2 ([firstSample] ++ tail) hcombinedWithin).trans hj

/-- Histories generated by repeatedly appending the element strategy's own
output while feeding it positive bits after a finite transcript seed. -/
noncomputable def sourceElementSelfHistory
    (strategy : SourceElementMistakeStrategy α)
    (seed : List α) (bits : List Bool) : ℕ → List α
  | 0 => seed
  | t + 1 =>
      let history := sourceElementSelfHistory strategy seed bits t
      history ++
        [strategy history (bits ++ List.replicate t true)]

/-- The next output in the all-positive self-simulation. -/
noncomputable def sourceElementSelfOutput
    (strategy : SourceElementMistakeStrategy α)
    (seed : List α) (bits : List Bool) (t : ℕ) : α :=
  strategy (sourceElementSelfHistory strategy seed bits t)
    (bits ++ List.replicate t true)

@[simp] theorem sourceElementSelfHistory_succ
    (strategy : SourceElementMistakeStrategy α)
    (seed : List α) (bits : List Bool) (t : ℕ) :
    sourceElementSelfHistory strategy seed bits (t + 1) =
      sourceElementSelfHistory strategy seed bits t ++
        [sourceElementSelfOutput strategy seed bits t] :=
  rfl

theorem sourceElementSelfHistory_prefix
    (strategy : SourceElementMistakeStrategy α)
    (seed : List α) (bits : List Bool) {s t : ℕ}
    (hst : s ≤ t) :
    sourceElementSelfHistory strategy seed bits s <+:
      sourceElementSelfHistory strategy seed bits t := by
  induction t, hst using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
      exact ih.trans (List.prefix_append _ _)

theorem sourceElementSelfOutput_mem_laterHistory
    (strategy : SourceElementMistakeStrategy α)
    (seed : List α) (bits : List Bool) {s t : ℕ}
    (hst : s < t) :
    sourceElementSelfOutput strategy seed bits s ∈
      sourceElementSelfHistory strategy seed bits t := by
  have hmem :
      sourceElementSelfOutput strategy seed bits s ∈
        sourceElementSelfHistory strategy seed bits (s + 1) := by
    rw [sourceElementSelfHistory_succ]
    simp
  exact
    List.IsPrefix.mem hmem
      (sourceElementSelfHistory_prefix strategy seed bits
        (Nat.succ_le_iff.mpr hst))

theorem sourceElementSelfHistory_eq_seed_append
    (strategy : SourceElementMistakeStrategy α)
    (seed : List α) (bits : List Bool) (t : ℕ) :
    sourceElementSelfHistory strategy seed bits t =
      seed ++ List.ofFn
        (fun i : Fin t =>
          sourceElementSelfOutput strategy seed bits i) := by
  induction t with
  | zero => simp [sourceElementSelfHistory]
  | succ t ih =>
      rw [sourceElementSelfHistory_succ, ih]
      rw [List.ofFn_succ']
      simp

/-- The set of all outputs in one finite-seed all-positive simulation. -/
def sourceElementSelfSet
    (strategy : SourceElementMistakeStrategy α)
    (seed : List α) (bits : List Bool) : Set α :=
  Set.range (sourceElementSelfOutput strategy seed bits)

theorem sourceElementSelfOutput_injective_of_fresh
    (strategy : SourceElementMistakeStrategy α)
    (seed : List α) (bits : List Bool)
    (hfresh :
      ∀ t, sourceElementSelfOutput strategy seed bits t ∉
        sourceElementSelfHistory strategy seed bits t) :
    Function.Injective
      (sourceElementSelfOutput strategy seed bits) := by
  intro s t heq
  rcases lt_trichotomy s t with hst | hst | hst
  · exact False.elim
      (hfresh t
        (by
          rw [← heq]
          exact sourceElementSelfOutput_mem_laterHistory
            strategy seed bits hst))
  · exact hst
  · exact False.elim
      (hfresh s
        (by
          rw [heq]
          exact sourceElementSelfOutput_mem_laterHistory
            strategy seed bits hst))

/-- A nonempty seed remains nonempty throughout self-simulation. -/
theorem sourceElementSelfHistory_ne_nil
    (strategy : SourceElementMistakeStrategy α)
    (seed : List α) (bits : List Bool)
    (hseed : seed ≠ []) (t : ℕ) :
    sourceElementSelfHistory strategy seed bits t ≠ [] := by
  intro hempty
  have hprefix :=
    sourceElementSelfHistory_prefix strategy seed bits
      (Nat.zero_le t)
  have hlen : seed.length ≤ 0 := by
    simpa [sourceElementSelfHistory, hempty] using hprefix.length_le
  exact hseed (List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen))

/-- The induction used in Appendix A.1: all simulated outputs seen so far
are target members, the actual transcript is the seeded transcript followed
by positive bits, and the next output is correct and fresh. -/
theorem sourceElementSelfSimulation_of_lock
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (seed : List α)
    (hseed : seed ≠ [])
    (hlock :
      ∀ tail : List α, ListWithin tail target →
        SourceElementMistakeCorrect strategy target (seed ++ tail)) :
    ∀ t,
      ListWithin
          (List.ofFn
            (fun i : Fin t =>
              sourceElementSelfOutput strategy seed
                (sourceElementFeedback strategy target seed) i))
          target ∧
        sourceElementFeedback strategy target
            (sourceElementSelfHistory strategy seed
              (sourceElementFeedback strategy target seed) t) =
          sourceElementFeedback strategy target seed ++
            List.replicate t true ∧
        SourceElementMistakeCorrect strategy target
          (sourceElementSelfHistory strategy seed
            (sourceElementFeedback strategy target seed) t) := by
  intro t
  induction t with
  | zero =>
      refine ⟨by simp [ListWithin], by simp [sourceElementSelfHistory], ?_⟩
      simpa [sourceElementSelfHistory] using
        hlock [] (by simp [ListWithin])
  | succ t ih =>
      obtain ⟨hwithin, hfeedback, hcorrect⟩ := ih
      have hnextTarget :
          sourceElementSelfOutput strategy seed
              (sourceElementFeedback strategy target seed) t ∈ target := by
        simpa [SourceElementMistakeCorrect, sourceElementOutput,
          sourceElementSelfOutput, hfeedback] using hcorrect.1
      have hnextFresh :
          sourceElementSelfOutput strategy seed
              (sourceElementFeedback strategy target seed) t ∉
            sourceElementSelfHistory strategy seed
              (sourceElementFeedback strategy target seed) t := by
        simpa [SourceElementMistakeCorrect, sourceElementOutput,
          sourceElementSelfOutput, hfeedback] using hcorrect.2
      have hwithinSucc :
          ListWithin
            (List.ofFn
              (fun i : Fin (t + 1) =>
                sourceElementSelfOutput strategy seed
                  (sourceElementFeedback strategy target seed) i))
            target := by
        rw [List.ofFn_succ', List.concat_eq_append]
        apply listWithin_append
        · simpa using hwithin
        · simpa [ListWithin] using hnextTarget
      have hreply :
          sourceElementReply target
              (sourceElementSelfHistory strategy seed
                (sourceElementFeedback strategy target seed) t)
              (sourceElementSelfOutput strategy seed
                (sourceElementFeedback strategy target seed) t) =
            true := by
        rw [sourceElementReply_eq_true_iff]
        exact ⟨hnextTarget, hnextFresh⟩
      have hfeedbackSucc :
          sourceElementFeedback strategy target
              (sourceElementSelfHistory strategy seed
                (sourceElementFeedback strategy target seed) (t + 1)) =
            sourceElementFeedback strategy target seed ++
              List.replicate (t + 1) true := by
        rw [sourceElementSelfHistory_succ,
          sourceElementFeedback_append]
        · rw [hfeedback]
          change
            sourceElementFeedback strategy target seed ++
                List.replicate t true ++
                  [sourceElementReply target
                    (sourceElementSelfHistory strategy seed
                      (sourceElementFeedback strategy target seed) t)
                    (sourceElementSelfOutput strategy seed
                      (sourceElementFeedback strategy target seed) t)] =
              _
          rw [hreply]
          simp [List.replicate_succ']
        · exact sourceElementSelfHistory_ne_nil strategy seed
            (sourceElementFeedback strategy target seed) hseed t
      refine ⟨hwithinSucc, hfeedbackSucc, ?_⟩
      rw [sourceElementSelfHistory_eq_seed_append]
      exact hlock _ hwithinSucc

theorem sourceElementSelfSet_infinite_of_lock
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (seed : List α)
    (hseed : seed ≠ [])
    (hlock :
      ∀ tail : List α, ListWithin tail target →
        SourceElementMistakeCorrect strategy target (seed ++ tail)) :
    (sourceElementSelfSet strategy seed
      (sourceElementFeedback strategy target seed)).Infinite := by
  classical
  have hfresh :
      ∀ t,
        sourceElementSelfOutput strategy seed
            (sourceElementFeedback strategy target seed) t ∉
          sourceElementSelfHistory strategy seed
            (sourceElementFeedback strategy target seed) t := by
    intro t
    have hinvariant :=
      sourceElementSelfSimulation_of_lock strategy target seed hseed hlock t
    simpa [SourceElementMistakeCorrect, sourceElementOutput,
      sourceElementSelfOutput, hinvariant.2.1] using hinvariant.2.2.2
  exact Set.infinite_range_of_injective
    (sourceElementSelfOutput_injective_of_fresh
      strategy seed (sourceElementFeedback strategy target seed) hfresh)

theorem sourceElementSelfSet_subset_of_lock
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (seed : List α)
    (hseed : seed ≠ [])
    (hlock :
      ∀ tail : List α, ListWithin tail target →
        SourceElementMistakeCorrect strategy target (seed ++ tail)) :
    sourceElementSelfSet strategy seed
        (sourceElementFeedback strategy target seed) ⊆ target := by
  classical
  intro x hx
  obtain ⟨t, rfl⟩ := hx
  have hinvariant :=
    sourceElementSelfSimulation_of_lock strategy target seed hseed hlock t
  simpa [SourceElementMistakeCorrect, sourceElementOutput,
    sourceElementSelfOutput, hinvariant.2.1] using hinvariant.2.2.1

/-!
The source proof above is represented directly by `sourceElementSelfSet`.
For the paper-facing characterization below, we package the locking
extraction as the precise necessity interface.  This keeps transcript
enumeration separate from the interactive argument and makes the remaining
countability step reusable.
-/

abbrev SourceElementSeed (α : Type*) := List α × List Bool

noncomputable def sourceElementSeedEnumeration [Countable α] :
    ℕ → SourceElementSeed α := by
  classical
  exact Classical.choose
    (exists_surjective_nat (SourceElementSeed α))

theorem sourceElementSeedEnumeration_surjective [Countable α] :
    Function.Surjective
      (sourceElementSeedEnumeration (α := α)) := by
  classical
  exact Classical.choose_spec
    (exists_surjective_nat (SourceElementSeed α))

noncomputable def sourceElementInnerCandidate
    [Countable α] [Infinite α]
    (strategy : SourceElementMistakeStrategy α) (n : ℕ) : Set α := by
  classical
  let seed := sourceElementSeedEnumeration (α := α) n
  let S := sourceElementSelfSet strategy seed.1 seed.2
  exact if hS : S.Infinite then S else Set.univ

theorem sourceElementInnerCandidate_infinite
    [Countable α] [Infinite α]
    (strategy : SourceElementMistakeStrategy α) (n : ℕ) :
    (sourceElementInnerCandidate strategy n).Infinite := by
  classical
  simp only [sourceElementInnerCandidate]
  split_ifs with hS
  · exact hS
  · exact Set.infinite_univ

/-- Theorem 3.1, necessity: exact element-valued mistake generation yields a
countable inner cover. -/
def countableInnerCoverOfSourceElementMistake
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (strategy : SourceElementMistakeStrategy α)
    (hstrategy : SourceElementMistakeGenerates strategy targets) :
    CountableInnerCover targets where
  cover := sourceElementInnerCandidate strategy
  infinite_cover := sourceElementInnerCandidate_infinite strategy
  contained := by
    classical
    intro L hL
    obtain ⟨seed, hseed, _hseedWithin, hlock⟩ :=
      exists_sourceElementMistake_lock
        (hinfinite L hL) (hstrategy L hL)
    let bits := sourceElementFeedback strategy L seed
    obtain ⟨n, hn⟩ :=
      sourceElementSeedEnumeration_surjective (seed, bits)
    refine ⟨n, ?_⟩
    have hInf :
        (sourceElementSelfSet strategy seed bits).Infinite := by
      simpa [bits] using
        sourceElementSelfSet_infinite_of_lock
          strategy L seed hseed hlock
    change
      (if hS :
          (sourceElementSelfSet strategy
            (sourceElementSeedEnumeration (α := α) n).1
            (sourceElementSeedEnumeration (α := α) n).2).Infinite
        then
          sourceElementSelfSet strategy
            (sourceElementSeedEnumeration (α := α) n).1
            (sourceElementSeedEnumeration (α := α) n).2
        else Set.univ) ⊆ L
    rw [hn, dif_pos hInf]
    simpa [bits] using
      sourceElementSelfSet_subset_of_lock
        strategy L seed hseed hlock

theorem sourceElementMistake_implies_countableInnerCover
    [Countable α] [Infinite α]
    {targets : LanguageClass α}
    (hinfinite : ∀ L, L ∈ targets → L.Infinite)
    (h : SourceElementMistakeGeneratable targets) :
    HasCountableInnerCover targets := by
  obtain ⟨strategy, hstrategy⟩ := h
  exact
    ⟨countableInnerCoverOfSourceElementMistake
      hinfinite strategy hstrategy⟩

/-! ## Inner-cover sufficiency -/

/-- The first `t+1` observations are obtained by appending the observation
at time `t` to the first `t` observations. -/
theorem source_streamPrefix_succ
    (stream : Stream α) (t : ℕ) :
    streamPrefix stream (t + 1) =
      streamPrefix stream t ++ [stream t] := by
  exact GenLimit.textPrefix_succ stream t

/-- A finite subset of an exact presentation is eventually contained in
every later ordered prefix. -/
theorem source_finset_eventually_mem_streamPrefix
    {stream : Stream α} (F : Finset α)
    (hF : (F : Set α) ⊆ Set.range stream) :
    ∃ T, ∀ t, T ≤ t → ∀ x ∈ F, x ∈ streamPrefix stream t := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x F hx ih =>
      have hxRange : x ∈ Set.range stream :=
        hF (by simp)
      obtain ⟨n, hn⟩ := hxRange
      have hFRange : (F : Set α) ⊆ Set.range stream := by
        intro y hy
        exact hF (by simp [hy])
      obtain ⟨T, hT⟩ := ih hFRange
      refine ⟨max (n + 1) T, ?_⟩
      intro t ht y hy
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · rw [streamPrefix, GenLimit.mem_textPrefix_iff]
        exact
          ⟨n,
            lt_of_lt_of_le (Nat.lt_succ_self n)
              ((Nat.le_max_left (n + 1) T).trans ht),
            hn⟩
      · exact hT t ((Nat.le_max_right (n + 1) T).trans ht) y hy

theorem source_mem_sequenceSample_list_get_iff
    {samples : List α} {x : α} :
    x ∈ Generic.sequenceSample samples.get ↔ x ∈ samples := by
  classical
  rw [Generic.mem_sequenceSample_iff, List.mem_iff_get]

/-- Appendix A.1's cover-search element strategy.  Its active cover index is
one plus the number of preceding negative bits (zero-based here), and it
outputs the canonically first member not already shown by the adversary. -/
noncomputable def innerCoverSourceElementStrategy
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    SourceElementMistakeStrategy α := by
  classical
  intro samples bits
  let candidate :=
    inner.cover (bits.count false) \
      ((Generic.sequenceSample samples.get : Finset α) : Set α)
  have hcandidate : candidate.Infinite :=
    (inner.infinite_cover (bits.count false)).diff
      (Generic.sequenceSample samples.get).finite_toSet
  exact sourceFirst candidate hcandidate.nonempty

theorem innerCoverSourceElementStrategy_mem
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (samples : List α) (bits : List Bool) :
    innerCoverSourceElementStrategy inner samples bits ∈
      inner.cover (bits.count false) \
        ((Generic.sequenceSample samples.get : Finset α) : Set α) := by
  classical
  simp only [innerCoverSourceElementStrategy]
  exact sourceFirst_mem _ <|
    ((inner.infinite_cover (bits.count false)).diff
      (Generic.sequenceSample samples.get).finite_toSet).nonempty

theorem innerCoverSourceElementStrategy_rank_le
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (samples : List α) (bits : List Bool)
    {x : α}
    (hx :
      x ∈ inner.cover (bits.count false) \
        ((Generic.sequenceSample samples.get : Finset α) : Set α)) :
    sourceCanonicalRank
        (innerCoverSourceElementStrategy inner samples bits) ≤
      sourceCanonicalRank x := by
  classical
  simp only [innerCoverSourceElementStrategy]
  apply sourceFirst_rank_le
  exact hx

/-- The active zero-based inner-cover index along the truthful interaction. -/
noncomputable def sourceElementPhase
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : ℕ :=
  (sourceElementFeedback strategy target
    (streamPrefix stream t)).count false

@[simp] theorem sourceElementPhase_zero
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) :
    sourceElementPhase strategy target stream 0 = 0 := by
  simp [sourceElementPhase, sourceElementFeedback,
    sourceElementFeedbackRun, streamPrefix]

@[simp] theorem sourceElementPhase_one
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) :
    sourceElementPhase strategy target stream 1 = 0 := by
  rw [sourceElementPhase, show streamPrefix stream 1 = [stream 0] by
    simpa [streamPrefix] using GenLimit.textPrefix_succ stream 0]
  simp [sourceElementFeedback,
    sourceElementFeedbackRun, sourceElementFeedbackStep]

theorem sourceElementPhase_succ
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) {t : ℕ}
    (ht : 0 < t) :
    sourceElementPhase strategy target stream (t + 1) =
      sourceElementPhase strategy target stream t +
        [sourceElementReply target (streamPrefix stream t)
          (sourceElementOutput strategy target
            (streamPrefix stream t))].count false := by
  classical
  rw [sourceElementPhase, source_streamPrefix_succ,
    sourceElementFeedback_append]
  · simp [sourceElementPhase, sourceElementOutput, List.count_append]
  · exact List.ne_nil_of_length_pos (by simpa [streamPrefix] using ht)

theorem sourceElementPhase_mono_step
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    sourceElementPhase strategy target stream t ≤
      sourceElementPhase strategy target stream (t + 1) := by
  by_cases ht : t = 0
  · subst t
    simp
  · rw [sourceElementPhase_succ strategy target stream
      (Nat.pos_of_ne_zero ht)]
    omega

theorem sourceElementPhase_step_le
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    sourceElementPhase strategy target stream (t + 1) ≤
      sourceElementPhase strategy target stream t + 1 := by
  by_cases ht : t = 0
  · subst t
    simp
  · rw [sourceElementPhase_succ strategy target stream
      (Nat.pos_of_ne_zero ht)]
    cases sourceElementReply target (streamPrefix stream t)
      (sourceElementOutput strategy target (streamPrefix stream t)) <;>
      simp

theorem sourceElementPhase_mono
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) {s t : ℕ}
    (hst : s ≤ t) :
    sourceElementPhase strategy target stream s ≤
      sourceElementPhase strategy target stream t := by
  induction t, hst using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ t _ ih =>
      exact ih.trans
        (sourceElementPhase_mono_step strategy target stream t)

theorem sourceElementPhase_succ_of_false
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) {t : ℕ}
    (ht : 0 < t)
    (hfalse :
      sourceElementReply target (streamPrefix stream t)
        (sourceElementOutput strategy target
          (streamPrefix stream t)) = false) :
    sourceElementPhase strategy target stream (t + 1) =
      sourceElementPhase strategy target stream t + 1 := by
  rw [sourceElementPhase_succ strategy target stream ht, hfalse]
  simp

theorem sourceElementPhase_succ_of_true
    (strategy : SourceElementMistakeStrategy α)
    (target : Set α) (stream : Stream α) {t : ℕ}
    (ht : 0 < t)
    (htrue :
      sourceElementReply target (streamPrefix stream t)
        (sourceElementOutput strategy target
          (streamPrefix stream t)) = true) :
    sourceElementPhase strategy target stream (t + 1) =
      sourceElementPhase strategy target stream t := by
  rw [sourceElementPhase_succ strategy target stream ht, htrue]
  simp

private theorem innerCoverSourceElement_output_mem
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    sourceElementOutput
        (innerCoverSourceElementStrategy inner) target
        (streamPrefix stream t) ∈
      inner.cover
          (sourceElementPhase
            (innerCoverSourceElementStrategy inner) target stream t) \
        ((Generic.sequenceSample (streamPrefix stream t).get : Finset α) :
          Set α) := by
  simpa [sourceElementOutput, sourceElementPhase] using
    innerCoverSourceElementStrategy_mem inner
      (streamPrefix stream t)
      (sourceElementFeedback
        (innerCoverSourceElementStrategy inner) target
        (streamPrefix stream t))

private theorem innerCoverSourceElement_output_rank_le
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (stream : Stream α) (t : ℕ)
    {x : α}
    (hx :
      x ∈
        inner.cover
            (sourceElementPhase
              (innerCoverSourceElementStrategy inner) target stream t) \
          ((Generic.sequenceSample (streamPrefix stream t).get : Finset α) :
            Set α)) :
    sourceCanonicalRank
        (sourceElementOutput
          (innerCoverSourceElementStrategy inner) target
          (streamPrefix stream t)) ≤
      sourceCanonicalRank x := by
  simpa [sourceElementOutput, sourceElementPhase] using
    innerCoverSourceElementStrategy_rank_le inner
      (streamPrefix stream t)
      (sourceElementFeedback
        (innerCoverSourceElementStrategy inner) target
        (streamPrefix stream t)) hx

/-- Once the active index is a cover contained in the target, its next bit is
positive and the phase remains fixed. -/
theorem innerCoverSourceElement_good_phase_stays
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (stream : Stream α)
    {k t : ℕ} (ht : 0 < t)
    (hphase :
      sourceElementPhase
        (innerCoverSourceElementStrategy inner) target stream t = k)
    (hgood : inner.cover k ⊆ target) :
    sourceElementPhase
        (innerCoverSourceElementStrategy inner) target stream (t + 1) = k := by
  have hout :=
    innerCoverSourceElement_output_mem inner target stream t
  rw [hphase] at hout
  have hreply :
      sourceElementReply target (streamPrefix stream t)
        (sourceElementOutput
          (innerCoverSourceElementStrategy inner) target
          (streamPrefix stream t)) = true := by
    rw [sourceElementReply_eq_true_iff]
    exact
      ⟨hgood hout.1,
        fun hmem =>
          hout.2
            (source_mem_sequenceSample_list_get_iff.mpr hmem)⟩
  rw [sourceElementPhase_succ_of_true
    (innerCoverSourceElementStrategy inner) target stream ht hreply,
    hphase]

/-- The cover search can never pass the least cover contained in the target. -/
theorem innerCoverSourceElement_phase_le_good
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (stream : Stream α)
    (k : ℕ) (hgood : inner.cover k ⊆ target) :
    ∀ t,
      sourceElementPhase
        (innerCoverSourceElementStrategy inner) target stream t ≤ k := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      by_cases htk :
          sourceElementPhase
            (innerCoverSourceElementStrategy inner) target stream t = k
      · by_cases ht0 : t = 0
        · subst t
          simp
        · rw [innerCoverSourceElement_good_phase_stays
            inner target stream (Nat.pos_of_ne_zero ht0) htk hgood]
      · have hlt :
            sourceElementPhase
              (innerCoverSourceElementStrategy inner) target stream t < k :=
          lt_of_le_of_ne ih htk
        exact
          (sourceElementPhase_step_le
            (innerCoverSourceElementStrategy inner) target stream t).trans
            (Nat.succ_le_iff.mpr hlt)

/-- If phase `i` is still active after every lower-ranked positive member of
cover `i` has appeared, the next proposal is the least negative witness. -/
theorem innerCoverSourceElement_false_at_exposed_phase
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (stream : Stream α)
    (hstream : Set.range stream ⊆ target)
    {i t : ℕ}
    (hphase :
      sourceElementPhase
        (innerCoverSourceElementStrategy inner) target stream t = i)
    (hbad : ¬ inner.cover i ⊆ target)
    (hexposed :
      ∀ x, x ∈ inner.cover i →
        sourceCanonicalRank x <
          sourceCanonicalRank
            (sourceFirst (inner.cover i \ target)
              (Set.not_subset.mp hbad)) →
        x ∈ streamPrefix stream t) :
    sourceElementReply target (streamPrefix stream t)
        (sourceElementOutput
          (innerCoverSourceElementStrategy inner) target
          (streamPrefix stream t)) = false := by
  classical
  let badFirst :=
    sourceFirst (inner.cover i \ target) (Set.not_subset.mp hbad)
  have hbadFirst : badFirst ∈ inner.cover i \ target :=
    sourceFirst_mem _ _
  have hbadUnseen : badFirst ∉ streamPrefix stream t := by
    intro hmem
    rw [streamPrefix, GenLimit.mem_textPrefix_iff] at hmem
    obtain ⟨q, _hqLt, hq⟩ := hmem
    exact hbadFirst.2 (hstream ⟨q, hq⟩)
  have hbadCandidate :
      badFirst ∈
        inner.cover
            (sourceElementPhase
              (innerCoverSourceElementStrategy inner) target stream t) \
          ((Generic.sequenceSample (streamPrefix stream t).get : Finset α) :
            Set α) := by
    rw [hphase]
    exact
      ⟨hbadFirst.1,
        fun hmem =>
          hbadUnseen
            (source_mem_sequenceSample_list_get_iff.mp hmem)⟩
  let output :=
    sourceElementOutput
      (innerCoverSourceElementStrategy inner) target
      (streamPrefix stream t)
  have houtputMem :=
    innerCoverSourceElement_output_mem inner target stream t
  rw [hphase] at houtputMem
  have hrankLe :
      sourceCanonicalRank output ≤ sourceCanonicalRank badFirst :=
    innerCoverSourceElement_output_rank_le
      inner target stream t hbadCandidate
  have hnotLt :
      ¬ sourceCanonicalRank output < sourceCanonicalRank badFirst := by
    intro hlt
    have hexposedOutput : output ∈ streamPrefix stream t :=
      hexposed output houtputMem.1 hlt
    exact houtputMem.2
      (source_mem_sequenceSample_list_get_iff.mpr hexposedOutput)
  have hrankEq :
      sourceCanonicalRank output = sourceCanonicalRank badFirst :=
    Nat.le_antisymm hrankLe (Nat.le_of_not_gt hnotLt)
  have houtputEq : output = badFirst :=
    sourceCanonicalRank_injective hrankEq
  simp [sourceElementReply, output, houtputEq, hbadFirst.2]

/-- Every index below the least good cover is eventually rejected, so the
cover-search phase reaches that least good index. -/
theorem innerCoverSourceElement_eventually_reaches
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (target : Set α) (stream : Stream α)
    (hPresents : Generic.Presents stream target)
    (k : ℕ) (hgood : inner.cover k ⊆ target)
    (hminimal : ∀ i, i < k → ¬ inner.cover i ⊆ target) :
    ∃ T, 0 < T ∧
      sourceElementPhase
        (innerCoverSourceElementStrategy inner) target stream T = k := by
  have hphaseLe :=
    innerCoverSourceElement_phase_le_good
      inner target stream k hgood
  have hstream : Set.range stream ⊆ target := by
    rw [hPresents]
  have hreach :
      ∀ i, i ≤ k →
        ∃ T, 0 < T ∧ i ≤
          sourceElementPhase
            (innerCoverSourceElementStrategy inner) target stream T := by
    intro i hik
    induction i with
    | zero => exact ⟨1, by omega, by simp⟩
    | succ i ih =>
        have hik' : i ≤ k := Nat.le_trans (Nat.le_succ i) hik
        obtain ⟨T, hTpos, hTi⟩ := ih hik'
        have hi_lt_k : i < k := by omega
        have hbad := hminimal i hi_lt_k
        let badFirst :=
          sourceFirst (inner.cover i \ target) (Set.not_subset.mp hbad)
        let prior : Set α :=
          {x | x ∈ inner.cover i ∧
            sourceCanonicalRank x < sourceCanonicalRank badFirst}
        have hpriorFinite : prior.Finite := by
          apply (sourceCanonicalRank_lt_finite
            (sourceCanonicalRank badFirst)).subset
          intro x hx
          exact hx.2
        have hpriorTarget : prior ⊆ target := by
          intro x hx
          by_contra hxTarget
          have hxBad : x ∈ inner.cover i \ target :=
            ⟨hx.1, hxTarget⟩
          have hleast :
              sourceCanonicalRank badFirst ≤ sourceCanonicalRank x := by
            dsimp [badFirst]
            exact sourceFirst_rank_le _ _ hxBad
          exact (Nat.not_lt_of_ge hleast) hx.2
        let priorFinset := hpriorFinite.toFinset
        have hpriorRange :
            (priorFinset : Set α) ⊆ Set.range stream := by
          intro x hx
          rw [hPresents]
          exact hpriorTarget (by simpa [priorFinset] using hx)
        obtain ⟨U₀, hU₀⟩ :=
          source_finset_eventually_mem_streamPrefix
            priorFinset hpriorRange
        let U := max T (max U₀ 1)
        have hTU : T ≤ U := Nat.le_max_left _ _
        have hUpos : 0 < U :=
          lt_of_lt_of_le (by omega : 0 < 1)
            ((Nat.le_max_right U₀ 1).trans
              (Nat.le_max_right T (max U₀ 1)))
        have hphaseUi : i ≤
            sourceElementPhase
              (innerCoverSourceElementStrategy inner) target stream U :=
          hTi.trans
            (sourceElementPhase_mono
              (innerCoverSourceElementStrategy inner) target stream hTU)
        by_cases hdone :
            i + 1 ≤
              sourceElementPhase
                (innerCoverSourceElementStrategy inner) target stream U
        · exact ⟨U, hUpos, hdone⟩
        · have hphaseU :
              sourceElementPhase
                (innerCoverSourceElementStrategy inner) target stream U = i := by
            omega
          have hexposed :
              ∀ x, x ∈ inner.cover i →
                sourceCanonicalRank x <
                    sourceCanonicalRank
                      (sourceFirst (inner.cover i \ target)
                        (Set.not_subset.mp hbad)) →
                  x ∈ streamPrefix stream U := by
            intro x hxCover hxRank
            apply hU₀ U
              ((Nat.le_max_left U₀ 1).trans
                (Nat.le_max_right T (max U₀ 1)))
            simpa [priorFinset, prior, badFirst] using
              (show x ∈ prior from ⟨hxCover, hxRank⟩)
          have hfalse :=
            innerCoverSourceElement_false_at_exposed_phase
              inner target stream hstream hphaseU hbad hexposed
          refine ⟨U + 1, by omega, ?_⟩
          rw [sourceElementPhase_succ_of_false
            (innerCoverSourceElementStrategy inner) target stream
            hUpos hfalse, hphaseU]
  obtain ⟨T, hTpos, hkT⟩ := hreach k (Nat.le_refl k)
  exact ⟨T, hTpos, Nat.le_antisymm (hphaseLe T) hkT⟩

/-- Theorem 3.1, sufficiency: a countable inner cover yields the exact
element-valued mistake-feedback generator from Appendix A.1. -/
theorem countableInnerCover_implies_sourceElementMistake
    [Countable α]
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    SourceElementMistakeGeneratable targets := by
  classical
  let inner := Nonempty.some hinner
  refine ⟨innerCoverSourceElementStrategy inner, ?_⟩
  intro L hL stream hPresents
  let hexists : ∃ i, inner.cover i ⊆ L :=
    inner.contained L hL
  let k := Nat.find hexists
  have hgood : inner.cover k ⊆ L := by
    simpa [k] using Nat.find_spec hexists
  have hminimal : ∀ i, i < k → ¬ inner.cover i ⊆ L := by
    intro i hi
    exact Nat.find_min hexists (by simpa [k] using hi)
  obtain ⟨T, hTpos, hphaseT⟩ :=
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
  have hout :=
    innerCoverSourceElement_output_mem inner L stream t
  rw [hphase] at hout
  exact
    ⟨hgood hout.1,
      fun hmem =>
        hout.2
          (source_mem_sequenceSample_list_get_iff.mpr hmem)⟩

/-- Source Theorem 3.1: the exact element-valued mistake-feedback
characterization for classes of infinite languages over a countable
universe. -/
theorem theorem_3_1_elementMistake_characterization
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    SourceElementMistakeGeneratable targets ↔
      HasCountableInnerCover targets :=
  ⟨sourceElementMistake_implies_countableInnerCover hinfinite,
    countableInnerCover_implies_sourceElementMistake⟩

end GenLimit.FeedbackQueries
