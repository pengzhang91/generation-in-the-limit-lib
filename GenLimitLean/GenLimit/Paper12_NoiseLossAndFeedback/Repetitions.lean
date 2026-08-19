import GenLimit.Paper12_NoiseLossAndFeedback.InfiniteOmissions
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Nth

/-!
# Noise, Loss, and Feedback: Appendix A repetitions

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Definitions A.1--A.3 and
Lemmas A.4--A.6.

The source's Algorithm 7 removes repeated observations before calling a
generator designed for repetition-free enumerations.  `firstOccurrences`
implements that transformation on the finite prefix supplied to the
generator, so the adapter is causal by construction.

There is a small indexing defect in the printed proofs of Lemmas A.4--A.5.
Their `d*` is chosen separately from each enumeration as the first raw time
at which `t*` distinct values have appeared.  That is not a uniform
distinct-cardinality threshold, and paper time `t*` in the repetition-free
model has already exposed `t* + 1` values (`x_0,...,x_t*`).  The repaired
proof below uses the enumeration-independent threshold `D = T + 1`.  A
repeated prefix with at least `D` distinct values deduplicates to a prefix of
length at least `T + 1`, so the original generator is invoked at paper time
at least `T`.

The printed proof of Lemma A.6 has a separate type error: it starts from a
non-uniform generator rather than a generator in the limit, and later refers
to an undefined `d*`.  Moreover, any such threshold must be allowed to
depend on the repeated presentation.  The repaired proof constructs the
single exact stream of first occurrences, obtains its presentation-dependent
limit time `T`, and chooses as raw burn-in the time of its `T`-th
zero-indexed first occurrence.

As throughout the paper, the equivalence is stated for classes of infinite
languages.  This hypothesis is semantically necessary: finite targets have
repetition-allowing presentations but no injective infinite presentations.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-! ## Definitions A.1--A.3 -/

/-- A full enumeration in which observations may repeat. -/
def RepetitionEnumeration
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  GenLimit.Generic.Presents stream L

/-- Definition A.1 at a fixed generator.  The threshold counts distinct
observations, including the current observation. -/
def IsUniformRepetitionGenerator
    (gen : Generator α) (C : LanguageClass α) : Prop :=
  ∃ D : ℕ, ∀ L, L ∈ C → ∀ stream,
    RepetitionEnumeration stream L →
      ∀ t, D ≤ (observedThrough stream t).card →
        CorrectAt gen L stream t

/-- Existential generator wrapper for Definition A.1. -/
def UniformlyGeneratableWithRepetitions
    (C : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsUniformRepetitionGenerator gen C

/-- Definition A.2 at a fixed generator.  The distinct-cardinality threshold
may depend on the target, but not on its enumeration. -/
def IsNonuniformRepetitionGenerator
    (gen : Generator α) (C : LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∃ D : ℕ, ∀ stream,
    RepetitionEnumeration stream L →
      ∀ t, D ≤ (observedThrough stream t).card →
        CorrectAt gen L stream t

/-- Existential generator wrapper for Definition A.2. -/
def NonuniformlyGeneratableWithRepetitions
    (C : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsNonuniformRepetitionGenerator gen C

/-- Definition A.3 at a fixed generator.  Here the raw-time threshold may
depend on both the target and its repetition-allowing enumeration. -/
def IsLimitRepetitionGenerator
    (gen : Generator α) (C : LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∀ stream,
    RepetitionEnumeration stream L →
      ∃ T : ℕ, ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Existential generator wrapper for Definition A.3. -/
def GeneratableInLimitWithRepetitions
    (C : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsLimitRepetitionGenerator gen C

/-- Generation in the limit at a fixed generator in the paper's standard
repetition-free model.  The burn-in may depend on the target and on its exact
enumeration. -/
def IsLimitGeneratorWithoutRepetitions
    (gen : Generator α) (C : LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∀ stream,
    ExactEnumeration stream L →
      ∃ T : ℕ, ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Existential generation in the limit in the paper's standard
repetition-free model. -/
def GeneratableInLimitWithoutRepetitions
    (C : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsLimitGeneratorWithoutRepetitions gen C

/-- Existential uniform generation in the paper's standard repetition-free
model. -/
def UniformlyGeneratableWithoutRepetitions
    (C : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsUniformGenerator gen C

/-- Existential non-uniform generation in the paper's standard
repetition-free model. -/
def NonuniformlyGeneratableWithoutRepetitions
    (C : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsNonuniformGenerator gen C

/-! ## The causal first-occurrence adapter -/

/-- Remove all but the leftmost occurrence of each value.  Lean's
`List.dedup` keeps rightmost occurrences, so reversing before and after
deduplication implements the source's first-occurrence order. -/
noncomputable def firstOccurrences {n : ℕ} (xs : Fin n → α) : List α := by
  classical
  exact (List.ofFn xs).reverse.dedup.reverse

theorem firstOccurrences_nodup {n : ℕ} (xs : Fin n → α) :
    (firstOccurrences xs).Nodup := by
  classical
  rw [firstOccurrences, List.nodup_reverse]
  exact List.nodup_dedup _

theorem mem_firstOccurrences_iff {n : ℕ} {xs : Fin n → α} {x : α} :
    x ∈ firstOccurrences xs ↔ ∃ i : Fin n, xs i = x := by
  classical
  simp [firstOccurrences]

theorem firstOccurrences_toFinset [DecidableEq α]
    {n : ℕ} (xs : Fin n → α) :
    (firstOccurrences xs).toFinset =
      GenLimit.Generic.sequenceSample xs := by
  ext x
  constructor
  · intro hx
    exact GenLimit.Generic.mem_sequenceSample_iff.mpr
      (mem_firstOccurrences_iff.mp (List.mem_toFinset.mp hx))
  · intro hx
    exact List.mem_toFinset.mpr
      (mem_firstOccurrences_iff.mpr
        (GenLimit.Generic.mem_sequenceSample_iff.mp hx))

theorem firstOccurrences_length {n : ℕ} (xs : Fin n → α) :
    (firstOccurrences xs).length =
      (GenLimit.Generic.sequenceSample xs).card := by
  classical
  rw [← firstOccurrences_toFinset]
  exact
    (List.toFinset_card_of_nodup
      (firstOccurrences_nodup xs)).symm

theorem firstOccurrences_prefix_toFinset
    [DecidableEq α]
    (stream : GenLimit.Generic.Stream α) (n : ℕ) :
    (firstOccurrences (fun i : Fin n => stream i)).toFinset =
      GenLimit.Generic.sample stream n := by
  rw [firstOccurrences_toFinset,
    GenLimit.Generic.sequenceSample_prefix]

theorem firstOccurrences_prefix_length
    (stream : GenLimit.Generic.Stream α) (n : ℕ) :
    (firstOccurrences (fun i : Fin n => stream i)).length =
      (GenLimit.Generic.sample stream n).card := by
  rw [firstOccurrences_length,
    GenLimit.Generic.sequenceSample_prefix]

/-- On an already repetition-free finite history, the adapter preserves the
history exactly, including its order. -/
theorem firstOccurrences_eq_of_injective
    {n : ℕ} (xs : Fin n → α) (hxs : Function.Injective xs) :
    firstOccurrences xs = List.ofFn xs := by
  classical
  unfold firstOccurrences
  have hnodup : (List.ofFn xs).Nodup :=
    List.nodup_ofFn.mpr hxs
  rw [List.dedup_eq_self.mpr (List.nodup_reverse.mpr hnodup)]
  simp

/-- Algorithm 7: call `gen` on the distinct observations in their
first-occurrence order.  Only the supplied finite history is inspected. -/
noncomputable def repetitionAdapter
    (gen : Generator α) : Generator α :=
  fun _ xs =>
    let ys := firstOccurrences xs
    gen ys.length fun i => ys.get i

/-! ## The canonical first-occurrence stream -/

/-- Raw time `t` is a first-occurrence time when the value observed at `t`
did not occur at any earlier raw time. -/
def IsFirstOccurrence
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  ∀ i, i < t → stream i ≠ stream t

/-- The raw time of the `k`-th first occurrence, in increasing order. -/
noncomputable def firstOccurrenceTime
    (stream : GenLimit.Generic.Stream α) (k : ℕ) : ℕ :=
  Nat.nth (IsFirstOccurrence stream) k

/-- The repetition-free stream obtained by retaining the first occurrence of
each value of the raw stream. -/
noncomputable def firstOccurrenceStream
    (stream : GenLimit.Generic.Stream α) : GenLimit.Generic.Stream α :=
  fun k => stream (firstOccurrenceTime stream k)

private theorem leftDedup_concat_of_mem
    [DecidableEq α]
    (xs : List α) (x : α) (hx : x ∈ xs) :
    (xs.concat x).reverse.dedup.reverse =
      xs.reverse.dedup.reverse := by
  classical
  rw [List.concat_eq_append, List.reverse_concat',
    List.dedup_cons_of_mem]
  simpa using hx

private theorem leftDedup_concat_of_notMem
    [DecidableEq α]
    (xs : List α) (x : α) (hx : x ∉ xs) :
    (xs.concat x).reverse.dedup.reverse =
      (xs.reverse.dedup.reverse).concat x := by
  classical
  rw [List.concat_eq_append, List.reverse_concat',
    List.dedup_cons_of_notMem]
  · simp [List.concat_eq_append]
  · simpa using hx

/-- A new first occurrence is appended to the causal first-occurrence
prefix. -/
theorem firstOccurrences_succ_of_firstOccurrence
    (stream : GenLimit.Generic.Stream α) (n : ℕ) :
    IsFirstOccurrence stream n →
      firstOccurrences (fun i : Fin (n + 1) => stream i) =
        (firstOccurrences (fun i : Fin n => stream i)).concat (stream n) := by
  classical
  intro hn
  unfold firstOccurrences
  rw [List.ofFn_succ']
  apply leftDedup_concat_of_notMem
  intro hmem
  rw [List.mem_ofFn] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact hn i i.isLt (by simpa using hi)

/-- A repeated observation leaves the causal first-occurrence prefix
unchanged. -/
theorem firstOccurrences_succ_of_not_firstOccurrence
    (stream : GenLimit.Generic.Stream α) (n : ℕ) :
    ¬IsFirstOccurrence stream n →
      firstOccurrences (fun i : Fin (n + 1) => stream i) =
        firstOccurrences (fun i : Fin n => stream i) := by
  classical
  intro hn
  simp only [IsFirstOccurrence] at hn
  push_neg at hn
  obtain ⟨i, hi, hivalue⟩ := hn
  unfold firstOccurrences
  rw [List.ofFn_succ']
  apply leftDedup_concat_of_mem
  rw [List.mem_ofFn]
  exact ⟨⟨i, hi⟩, by simpa using hivalue⟩

/-- Every value in the range of a stream occurs at a first-occurrence time. -/
theorem range_subset_image_firstOccurrence
    (stream : GenLimit.Generic.Stream α) :
    Set.range stream ⊆
      stream '' {t | IsFirstOccurrence stream t} := by
  classical
  rintro x ⟨n, rfl⟩
  let hexists : ∃ i, stream i = stream n := ⟨n, rfl⟩
  let t := Nat.find hexists
  have htvalue : stream t = stream n :=
    Nat.find_spec hexists
  have hfirst : IsFirstOccurrence stream t := by
    intro i hi hit
    have hivalue : stream i = stream n :=
      hit.trans htvalue
    have hti : t ≤ i :=
      Nat.find_min' hexists hivalue
    omega
  exact ⟨t, hfirst, htvalue⟩

/-- An infinite-range stream has infinitely many first-occurrence times. -/
theorem firstOccurrenceTimes_infinite
    {stream : GenLimit.Generic.Stream α}
    (hrange : (Set.range stream).Infinite) :
    {t | IsFirstOccurrence stream t}.Infinite := by
  intro hfinite
  exact hrange
    ((hfinite.image stream).subset
      (range_subset_image_firstOccurrence stream))

theorem firstOccurrenceTime_mem
    {stream : GenLimit.Generic.Stream α}
    (hfresh : {t | IsFirstOccurrence stream t}.Infinite)
    (k : ℕ) :
    IsFirstOccurrence stream (firstOccurrenceTime stream k) := by
  exact Nat.nth_mem_of_infinite hfresh k

theorem firstOccurrenceTime_strictMono
    {stream : GenLimit.Generic.Stream α}
    (hfresh : {t | IsFirstOccurrence stream t}.Infinite) :
    StrictMono (firstOccurrenceTime stream) := by
  exact Nat.nth_strictMono hfresh

theorem firstOccurrenceStream_injective
    {stream : GenLimit.Generic.Stream α}
    (hfresh : {t | IsFirstOccurrence stream t}.Infinite) :
    Function.Injective (firstOccurrenceStream stream) := by
  intro i j hij
  rcases lt_trichotomy i j with hijOrder | hijEq | hjiOrder
  · have htime :
        firstOccurrenceTime stream i <
          firstOccurrenceTime stream j :=
      firstOccurrenceTime_strictMono hfresh hijOrder
    have hfreshJ :=
      firstOccurrenceTime_mem hfresh j
    exact False.elim
      ((hfreshJ (firstOccurrenceTime stream i) htime)
        (by simpa [firstOccurrenceStream] using hij))
  · exact hijEq
  · have htime :
        firstOccurrenceTime stream j <
          firstOccurrenceTime stream i :=
      firstOccurrenceTime_strictMono hfresh hjiOrder
    have hfreshI :=
      firstOccurrenceTime_mem hfresh i
    exact False.elim
      ((hfreshI (firstOccurrenceTime stream j) htime)
        (by simpa [firstOccurrenceStream] using hij.symm))

theorem firstOccurrenceStream_range
    {stream : GenLimit.Generic.Stream α}
    (hfresh : {t | IsFirstOccurrence stream t}.Infinite) :
    Set.range (firstOccurrenceStream stream) = Set.range stream := by
  apply Set.Subset.antisymm
  · rintro x ⟨k, rfl⟩
    exact ⟨firstOccurrenceTime stream k, rfl⟩
  · intro x hx
    obtain ⟨t, htFresh, htValue⟩ :=
      range_subset_image_firstOccurrence stream hx
    have htRange :
        t ∈ Set.range (firstOccurrenceTime stream) := by
      change t ∈ Set.range (Nat.nth (IsFirstOccurrence stream))
      rw [Nat.range_nth_of_infinite hfresh]
      exact htFresh
    obtain ⟨k, hk⟩ := htRange
    exact ⟨k, by simpa [firstOccurrenceStream, hk] using htValue⟩

theorem firstOccurrenceStream_exactEnumeration
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hL : L.Infinite)
    (hstream : RepetitionEnumeration stream L) :
    ExactEnumeration (firstOccurrenceStream stream) L := by
  have hrange : (Set.range stream).Infinite := by
    rw [hstream]
    exact hL
  let hfresh := firstOccurrenceTimes_infinite hrange
  exact
    ⟨firstOccurrenceStream_injective hfresh,
      (firstOccurrenceStream_range hfresh).trans hstream⟩

/-- The number of first-occurrence times strictly before raw time `n`. -/
noncomputable def firstOccurrenceCount
    (stream : GenLimit.Generic.Stream α) (n : ℕ) : ℕ := by
  classical
  exact Nat.count (IsFirstOccurrence stream) n

/-- The finite causal adapter is exactly the prefix of the canonical
first-occurrence stream. -/
theorem firstOccurrences_eq_firstOccurrenceStream_prefix
    {stream : GenLimit.Generic.Stream α}
    (n : ℕ) :
    firstOccurrences (fun i : Fin n => stream i) =
      List.ofFn
        (fun k : Fin (firstOccurrenceCount stream n) =>
          firstOccurrenceStream stream k) := by
  classical
  induction n with
  | zero =>
      simp [firstOccurrences, firstOccurrenceCount]
  | succ n ih =>
      by_cases hn : IsFirstOccurrence stream n
      · rw [firstOccurrences_succ_of_firstOccurrence stream n hn, ih]
        have hcount :
            firstOccurrenceCount stream (Nat.succ n) =
              firstOccurrenceCount stream n + 1 := by
          simp [firstOccurrenceCount, Nat.count_succ, hn,
            Nat.succ_eq_add_one]
        rw [hcount, List.ofFn_succ']
        congr 1
        have htime :
            Nat.nth (IsFirstOccurrence stream)
                (firstOccurrenceCount stream n) = n := by
          simpa [firstOccurrenceCount] using (Nat.nth_count hn)
        exact (congrArg stream htime).symm
      · rw [firstOccurrences_succ_of_not_firstOccurrence stream n hn, ih]
        have hcount :
            firstOccurrenceCount stream (Nat.succ n) =
              firstOccurrenceCount stream n := by
          simp [firstOccurrenceCount, Nat.count_succ, hn,
            Nat.succ_eq_add_one]
        rw [hcount]

/-- Counting first-occurrence times is the same as counting distinct values
in the corresponding raw prefix. -/
theorem firstOccurrenceCount_eq_sample_card
    (stream : GenLimit.Generic.Stream α) (n : ℕ) :
    firstOccurrenceCount stream n =
      (GenLimit.Generic.sample stream n).card := by
  classical
  calc
    firstOccurrenceCount stream n =
        (List.ofFn
          (fun k : Fin (firstOccurrenceCount stream n) =>
            firstOccurrenceStream stream k)).length := by simp
    _ = (firstOccurrences (fun i : Fin n => stream i)).length :=
      congrArg List.length
        (firstOccurrences_eq_firstOccurrenceStream_prefix n).symm
    _ = (GenLimit.Generic.sample stream n).card :=
      firstOccurrences_prefix_length stream n

/-! ## Completing the deduplicated prefix -/

theorem sequenceSample_get_eq_toFinset
    [DecidableEq α] (ys : List α) :
    GenLimit.Generic.sequenceSample
        (fun i : Fin ys.length => ys.get i) =
      ys.toFinset := by
  ext x
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact List.mem_toFinset.mpr
      (List.mem_iff_get.mpr ⟨i, hi⟩)
  · intro hx
    exact List.mem_iff_get.mp (List.mem_toFinset.mp hx)

/-- Any finite repetition-free list of target values extends to an exact
repetition-free enumeration of an infinite target. -/
theorem exactEnumeration_extending_nodup_list
    [Countable α]
    {L : GenLimit.Generic.Language α} (hL : L.Infinite)
    (ys : List α) (hys : ys.Nodup)
    (hysL : ∀ i : Fin ys.length, ys.get i ∈ L) :
    ∃ full : GenLimit.Generic.Stream α,
      ExactEnumeration full L ∧
      (∀ i : Fin ys.length, full i = ys.get i) := by
  let xs : Fin ys.length → α := fun i => ys.get i
  have hxs : Function.Injective xs :=
    List.nodup_iff_injective_get.mp hys
  let hrest :
      (L \ (GenLimit.Generic.sequenceSample xs : Set α)).Infinite :=
    hL.diff (GenLimit.Generic.sequenceSample xs).finite_toSet
  let full := prefixThenTarget xs L hrest
  refine ⟨full, ?_, ?_⟩
  · exact
      ⟨prefixThenTarget_injective hxs L hrest,
        prefixThenTarget_range L hysL hrest⟩
  · intro i
    exact prefixThenTarget_prefix xs L hrest i

theorem sample_eq_toFinset_of_prefix_get
    [DecidableEq α]
    {full : GenLimit.Generic.Stream α} (ys : List α)
    (hprefix : ∀ i : Fin ys.length, full i = ys.get i) :
    GenLimit.Generic.sample full ys.length = ys.toFinset := by
  rw [← GenLimit.Generic.sequenceSample_prefix full ys.length,
    ← sequenceSample_get_eq_toFinset ys]
  congr 1
  funext i
  exact hprefix i

theorem firstOccurrenceCount_succ_pos
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    0 < firstOccurrenceCount stream (t + 1) := by
  classical
  rw [firstOccurrenceCount_eq_sample_card]
  exact Finset.card_pos.mpr
    ⟨stream t,
      GenLimit.Generic.value_mem_sample (Nat.lt_succ_self t)⟩

/-- At every raw time, the causal adapter's output is exactly the original
generator's output on the corresponding prefix of the canonical
first-occurrence stream. -/
theorem repetitionAdapter_outputAt_eq_firstOccurrenceStream
    {gen : Generator α}
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    outputAt (repetitionAdapter gen) stream t =
      outputAt gen (firstOccurrenceStream stream)
        (firstOccurrenceCount stream (t + 1) - 1) := by
  classical
  have hpositive :
      0 < firstOccurrenceCount stream (t + 1) :=
    firstOccurrenceCount_succ_pos stream t
  have hlength :
      firstOccurrenceCount stream (t + 1) - 1 + 1 =
        firstOccurrenceCount stream (t + 1) :=
    Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpositive))
  unfold outputAt GenLimit.Generic.output repetitionAdapter
  dsimp only
  rw [firstOccurrences_eq_firstOccurrenceStream_prefix, hlength]
  have hlistLength :
      (List.ofFn
        (fun k : Fin (firstOccurrenceCount stream (t + 1)) =>
          firstOccurrenceStream stream k)).length =
        firstOccurrenceCount stream (t + 1) := by
    simp
  congr 1
  refine (Fin.heq_fun_iff hlistLength).2 ?_
  intro i
  simp

/-- The corresponding first-occurrence prefix contains exactly the distinct
values in the raw prefix. -/
theorem firstOccurrenceStream_observedThrough_eq
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    observedThrough (firstOccurrenceStream stream)
        (firstOccurrenceCount stream (t + 1) - 1) =
      observedThrough stream t := by
  classical
  have hpositive :
      0 < firstOccurrenceCount stream (t + 1) :=
    firstOccurrenceCount_succ_pos stream t
  have hlength :
      firstOccurrenceCount stream (t + 1) - 1 + 1 =
        firstOccurrenceCount stream (t + 1) :=
    Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpositive))
  have hprefix :=
    firstOccurrences_eq_firstOccurrenceStream_prefix
      (stream := stream) (t + 1)
  unfold observedThrough
  rw [hlength, ← GenLimit.Generic.sequenceSample_prefix,
    ← GenLimit.Generic.sequenceSample_prefix]
  ext x
  simp only [GenLimit.Generic.mem_sequenceSample_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hxList :
        x ∈ List.ofFn
          (fun j : Fin (firstOccurrenceCount stream (t + 1)) =>
            firstOccurrenceStream stream j) :=
      List.mem_ofFn.mpr ⟨k, hk⟩
    rw [← hprefix] at hxList
    exact mem_firstOccurrences_iff.mp hxList
  · intro hx
    have hxList :
        x ∈ firstOccurrences (fun i : Fin (t + 1) => stream i) :=
      mem_firstOccurrences_iff.mpr hx
    rw [hprefix] at hxList
    exact List.mem_ofFn.mp hxList

/-- Correctness at raw time `t` is therefore correctness at the matching
paper time of the canonical first-occurrence stream. -/
theorem repetitionAdapter_correctAt_firstOccurrenceStream_iff
    {gen : Generator α}
    {L : GenLimit.Generic.Language α}
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    CorrectAt (repetitionAdapter gen) L stream t ↔
      CorrectAt gen L (firstOccurrenceStream stream)
        (firstOccurrenceCount stream (t + 1) - 1) := by
  rw [CorrectAt, CorrectAt,
    repetitionAdapter_outputAt_eq_firstOccurrenceStream,
    firstOccurrenceStream_observedThrough_eq]

/-! ## The repaired forward implication -/

/-- Semantic core of Lemmas A.4--A.5.  A repetition-free generator correct
from paper time `T` becomes correct on a repeated prefix once that prefix has
at least `T + 1` distinct observations. -/
theorem repetitionAdapter_correctAt
    [Countable α]
    {gen : Generator α} {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t T : ℕ}
    (hL : L.Infinite)
    (hstream : RepetitionEnumeration stream L)
    (hcard : T + 1 ≤ (observedThrough stream t).card)
    (hcorrect :
      ∀ full : GenLimit.Generic.Stream α, ExactEnumeration full L →
        ∀ r, T ≤ r → CorrectAt gen L full r) :
    CorrectAt (repetitionAdapter gen) L stream t := by
  classical
  let xs : Fin (t + 1) → α := fun i => stream i
  let ys : List α := firstOccurrences xs
  have hysNodup : ys.Nodup :=
    firstOccurrences_nodup xs
  have hysLength :
      ys.length = (observedThrough stream t).card := by
    simpa [ys, xs, observedThrough] using
      firstOccurrences_prefix_length stream (t + 1)
  have hysL : ∀ i : Fin ys.length, ys.get i ∈ L := by
    intro i
    apply GenLimit.Generic.mem_language_of_mem_sample_of_presents hstream
    have hiMem : ys.get i ∈ ys.toFinset := by
      exact List.mem_toFinset.mpr (List.get_mem ys i)
    have hset :
        ys.toFinset = GenLimit.Generic.sample stream (t + 1) := by
      simpa [ys, xs] using
        firstOccurrences_prefix_toFinset stream (t + 1)
    exact hset ▸ hiMem
  obtain ⟨full, hfull, hprefix⟩ :=
    exactEnumeration_extending_nodup_list hL ys hysNodup hysL
  have hpositive : 0 < ys.length := by
    omega
  have htime : T ≤ ys.length - 1 := by
    omega
  have hlength : ys.length - 1 + 1 = ys.length :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpositive))
  have hbase :=
    hcorrect full hfull (ys.length - 1) htime
  have hout :
      outputAt (repetitionAdapter gen) stream t =
        outputAt gen full (ys.length - 1) := by
    change
      gen ys.length (fun i => ys.get i) =
        gen (ys.length - 1 + 1) (fun i => full i)
    rw [hlength]
    congr 1
    funext i
    exact (hprefix i).symm
  have hsample :
      observedThrough full (ys.length - 1) =
        observedThrough stream t := by
    unfold observedThrough
    rw [hlength, sample_eq_toFinset_of_prefix_get ys hprefix]
    simpa [ys, xs] using
      firstOccurrences_prefix_toFinset stream (t + 1)
  simpa [CorrectAt, hout, hsample] using hbase

theorem uniform_withoutRepetitions_to_withRepetitions
    [Countable α]
    {gen : Generator α} {C : LanguageClass α}
    (hInfinite : ∀ L, L ∈ C → L.Infinite)
    (hgen : IsUniformGenerator gen C) :
    IsUniformRepetitionGenerator (repetitionAdapter gen) C := by
  obtain ⟨T, hT⟩ := hgen
  refine ⟨T + 1, ?_⟩
  intro L hLC stream hstream t hcard
  exact repetitionAdapter_correctAt
    (hInfinite L hLC) hstream hcard (hT L hLC)

theorem nonuniform_withoutRepetitions_to_withRepetitions
    [Countable α]
    {gen : Generator α} {C : LanguageClass α}
    (hInfinite : ∀ L, L ∈ C → L.Infinite)
    (hgen : IsNonuniformGenerator gen C) :
    IsNonuniformRepetitionGenerator (repetitionAdapter gen) C := by
  intro L hLC
  obtain ⟨T, hT⟩ := hgen L hLC
  refine ⟨T + 1, ?_⟩
  intro stream hstream t hcard
  exact repetitionAdapter_correctAt
    (hInfinite L hLC) hstream hcard hT

/-- Repaired forward implication of Lemma A.6.  Unlike the uniform and
non-uniform cases, the successful paper time may depend on the exact
deduplicated presentation.  We therefore apply the original generator once
to the single canonical first-occurrence stream and translate its threshold
back to raw time. -/
theorem limit_withoutRepetitions_to_withRepetitions
    {gen : Generator α} {C : LanguageClass α}
    (hInfinite : ∀ L, L ∈ C → L.Infinite)
    (hgen : IsLimitGeneratorWithoutRepetitions gen C) :
    IsLimitRepetitionGenerator (repetitionAdapter gen) C := by
  classical
  intro L hLC stream hstream
  have hL : L.Infinite :=
    hInfinite L hLC
  have hfull :
      ExactEnumeration (firstOccurrenceStream stream) L :=
    firstOccurrenceStream_exactEnumeration hL hstream
  have hrange : (Set.range stream).Infinite := by
    rw [hstream]
    exact hL
  have hfresh :
      {t | IsFirstOccurrence stream t}.Infinite :=
    firstOccurrenceTimes_infinite hrange
  obtain ⟨T, hT⟩ :=
    hgen L hLC (firstOccurrenceStream stream) hfull
  refine ⟨firstOccurrenceTime stream T, ?_⟩
  intro t ht
  apply
    (repetitionAdapter_correctAt_firstOccurrenceStream_iff
      (gen := gen) (L := L) stream t).2
  apply hT
  have hnthlt :
      firstOccurrenceTime stream T < t + 1 := by
    omega
  have hTcountNat :
      T < Nat.count (IsFirstOccurrence stream) (t + 1) := by
    exact
      (Nat.lt_nth_iff_count_lt hfresh).2
        (by simpa [firstOccurrenceTime] using hnthlt)
  have hTcount :
      T < firstOccurrenceCount stream (t + 1) := by
    simpa [firstOccurrenceCount] using hTcountNat
  omega

/-! ## The immediate reverse implication -/

theorem observedThrough_card_of_injective
    (stream : GenLimit.Generic.Stream α)
    (hstream : Function.Injective stream) (t : ℕ) :
    (observedThrough stream t).card = t + 1 := by
  classical
  unfold observedThrough GenLimit.Generic.sample
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact hstream hij

theorem uniform_withRepetitions_to_withoutRepetitions
    {gen : Generator α} {C : LanguageClass α}
    (hgen : IsUniformRepetitionGenerator gen C) :
    IsUniformGenerator gen C := by
  obtain ⟨D, hD⟩ := hgen
  refine ⟨D, ?_⟩
  intro L hLC stream hstream t ht
  apply hD L hLC stream hstream.2 t
  rw [observedThrough_card_of_injective stream hstream.1 t]
  omega

theorem nonuniform_withRepetitions_to_withoutRepetitions
    {gen : Generator α} {C : LanguageClass α}
    (hgen : IsNonuniformRepetitionGenerator gen C) :
    IsNonuniformGenerator gen C := by
  intro L hLC
  obtain ⟨D, hD⟩ := hgen L hLC
  refine ⟨D, ?_⟩
  intro stream hstream t ht
  apply hD stream hstream.2 t
  rw [observedThrough_card_of_injective stream hstream.1 t]
  omega

theorem limit_withRepetitions_to_withoutRepetitions
    {gen : Generator α} {C : LanguageClass α}
    (hgen : IsLimitRepetitionGenerator gen C) :
    IsLimitGeneratorWithoutRepetitions gen C := by
  intro L hLC stream hstream
  exact hgen L hLC stream hstream.2

/-! ## Lemmas A.4--A.6 -/

/-- Lemma A.4: uniform generation is unchanged when adversarial
enumerations are allowed to repeat values. -/
theorem lemma_a_4
    [Countable α]
    (C : LanguageClass α)
    (hInfinite : ∀ L, L ∈ C → L.Infinite) :
    UniformlyGeneratableWithoutRepetitions C ↔
      UniformlyGeneratableWithRepetitions C := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact
      ⟨repetitionAdapter gen,
        uniform_withoutRepetitions_to_withRepetitions hInfinite hgen⟩
  · rintro ⟨gen, hgen⟩
    exact
      ⟨gen, uniform_withRepetitions_to_withoutRepetitions hgen⟩

/-- Lemma A.5: non-uniform generation is likewise unchanged by adversarial
repetitions. -/
theorem lemma_a_5
    [Countable α]
    (C : LanguageClass α)
    (hInfinite : ∀ L, L ∈ C → L.Infinite) :
    NonuniformlyGeneratableWithoutRepetitions C ↔
      NonuniformlyGeneratableWithRepetitions C := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact
      ⟨repetitionAdapter gen,
        nonuniform_withoutRepetitions_to_withRepetitions hInfinite hgen⟩
  · rintro ⟨gen, hgen⟩
    exact
      ⟨gen, nonuniform_withRepetitions_to_withoutRepetitions hgen⟩

/-- Lemma A.6: generation in the limit is unchanged by adversarial
repetitions.  The infinite-language hypothesis is necessary because finite
targets have repeated presentations but no injective infinite
presentations. -/
theorem lemma_a_6
    [Countable α]
    (C : LanguageClass α)
    (hInfinite : ∀ L, L ∈ C → L.Infinite) :
    GeneratableInLimitWithoutRepetitions C ↔
      GeneratableInLimitWithRepetitions C := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact
      ⟨repetitionAdapter gen,
        limit_withoutRepetitions_to_withRepetitions hInfinite hgen⟩
  · rintro ⟨gen, hgen⟩
    exact
      ⟨gen, limit_withRepetitions_to_withoutRepetitions hgen⟩

end GenLimit.NoiseLossFeedback
