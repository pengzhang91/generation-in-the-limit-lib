import GenLimit.Core.GenericGeneration
import Mathlib.Data.Finset.Image

/-!
# Safe language generation: paper-facing definitions

This file formalizes the positive/negative occurrence model used by
Anastasopoulos--Ateniese--Kornaropoulos, *Safe Language Generation in the
Limit*, arXiv:2601.08648v2.

An occurrence is tagged rather than assigning one permanent label to each
example.  This matters when an example belongs to both the target and the
harmful language: the same value may then occur once with each tag.
-/

namespace GenLimit.SafeGeneration

open GenLimit.Generic

/-- A labeled occurrence.  `true` marks the target-language enumeration and
`false` marks the harmful-language enumeration. -/
abbrev Tagged (α : Type*) := α × Bool

/-- Values with tag `b` in a finite labeled history. -/
noncomputable def historyTaggedSample
    {t : ℕ} (xs : Fin t → Tagged α) (b : Bool) : Finset α := by
  classical
  exact (Finset.univ.filter fun n => (xs n).2 = b).image fun n => (xs n).1

/-- Values in a finite labeled history, with tags forgotten. -/
noncomputable def historyObservedSample
    {t : ℕ} (xs : Fin t → Tagged α) : Finset α := by
  exact Generic.sequenceSample fun n => (xs n).1

/-- The values carrying tag `b` among the first `t` occurrences. -/
noncomputable def taggedSample
    (stream : Stream (Tagged α)) (b : Bool) (t : ℕ) : Finset α := by
  exact historyTaggedSample (fun i : Fin t => stream i) b

/-- All values that ever carry tag `b`. -/
def taggedRange (stream : Stream (Tagged α)) (b : Bool) : Set α :=
  {x | ∃ n, stream n = (x, b)}

/-- A merged labeled presentation enumerates each component exactly. -/
def LabeledPresents
    (stream : Stream (Tagged α))
    (target harmful : Generic.Language α) : Prop :=
  taggedRange stream true = target ∧ taggedRange stream false = harmful

/-- All values, with labels forgotten, among the first `t` occurrences. -/
noncomputable def observedSample
    (stream : Stream (Tagged α)) (t : ℕ) : Finset α := by
  exact Generic.sample (fun n => (stream n).1) t

theorem historyTaggedSample_prefix
    (stream : Stream (Tagged α)) (b : Bool) (t : ℕ) :
    historyTaggedSample (fun i : Fin t => stream i) b =
      taggedSample stream b t :=
  rfl

theorem historyObservedSample_prefix
    (stream : Stream (Tagged α)) (t : ℕ) :
    historyObservedSample (fun i : Fin t => stream i) =
      observedSample stream t := by
  simpa [historyObservedSample, observedSample] using
    (Generic.sequenceSample_prefix (fun n => (stream n).1) t)

theorem mem_taggedSample_iff
    {stream : Stream (Tagged α)} {b : Bool} {t : ℕ} {x : α} :
    x ∈ taggedSample stream b t ↔ ∃ n < t, stream n = (x, b) := by
  classical
  constructor
  · intro hx
    rw [taggedSample] at hx
    obtain ⟨n, hn, hnx⟩ := Finset.mem_image.mp hx
    have hn' := Finset.mem_filter.mp hn
    refine ⟨n, n.isLt, ?_⟩
    apply Prod.ext
    · simpa using hnx
    · exact hn'.2
  · rintro ⟨n, hnt, hn⟩
    rw [taggedSample]
    apply Finset.mem_image.mpr
    refine ⟨⟨n, hnt⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · simp [hn]
    · simp [hn]

theorem mem_observedSample_iff
    {stream : Stream (Tagged α)} {t : ℕ} {x : α} :
    x ∈ observedSample stream t ↔ ∃ n < t, (stream n).1 = x := by
  simpa [observedSample] using
    (Generic.mem_sample_iff
      (stream := fun n => (stream n).1) (t := t) (x := x))

theorem taggedSample_subset_observedSample
    (stream : Stream (Tagged α)) (b : Bool) (t : ℕ) :
    taggedSample stream b t ⊆ observedSample stream t := by
  intro x hx
  obtain ⟨n, hnt, hn⟩ := mem_taggedSample_iff.mp hx
  exact mem_observedSample_iff.mpr ⟨n, hnt, by simp [hn]⟩

theorem taggedSample_mono
    {stream : Stream (Tagged α)} {b : Bool} {s t : ℕ} (hst : s ≤ t) :
    taggedSample stream b s ⊆ taggedSample stream b t := by
  intro x hx
  obtain ⟨n, hns, hn⟩ := mem_taggedSample_iff.mp hx
  exact mem_taggedSample_iff.mpr ⟨n, lt_of_lt_of_le hns hst, hn⟩

theorem observedSample_mono
    {stream : Stream (Tagged α)} {s t : ℕ} (hst : s ≤ t) :
    observedSample stream s ⊆ observedSample stream t := by
  intro x hx
  obtain ⟨n, hns, hn⟩ := mem_observedSample_iff.mp hx
  exact mem_observedSample_iff.mpr ⟨n, lt_of_lt_of_le hns hst, hn⟩

theorem eventually_mem_taggedSample
    {stream : Stream (Tagged α)} {b : Bool} {L : Generic.Language α}
    (hP : taggedRange stream b = L) {x : α} (hx : x ∈ L) :
    ∃ T, ∀ t, T ≤ t → x ∈ taggedSample stream b t := by
  rw [← hP] at hx
  obtain ⟨n, hn⟩ := hx
  refine ⟨n + 1, ?_⟩
  intro t ht
  exact mem_taggedSample_iff.mpr
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) ht, hn⟩

theorem finset_eventually_subset_taggedSample
    {stream : Stream (Tagged α)} {b : Bool} {L : Generic.Language α}
    (hP : taggedRange stream b = L)
    (S : Finset α) (hS : (↑S : Set α) ⊆ L) :
    ∃ T, ∀ t, T ≤ t → S ⊆ taggedSample stream b t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x S hxS ih =>
      have hxL : x ∈ L := hS (by simp)
      have hSL : (↑S : Set α) ⊆ L := by
        intro y hy
        exact hS (by simp [hy])
      obtain ⟨Tx, hTx⟩ := eventually_mem_taggedSample hP hxL
      obtain ⟨TS, hTS⟩ := ih hSL
      refine ⟨max Tx TS, ?_⟩
      intro t ht y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hTx t (le_trans (Nat.le_max_left _ _) ht)
      · exact hTS t (le_trans (Nat.le_max_right _ _) ht) hy

/-- A safe generator may either emit a value or the bottom marker `none`. -/
abbrev SafeGenerator (α : Type*) :=
  ∀ t : ℕ, (Fin t → Tagged α) → Option α

/-- Run a safe generator on the prefix strictly before time `t`. -/
def safeOutput
    (G : SafeGenerator α) (stream : Stream (Tagged α)) (t : ℕ) : Option α :=
  G t fun i => stream i

/-- Correct output in the infinite-difference regime of Definition 2. -/
def SafeCorrectAt
    (G : SafeGenerator α) (target harmful : Generic.Language α)
    (stream : Stream (Tagged α)) (t : ℕ) : Prop :=
  ∃ x, safeOutput G stream t = some x ∧
    x ∈ target \ harmful ∧ x ∉ observedSample stream t

/-- Correct bottom output in the finite-difference regime of Definition 2. -/
def BottomCorrectAt
    (G : SafeGenerator α) (target harmful : Generic.Language α)
    (stream : Stream (Tagged α)) (t : ℕ) : Prop :=
  (target \ harmful).Finite ∧ safeOutput G stream t = none

/-- Literal semantic content of safe generation (Definition 2), split on
whether the safe difference is infinite or finite. -/
def SafelyGenerates
    (G : SafeGenerator α) (target harmful : Generic.Language α)
    (stream : Stream (Tagged α)) : Prop :=
  ((target \ harmful).Infinite →
      ∃ T, ∀ t, T ≤ t → SafeCorrectAt G target harmful stream t) ∧
  ((target \ harmful).Finite →
      ∃ T, ∀ t, T ≤ t → BottomCorrectAt G target harmful stream t)

/-- The only asymptotic obligation in Definition 2's finite-difference
branch: the generator eventually emits bottom on the fixed run. -/
def EventuallyBottom
    (G : SafeGenerator α) (stream : Stream (Tagged α)) : Prop :=
  ∃ T, ∀ t, T ≤ t → safeOutput G stream t = none

/-- Once the safe difference is finite, Definition 2 is exactly eventual
bottom output; its size and contents no longer occur in the obligation. -/
theorem safelyGenerates_iff_eventuallyBottom_of_finite
    (G : SafeGenerator α) (target harmful : Generic.Language α)
    (stream : Stream (Tagged α))
    (hfinite : (target \ harmful).Finite) :
    SafelyGenerates G target harmful stream ↔
      EventuallyBottom G stream := by
  constructor
  · intro hsafe
    obtain ⟨T, hT⟩ := hsafe.2 hfinite
    exact ⟨T, fun t ht => (hT t ht).2⟩
  · rintro ⟨T, hT⟩
    constructor
    · intro hinfinite
      exact (hinfinite hfinite).elim
    · intro _
      exact ⟨T, fun t ht => ⟨hfinite, hT t ht⟩⟩

/-- On one fixed run, all finite safe differences impose the same success
predicate.  In particular Definition 2 cannot distinguish an empty
difference from a singleton difference through their eventual behavior. -/
theorem safelyGenerates_iff_of_finite_differences
    (G : SafeGenerator α)
    (target₁ harmful₁ target₂ harmful₂ : Generic.Language α)
    (stream : Stream (Tagged α))
    (hfinite₁ : (target₁ \ harmful₁).Finite)
    (hfinite₂ : (target₂ \ harmful₂).Finite) :
    SafelyGenerates G target₁ harmful₁ stream ↔
      SafelyGenerates G target₂ harmful₂ stream :=
  (safelyGenerates_iff_eventuallyBottom_of_finite
    G target₁ harmful₁ stream hfinite₁).trans
    (safelyGenerates_iff_eventuallyBottom_of_finite
      G target₂ harmful₂ stream hfinite₂).symm

/-- Definition 2 with its outer quantifiers over both indexed families and
every valid merged labeled presentation. -/
def SafelyGeneratesFamilies
    (G : SafeGenerator α)
    (targets harmfuls : Generic.LanguageFamily α) : Prop :=
  ∀ i j stream, LabeledPresents stream (targets i) (harmfuls j) →
    SafelyGenerates G (targets i) (harmfuls j) stream

/-- Definition 3 (`SG∞`): every cross-pair difference is infinite. -/
def AllCrossDifferencesInfinite
    (targets harmfuls : Generic.LanguageFamily α) : Prop :=
  ∀ i j, (targets i \ harmfuls j).Infinite

/-- Paper-facing success criterion for the `SG∞` model. -/
def SafelyGeneratesInfiniteDifferences
    (G : SafeGenerator α)
    (targets harmfuls : Generic.LanguageFamily α) : Prop :=
  ∀ i j stream, LabeledPresents stream (targets i) (harmfuls j) →
    ∃ T, ∀ t, T ≤ t → SafeCorrectAt G (targets i) (harmfuls j) stream t

end GenLimit.SafeGeneration
