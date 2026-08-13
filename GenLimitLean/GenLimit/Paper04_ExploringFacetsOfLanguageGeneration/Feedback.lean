import GenLimit.Paper02_GenerationThroughTheLensOfLearningTheory.Closure
import Mathlib.Data.Set.Countable

/-!
# Charikar--Pabbaraju: generation with feedback

This file formalizes the alternating strategy model in Section 7 of
Charikar--Pabbaraju, *Exploring Facets of Language Generation in the Limit*,
arXiv:2411.15364v2.

Paper rounds are one-based.  Lean round `t` is zero-based, and
`feedbackSampleThrough A G t` contains the inputs in rounds `0,...,t`.
Consequently the paper condition `r ≥ d` is written `d ≤ t + 1`.

The definitions below retain the fact that the adversary sees earlier
generator outputs.  In particular, the continuation lemma does not replace
the paper's strategy model by an arbitrary finite transcript: it constructs
an actual adversary which replays a finite interaction prefix and then
completes an exact presentation of a selected consistent language.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic
open GenLimit.LiRamanTewari

/-! ## Alternating feedback strategies and their unique interaction -/

/-- One completed feedback round `(x_t,y_t,a_t,z_t)`. -/
structure FeedbackRound (α : Type*) where
  input : α
  query : α
  answer : Bool
  output : α
deriving DecidableEq

/-- The generator first chooses a membership query after seeing the new
positive input, and then chooses its output after receiving the answer. -/
structure FeedbackGeneratorStrategy (α : Type*) where
  query : List (FeedbackRound α) → α → α
  output : List (FeedbackRound α) → α → α → Bool → α

/-- The adversary chooses the next positive input after completed rounds and
answers the current membership query. -/
structure FeedbackAdversaryStrategy (α : Type*) where
  input : List (FeedbackRound α) → α
  answer : List (FeedbackRound α) → α → α → Bool

def feedbackNextRound
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α)
    (h : List (FeedbackRound α)) : FeedbackRound α :=
  let x := A.input h
  let y := G.query h x
  let a := A.answer h x y
  let z := G.output h x y a
  ⟨x, y, a, z⟩

/-- The first `n` completed rounds of the unique interaction. -/
def feedbackHistory
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) : ℕ → List (FeedbackRound α)
  | 0 => []
  | n + 1 =>
      let h := feedbackHistory A G n
      h ++ [feedbackNextRound A G h]

@[simp] theorem feedbackHistory_zero
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) :
    feedbackHistory A G 0 = [] :=
  rfl

@[simp] theorem feedbackHistory_succ
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (n : ℕ) :
    feedbackHistory A G (n + 1) =
      feedbackHistory A G n ++
        [feedbackNextRound A G (feedbackHistory A G n)] :=
  rfl

@[simp] theorem feedbackHistory_length
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (n : ℕ) :
    (feedbackHistory A G n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [feedbackHistory, ih]

/-- Round `t` of the interaction, before appending it to the history. -/
def feedbackRound
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (t : ℕ) : FeedbackRound α :=
  feedbackNextRound A G (feedbackHistory A G t)

def feedbackInput
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) : Stream α :=
  fun t => (feedbackRound A G t).input

def feedbackQuery
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) : Stream α :=
  fun t => (feedbackRound A G t).query

def feedbackAnswer
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) : ℕ → Bool :=
  fun t => (feedbackRound A G t).answer

def feedbackOutput
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) : Stream α :=
  fun t => (feedbackRound A G t).output

/-- The paper's `S_t`, with zero-based Lean round `t` included. -/
noncomputable def feedbackSampleThrough
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (t : ℕ) : Finset α :=
  Generic.sample (feedbackInput A G) (t + 1)

theorem feedbackSampleThrough_card_le
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (t : ℕ) :
    (feedbackSampleThrough A G t).card ≤ t + 1 :=
  Generic.sample_card_le _ _

/-- A feedback adversary is consistent with `K` exactly when its positive
inputs present all of `K` and every answer is truthful. -/
def FeedbackAdversaryConsistent
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (K : Set α) : Prop :=
  Generic.Presents (feedbackInput A G) K ∧
    ∀ t, feedbackAnswer A G t = true ↔ feedbackQuery A G t ∈ K

/-- Languages consistent with every input and query answer through round
`t`, as in Section 7.2. -/
def feedbackConsistentLanguagesThrough
    (C : Generic.LanguageClass α)
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (t : ℕ) :
    Set (Generic.Language α) :=
  {L | L ∈ C ∧
    (↑(feedbackSampleThrough A G t) : Set α) ⊆ L ∧
    ∀ s, s ≤ t →
      (feedbackAnswer A G s = true ↔ feedbackQuery A G s ∈ L)}

/-- Equation (13) in the feedback model: the common intersection of all
consistent languages, with the observed sample removed. -/
def feedbackEffectiveIntersection
    (C : Generic.LanguageClass α)
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (t : ℕ) : Set α :=
  {x | ∀ L, L ∈ feedbackConsistentLanguagesThrough C A G t → x ∈ L} \
    (↑(feedbackSampleThrough A G t) : Set α)

theorem target_mem_feedbackConsistentLanguagesThrough
    {C : Generic.LanguageClass α}
    {A : FeedbackAdversaryStrategy α}
    {G : FeedbackGeneratorStrategy α} {K : Set α}
    (hK : K ∈ C) (hA : FeedbackAdversaryConsistent A G K) (t : ℕ) :
    K ∈ feedbackConsistentLanguagesThrough C A G t := by
  refine ⟨hK, ?_, ?_⟩
  · intro x hx
    exact Generic.mem_language_of_mem_sample_of_presents hA.1 hx
  · intro s _hs
    exact hA.2 s

theorem feedbackConsistentLanguagesThrough_nonempty
    {C : Generic.LanguageClass α}
    {A : FeedbackAdversaryStrategy α}
    {G : FeedbackGeneratorStrategy α} {K : Set α}
    (hK : K ∈ C) (hA : FeedbackAdversaryConsistent A G K) (t : ℕ) :
    (feedbackConsistentLanguagesThrough C A G t).Nonempty :=
  ⟨K, target_mem_feedbackConsistentLanguagesThrough hK hA t⟩

/-! ## Finite transcript semantics

These definitions expose the paper's consistent-language intersection as a
function of a finite transcript.  Generator outputs are retained in the
history because the adversary may react to them, but they do not enter the
consistency test itself.
-/

def feedbackHistoryObserved (h : List (FeedbackRound α)) : Set α :=
  {x | ∃ q ∈ h, q.input = x}

def feedbackHistoryConsistentLanguages
    (C : Generic.LanguageClass α) (h : List (FeedbackRound α)) :
    Set (Generic.Language α) :=
  {L | L ∈ C ∧ feedbackHistoryObserved h ⊆ L ∧
    ∀ q ∈ h, q.answer = true ↔ q.query ∈ L}

def feedbackHistoryEffectiveIntersection
    (C : Generic.LanguageClass α) (h : List (FeedbackRound α)) : Set α :=
  {x | ∀ L, L ∈ feedbackHistoryConsistentLanguages C h → x ∈ L} \
    feedbackHistoryObserved h

theorem mem_feedbackHistory_iff
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) {n : ℕ} {q : FeedbackRound α} :
    q ∈ feedbackHistory A G n ↔
      ∃ s < n, feedbackRound A G s = q := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [feedbackHistory_succ]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (hq | hq)
        · obtain ⟨s, hs, rfl⟩ := ih.mp hq
          exact ⟨s, Nat.lt.step hs, rfl⟩
        · subst q
          exact ⟨n, Nat.lt_succ_self n, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
        · exact Or.inl (ih.mpr ⟨s, hs, rfl⟩)
        · exact Or.inr rfl

theorem feedbackHistoryObserved_eq_sample
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (n : ℕ) :
    feedbackHistoryObserved (feedbackHistory A G n) =
      (↑(Generic.sample (feedbackInput A G) n) : Set α) := by
  ext x
  change (∃ q ∈ feedbackHistory A G n, q.input = x) ↔
    x ∈ Generic.sample (feedbackInput A G) n
  rw [Generic.mem_sample_iff]
  constructor
  · rintro ⟨q, hq, hqx⟩
    obtain ⟨s, hs, hsq⟩ :=
      (mem_feedbackHistory_iff A G).mp hq
    refine ⟨s, hs, ?_⟩
    subst q
    exact hqx
  · rintro ⟨s, hs, hsx⟩
    exact ⟨feedbackRound A G s,
      (mem_feedbackHistory_iff A G).mpr ⟨s, hs, rfl⟩, hsx⟩

theorem feedbackHistoryConsistentLanguages_eq
    (C : Generic.LanguageClass α)
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (t : ℕ) :
    feedbackHistoryConsistentLanguages C (feedbackHistory A G (t + 1)) =
      feedbackConsistentLanguagesThrough C A G t := by
  ext L
  simp only [feedbackHistoryConsistentLanguages,
    feedbackConsistentLanguagesThrough, Set.mem_setOf_eq,
    feedbackHistoryObserved_eq_sample]
  constructor
  · rintro ⟨hLC, hsample, hans⟩
    refine ⟨hLC, hsample, ?_⟩
    intro s hs
    exact hans (feedbackRound A G s)
      ((mem_feedbackHistory_iff A G).mpr
        ⟨s, Nat.lt_succ_iff.mpr hs, rfl⟩)
  · rintro ⟨hLC, hsample, hans⟩
    refine ⟨hLC, hsample, ?_⟩
    intro q hq
    obtain ⟨s, hs, rfl⟩ := (mem_feedbackHistory_iff A G).mp hq
    exact hans s (Nat.lt_succ_iff.mp hs)

theorem feedbackHistoryEffectiveIntersection_eq
    (C : Generic.LanguageClass α)
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (t : ℕ) :
    feedbackHistoryEffectiveIntersection C
        (feedbackHistory A G (t + 1)) =
      feedbackEffectiveIntersection C A G t := by
  rw [feedbackHistoryEffectiveIntersection, feedbackEffectiveIntersection,
    feedbackHistoryConsistentLanguages_eq,
    feedbackHistoryObserved_eq_sample]
  rfl

/-- Add the current input, query, and answer to a history.  The placeholder
output is immaterial to consistency and effective intersection. -/
def feedbackCurrentHistory
    (h : List (FeedbackRound α)) (x y : α) (a : Bool) :
    List (FeedbackRound α) :=
  h ++ [⟨x, y, a, x⟩]

theorem feedbackHistoryEffectiveIntersection_output_irrel
    (C : Generic.LanguageClass α) (h : List (FeedbackRound α))
    (x y : α) (a : Bool) (z₁ z₂ : α) :
    feedbackHistoryEffectiveIntersection C
        (h ++ [⟨x, y, a, z₁⟩]) =
      feedbackHistoryEffectiveIntersection C
        (h ++ [⟨x, y, a, z₂⟩]) := by
  unfold feedbackHistoryEffectiveIntersection
  have hobs :
      feedbackHistoryObserved (h ++ [⟨x, y, a, z₁⟩]) =
        feedbackHistoryObserved (h ++ [⟨x, y, a, z₂⟩]) := by
    ext w
    change
      (∃ q ∈ h ++ [⟨x, y, a, z₁⟩], q.input = w) ↔
        ∃ q ∈ h ++ [⟨x, y, a, z₂⟩], q.input = w
    constructor
    · rintro ⟨q, hq, hqw⟩
      rw [List.mem_append] at hq
      rcases hq with hq | hq
      · exact ⟨q, List.mem_append.mpr (Or.inl hq), hqw⟩
      · simp only [List.mem_singleton] at hq
        subst q
        exact ⟨⟨x, y, a, z₂⟩,
          List.mem_append.mpr (Or.inr (by simp)), hqw⟩
    · rintro ⟨q, hq, hqw⟩
      rw [List.mem_append] at hq
      rcases hq with hq | hq
      · exact ⟨q, List.mem_append.mpr (Or.inl hq), hqw⟩
      · simp only [List.mem_singleton] at hq
        subst q
        exact ⟨⟨x, y, a, z₁⟩,
          List.mem_append.mpr (Or.inr (by simp)), hqw⟩
  have hcons :
      feedbackHistoryConsistentLanguages C (h ++ [⟨x, y, a, z₁⟩]) =
        feedbackHistoryConsistentLanguages C (h ++ [⟨x, y, a, z₂⟩]) := by
    ext L
    simp only [feedbackHistoryConsistentLanguages, Set.mem_setOf_eq]
    rw [hobs]
    constructor
    · rintro ⟨hLC, hsubset, hans⟩
      refine ⟨hLC, hsubset, ?_⟩
      intro q hq
      rw [List.mem_append] at hq
      rcases hq with hq | hq
      · exact hans q (List.mem_append.mpr (Or.inl hq))
      · simp only [List.mem_singleton] at hq
        subst q
        exact hans ⟨x, y, a, z₁⟩
          (List.mem_append.mpr (Or.inr (by simp)))
    · rintro ⟨hLC, hsubset, hans⟩
      refine ⟨hLC, hsubset, ?_⟩
      intro q hq
      rw [List.mem_append] at hq
      rcases hq with hq | hq
      · exact hans q (List.mem_append.mpr (Or.inl hq))
      · simp only [List.mem_singleton] at hq
        subst q
        exact hans ⟨x, y, a, z₂⟩
          (List.mem_append.mpr (Or.inr (by simp)))
  rw [hobs, hcons]

theorem feedbackCurrentHistory_eq_up_to_output
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α) (t : ℕ) :
    feedbackHistoryEffectiveIntersection C
        (feedbackCurrentHistory (feedbackHistory A G t)
          (feedbackInput A G t) (feedbackQuery A G t)
          (feedbackAnswer A G t)) =
      feedbackEffectiveIntersection C A G t := by
  rw [← feedbackHistoryEffectiveIntersection_eq C A G t]
  change feedbackHistoryEffectiveIntersection C
      (feedbackHistory A G t ++
        [⟨feedbackInput A G t, feedbackQuery A G t,
          feedbackAnswer A G t, feedbackInput A G t⟩]) =
    feedbackHistoryEffectiveIntersection C
      (feedbackHistory A G t ++ [feedbackNextRound A G
        (feedbackHistory A G t)])
  simpa [feedbackInput, feedbackQuery, feedbackAnswer, feedbackOutput,
    feedbackRound, feedbackNextRound] using
    feedbackHistoryEffectiveIntersection_output_irrel C
      (feedbackHistory A G t)
      (feedbackInput A G t) (feedbackQuery A G t)
      (feedbackAnswer A G t) (feedbackInput A G t)
      (feedbackOutput A G t)

/-! ## Definition 10: uniform generation with feedback -/

def IsUniformFeedbackGeneratorAt
    (G : FeedbackGeneratorStrategy α)
    (C : Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∀ K, K ∈ C → ∀ A : FeedbackAdversaryStrategy α,
    FeedbackAdversaryConsistent A G K →
    ∀ t, d ≤ (feedbackSampleThrough A G t).card →
      feedbackOutput A G t ∈
        K \ (↑(feedbackSampleThrough A G t) : Set α)

/-- Definition 10 (`def:uniform-generation-with-feedback`). -/
def UniformlyGeneratableWithFeedback
    (C : Generic.LanguageClass α) : Prop :=
  ∃ G : FeedbackGeneratorStrategy α, ∃ d : ℕ,
    IsUniformFeedbackGeneratorAt G C d

/-! ## Definition 11: the GF dimension -/

/-- The property inside Definition 11 for one integer `d`. -/
def GFDimensionAtLeast
    (C : Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∀ G : FeedbackGeneratorStrategy α,
    ∃ K, K ∈ C ∧ ∃ A : FeedbackAdversaryStrategy α,
      FeedbackAdversaryConsistent A G K ∧
      ∃ t, d ≤ t + 1 ∧
        d ≤ (feedbackSampleThrough A G t).card ∧
        feedbackEffectiveIntersection C A G t = ∅

/-- The paper statement that the supremum in Definition 11 is infinite. -/
def HasInfiniteGFDimension
    (C : Generic.LanguageClass α) : Prop :=
  ∀ d : ℕ, GFDimensionAtLeast C d

/-- The paper statement that the supremum in Definition 11 is finite.

Writing this as failure at one finite level avoids an auxiliary extended
natural number.  `GFDimensionAtLeast` is downward closed, so this is
equivalent to boundedness of the source supremum. -/
def HasFiniteGFDimension
    (C : Generic.LanguageClass α) : Prop :=
  ∃ d : ℕ, ¬ GFDimensionAtLeast C d

theorem finiteGFDimension_iff_not_infinite
    (C : Generic.LanguageClass α) :
    HasFiniteGFDimension C ↔ ¬ HasInfiniteGFDimension C := by
  constructor
  · rintro ⟨d, hd⟩ hinf
    exact hd (hinf d)
  · intro h
    unfold HasInfiniteGFDimension at h
    push_neg at h
    exact h

/-! ## Replaying a finite prefix and completing another language -/

/-- A countable nonempty set has an exact positive presentation. -/
noncomputable def presentationOfCountableSet
    [Countable α] (L : Set α) (hL : L.Nonempty) : Stream α := by
  classical
  have hcount : L.Countable :=
    Set.countable_univ.mono (Set.subset_univ L)
  let f : ℕ → L := Classical.choose (hcount.exists_surjective hL)
  exact fun n => f n

theorem presentationOfCountableSet_presents
    [Countable α] (L : Set α) (hL : L.Nonempty) :
    Generic.Presents (presentationOfCountableSet L hL) L := by
  classical
  have hcount : L.Countable :=
    Set.countable_univ.mono (Set.subset_univ L)
  let hf := Classical.choose_spec (hcount.exists_surjective hL)
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    exact (Classical.choose (hcount.exists_surjective hL) n).property
  · intro x hx
    obtain ⟨n, hn⟩ := hf ⟨x, hx⟩
    refine ⟨n, ?_⟩
    exact congrArg Subtype.val hn

/-- Replay `A` for `cutoff` completed rounds.  Thereafter enumerate `L`
and answer every query by membership in `L`. -/
noncomputable def spliceFeedbackAdversary
    [Countable α]
    (A : FeedbackAdversaryStrategy α) (cutoff : ℕ)
    (L : Set α) (hL : L.Nonempty) :
    FeedbackAdversaryStrategy α := by
  classical
  exact
    { input := fun h =>
        if h.length < cutoff then A.input h
        else presentationOfCountableSet L hL (h.length - cutoff)
      answer := fun h x y =>
        if h.length < cutoff then A.answer h x y
        else if y ∈ L then true else false }

theorem feedbackHistory_splice_eq
    [Countable α]
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α)
    (cutoff : ℕ) (L : Set α) (hL : L.Nonempty)
    {n : ℕ} (hn : n ≤ cutoff) :
    feedbackHistory (spliceFeedbackAdversary A cutoff L hL) G n =
      feedbackHistory A G n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < cutoff := Nat.lt_of_succ_le hn
      have ihn : n ≤ cutoff := Nat.le_of_lt hnlt
      rw [feedbackHistory_succ, feedbackHistory_succ, ih ihn]
      congr 1
      simp only [feedbackNextRound, spliceFeedbackAdversary,
        feedbackHistory_length, if_pos hnlt]

theorem feedbackRound_splice_eq
    [Countable α]
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α)
    (cutoff : ℕ) (L : Set α) (hL : L.Nonempty)
    {t : ℕ} (ht : t < cutoff) :
    feedbackRound (spliceFeedbackAdversary A cutoff L hL) G t =
      feedbackRound A G t := by
  unfold feedbackRound
  rw [feedbackHistory_splice_eq A G cutoff L hL (Nat.le_of_lt ht)]
  simp [feedbackNextRound, spliceFeedbackAdversary,
    feedbackHistory_length, ht]

theorem feedbackSampleThrough_splice_eq
    [Countable α]
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α)
    (cutoff : ℕ) (L : Set α) (hL : L.Nonempty)
    {t : ℕ} (ht : t < cutoff) :
    feedbackSampleThrough (spliceFeedbackAdversary A cutoff L hL) G t =
      feedbackSampleThrough A G t := by
  classical
  apply Finset.ext
  intro x
  simp only [feedbackSampleThrough, Generic.mem_sample_iff]
  constructor
  · rintro ⟨s, hs, hxs⟩
    refine ⟨s, hs, ?_⟩
    rw [feedbackInput, feedbackRound_splice_eq A G cutoff L hL
      (lt_of_lt_of_le hs (Nat.succ_le_iff.mpr ht))] at hxs
    exact hxs
  · rintro ⟨s, hs, hxs⟩
    refine ⟨s, hs, ?_⟩
    rw [feedbackInput, feedbackRound_splice_eq A G cutoff L hL
      (lt_of_lt_of_le hs (Nat.succ_le_iff.mpr ht))]
    exact hxs

private theorem feedbackInput_splice_after
    [Countable α]
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α)
    (cutoff : ℕ) (L : Set α) (hL : L.Nonempty)
    (n : ℕ) :
    feedbackInput (spliceFeedbackAdversary A cutoff L hL) G
        (cutoff + n) =
      presentationOfCountableSet L hL n := by
  simp [feedbackInput, feedbackRound, feedbackNextRound,
    spliceFeedbackAdversary, feedbackHistory_length]

/-- The finite-prefix continuation used in the proof of Lemma 7.3. -/
theorem spliceFeedbackAdversary_consistent
    [Countable α]
    {C : Generic.LanguageClass α}
    (A : FeedbackAdversaryStrategy α)
    (G : FeedbackGeneratorStrategy α)
    (t : ℕ) {L : Set α}
    (hL : L ∈ feedbackConsistentLanguagesThrough C A G t)
    (hLnonempty : L.Nonempty) :
    FeedbackAdversaryConsistent
      (spliceFeedbackAdversary A (t + 1) L hLnonempty) G L := by
  classical
  let A' := spliceFeedbackAdversary A (t + 1) L hLnonempty
  constructor
  · apply Set.Subset.antisymm
    · rintro x ⟨n, rfl⟩
      by_cases hn : n < t + 1
      · rw [feedbackInput, feedbackRound_splice_eq A G (t + 1) L
          hLnonempty hn]
        exact hL.2.1 (Generic.mem_sample_iff.mpr
          ⟨n, hn, rfl⟩)
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le
          (Nat.le_of_not_gt hn)
        rw [feedbackInput_splice_after]
        exact (Set.ext_iff.mp
          (presentationOfCountableSet_presents L hLnonempty) _).mp
            ⟨k, rfl⟩
    · intro x hx
      rw [← presentationOfCountableSet_presents L hLnonempty] at hx
      obtain ⟨n, rfl⟩ := hx
      refine ⟨t + 1 + n, ?_⟩
      exact feedbackInput_splice_after A G (t + 1) L hLnonempty n
  · intro n
    by_cases hn : n < t + 1
    · have hround := feedbackRound_splice_eq A G (t + 1) L
        hLnonempty hn
      rw [feedbackAnswer, feedbackQuery, hround]
      exact hL.2.2 n (Nat.lt_succ_iff.mp hn)
    · simp [feedbackAnswer, feedbackQuery, feedbackRound,
        feedbackNextRound, spliceFeedbackAdversary,
        feedbackHistory_length, hn]

/-! ## Lemma 7.3: infinite GF dimension is an obstruction -/

private theorem exists_consistent_language_omitting_output
    {C : Generic.LanguageClass α}
    {A : FeedbackAdversaryStrategy α}
    {G : FeedbackGeneratorStrategy α} {t : ℕ}
    (hempty : feedbackEffectiveIntersection C A G t = ∅)
    (hfresh :
      feedbackOutput A G t ∉ feedbackSampleThrough A G t) :
    ∃ L, L ∈ feedbackConsistentLanguagesThrough C A G t ∧
      feedbackOutput A G t ∉ L := by
  classical
  by_contra h
  push_neg at h
  have hcore :
      feedbackOutput A G t ∈
        {x | ∀ L, L ∈ feedbackConsistentLanguagesThrough C A G t → x ∈ L} :=
    fun L hL => h L hL
  have heff :
      feedbackOutput A G t ∈ feedbackEffectiveIntersection C A G t :=
    ⟨hcore, hfresh⟩
  rw [hempty] at heff
  exact heff

/-- Lemma 7.3 (`lem:gf-lb`), including the paper's adversary splice. -/
theorem infinite_gf_dimension_not_uniformly_generatable
    [Countable α]
    {C : Generic.LanguageClass α}
    (hUUS : UUS C) (hGF : HasInfiniteGFDimension C) :
    ¬ UniformlyGeneratableWithFeedback C := by
  rintro ⟨G, d, hG⟩
  obtain ⟨K, hKC, A, hAK, t, _hdt, hcard, hempty⟩ := hGF d G
  have hvalid := hG K hKC A hAK t hcard
  obtain ⟨L, hLcons, hzL⟩ :=
    exists_consistent_language_omitting_output
      hempty hvalid.2
  let A' := spliceFeedbackAdversary A (t + 1) L
    (hUUS L hLcons.1).nonempty
  have hA' : FeedbackAdversaryConsistent A' G L :=
    spliceFeedbackAdversary_consistent A G t hLcons
      (hUUS L hLcons.1).nonempty
  have hround :
      feedbackRound A' G t = feedbackRound A G t :=
    feedbackRound_splice_eq A G (t + 1) L
      (hUUS L hLcons.1).nonempty (Nat.lt_succ_self t)
  have hsample :
      feedbackSampleThrough A' G t =
        feedbackSampleThrough A G t :=
    feedbackSampleThrough_splice_eq A G (t + 1) L
      (hUUS L hLcons.1).nonempty (Nat.lt_succ_self t)
  have hvalid' := hG L hLcons.1 A' hA' t (by simpa [hsample])
  apply hzL
  simpa [feedbackOutput, hround] using hvalid'.1

/-! ## Core selection and Lemma 7.2

Negating Definition 11 first produces a strategy whose reachable effective
intersections never collapse.  That strategy need not itself output from the
intersection.  The paper's phrase “there exists a string ... the generator
can generate” therefore requires a small but real strategy transformation.
The transformation below runs the safe strategy on a shadow history which
retains all inputs, queries, and answers but replaces earlier outputs by the
safe strategy's own outputs.  This preserves adaptivity to earlier generated
strings and closes the implicit step in the printed proof.
-/

def feedbackSkeleton (q : FeedbackRound α) : α × α × Bool :=
  (q.input, q.query, q.answer)

def feedbackHistorySkeleton (h : List (FeedbackRound α)) :
    List (α × α × Bool) :=
  h.map feedbackSkeleton

def feedbackShadowStep
    (G : FeedbackGeneratorStrategy α)
    (shadow : List (FeedbackRound α)) (q : FeedbackRound α) :
    List (FeedbackRound α) :=
  shadow ++
    [⟨q.input, q.query, q.answer,
      G.output shadow q.input q.query q.answer⟩]

/-- Replace outputs chronologically by those of `G`, while retaining the
input/query/answer skeleton. -/
def feedbackShadowHistory
    (G : FeedbackGeneratorStrategy α)
    (h : List (FeedbackRound α)) : List (FeedbackRound α) :=
  h.foldl (feedbackShadowStep G) []

theorem feedbackShadowHistory_append
    (G : FeedbackGeneratorStrategy α)
    (h : List (FeedbackRound α)) (q : FeedbackRound α) :
    feedbackShadowHistory G (h ++ [q]) =
      feedbackShadowStep G (feedbackShadowHistory G h) q := by
  simp [feedbackShadowHistory, feedbackShadowStep]

theorem feedbackHistorySkeleton_shadow
    (G : FeedbackGeneratorStrategy α)
    (h : List (FeedbackRound α)) :
    feedbackHistorySkeleton (feedbackShadowHistory G h) =
      feedbackHistorySkeleton h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h q ih =>
      rw [feedbackShadowHistory_append]
      simp only [feedbackShadowStep, feedbackHistorySkeleton,
        List.map_append, List.map_singleton]
      change List.map feedbackSkeleton (feedbackShadowHistory G h) =
        List.map feedbackSkeleton h at ih
      rw [ih]
      rfl

theorem feedbackShadowHistory_length
    (G : FeedbackGeneratorStrategy α)
    (h : List (FeedbackRound α)) :
    (feedbackShadowHistory G h).length = h.length := by
  have hs := congrArg List.length
    (feedbackHistorySkeleton_shadow G h)
  simpa [feedbackHistorySkeleton] using hs

theorem feedbackHistoryObserved_eq_of_skeleton_eq
    {h₁ h₂ : List (FeedbackRound α)}
    (hs : feedbackHistorySkeleton h₁ = feedbackHistorySkeleton h₂) :
    feedbackHistoryObserved h₁ = feedbackHistoryObserved h₂ := by
  ext x
  change (∃ q ∈ h₁, q.input = x) ↔ ∃ q ∈ h₂, q.input = x
  have hmem :
      ∀ q : FeedbackRound α, q ∈ h₁ →
        feedbackSkeleton q ∈ feedbackHistorySkeleton h₂ := by
    intro q hq
    rw [← hs]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  have hmem' :
      ∀ q : FeedbackRound α, q ∈ h₂ →
        feedbackSkeleton q ∈ feedbackHistorySkeleton h₁ := by
    intro q hq
    rw [hs]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  constructor
  · rintro ⟨q, hq, hqx⟩
    obtain ⟨q', hq', hskel⟩ := List.mem_map.mp (hmem q hq)
    refine ⟨q', hq', ?_⟩
    have hinput : q'.input = q.input := by
      simpa [feedbackSkeleton] using congrArg Prod.fst hskel
    exact hinput.trans hqx
  · rintro ⟨q, hq, hqx⟩
    obtain ⟨q', hq', hskel⟩ := List.mem_map.mp (hmem' q hq)
    refine ⟨q', hq', ?_⟩
    have hinput : q'.input = q.input := by
      simpa [feedbackSkeleton] using congrArg Prod.fst hskel
    exact hinput.trans hqx

theorem feedbackHistoryConsistentLanguages_eq_of_skeleton_eq
    (C : Generic.LanguageClass α)
    {h₁ h₂ : List (FeedbackRound α)}
    (hs : feedbackHistorySkeleton h₁ = feedbackHistorySkeleton h₂) :
    feedbackHistoryConsistentLanguages C h₁ =
      feedbackHistoryConsistentLanguages C h₂ := by
  have hobs := feedbackHistoryObserved_eq_of_skeleton_eq hs
  ext L
  simp only [feedbackHistoryConsistentLanguages, Set.mem_setOf_eq]
  rw [hobs]
  constructor
  · rintro ⟨hLC, hsubset, hans⟩
    refine ⟨hLC, hsubset, ?_⟩
    intro q hq
    have hqskel : feedbackSkeleton q ∈ feedbackHistorySkeleton h₂ :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    rw [← hs] at hqskel
    obtain ⟨q', hq', heq⟩ := List.mem_map.mp hqskel
    have ha : q'.answer = q.answer := by
      simpa [feedbackSkeleton] using
        congrArg (fun p : α × α × Bool => p.2.2) heq
    have hy : q'.query = q.query := by
      simpa [feedbackSkeleton] using
        congrArg (fun p : α × α × Bool => p.2.1) heq
    rw [← ha, ← hy]
    exact hans q' hq'
  · rintro ⟨hLC, hsubset, hans⟩
    refine ⟨hLC, hsubset, ?_⟩
    intro q hq
    have hqskel : feedbackSkeleton q ∈ feedbackHistorySkeleton h₁ :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hs] at hqskel
    obtain ⟨q', hq', heq⟩ := List.mem_map.mp hqskel
    have ha : q'.answer = q.answer := by
      simpa [feedbackSkeleton] using
        congrArg (fun p : α × α × Bool => p.2.2) heq
    have hy : q'.query = q.query := by
      simpa [feedbackSkeleton] using
        congrArg (fun p : α × α × Bool => p.2.1) heq
    rw [← ha, ← hy]
    exact hans q' hq'

theorem feedbackHistoryEffectiveIntersection_eq_of_skeleton_eq
    (C : Generic.LanguageClass α)
    {h₁ h₂ : List (FeedbackRound α)}
    (hs : feedbackHistorySkeleton h₁ = feedbackHistorySkeleton h₂) :
    feedbackHistoryEffectiveIntersection C h₁ =
      feedbackHistoryEffectiveIntersection C h₂ := by
  unfold feedbackHistoryEffectiveIntersection
  rw [feedbackHistoryObserved_eq_of_skeleton_eq hs,
    feedbackHistoryConsistentLanguages_eq_of_skeleton_eq C hs]

theorem feedbackHistoryEffectiveIntersection_shadow
    (C : Generic.LanguageClass α)
    (G : FeedbackGeneratorStrategy α)
    (h : List (FeedbackRound α)) :
    feedbackHistoryEffectiveIntersection C
        (feedbackShadowHistory G h) =
      feedbackHistoryEffectiveIntersection C h :=
  feedbackHistoryEffectiveIntersection_eq_of_skeleton_eq C
    (feedbackHistorySkeleton_shadow G h)

/-- The corrected strategy implicit in Lemma 7.2.  It follows `G`'s query
policy on the shadow history and chooses its output from the current effective
intersection whenever that set is nonempty. -/
noncomputable def coreSelectingFeedbackStrategy
    (C : Generic.LanguageClass α)
    (G : FeedbackGeneratorStrategy α) :
    FeedbackGeneratorStrategy α := by
  classical
  exact
    { query := fun h x => G.query (feedbackShadowHistory G h) x
      output := fun h x y a =>
        let E := feedbackHistoryEffectiveIntersection C
          (feedbackCurrentHistory h x y a)
        if hE : E.Nonempty then Classical.choose hE
        else G.output (feedbackShadowHistory G h) x y a }

theorem coreSelectingFeedbackStrategy_output_mem
    (C : Generic.LanguageClass α)
    (G : FeedbackGeneratorStrategy α)
    (h : List (FeedbackRound α)) (x y : α) (a : Bool)
    (hE : (feedbackHistoryEffectiveIntersection C
      (feedbackCurrentHistory h x y a)).Nonempty) :
    (coreSelectingFeedbackStrategy C G).output h x y a ∈
      feedbackHistoryEffectiveIntersection C
        (feedbackCurrentHistory h x y a) := by
  classical
  simp only [coreSelectingFeedbackStrategy, hE, dif_pos]
  exact Classical.choose_spec hE

/-- Replay the input and answer streams from another fixed interaction.
Against `G`, this produces the shadow transcript of that interaction. -/
def replayFeedbackAdversary
    (A : FeedbackAdversaryStrategy α)
    (H : FeedbackGeneratorStrategy α) :
    FeedbackAdversaryStrategy α where
  input h := feedbackInput A H h.length
  answer h _x _y := feedbackAnswer A H h.length

theorem feedbackHistory_replay_eq_shadow
    (C : Generic.LanguageClass α)
    (G : FeedbackGeneratorStrategy α)
    (A : FeedbackAdversaryStrategy α) (n : ℕ) :
    feedbackHistory
        (replayFeedbackAdversary A (coreSelectingFeedbackStrategy C G)) G n =
      feedbackShadowHistory G
        (feedbackHistory A (coreSelectingFeedbackStrategy C G) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [feedbackHistory_succ, feedbackHistory_succ,
        feedbackShadowHistory_append, ih]
      simp [feedbackNextRound, feedbackShadowStep,
        replayFeedbackAdversary, coreSelectingFeedbackStrategy,
        feedbackInput, feedbackAnswer, feedbackRound,
        feedbackHistory_length, feedbackShadowHistory_length]

theorem replay_feedbackInput_eq
    (C : Generic.LanguageClass α)
    (G : FeedbackGeneratorStrategy α)
    (A : FeedbackAdversaryStrategy α) (t : ℕ) :
    feedbackInput
        (replayFeedbackAdversary A (coreSelectingFeedbackStrategy C G)) G t =
      feedbackInput A (coreSelectingFeedbackStrategy C G) t := by
  simp [feedbackInput, feedbackRound, feedbackNextRound,
    replayFeedbackAdversary, feedbackHistory_length]

theorem replay_feedbackQuery_eq
    (C : Generic.LanguageClass α)
    (G : FeedbackGeneratorStrategy α)
    (A : FeedbackAdversaryStrategy α) (t : ℕ) :
    feedbackQuery
        (replayFeedbackAdversary A (coreSelectingFeedbackStrategy C G)) G t =
      feedbackQuery A (coreSelectingFeedbackStrategy C G) t := by
  unfold feedbackQuery feedbackRound
  rw [feedbackHistory_replay_eq_shadow]
  simp [feedbackNextRound, replayFeedbackAdversary,
    coreSelectingFeedbackStrategy, feedbackShadowHistory_length,
    feedbackHistory_length, feedbackInput, feedbackRound]

theorem replay_feedbackAnswer_eq
    (C : Generic.LanguageClass α)
    (G : FeedbackGeneratorStrategy α)
    (A : FeedbackAdversaryStrategy α) (t : ℕ) :
    feedbackAnswer
        (replayFeedbackAdversary A (coreSelectingFeedbackStrategy C G)) G t =
      feedbackAnswer A (coreSelectingFeedbackStrategy C G) t := by
  simp [feedbackAnswer, feedbackRound, feedbackNextRound,
    replayFeedbackAdversary, feedbackHistory_length]

theorem replay_feedbackSampleThrough_eq
    (C : Generic.LanguageClass α)
    (G : FeedbackGeneratorStrategy α)
    (A : FeedbackAdversaryStrategy α) (t : ℕ) :
    feedbackSampleThrough
        (replayFeedbackAdversary A (coreSelectingFeedbackStrategy C G)) G t =
      feedbackSampleThrough A (coreSelectingFeedbackStrategy C G) t := by
  classical
  apply Finset.ext
  intro x
  simp only [feedbackSampleThrough, Generic.mem_sample_iff]
  constructor <;> rintro ⟨s, hs, rfl⟩
  · exact ⟨s, hs, (replay_feedbackInput_eq C G A s).symm⟩
  · exact ⟨s, hs, replay_feedbackInput_eq C G A s⟩

theorem replay_feedbackEffectiveIntersection_eq
    (C : Generic.LanguageClass α)
    (G : FeedbackGeneratorStrategy α)
    (A : FeedbackAdversaryStrategy α) (t : ℕ) :
    feedbackEffectiveIntersection C
        (replayFeedbackAdversary A (coreSelectingFeedbackStrategy C G)) G t =
      feedbackEffectiveIntersection C A
        (coreSelectingFeedbackStrategy C G) t := by
  rw [← feedbackHistoryEffectiveIntersection_eq C _ G t,
    ← feedbackHistoryEffectiveIntersection_eq C A
      (coreSelectingFeedbackStrategy C G) t,
    feedbackHistory_replay_eq_shadow,
    feedbackHistoryEffectiveIntersection_shadow]

theorem replay_feedbackAdversary_consistent
    (C : Generic.LanguageClass α)
    (G : FeedbackGeneratorStrategy α)
    (A : FeedbackAdversaryStrategy α) {K : Set α}
    (hA : FeedbackAdversaryConsistent A
      (coreSelectingFeedbackStrategy C G) K) :
    FeedbackAdversaryConsistent
      (replayFeedbackAdversary A (coreSelectingFeedbackStrategy C G))
      G K := by
  constructor
  · have hinputs :
        feedbackInput
            (replayFeedbackAdversary A
              (coreSelectingFeedbackStrategy C G)) G =
          feedbackInput A (coreSelectingFeedbackStrategy C G) := by
      funext t
      exact replay_feedbackInput_eq C G A t
    simpa [hinputs] using hA.1
  · intro t
    rw [replay_feedbackAnswer_eq C G A,
      replay_feedbackQuery_eq C G A]
    exact hA.2 t

/-- Lemma 7.2 (`lem:gf-ub`). -/
theorem finite_gf_dimension_uniformly_generatable
    {C : Generic.LanguageClass α}
    (hGF : HasFiniteGFDimension C) :
    UniformlyGeneratableWithFeedback C := by
  classical
  obtain ⟨d, hd⟩ := hGF
  unfold GFDimensionAtLeast at hd
  push_neg at hd
  obtain ⟨G, hG⟩ := hd
  let H := coreSelectingFeedbackStrategy C G
  refine ⟨H, d, ?_⟩
  intro K hKC A hAK t hcard
  let A' := replayFeedbackAdversary A H
  have hA' : FeedbackAdversaryConsistent A' G K := by
    exact replay_feedbackAdversary_consistent C G A hAK
  have hround : d ≤ t + 1 :=
    hcard.trans (feedbackSampleThrough_card_le A H t)
  have hE : (feedbackEffectiveIntersection C A H t).Nonempty := by
    by_contra hempty
    have hempty' : feedbackEffectiveIntersection C A' G t = ∅ := by
      rw [replay_feedbackEffectiveIntersection_eq C G A]
      exact Set.not_nonempty_iff_eq_empty.mp hempty
    have hcard' :
        d ≤ (feedbackSampleThrough A' G t).card := by
      rw [replay_feedbackSampleThrough_eq C G A]
      exact hcard
    have hnonempty := hG K hKC A' hA' t hround hcard'
    rw [hempty'] at hnonempty
    rcases hnonempty with ⟨x, hx⟩
    exact hx
  have hEhist :
      (feedbackHistoryEffectiveIntersection C
        (feedbackCurrentHistory (feedbackHistory A H t)
          (feedbackInput A H t) (feedbackQuery A H t)
          (feedbackAnswer A H t))).Nonempty := by
    rw [feedbackCurrentHistory_eq_up_to_output A H t]
    exact hE
  have hout := coreSelectingFeedbackStrategy_output_mem C G
    (feedbackHistory A H t) (feedbackInput A H t)
    (feedbackQuery A H t) (feedbackAnswer A H t) hEhist
  rw [feedbackCurrentHistory_eq_up_to_output A H t] at hout
  have hKcons :
      K ∈ feedbackConsistentLanguagesThrough C A H t :=
    target_mem_feedbackConsistentLanguagesThrough hKC hAK t
  exact ⟨hout.1 K hKcons, hout.2⟩

/-- Overview Theorem 5: finite GF dimension exactly characterizes uniform
generation with feedback, under the paper's standing assumptions that the
universe is countable and every language is infinite. -/
theorem theorem5_uniform_feedback_characterization
    [Countable α]
    {C : Generic.LanguageClass α} (hUUS : UUS C) :
    UniformlyGeneratableWithFeedback C ↔ HasFiniteGFDimension C := by
  constructor
  · intro hUniform
    apply (finiteGFDimension_iff_not_infinite C).mpr
    exact fun hInfinite =>
      infinite_gf_dimension_not_uniformly_generatable hUUS hInfinite hUniform
  · exact finite_gf_dimension_uniformly_generatable

end GenLimit.CharikarPabbaraju
