import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Exhaustive
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Feedback

/-!
# Charikar--Pabbaraju: the co-singleton/co-doubleton feedback example

This file formalizes the set-theoretic and generation claims in the final
example of Section 7 of Charikar--Pabbaraju, *Exploring Facets of Language
Generation in the Limit*, arXiv:2411.15364v2.

The paper takes the class consisting of every integer co-singleton and every
integer co-doubleton.  We prove that this class is countable, has infinite
closure dimension, is therefore not uniformly generatable without feedback,
and is nevertheless non-uniformly generatable by the paper's direct integer
sweep which skips examples already seen.

We also prove the paper's alternating adversary construction.  It makes each
input fresh, absorbs the preceding query into the next input when necessary,
answers every query except the final query affirmatively, and answers the
final query according to whether it was already observed.  The resulting
finite prefix has empty effective intersection; the generic finite-prefix
splice then completes a truthful exact presentation of a consistent target.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-! ## The paper's language class -/

/-- All co-singletons and co-doubletons of `ℤ`; the indices of a
co-doubleton are put in increasing order exactly as in the paper. -/
def coOneTwoIntegerClass : Generic.LanguageClass ℤ :=
  {K | (∃ i : ℤ, K = Set.univ \ {i}) ∨
    ∃ i j : ℤ, i < j ∧ K = Set.univ \ {i, j}}

theorem coSingleton_mem_coOneTwoIntegerClass (i : ℤ) :
    (Set.univ \ {i} : Set ℤ) ∈ coOneTwoIntegerClass :=
  Or.inl ⟨i, rfl⟩

theorem coDoubleton_mem_coOneTwoIntegerClass
    {i j : ℤ} (hij : i ≠ j) :
    (Set.univ \ {i, j} : Set ℤ) ∈ coOneTwoIntegerClass := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Or.inr ⟨i, j, hij, rfl⟩
  · refine Or.inr ⟨j, i, hji, ?_⟩
    congr 1
    ext x
    simp [or_comm]

theorem coOneTwoIntegerClass_countable :
    coOneTwoIntegerClass.Countable := by
  let code : Sum ℤ (ℤ × ℤ) → Set ℤ
    | .inl i => Set.univ \ {i}
    | .inr p => Set.univ \ {p.1, p.2}
  apply (Set.countable_range code).mono
  intro K hK
  rcases hK with ⟨i, rfl⟩ | ⟨i, j, _hij, rfl⟩
  · exact ⟨Sum.inl i, rfl⟩
  · exact ⟨Sum.inr (i, j), rfl⟩

theorem coOneTwoIntegerClass_uus : UUS coOneTwoIntegerClass := by
  intro K hK
  rcases hK with ⟨i, rfl⟩ | ⟨i, j, _hij, rfl⟩
  · exact Set.infinite_univ.diff (Set.finite_singleton i)
  · exact Set.infinite_univ.diff
      ((Set.finite_singleton j).insert i)

/-! ## The direct non-uniform generator from the example -/

private theorem exists_fresh_sweep_index {t : ℕ} (xs : Fin t → ℤ) :
    ∃ n : ℕ, t ≤ n ∧
      integerSweep n ∉ Generic.sequenceSample xs := by
  let tail : Set ℤ := Set.range (fun k : ℕ => integerSweep (t + k))
  have htail : tail.Infinite := by
    apply Set.infinite_range_of_injective
    intro m n h
    exact Nat.add_left_cancel (integerSweep_bijective.injective h)
  obtain ⟨z, hzTail, hzFresh⟩ :=
    (htail.diff (Generic.sequenceSample xs).finite_toSet).nonempty
  obtain ⟨k, rfl⟩ := hzTail
  exact ⟨t + k, Nat.le_add_right t k, hzFresh⟩

/-- The least unseen point in the remaining integer sweep. -/
noncomputable def firstFreshSweepIndex {t : ℕ} (xs : Fin t → ℤ) : ℕ :=
  Nat.find (exists_fresh_sweep_index xs)

/-- The direct generator described at the end of the feedback example: scan
`0,-1,1,-2,2,...`, skip past time, and skip all inputs already observed. -/
noncomputable def freshIntegerSweepGenerator : Generic.Generator ℤ :=
  fun _t xs => integerSweep (firstFreshSweepIndex xs)

theorem freshIntegerSweepGenerator_spec {t : ℕ} (xs : Fin t → ℤ) :
    t ≤ firstFreshSweepIndex xs ∧
      freshIntegerSweepGenerator t xs =
        integerSweep (firstFreshSweepIndex xs) ∧
      freshIntegerSweepGenerator t xs ∉ Generic.sequenceSample xs := by
  have h := Nat.find_spec (exists_fresh_sweep_index xs)
  exact ⟨h.1, rfl, h.2⟩

private theorem freshIntegerSweepGenerator_avoids_finset
    (B : Finset ℤ) (d : ℕ)
    (hB : ∀ z ∈ B, Equiv.intEquivNat z < d)
    (stream : Generic.Stream ℤ) {s : ℕ} (hds : d ≤ s) :
    Generic.CorrectAt freshIntegerSweepGenerator
      (Set.univ \ (B : Set ℤ)) stream s := by
  obtain ⟨hsn, hout, hfresh⟩ :=
    freshIntegerSweepGenerator_spec (fun i : Fin s => stream i)
  constructor
  · constructor
    · trivial
    · intro houtB
      have hzIndex : Equiv.intEquivNat
          (freshIntegerSweepGenerator s (fun i : Fin s => stream i)) < d :=
        hB _ houtB
      rw [hout] at hzIndex
      simp only [integerSweep, Equiv.apply_symm_apply] at hzIndex
      exact (Nat.not_lt_of_ge (hds.trans hsn)) hzIndex
  · simpa [Generic.output, Generic.sequenceSample_prefix] using hfresh

/-- The final example's direct positive claim: although uniform generation
fails, the class can be non-uniformly generated without feedback. -/
theorem coOneTwoIntegerClass_nonuniformlyGeneratable :
    NonuniformlyGeneratable coOneTwoIntegerClass := by
  classical
  refine ⟨freshIntegerSweepGenerator, ?_⟩
  intro K hK
  rcases hK with ⟨i, rfl⟩ | ⟨i, j, _hij, rfl⟩
  · let d := Equiv.intEquivNat i + 1
    refine ⟨d, ?_⟩
    intro stream _hstream t hcard s hts
    have hdt : d ≤ t := by
      rw [← hcard]
      exact Generic.sample_card_le stream t
    have hds : d ≤ s := hdt.trans hts
    simpa using freshIntegerSweepGenerator_avoids_finset
      ({i} : Finset ℤ) d (by simp [d]) stream hds
  · let d := max (Equiv.intEquivNat i) (Equiv.intEquivNat j) + 1
    refine ⟨d, ?_⟩
    intro stream _hstream t hcard s hts
    have hdt : d ≤ t := by
      rw [← hcard]
      exact Generic.sample_card_le stream t
    have hds : d ≤ s := hdt.trans hts
    have hcorrect := freshIntegerSweepGenerator_avoids_finset
      ({i, j} : Finset ℤ) d (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> dsimp only [d] <;> omega)
      stream hds
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hcorrect

/-! ## Infinite ordinary closure dimension -/

theorem commonCore_coOneTwoIntegerClass_eq (S : Finset ℤ) :
    commonCore coOneTwoIntegerClass S = (S : Set ℤ) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxS
    let L : Set ℤ := Set.univ \ {x}
    have hLClass : L ∈ coOneTwoIntegerClass :=
      coSingleton_mem_coOneTwoIntegerClass x
    have hSL : (S : Set ℤ) ⊆ L := by
      intro y hy
      simp only [L, Set.mem_diff, Set.mem_univ, true_and,
        Set.mem_singleton_iff]
      intro hyx
      exact hxS (hyx ▸ hy)
    have hxL : x ∈ L := hx L ⟨hLClass, hSL⟩
    simp [L] at hxL
  · exact sample_subset_commonCore

theorem versionSpace_coOneTwoIntegerClass_nonempty (S : Finset ℤ) :
    (versionSpace coOneTwoIntegerClass S).Nonempty := by
  obtain ⟨i, hiS⟩ := S.exists_notMem
  refine ⟨Set.univ \ {i}, coSingleton_mem_coOneTwoIntegerClass i, ?_⟩
  intro z hz
  simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_singleton_iff]
  intro hzi
  exact hiS (hzi ▸ hz)

private def integerSweepPrefix (d : ℕ) : Finset ℤ :=
  (Finset.range d).image integerSweep

private theorem integerSweepPrefix_card (d : ℕ) :
    (integerSweepPrefix d).card = d := by
  rw [integerSweepPrefix, Finset.card_image_of_injective _
    integerSweep_bijective.injective, Finset.card_range]

theorem coOneTwoIntegerClass_infiniteClosureDimension :
    HasInfiniteClosureDimension coOneTwoIntegerClass := by
  intro d
  refine ⟨integerSweepPrefix d, le_of_eq (integerSweepPrefix_card d).symm,
    ?_, ?_⟩
  · exact versionSpace_coOneTwoIntegerClass_nonempty _
  · rw [commonCore_coOneTwoIntegerClass_eq]
    exact Finset.finite_toSet _

/-- The ordinary (no-feedback) negative claim in the final example, obtained
from its infinite closure dimension. -/
theorem coOneTwoIntegerClass_not_uniformlyGeneratable :
    ¬ UniformlyGeneratable coOneTwoIntegerClass :=
  GenLimit.LiRamanTewari.closure_dimension_necessity coOneTwoIntegerClass_uus
    coOneTwoIntegerClass_infiniteClosureDimension

/-! ## The two feedback-consistency calculations -/

/-- Languages consistent with a finite sample and finite sets of positive
and negative membership-query answers. -/
def feedbackVersionSpace
    (C : Generic.LanguageClass α) (S yes no : Finset α) :
    Set (Generic.Language α) :=
  {L | L ∈ C ∧ (S : Set α) ⊆ L ∧ (yes : Set α) ⊆ L ∧
    ∀ x ∈ no, x ∉ L}

/-- The effective common intersection of all languages consistent with a
finite feedback history (before removing the observed sample). -/
def feedbackCommonCore
    (C : Generic.LanguageClass α) (S yes no : Finset α) : Set α :=
  {x | ∀ L, L ∈ feedbackVersionSpace C S yes no → x ∈ L}

theorem sample_subset_feedbackCommonCore
    (C : Generic.LanguageClass α) (S yes no : Finset α) :
    (S : Set α) ⊆ feedbackCommonCore C S yes no := by
  intro x hx L hL
  exact hL.2.1 hx

/-- First case of the paper's feedback adversary: if every affirmative query
was already observed, the consistent-language intersection is the sample. -/
theorem feedbackCommonCore_positive_eq_sample
    (S yes : Finset ℤ) (hyes : yes ⊆ S) :
    feedbackCommonCore coOneTwoIntegerClass S yes ∅ = (S : Set ℤ) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxS
    let L : Set ℤ := Set.univ \ {x}
    have hSL : (S : Set ℤ) ⊆ L := by
      intro z hz
      simp only [L, Set.mem_diff, Set.mem_univ, true_and,
        Set.mem_singleton_iff]
      intro hzx
      exact hxS (hzx ▸ hz)
    have hyesL : (yes : Set ℤ) ⊆ L := by
      intro z hz
      exact hSL (hyes hz)
    have hxL := hx L ⟨coSingleton_mem_coOneTwoIntegerClass x,
      hSL, hyesL, by simp⟩
    simp [L] at hxL
  · exact sample_subset_feedbackCommonCore _ _ _ _

/-- Second case of the paper's feedback adversary: after a fresh query `y`
is answered negatively, the consistent-language intersection is still
exactly the sample. -/
theorem feedbackCommonCore_one_negative_eq_sample
    (S yes : Finset ℤ) (y : ℤ) (hyes : yes ⊆ S) (hyS : y ∉ S) :
    feedbackCommonCore coOneTwoIntegerClass S yes {y} = (S : Set ℤ) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxS
    by_cases hxy : x = y
    · subst x
      let L : Set ℤ := Set.univ \ {y}
      have hSL : (S : Set ℤ) ⊆ L := by
        intro z hz
        simp only [L, Set.mem_diff, Set.mem_univ, true_and,
          Set.mem_singleton_iff]
        intro hzy
        exact hyS (hzy ▸ hz)
      have hyesL : (yes : Set ℤ) ⊆ L := by
        intro z hz
        exact hSL (hyes hz)
      have hyL := hx L ⟨coSingleton_mem_coOneTwoIntegerClass y,
        hSL, hyesL, by simp [L]⟩
      simp [L] at hyL
    · let L : Set ℤ := Set.univ \ {x, y}
      have hSL : (S : Set ℤ) ⊆ L := by
        intro z hz
        simp only [L, Set.mem_diff, Set.mem_univ, true_and,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        intro hzxy
        rcases hzxy with hzx | hzy
        · exact hxS (hzx ▸ hz)
        · exact hyS (hzy ▸ hz)
      have hyesL : (yes : Set ℤ) ⊆ L := by
        intro z hz
        exact hSL (hyes hz)
      have hxL := hx L ⟨coDoubleton_mem_coOneTwoIntegerClass hxy,
        hSL, hyesL, by simp [L]⟩
      simp [L] at hxL
  · exact sample_subset_feedbackCommonCore _ _ _ _

theorem feedbackEffectiveIntersection_positive_empty
    (S yes : Finset ℤ) (hyes : yes ⊆ S) :
    feedbackCommonCore coOneTwoIntegerClass S yes ∅ \ (S : Set ℤ) = ∅ := by
  rw [feedbackCommonCore_positive_eq_sample S yes hyes]
  exact Set.diff_self

theorem feedbackEffectiveIntersection_one_negative_empty
    (S yes : Finset ℤ) (y : ℤ) (hyes : yes ⊆ S) (hyS : y ∉ S) :
    feedbackCommonCore coOneTwoIntegerClass S yes {y} \ (S : Set ℤ) = ∅ := by
  rw [feedbackCommonCore_one_negative_eq_sample S yes y hyes hyS]
  exact Set.diff_self

/-! ## The alternating adversary in the final example -/

/-- The distinct inputs appearing in a finite feedback history. -/
def feedbackHistoryInputFinset
    (h : List (FeedbackRound ℤ)) : Finset ℤ :=
  (h.map FeedbackRound.input).toFinset

theorem mem_feedbackHistoryInputFinset_iff
    {h : List (FeedbackRound ℤ)} {x : ℤ} :
    x ∈ feedbackHistoryInputFinset h ↔
      x ∈ feedbackHistoryObserved h := by
  simp [feedbackHistoryInputFinset, feedbackHistoryObserved]

noncomputable def freshFeedbackHistoryInput
    (h : List (FeedbackRound ℤ)) : ℤ :=
  Classical.choose (feedbackHistoryInputFinset h).exists_notMem

theorem freshFeedbackHistoryInput_not_mem
    (h : List (FeedbackRound ℤ)) :
    freshFeedbackHistoryInput h ∉ feedbackHistoryInputFinset h :=
  Classical.choose_spec (feedbackHistoryInputFinset h).exists_notMem

/-- The finite-prefix policy in the paper's final example.  A query from the
previous round is made into the next positive input if it has not already
appeared; otherwise a genuinely fresh input is used.  All non-final queries
are answered `true`, and the final query is answered according to membership
in the current sample. -/
noncomputable def coOneTwoPrefixAdversary (rounds : ℕ) :
    FeedbackAdversaryStrategy ℤ where
  input h :=
    match h.getLast? with
    | none => freshFeedbackHistoryInput h
    | some q =>
        if q.query ∈ feedbackHistoryInputFinset h then
          freshFeedbackHistoryInput h
        else q.query
  answer h x y :=
    if h.length + 1 < rounds then true
    else decide (y ∈ insert x (feedbackHistoryInputFinset h))

theorem coOneTwoPrefixAdversary_input_fresh
    (rounds : ℕ) (h : List (FeedbackRound ℤ)) :
    (coOneTwoPrefixAdversary rounds).input h ∉
      feedbackHistoryInputFinset h := by
  classical
  simp only [coOneTwoPrefixAdversary]
  split
  · exact freshFeedbackHistoryInput_not_mem h
  · split_ifs with hq
    · exact freshFeedbackHistoryInput_not_mem h
    · exact hq

theorem feedbackHistoryInputFinset_eq_sample
    (A : FeedbackAdversaryStrategy ℤ)
    (G : FeedbackGeneratorStrategy ℤ) (n : ℕ) :
    feedbackHistoryInputFinset (feedbackHistory A G n) =
      Generic.sample (feedbackInput A G) n := by
  classical
  ext x
  rw [mem_feedbackHistoryInputFinset_iff,
    feedbackHistoryObserved_eq_sample]
  rfl

private theorem sample_succ_eq_insert
    (stream : Generic.Stream ℤ) (t : ℕ) :
    Generic.sample stream (t + 1) =
      insert (stream t) (Generic.sample stream t) := by
  classical
  ext x
  simp only [Generic.mem_sample_iff, Finset.mem_insert]
  constructor
  · rintro ⟨s, hs, hxs⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact Or.inr ⟨s, hs, hxs⟩
    · exact Or.inl hxs.symm
  · rintro (rfl | ⟨s, hs, hxs⟩)
    · exact ⟨t, Nat.lt_succ_self t, rfl⟩
    · exact ⟨s, Nat.lt.step hs, hxs⟩

theorem coOneTwoPrefixAdversary_input_not_mem_sample
    (rounds : ℕ) (G : FeedbackGeneratorStrategy ℤ) (t : ℕ) :
    feedbackInput (coOneTwoPrefixAdversary rounds) G t ∉
      Generic.sample
        (feedbackInput (coOneTwoPrefixAdversary rounds) G) t := by
  rw [← feedbackHistoryInputFinset_eq_sample]
  exact coOneTwoPrefixAdversary_input_fresh rounds _

theorem coOneTwoPrefixAdversary_sample_card
    (rounds : ℕ) (G : FeedbackGeneratorStrategy ℤ) (n : ℕ) :
    (Generic.sample
      (feedbackInput (coOneTwoPrefixAdversary rounds) G) n).card = n := by
  induction n with
  | zero => simp [Generic.sample]
  | succ n ih =>
      rw [sample_succ_eq_insert,
        Finset.card_insert_of_notMem
          (coOneTwoPrefixAdversary_input_not_mem_sample rounds G n),
        ih]

theorem coOneTwoPrefixAdversary_sampleThrough_card
    (rounds : ℕ) (G : FeedbackGeneratorStrategy ℤ) (t : ℕ) :
    (feedbackSampleThrough
      (coOneTwoPrefixAdversary rounds) G t).card = t + 1 := by
  exact coOneTwoPrefixAdversary_sample_card rounds G (t + 1)

theorem coOneTwoPrefixAdversary_previous_query_mem_sample
    (rounds : ℕ) (G : FeedbackGeneratorStrategy ℤ) (s : ℕ) :
    feedbackQuery (coOneTwoPrefixAdversary rounds) G s ∈
      Generic.sample
        (feedbackInput (coOneTwoPrefixAdversary rounds) G) (s + 2) := by
  classical
  let A := coOneTwoPrefixAdversary rounds
  by_cases hmem :
      feedbackQuery A G s ∈ Generic.sample (feedbackInput A G) (s + 1)
  · exact Generic.sample_mono (by omega) hmem
  · have hlast :
        (feedbackHistory A G (s + 1)).getLast? =
          some (feedbackRound A G s) := by
      rw [feedbackHistory_succ]
      simp [feedbackRound]
    have hfin :
        feedbackQuery A G s ∉
          feedbackHistoryInputFinset (feedbackHistory A G (s + 1)) := by
      rw [feedbackHistoryInputFinset_eq_sample]
      exact hmem
    have hinput :
        feedbackInput A G (s + 1) = feedbackQuery A G s := by
      change (coOneTwoPrefixAdversary rounds).input
          (feedbackHistory A G (s + 1)) =
        (feedbackRound A G s).query
      simp only [coOneTwoPrefixAdversary]
      rw [show (feedbackHistory A G (s + 1)).getLast? =
        some (feedbackRound A G s) from hlast]
      change
        (if (feedbackRound A G s).query ∈
            feedbackHistoryInputFinset (feedbackHistory A G (s + 1)) then
          freshFeedbackHistoryInput (feedbackHistory A G (s + 1))
        else (feedbackRound A G s).query) =
          (feedbackRound A G s).query
      change (feedbackRound A G s).query ∉
        feedbackHistoryInputFinset (feedbackHistory A G (s + 1)) at hfin
      rw [if_neg hfin]
    rw [← hinput]
    exact Generic.value_mem_sample (by omega)

theorem coOneTwoPrefixAdversary_previous_query_mem_sampleThrough
    (rounds : ℕ) (G : FeedbackGeneratorStrategy ℤ)
    {s t : ℕ} (hst : s < t) :
    feedbackQuery (coOneTwoPrefixAdversary rounds) G s ∈
      feedbackSampleThrough (coOneTwoPrefixAdversary rounds) G t := by
  apply Generic.sample_mono (show s + 2 ≤ t + 1 by omega)
  exact coOneTwoPrefixAdversary_previous_query_mem_sample rounds G s

theorem coOneTwoPrefixAdversary_answer_true_before_final
    (rounds : ℕ) (G : FeedbackGeneratorStrategy ℤ)
    {s : ℕ} (hs : s + 1 < rounds) :
    feedbackAnswer (coOneTwoPrefixAdversary rounds) G s = true := by
  simp [feedbackAnswer, feedbackRound, feedbackNextRound,
    coOneTwoPrefixAdversary, feedbackHistory_length, hs]

theorem coOneTwoPrefixAdversary_final_answer_iff
    (rounds : ℕ) (G : FeedbackGeneratorStrategy ℤ)
    {t : ℕ} (ht : t + 1 = rounds) :
    feedbackAnswer (coOneTwoPrefixAdversary rounds) G t = true ↔
      feedbackQuery (coOneTwoPrefixAdversary rounds) G t ∈
        feedbackSampleThrough (coOneTwoPrefixAdversary rounds) G t := by
  classical
  let A := coOneTwoPrefixAdversary rounds
  have hnot : ¬ t + 1 < rounds := by omega
  change
    (if (feedbackHistory A G t).length + 1 < rounds then true
      else decide
        (feedbackQuery A G t ∈
          insert (feedbackInput A G t)
            (feedbackHistoryInputFinset (feedbackHistory A G t)))) =
      true ↔
    feedbackQuery A G t ∈ feedbackSampleThrough A G t
  rw [feedbackHistory_length, if_neg hnot, decide_eq_true_eq,
    feedbackHistoryInputFinset_eq_sample]
  unfold feedbackSampleThrough
  rw [sample_succ_eq_insert]

private theorem coOneTwo_effectiveIntersection_all_positive
    {A : FeedbackAdversaryStrategy ℤ}
    {G : FeedbackGeneratorStrategy ℤ} {t : ℕ}
    (hanswer : ∀ s, s ≤ t → feedbackAnswer A G s = true)
    (hquery : ∀ s, s ≤ t →
      feedbackQuery A G s ∈ feedbackSampleThrough A G t) :
    feedbackEffectiveIntersection coOneTwoIntegerClass A G t = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  rcases hz with ⟨hzcore, hzsample⟩
  let L : Set ℤ := Set.univ \ {z}
  have hsampleL :
      (↑(feedbackSampleThrough A G t) : Set ℤ) ⊆ L := by
    intro x hx
    simp only [L, Set.mem_diff, Set.mem_univ, true_and,
      Set.mem_singleton_iff]
    intro hxz
    exact hzsample (hxz ▸ hx)
  have hL :
      L ∈ feedbackConsistentLanguagesThrough
        coOneTwoIntegerClass A G t := by
    refine ⟨coSingleton_mem_coOneTwoIntegerClass z, hsampleL, ?_⟩
    intro s hs
    rw [hanswer s hs]
    simp only [true_iff]
    exact hsampleL (hquery s hs)
  have hzL := hzcore L hL
  simp [L] at hzL

private theorem coOneTwo_effectiveIntersection_one_final_negative
    {A : FeedbackAdversaryStrategy ℤ}
    {G : FeedbackGeneratorStrategy ℤ} {t : ℕ}
    (hanswer : ∀ s, s < t → feedbackAnswer A G s = true)
    (hquery : ∀ s, s < t →
      feedbackQuery A G s ∈ feedbackSampleThrough A G t)
    (hfinal : feedbackAnswer A G t = false)
    (hyfresh :
      feedbackQuery A G t ∉ feedbackSampleThrough A G t) :
    feedbackEffectiveIntersection coOneTwoIntegerClass A G t = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  rcases hz with ⟨hzcore, hzsample⟩
  let y := feedbackQuery A G t
  change y ∉ feedbackSampleThrough A G t at hyfresh
  by_cases hzy : z = y
  · subst z
    let L : Set ℤ := Set.univ \ {y}
    have hsampleL :
        (↑(feedbackSampleThrough A G t) : Set ℤ) ⊆ L := by
      intro x hx
      simp only [L, Set.mem_diff, Set.mem_univ, true_and,
        Set.mem_singleton_iff]
      intro hxy
      exact hyfresh (hxy ▸ hx)
    have hL :
        L ∈ feedbackConsistentLanguagesThrough
          coOneTwoIntegerClass A G t := by
      refine ⟨coSingleton_mem_coOneTwoIntegerClass y, hsampleL, ?_⟩
      intro s hs
      rcases lt_or_eq_of_le hs with hst | rfl
      · rw [hanswer s hst]
        simp only [true_iff]
        exact hsampleL (hquery s hst)
      · rw [hfinal]
        simp [L, y]
    have hyL := hzcore L hL
    simp [L] at hyL
  · let L : Set ℤ := Set.univ \ {z, y}
    have hsampleL :
        (↑(feedbackSampleThrough A G t) : Set ℤ) ⊆ L := by
      intro x hx
      simp only [L, Set.mem_diff, Set.mem_univ, true_and,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (hxz | hxy)
      · exact hzsample (hxz ▸ hx)
      · exact hyfresh (hxy ▸ hx)
    have hL :
        L ∈ feedbackConsistentLanguagesThrough
          coOneTwoIntegerClass A G t := by
      refine ⟨coDoubleton_mem_coOneTwoIntegerClass hzy, hsampleL, ?_⟩
      intro s hs
      rcases lt_or_eq_of_le hs with hst | rfl
      · rw [hanswer s hst]
        simp only [true_iff]
        exact hsampleL (hquery s hst)
      · rw [hfinal]
        simp [L, y]
    have hzL := hzcore L hL
    simp [L] at hzL

theorem coOneTwoPrefixAdversary_effectiveIntersection_empty
    (rounds : ℕ) (hrounds : 0 < rounds)
    (G : FeedbackGeneratorStrategy ℤ) :
    let t := rounds - 1
    feedbackEffectiveIntersection coOneTwoIntegerClass
      (coOneTwoPrefixAdversary rounds) G t = ∅ := by
  classical
  let A := coOneTwoPrefixAdversary rounds
  let t := rounds - 1
  have ht : t + 1 = rounds := by
    dsimp [t]
    omega
  have hfinalIff :=
    coOneTwoPrefixAdversary_final_answer_iff rounds G ht
  by_cases hy :
      feedbackQuery A G t ∈ feedbackSampleThrough A G t
  · apply coOneTwo_effectiveIntersection_all_positive
    · intro s hs
      rcases lt_or_eq_of_le hs with hst | rfl
      · apply coOneTwoPrefixAdversary_answer_true_before_final
        omega
      · exact hfinalIff.mpr hy
    · intro s hs
      rcases lt_or_eq_of_le hs with hst | rfl
      · exact
          coOneTwoPrefixAdversary_previous_query_mem_sampleThrough
            rounds G hst
      · exact hy
  · have hfinal :
        feedbackAnswer A G t = false := by
      cases h : feedbackAnswer A G t with
      | false => rfl
      | true => exact (hy (hfinalIff.mp h)).elim
    apply coOneTwo_effectiveIntersection_one_final_negative
    · intro s hst
      apply coOneTwoPrefixAdversary_answer_true_before_final
      omega
    · intro s hst
      exact coOneTwoPrefixAdversary_previous_query_mem_sampleThrough
        rounds G hst
    · exact hfinal
    · exact hy

private theorem coOneTwoPrefixAdversary_exists_consistent_target
    (rounds : ℕ) (hrounds : 0 < rounds)
    (G : FeedbackGeneratorStrategy ℤ) :
    let t := rounds - 1
    ∃ K, K ∈ feedbackConsistentLanguagesThrough
      coOneTwoIntegerClass (coOneTwoPrefixAdversary rounds) G t := by
  classical
  let A := coOneTwoPrefixAdversary rounds
  let t := rounds - 1
  have ht : t + 1 = rounds := by
    dsimp [t]
    omega
  have hfinalIff :=
    coOneTwoPrefixAdversary_final_answer_iff rounds G ht
  by_cases hy :
      feedbackQuery A G t ∈ feedbackSampleThrough A G t
  · obtain ⟨w, hw⟩ :=
      (feedbackSampleThrough A G t).exists_notMem
    let K : Set ℤ := Set.univ \ {w}
    refine ⟨K, coSingleton_mem_coOneTwoIntegerClass w, ?_, ?_⟩
    · intro x hx
      simp only [K, Set.mem_diff, Set.mem_univ, true_and,
        Set.mem_singleton_iff]
      intro hxw
      exact hw (hxw ▸ hx)
    · intro s hs
      have hquery :
          feedbackQuery A G s ∈ feedbackSampleThrough A G t := by
        rcases lt_or_eq_of_le hs with hst | rfl
        · exact
            coOneTwoPrefixAdversary_previous_query_mem_sampleThrough
              rounds G hst
        · exact hy
      have hanswer : feedbackAnswer A G s = true := by
        rcases lt_or_eq_of_le hs with hst | rfl
        · apply coOneTwoPrefixAdversary_answer_true_before_final
          omega
        · exact hfinalIff.mpr hy
      rw [hanswer]
      simp only [true_iff]
      simp only [K, Set.mem_diff, Set.mem_univ, true_and,
        Set.mem_singleton_iff]
      intro hqw
      exact hw (hqw ▸ hquery)
  · let y := feedbackQuery A G t
    have hfinal :
        feedbackAnswer A G t = false := by
      cases h : feedbackAnswer A G t with
      | false => rfl
      | true => exact (hy (hfinalIff.mp h)).elim
    let K : Set ℤ := Set.univ \ {y}
    refine ⟨K, coSingleton_mem_coOneTwoIntegerClass y, ?_, ?_⟩
    · intro x hx
      simp only [K, Set.mem_diff, Set.mem_univ, true_and,
        Set.mem_singleton_iff]
      intro hxy
      apply hy
      change y ∈ feedbackSampleThrough A G t
      exact hxy ▸ hx
    · intro s hs
      rcases lt_or_eq_of_le hs with hst | rfl
      · have hanswer :
            feedbackAnswer A G s = true := by
          apply coOneTwoPrefixAdversary_answer_true_before_final
          omega
        rw [hanswer]
        simp only [true_iff]
        have hquery :=
          coOneTwoPrefixAdversary_previous_query_mem_sampleThrough
            rounds G hst
        simp only [K, Set.mem_diff, Set.mem_univ, true_and,
          Set.mem_singleton_iff]
        intro hqy
        apply hy
        change y ∈ feedbackSampleThrough A G t
        exact hqy ▸ hquery
      · rw [hfinal]
        simp [K]
        rfl

/-- The full negative-feedback claim in the final example: the class has
infinite GF dimension.  The constructed infinite adversary is obtained by
splicing the paper's finite prefix to an exact enumeration of a consistent
co-singleton target. -/
theorem coOneTwoIntegerClass_hasInfiniteGFDimension :
    HasInfiniteGFDimension coOneTwoIntegerClass := by
  classical
  intro d G
  let rounds := max 1 d
  have hrounds : 0 < rounds := by
    dsimp [rounds]
    omega
  let t := rounds - 1
  have ht : t + 1 = rounds := by
    dsimp [t]
    omega
  let A₀ := coOneTwoPrefixAdversary rounds
  obtain ⟨K, hK⟩ :=
    coOneTwoPrefixAdversary_exists_consistent_target rounds hrounds G
  have hKnonempty : K.Nonempty :=
    (coOneTwoIntegerClass_uus K hK.1).nonempty
  let A :=
    spliceFeedbackAdversary A₀ (t + 1) K hKnonempty
  have hA : FeedbackAdversaryConsistent A G K := by
    exact spliceFeedbackAdversary_consistent A₀ G t hK hKnonempty
  have hsample :
      feedbackSampleThrough A G t =
        feedbackSampleThrough A₀ G t := by
    exact feedbackSampleThrough_splice_eq A₀ G (t + 1) K
      hKnonempty (Nat.lt_succ_self t)
  have heffective :
      feedbackEffectiveIntersection coOneTwoIntegerClass A G t =
        feedbackEffectiveIntersection coOneTwoIntegerClass A₀ G t := by
    rw [← feedbackHistoryEffectiveIntersection_eq
        coOneTwoIntegerClass A G t,
      ← feedbackHistoryEffectiveIntersection_eq
        coOneTwoIntegerClass A₀ G t]
    exact congrArg
      (feedbackHistoryEffectiveIntersection coOneTwoIntegerClass)
      (feedbackHistory_splice_eq A₀ G (t + 1) K hKnonempty le_rfl)
  refine ⟨K, hK.1, A, hA, t, ?_, ?_, ?_⟩
  · dsimp [rounds] at ht ⊢
    omega
  · rw [hsample,
      coOneTwoPrefixAdversary_sampleThrough_card rounds G t, ht]
    dsimp [rounds]
    omega
  · rw [heffective]
    exact coOneTwoPrefixAdversary_effectiveIntersection_empty
      rounds hrounds G

/-- Consequently the final example cannot be uniformly generated even with
membership feedback. -/
theorem coOneTwoIntegerClass_not_uniformlyGeneratableWithFeedback :
    ¬ UniformlyGeneratableWithFeedback coOneTwoIntegerClass :=
  infinite_gf_dimension_not_uniformly_generatable
    coOneTwoIntegerClass_uus
    coOneTwoIntegerClass_hasInfiniteGFDimension

end GenLimit.CharikarPabbaraju
