import GenLimit.LiRamanTewari.PromptedDefinitions
import Mathlib.Data.Countable.Defs

/-!
# Prompted closure dimension

This file formalizes Definition 5.5, the two proof directions sketched in
Appendix B.1, and Theorem 5.1 of Li--Raman--Tewari,
arXiv:2410.13714v5 / COLT 2025.
-/

namespace GenLimit.LiRamanTewari

/-- A finite sample and prompt witness prompted closure dimension. -/
def IsPromptedClosureWitness
    (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Prop :=
  (promptedVersionSpace H S y).Nonempty ∧
    (promptedCommonCore H S y).Finite

/-- No prompted closure witness has cardinality strictly larger than `d`. -/
def PromptedClosureDimensionAtMost
    (H : MulticlassHypothesisClass α ι) (d : ℕ) : Prop :=
  ∀ y : ι, ∀ S : Finset α, d < S.card →
    (promptedVersionSpace H S y).Nonempty →
      (promptedCommonCore H S y).Infinite

/-- The finite value `PC(H)=d`, with the source's special zero convention. -/
def HasPromptedClosureDimension
    (H : MulticlassHypothesisClass α ι) (d : ℕ) : Prop :=
  PromptedClosureDimensionAtMost H d ∧
    (d = 0 ∨
      ∃ y : ι, ∃ S : Finset α,
        S.card = d ∧ IsPromptedClosureWitness H S y)

/-- The paper statement `PC(H) < ∞`. -/
def HasFinitePromptedClosureDimension
    (H : MulticlassHypothesisClass α ι) : Prop :=
  ∃ d : ℕ, HasPromptedClosureDimension H d

/-- The paper statement `PC(H) = ∞`. -/
def HasInfinitePromptedClosureDimension
    (H : MulticlassHypothesisClass α ι) : Prop :=
  ∀ d : ℕ, ∃ y : ι, ∃ S : Finset α,
    d ≤ S.card ∧ IsPromptedClosureWitness H S y

theorem prompted_closure_witness_mono
    {H : MulticlassHypothesisClass α ι} {S T : Finset α} {y : ι}
    (hST : S ⊆ T) (hT : IsPromptedClosureWitness H T y) :
    IsPromptedClosureWitness H S y := by
  rcases hT with ⟨⟨h, hhH, hhT⟩, hcore⟩
  constructor
  · exact ⟨h, hhH, fun x hx ↦ hhT x (hST hx)⟩
  · apply hcore.subset
    intro x hx h' hh'
    exact hx h' ⟨hh'.1, fun z hz ↦ hh'.2 z (hST hz)⟩

theorem exists_prompted_closure_witness_card_eq
    {H : MulticlassHypothesisClass α ι}
    (hPC : HasInfinitePromptedClosureDimension H) (d : ℕ) :
    ∃ y : ι, ∃ S : Finset α,
      S.card = d ∧ IsPromptedClosureWitness H S y := by
  obtain ⟨y, T, hdT, hT⟩ := hPC d
  obtain ⟨S, hST, hSd⟩ := Finset.exists_subset_card_eq hdT
  exact ⟨y, S, hSd, prompted_closure_witness_mono hST hT⟩

/-- The finite and infinite relational encodings of prompted closure
dimension are complementary. -/
theorem finite_prompted_closure_dimension_iff_not_infinite
    {H : MulticlassHypothesisClass α ι} :
    HasFinitePromptedClosureDimension H ↔
      ¬ HasInfinitePromptedClosureDimension H := by
  classical
  constructor
  · rintro ⟨d, hd⟩ hInfinite
    obtain ⟨y, S, hcard, hS⟩ := hInfinite (d + 1)
    exact (hd.1 y S (Nat.lt_of_succ_le hcard) hS.1) hS.2
  · intro hNotInfinite
    unfold HasInfinitePromptedClosureDimension at hNotInfinite
    push_neg at hNotInfinite
    let P : ℕ → Prop := fun n ↦
      ∀ y : ι, ∀ S : Finset α, n ≤ S.card →
        ¬ IsPromptedClosureWitness H S y
    have hPExists : ∃ n, P n := by
      simpa only [P] using hNotInfinite
    let m := Nat.find hPExists
    have hm : P m := Nat.find_spec hPExists
    by_cases hm0 : m = 0
    · refine ⟨0, ?_, Or.inl rfl⟩
      intro y S _ hVS
      change ¬(promptedCommonCore H S y).Finite
      intro hfinite
      exact hm y S (by simp [hm0]) ⟨hVS, hfinite⟩
    · obtain ⟨k, hmk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hNotPk : ¬P k := by
        apply Nat.find_min hPExists
        change k < m
        rw [hmk]
        exact Nat.lt_succ_self k
      dsimp only [P] at hNotPk
      push_neg at hNotPk
      obtain ⟨y, S, hkS, hS⟩ := hNotPk
      have hSm : S.card < m := by
        by_contra hnot
        exact hm y S (Nat.le_of_not_gt hnot) hS
      have hSk : S.card = k := by
        apply Nat.le_antisymm
        · rw [hmk] at hSm
          exact Nat.lt_succ_iff.mp hSm
        · exact hkS
      refine ⟨k, ?_, Or.inr ⟨y, S, hSk, hS⟩⟩
      intro z T hkT hTVS
      change ¬(promptedCommonCore H T z).Finite
      intro hfinite
      apply hm z T
      · rw [hmk]
        exact Nat.succ_le_iff.mpr hkT
      · exact ⟨hTVS, hfinite⟩

/-- The examples in a prompted history whose revealed label equals `y`. -/
noncomputable def promptedSequenceSample
    {t : ℕ} (history : Fin t → PromptedObservation α ι) (y : ι) :
    Finset α := by
  classical
  exact (Finset.univ.filter (fun i ↦ (history i).2.1 = y)).image
    (fun i ↦ (history i).1)

/-- All examples in a prompted history, independent of their labels. -/
noncomputable def promptedObservedSample
    {t : ℕ} (history : Fin t → PromptedObservation α ι) : Finset α :=
  GenLimit.Generic.sequenceSample (fun i ↦ (history i).1)

theorem promptedSequenceSample_history
    (h : MulticlassHypothesis α ι)
    (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι)
    (t : ℕ) (y : ι) :
    promptedSequenceSample (promptedHistory h xs ys t) y =
      promptedSample h xs y t := by
  classical
  ext x
  simp only [promptedSequenceSample, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, promptedHistory, mem_promptedSample_iff,
    GenLimit.Generic.mem_sample_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, i.isLt, rfl⟩, hi⟩
  · rintro ⟨⟨n, hn, rfl⟩, hlabel⟩
    exact ⟨⟨n, hn⟩, hlabel, rfl⟩

theorem promptedObservedSample_history
    (h : MulticlassHypothesis α ι)
    (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι)
    (t : ℕ) :
    promptedObservedSample (promptedHistory h xs ys t) =
      GenLimit.Generic.sample xs t := by
  simpa [promptedObservedSample, promptedHistory] using
    GenLimit.Generic.sequenceSample_prefix xs t

private theorem prompted_core_diff_observed_infinite
    {H : MulticlassHypothesisClass α ι} {d : ℕ}
    (hPC : PromptedClosureDimensionAtMost H d)
    (S observed : Finset α) (y : ι)
    (hd : d < S.card)
    (hVS : (promptedVersionSpace H S y).Nonempty) :
    (promptedCommonCore H S y \ (↑observed : Set α)).Infinite :=
  (hPC y S hd hVS).diff observed.finite_toSet

/-- The closure generator in the sufficiency sketch of Theorem 5.1. -/
noncomputable def promptedClosureGenerator [Nonempty α]
    (H : MulticlassHypothesisClass α ι) (d : ℕ)
    (hPC : PromptedClosureDimensionAtMost H d) :
    PromptedGenerator α ι := by
  classical
  exact fun t history ↦
    if ht : 0 < t then
      let last : Fin t := ⟨t - 1, Nat.sub_lt (by omega) (by omega)⟩
      let y := (history last).2.2
      let S := promptedSequenceSample history y
      let observed := promptedObservedSample history
      if hd : d < S.card then
        if hVS : (promptedVersionSpace H S y).Nonempty then
          Classical.choose
            (prompted_core_diff_observed_infinite hPC S observed y hd hVS).nonempty
        else Classical.choice inferInstance
      else Classical.choice inferInstance
    else Classical.choice inferInstance

theorem promptedClosureGenerator_spec [Nonempty α]
    {H : MulticlassHypothesisClass α ι} {d t : ℕ}
    (hPC : PromptedClosureDimensionAtMost H d)
    (history : Fin t → PromptedObservation α ι)
    (ht : 0 < t) :
    let last : Fin t := ⟨t - 1, Nat.sub_lt (by omega) (by omega)⟩
    let y := (history last).2.2
    let S := promptedSequenceSample history y
    let observed := promptedObservedSample history
    d < S.card →
    (promptedVersionSpace H S y).Nonempty →
    promptedClosureGenerator H d hPC t history ∈
      promptedCommonCore H S y \ (↑observed : Set α) := by
  classical
  dsimp only
  intro hd hVS
  simpa only [promptedClosureGenerator, dif_pos ht, hd, hVS] using
    Classical.choose_spec
      (prompted_core_diff_observed_infinite hPC
        (promptedSequenceSample history
          (history ⟨t - 1, Nat.sub_lt (by omega) (by omega)⟩).2.2)
        (promptedObservedSample history)
        (history ⟨t - 1, Nat.sub_lt (by omega) (by omega)⟩).2.2
        hd hVS).nonempty

/-- Sufficiency direction in Theorem 5.1, with the source's quantitative
threshold `PC(H)+1`. -/
theorem prompted_closure_dimension_sufficiency
    [Nonempty α] [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι} (_hPUUS : PUUS H) {d : ℕ}
    (hPC : HasPromptedClosureDimension H d) :
    ∃ gen : PromptedGenerator α ι,
      IsPromptedUniformGeneratorAt gen H (d + 1) := by
  let gen := promptedClosureGenerator H d hPC.1
  refine ⟨gen, ?_⟩
  intro h hhH xs ys yStar t ht s hts hs hcurrent _hs
  have hmono :
      promptedSample h xs yStar t ⊆ promptedSample h xs yStar s :=
    promptedSample_mono hts
  have hcard : d < (promptedSample h xs yStar s).card := by
    have : d + 1 ≤ (promptedSample h xs yStar s).card := by
      rw [← ht]
      exact Finset.card_le_card hmono
    exact Nat.lt_of_succ_le this
  let history := promptedHistory h xs ys s
  have hlast :
      (history ⟨s - 1, Nat.sub_lt (by omega) (by omega)⟩).2.2 = yStar := by
    simpa [history, promptedHistory] using hcurrent
  have hS :
      promptedSequenceSample history
          (history ⟨s - 1, Nat.sub_lt (by omega) (by omega)⟩).2.2 =
        promptedSample h xs yStar s := by
    rw [hlast]
    exact promptedSequenceSample_history h xs ys s yStar
  have htarget :
      h ∈ promptedVersionSpace H (promptedSample h xs yStar s) yStar := by
    refine ⟨hhH, ?_⟩
    intro x hx
    exact (mem_promptedSample_iff.mp hx).2
  have hdOriginal :
      d < (promptedSequenceSample history
        (history ⟨s - 1, Nat.sub_lt (by omega) (by omega)⟩).2.2).card := by
    rw [hS]
    exact hcard
  have hVSOriginal :
      (promptedVersionSpace H
        (promptedSequenceSample history
          (history ⟨s - 1, Nat.sub_lt (by omega) (by omega)⟩).2.2)
        (history ⟨s - 1, Nat.sub_lt (by omega) (by omega)⟩).2.2).Nonempty := by
    rw [hS, hlast]
    exact ⟨h, htarget⟩
  have hspec := promptedClosureGenerator_spec hPC.1 history hs
    hdOriginal hVSOriginal
  rw [hS, hlast] at hspec
  change gen s history ∈
    promptSupport h (ys (s - 1)) \
      (↑(GenLimit.Generic.sample xs s) : Set α)
  have hcore :
      gen s history ∈
        promptedCommonCore H (promptedSample h xs yStar s) yStar := by
    simpa [gen] using hspec.1
  constructor
  · rw [hcurrent]
    exact promptedCommonCore_subset_support htarget hcore
  · have hfresh :
        gen s history ∉ promptedObservedSample history := by
      simpa [gen] using hspec.2
    rwa [promptedObservedSample_history h xs ys s] at hfresh

/-- `PC(H)<∞` implies prompted uniform generatability. -/
theorem finite_prompted_closure_dimension_implies_uniform
    [Nonempty α] [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι}
    (hPUUS : PUUS H)
    (hfinite : HasFinitePromptedClosureDimension H) :
    PromptedUniformlyGeneratable H := by
  obtain ⟨d, hd⟩ := hfinite
  obtain ⟨gen, hgen⟩ :=
    prompted_closure_dimension_sufficiency hPUUS hd
  exact ⟨gen, d + 1, hgen⟩

private theorem promptedSample_card_step
    (h : MulticlassHypothesis α ι)
    (xs : GenLimit.Generic.Stream α) (y : ι) (t : ℕ) :
    (promptedSample h xs y (t + 1)).card ≤
      (promptedSample h xs y t).card + 1 := by
  classical
  have hsub :
      promptedSample h xs y (t + 1) ⊆
        insert (xs t) (promptedSample h xs y t) := by
    intro x hx
    rw [mem_promptedSample_iff] at hx
    obtain ⟨n, hn, hnx⟩ := GenLimit.Generic.mem_sample_iff.mp hx.1
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
    · exact Finset.mem_insert_of_mem
        (mem_promptedSample_iff.mpr
          ⟨GenLimit.Generic.mem_sample_iff.mpr ⟨n, hn, hnx⟩, hx.2⟩)
    · subst x
      exact @Finset.mem_insert_self α (Classical.decEq α) (xs n)
        (promptedSample h xs y n)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

theorem exists_earlier_promptedSample_card_eq
    {h : MulticlassHypothesis α ι}
    {xs : GenLimit.Generic.Stream α} {y : ι} {t k : ℕ}
    (hk : k ≤ (promptedSample h xs y t).card) :
    ∃ r ≤ t, (promptedSample h xs y r).card = k := by
  classical
  let hex : ∃ r, k ≤ (promptedSample h xs y r).card := ⟨t, hk⟩
  let r := Nat.find hex
  have hrLower : k ≤ (promptedSample h xs y r).card := Nat.find_spec hex
  have hrt : r ≤ t := Nat.find_min' hex hk
  by_cases hr0 : r = 0
  · have hk0 : k = 0 := by
      rw [hr0] at hrLower
      simpa [promptedSample, GenLimit.Generic.sample] using hrLower
    exact ⟨0, by simp, by simp [promptedSample, GenLimit.Generic.sample, hk0]⟩
  · obtain ⟨s, hrs⟩ := Nat.exists_eq_succ_of_ne_zero hr0
    have hprevNot : ¬k ≤ (promptedSample h xs y s).card :=
      Nat.find_min hex (by
        change s < r
        rw [hrs]
        exact Nat.lt_succ_self s)
    have hprev : (promptedSample h xs y s).card < k :=
      Nat.lt_of_not_ge hprevNot
    have hupper : (promptedSample h xs y (s + 1)).card ≤ k :=
      le_trans (promptedSample_card_step h xs y s)
        (Nat.succ_le_iff.mpr hprev)
    rw [hrs] at hrLower hrt
    exact ⟨s + 1, hrt, Nat.le_antisymm hupper hrLower⟩

theorem prompted_uniform_threshold_mono
    {gen : PromptedGenerator α ι}
    {H : MulticlassHypothesisClass α ι} {d n : ℕ}
    (hdn : d ≤ n)
    (hgen : IsPromptedUniformGeneratorAt gen H d) :
    IsPromptedUniformGeneratorAt gen H n := by
  intro h hhH xs ys yStar
  exact GenLimit.Generic.eventualAtExactSize_mono
    (size := fun t ↦ (promptedSample h xs yStar t).card)
    (fun hk ↦ exists_earlier_promptedSample_card_eq hk)
    hdn (hgen h hhH xs ys yStar)

/-- Necessity direction in Theorem 5.1.  The proof follows Appendix B.1:
enumerate the finite prompted closure and choose, after seeing the proposed
output, a consistent target on which that output is either invalid or old. -/
theorem prompted_closure_dimension_necessity
    [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H)
    (hPC : HasInfinitePromptedClosureDimension H) :
    ¬ PromptedUniformlyGeneratable H := by
  classical
  rintro ⟨gen, d, hgen⟩
  have hgenSucc :
      IsPromptedUniformGeneratorAt gen H (d + 1) :=
    prompted_uniform_threshold_mono (Nat.le_succ d) hgen
  obtain ⟨y, S, hSd, hVS, hcoreFinite⟩ :=
    exists_prompted_closure_witness_card_eq hPC (d + 1)
  let C : Finset α := hcoreFinite.toFinset
  have hSC : S ⊆ C := by
    intro x hx
    change x ∈ hcoreFinite.toFinset
    rw [Set.Finite.mem_toFinset]
    exact promptedSample_subset_commonCore hx
  let historyList : List α := S.toList ++ (C \ S).toList
  have hhistoryFinset : historyList.toFinset = C := by
    simp only [historyList, List.toFinset_append, Finset.toList_toFinset]
    exact Finset.union_sdiff_of_subset hSC
  have hhistoryPos : 0 < historyList.length := by
    have : 0 < S.card := by omega
    simpa [historyList] using
      lt_of_lt_of_le this
        (show S.card ≤ S.card + (C \ S).card from Nat.le_add_right _ _)
  let xhat : α :=
    gen historyList.length (fun i ↦ (historyList.get i, y, y))
  obtain ⟨h, hhVS, hbad⟩ :
      ∃ h, h ∈ promptedVersionSpace H S y ∧
        (xhat ∈ promptedCommonCore H S y ∨ h xhat ≠ y) := by
    by_cases hx : xhat ∈ promptedCommonCore H S y
    · obtain ⟨h, hh⟩ := hVS
      exact ⟨h, hh, Or.inl hx⟩
    · change ¬∀ h, h ∈ promptedVersionSpace H S y → h xhat = y at hx
      push_neg at hx
      obtain ⟨h, hh, hxy⟩ := hx
      exact ⟨h, hh, Or.inr hxy⟩
  have hsupportInfinite : (promptSupport h y).Infinite :=
    hPUUS h hhVS.1 y
  obtain ⟨fallback, hfallback⟩ := hsupportInfinite.nonempty
  let xs : GenLimit.Generic.Stream α :=
    GenLimit.Generic.historyThenFallback historyList fallback
  let ys : GenLimit.Generic.Stream ι := fun _ ↦ y
  have hhistoryMemCore :
      ∀ i : Fin historyList.length,
        historyList.get i ∈ promptedCommonCore H S y := by
    intro i
    have hmemList : historyList.get i ∈ historyList :=
      List.get_mem historyList i
    have hmemC : historyList.get i ∈ C := by
      rw [← hhistoryFinset]
      simpa only [List.mem_toFinset] using hmemList
    change historyList.get i ∈ hcoreFinite.toFinset at hmemC
    rwa [Set.Finite.mem_toFinset] at hmemC
  have hhistoryLabel :
      ∀ i : Fin historyList.length, h (historyList.get i) = y := by
    intro i
    exact promptedCommonCore_subset_support hhVS (hhistoryMemCore i)
  have hfirstSample :
      GenLimit.Generic.sample xs S.card = S := by
    calc
      GenLimit.Generic.sample xs S.card =
          GenLimit.Generic.sample
            (GenLimit.Generic.historyThenFallback S.toList fallback) S.card := by
        apply GenLimit.Generic.sample_eq_of_eq_on_prefix
        intro n hn
        have hnS : n < S.toList.length := by simpa using hn
        have hnHistory : n < historyList.length := by
          simp only [historyList, List.length_append, Finset.length_toList]
          omega
        change GenLimit.Generic.historyThenFallback historyList fallback n =
          GenLimit.Generic.historyThenFallback S.toList fallback n
        simp only [GenLimit.Generic.historyThenFallback, dif_pos hnHistory,
          dif_pos hnS, historyList]
        exact List.getElem_append_left hnS
      _ = GenLimit.Generic.sample
          (GenLimit.Generic.historyThenFallback S.toList fallback)
            S.toList.length := by
        rw [Finset.length_toList]
      _ = S.toList.toFinset :=
        GenLimit.Generic.sample_historyThenFallback_length S.toList fallback
      _ = S := Finset.toList_toFinset S
  have hfirstPrompted :
      promptedSample h xs y S.card = S := by
    classical
    ext x
    rw [mem_promptedSample_iff, hfirstSample]
    constructor
    · exact fun hx ↦ hx.1
    · intro hx
      exact ⟨hx, hhVS.2 x hx⟩
  have hfullSample :
      GenLimit.Generic.sample xs historyList.length = C := by
    change GenLimit.Generic.sample
      (GenLimit.Generic.historyThenFallback historyList fallback)
        historyList.length = C
    rw [GenLimit.Generic.sample_historyThenFallback_length, hhistoryFinset]
  have htrigger :
      (promptedSample h xs y S.card).card = d + 1 := by
    rw [hfirstPrompted, hSd]
  have htime : S.card ≤ historyList.length := by
    simp [historyList]
  have hhistoryEq :
      promptedHistory h xs ys historyList.length =
        (fun i ↦ (historyList.get i, y, y)) := by
    funext i
    have hi : (i : ℕ) < historyList.length := i.isLt
    have hxsi : xs i = historyList.get i := by
      simp [xs, GenLimit.Generic.historyThenFallback, hi]
    change (xs i, h (xs i), ys i) = (historyList.get i, y, y)
    rw [hxsi, hhistoryLabel i]
  have hcorrect :=
    hgenSucc h hhVS.1 xs ys y S.card htrigger historyList.length htime
      hhistoryPos (by simp [ys])
  have hcorrect' := hcorrect hhistoryPos
  have houtput :
      gen historyList.length
          (promptedHistory h xs ys historyList.length) = xhat := by
    rw [hhistoryEq]
  rcases hbad with hxCore | hxLabel
  · apply hcorrect'.2
    rw [hfullSample, houtput]
    change xhat ∈ hcoreFinite.toFinset
    rwa [Set.Finite.mem_toFinset]
  · apply hxLabel
    have := hcorrect'.1
    rw [show ys (historyList.length - 1) = y by simp [ys],
      houtput] at this
    exact this

/-- Theorem 5.1, Characterization of Prompted Uniform Generatability. -/
theorem prompted_uniform_generatability_iff_finite_prompted_closure_dimension
    [Nonempty α] [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) :
    PromptedUniformlyGeneratable H ↔
      HasFinitePromptedClosureDimension H := by
  constructor
  · intro hUniform
    apply finite_prompted_closure_dimension_iff_not_infinite.mpr
    intro hInfinite
    exact prompted_closure_dimension_necessity hPUUS hInfinite hUniform
  · exact finite_prompted_closure_dimension_implies_uniform hPUUS

end GenLimit.LiRamanTewari
