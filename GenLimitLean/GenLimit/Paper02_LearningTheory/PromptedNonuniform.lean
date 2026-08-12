import GenLimit.Paper02_LearningTheory.PromptedClosure
import GenLimit.Paper02_LearningTheory.Common.Selection
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range

/-!
# Prompted non-uniform generation

This file formalizes Theorem 5.2 and Corollary 5.3 of
Li--Raman--Tewari, arXiv:2410.13714v5 / COLT 2025.
-/

namespace GenLimit.LiRamanTewari

open Common

/-- A literal non-decreasing cover of a multiclass hypothesis class. -/
def IsPromptedNondecreasingCover
    (H : MulticlassHypothesisClass α ι)
    (classes : ℕ → MulticlassHypothesisClass α ι) : Prop :=
  Monotone classes ∧ H = ⋃ n, classes n

/-- Necessity direction in Theorem 5.2. -/
theorem prompted_nonuniform_characterization_necessity
    [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι} (_hPUUS : PUUS H)
    (hNonuniform : PromptedNonuniformlyGeneratable H) :
    ∃ classes : ℕ → MulticlassHypothesisClass α ι,
      IsPromptedNondecreasingCover H classes ∧
      ∀ n, PromptedUniformlyGeneratable (classes n) := by
  classical
  obtain ⟨gen, hgen⟩ := hNonuniform
  let threshold : ∀ h, h ∈ H → ℕ :=
    fun h hhH ↦ Nat.find (hgen h hhH)
  let classes : ℕ → MulticlassHypothesisClass α ι :=
    fun n ↦ {h | ∃ hhH : h ∈ H, threshold h hhH ≤ n}
  refine ⟨classes, ?_, ?_⟩
  · constructor
    · intro m n hmn h hhm
      obtain ⟨hhH, hd⟩ := hhm
      exact ⟨hhH, hd.trans hmn⟩
    · ext h
      constructor
      · intro hhH
        exact Set.mem_iUnion.mpr
          ⟨threshold h hhH, hhH, le_rfl⟩
      · intro hh
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
        exact hn.choose
  · intro n
    refine ⟨gen, n, ?_⟩
    intro h hhn
    obtain ⟨hhH, hthreshold⟩ := hhn
    have hAtThreshold := Nat.find_spec (hgen h hhH)
    intro xs ys yStar
    exact GenLimit.Generic.eventualAtExactSize_mono
      (size := fun t ↦ (promptedSample h xs yStar t).card)
      (fun hk ↦ exists_earlier_promptedSample_card_eq hk)
      hthreshold (hAtThreshold xs ys yStar)

private noncomputable def promptedCoverGenerator [Nonempty α]
    (generators : ℕ → PromptedGenerator α ι)
    (threshold : ℕ → ℕ) : PromptedGenerator α ι := by
  classical
  exact fun t history ↦
    if ht : 0 < t then
      let last : Fin t := ⟨t - 1, Nat.sub_lt (by omega) (by omega)⟩
      let y := (history last).2.2
      let k := (promptedSequenceSample history y).card
      let eligible := eligibleIndices threshold k
      if hEligible : eligible.Nonempty then
        generators (largestEligible threshold k) t history
      else Classical.choice inferInstance
    else Classical.choice inferInstance

/-- Sufficiency direction in Theorem 5.2.  Padding each component threshold
by its class index makes the source's maximum eligible index finite. -/
theorem prompted_nonuniform_characterization_sufficiency
    [Nonempty α] [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι} (_hPUUS : PUUS H)
    {classes : ℕ → MulticlassHypothesisClass α ι}
    (hcover : IsPromptedNondecreasingCover H classes)
    (hUniform : ∀ n, PromptedUniformlyGeneratable (classes n)) :
    PromptedNonuniformlyGeneratable H := by
  classical
  choose generators thresholds hgenerators using hUniform
  let gen := promptedCoverGenerator generators thresholds
  refine ⟨gen, ?_⟩
  intro h hhH
  have hhUnion : h ∈ ⋃ n, classes n := by
    rwa [← hcover.2]
  obtain ⟨targetIndex, hhTarget⟩ := Set.mem_iUnion.mp hhUnion
  refine ⟨paddedThreshold thresholds targetIndex, ?_⟩
  intro xs ys yStar t ht s hts hs hcurrent
  have hsampleMono :
      promptedSample h xs yStar t ⊆
        promptedSample h xs yStar s :=
    promptedSample_mono hts
  have htargetEligibleBound :
      paddedThreshold thresholds targetIndex ≤
        (promptedSample h xs yStar s).card := by
    rw [← ht]
    exact Finset.card_le_card hsampleMono
  let history := promptedHistory h xs ys s
  have hlast :
      (history ⟨s - 1, Nat.sub_lt (by omega) (by omega)⟩).2.2 =
        yStar := by
    simpa [history, promptedHistory] using hcurrent
  let k := (promptedSample h xs yStar s).card
  let eligible := eligibleIndices thresholds k
  have htargetMem : targetIndex ∈ eligible := by
    apply mem_eligibleIndices_iff.mpr
    exact htargetEligibleBound
  have heligible : eligible.Nonempty := ⟨targetIndex, htargetMem⟩
  let selected := largestEligible thresholds k
  have htargetSelected : targetIndex ≤ selected :=
    le_largestEligible thresholds k targetIndex htargetMem
  have hhSelected : h ∈ classes selected :=
    hcover.1 htargetSelected hhTarget
  have hrawThresholdBound : thresholds selected ≤ k :=
    largestEligible_threshold_le thresholds k heligible
  obtain ⟨r, hrs, hrCard⟩ :=
    exists_earlier_promptedSample_card_eq hrawThresholdBound
  have hselectedCorrect :
      PromptedCorrectAt (generators selected) h xs ys s :=
    hgenerators selected h hhSelected xs ys yStar r hrCard s hrs hs hcurrent
  have hsequence :
      promptedSequenceSample history
          (history ⟨s - 1, Nat.sub_lt (by omega) (by omega)⟩).2.2 =
        promptedSample h xs yStar s := by
    rw [hlast]
    exact promptedSequenceSample_history h xs ys s yStar
  have houtput :
      gen s history = generators selected s history := by
    simp only [gen, promptedCoverGenerator, dif_pos hs]
    rw [hsequence]
    simp only [k, eligible, dif_pos heligible, selected]
  intro hs'
  have hselectedAt := hselectedCorrect hs'
  change gen s history ∈
    promptSupport h (ys (s - 1)) \
      (↑(GenLimit.Generic.sample xs s) : Set α)
  rw [houtput]
  exact hselectedAt

private theorem puus_of_prompted_cover
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H)
    {classes : ℕ → MulticlassHypothesisClass α ι}
    (hcover : IsPromptedNondecreasingCover H classes) (n : ℕ) :
    PUUS (classes n) := by
  intro h hhn y
  apply hPUUS h
  rw [hcover.2]
  exact Set.mem_iUnion.mpr ⟨n, hhn⟩

/-- Theorem 5.2, Characterization of Prompted Non-uniform Generatability. -/
theorem prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover
    [Nonempty α] [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) :
    PromptedNonuniformlyGeneratable H ↔
      ∃ classes : ℕ → MulticlassHypothesisClass α ι,
        IsPromptedNondecreasingCover H classes ∧
        ∀ n, HasFinitePromptedClosureDimension (classes n) := by
  constructor
  · intro hNonuniform
    obtain ⟨classes, hcover, hUniform⟩ :=
      prompted_nonuniform_characterization_necessity hPUUS hNonuniform
    refine ⟨classes, hcover, ?_⟩
    intro n
    exact
      (prompted_uniform_generatability_iff_finite_prompted_closure_dimension
        (puus_of_prompted_cover hPUUS hcover n)).mp (hUniform n)
  · rintro ⟨classes, hcover, hfinite⟩
    apply prompted_nonuniform_characterization_sufficiency hPUUS hcover
    intro n
    exact
      (prompted_uniform_generatability_iff_finite_prompted_closure_dimension
        (puus_of_prompted_cover hPUUS hcover n)).mpr (hfinite n)

private theorem finset_eventually_subset_stream_sample
    {xs : GenLimit.Generic.Stream α} (S : Finset α)
    (hS : (↑S : Set α) ⊆ Set.range xs) :
    ∃ T, S ⊆ GenLimit.Generic.sample xs T := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x S hxS ih =>
      obtain ⟨n, hn⟩ := hS
        (show x ∈ (↑(insert x S) : Set α) by simp)
      have hSrange : (↑S : Set α) ⊆ Set.range xs := by
        intro z hz
        exact hS
          (show z ∈ (↑(insert x S) : Set α) by simp [hz])
      obtain ⟨T, hT⟩ := ih hSrange
      refine ⟨max (n + 1) T, ?_⟩
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · rw [← hn]
        exact GenLimit.Generic.value_mem_sample
          (lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_max_left _ _))
      · exact GenLimit.Generic.sample_mono (Nat.le_max_right _ _) (hT hz)

private theorem exists_promptedSample_card_eq_of_presented_support
    {h : MulticlassHypothesis α ι}
    {xs : GenLimit.Generic.Stream α} {y : ι}
    (hPresented : PromptSupportPresented h xs y)
    (hInfinite : (promptSupport h y).Infinite) (d : ℕ) :
    ∃ t, (promptedSample h xs y t).card = d := by
  classical
  obtain ⟨S, hSsupport, hScard⟩ :=
    hInfinite.exists_subset_card_eq d
  obtain ⟨T, hST⟩ :=
    finset_eventually_subset_stream_sample S
      (fun x hx ↦ hPresented (hSsupport hx))
  have hSprompted : S ⊆ promptedSample h xs y T := by
    intro x hx
    exact mem_promptedSample_iff.mpr
      ⟨hST hx, hSsupport hx⟩
  have hdT : d ≤ (promptedSample h xs y T).card := by
    rw [← hScard]
    exact Finset.card_le_card hSprompted
  obtain ⟨t, _htT, ht⟩ :=
    exists_earlier_promptedSample_card_eq hdT
  exact ⟨t, ht⟩

theorem prompted_uniform_implies_nonuniform
    {H : MulticlassHypothesisClass α ι} :
    PromptedUniformlyGeneratable H →
      PromptedNonuniformlyGeneratable H := by
  rintro ⟨gen, d, hgen⟩
  exact ⟨gen, fun h hhH ↦ ⟨d, hgen h hhH⟩⟩

theorem prompted_nonuniform_implies_limit
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) :
    PromptedNonuniformlyGeneratable H →
      PromptedGeneratableInLimit H := by
  rintro ⟨gen, hgen⟩
  refine ⟨gen, ?_⟩
  intro h hhH xs ys yStar hPresented
  obtain ⟨d, hd⟩ := hgen h hhH
  obtain ⟨t, ht⟩ :=
    exists_promptedSample_card_eq_of_presented_support hPresented
      (hPUUS h hhH yStar) d
  refine ⟨t, ?_⟩
  intro s hts hs hcurrent
  exact hd xs ys yStar t ht s hts hs hcurrent

theorem prompted_uniform_implies_limit
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) :
    PromptedUniformlyGeneratable H →
      PromptedGeneratableInLimit H :=
  fun h ↦ prompted_nonuniform_implies_limit hPUUS
    (prompted_uniform_implies_nonuniform h)

/-- Finite multiclass classes have finite prompted closure dimension when
the prompt space is finite.  This is the corrected combinatorial content of
the proof of Corollary 5.3(i); it does not assert the source's unjustified
equality with arbitrary (not necessarily minimal) per-prompt thresholds. -/
theorem finite_prompt_class_has_finite_prompted_closure_dimension
    [Finite ι]
    {H : MulticlassHypothesisClass α ι} (hH : H.Finite) :
    HasFinitePromptedClosureDimension H := by
  classical
  let coreOf (V : Set (MulticlassHypothesis α ι)) (y : ι) : Set α :=
    {x | ∀ h, h ∈ V → h x = y}
  let coresFor (y : ι) : Set (Set α) :=
    (fun V ↦ coreOf V y) '' Set.powerset H
  have hcoresFor : ∀ y, (coresFor y).Finite := by
    intro y
    exact hH.powerset.image (fun V ↦ coreOf V y)
  let allCores : Set (Set α) := ⋃ y, coresFor y
  have hcoresFinite : allCores.Finite := by
    exact Set.finite_iUnion hcoresFor
  let cores : Finset (Set α) := hcoresFinite.toFinset
  let bound : ℕ := cores.sup Set.ncard
  apply finite_prompted_closure_dimension_iff_not_infinite.mpr
  intro hInfinite
  obtain ⟨y, S, hlarge, hS⟩ := hInfinite (bound + 1)
  have hcoreMem : promptedCommonCore H S y ∈ cores := by
    change promptedCommonCore H S y ∈ hcoresFinite.toFinset
    rw [Set.Finite.mem_toFinset]
    apply Set.mem_iUnion.mpr
    refine ⟨y, ?_⟩
    exact ⟨promptedVersionSpace H S y, fun h hh ↦ hh.1, rfl⟩
  have hcoreBound :
      (promptedCommonCore H S y).ncard ≤ bound :=
    Finset.le_sup (f := Set.ncard) hcoreMem
  have hsampleCore :
      S.card ≤ (promptedCommonCore H S y).ncard := by
    simpa using
      Set.ncard_le_ncard promptedSample_subset_commonCore hS.2
  omega

/-- Corollary 5.3(i). -/
theorem finite_prompt_classes_are_uniformly_generatable
    [Nonempty α] [Countable α] [Countable ι] [Finite ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H)
    (hFinite : H.Finite) :
    PromptedUniformlyGeneratable H :=
  finite_prompted_closure_dimension_implies_uniform hPUUS
    (finite_prompt_class_has_finite_prompted_closure_dimension hFinite)

/-- Corollary 5.3(ii), stated in the stronger form covering every countable
class (finite or countably infinite). -/
theorem countable_prompt_classes_are_nonuniformly_generatable
    [Nonempty α] [Countable α] [Countable ι] [Finite ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H)
    (hCountable : H.Countable) :
    PromptedNonuniformlyGeneratable H := by
  classical
  by_cases hHempty : H = ∅
  · refine ⟨(fun _ _ ↦ Classical.choice (inferInstance : Nonempty α)), ?_⟩
    intro h hh
    rw [hHempty] at hh
    exact False.elim hh
  have hHnonempty : H.Nonempty := Set.nonempty_iff_ne_empty.mpr hHempty
  obtain ⟨h₀, hh₀⟩ := hHnonempty
  letI : Nonempty (MulticlassHypothesis α ι) := ⟨h₀⟩
  obtain ⟨enumerate, hEnumerates⟩ :=
    Set.countable_iff_exists_subset_range.mp hCountable
  let classes : ℕ → MulticlassHypothesisClass α ι :=
    fun n ↦ {h | h ∈ H ∧ ∃ i < n + 1, enumerate i = h}
  apply
    (prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover
      hPUUS).mpr
  refine ⟨classes, ?_, ?_⟩
  · constructor
    · intro m n hmn h hhm
      obtain ⟨hhH, i, him, rfl⟩ := hhm
      exact ⟨hhH, i, him.trans_le (Nat.add_le_add_right hmn 1), rfl⟩
    · ext h
      constructor
      · intro hhH
        obtain ⟨i, hi⟩ := hEnumerates hhH
        exact Set.mem_iUnion.mpr
          ⟨i, hhH, i, Nat.lt_succ_self i, hi⟩
      · intro hh
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
        exact hn.1
  · intro n
    apply finite_prompt_class_has_finite_prompted_closure_dimension
    apply (Set.finite_range
      (fun i : Fin (n + 1) ↦ enumerate i)).subset
    intro h hhn
    obtain ⟨_hhH, i, hin, rfl⟩ := hhn
    exact ⟨⟨i, hin⟩, rfl⟩

/-- Corollary 5.3(iii), again strengthened to all countable classes. -/
theorem countable_prompt_classes_are_generatable_in_limit
    [Nonempty α] [Countable α] [Countable ι] [Finite ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H)
    (hCountable : H.Countable) :
    PromptedGeneratableInLimit H :=
  prompted_nonuniform_implies_limit hPUUS
    (countable_prompt_classes_are_nonuniformly_generatable
      hPUUS hCountable)

end GenLimit.LiRamanTewari
