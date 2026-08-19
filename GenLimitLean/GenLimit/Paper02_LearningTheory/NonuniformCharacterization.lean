import GenLimit.Paper02_LearningTheory.Closure
import GenLimit.Paper02_LearningTheory.Common.Selection
import GenLimit.Support.CountableCovers
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Powerset

/-!
# Non-uniform generation and non-decreasing covers

This file formalizes Lemmas 3.7 and 3.8 and Theorem 3.5 of
Li--Raman--Tewari, *Generation through the Lens of Learning Theory*,
arXiv:2410.13714v5 / COLT 2025.

The proof of Lemma 3.8 uses the paper's maximum-eligible-index construction.
To make that maximum well-defined without an extra convergence assumption on
the displayed sample complexities, we replace each valid bound `d n` by the
still-valid padded bound `max n (d n)`.  Hence every index eligible after `k`
distinct examples is at most `k`, and the maximum is taken over a finite set.
The padding is necessary for the displayed proof as written: an unbounded
sequence can still have an infinite sublevel set (for example, alternate the
value `1` with an increasing sequence), in which case its eligible indices
need not have a maximum.
-/

namespace GenLimit.LiRamanTewari

open Common

/-- Lemma 3.7 (necessity in Theorem 3.5). -/
theorem nonuniform_characterization_necessity [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H)
    (hNonuniform : NonuniformlyGeneratable H) :
    ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
      IsNondecreasingCover H classes ∧
      ∀ n, UniformlyGeneratable (classes n) := by
  classical
  obtain ⟨gen, hgen⟩ := hNonuniform
  let threshold : ∀ L, L ∈ H → ℕ :=
    fun L hLH ↦ Nat.find (hgen L hLH)
  let classes : ℕ → GenLimit.Generic.LanguageClass α :=
    fun n ↦ {L | ∃ hLH : L ∈ H, threshold L hLH ≤ n}
  refine ⟨classes, ?_, ?_⟩
  · constructor
    · intro m n hmn L hLm
      obtain ⟨hLH, hd⟩ := hLm
      exact ⟨hLH, hd.trans hmn⟩
    · ext L
      constructor
      · intro hLH
        apply Set.mem_iUnion.mpr
        exact ⟨threshold L hLH, hLH, le_rfl⟩
      · intro hLUnion
        obtain ⟨n, hLn⟩ := Set.mem_iUnion.mp hLUnion
        exact hLn.choose
  · intro n
    refine ⟨gen, n, ?_⟩
    intro L hLn
    obtain ⟨hLH, hthreshold⟩ := hLn
    have hAtThreshold := Nat.find_spec (hgen L hLH)
    intro stream hstream
    exact GenLimit.Generic.eventualAtExactSize_mono
      (size := fun t ↦ (GenLimit.Generic.sample stream t).card)
      (fun hk ↦ GenLimit.Generic.exists_sample_card_eq_of_le hk)
      hthreshold (hAtThreshold stream hstream)

private noncomputable def coverGenerator [Nonempty α]
    (generators : ℕ → GenLimit.Generic.Generator α)
    (threshold : ℕ → ℕ) : GenLimit.Generic.Generator α := by
  classical
  exact fun _ xs ↦
    let k := (GenLimit.Generic.sequenceSample xs).card
    let eligible := eligibleIndices threshold k
    if h : eligible.Nonempty then
      generators (largestEligible threshold k) _ xs
    else
      Classical.choice inferInstance

/-- Lemma 3.8 (sufficiency in Theorem 3.5).

The padded thresholds are legitimate upper bounds for the individual
generators and make the paper's maximum-eligible-index step finite. -/
theorem nonuniform_characterization_sufficiency [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (_hUUS : UUS H)
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hcover : IsNondecreasingCover H classes)
    (hUniform : ∀ n, UniformlyGeneratable (classes n)) :
    NonuniformlyGeneratable H := by
  classical
  choose generators thresholds hgenerators using hUniform
  let gen := coverGenerator generators thresholds
  refine ⟨gen, ?_⟩
  intro L hLH
  have hLUnion : L ∈ ⋃ n, classes n := by
    rwa [← hcover.2]
  obtain ⟨targetIndex, hLTarget⟩ := Set.mem_iUnion.mp hLUnion
  refine ⟨paddedThreshold thresholds targetIndex, ?_⟩
  intro stream hstream t ht s hts
  have hsampleMono : GenLimit.Generic.sample stream t ⊆ GenLimit.Generic.sample stream s :=
    GenLimit.Generic.sample_mono hts
  have htargetEligibleBound :
      paddedThreshold thresholds targetIndex ≤
        (GenLimit.Generic.sample stream s).card := by
    rw [← ht]
    exact Finset.card_le_card hsampleMono
  let k := (GenLimit.Generic.sample stream s).card
  let eligible := eligibleIndices thresholds k
  have htargetMem : targetIndex ∈ eligible := by
    apply mem_eligibleIndices_iff.mpr
    exact htargetEligibleBound
  have heligible : eligible.Nonempty := ⟨targetIndex, htargetMem⟩
  let selected := largestEligible thresholds k
  have htargetSelected : targetIndex ≤ selected :=
    le_largestEligible thresholds k targetIndex htargetMem
  have hLSelected : L ∈ classes selected :=
    hcover.1 htargetSelected hLTarget
  have hrawThresholdBound : thresholds selected ≤ k :=
    largestEligible_threshold_le thresholds k heligible
  obtain ⟨r, hrs, hrCard⟩ :=
    GenLimit.Generic.exists_sample_card_eq_of_le hrawThresholdBound
  have hselectedCorrect :
      GenLimit.Generic.CorrectAt (generators selected) L stream s :=
    hgenerators selected L hLSelected stream hstream r hrCard s hrs
  have houtput :
      GenLimit.Generic.output gen stream s =
        GenLimit.Generic.output (generators selected) stream s := by
    unfold GenLimit.Generic.output
    simp only [gen, coverGenerator, GenLimit.Generic.sequenceSample_prefix,
      k, eligible, dif_pos heligible, selected]
  simpa only [GenLimit.Generic.CorrectAt, houtput] using hselectedCorrect

private theorem uus_of_cover
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hcover : IsNondecreasingCover H classes) (n : ℕ) :
    UUS (classes n) := by
  intro L hLn
  apply hUUS L
  rw [hcover.2]
  exact Set.mem_iUnion.mpr ⟨n, hLn⟩

/-- Theorem 3.5 (Characterization of Non-uniform Generatability). -/
theorem nonuniform_generatability_iff_nondecreasing_finite_closure_cover
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) :
    NonuniformlyGeneratable H ↔
      ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
        IsNondecreasingCover H classes ∧
        ∀ n, HasFiniteClosureDimension (classes n) := by
  constructor
  · intro hNonuniform
    obtain ⟨classes, hcover, hUniform⟩ :=
      nonuniform_characterization_necessity hUUS hNonuniform
    refine ⟨classes, hcover, ?_⟩
    intro n
    exact (uniform_generatability_iff_finite_closure_dimension
      (uus_of_cover hUUS hcover n)).mp (hUniform n)
  · rintro ⟨classes, hcover, hfinite⟩
    apply nonuniform_characterization_sufficiency hUUS hcover
    intro n
    exact (uniform_generatability_iff_finite_closure_dimension
      (uus_of_cover hUUS hcover n)).mpr (hfinite n)

/-- A finite language class has finite closure dimension.  This is the
combinatorial fact about finite classes used in the paper's proof of
Corollary 3.6 (there via Theorem 2.5 and Theorem 3.3). -/
theorem finite_language_class_has_finite_closure_dimension
    {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite) :
    HasFiniteClosureDimension H := by
  classical
  apply finite_closure_dimension_iff_not_infinite.mpr
  intro hInfinite
  let coreOf : Set (GenLimit.Generic.Language α) → GenLimit.Generic.Language α :=
    fun V ↦ {x | ∀ L, L ∈ V → x ∈ L}
  have hcoresFinite : (coreOf '' Set.powerset H).Finite :=
    hH.powerset.image coreOf
  let cores : Finset (GenLimit.Generic.Language α) := hcoresFinite.toFinset
  let bound : ℕ := cores.sup Set.ncard
  obtain ⟨S, hlarge, hS⟩ := hInfinite (bound + 1)
  have hcoreMem : commonCore H S ∈ cores := by
    change commonCore H S ∈ hcoresFinite.toFinset
    rw [Set.Finite.mem_toFinset]
    refine ⟨versionSpace H S, ?_, rfl⟩
    exact fun L hL ↦ hL.1
  have hcoreBound : (commonCore H S).ncard ≤ bound := by
    exact Finset.le_sup (f := Set.ncard) hcoreMem
  have hsampleCore : S.card ≤ (commonCore H S).ncard := by
    simpa using Set.ncard_le_ncard sample_subset_commonCore hS.2
  omega

/-- Corollary 3.6 (Countable Classes are Non-uniformly Generatable).

The finite-prefix cover below also handles empty and finite classes: the
ambient enumeration may repeat or contain values outside `H`, and every
prefix is intersected back with `H`. -/
theorem countable_classes_are_nonuniformly_generatable
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hCountable : H.Countable) :
    NonuniformlyGeneratable H := by
  classical
  obtain ⟨enumerate, hEnumerates⟩ :=
    Set.countable_iff_exists_subset_range.mp hCountable
  apply (nonuniform_generatability_iff_nondecreasing_finite_closure_cover hUUS).mpr
  refine
    ⟨GenLimit.Support.finitePrefixSubclass H enumerate,
      GenLimit.Support.finitePrefixSubclass_isNondecreasingCover
        H enumerate hEnumerates,
      ?_⟩
  · intro n
    apply finite_language_class_has_finite_closure_dimension
    exact GenLimit.Support.finitePrefixSubclass_finite H enumerate n

end GenLimit.LiRamanTewari
