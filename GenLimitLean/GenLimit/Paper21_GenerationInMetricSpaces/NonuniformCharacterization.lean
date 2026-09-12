import GenLimit.Paper21_GenerationInMetricSpaces.UniformSufficiency
import GenLimit.Paper21_GenerationInMetricSpaces.UniformNecessityDiagnostic
import GenLimit.Core.ClassCovers
import Mathlib.Data.Finset.Max

/-!
# Non-uniform metric generation: Theorem 3.3

Source: Jiaxun Li, Vinod Raman, and Ambuj Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1.

The semantic equivalence with a nondecreasing cover by *uniformly
generatable* subclasses is valid without any covering-center repair.  The
finite scale-closure-dimension formulation has a valid forward construction
from such a cover, while its converse needs the same internal-center premise
missing from Theorem 3.1.

Thus the source's printed implication `(ii) → (i)` is checked literally,
whereas `(i) → (ii)` is stated only with the exact missing premise exposed.
`NonuniformNecessityDiagnostic` gives a separable genuine-metric
counterexample to the unqualified printed converse.
-/

namespace GenLimit.MetricSpaces

/-- Compatibility name for the shared nondecreasing-cover interface. -/
abbrev IsNondecreasingMetricCover
    (H : GenLimit.Generic.LanguageClass α)
    (classes : ℕ → GenLimit.Generic.LanguageClass α) : Prop :=
  GenLimit.Generic.IsNondecreasingCover H classes

/-- A uniform generator is also a non-uniform generator. -/
theorem metric_uniform_implies_nonuniform
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (h : UniformlyGeneratableAt ρ ε ε' H) :
    NonuniformlyGeneratableAt ρ ε ε' H := by
  obtain ⟨gen, d, hgen⟩ := h
  exact ⟨gen, fun L hL ↦ ⟨d, hgen L hL⟩⟩

/-- Lemma B.4, before the paper replaces uniform generatability by finite
scale-closure dimension.  This step is independent of Theorem 3.1. -/
theorem nonuniform_implies_nondecreasing_uniform_cover
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hNonuniform : NonuniformlyGeneratableAt ρ ε ε' H) :
    ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
      IsNondecreasingMetricCover H classes ∧
      ∀ n, UniformlyGeneratableAt ρ ε ε' (classes n) := by
  classical
  obtain ⟨gen, hgen⟩ := hNonuniform
  let threshold : ∀ L, L ∈ H → ℕ :=
    fun L hLH ↦ Classical.choose (hgen L hLH)
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
        exact Set.mem_iUnion.mpr
          ⟨threshold L hLH, hLH, le_rfl⟩
      · intro hLUnion
        obtain ⟨n, hLn⟩ := Set.mem_iUnion.mp hLUnion
        exact hLn.choose
  · intro n
    refine ⟨gen, n, ?_⟩
    intro L hLn
    obtain ⟨hLH, hthreshold⟩ := hLn
    have hAtThreshold :=
      Classical.choose_spec (hgen L hLH)
    intro stream hstream t ht s hts
    exact hAtThreshold stream hstream t
      (fun centers hcover ↦
        hthreshold.trans (ht centers hcover)) s hts

private def paddedMetricThreshold
    (threshold : ℕ → ℕ) (n : ℕ) : ℕ :=
  max n (threshold n)

private noncomputable def eligibleMetricIndices
    (ρ : Distance α) (ε : ℝ)
    (threshold : ℕ → ℕ)
    (t : ℕ) (xs : Fin t → α) : Finset ℕ :=
  by
    classical
    exact
      (Finset.range (t + 1)).filter fun n ↦
        CoveringNumberAtLeast ρ ε
          (GenLimit.Generic.sequenceSample xs : Set α)
          (threshold n)

private theorem mem_eligibleMetricIndices
    {ρ : Distance α} {ε : ℝ}
    {threshold : ℕ → ℕ}
    {t : ℕ} {xs : Fin t → α} {n : ℕ}
    (hnt : n ≤ t)
    (htrigger :
      CoveringNumberAtLeast ρ ε
        (GenLimit.Generic.sequenceSample xs : Set α)
        (threshold n)) :
    n ∈ eligibleMetricIndices ρ ε threshold t xs := by
  classical
  rw [eligibleMetricIndices, Finset.mem_filter]
  exact
    ⟨Finset.mem_range.mpr
      (by
        simpa only [Nat.succ_eq_add_one] using
          (Nat.lt_succ_iff.mpr hnt)),
      htrigger⟩

private noncomputable def metricCoverGenerator
    (ρ : Distance α) (ε : ℝ)
    (generators : ℕ → GenLimit.Generic.Generator α)
    (threshold : ℕ → ℕ) :
    GenLimit.Generic.Generator α := by
  classical
  exact fun t xs ↦
    let eligible :=
      eligibleMetricIndices ρ ε threshold t xs
    if h : eligible.Nonempty then
      generators (eligible.max' h) t xs
    else
      generators 0 t xs

/-- Lemma B.5.  A nondecreasing cover by uniformly generatable subclasses
is non-uniformly generatable.

The index padding is encoded in the target threshold `max targetIndex
(threshold targetIndex)`.  At round `s`, eligible indices are restricted to
`0,...,s`, so their maximum exists even when the raw threshold sequence has
an infinite sublevel set. -/
theorem nondecreasing_uniform_cover_implies_nonuniform
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hself : ∀ x : α, ρ x x ≤ ε)
    (hcover : IsNondecreasingMetricCover H classes)
    (hUniform :
      ∀ n, UniformlyGeneratableAt ρ ε ε' (classes n)) :
    NonuniformlyGeneratableAt ρ ε ε' H := by
  classical
  choose generators thresholds hgenerators using hUniform
  let gen := metricCoverGenerator ρ ε generators thresholds
  refine ⟨gen, ?_⟩
  intro L hLH
  have hLUnion : L ∈ ⋃ n, classes n := by
    rwa [← hcover.2]
  obtain ⟨targetIndex, hLTarget⟩ :=
    Set.mem_iUnion.mp hLUnion
  refine
    ⟨paddedMetricThreshold thresholds targetIndex, ?_⟩
  intro stream hstream t ht s hts
  have hsampleMono :
      (GenLimit.Generic.sample stream t : Set α) ⊆
        (GenLimit.Generic.sample stream s : Set α) := by
    exact fun x hx ↦
      GenLimit.Generic.sample_mono hts hx
  have htargetRawTrigger :
      CoveringNumberAtLeast ρ ε
        (GenLimit.Generic.sample stream s : Set α)
        (thresholds targetIndex) := by
    intro centers hcenters
    have hcoverAtT :
        (GenLimit.Generic.sample stream t : Set α) ⊆
          closedNeighborhood ρ (centers : Set α) ε :=
      hsampleMono.trans hcenters
    have hpadded :=
      ht centers hcoverAtT
    exact
      (le_max_right targetIndex
        (thresholds targetIndex)).trans hpadded
  have htargetTime : targetIndex ≤ s := by
    have hsampleSelfCover :
        (GenLimit.Generic.sample stream t : Set α) ⊆
          closedNeighborhood ρ
            (GenLimit.Generic.sample stream t : Set α) ε := by
      intro x hx η hεη
      exact ⟨x, hx, (hself x).trans_lt hεη⟩
    have hpaddedCard :
        paddedMetricThreshold thresholds targetIndex ≤
          (GenLimit.Generic.sample stream t).card :=
      ht (GenLimit.Generic.sample stream t)
        hsampleSelfCover
    exact
      (le_max_left targetIndex
        (thresholds targetIndex)).trans
        (hpaddedCard.trans
          ((GenLimit.Generic.sample_card_le stream t).trans hts))
  let xs : Fin s → α := fun i ↦ stream i
  let eligible :=
    eligibleMetricIndices ρ ε thresholds s xs
  have htargetMem : targetIndex ∈ eligible := by
    apply mem_eligibleMetricIndices htargetTime
    simpa only [xs, GenLimit.Generic.sequenceSample_prefix]
      using htargetRawTrigger
  have heligible : eligible.Nonempty :=
    ⟨targetIndex, htargetMem⟩
  let selected := eligible.max' heligible
  have hselectedMem : selected ∈ eligible :=
    Finset.max'_mem eligible heligible
  have htargetSelected : targetIndex ≤ selected :=
    Finset.le_max' eligible targetIndex htargetMem
  have hLSelected : L ∈ classes selected :=
    hcover.1 htargetSelected hLTarget
  have hselectedTrigger :
      CoveringNumberAtLeast ρ ε
        (GenLimit.Generic.sample stream s : Set α)
        (thresholds selected) := by
    have hselectedMem' :
        selected ∈
          eligibleMetricIndices ρ ε thresholds s xs := by
      exact hselectedMem
    have hselectedFiltered :=
      (Finset.mem_filter.mp
        (by
          simpa only [eligibleMetricIndices]
            using hselectedMem')).2
    simpa only [xs, GenLimit.Generic.sequenceSample_prefix]
      using hselectedFiltered
  have hselectedCorrect :
      MetricCorrectAt ρ ε' (generators selected)
        L stream s :=
    hgenerators selected L hLSelected stream hstream
      s hselectedTrigger s le_rfl
  have houtput :
      GenLimit.Generic.output gen stream s =
        GenLimit.Generic.output
          (generators selected) stream s := by
    unfold GenLimit.Generic.output
    simp only [gen, metricCoverGenerator,
      xs, eligible, dif_pos heligible, selected]
  simpa only [MetricCorrectAt, houtput]
    using hselectedCorrect

/-- The exact semantic core of source Theorem 3.3 is valid. -/
theorem nonuniform_iff_nondecreasing_uniform_cover
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hself : ∀ x : α, ρ x x ≤ ε) :
    NonuniformlyGeneratableAt ρ ε ε' H ↔
      ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
        IsNondecreasingMetricCover H classes ∧
        ∀ n, UniformlyGeneratableAt ρ ε ε' (classes n) := by
  constructor
  · exact nonuniform_implies_nondecreasing_uniform_cover
  · rintro ⟨classes, hcover, hUniform⟩
    exact
      nondecreasing_uniform_cover_implies_nonuniform
        hself hcover hUniform

/-- The `(ii) → (i)` direction of printed Theorem 3.3 is source-faithful
under the paper's literal ambient-center covering definition. -/
theorem finite_scaleClosure_cover_implies_nonuniform
    [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x : α, ρ x x = 0)
    (hε : 0 ≤ ε)
    (hcover : IsNondecreasingMetricCover H classes)
    (hfinite :
      ∀ n,
        HasFiniteScaleClosureDimension
          ρ ε ε' (classes n)) :
    NonuniformlyGeneratableAt ρ ε ε' H := by
  apply
    nondecreasing_uniform_cover_implies_nonuniform
      (fun x ↦ by rw [hrefl x]; exact hε) hcover
  intro n
  exact
    finite_scaleClosureDimension_implies_uniform
      hrefl hε (hfinite n)

/-- A corrected `(i) → (ii)` direction: it suffices that every subclass of
the target class internalize ambient covers of scale-closure witnesses at
the same radius. -/
theorem nonuniform_implies_finite_scaleClosure_cover_of_internalization
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hInternal :
      ∀ K : GenLimit.Generic.LanguageClass α,
        K ⊆ H →
          ScaleClosureWitnessCoverInternalizationAt
            ρ ε ε' K)
    (hNonuniform :
      NonuniformlyGeneratableAt ρ ε ε' H) :
    ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
      IsNondecreasingMetricCover H classes ∧
      ∀ n,
        HasFiniteScaleClosureDimension
          ρ ε ε' (classes n) := by
  obtain ⟨classes, hcover, hUniform⟩ :=
    nonuniform_implies_nondecreasing_uniform_cover
      hNonuniform
  refine ⟨classes, hcover, ?_⟩
  intro n
  apply
    uniform_implies_finite_scaleClosureDimension_of_internalization
      (hInternal (classes n) ?_)
      (hUniform n)
  intro L hLn
  rw [hcover.2]
  exact Set.mem_iUnion.mpr ⟨n, hLn⟩

end GenLimit.MetricSpaces
