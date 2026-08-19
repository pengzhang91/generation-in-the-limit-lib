import GenLimit.Paper09_RepresentativeLanguageGeneration.Definitions
import GenLimit.Core.ClassCovers
import GenLimit.Support.ThresholdSelection

/-!
# Representative non-uniform generation

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Theorem 3.7 and Appendix C.4.

The proof follows the paper's increasing-cover construction.  As in the
shared Li--Raman--Tewari formalization, each component threshold is padded by
its class index.  This makes every eligible-index set finite and gives its
maximum without the source proof's unnecessary assertion that the raw
threshold sequence may be taken monotone.

The theorem below is slightly stronger than the displayed source statement:
neither countability, the UUS property, nor the partition axioms are used by
this characterization once representative uniform/non-uniform generation
have been defined.
-/

namespace GenLimit.RepresentativeGeneration

/-- Necessity in published Theorem 3.7: one representative non-uniform generator
uniformly generates each bounded-threshold subcollection. -/
theorem representative_nonuniform_cover_necessity
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (hNonuniform : RepresentativelyNonuniformlyGeneratable H groups) :
    ∀ alpha : ℝ, 0 < alpha →
      ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
        GenLimit.Generic.IsNondecreasingCover H classes ∧
        ∀ n, AlphaRepresentativeUniformlyGeneratable
          (classes n) groups alpha := by
  classical
  intro alpha halpha
  obtain ⟨gen, hrep, hgen⟩ := hNonuniform alpha halpha
  let threshold : ∀ L, L ∈ H → ℕ :=
    fun L hLH => Classical.choose (hgen L hLH)
  let classes : ℕ → GenLimit.Generic.LanguageClass α :=
    fun n => {L | ∃ hLH : L ∈ H, threshold L hLH ≤ n}
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
    refine ⟨gen, hrep, n, ?_⟩
    intro L hLn
    obtain ⟨hLH, hthreshold⟩ := hLn
    intro stream hstream
    exact GenLimit.Generic.eventualAtExactSize_mono
      (size := fun t ↦ (GenLimit.Generic.sample stream t).card)
      (fun hk ↦ GenLimit.Generic.exists_sample_card_eq_of_le hk)
      hthreshold (Classical.choose_spec (hgen L hLH) stream hstream)

private noncomputable def coverRepresentativeGenerator
    (generators : ℕ → RandomizedGenerator α)
    (threshold : ℕ → ℕ) : RandomizedGenerator α :=
  fun _ xs =>
    generators
      (GenLimit.Support.largestEligible threshold
        (GenLimit.Generic.sequenceSample xs).card) _ xs

/-- Sufficiency in published Theorem 3.7.  The maximum eligible index is selected from
a genuinely finite set after padding each valid threshold by its index. -/
theorem representative_nonuniform_cover_sufficiency
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (hcover :
      ∀ alpha : ℝ, 0 < alpha →
        ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
          GenLimit.Generic.IsNondecreasingCover H classes ∧
          ∀ n, AlphaRepresentativeUniformlyGeneratable
            (classes n) groups alpha) :
    RepresentativelyNonuniformlyGeneratable H groups := by
  classical
  intro alpha halpha
  obtain ⟨classes, hclasses, hUniform⟩ := hcover alpha halpha
  choose generators hrepresentative thresholds hgenerators using hUniform
  let gen := coverRepresentativeGenerator generators thresholds
  have hgenRepresentative : IsAlphaRepresentative gen groups alpha := by
    intro stream t ht
    let k := (GenLimit.Generic.sample stream t).card
    let selected := GenLimit.Support.largestEligible thresholds k
    have houtput :
        distributionAt gen stream t =
          distributionAt (generators selected) stream t := by
      simp only [distributionAt, gen, coverRepresentativeGenerator,
        GenLimit.Generic.sequenceSample_prefix, k, selected]
    rw [houtput]
    exact hrepresentative selected stream t ht
  refine ⟨gen, hgenRepresentative, ?_⟩
  intro L hLH
  have hLUnion : L ∈ ⋃ n, classes n := by
    rwa [← hclasses.2]
  obtain ⟨targetIndex, hLTarget⟩ := Set.mem_iUnion.mp hLUnion
  refine
    ⟨GenLimit.Support.paddedThreshold thresholds targetIndex, ?_⟩
  intro stream hstream t ht s hts
  have hsampleMono :
      GenLimit.Generic.sample stream t ⊆
        GenLimit.Generic.sample stream s :=
    GenLimit.Generic.sample_mono hts
  have htargetEligibleBound :
      GenLimit.Support.paddedThreshold thresholds targetIndex ≤
        (GenLimit.Generic.sample stream s).card := by
    rw [← ht]
    exact Finset.card_le_card hsampleMono
  let k := (GenLimit.Generic.sample stream s).card
  let eligible := GenLimit.Support.eligibleIndices thresholds k
  have htargetMem : targetIndex ∈ eligible := by
    exact GenLimit.Support.mem_eligibleIndices_iff.mpr
      htargetEligibleBound
  have heligible : eligible.Nonempty := ⟨targetIndex, htargetMem⟩
  let selected := GenLimit.Support.largestEligible thresholds k
  have htargetSelected : targetIndex ≤ selected :=
    GenLimit.Support.le_largestEligible
      thresholds k targetIndex htargetMem
  have hLSelected : L ∈ classes selected :=
    hclasses.1 htargetSelected hLTarget
  have hrawThresholdBound : thresholds selected ≤ k :=
    GenLimit.Support.largestEligible_threshold_le
      thresholds k heligible
  obtain ⟨r, hrs, hrCard⟩ :=
    GenLimit.Generic.exists_sample_card_eq_of_le hrawThresholdBound
  have hselectedConsistent :
      IsConsistentAt (generators selected) L stream s :=
    hgenerators selected L hLSelected stream hstream r hrCard s hrs
  have houtput :
      distributionAt gen stream s =
        distributionAt (generators selected) stream s := by
    simp only [distributionAt, gen, coverRepresentativeGenerator,
      GenLimit.Generic.sequenceSample_prefix, k, selected]
  simpa only [IsConsistentAt, houtput] using hselectedConsistent

/-- Published Theorem 3.7 (Characterization of Representative Non-uniform
Generatability). -/
theorem representative_nonuniform_iff_uniform_nondecreasing_cover
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} :
    RepresentativelyNonuniformlyGeneratable H groups ↔
      ∀ alpha : ℝ, 0 < alpha →
        ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
          GenLimit.Generic.IsNondecreasingCover H classes ∧
          ∀ n, AlphaRepresentativeUniformlyGeneratable
            (classes n) groups alpha :=
  ⟨representative_nonuniform_cover_necessity,
    representative_nonuniform_cover_sufficiency⟩

end GenLimit.RepresentativeGeneration
