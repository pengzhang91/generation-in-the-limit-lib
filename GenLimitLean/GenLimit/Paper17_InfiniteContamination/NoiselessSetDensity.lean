import GenLimit.Bridges.BasicToGeneric
import GenLimit.Paper01_LanguageGeneration.SetInterface
import GenLimit.Paper17_InfiniteContamination.SetDensityObstruction

/-!
# Noiseless set generation with lower density

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Lemma 6.8.

The source invokes the noiseless Kleinberg--Mullainathan generator.  On a
finite sample we take its highest critical language, but output the whole
language after deleting the observed sample.  The critical-language proof
eventually puts this output inside the target.  The pairwise hypothesis of
Lemma 6.8 supplies its density, and the shared finite-perturbation theorem
shows that deleting the finite sample does not change that density.

The interface is an explicit indexed enumeration of the countable family,
matching the indexed interfaces used elsewhere in this repository.  An
`OrderedLanguage` is supplied for each family member solely to measure
density in that target's fixed canonical order.
-/

namespace GenLimit.InfiniteContamination

open Filter
open GenLimit.KleinbergWei

/-- Set-valued form of the semantic KM construction used in Lemma 6.8. -/
noncomputable def noiselessDensityGenerator
    (O : GenLimit.OracleFamily) : SetGenerator ℕ :=
  fun _ history =>
    O.language
        (GenLimit.KM.SetInterface.focus O.language
          (GenLimit.Generic.sequenceSample history)) \
      (↑(GenLimit.Generic.sequenceSample history) : Set ℕ)

@[simp] theorem noiselessDensityGenerator_output
    (O : GenLimit.OracleFamily)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    setOutput (noiselessDensityGenerator O) stream t =
      O.language
          (GenLimit.KM.SetInterface.focus O.language
            (GenLimit.Generic.sample stream t)) \
        (↑(GenLimit.Generic.sample stream t) : Set ℕ) := by
  simp [setOutput, noiselessDensityGenerator,
    GenLimit.Generic.sequenceSample_prefix]

/-- Every finite-history output of the Lemma 6.8 generator is infinite. -/
theorem noiselessDensityGenerator_infinite
    (O : GenLimit.OracleFamily) :
    IsInfiniteSetGenerator (noiselessDensityGenerator O) := by
  intro t history
  exact
    (O.infinite'
      (GenLimit.KM.SetInterface.focus O.language
        (GenLimit.Generic.sequenceSample history))).diff
      (GenLimit.Generic.sequenceSample history).finite_toSet

private theorem noiselessDensityGenerator_eventually_correct
    (O : GenLimit.OracleFamily)
    {stream : GenLimit.Generic.Stream ℕ} {z : ℕ}
    (hpresents :
      GenLimit.Generic.Presents stream (O.language z))
    (hinjective : Function.Injective stream) :
    ∃ T, ∀ t, T ≤ t →
      let i :=
        GenLimit.KM.SetInterface.focus O.language
          (GenLimit.Generic.sample stream t)
      O.language i ⊆ O.language z ∧
        SetCorrectAt (noiselessDensityGenerator O)
          (O.language z) stream t := by
  have hpresentsBasic : GenLimit.Presents stream (O.language z) :=
    (GenLimit.Bridge.basicPresents_iff_genericPresents stream
      (O.language z)).2 hpresents
  obtain ⟨Tcritical, hcritical⟩ :=
    GenLimit.target_eventually_critical hpresentsBasic
  refine ⟨max Tcritical (z + 1), ?_⟩
  intro t ht
  have htCritical : Tcritical ≤ t :=
    (Nat.le_max_left _ _).trans ht
  have hzt : z < t := by
    omega
  have hsampleCard :
      (GenLimit.Generic.sample stream t).card = t := by
    rw [GenLimit.Bridge.genericSample_eq_basicSample]
    exact
      GenLimit.KM.SetInterface.sample_card_of_injective
        stream hinjective t
  have hzScope : z < (GenLimit.Generic.sample stream t).card := by
    rw [hsampleCard]
    exact hzt
  have hzCritical :
      GenLimit.KM.SetInterface.CriticalOn O.language
        (GenLimit.Generic.sample stream t) z := by
    rw [GenLimit.Bridge.genericSample_eq_basicSample]
    exact hcritical t htCritical
  let i :=
    GenLimit.KM.SetInterface.focus O.language
      (GenLimit.Generic.sample stream t)
  have hfocus :=
    GenLimit.KM.SetInterface.focus_spec hzScope hzCritical
  have hsubset : O.language i ⊆ O.language z := by
    exact
      GenLimit.KM.SetInterface.criticalOn_subset_of_le
        hfocus.2.2 hzCritical hfocus.2.1
  refine ⟨hsubset, ?_⟩
  unfold SetCorrectAt
  rw [noiselessDensityGenerator_output]
  refine ⟨?_, ?_⟩
  · exact fun _ hx => hsubset hx.1
  · rw [Set.disjoint_left]
    exact fun _ hxOutput hxSample => hxOutput.2 hxSample

/-- Lemma 6.8's run-wise correctness conclusion. -/
theorem lemma_6_8_noiseless_generation
    (O : GenLimit.OracleFamily)
    {stream : GenLimit.Generic.Stream ℕ} {z : ℕ}
    (hpresents :
      GenLimit.Generic.Presents stream (O.language z))
    (hinjective : Function.Injective stream) :
    GeneratesInfiniteSetInLimitOn
      (noiselessDensityGenerator O) (O.language z) stream := by
  refine ⟨noiselessDensityGenerator_infinite O, ?_⟩
  obtain ⟨T, hT⟩ :=
    noiselessDensityGenerator_eventually_correct
      O hpresents hinjective
  exact ⟨T, fun t ht => (hT t ht).2⟩

/-- Pointwise late density guarantee used to pass from the critical language
to the set output after deleting the observed sample. -/
theorem lemma_6_8_eventually_lowerDensity
    (O : GenLimit.OracleFamily)
    (orders : ℕ → OrderedLanguage)
    (c : ℝ)
    (hpair :
      ∀ i j,
        (O.language i \ O.language j).Finite →
          c ≤ (orders j).lowerDensity (O.language i))
    {stream : GenLimit.Generic.Stream ℕ} {z : ℕ}
    (hpresents :
      GenLimit.Generic.Presents stream (O.language z))
    (hinjective : Function.Injective stream) :
    ∀ᶠ t : ℕ in atTop,
      c ≤ (orders z).lowerDensity
        (setOutput (noiselessDensityGenerator O) stream t) := by
  obtain ⟨T, hT⟩ :=
    noiselessDensityGenerator_eventually_correct
      O hpresents hinjective
  rw [eventually_atTop]
  refine ⟨T, fun t ht => ?_⟩
  let i :=
    GenLimit.KM.SetInterface.focus O.language
      (GenLimit.Generic.sample stream t)
  have hsubset : O.language i ⊆ O.language z := (hT t ht).1
  have hdiff : (O.language i \ O.language z).Finite := by
    rw [Set.diff_eq_empty.mpr hsubset]
    exact Set.finite_empty
  have hbase : c ≤ (orders z).lowerDensity (O.language i) :=
    hpair i z hdiff
  have hdelete :=
    (orders z).lowerDensity_diff_finite
      (O.language i)
      (GenLimit.Generic.sample stream t).finite_toSet
  rw [noiselessDensityGenerator_output]
  exact hbase.trans_eq hdelete.symm

/-- General measurement form of Lemma 6.8.  Correctness is with respect to
the indexed target language, while density may be measured in a separately
supplied ordered reference.  The finite-expansion reduction in Lemma 6.9
uses this with the original target's canonical order. -/
theorem lemma_6_8_noiseless_setDensity_with_measure
    (O : GenLimit.OracleFamily)
    (measure : ℕ → OrderedLanguage)
    (c : ℝ)
    (hpair :
      ∀ i j,
        (O.language i \ O.language j).Finite →
          c ≤ (measure j).lowerDensity (O.language i))
    {stream : GenLimit.Generic.Stream ℕ} {z : ℕ}
    (hpresents :
      GenLimit.Generic.Presents stream (O.language z))
    (hinjective : Function.Injective stream) :
    GeneratesInfiniteSetInLimitOn
        (noiselessDensityGenerator O) (O.language z) stream ∧
      c ≤ setBasedLowerDensity
        (noiselessDensityGenerator O) (measure z) stream := by
  refine ⟨lemma_6_8_noiseless_generation O hpresents hinjective, ?_⟩
  unfold setBasedLowerDensity
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop
      (fun t => (measure z).lowerDensity_le_one
        (setOutput (noiselessDensityGenerator O) stream t))
  · exact lemma_6_8_eventually_lowerDensity
      O measure c hpair hpresents hinjective

/-- Lemma 6.8: the explicit indexed-family noiseless set generator is
eventually valid and achieves the prescribed set-based lower density on
every exact repetition-free presentation. -/
theorem lemma_6_8_noiseless_setDensity
    (O : GenLimit.OracleFamily)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = O.language i)
    (c : ℝ)
    (hpair :
      ∀ i j,
        (O.language i \ O.language j).Finite →
          c ≤ (orders j).lowerDensity (O.language i))
    {stream : GenLimit.Generic.Stream ℕ} {z : ℕ}
    (hpresents :
      GenLimit.Generic.Presents stream (O.language z))
    (hinjective : Function.Injective stream) :
    GeneratesInfiniteSetInLimitOn
        (noiselessDensityGenerator O) (orders z).carrier stream ∧
      c ≤ setBasedLowerDensity
        (noiselessDensityGenerator O) (orders z) stream := by
  have h :=
    lemma_6_8_noiseless_setDensity_with_measure
      O orders c hpair hpresents hinjective
  rw [hcarrier z]
  exact h

end GenLimit.InfiniteContamination
