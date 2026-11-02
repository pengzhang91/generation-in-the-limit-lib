import GenLimit.Paper21_GenerationInMetricSpaces.NonuniformCharacterization
import GenLimit.Support.CountableCovers

/-!
# Finite and countable class corollaries in metric spaces

Corollaries 3.2 and 3.4 of Li--Raman--Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v2.
A finite family has only finitely many version-space cores. The finite
union of chosen covers bounds the sample covering numbers of all internal
closure witnesses. Finite prefixes of an ambient enumeration, intersected
with the target class, then handle every countable class, including empty
and finite classes. The generator's empty-input output requires `[Nonempty α]`.
-/

namespace GenLimit.MetricSpaces

private noncomputable def chosenFiniteCoverCenters
    (ρ : Distance α) (r : ℝ) (A : Set α) : Finset α := by
  classical
  exact if h : HasFiniteCover ρ r A then Classical.choose h else ∅

private theorem chosenFiniteCoverCenters_spec
    {ρ : Distance α} {r : ℝ} {A : Set α}
    (h : HasFiniteCover ρ r A) :
    A ⊆ closedNeighborhood ρ
      (chosenFiniteCoverCenters ρ r A : Set α) r := by
  classical
  simp only [chosenFiniteCoverCenters, dif_pos h]
  exact Classical.choose_spec h

/-- The finite-core combinatorial argument for Corollary 3.2.

Only an upper bound over the finitely many cores is needed.
The result is stronger than the paper-facing corollary: it assumes neither
UUS nor positive scales nor any metric laws, only the scale order
`ε' ≤ ε` used to enlarge the chosen covers. -/
theorem finite_languageClass_has_finite_scaleClosureDimension
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hFinite : H.Finite) (hε'ε : ε' ≤ ε) :
    HasFiniteScaleClosureDimension ρ ε ε' H := by
  classical
  let cores : Finset (GenLimit.Generic.Language α) :=
    GenLimit.Generic.subclassCores H hFinite
  let allCenters : Finset α :=
    cores.biUnion fun C ↦ chosenFiniteCoverCenters ρ ε' C
  refine ⟨allCenters.card, ?_⟩
  intro d hlarge
  rintro ⟨S, _hversion, hcoverEq, hcoreCover⟩
  have hcoreMem : commonCore H S ∈ cores := by
    exact GenLimit.Generic.commonCore_mem_subclassCores hFinite S
  have hchosenSubset :
      (chosenFiniteCoverCenters ρ ε' (commonCore H S) : Set α) ⊆
        (allCenters : Set α) := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨commonCore H S, hcoreMem, hx⟩
  have hsampleCore :
      (S : Set α) ⊆ commonCore H S :=
    GenLimit.Generic.sample_subset_commonCore
  have hcoreChosen :
      commonCore H S ⊆
        closedNeighborhood ρ
          (chosenFiniteCoverCenters ρ ε' (commonCore H S) : Set α) ε' :=
    chosenFiniteCoverCenters_spec hcoreCover.toFiniteCover
  have hsampleAll :
      (S : Set α) ⊆
        closedNeighborhood ρ (allCenters : Set α) ε := by
    exact hsampleCore.trans
      (hcoreChosen.trans
        ((inClosedNeighborhood_mono_radius hε'ε).trans
          (inClosedNeighborhood_mono_centers hchosenSubset)))
  have hdBound : d ≤ allCenters.card :=
    hcoverEq.1 allCenters hsampleAll
  exact (Nat.not_le_of_gt hlarge) hdBound

/-- Every finite class is uniformly generatable at ordered scales.

This is the strongest direct helper used by Corollary 3.2.  Positivity of
`ε` is relaxed to nonnegativity, while UUS and the upper bounds by `r` are
not needed by the valid sufficiency proof. -/
theorem finite_languageClass_uniformlyGeneratable_of_le
    [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x : α, ρ x x = 0)
    (hε : 0 ≤ ε)
    (hε'ε : ε' ≤ ε)
    (hFinite : H.Finite) :
    UniformlyGeneratableAt ρ ε ε' H :=
  finite_scaleClosureDimension_implies_uniform hrefl hε
    (finite_languageClass_has_finite_scaleClosureDimension
      hFinite hε'ε)

/-- Corollary 3.2, with all printed scalar and class hypotheses retained.

The `r`-UUS premise and the two upper scale bounds are intentionally present
in this source-facing wrapper even though the corrected upper-bound proof
does not use them.  `[Nonempty α]` makes the generation model's implicit
inhabited-example-space convention explicit. -/
theorem corollary_3_2
    [Nonempty α]
    {ρ : Distance α} {r ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x : α, ρ x x = 0)
    (_hr : 0 < r)
    (_hUUS : UniformlyUnboundedSupportAt ρ r H)
    (hε : 0 < ε) (_hε' : 0 < ε')
    (_hεr : ε ≤ r) (_hε'r : ε' ≤ r)
    (hε'ε : ε' ≤ ε)
    (hFinite : H.Finite) :
    UniformlyGeneratableAt ρ ε ε' H := by
  exact
    finite_languageClass_uniformlyGeneratable_of_le
      hrefl hε.le hε'ε hFinite

/-- Every countable class is non-uniformly generatable at ordered scales.

This stronger helper covers empty, finite, and countably infinite classes.
It uses finite prefixes of an ambient enumeration, intersected back with
`H`, so it does not assume an exact infinite enumeration of `H`. -/
theorem countable_languageClass_nonuniformlyGeneratable_of_le
    [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x : α, ρ x x = 0)
    (hε : 0 ≤ ε)
    (hε'ε : ε' ≤ ε)
    (hCountable : H.Countable) :
    NonuniformlyGeneratableAt ρ ε ε' H := by
  classical
  obtain ⟨enumerate, hEnumerates⟩ :=
    Set.countable_iff_exists_subset_range.mp hCountable
  let classes : ℕ → GenLimit.Generic.LanguageClass α :=
    GenLimit.Support.finitePrefixSubclass H enumerate
  apply
    nondecreasing_uniform_cover_implies_nonuniform
      (classes := classes)
      (fun x ↦ by rw [hrefl x]; exact hε)
  · exact
      GenLimit.Support.finitePrefixSubclass_isNondecreasingCover
        H enumerate hEnumerates
  · intro n
    apply finite_languageClass_uniformlyGeneratable_of_le
      hrefl hε hε'ε
    exact GenLimit.Support.finitePrefixSubclass_finite H enumerate n

/-- Corollary 3.4, with the paper's positive scales, scale bounds, and UUS
premise retained exactly.  `[Nonempty α]` records the generator interface's
implicit inhabited-example-space convention. -/
theorem corollary_3_4
    [Nonempty α]
    {ρ : Distance α} {r ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x : α, ρ x x = 0)
    (_hr : 0 < r)
    (_hUUS : UniformlyUnboundedSupportAt ρ r H)
    (hε : 0 < ε) (_hε' : 0 < ε')
    (_hεr : ε ≤ r) (_hε'r : ε' ≤ r)
    (hε'ε : ε' ≤ ε)
    (hCountable : H.Countable) :
    NonuniformlyGeneratableAt ρ ε ε' H := by
  exact
    countable_languageClass_nonuniformlyGeneratable_of_le
      hrefl hε.le hε'ε hCountable

end GenLimit.MetricSpaces
