import GenLimit.Paper17_InfiniteContamination.SetDensityObstruction

/-!
# Finite-expansion transfer under finite contamination

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Algorithm 2 and Lemma 4.3, as used in the
sufficiency proof of Lemma 6.9.

Algorithm 2 replaces each language `L` by all finite expansions
`(L ∪ add) \ remove`, where `add` consists of finitely many points outside
`L` and `remove` of finitely many points inside `L`.  A finite-noise,
finite-omission stream is an exact noiseless presentation of one such
expansion.  Once its finitely many added points have appeared in the sample,
the freshness rule prevents either an element generator or a set generator
from emitting them again.  Correct generation for the expanded target
therefore transfers back to the original target.

This module formalizes that deterministic reduction.  It does not postulate
the noiseless positive-density generator used as a black box in Lemma 6.8;
constructing and analyzing that generator is the next, substantially more
stateful part of Lemma 6.9.
-/

namespace GenLimit.InfiniteContamination

/-- Algorithm 2's finite expansion `(L ∪ add) \ remove`. -/
def finiteExpansion
    (L add remove : GenLimit.Generic.Language α) :
    GenLimit.Generic.Language α :=
  (L ∪ add) \ remove

/-- Exact semantic witness that `expanded` is one of Algorithm 2's finite
expansions of `L`. -/
structure FiniteExpansionWitness
    (L expanded : GenLimit.Generic.Language α) where
  add : Set α
  remove : Set α
  add_finite : add.Finite
  remove_finite : remove.Finite
  add_outside : add ⊆ Lᶜ
  remove_inside : remove ⊆ L
  expansion_eq : finiteExpansion L add remove = expanded

/-- The values actually displayed outside the target. -/
def displayedNoise
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Set α :=
  Set.range stream \ L

/-- The target values omitted by the stream. -/
def displayedOmissions
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Set α :=
  L \ Set.range stream

theorem displayedNoise_eq_image_badTimes
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) :
    displayedNoise stream L =
      stream '' {t | stream t ∉ L} := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, hnot⟩
    exact ⟨t, hnot, rfl⟩
  · rintro ⟨t, hnot, rfl⟩
    exact ⟨⟨t, rfl⟩, hnot⟩

theorem displayedNoise_finite
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hnoise : FiniteNoise stream L) :
    (displayedNoise stream L).Finite := by
  rw [displayedNoise_eq_image_badTimes]
  exact hnoise.image stream

theorem finiteExpansion_displayedNoise_displayedOmissions
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) :
    finiteExpansion L
        (displayedNoise stream L)
        (displayedOmissions stream L) =
      Set.range stream := by
  ext x
  simp only [finiteExpansion, displayedNoise, displayedOmissions,
    Set.mem_diff, Set.mem_union, Set.mem_range]
  tauto

/-- A finite-noise, finite-omission stream is an exact presentation of a
member of Algorithm 2's expanded collection. -/
def finiteContamination_expansionWitness
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hcontam :
      FiniteNoiseFiniteOmissionEnumeration stream L) :
    FiniteExpansionWitness L (Set.range stream) where
  add := displayedNoise stream L
  remove := displayedOmissions stream L
  add_finite := displayedNoise_finite hcontam.2.1
  remove_finite := hcontam.2.2
  add_outside := by
    intro x hx
    exact hx.2
  remove_inside := by
    intro x hx
    exact hx.1
  expansion_eq :=
    finiteExpansion_displayedNoise_displayedOmissions stream L

theorem stream_presents_range
    (stream : GenLimit.Generic.Stream α) :
    GenLimit.Generic.Presents stream (Set.range stream) :=
  rfl

/-! ## Lemma 4.3's freshness transfer -/

/-- Element form of the deterministic core of Lemma 4.3.

Every extraneous point of `expanded` eventually belongs to the observed
sample.  The literal freshness conjunct then rules it out forever. -/
theorem generatesElementInLimitOn_of_finite_extraneous
    {gen : GenLimit.Generic.Generator α}
    {stream : GenLimit.Generic.Stream α}
    {L expanded : GenLimit.Generic.Language α}
    (hpresents : GenLimit.Generic.Presents stream expanded)
    (hextraneous : (expanded \ L).Finite)
    (hgenerate :
      GeneratesElementInLimitOn gen expanded stream) :
    GeneratesElementInLimitOn gen L stream := by
  classical
  obtain ⟨Tgenerate, hTgenerate⟩ := hgenerate
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hpresents hextraneous.toFinset (by
        intro x hx
        exact
          ((Set.Finite.mem_toFinset hextraneous).mp hx).1)
  refine ⟨max Tgenerate Tseen, ?_⟩
  intro t ht
  have htGenerate : Tgenerate ≤ t :=
    (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t :=
    (Nat.le_max_right _ _).trans ht
  have hcorrect := hTgenerate t htGenerate
  have hseen :
      hextraneous.toFinset ⊆
        GenLimit.Generic.sample stream t := by
    intro x hx
    exact
      GenLimit.Generic.sample_mono htSeen (hTseen hx)
  refine ⟨?_, hcorrect.2.1, hcorrect.2.2⟩
  by_contra houtside
  have hbad :
      GenLimit.Generic.output gen stream t ∈
        hextraneous.toFinset :=
    (Set.Finite.mem_toFinset hextraneous).mpr
      ⟨hcorrect.1, houtside⟩
  exact hcorrect.2.1 (hseen hbad)

/-- Set-output form of Lemma 4.3.  Disjointness from the observed sample
removes every point in the finite difference `expanded \ L`. -/
theorem generatesSetInLimitOn_of_finite_extraneous
    {gen : SetGenerator α}
    {stream : GenLimit.Generic.Stream α}
    {L expanded : GenLimit.Generic.Language α}
    (hpresents : GenLimit.Generic.Presents stream expanded)
    (hextraneous : (expanded \ L).Finite)
    (hgenerate :
      GeneratesSetInLimitOn gen expanded stream) :
    GeneratesSetInLimitOn gen L stream := by
  classical
  obtain ⟨Tgenerate, hTgenerate⟩ := hgenerate
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hpresents hextraneous.toFinset (by
        intro x hx
        exact
          ((Set.Finite.mem_toFinset hextraneous).mp hx).1)
  refine ⟨max Tgenerate Tseen, ?_⟩
  intro t ht
  have htGenerate : Tgenerate ≤ t :=
    (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t :=
    (Nat.le_max_right _ _).trans ht
  have hcorrect := hTgenerate t htGenerate
  have hseen :
      hextraneous.toFinset ⊆
        GenLimit.Generic.sample stream t := by
    intro x hx
    exact
      GenLimit.Generic.sample_mono htSeen (hTseen hx)
  refine ⟨?_, hcorrect.2⟩
  intro x hxOutput
  have hxExpanded : x ∈ expanded := hcorrect.1 hxOutput
  by_contra hxL
  have hxBad : x ∈ hextraneous.toFinset :=
    (Set.Finite.mem_toFinset hextraneous).mpr
      ⟨hxExpanded, hxL⟩
  exact
    Set.disjoint_left.mp hcorrect.2
      hxOutput (hseen hxBad)

/-- Infinite-output form of Lemma 4.3.  The weak correctness transfer removes
the finitely many extraneous points, while infinitude is preserved because
the generator's output set itself is unchanged. -/
theorem generatesInfiniteSetInLimitOn_of_finite_extraneous
    {gen : SetGenerator α}
    {stream : GenLimit.Generic.Stream α}
    {L expanded : GenLimit.Generic.Language α}
    (hpresents : GenLimit.Generic.Presents stream expanded)
    (hextraneous : (expanded \ L).Finite)
    (hgenerate :
      GeneratesInfiniteSetInLimitOn gen expanded stream) :
    GeneratesInfiniteSetInLimitOn gen L stream := by
  exact ⟨hgenerate.1,
    generatesSetInLimitOn_of_finite_extraneous
      hpresents hextraneous hgenerate.generatesSetInLimitOn⟩

/-- Lemma 4.3, element-generator branch, specialized to the exact expanded
target represented by a finite-contamination stream. -/
theorem lemma_4_3_element_finiteExpansion_transfer
    {gen : GenLimit.Generic.Generator α}
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hcontam :
      FiniteNoiseFiniteOmissionEnumeration stream L)
    (hgenerateExpanded :
      GeneratesElementInLimitOn gen (Set.range stream) stream) :
    GeneratesElementInLimitOn gen L stream := by
  apply generatesElementInLimitOn_of_finite_extraneous
      (stream_presents_range stream)
      (displayedNoise_finite hcontam.2.1)
  exact hgenerateExpanded

/-- Lemma 4.3, set-generator branch, specialized to the exact expanded
target represented by a finite-contamination stream. -/
theorem lemma_4_3_set_finiteExpansion_transfer
    {gen : SetGenerator α}
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hcontam :
      FiniteNoiseFiniteOmissionEnumeration stream L)
    (hgenerateExpanded :
      GeneratesSetInLimitOn gen (Set.range stream) stream) :
    GeneratesSetInLimitOn gen L stream := by
  apply generatesSetInLimitOn_of_finite_extraneous
      (stream_presents_range stream)
      (displayedNoise_finite hcontam.2.1)
  exact hgenerateExpanded

/-- Lemma 4.3 specialized to source-faithful infinite set outputs. -/
theorem lemma_4_3_infiniteSet_finiteExpansion_transfer
    {gen : SetGenerator α}
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hcontam :
      FiniteNoiseFiniteOmissionEnumeration stream L)
    (hgenerateExpanded :
      GeneratesInfiniteSetInLimitOn
        gen (Set.range stream) stream) :
    GeneratesInfiniteSetInLimitOn gen L stream := by
  apply generatesInfiniteSetInLimitOn_of_finite_extraneous
      (stream_presents_range stream)
      (displayedNoise_finite hcontam.2.1)
  exact hgenerateExpanded

/-! ## The finite-difference algebra used in Lemma 6.9 -/

theorem finiteExpansion_diff_base_subset
    {L L' add remove add' remove' :
      GenLimit.Generic.Language α} :
    L \ L' ⊆
      (finiteExpansion L add remove \
          finiteExpansion L' add' remove') ∪
        add' ∪ remove := by
  intro x hx
  by_cases hxRemove : x ∈ remove
  · exact Or.inr hxRemove
  by_cases hxAdd' : x ∈ add'
  · exact Or.inl (Or.inr hxAdd')
  · exact Or.inl (Or.inl
      ⟨⟨Or.inl hx.1, hxRemove⟩,
        fun hxExpanded' => hx.2 (hxExpanded'.1.resolve_right hxAdd')⟩)

/-- Algebraic step in the density proof of Lemma 6.9: if two finite
expansions have finite asymmetric difference, then their two base languages
already have finite asymmetric difference. -/
theorem finite_base_diff_of_finite_expansion_diff
    {L L' add remove add' remove' :
      GenLimit.Generic.Language α}
    (hadd' : add'.Finite)
    (hremove : remove.Finite)
    (hexpanded :
      (finiteExpansion L add remove \
        finiteExpansion L' add' remove').Finite) :
    (L \ L').Finite := by
  apply
    ((hexpanded.union hadd').union hremove).subset
  intro x hx
  exact
    finiteExpansion_diff_base_subset
      (L := L) (L' := L') (add := add) (remove := remove)
      (add' := add') (remove' := remove') hx

/-- Witness-level form of Lemma 6.9's finite-difference inheritance. -/
theorem FiniteExpansionWitness.base_diff_finite
    {L L' expanded expanded' :
      GenLimit.Generic.Language α}
    (h : FiniteExpansionWitness L expanded)
    (h' : FiniteExpansionWitness L' expanded')
    (hdiff : (expanded \ expanded').Finite) :
    (L \ L').Finite := by
  rw [← h.expansion_eq, ← h'.expansion_eq] at hdiff
  exact
    finite_base_diff_of_finite_expansion_diff
      h'.add_finite h.remove_finite hdiff

end GenLimit.InfiniteContamination
