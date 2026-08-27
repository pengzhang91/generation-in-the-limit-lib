import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.DynamicComponent

/-!
# Kleinberg--Wei Claims 6.7--6.9

This file formalizes the eventual target-ancestry argument in Section 6 of
Kleinberg and Wei's *Density Measures for Language Generation*.

The printed proof of Claim 6.7 invokes a time-varying perfect-tower argument
without establishing its nonredundancy.  Here the claim follows directly from
the finite basic neighborhood isolating a target at its Cantor--Bendixson
level.  Claim 6.8 then climbs the parent forest by strict level increase,
covering both the finite-minimum and infinite-chain parent cases.
-/

namespace GenLimit
namespace KleinbergWei
namespace DensityMeasures

open TowerTopology

namespace FiniteRankParent

/-- A finite basic neighborhood isolates every level-`i` point inside the
`i`-th Cantor--Bendixson derivative. -/
theorem exists_isolating_finset_of_mem_cbLevel
    {X : Set Language} {i : ℕ} {K : Point X}
    (hK : K ∈ cbLevel X i) :
    ∃ F : Finset ℕ,
      (↑F : Set ℕ) ⊆ K.1 ∧
        ∀ L : Point X,
          L ∈ cbDerivative X i →
            L ∈ basicNeighborhood X K F →
              L = K := by
  classical
  by_contra hnone
  push_neg at hnone
  apply hK.2
  rw [cbDerivative_succ]
  refine ⟨hK.1, ?_⟩
  intro F hFK
  obtain ⟨L, hLi, hLF, hne⟩ := hnone F hFK
  exact ⟨L, hLi, hne, hLF⟩

/-- Strong purge form of Claim 6.7: after one finite round, no remaining
proper sublanguage of the target can lie at the target's level or above. -/
theorem claim_6_7_eventual_purge
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z : ℕ}
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (hP : Presents stream (C z)) :
    ∃ T, ∀ round, T ≤ round →
      ∀ L : FamilyPoint C,
        L.1 ⊂ C z →
          levelOf hr (familyPoint C z) ≤ levelOf hr L →
            ¬ RemainingAt C stream round L := by
  let K := familyPoint C z
  have hKlevel :
      K ∈ cbLevel (FamilySpace C) (levelOf hr K) :=
    mem_cbLevel_levelOf hr K
  obtain ⟨F, hFK, hisolate⟩ :=
    exists_isolating_finset_of_mem_cbLevel hKlevel
  obtain ⟨T, hT⟩ :=
    finite_eventually_subset_sample hP F hFK
  refine ⟨T, ?_⟩
  intro round hround L hLK hlevel hremaining
  have hFsample :
      (↑F : Set ℕ) ⊆ sample stream (round + 1) := by
    intro u hu
    exact hT (round + 1) (by omega) hu
  have hFsubL : (↑F : Set ℕ) ⊆ L.1 :=
    hFsample.trans hremaining
  have hLderivative :
      L ∈ cbDerivative (FamilySpace C) (levelOf hr K) := by
    apply
      (cbDerivative_antitone (FamilySpace C) hlevel)
    exact (mem_cbLevel_levelOf hr L).1
  have hLneighborhood :
      L ∈ basicNeighborhood (FamilySpace C) K F :=
    ⟨hFsubL, hLK.le⟩
  have hLKpoint : L = K :=
    hisolate L hLderivative hLneighborhood
  exact hLK.ne (congrArg Subtype.val hLKpoint)

/-- Claim 6.7.  The conclusion is stated for every remaining child, hence in
particular for the language identified by the accurate selector. -/
theorem claim_6_7
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z : ℕ}
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (hP : Presents stream (C z)) :
    ∃ T, ∀ round, T ≤ round →
      ∀ child ancestor : RemainingPoint C stream round,
        ancestor.1.1 ⊂ C z →
          levelOf hr (familyPoint C z) ≤ levelOf hr ancestor.1 →
            ¬ AncestorAt C stream r hr round child ancestor := by
  obtain ⟨T, hpurge⟩ := claim_6_7_eventual_purge hr hP
  refine ⟨T, ?_⟩
  intro round hround child ancestor hproper hlevel _
  exact
    hpurge round hround ancestor.1 hproper hlevel
      ancestor.2

/-- Once the round has passed the target's family index, any selected parent
of a proper sublanguage below the target level remains a sublanguage of the
target.  The generic parent-selection lemma covers both the finite-minimum
and infinite-chain branches. -/
theorem selected_parent_subset_target
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z round : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {child parent : RemainingPoint C stream round}
    (hcritical : StrictCritical C stream (round + 1) z)
    (hzround : z < round)
    (hproper : child.1.1 ⊂ C z)
    (hlevel :
      levelOf hr child.1 < levelOf hr (familyPoint C z))
    (hEdge : EdgeAt C stream r hr round child parent) :
    parent.1.1 ⊆ C z := by
  have htargetCandidate :
      ParentCandidate C stream r hr round child z :=
    ⟨hcritical, hproper, hlevel⟩
  obtain ⟨chosen, hChosenEdge, hChosenSubset⟩ :=
    exists_parent_edge_subset_candidate
      hzround.le htargetCandidate
  have hEq : parent = chosen :=
    edge_outdegree_at_most_one hEdge hChosenEdge
  simpa [hEq] using hChosenSubset

/-- The exactly presented target is a remaining forest vertex at every
round. -/
def targetRemainingPoint
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) (round : ℕ) :
    RemainingPoint C stream round :=
  ⟨familyPoint C z, fun _ hu =>
    mem_language_of_mem_sample_of_presents hP hu⟩

@[simp] theorem targetRemainingPoint_val
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) (round : ℕ) :
    (targetRemainingPoint hP round).1 = familyPoint C z :=
  rfl

/-- At a fixed post-purge round, every remaining proper sublanguage below
the target level has the target as an ancestor. -/
theorem reaches_target_at_stable_round
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z round : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    (hP : Presents stream (C z))
    (hcritical : StrictCritical C stream (round + 1) z)
    (hzround : z < round)
    (hpurge :
      ∀ L : FamilyPoint C,
        L.1 ⊂ C z →
          levelOf hr (familyPoint C z) ≤ levelOf hr L →
            ¬ RemainingAt C stream round L)
    (child : RemainingPoint C stream round)
    (hchildProper : child.1.1 ⊂ C z)
    (hchildLevel :
      levelOf hr child.1 < levelOf hr (familyPoint C z)) :
    Relation.TransGen (EdgeAt C stream r hr round)
      child (targetRemainingPoint hP round) := by
  let rec ascend
      (current : RemainingPoint C stream round)
      (hcurrentProper : current.1.1 ⊂ C z)
      (hcurrentLevel :
        levelOf hr current.1 <
          levelOf hr (familyPoint C z)) :
      Relation.TransGen (EdgeAt C stream r hr round)
        current (targetRemainingPoint hP round) := by
    have htargetCandidate :
        ParentCandidate C stream r hr round current z :=
      ⟨hcritical, hcurrentProper, hcurrentLevel⟩
    obtain ⟨n, hn⟩ :=
      parentIndexAt_exists_of_candidate htargetCandidate
    have hnCandidate := parentIndexAt_spec hn
    have hparentRemaining :
        RemainingAt C stream round (familyPoint C n) :=
      hnCandidate.1.1
    let parent : RemainingPoint C stream round :=
      ⟨familyPoint C n, hparentRemaining⟩
    have hEdge :
        EdgeAt C stream r hr round current parent := by
      simp [EdgeAt, parentAt, parent, hn]
    have hparentSubset : parent.1.1 ⊆ C z :=
      selected_parent_subset_target
        hcritical hzround hcurrentProper hcurrentLevel hEdge
    by_cases hparentEq : parent.1.1 = C z
    · have hparentTarget :
          parent = targetRemainingPoint hP round := by
        apply Subtype.ext
        apply Subtype.ext
        exact hparentEq
      rw [← hparentTarget]
      exact Relation.TransGen.single hEdge
    · have hparentProper : parent.1.1 ⊂ C z :=
        Set.ssubset_iff_subset_ne.mpr
          ⟨hparentSubset, hparentEq⟩
      have hparentLevel :
          levelOf hr parent.1 <
            levelOf hr (familyPoint C z) := by
        by_contra hnot
        have htargetLe :
            levelOf hr (familyPoint C z) ≤
              levelOf hr parent.1 :=
          Nat.le_of_not_gt hnot
        exact
          hpurge parent.1 hparentProper htargetLe parent.2
      have hlevelStep :
          levelOf hr current.1 < levelOf hr parent.1 :=
        (edge_strict_level_and_inclusion hEdge).1
      exact
        Relation.TransGen.head hEdge
          (ascend parent hparentProper hparentLevel)
    termination_by
      levelOf hr (familyPoint C z) - levelOf hr current.1
    decreasing_by
      exact Nat.sub_lt_sub_left hcurrentLevel hlevelStep
  exact ascend child hchildProper hchildLevel

/-- The selector's canonical remaining vertex after source round `t+1`. -/
def identifiedRemainingPoint
    {C : LanguageFamily} {stream : ℕ → ℕ} {t z : ℕ}
    (hzt : z ≤ t)
    (hz : StrictCritical C stream t z)
    (hstream : stream t ∈ C z) :
    RemainingPoint C stream t :=
  ⟨identifiedPointAt C stream t,
    identifiedPointAt_remaining_of_stable_target
      hzt hz hstream⟩

@[simp] theorem identifiedRemainingPoint_val
    {C : LanguageFamily} {stream : ℕ → ℕ} {t z : ℕ}
    (hzt : z ≤ t)
    (hz : StrictCritical C stream t z)
    (hstream : stream t ∈ C z) :
    (identifiedRemainingPoint hzt hz hstream).1 =
      familyPoint C (guessIndex C stream (t + 1)) :=
  rfl

/-- Claim 6.8: after a finite round, the true language is an ancestor
(allowing equality) of the language identified by the accurate selector. -/
theorem claim_6_8
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z : ℕ}
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∃ T, ∀ t, T ≤ t →
      ∃ identified : RemainingPoint C stream t,
        identified.1 =
            familyPoint C (guessIndex C stream (t + 1)) ∧
          AncestorAt C stream r hr t
            identified (targetRemainingPoint hP t) := by
  obtain ⟨Tcritical, hcritical⟩ :=
    lemma_3_3 hP hfirst
  obtain ⟨Tpurge, hpurge⟩ :=
    claim_6_7_eventual_purge hr hP
  obtain ⟨Tvalid, hvalid⟩ :=
    proposition_3_4 hP hfirst
  refine
    ⟨max Tcritical (max Tpurge (max Tvalid (z + 1))), ?_⟩
  intro t ht
  have hTcritical : Tcritical ≤ t := by
    omega
  have hTpurge : Tpurge ≤ t := by
    omega
  have hTvalid : Tvalid ≤ t + 1 := by
    omega
  have hzt : z ≤ t := by
    omega
  have hztStrict : z < t := by
    omega
  have hzNow : StrictCritical C stream t z :=
    hcritical t hTcritical
  have hzNext : StrictCritical C stream (t + 1) z :=
    hcritical (t + 1) (by omega)
  have hstream : stream t ∈ C z := by
    rw [← hP]
    exact ⟨t, rfl⟩
  let identified : RemainingPoint C stream t :=
    identifiedRemainingPoint hzt hzNow hstream
  refine ⟨identified, rfl, ?_⟩
  have hidentifiedSubset : identified.1.1 ⊆ C z := by
    simpa [identified] using hvalid (t + 1) hTvalid
  by_cases heq : identified.1.1 = C z
  · have hpoint :
        identified = targetRemainingPoint hP t := by
      apply Subtype.ext
      apply Subtype.ext
      exact heq
    rw [hpoint]
  ·
    have hproper : identified.1.1 ⊂ C z :=
      Set.ssubset_iff_subset_ne.mpr
        ⟨hidentifiedSubset, heq⟩
    have hlevel :
        levelOf hr identified.1 <
          levelOf hr (familyPoint C z) := by
      by_contra hnot
      have htargetLe :
          levelOf hr (familyPoint C z) ≤
            levelOf hr identified.1 :=
        Nat.le_of_not_gt hnot
      exact
        hpurge t hTpurge identified.1
          hproper htargetLe identified.2
    exact (
      reaches_target_at_stable_round
        hP hzNext hztStrict
        (hpurge t hTpurge) identified hproper hlevel).to_reflTransGen

/-- Corollary 6.9: at two consecutive stable rounds, both selector outputs
have the target as an ancestor in their respective dynamic forests. -/
theorem corollary_6_9
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z : ℕ}
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∃ T, ∀ t, T ≤ t →
      (∃ identified : RemainingPoint C stream t,
        identified.1 =
            familyPoint C (guessIndex C stream (t + 1)) ∧
          AncestorAt C stream r hr t
            identified (targetRemainingPoint hP t)) ∧
      (∃ identified : RemainingPoint C stream (t + 1),
        identified.1 =
            familyPoint C (guessIndex C stream (t + 2)) ∧
          AncestorAt C stream r hr (t + 1)
            identified (targetRemainingPoint hP (t + 1))) := by
  obtain ⟨T, hT⟩ := claim_6_8 hr hP hfirst
  refine ⟨T, ?_⟩
  intro t ht
  exact ⟨hT t ht, hT (t + 1) (by omega)⟩

end FiniteRankParent

end DensityMeasures
end KleinbergWei
end GenLimit
