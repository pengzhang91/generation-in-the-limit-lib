import GenLimit.Paper09_RepresentativeLanguageGeneration.FiniteSupport

/-!
# Representative generation: counterexample to the finite-support claim

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Definitions 4.1--4.2, Lemma 4.8, and Theorem 4.4.

The published Lemma 4.8 and Theorem 4.4 are false for overlapping countably many
groups.  This module kernel-checks the counterexample:

* `X = ℕ`;
* the singleton class whose only language is `ℕ`;
* `A_n = {m | n ≤ m}`.

Every finite intersection counted by Definition 4.1 is empty (every nonempty
intersection is an infinite tail), so the finite-support size is zero.  Along
the enumeration `0,1,2,...`, however, all unseen values at history length `t`
lie in `A_t`.  Consistency therefore forces group mass one on `A_t`, while its
empirical mass is zero.  The representation error is at least one at every
positive time.
-/

namespace GenLimit.RepresentativeGeneration

/-- The nested tail groups `A_n`. -/
def tailGroups (n : ℕ) : Set ℕ :=
  {m | n ≤ m}

def tailLanguage : GenLimit.Generic.Language ℕ := Set.univ

def tailClass : GenLimit.Generic.LanguageClass ℕ := {tailLanguage}

def identityEnumeration : GenLimit.Generic.Stream ℕ := fun n => n

theorem tailGroups_cover : GroupsCover tailGroups := by
  apply Set.eq_univ_of_forall
  intro x
  apply Set.mem_iUnion.mpr
  exact ⟨0, by simp [tailGroups]⟩

theorem tailClass_countable : tailClass.Countable := by
  simp [tailClass]

theorem tailClass_UUS : GenLimit.Generic.UUS tailClass := by
  intro L hL
  have hLuniv : L = Set.univ := by
    simpa [tailClass, tailLanguage] using hL
  rw [hLuniv]
  exact Set.infinite_univ

theorem tail_indexedIntersection_finite_eq_empty
    (I : Set ℕ)
    (hfinite :
      (indexedGroupIntersection tailLanguage tailGroups I).Finite) :
    indexedGroupIntersection tailLanguage tailGroups I = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let f : ℕ → ℕ := fun n => x + n
  have hfinj : Function.Injective f := by
    intro a b hab
    exact Nat.add_left_cancel hab
  have hrangeInfinite : (Set.range f).Infinite :=
    Set.infinite_range_of_injective hfinj
  have hrangeSubset :
      Set.range f ⊆ indexedGroupIntersection tailLanguage tailGroups I := by
    rintro y ⟨n, rfl⟩
    refine ⟨by simp [tailLanguage], ?_⟩
    intro i hi
    have hix : i ≤ x := by
      exact hx.2 i hi
    show i ≤ x + n
    omega
  exact hrangeInfinite (hfinite.subset hrangeSubset)

theorem tail_finiteIntersectionContribution_zero (I : Set ℕ) :
    finiteIntersectionContribution tailLanguage tailGroups I = 0 := by
  classical
  unfold finiteIntersectionContribution
  dsimp only
  split
  · rename_i hfinite
    have hempty := tail_indexedIntersection_finite_eq_empty I hfinite
    have hcard :
        hfinite.toFinset.card = 0 := by
      have hfinset : hfinite.toFinset = ∅ := by
        ext x
        simp [hempty]
      simp [hfinset]
    simp [hcard]
  · rfl

theorem tail_finiteSupportSize_zero :
    finiteSupportSize tailLanguage tailGroups = 0 := by
  simp [finiteSupportSize, tail_finiteIntersectionContribution_zero]

theorem tailClass_hasFiniteSupport :
    HasFiniteSupport tailClass tailGroups := by
  intro L hL
  have hLuniv : L = tailLanguage := by
    simpa [tailClass] using hL
  subst L
  rw [tail_finiteSupportSize_zero]
  exact ENNReal.zero_lt_top

theorem sample_identityEnumeration (t : ℕ) :
    GenLimit.Generic.sample identityEnumeration t = Finset.range t := by
  classical
  ext x
  rw [GenLimit.Generic.mem_sample_iff, Finset.mem_range]
  constructor
  · rintro ⟨s, hs, h⟩
    simpa [identityEnumeration] using h ▸ hs
  · intro hx
    exact ⟨x, hx, by simp [identityEnumeration]⟩

theorem unseen_identity_eq_tail (t : ℕ) :
    tailLanguage \
        (↑(GenLimit.Generic.sample identityEnumeration t) : Set ℕ) =
      tailGroups t := by
  ext x
  rw [sample_identityEnumeration]
  simp [tailLanguage, tailGroups]

theorem empirical_identity_tail_zero (t : ℕ) (ht : 0 < t) :
    empiricalGroupProbability
        (GenLimit.Generic.sample identityEnumeration t) tailGroups t = 0 := by
  classical
  have hnonempty : (Finset.range t).Nonempty :=
    ⟨0, Finset.mem_range.mpr ht⟩
  have hfilter :
      (Finset.range t).filter (fun x => x ∈ tailGroups t) = ∅ := by
    ext x
    simp [tailGroups]
  rw [sample_identityEnumeration]
  simp [empiricalGroupProbability, hnonempty, hfilter]

/-- The pointwise contradiction behind the failure of published Lemma 4.8. -/
theorem distance_one_le_of_consistent_identity
    {gen : RandomizedGenerator ℕ} {t : ℕ} (ht : 0 < t)
    (hconsistent :
      IsConsistentAt gen tailLanguage identityEnumeration t) :
    (1 : ENNReal) ≤
      groupSupDistance
        (distributionAt gen identityEnumeration t)
        (GenLimit.Generic.sample identityEnumeration t) tailGroups := by
  have hmass :
      inducedGroupProbability
          (distributionAt gen identityEnumeration t) tailGroups t = 1 := by
    change groupMass (distributionAt gen identityEnumeration t)
      (tailGroups t) = 1
    rw [← unseen_identity_eq_tail t]
    exact hconsistent
  have hemp := empirical_identity_tail_zero t ht
  have hcoord :=
    coordinate_le_groupSupDistance
      (distributionAt gen identityEnumeration t)
      (GenLimit.Generic.sample identityEnumeration t) tailGroups t
  rw [hmass, hemp] at hcoord
  norm_num at hcoord ⊢
  exact hcoord

theorem no_eventually_consistent_alpha_representative
    {alpha : ℝ} (halpha : alpha < 1)
    (gen : RandomizedGenerator ℕ)
    (hrep : IsAlphaRepresentative gen tailGroups alpha)
    (T : ℕ)
    (hconsistent :
      IsConsistentFrom gen tailLanguage identityEnumeration T) :
    False := by
  let t := max 1 T
  have ht : 0 < t := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 T)
  have hlower :
      (1 : ENNReal) ≤
        groupSupDistance
          (distributionAt gen identityEnumeration t)
          (GenLimit.Generic.sample identityEnumeration t) tailGroups :=
    distance_one_le_of_consistent_identity ht
      (hconsistent t (Nat.le_max_right 1 T))
  have hupper := hrep identityEnumeration t ht
  have hone : (1 : ENNReal) ≤ ENNReal.ofReal alpha :=
    hlower.trans hupper
  exact (not_le_of_gt (ENNReal.ofReal_lt_one.mpr halpha)) hone

theorem identity_presents_tailLanguage :
    GenLimit.Generic.Presents identityEnumeration tailLanguage := by
  ext x
  simp [identityEnumeration, tailLanguage]

/-- A kernel-checked counterexample to published Lemma 4.8 and Theorem 4.4. -/
theorem tail_pair_not_representativelyGeneratableInLimit :
    ¬RepresentativelyGeneratableInLimit tailClass tailGroups := by
  intro hgen
  obtain ⟨gen, hrep, hlimit⟩ := hgen (1 / 2) (by norm_num)
  have hLmem : tailLanguage ∈ tailClass := by simp [tailClass]
  obtain ⟨T, hconsistent⟩ :=
    hlimit tailLanguage hLmem identityEnumeration
      identity_presents_tailLanguage
  exact no_eventually_consistent_alpha_representative
    (alpha := 1 / 2) (by norm_num) gen hrep T hconsistent

/-- All printed premises of published Theorem 4.4 hold for the tail construction, while
its conclusion fails. -/
theorem printed_theorem_4_4_counterexample :
    tailClass.Countable ∧
    GenLimit.Generic.UUS tailClass ∧
    GroupsCover tailGroups ∧
    HasFiniteSupport tailClass tailGroups ∧
    ¬RepresentativelyGeneratableInLimit tailClass tailGroups :=
  ⟨tailClass_countable, tailClass_UUS, tailGroups_cover,
    tailClass_hasFiniteSupport,
    tail_pair_not_representativelyGeneratableInLimit⟩

end GenLimit.RepresentativeGeneration
