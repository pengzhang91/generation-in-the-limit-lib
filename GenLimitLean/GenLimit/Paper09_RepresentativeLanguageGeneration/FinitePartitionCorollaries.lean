import GenLimit.Paper09_RepresentativeLanguageGeneration.GroupClosure
import GenLimit.Paper09_RepresentativeLanguageGeneration.NonuniformCharacterization
import GenLimit.Paper09_RepresentativeLanguageGeneration.Relationships
import GenLimit.Support.CountableCovers
import Mathlib.Data.Finset.Powerset

/-!
# Finite-partition corollaries

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Corollaries 3.5 and 3.8.

The paper states these results for a partition indexed by a finite set.  The
core representative-generation API uses natural-number indexed partitions,
so `extendFinitePartition` pads a finite family with empty groups.  This
module proves the missing finite-class combinatorial bound directly and then
uses published Theorems 3.3 and 3.7.

The source proof of Corollary 3.5 writes a maximum over the possibly empty
family of finite group intersections and chooses the generally nonintegral
quantity `Kp/α` as a natural threshold.  The proof below avoids both issues:
there are only finitely many version-space cores, and the union of all their
finite group pieces is one finite exceptional set.  Above an Archimedean
threshold, its empirical mass is at most `α`, ruling out both group-closure
alternatives.
-/

namespace GenLimit.RepresentativeGeneration

/-! ## Finite partitions inside the countable-partition API -/

/-- Pad a `k`-group family by empty groups at every index at least `k`. -/
def extendFinitePartition
    {k : ℕ} (groups : Fin k → Set α) : ℕ → Set α :=
  fun i ↦ if h : i < k then groups ⟨i, h⟩ else ∅

@[simp]
theorem extendFinitePartition_apply_fin
    {k : ℕ} (groups : Fin k → Set α) (i : Fin k) :
    extendFinitePartition groups i = groups i := by
  simp [extendFinitePartition, i.isLt]

@[simp]
theorem extendFinitePartition_apply_of_ge
    {k : ℕ} (groups : Fin k → Set α) {i : ℕ} (hi : k ≤ i) :
    extendFinitePartition groups i = ∅ := by
  simp [extendFinitePartition, Nat.not_lt.mpr hi]

/-- A finite partition is represented by its empty-padded natural-indexed
extension, so all existing representative-generation definitions apply
without a second parallel API. -/
def IsFinitePartition
    {k : ℕ} (groups : Fin k → Set α) : Prop :=
  IsCountablePartition (extendFinitePartition groups)

/-- Build the finite-partition predicate from the native finite-indexed
pairwise-disjointness and coverage conditions. -/
theorem isFinitePartition_of_pairwise_iUnion
    {k : ℕ} {groups : Fin k → Set α}
    (hdisjoint :
      ∀ i j : Fin k, i ≠ j →
        Disjoint (groups i) (groups j))
    (hcover : (⋃ i : Fin k, groups i) = Set.univ) :
    IsFinitePartition groups := by
  constructor
  · intro i j hij
    by_cases hi : i < k
    · by_cases hj : j < k
      · have hfin :
            (⟨i, hi⟩ : Fin k) ≠ ⟨j, hj⟩ := by
          intro heq
          apply hij
          exact congrArg Fin.val heq
        simpa [extendFinitePartition, hi, hj] using
          hdisjoint ⟨i, hi⟩ ⟨j, hj⟩ hfin
      · simp [extendFinitePartition, hi, hj]
    · simp [extendFinitePartition, hi]
  · apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro x _hx
      have hxFinite :
          x ∈ ⋃ i : Fin k, groups i := by
        rw [hcover]
        exact Set.mem_univ x
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxFinite
      exact Set.mem_iUnion.mpr
        ⟨i.1, by
          simpa [extendFinitePartition, i.isLt] using hxi⟩

theorem isCountablePartition_extendFinitePartition
    {k : ℕ} {groups : Fin k → Set α}
    (hpartition : IsFinitePartition groups) :
    IsCountablePartition (extendFinitePartition groups) :=
  hpartition

theorem active_extendFinitePartition_index_lt
    {k : ℕ} (groups : Fin k → Set α) {i : ℕ}
    (hi : (extendFinitePartition groups i).Nonempty) :
    i < k := by
  by_contra hnot
  rw [extendFinitePartition_apply_of_ge groups (Nat.le_of_not_gt hnot)] at hi
  exact Set.not_nonempty_empty hi

/-! ## Empirical mass on a set of partition coordinates -/

/-- The empirical mass of one group, expressed as a finite-set cardinality
in `ENNReal`. -/
theorem empiricalGroupENN_eq_ncard_div
    (S : Finset α) (groups : ℕ → Set α) (i : ℕ)
    (hS : S.Nonempty) :
    empiricalGroupENN S groups i =
      ((((↑S : Set α) ∩ groups i).ncard : ℕ) : ENNReal) /
        (S.card : ENNReal) := by
  classical
  have hcardPos : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  simp only [empiricalGroupENN, empiricalGroupProbability, if_pos hS,
    ENNReal.ofReal_div_of_pos hcardPos, ENNReal.ofReal_natCast]
  congr 2
  rw [← Set.ncard_coe_finset
    (S.filter (fun x => x ∈ groups i))]
  congr 1
  ext x
  simp

/-- For a genuine partition, empirical mass on an arbitrary set of group
indices is the fraction of observed points whose unique group index lies in
that set. -/
theorem empiricalMassOnGroupIndices_eq_ncard_div
    (S : Finset α) (groups : ℕ → Set α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty) (I : Set ℕ) :
    empiricalMassOnGroupIndices S groups I =
      (((↑S : Set α) ∩
          (partitionIndex groups hpartition ⁻¹' I)).ncard : ENNReal) /
        (S.card : ENNReal) := by
  classical
  let idx := partitionIndex groups hpartition
  unfold empiricalMassOnGroupIndices
  rw [tsum_eq_sum (s := S.image idx) (fun i hi => by
    by_cases hiI : i ∈ I
    · rw [if_pos hiI]
      exact empiricalGroupENN_eq_zero_of_not_mem_image
        S groups hpartition hi
    · simp [hiI])]
  have hfiberCard (i : ℕ) :
      ((↑S : Set α) ∩ groups i).ncard =
        (S.filter (fun x => idx x = i)).card := by
    rw [← Set.ncard_coe_finset
      (S.filter (fun x => idx x = i))]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Finset.mem_coe,
      Finset.mem_filter]
    exact and_congr_right (fun _ =>
      mem_group_iff_partitionIndex_eq groups hpartition x i)
  calc
    ∑ i ∈ S.image idx,
        (if i ∈ I then empiricalGroupENN S groups i else 0) =
        (∑ i ∈ S.image idx,
          (if i ∈ I then
            (((↑S : Set α) ∩ groups i).ncard : ENNReal)
          else 0)) / (S.card : ENNReal) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hiI : i ∈ I
      · simp [hiI, empiricalGroupENN_eq_ncard_div S groups i hS,
          div_eq_mul_inv]
      · simp [hiI]
    _ = (((↑S : Set α) ∩ (idx ⁻¹' I)).ncard : ENNReal) /
          (S.card : ENNReal) := by
      congr 1
      exact_mod_cast (by
        simp_rw [hfiberCard]
        let T := S.filter (fun x => idx x ∈ I)
        have himage :
            T.image idx =
              (S.image idx).filter (fun i => i ∈ I) := by
          ext i
          constructor
          · intro hi
            obtain ⟨x, hxT, hxi⟩ :=
              Finset.mem_image.mp hi
            have hx := Finset.mem_filter.mp hxT
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_image.mpr ⟨x, hx.1, hxi⟩,
                hxi ▸ hx.2⟩
          · intro hi
            have hi' := Finset.mem_filter.mp hi
            obtain ⟨x, hxS, hxi⟩ :=
              Finset.mem_image.mp hi'.1
            exact Finset.mem_image.mpr
              ⟨x, Finset.mem_filter.mpr
                ⟨hxS, hxi ▸ hi'.2⟩, hxi⟩
        have hfiber (i : ℕ) (hi : i ∈ I) :
            T.filter (fun x => idx x = i) =
              S.filter (fun x => idx x = i) := by
          ext x
          simp only [Finset.mem_filter, T]
          constructor
          · rintro ⟨⟨hxS, _hxI⟩, hxi⟩
            exact ⟨hxS, hxi⟩
          · rintro ⟨hxS, hxi⟩
            exact ⟨⟨hxS, hxi ▸ hi⟩, hxi⟩
        calc
          ∑ i ∈ S.image idx,
              (if i ∈ I then
                (S.filter (fun x => idx x = i)).card
              else 0) =
              ∑ i ∈ (S.image idx).filter (fun i => i ∈ I),
                (S.filter (fun x => idx x = i)).card := by
                  simp [Finset.sum_filter]
          _ = ∑ i ∈ T.image idx,
                (T.filter (fun x => idx x = i)).card := by
                  rw [himage]
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact congrArg Finset.card
                    (hfiber i (Finset.mem_filter.mp hi).2).symm
          _ = T.card :=
            (Finset.card_eq_sum_card_image idx T).symm
          _ = ((↑S : Set α) ∩ (idx ⁻¹' I)).ncard := by
            rw [← Set.ncard_coe_finset T]
            congr 1
            ext x
            simp [T])

/-! ## Finite classes have finite group-closure dimension -/

private noncomputable def finiteCorePart
    (C : Set α) (A : Set α) : Finset α := by
  classical
  exact if h : (C ∩ A).Finite then h.toFinset else ∅

private theorem mem_finiteCorePart
    {C A : Set α} (hfinite : (C ∩ A).Finite) {x : α} :
    x ∈ finiteCorePart C A ↔ x ∈ C ∩ A := by
  classical
  simp [finiteCorePart, hfinite]

/-- The finite-class combinatorial core of published Corollary 3.5.  Finitely many
languages yield finitely many possible version-space cores; with finitely
many groups, all finite core/group intersections fit inside one finite
exceptional set. -/
theorem finite_languageClass_has_finite_groupClosureDimension
    {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite)
    {k : ℕ} (groups : Fin k → Set α)
    (hpartition : IsFinitePartition groups)
    {alpha : ℝ} (halpha : 0 < alpha) :
    HasFiniteGroupClosureDimension H
      (extendFinitePartition groups) alpha := by
  classical
  let natGroups := extendFinitePartition groups
  have hnatPartition : IsCountablePartition natGroups :=
    hpartition
  let coreOf :
      Set (GenLimit.Generic.Language α) →
        GenLimit.Generic.Language α :=
    fun V ↦ {x | ∀ L, L ∈ V → x ∈ L}
  have hcoresFinite : (coreOf '' Set.powerset H).Finite :=
    hH.powerset.image coreOf
  let cores : Finset (GenLimit.Generic.Language α) :=
    hcoresFinite.toFinset
  let exceptional : Finset α :=
    cores.biUnion (fun C =>
      Finset.univ.biUnion (fun i : Fin k =>
        finiteCorePart C (groups i)))
  let cap : ENNReal := ENNReal.ofReal alpha
  have hcap : cap ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr halpha
  obtain ⟨n, _hnpos, hn⟩ :=
    ENNReal.exists_nat_pos_mul_gt hcap
      (show (exceptional.card : ENNReal) ≠ ⊤ by simp)
  refine ⟨max n exceptional.card, ?_⟩
  intro S hWitness
  by_contra hnot
  have hlarge : max n exceptional.card < S.card :=
    Nat.lt_of_not_ge hnot
  have hnCard : n ≤ S.card :=
    (le_max_left n exceptional.card).trans hlarge.le
  have hExceptionalCard : exceptional.card < S.card :=
    (le_max_right n exceptional.card).trans_lt hlarge
  have hSnonempty : S.Nonempty := hWitness.1
  have hsampleCore :
      (↑S : Set α) ⊆ commonCore H S := by
    exact GenLimit.Generic.sample_subset_commonCore
  have hcoreMem : commonCore H S ∈ cores := by
    change commonCore H S ∈ hcoresFinite.toFinset
    rw [Set.Finite.mem_toFinset]
    refine ⟨consistentHypotheses H S, ?_, rfl⟩
    intro L hL
    exact hL.1
  let unavailable :=
    unavailableGroups H natGroups S
  let idx := partitionIndex natGroups hnatPartition
  let bad : Set α :=
    (↑S : Set α) ∩ (idx ⁻¹' unavailable)
  have hbadSubset : bad ⊆ (↑exceptional : Set α) := by
    intro x hx
    have hxS : x ∈ S := hx.1
    have hxCore : x ∈ commonCore H S :=
      hsampleCore hx.1
    have hxGroup :
        x ∈ natGroups (idx x) :=
      mem_partitionIndex natGroups hnatPartition x
    have hidxUnavailable : idx x ∈ unavailable := hx.2
    have hcoreGroupSubset :
        commonCore H S ∩ natGroups (idx x) ⊆
          (↑S : Set α) := by
      intro y hy
      by_contra hyS
      have hyUnseen :
          y ∈ unseenClosure H S :=
        ⟨hy.1, hyS⟩
      have hyIntersection :
          y ∈ unseenClosure H S ∩ natGroups (idx x) :=
        ⟨hyUnseen, hy.2⟩
      change
        unseenClosure H S ∩ natGroups (idx x) = ∅
        at hidxUnavailable
      rw [hidxUnavailable] at hyIntersection
      exact hyIntersection
    have hcoreGroupFinite :
        (commonCore H S ∩ natGroups (idx x)).Finite :=
      S.finite_toSet.subset hcoreGroupSubset
    have hidxLt : idx x < k := by
      apply active_extendFinitePartition_index_lt groups
      exact ⟨x, hxGroup⟩
    let i : Fin k := ⟨idx x, hidxLt⟩
    have hgroupEq : natGroups (idx x) = groups i := by
      exact extendFinitePartition_apply_fin groups i
    have hfinite :
        (commonCore H S ∩ groups i).Finite := by
      rwa [← hgroupEq]
    change x ∈ exceptional
    simp only [exceptional, Finset.mem_biUnion]
    refine ⟨commonCore H S, hcoreMem, i,
      Finset.mem_univ i, ?_⟩
    apply (mem_finiteCorePart hfinite).2
    exact ⟨hxCore, hgroupEq ▸ hxGroup⟩
  have hbadCard : bad.ncard ≤ exceptional.card := by
    simpa [Set.ncard_coe_finset] using
      Set.ncard_le_ncard hbadSubset exceptional.finite_toSet
  have hScardNeZero : (S.card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hSnonempty
  have hScardNeTop : (S.card : ENNReal) ≠ ⊤ := by
    simp
  have hExceptionalRatio :
      (exceptional.card : ENNReal) / S.card < cap := by
    apply (ENNReal.div_lt_iff
      (Or.inl hScardNeZero) (Or.inl hScardNeTop)).2
    calc
      (exceptional.card : ENNReal) < (n : ENNReal) * cap := hn
      _ ≤ (S.card : ENNReal) * cap := by
        exact mul_le_mul_right'
          (by exact_mod_cast hnCard) cap
      _ = cap * (S.card : ENNReal) := mul_comm _ _
  have hbadRatio :
      (bad.ncard : ENNReal) / S.card < cap := by
    exact (ENNReal.div_le_div_right
      (by exact_mod_cast hbadCard) S.card).trans_lt
      hExceptionalRatio
  rcases hWitness.2.2 with hone | htwo
  · obtain ⟨i, hiUnavailable, hiLarge⟩ := hone
    have hgroupSubsetBad :
        (↑S : Set α) ∩ natGroups i ⊆ bad := by
      intro x hx
      have hidx :
          partitionIndex natGroups hnatPartition x = i :=
        partitionIndex_eq_of_mem natGroups hnatPartition hx.2
      refine ⟨hx.1, ?_⟩
      change partitionIndex natGroups hnatPartition x ∈ unavailable
      rw [hidx]
      exact hiUnavailable
    have hbadFinite : bad.Finite :=
      exceptional.finite_toSet.subset hbadSubset
    have hgroupCard :
        ((↑S : Set α) ∩ natGroups i).ncard ≤ bad.ncard :=
      Set.ncard_le_ncard hgroupSubsetBad
        hbadFinite
    have hgroupRatio :
        (((↑S : Set α) ∩ natGroups i).ncard : ENNReal) /
            S.card < cap :=
      (ENNReal.div_le_div_right
        (by exact_mod_cast hgroupCard) S.card).trans_lt
        hbadRatio
    change cap < empiricalGroupENN S natGroups i at hiLarge
    rw [empiricalGroupENN_eq_ncard_div
      S natGroups i hSnonempty] at hiLarge
    exact (lt_asymm hiLarge hgroupRatio)
  · obtain ⟨havailableFinite, hcapacityFailure⟩ := htwo
    by_cases havailable :
        unavailableᶜ.Nonempty
    · have havailableCardPos :
          0 < havailableFinite.toFinset.card := by
        exact Finset.card_pos.mpr
          ((Set.Finite.toFinset_nonempty havailableFinite).mpr
            havailable)
      have hcapLe :
          cap ≤ cap * havailableFinite.toFinset.card := by
        calc
          cap = cap * 1 := by simp
          _ ≤ cap * havailableFinite.toFinset.card := by
            exact mul_le_mul_left'
              (by exact_mod_cast havailableCardPos) cap
      have hmassLt :
          empiricalMassOnGroupIndices S natGroups unavailable <
            cap := by
        rw [empiricalMassOnGroupIndices_eq_ncard_div
          S natGroups hnatPartition hSnonempty unavailable]
        exact hbadRatio
      exact (not_lt_of_ge hcapLe)
        (hcapacityFailure.trans hmassLt)
    · have hsampleSubsetBad :
          (↑S : Set α) ⊆ bad := by
        intro x hxS
        refine ⟨hxS, ?_⟩
        by_contra hidx
        exact havailable ⟨idx x, hidx⟩
      have hsampleSubsetExceptional :
          (↑S : Set α) ⊆ (↑exceptional : Set α) :=
        hsampleSubsetBad.trans hbadSubset
      have hcard :
          S.card ≤ exceptional.card :=
        Finset.card_le_card (by
          intro x hx
          exact hsampleSubsetExceptional hx)
      omega

/-! ## Published Corollary 3.5 -/

/-- Fixed-tolerance form of the finite-class/finite-partition result. -/
theorem finiteClass_finitePartition_alphaRepresentativeUniformlyGeneratable
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite)
    {k : ℕ} (groups : Fin k → Set α)
    (hpartition : IsFinitePartition groups)
    {alpha : ℝ} (halpha : 0 < alpha) :
    AlphaRepresentativeUniformlyGeneratable H
      (extendFinitePartition groups) alpha := by
  apply
    alphaRepresentativeUniformlyGeneratable_of_finite_groupClosureDimension
      hpartition halpha
  exact finite_languageClass_has_finite_groupClosureDimension
    hH groups hpartition halpha

/-- Every finite language class and finite partition is representatively
uniformly generatable.  This stronger internal form does not need
countability or UUS once the finite partition has been supplied. -/
theorem finiteClass_finitePartition_representativelyUniformlyGeneratable
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite)
    {k : ℕ} (groups : Fin k → Set α)
    (hpartition : IsFinitePartition groups) :
    RepresentativelyUniformlyGeneratable H
      (extendFinitePartition groups) := by
  intro alpha halpha _halphaOne
  exact
    finiteClass_finitePartition_alphaRepresentativeUniformlyGeneratable
      hH groups hpartition halpha

/-! ## Published Corollary 3.8 -/

/-- A countable class is the increasing union of finite prefixes, each of
which is representatively uniformly generatable for a finite partition.
Theorem 3.7 therefore gives representative non-uniform generation.  The
statement also covers empty and finite classes. -/
theorem countableClass_finitePartition_representativelyNonuniformlyGeneratable
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α} (hCountable : H.Countable)
    {k : ℕ} (groups : Fin k → Set α)
    (hpartition : IsFinitePartition groups) :
    RepresentativelyNonuniformlyGeneratable H
      (extendFinitePartition groups) := by
  classical
  obtain ⟨enumerate, hEnumerates⟩ :=
    Set.countable_iff_exists_subset_range.mp hCountable
  apply representative_nonuniform_cover_sufficiency
  intro alpha halpha
  refine
    ⟨GenLimit.Support.finitePrefixSubclass H enumerate,
      GenLimit.Support.finitePrefixSubclass_isNondecreasingCover
        H enumerate hEnumerates,
      ?_⟩
  · intro n
    apply
      finiteClass_finitePartition_alphaRepresentativeUniformlyGeneratable
        (groups := groups) (hpartition := hpartition)
        (halpha := halpha)
    exact GenLimit.Support.finitePrefixSubclass_finite
      H enumerate n

/-- A countably infinite UUS class paired with a finite partition is
representatively non-uniformly generatable and hence representatively
generatable in the limit, as asserted by published Corollary 3.8. -/
theorem countableClass_finitePartition_nonuniform_and_limit
    [Nonempty α] [Countable α]
    (H : GenLimit.Generic.LanguageClass α)
    (hCountable : H.Countable) (_hInfinite : H.Infinite)
    (hUUS : GenLimit.Generic.UUS H)
    {k : ℕ} (groups : Fin k → Set α)
    (hpartition : IsFinitePartition groups) :
    RepresentativelyNonuniformlyGeneratable H
        (extendFinitePartition groups) ∧
      RepresentativelyGeneratableInLimit H
        (extendFinitePartition groups) := by
  have hNonuniform :
      RepresentativelyNonuniformlyGeneratable H
        (extendFinitePartition groups) :=
    countableClass_finitePartition_representativelyNonuniformlyGeneratable
      hCountable groups hpartition
  exact
    ⟨hNonuniform,
      representative_nonuniform_implies_limit hUUS hNonuniform⟩

end GenLimit.RepresentativeGeneration
