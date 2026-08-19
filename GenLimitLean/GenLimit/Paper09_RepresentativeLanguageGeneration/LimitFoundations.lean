import GenLimit.Paper09_RepresentativeLanguageGeneration.GroupClosure
import GenLimit.Paper09_RepresentativeLanguageGeneration.FiniteSupport
import GenLimit.Paper09_RepresentativeLanguageGeneration.TailCounterexample

/-!
# Representative generation in the limit: source definitions and necessity

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Lemmas 4.3 and 4.6 and Definitions 4.5 and 4.7.

The source's critical-language and feasibility definitions are recorded
first, together with their basic semantic consequences.  We then formalize
Lemma 4.3 using one fixed partition whose finite blocks grow fast enough that
each new block eventually occupies an arbitrarily large fraction of the
observed prefix.  This strengthens the source proof, which chooses a
different partition after fixing the tolerance and therefore does not by
itself establish the quantifier order printed in the lemma.
-/

namespace GenLimit.RepresentativeGeneration

/-! ## Published Definitions 4.5 and 4.7 -/

/-- A language is consistent with the observations strictly before `t`. -/
def LanguageConsistentAt
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  (↑(GenLimit.Generic.sample stream t) : Set α) ⊆ L

/-- Published Definition 4.5: a scoped critical hypothesis.  Since `family 0`
corresponds to the source's `h₁`, its one-based condition `n ≤ t` becomes
`n < t` for a history of length `t`; every earlier consistent hypothesis
must contain the critical language. -/
def IsCriticalAt
    (family : GenLimit.Generic.LanguageFamily α)
    (stream : GenLimit.Generic.Stream α) (t n : ℕ) : Prop :=
  n < t ∧
    LanguageConsistentAt (family n) stream t ∧
    ∀ i, i < n →
      LanguageConsistentAt (family i) stream t →
      family n ⊆ family i

/-- Critical hypotheses in the same scope form a reverse-inclusion chain. -/
theorem critical_subset_of_le
    {family : GenLimit.Generic.LanguageFamily α}
    {stream : GenLimit.Generic.Stream α} {t i j : ℕ}
    (hij : i ≤ j)
    (hi : IsCriticalAt family stream t i)
    (hj : IsCriticalAt family stream t j) :
    family j ⊆ family i := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact Set.Subset.rfl
  · exact hj.2.2 i hij hi.2.1

/-- For a fixed candidate, sample consistency eventually agrees with
containment of the presented target. -/
theorem candidate_eventually_consistent_iff_target_subset
    {family : GenLimit.Generic.LanguageFamily α}
    {stream : GenLimit.Generic.Stream α} {z i : ℕ}
    (hP : GenLimit.Generic.Presents stream (family z)) :
    ∃ T, ∀ t, T ≤ t →
      (LanguageConsistentAt (family i) stream t ↔
        family z ⊆ family i) := by
  classical
  by_cases hsubset : family z ⊆ family i
  · refine ⟨0, ?_⟩
    intro t _ht
    constructor
    · intro _hconsistent
      exact hsubset
    · intro _hsubset x hx
      obtain ⟨s, _hs, rfl⟩ :=
        GenLimit.Generic.mem_sample_iff.mp hx
      exact hsubset
        (GenLimit.Generic.streamIn_of_presents hP ⟨s, rfl⟩)
  · obtain ⟨x, hxTarget, hxNotCandidate⟩ :=
      Set.not_subset.mp hsubset
    have hxRange : x ∈ Set.range stream := by
      rw [hP]
      exact hxTarget
    obtain ⟨s, hsx⟩ := hxRange
    refine ⟨s + 1, ?_⟩
    intro t hst
    constructor
    · intro hconsistent
      exfalso
      apply hxNotCandidate
      apply hconsistent
      exact GenLimit.Generic.mem_sample_iff.mpr
        ⟨s, (Nat.lt_succ_self s).trans_le hst, hsx⟩
    · intro hsubset'
      exact False.elim (hsubset hsubset')

/-- The previous stabilization can be made uniform over a finite index
scope. -/
theorem finite_scope_eventually_consistent_iff_target_subset
    {family : GenLimit.Generic.LanguageFamily α}
    {stream : GenLimit.Generic.Stream α} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (family z))
    (scope : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < scope →
      (LanguageConsistentAt (family i) stream t ↔
        family z ⊆ family i) := by
  induction scope with
  | zero =>
      exact ⟨0, by omega⟩
  | succ scope ih =>
      obtain ⟨Tscope, hscope⟩ := ih
      obtain ⟨Tlast, hlast⟩ :=
        candidate_eventually_consistent_iff_target_subset
          (family := family) (stream := stream)
          (z := z) (i := scope) hP
      refine ⟨max Tscope Tlast, ?_⟩
      intro t ht i hi
      have hscopeT : Tscope ≤ t :=
        (Nat.le_max_left Tscope Tlast).trans ht
      have hlastT : Tlast ≤ t :=
        (Nat.le_max_right Tscope Tlast).trans ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hscope t hscopeT i hi
      · exact hlast t hlastT

/-- Published Lemma 4.6: the true target is eventually critical.  This is the
cited KM Claim 4.3 reused by the source immediately after Definition 4.5. -/
theorem target_eventually_critical
    {family : GenLimit.Generic.LanguageFamily α}
    {stream : GenLimit.Generic.Stream α} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (family z)) :
    ∃ T, ∀ t, T ≤ t → IsCriticalAt family stream t z := by
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistent_iff_target_subset hP z
  refine ⟨max (z + 1) T, ?_⟩
  intro t ht
  have hzT : z < t :=
    lt_of_lt_of_le (Nat.lt_succ_self z)
      ((Nat.le_max_left (z + 1) T).trans ht)
  have hTT : T ≤ t :=
    (Nat.le_max_right (z + 1) T).trans ht
  refine ⟨hzT, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, _hs, rfl⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hx
    exact GenLimit.Generic.streamIn_of_presents hP ⟨s, rfl⟩
  · intro i hiz hconsistent
    exact (hT t hTT i hiz).mp hconsistent

/-- Published Definition 4.7: at the paper's standing positive tolerance, the language
admits a representative distribution supported on its currently unseen
points.  The formula itself remains meaningful for every real `alpha`. -/
def IsAlphaFeasibleAt
    (L : GenLimit.Generic.Language α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  ∃ μ : DiscreteDistribution α,
    SupportedOn μ
      (L \ (↑(GenLimit.Generic.sample stream t) : Set α)) ∧
    groupSupDistance μ
        (GenLimit.Generic.sample stream t) groups ≤
      ENNReal.ofReal alpha

/-- The fixed-tolerance component of Definition 2.12.  Naming it explicitly
lets Lemma 4.3 state its printed quantifier order over every `0 < alpha < 1`.
-/
def AlphaRepresentativelyGeneratableInLimit
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) : Prop :=
  ∃ gen : RandomizedGenerator α,
    IsAlphaRepresentative gen groups alpha ∧
    ∀ L, L ∈ H →
      ∀ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.Presents stream L →
          ∃ T : ℕ, IsConsistentFrom gen L stream T

theorem representativelyGeneratableInLimit_iff_forall_alpha :
    RepresentativelyGeneratableInLimit H groups ↔
      ∀ alpha : ℝ, 0 < alpha →
        AlphaRepresentativelyGeneratableInLimit H groups alpha :=
  Iff.rfl

/-- A representative generator that is consistent at one time witnesses
feasibility of the target language at that time. -/
theorem isAlphaFeasibleAt_of_generator
    {gen : RandomizedGenerator α}
    {L : GenLimit.Generic.Language α}
    {groups : ℕ → Set α} {alpha : ℝ}
    {stream : GenLimit.Generic.Stream α} {t : ℕ}
    (ht : 0 < t)
    (hrepresentative : IsAlphaRepresentative gen groups alpha)
    (hconsistent : IsConsistentAt gen L stream t) :
    IsAlphaFeasibleAt L groups alpha stream t := by
  exact
    ⟨distributionAt gen stream t,
      isConsistentAt_iff_supportedOn.mp hconsistent,
      hrepresentative stream t ht⟩

/-! ## A fixed dominant-block partition -/

/-- Endpoints of increasingly dominant finite blocks. -/
def dominantEndpoint : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      dominantEndpoint n +
        (n + 1) * (dominantEndpoint n + 1)

@[simp]
theorem dominantEndpoint_zero :
    dominantEndpoint 0 = 0 :=
  rfl

@[simp]
theorem dominantEndpoint_succ (n : ℕ) :
    dominantEndpoint (n + 1) =
      dominantEndpoint n +
        (n + 1) * (dominantEndpoint n + 1) :=
  rfl

theorem dominantEndpoint_lt_succ (n : ℕ) :
    dominantEndpoint n < dominantEndpoint (n + 1) := by
  rw [dominantEndpoint_succ]
  have hpositive :
      0 < (n + 1) * (dominantEndpoint n + 1) :=
    Nat.mul_pos (Nat.succ_pos n)
      (Nat.succ_pos (dominantEndpoint n))
  omega

theorem dominantEndpoint_strictMono :
    StrictMono dominantEndpoint :=
  strictMono_nat_of_lt_succ dominantEndpoint_lt_succ

theorem index_le_dominantEndpoint (n : ℕ) :
    n ≤ dominantEndpoint n := by
  induction n with
  | zero => simp
  | succ n ih =>
      exact Nat.succ_le_of_lt
        (ih.trans_lt (dominantEndpoint_lt_succ n))

/-- The half-open block between two consecutive dominant endpoints. -/
def dominantBlockGroups (n : ℕ) : Set ℕ :=
  Set.Ico (dominantEndpoint n) (dominantEndpoint (n + 1))

theorem dominantBlockGroups_nonempty (n : ℕ) :
    (dominantBlockGroups n).Nonempty :=
  ⟨dominantEndpoint n, le_rfl, dominantEndpoint_lt_succ n⟩

theorem dominantBlockGroups_pairwise :
    ∀ i j, i ≠ j →
      Disjoint (dominantBlockGroups i) (dominantBlockGroups j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hend :
        dominantEndpoint (i + 1) ≤ dominantEndpoint j :=
      dominantEndpoint_strictMono.monotone
        (Nat.succ_le_of_lt hij)
    exact (not_lt_of_ge (hend.trans hxj.1)) hxi.2
  · apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hend :
        dominantEndpoint (j + 1) ≤ dominantEndpoint i :=
      dominantEndpoint_strictMono.monotone
        (Nat.succ_le_of_lt hji)
    exact (not_lt_of_ge (hend.trans hxi.1)) hxj.2

theorem iUnion_dominantBlockGroups :
    (⋃ n, dominantBlockGroups n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hexists :
      ∃ n, x < dominantEndpoint (n + 1) := by
    refine ⟨x, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self x)
      (index_le_dominantEndpoint (x + 1))
  let n := Nat.find hexists
  have hnUpper :
      x < dominantEndpoint (n + 1) :=
    Nat.find_spec hexists
  have hnLower :
      dominantEndpoint n ≤ x := by
    by_cases hn : n = 0
    · simp [hn]
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hmFind : m < Nat.find hexists := by
        change m < n
        rw [hm]
        exact Nat.lt_succ_self m
      have hnotM :
          ¬ x < dominantEndpoint (m + 1) :=
        Nat.find_min hexists hmFind
      have hnotN :
          ¬ x < dominantEndpoint n := by
        simpa [hm] using hnotM
      exact Nat.le_of_not_gt hnotN
  exact Set.mem_iUnion.mpr
    ⟨n, hnLower, hnUpper⟩

theorem dominantBlockGroups_isCountablePartition :
    IsCountablePartition dominantBlockGroups :=
  ⟨dominantBlockGroups_pairwise,
    iUnion_dominantBlockGroups⟩

theorem dominantBlockGroups_injective :
    Function.Injective dominantBlockGroups := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hi :
        dominantEndpoint i ∈ dominantBlockGroups i :=
      ⟨le_rfl, dominantEndpoint_lt_succ i⟩
    have hj :
        dominantEndpoint i ∈ dominantBlockGroups j := by
      rw [← hij]
      exact hi
    exact
      (not_le_of_gt
        (dominantEndpoint_strictMono hijlt)) hj.1
  · have hj :
        dominantEndpoint j ∈ dominantBlockGroups j :=
      ⟨le_rfl, dominantEndpoint_lt_succ j⟩
    have hi :
        dominantEndpoint j ∈ dominantBlockGroups i := by
      rw [hij]
      exact hj
    exact
      (not_le_of_gt
        (dominantEndpoint_strictMono hjilt)) hi.1

theorem dominantEndpoint_succ_pos (n : ℕ) :
    0 < dominantEndpoint (n + 1) := by
  rw [← dominantEndpoint_zero]
  exact dominantEndpoint_strictMono (Nat.zero_lt_succ n)

theorem dominantBlock_filter_range (n : ℕ) :
    @Finset.filter ℕ
        (fun x => x ∈ dominantBlockGroups n)
        (fun x =>
          Classical.propDecidable
            (x ∈ dominantBlockGroups n))
        (Finset.range (dominantEndpoint (n + 1))) =
      Finset.Ico (dominantEndpoint n)
        (dominantEndpoint (n + 1)) := by
  classical
  ext x
  simp [dominantBlockGroups]

theorem dominantEndpoint_sub (n : ℕ) :
    dominantEndpoint (n + 1) - dominantEndpoint n =
      (n + 1) * (dominantEndpoint n + 1) := by
  rw [dominantEndpoint_succ]
  omega

/-- At the moment block `n` has just been exhausted, its empirical mass is
its block length divided by the full prefix length. -/
theorem empirical_identity_dominantBlock (n : ℕ) :
    empiricalGroupProbability
        (GenLimit.Generic.sample identityEnumeration
          (dominantEndpoint (n + 1)))
        dominantBlockGroups n =
      (((n + 1) * (dominantEndpoint n + 1) : ℕ) : ℝ) /
        dominantEndpoint (n + 1) := by
  classical
  rw [sample_identityEnumeration]
  have hnonempty :
      (Finset.range (dominantEndpoint (n + 1))).Nonempty :=
    ⟨0, Finset.mem_range.mpr (dominantEndpoint_succ_pos n)⟩
  rw [empiricalGroupProbability]
  simp only [hnonempty, if_true]
  rw [dominantBlock_filter_range, Nat.card_Ico,
    dominantEndpoint_sub,
    Finset.card_range]

/-- The newest block occupies more than `(n+1)/(n+2)` of its completed
prefix, hence asymptotically an arbitrarily large empirical fraction. -/
theorem indexRatio_lt_empirical_identity_dominantBlock (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) / (n + 2) <
      empiricalGroupProbability
        (GenLimit.Generic.sample identityEnumeration
          (dominantEndpoint (n + 1)))
        dominantBlockGroups n := by
  rw [empirical_identity_dominantBlock,
    dominantEndpoint_succ]
  push_cast
  have hleft : (0 : ℝ) < n + 2 := by positivity
  have hright :
      (0 : ℝ) <
        dominantEndpoint n +
          (n + 1) * (dominantEndpoint n + 1) := by
    exact_mod_cast dominantEndpoint_succ_pos n
  rw [div_lt_div_iff₀ hleft hright]
  ring_nf
  nlinarith

/-! ## Published Lemma 4.3 -/

theorem indexedGroupIntersection_singleton_dominantBlock (n : ℕ) :
    indexedGroupIntersection tailLanguage dominantBlockGroups {n} =
      dominantBlockGroups n := by
  ext x
  simp [indexedGroupIntersection, tailLanguage]

theorem finiteIntersectionContribution_eq_ncard
    (L : GenLimit.Generic.Language α) (groups : ℕ → Set α)
    (I : Set ℕ)
    (hfinite : (indexedGroupIntersection L groups I).Finite) :
    finiteIntersectionContribution L groups I =
      ((indexedGroupIntersection L groups I).ncard : ENNReal) := by
  classical
  unfold finiteIntersectionContribution
  dsimp only
  split
  · rename_i h
    exact_mod_cast
      (Set.ncard_eq_toFinset_card
        (indexedGroupIntersection L groups I) h).symm
  · contradiction

theorem one_le_finiteIntersectionContribution_singleton_dominantBlock
    (n : ℕ) :
    1 ≤
      finiteIntersectionContribution
        tailLanguage dominantBlockGroups {n} := by
  have hfinite :
      (indexedGroupIntersection
        tailLanguage dominantBlockGroups {n}).Finite := by
    rw [indexedGroupIntersection_singleton_dominantBlock]
    exact Set.finite_Ico _ _
  rw [finiteIntersectionContribution_eq_ncard
    tailLanguage dominantBlockGroups {n} hfinite]
  exact_mod_cast
    (Set.ncard_pos hfinite).mpr
      (by
        rw [indexedGroupIntersection_singleton_dominantBlock]
        exact dominantBlockGroups_nonempty n)

theorem singleton_set_injective :
    Function.Injective (fun n : ℕ => ({n} : Set ℕ)) := by
  intro m n h
  have hm :=
    congrArg (fun s : Set ℕ => m ∈ s) h
  simpa using hm

theorem dominantBlock_finiteSupportSize_top :
    finiteSupportSize tailLanguage dominantBlockGroups = ⊤ := by
  apply top_unique
  calc
    ⊤ = ∑' _n : ℕ, (1 : ENNReal) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∑' n : ℕ,
        finiteIntersectionContribution
          tailLanguage dominantBlockGroups ({n} : Set ℕ) :=
      ENNReal.tsum_le_tsum
        one_le_finiteIntersectionContribution_singleton_dominantBlock
    _ ≤ finiteSupportSize tailLanguage dominantBlockGroups := by
      exact
        ENNReal.tsum_comp_le_tsum_of_injective
          singleton_set_injective
          (finiteIntersectionContribution
            tailLanguage dominantBlockGroups)

theorem tailClass_not_hasFiniteSupport_dominantBlocks :
    ¬ HasFiniteSupport tailClass dominantBlockGroups := by
  intro hfiniteSupport
  have hfinite :=
    hfiniteSupport tailLanguage (by simp [tailClass])
  rw [dominantBlock_finiteSupportSize_top] at hfinite
  exact (lt_irrefl ⊤) hfinite

theorem unseen_identity_disjoint_dominantBlock (n : ℕ) :
    Disjoint
      (tailLanguage \
        (↑(GenLimit.Generic.sample identityEnumeration
          (dominantEndpoint (n + 1))) : Set ℕ))
      (dominantBlockGroups n) := by
  apply Set.disjoint_left.mpr
  intro x hxUnseen hxBlock
  apply hxUnseen.2
  rw [sample_identityEnumeration]
  exact Finset.mem_range.mpr hxBlock.2

theorem dominantBlock_mass_zero_of_consistent
    {gen : RandomizedGenerator ℕ} (n : ℕ)
    (hconsistent :
      IsConsistentAt gen tailLanguage identityEnumeration
        (dominantEndpoint (n + 1))) :
    inducedGroupProbability
        (distributionAt gen identityEnumeration
          (dominantEndpoint (n + 1)))
        dominantBlockGroups n = 0 := by
  change
    groupMass
      (distributionAt gen identityEnumeration
        (dominantEndpoint (n + 1)))
      (dominantBlockGroups n) = 0
  apply groupMass_eq_zero_of_supportedOn_of_disjoint
    (isConsistentAt_iff_supportedOn.mp hconsistent)
  exact unseen_identity_disjoint_dominantBlock n

theorem empiricalGroupProbability_le_distance_of_consistent_dominantBlock
    {gen : RandomizedGenerator ℕ} (n : ℕ)
    (hconsistent :
      IsConsistentAt gen tailLanguage identityEnumeration
        (dominantEndpoint (n + 1))) :
    ENNReal.ofReal
        (empiricalGroupProbability
          (GenLimit.Generic.sample identityEnumeration
            (dominantEndpoint (n + 1)))
          dominantBlockGroups n) ≤
      groupSupDistance
        (distributionAt gen identityEnumeration
          (dominantEndpoint (n + 1)))
        (GenLimit.Generic.sample identityEnumeration
          (dominantEndpoint (n + 1)))
        dominantBlockGroups := by
  have hmass :=
    dominantBlock_mass_zero_of_consistent n hconsistent
  have hcoordinate :=
    coordinate_le_groupSupDistance
      (distributionAt gen identityEnumeration
        (dominantEndpoint (n + 1)))
      (GenLimit.Generic.sample identityEnumeration
        (dominantEndpoint (n + 1)))
      dominantBlockGroups n
  have hempiricalNonnegative :=
    empiricalGroupProbability_nonnegative
      (GenLimit.Generic.sample identityEnumeration
        (dominantEndpoint (n + 1)))
      dominantBlockGroups n
  rw [hmass, zero_sub, abs_neg,
    abs_of_nonneg hempiricalNonnegative] at hcoordinate
  exact hcoordinate

theorem exists_indexRatio_gt
    {alpha : ℝ} (halpha : alpha < 1) :
    ∃ n : ℕ, alpha < ((n + 1 : ℕ) : ℝ) / (n + 2) := by
  have hgap : 0 < (1 : ℝ) - alpha := sub_pos.mpr halpha
  obtain ⟨n, hn⟩ :=
    exists_nat_one_div_lt hgap
  refine ⟨n, ?_⟩
  have hdenom : (0 : ℝ) < n + 2 := by positivity
  have hratio :
      ((n + 1 : ℕ) : ℝ) / (n + 2) =
        1 - 1 / (n + 2 : ℝ) := by
    field_simp
    push_cast
    ring
  have hinv :
      1 / (n + 2 : ℝ) ≤ 1 / (n + 1 : ℝ) := by
    apply one_div_le_one_div_of_le
    · positivity
    · norm_num
  rw [hratio]
  linarith

/-- No representative generator can become consistent on the dominant-block
presentation at any tolerance below one. -/
theorem no_eventually_consistent_alpha_representative_dominantBlocks
    {alpha : ℝ} (halphaPositive : 0 < alpha)
    (halphaOne : alpha < 1)
    (gen : RandomizedGenerator ℕ)
    (hrepresentative :
      IsAlphaRepresentative gen dominantBlockGroups alpha)
    (T : ℕ)
    (hconsistent :
      IsConsistentFrom gen tailLanguage identityEnumeration T) :
    False := by
  obtain ⟨m, hmRatio⟩ := exists_indexRatio_gt halphaOne
  let n := max m T
  have hindexRatio :
      alpha < ((n + 1 : ℕ) : ℝ) / (n + 2) := by
    have hmono :
        ((m + 1 : ℕ) : ℝ) / (m + 2) ≤
          ((n + 1 : ℕ) : ℝ) / (n + 2) := by
      have hmn : m ≤ n := Nat.le_max_left m T
      have hleft : (0 : ℝ) < m + 2 := by positivity
      have hright : (0 : ℝ) < n + 2 := by positivity
      rw [div_le_div_iff₀ hleft hright]
      push_cast
      have hmnReal : (m : ℝ) ≤ n := by
        exact_mod_cast hmn
      nlinarith
    exact hmRatio.trans_le hmono
  let t := dominantEndpoint (n + 1)
  have hTt : T ≤ t := by
    have hTn : T ≤ n := Nat.le_max_right m T
    have hnEndpoint : n ≤ dominantEndpoint n :=
      index_le_dominantEndpoint n
    exact hTn.trans
      (hnEndpoint.trans
        (Nat.le_of_lt (dominantEndpoint_lt_succ n)))
  have hconsistentAt :
      IsConsistentAt gen tailLanguage identityEnumeration t :=
    hconsistent t hTt
  have hlower :=
    empiricalGroupProbability_le_distance_of_consistent_dominantBlock
      n hconsistentAt
  have htPositive : 0 < t :=
    dominantEndpoint_succ_pos n
  have hupper :=
    hrepresentative identityEnumeration t htPositive
  have hempiricalGt :
      alpha <
        empiricalGroupProbability
          (GenLimit.Generic.sample identityEnumeration t)
          dominantBlockGroups n := by
    exact hindexRatio.trans
      (indexRatio_lt_empirical_identity_dominantBlock n)
  have hempiricalPositive :
      0 <
        empiricalGroupProbability
          (GenLimit.Generic.sample identityEnumeration t)
          dominantBlockGroups n :=
    halphaPositive.trans hempiricalGt
  have hofRealLt :
      ENNReal.ofReal alpha <
        ENNReal.ofReal
          (empiricalGroupProbability
            (GenLimit.Generic.sample identityEnumeration t)
            dominantBlockGroups n) :=
    (ENNReal.ofReal_lt_ofReal_iff hempiricalPositive).mpr
      hempiricalGt
  exact (not_lt_of_ge (hlower.trans hupper)) hofRealLt

theorem tailClass_not_alphaRepresentativelyGeneratableInLimit_dominantBlocks
    {alpha : ℝ} (halphaPositive : 0 < alpha)
    (halphaOne : alpha < 1) :
    ¬ AlphaRepresentativelyGeneratableInLimit
        tailClass dominantBlockGroups alpha := by
  rintro ⟨gen, hrepresentative, hlimit⟩
  have hL : tailLanguage ∈ tailClass := by
    simp [tailClass]
  obtain ⟨T, hconsistent⟩ :=
    hlimit tailLanguage hL identityEnumeration
      identity_presents_tailLanguage
  exact
    no_eventually_consistent_alpha_representative_dominantBlocks
      halphaPositive halphaOne gen hrepresentative T hconsistent

theorem tailClass_not_representativelyGeneratableInLimit_dominantBlocks :
    ¬ RepresentativelyGeneratableInLimit
        tailClass dominantBlockGroups := by
  intro hlimit
  have hhalf :
      AlphaRepresentativelyGeneratableInLimit
        tailClass dominantBlockGroups (1 / 2 : ℝ) :=
    (representativelyGeneratableInLimit_iff_forall_alpha.mp hlimit)
      (1 / 2 : ℝ) (by norm_num)
  exact
    tailClass_not_alphaRepresentativelyGeneratableInLimit_dominantBlocks
      (alpha := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hhalf

/-- Published-facing Lemma 4.3, with the printed quantifier order repaired by one
alpha-independent dominant-block partition. -/
theorem finiteSupport_necessity :
    ∃ groups : ℕ → Set ℕ,
      ∃ H : GenLimit.Generic.LanguageClass ℕ,
        IsCountablePartition groups ∧
        Function.Injective groups ∧
        (∀ n, (groups n).Nonempty) ∧
        H.Finite ∧
        H.ncard = 1 ∧
        GenLimit.Generic.UUS H ∧
        ¬ HasFiniteSupport H groups ∧
        ¬ RepresentativelyGeneratableInLimit H groups ∧
        ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
          ¬ AlphaRepresentativelyGeneratableInLimit
              H groups alpha := by
  exact
    ⟨dominantBlockGroups, tailClass,
      dominantBlockGroups_isCountablePartition,
      dominantBlockGroups_injective,
      dominantBlockGroups_nonempty,
      Set.finite_singleton tailLanguage,
      by simp [tailClass],
      tailClass_UUS,
      tailClass_not_hasFiniteSupport_dominantBlocks,
      tailClass_not_representativelyGeneratableInLimit_dominantBlocks,
      fun _alpha halphaPositive halphaOne =>
        tailClass_not_alphaRepresentativelyGeneratableInLimit_dominantBlocks
          halphaPositive halphaOne⟩

end GenLimit.RepresentativeGeneration
