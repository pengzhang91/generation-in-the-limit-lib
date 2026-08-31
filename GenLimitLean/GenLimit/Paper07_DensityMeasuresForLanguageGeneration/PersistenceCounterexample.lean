import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.DynamicComponent

/-!
# A dynamic-parent persistence counterexample

This module isolates the cross-round ancestor-persistence premise used in the
printed proof of Kleinberg--Wei Claim 6.11.  The final construction satisfies
the paper's global infinite-language and exact-presentation hypotheses, while
a still-consistent old ancestor disappears after one observation.  Thus a
formal proof of the density conclusion needs a different stateful invariant;
this module does not refute the conclusion of Claim 6.11 itself.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

open TowerTopology
open FiniteRankParent

namespace PersistenceCounterexample

def topLanguage : Language := Set.univ

def evenLanguage : Language := {x | x % 2 = 0}

def blockerLanguage : Language := {0, 1}

def childLanguage : Language := {0, 2}

def allPrefix (n : ℕ) : Language := Set.Iio n

def evenPrefix (n : ℕ) : Language := {x | x < n ∧ x % 2 = 0}

def family : LanguageFamily
  | 0 => topLanguage
  | 1 => blockerLanguage
  | 2 => evenLanguage
  | 3 => childLanguage
  | n + 4 =>
      if n % 2 = 0 then allPrefix (n / 2) else evenPrefix (n / 2)

abbrev X : Set Language := Set.range family

def topPoint : Point X := ⟨topLanguage, ⟨0, rfl⟩⟩

def evenPoint : Point X := ⟨evenLanguage, ⟨2, rfl⟩⟩

def childPoint : Point X := ⟨childLanguage, ⟨3, rfl⟩⟩

theorem allPrefix_mem_X (n : ℕ) : allPrefix n ∈ X := by
  refine ⟨2 * n + 4, ?_⟩
  simp [family]

theorem evenPrefix_mem_X (n : ℕ) : evenPrefix n ∈ X := by
  refine ⟨2 * n + 5, ?_⟩
  simp [family]
  congr 1
  omega

theorem allPrefix_finite (n : ℕ) : (allPrefix n).Finite := by
  exact Set.finite_Iio n

theorem evenPrefix_finite (n : ℕ) : (evenPrefix n).Finite := by
  apply (Set.finite_Iio n).subset
  intro x hx
  exact hx.1

theorem family_special_or_finite (i : ℕ) :
    family i = topLanguage ∨
      family i = evenLanguage ∨ (family i).Finite := by
  rcases i with _ | i
  · exact Or.inl rfl
  rcases i with _ | i
  · exact Or.inr (Or.inr (by simp [family, blockerLanguage]))
  rcases i with _ | i
  · exact Or.inr (Or.inl rfl)
  rcases i with _ | i
  · exact Or.inr (Or.inr (by simp [family, childLanguage]))
  simp only [family]
  split
  · exact Or.inr (Or.inr (allPrefix_finite _))
  · exact Or.inr (Or.inr (evenPrefix_finite _))

theorem finite_point_not_relativeLimitPoint
    {Y : Set (Point X)} {K : Point X}
    (hfinite : K.1.Finite) :
    ¬ RelativeLimitPoint Y K := by
  intro hlimit
  let F := hfinite.toFinset
  have hFK : (↑F : Set ℕ) ⊆ K.1 := by
    simp [F]
  obtain ⟨L, _hLY, hne, hLF⟩ := hlimit.2 F hFK
  apply hne
  apply Subtype.ext
  apply Set.Subset.antisymm hLF.2
  intro x hx
  exact hLF.1 (by simpa [F] using hx)

theorem derivative_one_subset :
    cbDerivative X 1 ⊆ {topPoint, evenPoint} := by
  intro K hK
  have hlimit : RelativeLimitPoint (Set.univ : Set (Point X)) K := by
    simpa [cbDerivative, derivative] using hK
  obtain ⟨i, hi⟩ := K.2
  have hcases := family_special_or_finite i
  rcases hcases with htop | heven | hfinite
  · have hval : K.1 = topLanguage := by simpa [hi] using htop
    have hpoint : K = topPoint := Subtype.ext hval
    simp [hpoint]
  · have hval : K.1 = evenLanguage := by simpa [hi] using heven
    have hpoint : K = evenPoint := Subtype.ext hval
    simp [hpoint]
  · have hKfinite : K.1.Finite := by simpa [hi] using hfinite
    exact (finite_point_not_relativeLimitPoint hKfinite hlimit).elim

theorem top_mem_derivative_one :
    topPoint ∈ cbDerivative X 1 := by
  rw [cbDerivative_succ]
  refine ⟨by simp, ?_⟩
  intro F _hF
  by_cases hne : F.Nonempty
  · let N := F.max' hne + 1
    let L : Point X := ⟨allPrefix N, allPrefix_mem_X N⟩
    refine ⟨L, by simp, ?_, ?_⟩
    · intro heq
      have hsets : allPrefix N = topLanguage :=
        congrArg Subtype.val heq
      have hNtop : N ∈ topLanguage := by simp [topLanguage]
      have hNprefix : N ∉ allPrefix N := by simp [allPrefix]
      exact hNprefix (by simpa [hsets] using hNtop)
    · refine ⟨?_, ?_⟩
      · intro x hx
        have hxle : x ≤ F.max' hne := Finset.le_max' F x hx
        simpa [L, allPrefix, N] using (show x < N by omega)
      · change allPrefix N ⊆ topLanguage
        simp [topLanguage]
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    let L : Point X := ⟨allPrefix 0, allPrefix_mem_X 0⟩
    refine ⟨L, by simp, ?_, ?_⟩
    · intro heq
      have hsets : allPrefix 0 = topLanguage :=
        congrArg Subtype.val heq
      have htop : 0 ∈ topLanguage := by simp [topLanguage]
      have hnot : 0 ∉ allPrefix 0 := by simp [allPrefix]
      exact hnot (by simpa [hsets] using htop)
    · simp [hFempty, L, allPrefix]

theorem even_mem_derivative_one :
    evenPoint ∈ cbDerivative X 1 := by
  rw [cbDerivative_succ]
  refine ⟨by simp, ?_⟩
  intro F hF
  by_cases hne : F.Nonempty
  · let N := F.max' hne + 1
    let L : Point X := ⟨evenPrefix N, evenPrefix_mem_X N⟩
    refine ⟨L, by simp, ?_, ?_⟩
    · intro heq
      have hsets : evenPrefix N = evenLanguage :=
        congrArg Subtype.val heq
      have hEven : (2 * N) % 2 = 0 := by omega
      have hmem : 2 * N ∈ evenLanguage := hEven
      have hnot : 2 * N ∉ evenPrefix N := by
        simp [evenPrefix]
        omega
      exact hnot (by simpa [hsets] using hmem)
    · refine ⟨?_, ?_⟩
      · intro x hx
        have hxle : x ≤ F.max' hne := Finset.le_max' F x hx
        have hxEven : x % 2 = 0 := by
          simpa [evenPoint, evenLanguage] using hF hx
        exact ⟨by simpa [N] using (show x < N by omega), hxEven⟩
      · intro x hx
        exact hx.2
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    let L : Point X := ⟨evenPrefix 0, evenPrefix_mem_X 0⟩
    refine ⟨L, by simp, ?_, ?_⟩
    · intro heq
      have hsets : evenPrefix 0 = evenLanguage :=
        congrArg Subtype.val heq
      have hmem : 0 ∈ evenLanguage := by simp [evenLanguage]
      have hnot : 0 ∉ evenPrefix 0 := by simp [evenPrefix]
      exact hnot (by simpa [hsets] using hmem)
    · simp [hFempty, L, evenPrefix]

theorem finiteRank_two : FiniteRankAtMost X 2 := by
  unfold FiniteRankAtMost
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro K hK
  rw [cbDerivative_succ] at hK
  have hKclass := derivative_one_subset hK.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hKclass
  rcases hKclass with htop | heven
  · subst K
    obtain ⟨L, hLderiv, hne, hLnbhd⟩ :=
      hK.2 {1} (by
        intro x hx
        simp only [Finset.mem_coe, Finset.mem_singleton] at hx
        subst x
        simp [topPoint, topLanguage])
    have hLclass := derivative_one_subset hLderiv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hLclass
    rcases hLclass with hLtop | hLeven
    · exact hne hLtop
    · subst L
      exact (by decide : 1 % 2 ≠ 0) (hLnbhd.1 (by simp))
  · subst K
    obtain ⟨L, hLderiv, hne, hLnbhd⟩ :=
      hK.2 ∅ (by simp)
    have hLclass := derivative_one_subset hLderiv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hLclass
    rcases hLclass with hLtop | hLeven
    · subst L
      have hOneTop : 1 ∈ topLanguage := by simp [topLanguage]
      have hOneEven : 1 ∉ evenLanguage := by
        exact (by decide : 1 % 2 ≠ 0)
      exact hOneEven (hLnbhd.2 hOneTop)
    · exact hne hLeven

theorem top_level_one :
    topPoint ∈ cbLevel X 1 := by
  exact ⟨top_mem_derivative_one, by
    intro h
    have hempty : cbDerivative X 2 = ∅ := finiteRank_two
    rw [hempty] at h
    exact Set.notMem_empty _ h⟩

theorem even_level_one :
    evenPoint ∈ cbLevel X 1 := by
  exact ⟨even_mem_derivative_one, by
    intro h
    have hempty : cbDerivative X 2 = ∅ := finiteRank_two
    rw [hempty] at h
    exact Set.notMem_empty _ h⟩

theorem child_level_zero :
    childPoint ∈ cbLevel X 0 := by
  refine ⟨by simp, ?_⟩
  intro hderiv
  have hlimit : RelativeLimitPoint (Set.univ : Set (Point X)) childPoint := by
    simpa [cbDerivative, derivative] using hderiv
  exact finite_point_not_relativeLimitPoint
    (by simp [childPoint, childLanguage]) hlimit

theorem level_top :
    levelOf finiteRank_two (familyPoint family 0) = 1 := by
  apply levelOf_eq_of_mem_cbLevel
  simpa [familyPoint, topPoint] using top_level_one

theorem level_even :
    levelOf finiteRank_two (familyPoint family 2) = 1 := by
  apply levelOf_eq_of_mem_cbLevel
  simpa [familyPoint, evenPoint] using even_level_one

theorem level_child :
    levelOf finiteRank_two (familyPoint family 3) = 0 := by
  apply levelOf_eq_of_mem_cbLevel
  simpa [familyPoint, childPoint] using child_level_zero

def stream : ℕ → ℕ
  | 0 => 0
  | _ + 1 => 2

theorem sample_one : sample stream 1 = {0} := by
  ext x
  simp [sample, stream]

theorem sample_two : sample stream 2 = {0, 2} := by
  ext x
  rw [mem_sample_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hsCases : s = 0 ∨ s = 1 := by omega
    rcases hsCases with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩

theorem remaining_top (round : ℕ) :
    RemainingAt family stream round (familyPoint family 0) := by
  intro x _
  simp [familyPoint, family, topLanguage]

theorem remaining_child_zero :
    RemainingAt family stream 0 (familyPoint family 3) := by
  intro x hx
  rw [sample_one] at hx
  simp only [Finset.mem_coe, Finset.mem_singleton] at hx
  subst x
  simp [familyPoint, family, childLanguage]

theorem remaining_child_one :
    RemainingAt family stream 1 (familyPoint family 3) := by
  intro x hx
  rw [sample_two] at hx
  simp only [Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;>
    simp [familyPoint, family, childLanguage]

theorem remaining_even_one :
    RemainingAt family stream 1 (familyPoint family 2) := by
  intro x hx
  rw [sample_two] at hx
  simp only [Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;>
    simp [familyPoint, family, evenLanguage]

theorem remaining_blocker_zero :
    RemainingAt family stream 0 (familyPoint family 1) := by
  intro x hx
  rw [sample_one] at hx
  simp only [Finset.mem_coe, Finset.mem_singleton] at hx
  subst x
  simp [familyPoint, family, blockerLanguage]

theorem blocker_purged_one :
    ¬ RemainingAt family stream 1 (familyPoint family 1) := by
  intro h
  have htwo : 2 ∈ sample stream 2 := by
    rw [sample_two]
    simp
  have := h htwo
  simp [familyPoint, family, blockerLanguage] at this

theorem top_critical (stage : ℕ) :
    StrictCritical family stream stage 0 := by
  refine ⟨?_, ?_⟩
  · intro x _
    simp [family, topLanguage]
  · intro i hi
    omega

theorem even_critical_one :
    StrictCritical family stream 2 2 := by
  refine ⟨?_, ?_⟩
  · simpa [Consistent, RemainingAt] using remaining_even_one
  · intro i hi hiconsistent
    have hiCases : i = 0 ∨ i = 1 := by omega
    rcases hiCases with rfl | rfl
    · refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro x hx
        simp [family, topLanguage]
      · intro heq
        have hOne : 1 ∈ topLanguage := by simp [topLanguage]
        have hNot : 1 ∉ evenLanguage := by
          simp [evenLanguage]
        have hsets : evenLanguage = topLanguage := by
          simpa [family] using heq
        apply hNot
        rw [hsets]
        exact hOne
    · exact (blocker_purged_one (by
        simpa [Consistent, RemainingAt] using hiconsistent)).elim

def childZero : RemainingPoint family stream 0 :=
  ⟨familyPoint family 3, remaining_child_zero⟩

def childOne : RemainingPoint family stream 1 :=
  ⟨familyPoint family 3, remaining_child_one⟩

def topZero : RemainingPoint family stream 0 :=
  ⟨familyPoint family 0, remaining_top 0⟩

def topOne : RemainingPoint family stream 1 :=
  ⟨familyPoint family 0, remaining_top 1⟩

def evenOne : RemainingPoint family stream 1 :=
  ⟨familyPoint family 2, remaining_even_one⟩

theorem child_ssubset_top : childLanguage ⊂ topLanguage := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨by simp [topLanguage], ?_⟩
  intro heq
  have hOne : 1 ∈ topLanguage := by simp [topLanguage]
  have hNot : 1 ∉ childLanguage := by simp [childLanguage]
  exact hNot (by simpa [heq] using hOne)

theorem child_ssubset_even : childLanguage ⊂ evenLanguage := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    simp only [childLanguage, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [evenLanguage]
  · intro heq
    have hFour : 4 ∈ evenLanguage := by simp [evenLanguage]
    have hNot : 4 ∉ childLanguage := by simp [childLanguage]
    exact hNot (by simpa [heq] using hFour)

theorem top_candidate_zero :
    ParentCandidate family stream 2 finiteRank_two 0 childZero 0 := by
  exact ⟨top_critical 1, child_ssubset_top, by
    simp [childZero, level_child, level_top]⟩

theorem top_candidate_one :
    ParentCandidate family stream 2 finiteRank_two 1 childOne 0 := by
  exact ⟨top_critical 2, child_ssubset_top, by
    simp [childOne, level_child, level_top]⟩

theorem even_candidate_one :
    ParentCandidate family stream 2 finiteRank_two 1 childOne 2 := by
  exact ⟨even_critical_one, child_ssubset_even, by
    simp [childOne, level_child, level_even]⟩

theorem positive_level_point_eq_top_or_even
    (n : ℕ)
    (hpositive :
      0 < levelOf finiteRank_two (familyPoint family n)) :
    familyPoint family n = topPoint ∨
      familyPoint family n = evenPoint := by
  have hlt :
      levelOf finiteRank_two (familyPoint family n) < 2 :=
    levelOf_lt finiteRank_two _
  have hlevel :
      levelOf finiteRank_two (familyPoint family n) = 1 := by
    omega
  have hmem :=
    mem_cbLevel_levelOf finiteRank_two (familyPoint family n)
  rw [hlevel] at hmem
  have hclass := derivative_one_subset hmem.1
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hclass

theorem critical_top_index_zero
    {stage n : ℕ}
    (hcritical : StrictCritical family stream stage n)
    (heq : familyPoint family n = topPoint) :
    n = 0 := by
  by_contra hn
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  have hproper :=
    hcritical.2 0 hpos (top_critical stage).1
  have hsets : family n = family 0 := by
    have hval := congrArg Subtype.val heq
    simpa [familyPoint, topPoint, family] using hval
  exact hproper.ne hsets

theorem critical_even_round_zero_impossible
    {n : ℕ}
    (hcritical : StrictCritical family stream 1 n)
    (heq : familyPoint family n = evenPoint) :
    False := by
  have hval : family n = evenLanguage := by
    have h := congrArg Subtype.val heq
    simpa [familyPoint, evenPoint] using h
  by_cases hn : n ≤ 1
  · have hnCases : n = 0 ∨ n = 1 := by omega
    rcases hnCases with rfl | rfl
    · have hOneTop : 1 ∈ family 0 := by
        simp [family, topLanguage]
      have hOneNotEven : 1 ∉ evenLanguage := by
        simp [evenLanguage]
      exact hOneNotEven (by simpa [hval] using hOneTop)
    · have hTwoBlocker : 2 ∉ family 1 := by
        simp [family, blockerLanguage]
      have hTwoEven : 2 ∈ evenLanguage := by simp [evenLanguage]
      exact hTwoBlocker (by simpa [hval] using hTwoEven)
  · have hOneLt : 1 < n := by omega
    have hproper :=
      hcritical.2 1 hOneLt (by
        simpa [Consistent, RemainingAt] using remaining_blocker_zero)
    have hTwoEven : 2 ∈ family n := by
      simpa [hval] using (show 2 ∈ evenLanguage by simp [evenLanguage])
    have hTwoNotBlocker : 2 ∉ family 1 := by
      simp [family, blockerLanguage]
    exact hTwoNotBlocker (hproper.le hTwoEven)

theorem critical_even_round_one_index_two
    {n : ℕ}
    (hcritical : StrictCritical family stream 2 n)
    (heq : familyPoint family n = evenPoint) :
    n = 2 := by
  have hval : family n = evenLanguage := by
    have h := congrArg Subtype.val heq
    simpa [familyPoint, evenPoint] using h
  by_contra hn
  rcases lt_or_gt_of_ne hn with hnlt | hngt
  · have hnCases : n = 0 ∨ n = 1 := by omega
    rcases hnCases with rfl | rfl
    · have hOneTop : 1 ∈ family 0 := by
        simp [family, topLanguage]
      have hOneNotEven : 1 ∉ evenLanguage := by
        simp [evenLanguage]
      exact hOneNotEven (by simpa [hval] using hOneTop)
    · have hTwoBlocker : 2 ∉ family 1 := by
        simp [family, blockerLanguage]
      have hTwoEven : 2 ∈ evenLanguage := by simp [evenLanguage]
      exact hTwoBlocker (by simpa [hval] using hTwoEven)
  · have hproper :=
      hcritical.2 2 hngt even_critical_one.1
    have hsets : family n = family 2 := by
      simpa [family] using hval
    exact hproper.ne hsets

theorem candidate_zero_index
    {n : ℕ}
    (h :
      ParentCandidate family stream 2 finiteRank_two 0 childZero n) :
    n = 0 := by
  have hpositive :
      0 < levelOf finiteRank_two (familyPoint family n) := by
    simpa [childZero, level_child] using h.2.2
  rcases positive_level_point_eq_top_or_even n hpositive with
      htop | heven
  · exact critical_top_index_zero h.1 htop
  · exact (critical_even_round_zero_impossible h.1 heven).elim

theorem candidate_one_index
    {n : ℕ}
    (h :
      ParentCandidate family stream 2 finiteRank_two 1 childOne n) :
    n = 0 ∨ n = 2 := by
  have hpositive :
      0 < levelOf finiteRank_two (familyPoint family n) := by
    simpa [childOne, level_child] using h.2.2
  rcases positive_level_point_eq_top_or_even n hpositive with
      htop | heven
  · exact Or.inl (critical_top_index_zero h.1 htop)
  · exact Or.inr (critical_even_round_one_index_two h.1 heven)

theorem candidateSet_zero :
    parentCandidateSet family stream 2 finiteRank_two 0 childZero =
      {0} := by
  ext n
  constructor
  · intro hn
    have h := candidate_zero_index hn
    simp [h]
  · intro hn
    have h : n = 0 := by simpa using hn
    subst n
    exact top_candidate_zero

theorem candidateSet_one :
    parentCandidateSet family stream 2 finiteRank_two 1 childOne =
      {0, 2} := by
  ext n
  constructor
  · intro hn
    rcases candidate_one_index hn with h | h
    · simp [h]
    · simp [h]
  · intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl
    · exact top_candidate_one
    · exact even_candidate_one

theorem parentIndex_zero :
    parentIndexAt family stream 2 finiteRank_two 0 childZero = some 0 := by
  classical
  unfold parentIndexAt
  dsimp only
  rw [candidateSet_zero]
  simp

theorem parentIndex_one :
    parentIndexAt family stream 2 finiteRank_two 1 childOne = some 2 := by
  classical
  unfold parentIndexAt
  dsimp only
  rw [candidateSet_one]
  simp

theorem edge_child_top_zero :
    EdgeAt family stream 2 finiteRank_two 0 childZero topZero := by
  change
    (parentIndexAt family stream 2 finiteRank_two 0 childZero).map
        (familyPoint family) =
      some topZero.1
  rw [parentIndex_zero]
  rfl

theorem edge_child_even_one :
    EdgeAt family stream 2 finiteRank_two 1 childOne evenOne := by
  change
    (parentIndexAt family stream 2 finiteRank_two 1 childOne).map
        (familyPoint family) =
      some evenOne.1
  rw [parentIndex_one]
  rfl

theorem evenOne_ne_topOne : evenOne ≠ topOne := by
  intro heq
  have hsets : evenLanguage = topLanguage := by
    have h := congrArg (fun p => p.1.1) heq
    simpa [evenOne, topOne, familyPoint, family] using h
  have hOneTop : 1 ∈ topLanguage := by simp [topLanguage]
  have hOneNotEven : 1 ∉ evenLanguage := by simp [evenLanguage]
  apply hOneNotEven
  rw [hsets]
  exact hOneTop

theorem ancestor_top_zero :
    AncestorAt family stream 2 finiteRank_two 0 childZero topZero :=
  edge_ancestorAt edge_child_top_zero

theorem not_ancestor_top_one :
    ¬ AncestorAt family stream 2 finiteRank_two 1 childOne topOne := by
  intro htop
  have heven :
      AncestorAt family stream 2 finiteRank_two 1 childOne evenOne :=
    edge_ancestorAt edge_child_even_one
  have hlevel :
      levelOf finiteRank_two evenOne.1 =
        levelOf finiteRank_two topOne.1 := by
    simp [evenOne, topOne, level_even, level_top]
  have heq : evenOne = topOne :=
    ancestor_level_injective heven htop hlevel
  exact evenOne_ne_topOne heq

/-- The exact parent forest can lose a still-consistent ancestor even when
the semantic child language is unchanged.  At round zero the only eligible
level-one parent is `topLanguage`.  Revealing `2` purges the finite blocker,
makes `evenLanguage` strictly critical, and the finite maximum-index branch
rewires the child to `evenLanguage`.  Both possible parents have level one,
so `topLanguage` is no longer on the path. -/
theorem still_consistent_ancestor_not_persistent :
    RemainingAt family stream 1 (familyPoint family 0) ∧
      (childZero.1 = childOne.1) ∧
      AncestorAt family stream 2 finiteRank_two 0 childZero topZero ∧
      ¬ AncestorAt family stream 2 finiteRank_two 1 childOne topOne := by
  exact ⟨remaining_top 1, rfl, ancestor_top_zero, not_ancestor_top_one⟩

/-- What survives from the failed temporal-persistence intuition at one
fixed round.  If `m` is an eligible parent candidate, the selected path
either reaches its language or reaches a sublanguage already at least as
high in Cantor--Bendixson level. -/
theorem fixed_round_replacement
    {C : LanguageFamily} {stream : ℕ → ℕ} {r round m : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    (hmround : m ≤ round)
    (child : RemainingPoint C stream round)
    (hmcritical : StrictCritical C stream (round + 1) m)
    (hproper : child.1.1 ⊂ C m)
    (hlevel :
      levelOf hr child.1 < levelOf hr (familyPoint C m)) :
    ∃ replacement : RemainingPoint C stream round,
      ProperAncestorAt C stream r hr round child replacement ∧
        replacement.1.1 ⊆ C m ∧
          (replacement.1.1 = C m ∨
            levelOf hr (familyPoint C m) ≤
              levelOf hr replacement.1) := by
  let rec ascend
      (current : RemainingPoint C stream round)
      (hcurrentProper : current.1.1 ⊂ C m)
      (hcurrentLevel :
        levelOf hr current.1 < levelOf hr (familyPoint C m)) :
      ∃ replacement : RemainingPoint C stream round,
        ProperAncestorAt C stream r hr round current replacement ∧
          replacement.1.1 ⊆ C m ∧
            (replacement.1.1 = C m ∨
              levelOf hr (familyPoint C m) ≤
                levelOf hr replacement.1) := by
    have hcand :
        ParentCandidate C stream r hr round current m :=
      ⟨hmcritical, hcurrentProper, hcurrentLevel⟩
    obtain ⟨parent, hedge, hparentSub⟩ :=
      exists_parent_edge_subset_candidate hmround hcand
    by_cases hparentEq : parent.1.1 = C m
    · exact
        ⟨parent, Relation.TransGen.single hedge,
          hparentSub, Or.inl hparentEq⟩
    by_cases hparentHigh :
        levelOf hr (familyPoint C m) ≤ levelOf hr parent.1
    · exact
        ⟨parent, Relation.TransGen.single hedge,
          hparentSub, Or.inr hparentHigh⟩
    · have hparentProper : parent.1.1 ⊂ C m :=
        Set.ssubset_iff_subset_ne.mpr ⟨hparentSub, hparentEq⟩
      have hparentLevel :
          levelOf hr parent.1 < levelOf hr (familyPoint C m) :=
        Nat.lt_of_not_ge hparentHigh
      obtain ⟨replacement, hpath, hsub, hstop⟩ :=
        ascend parent hparentProper hparentLevel
      exact
        ⟨replacement, Relation.TransGen.head hedge hpath,
          hsub, hstop⟩
    termination_by
      levelOf hr (familyPoint C m) - levelOf hr current.1
    decreasing_by
      have hstep :
          levelOf hr current.1 < levelOf hr parent.1 :=
        (edge_strict_level_and_inclusion hedge).1
      exact Nat.sub_lt_sub_left hcurrentLevel hstep
  exact ascend child hproper hlevel

/-- A viable repair for the source's cross-round step: compare the persistent
fallback and the new identified language inside one old forest.  Every common
ancestor then climbs strictly above the fallback whenever the new language
escapes it by inclusion. -/
theorem old_forest_commonAncestor_climbs_on_escape
    {C : LanguageFamily} {stream : ℕ → ℕ} {r round : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {fallback newGuess common :
      RemainingPoint C stream round}
    (hfallback :
      AncestorAt C stream r hr round fallback common)
    (hnew :
      AncestorAt C stream r hr round newGuess common)
    (hescape : ¬ newGuess.1.1 ⊆ fallback.1.1) :
    ProperAncestorAt C stream r hr round fallback common ∧
      levelOf hr fallback.1 < levelOf hr common.1 ∧
        fallback.1.1 ⊂ common.1.1 := by
  have hne : fallback ≠ common := by
    intro heq
    subst common
    exact hescape (ancestorAt_subset hnew)
  have hproper :
      ProperAncestorAt C stream r hr round fallback common := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hfallback with
      heq | hpath
    · exact (hne heq.symm).elim
    · exact hpath
  exact ⟨hproper, properAncestorAt_strict hproper⟩

/-! ## Infinite-language padding -/

/-- Add every even number as common infinite ballast and encode membership
in the original language on the odd numbers. -/
def padLanguage (A : Language) : Language :=
  {y | y % 2 = 0 ∨ (y % 2 = 1 ∧ y / 2 ∈ A)}

@[simp] theorem even_mem_padLanguage (A : Language) (n : ℕ) :
    2 * n ∈ padLanguage A := by
  simp [padLanguage]

@[simp] theorem odd_mem_padLanguage_iff (A : Language) (n : ℕ) :
    2 * n + 1 ∈ padLanguage A ↔ n ∈ A := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [padLanguage, hdiv]

theorem padLanguage_infinite (A : Language) :
    (padLanguage A).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n => 2 * n)
  · intro a b hab
    simp [Nat.succ_mul] at hab
    omega
  · exact even_mem_padLanguage A

theorem padLanguage_subset_iff {A B : Language} :
    padLanguage A ⊆ padLanguage B ↔ A ⊆ B := by
  constructor
  · intro h x hx
    have hodd : 2 * x + 1 ∈ padLanguage A := by
      simpa using hx
    simpa using h hodd
  · intro h y hy
    rcases hy with heven | ⟨hodd, hyA⟩
    · exact Or.inl heven
    · exact Or.inr ⟨hodd, h hyA⟩

theorem padLanguage_injective : Function.Injective padLanguage := by
  intro A B h
  apply Set.Subset.antisymm
  · exact padLanguage_subset_iff.mp (by simp [h])
  · exact padLanguage_subset_iff.mp (by simp [h])

def paddedFamily : LanguageFamily :=
  fun i => padLanguage (family i)

abbrev paddedX : Set Language := Set.range paddedFamily

def padPoint (K : Point X) : Point paddedX := by
  refine ⟨padLanguage K.1, ?_⟩
  obtain ⟨i, hi⟩ := K.2
  refine ⟨i, ?_⟩
  simpa [paddedFamily] using congrArg padLanguage hi

@[simp] theorem padPoint_val (K : Point X) :
    (padPoint K).1 = padLanguage K.1 :=
  rfl

theorem padPoint_injective : Function.Injective padPoint := by
  intro K L h
  apply Subtype.ext
  apply padLanguage_injective
  exact congrArg Subtype.val h

theorem padPoint_surjective : Function.Surjective padPoint := by
  intro L
  obtain ⟨i, hi⟩ := L.2
  refine ⟨familyPoint family i, ?_⟩
  apply Subtype.ext
  simpa [padPoint, paddedFamily, familyPoint] using hi

noncomputable def padPointEquiv : Point X ≃ Point paddedX :=
  Equiv.ofBijective padPoint
    ⟨padPoint_injective, padPoint_surjective⟩

@[simp] theorem padPointEquiv_apply (K : Point X) :
    padPointEquiv K = padPoint K :=
  rfl

noncomputable def encodeFinset (F : Finset ℕ) : Finset ℕ :=
  F.image fun x => 2 * x + 1

noncomputable def decodeFinset (G : Finset ℕ) : Finset ℕ :=
  (G.filter fun y => y % 2 = 1).image fun y => y / 2

@[simp] theorem mem_encodeFinset {F : Finset ℕ} {y : ℕ} :
    y ∈ encodeFinset F ↔ ∃ x ∈ F, 2 * x + 1 = y := by
  classical
  simp [encodeFinset]

@[simp] theorem mem_decodeFinset {G : Finset ℕ} {x : ℕ} :
    x ∈ decodeFinset G ↔
      ∃ y ∈ G, y % 2 = 1 ∧ y / 2 = x := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, hydiv⟩ :=
      Finset.mem_image.mp (show x ∈
        (G.filter fun y => y % 2 = 1).image (fun y => y / 2) from hx)
    exact ⟨y, (Finset.mem_filter.mp hy).1,
      (Finset.mem_filter.mp hy).2, hydiv⟩
  · rintro ⟨y, hyG, hyOdd, hydiv⟩
    apply Finset.mem_image.mpr
    exact ⟨y, Finset.mem_filter.mpr ⟨hyG, hyOdd⟩, hydiv⟩

theorem encodeFinset_subset_pad
    {F : Finset ℕ} {A : Language}
    (hFA : (↑F : Set ℕ) ⊆ A) :
    (↑(encodeFinset F) : Set ℕ) ⊆ padLanguage A := by
  intro y hy
  obtain ⟨x, hxF, rfl⟩ := mem_encodeFinset.mp hy
  simpa using hFA hxF

theorem decodeFinset_subset
    {G : Finset ℕ} {A : Language}
    (hGA : (↑G : Set ℕ) ⊆ padLanguage A) :
    (↑(decodeFinset G) : Set ℕ) ⊆ A := by
  intro x hx
  obtain ⟨y, hyG, hyOdd, rfl⟩ := mem_decodeFinset.mp hx
  have hy := hGA hyG
  rcases hy with hyEven | ⟨_hyOdd, hyA⟩
  · omega
  · exact hyA

theorem subset_pad_of_decode_subset
    {G : Finset ℕ} {A : Language}
    (hdecode : (↑(decodeFinset G) : Set ℕ) ⊆ A) :
    (↑G : Set ℕ) ⊆ padLanguage A := by
  intro y hy
  by_cases hEven : y % 2 = 0
  · exact Or.inl hEven
  · have hOdd : y % 2 = 1 := by
      have hlt := Nat.mod_lt y (by omega : 0 < 2)
      omega
    refine Or.inr ⟨hOdd, hdecode ?_⟩
    apply mem_decodeFinset.mpr
    exact ⟨y, hy, hOdd, rfl⟩

theorem encoded_subset_of_pad_subset
    {F : Finset ℕ} {A : Language}
    (h : (↑(encodeFinset F) : Set ℕ) ⊆ padLanguage A) :
    (↑F : Set ℕ) ⊆ A := by
  intro x hx
  have hodd : 2 * x + 1 ∈ encodeFinset F :=
    mem_encodeFinset.mpr ⟨x, hx, rfl⟩
  simpa using h hodd

/-- Padding is an isomorphism for every finite Cantor--Bendixson
derivative.  Even ballast in a finite neighbourhood is automatic, while
its odd part decodes to a finite neighbourhood before padding. -/
theorem mem_cbDerivative_padPoint_iff (n : ℕ) (K : Point X) :
    padPoint K ∈ cbDerivative paddedX n ↔
      K ∈ cbDerivative X n := by
  induction n generalizing K with
  | zero =>
      simp
  | succ n ih =>
      rw [cbDerivative_succ, cbDerivative_succ]
      constructor
      · rintro ⟨hK, hlimit⟩
        refine ⟨(ih K).mp hK, ?_⟩
        intro F hFK
        have hencoded :
            (↑(encodeFinset F) : Set ℕ) ⊆ (padPoint K).1 := by
          simpa using encodeFinset_subset_pad hFK
        obtain ⟨Lp, hLp, hne, hnear⟩ :=
          hlimit (encodeFinset F) hencoded
        obtain ⟨L, rfl⟩ := padPoint_surjective Lp
        refine ⟨L, (ih L).mp hLp, ?_, ?_⟩
        · intro hLK
          exact hne (congrArg padPoint hLK)
        · exact
            ⟨encoded_subset_of_pad_subset (by simpa using hnear.1),
              padLanguage_subset_iff.mp (by simpa using hnear.2)⟩
      · rintro ⟨hK, hlimit⟩
        refine ⟨(ih K).mpr hK, ?_⟩
        intro G hGK
        have hdecoded :
            (↑(decodeFinset G) : Set ℕ) ⊆ K.1 :=
          decodeFinset_subset (by simpa using hGK)
        obtain ⟨L, hLn, hne, hnear⟩ :=
          hlimit (decodeFinset G) hdecoded
        refine ⟨padPoint L, (ih L).mpr hLn, ?_, ?_⟩
        · intro hpad
          exact hne (padPoint_injective hpad)
        · exact
            ⟨subset_pad_of_decode_subset (by simpa using hnear.1),
              padLanguage_subset_iff.mpr (by simpa using hnear.2)⟩

theorem mem_cbLevel_padPoint_iff (n : ℕ) (K : Point X) :
    padPoint K ∈ cbLevel paddedX n ↔
      K ∈ cbLevel X n := by
  constructor
  · rintro ⟨hn, hnsucc⟩
    exact
      ⟨(mem_cbDerivative_padPoint_iff n K).mp hn,
        fun h => hnsucc
          ((mem_cbDerivative_padPoint_iff (n + 1) K).mpr h)⟩
  · rintro ⟨hn, hnsucc⟩
    exact
      ⟨(mem_cbDerivative_padPoint_iff n K).mpr hn,
        fun h => hnsucc
          ((mem_cbDerivative_padPoint_iff (n + 1) K).mp h)⟩

theorem paddedFiniteRank_two :
    FiniteRankAtMost paddedX 2 := by
  unfold FiniteRankAtMost
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro L hL
  obtain ⟨K, rfl⟩ := padPoint_surjective L
  have hK := (mem_cbDerivative_padPoint_iff 2 K).mp hL
  have hempty : cbDerivative X 2 = ∅ := finiteRank_two
  rw [hempty] at hK
  exact Set.notMem_empty K hK

theorem level_padPoint (K : Point X) :
    levelOf paddedFiniteRank_two (padPoint K) =
      levelOf finiteRank_two K := by
  apply levelOf_eq_of_mem_cbLevel
  apply (mem_cbLevel_padPoint_iff (levelOf finiteRank_two K) K).mpr
  exact mem_cbLevel_levelOf finiteRank_two K

theorem familyPoint_padded_eq (n : ℕ) :
    familyPoint paddedFamily n =
      padPoint (familyPoint family n) := by
  apply Subtype.ext
  rfl

theorem level_padded_familyPoint (n : ℕ) :
    levelOf paddedFiniteRank_two (familyPoint paddedFamily n) =
      levelOf finiteRank_two (familyPoint family n) := by
  rw [familyPoint_padded_eq]
  exact level_padPoint (familyPoint family n)

theorem paddedFamily_all_infinite (n : ℕ) :
    (paddedFamily n).Infinite :=
  padLanguage_infinite (family n)

theorem padLanguage_ssubset_iff {A B : Language} :
    padLanguage A ⊂ padLanguage B ↔ A ⊂ B := by
  constructor
  · intro h
    refine Set.ssubset_iff_subset_ne.mpr
      ⟨padLanguage_subset_iff.mp h.le, ?_⟩
    intro hAB
    exact h.ne (congrArg padLanguage hAB)
  · intro h
    refine Set.ssubset_iff_subset_ne.mpr
      ⟨padLanguage_subset_iff.mpr h.le, ?_⟩
    intro hpad
    exact h.ne (padLanguage_injective hpad)

/-- The first two observations are the odd encodings of `0,2`; afterwards
the stream enumerates the common even ballast. -/
def paddedStream : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | n + 2 => 2 * n

theorem sample_stream_add_two (n : ℕ) :
    sample stream (n + 2) = {0, 2} := by
  ext x
  rw [mem_sample_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases s with _ | s
    · exact Or.inl (by simp [stream])
    · exact Or.inr (by simp [stream])
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨0, by omega, by simp [stream]⟩
    · exact ⟨1, by omega, by simp [stream]⟩

/-- Finite samples of the padded presentation decode to exactly the
corresponding finite samples of the original presentation.  Even
observations disappear under decoding because every padded language shares
them. -/
theorem decode_sample_padded (t : ℕ) :
    decodeFinset (sample paddedStream t) = sample stream t := by
  rcases t with _ | t
  · simp [sample, decodeFinset]
  rcases t with _ | t
  · ext x
    simp [sample, decodeFinset, paddedStream, stream, eq_comm]
  · rw [sample_stream_add_two]
    ext x
    rw [mem_decodeFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨y, hy, hyOdd, hydiv⟩
      obtain ⟨s, hs, rfl⟩ := mem_sample_iff.mp hy
      rcases s with _ | s
      · left
        simp [paddedStream] at hydiv
        omega
      · rcases s with _ | s
        · right
          simp [paddedStream] at hydiv
          omega
        · simp [paddedStream] at hyOdd
    · intro hx
      rcases hx with rfl | rfl
      · refine ⟨1, ?_, by decide, by decide⟩
        exact mem_sample_iff.mpr
          ⟨0, by omega, by simp [paddedStream]⟩
      · refine ⟨5, ?_, by decide, by decide⟩
        exact mem_sample_iff.mpr
          ⟨1, by omega, by simp [paddedStream]⟩

theorem paddedStream_presents_child :
    Presents paddedStream (paddedFamily 3) := by
  unfold Presents
  ext y
  simp only [Set.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    rcases t with _ | t
    · simp [paddedStream, paddedFamily, family,
        padLanguage, childLanguage]
    · rcases t with _ | t
      · simp [paddedStream, paddedFamily, family,
          padLanguage, childLanguage]
      · simp [paddedStream, paddedFamily, family,
          padLanguage, childLanguage]
  · intro hy
    change y ∈ padLanguage childLanguage at hy
    rcases hy with hEven | ⟨hOdd, hbase⟩
    · refine ⟨y / 2 + 2, ?_⟩
      simp [paddedStream]
      have hdecomp := Nat.mod_add_div y 2
      omega
    · simp only [childLanguage, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hbase
      rcases hbase with hzero | htwo
      · refine ⟨0, ?_⟩
        simp [paddedStream]
        have hdecomp := Nat.mod_add_div y 2
        omega
      · refine ⟨1, ?_⟩
        simp [paddedStream]
        have hdecomp := Nat.mod_add_div y 2
        omega

theorem padded_consistent_iff (t n : ℕ) :
    Consistent paddedFamily paddedStream t n ↔
      Consistent family stream t n := by
  unfold Consistent
  constructor
  · intro h
    have hdecoded :=
      decodeFinset_subset (by simpa [paddedFamily] using h)
    simpa [decode_sample_padded] using hdecoded
  · intro h
    apply subset_pad_of_decode_subset
    simpa [decode_sample_padded] using h

theorem padded_strictCritical_iff (t n : ℕ) :
    StrictCritical paddedFamily paddedStream t n ↔
      StrictCritical family stream t n := by
  unfold StrictCritical
  constructor
  · rintro ⟨hn, hcritical⟩
    refine ⟨(padded_consistent_iff t n).mp hn, ?_⟩
    intro i hin hi
    exact padLanguage_ssubset_iff.mp
      (hcritical i hin ((padded_consistent_iff t i).mpr hi))
  · rintro ⟨hn, hcritical⟩
    refine ⟨(padded_consistent_iff t n).mpr hn, ?_⟩
    intro i hin hi
    exact padLanguage_ssubset_iff.mpr
      (hcritical i hin ((padded_consistent_iff t i).mp hi))

theorem remaining_padPoint_iff
    (round : ℕ) (K : FamilyPoint family) :
    RemainingAt paddedFamily paddedStream round (padPoint K) ↔
      RemainingAt family stream round K := by
  unfold RemainingAt
  constructor
  · intro h
    have hdecoded := decodeFinset_subset (by simpa using h)
    simpa [decode_sample_padded] using hdecoded
  · intro h
    apply subset_pad_of_decode_subset
    simpa [decode_sample_padded] using h

def padRemaining (round : ℕ)
    (K : RemainingPoint family stream round) :
    RemainingPoint paddedFamily paddedStream round :=
  ⟨padPoint K.1, (remaining_padPoint_iff round K.1).mpr K.2⟩

@[simp] theorem padRemaining_val (round : ℕ)
    (K : RemainingPoint family stream round) :
    (padRemaining round K).1 = padPoint K.1 :=
  rfl

theorem parentCandidate_pad_iff
    (round : ℕ) (child : RemainingPoint family stream round)
    (n : ℕ) :
    ParentCandidate paddedFamily paddedStream 2
        paddedFiniteRank_two round (padRemaining round child) n ↔
      ParentCandidate family stream 2
        finiteRank_two round child n := by
  unfold ParentCandidate
  rw [padded_strictCritical_iff]
  constructor
  · rintro ⟨hcritical, hproper, hlevel⟩
    refine ⟨hcritical, ?_, ?_⟩
    · exact padLanguage_ssubset_iff.mp (by
        simpa [padRemaining, paddedFamily] using hproper)
    · simpa [padRemaining, level_padPoint,
        level_padded_familyPoint] using hlevel
  · rintro ⟨hcritical, hproper, hlevel⟩
    refine ⟨hcritical, ?_, ?_⟩
    · simpa [padRemaining, paddedFamily] using
        padLanguage_ssubset_iff.mpr hproper
    · simpa [padRemaining, level_padPoint,
        level_padded_familyPoint] using hlevel

def paddedChildZero :
    RemainingPoint paddedFamily paddedStream 0 :=
  padRemaining 0 childZero

def paddedChildOne :
    RemainingPoint paddedFamily paddedStream 1 :=
  padRemaining 1 childOne

def paddedTopZero :
    RemainingPoint paddedFamily paddedStream 0 :=
  padRemaining 0 topZero

def paddedTopOne :
    RemainingPoint paddedFamily paddedStream 1 :=
  padRemaining 1 topOne

def paddedEvenOne :
    RemainingPoint paddedFamily paddedStream 1 :=
  padRemaining 1 evenOne

theorem candidateSet_pad
    (round : ℕ) (child : RemainingPoint family stream round) :
    parentCandidateSet paddedFamily paddedStream 2
        paddedFiniteRank_two round (padRemaining round child) =
      parentCandidateSet family stream 2
        finiteRank_two round child := by
  ext n
  exact parentCandidate_pad_iff round child n

theorem paddedCandidateSet_zero :
    parentCandidateSet paddedFamily paddedStream 2
        paddedFiniteRank_two 0 paddedChildZero = {0} := by
  change
    parentCandidateSet paddedFamily paddedStream 2
        paddedFiniteRank_two 0 (padRemaining 0 childZero) = {0}
  rw [candidateSet_pad, candidateSet_zero]

theorem paddedCandidateSet_one :
    parentCandidateSet paddedFamily paddedStream 2
        paddedFiniteRank_two 1 paddedChildOne = {0, 2} := by
  change
    parentCandidateSet paddedFamily paddedStream 2
        paddedFiniteRank_two 1 (padRemaining 1 childOne) = {0, 2}
  rw [candidateSet_pad, candidateSet_one]

theorem paddedParentIndex_zero :
    parentIndexAt paddedFamily paddedStream 2
        paddedFiniteRank_two 0 paddedChildZero = some 0 := by
  classical
  unfold parentIndexAt
  dsimp only
  rw [paddedCandidateSet_zero]
  simp

theorem paddedParentIndex_one :
    parentIndexAt paddedFamily paddedStream 2
        paddedFiniteRank_two 1 paddedChildOne = some 2 := by
  classical
  unfold parentIndexAt
  dsimp only
  rw [paddedCandidateSet_one]
  simp

theorem paddedEdge_child_top_zero :
    EdgeAt paddedFamily paddedStream 2 paddedFiniteRank_two
      0 paddedChildZero paddedTopZero := by
  change
    (parentIndexAt paddedFamily paddedStream 2
      paddedFiniteRank_two 0 paddedChildZero).map
        (familyPoint paddedFamily) =
      some paddedTopZero.1
  rw [paddedParentIndex_zero]
  apply congrArg some
  simpa [paddedTopZero, topZero] using familyPoint_padded_eq 0

theorem paddedEdge_child_even_one :
    EdgeAt paddedFamily paddedStream 2 paddedFiniteRank_two
      1 paddedChildOne paddedEvenOne := by
  change
    (parentIndexAt paddedFamily paddedStream 2
      paddedFiniteRank_two 1 paddedChildOne).map
        (familyPoint paddedFamily) =
      some paddedEvenOne.1
  rw [paddedParentIndex_one]
  apply congrArg some
  simpa [paddedEvenOne, evenOne] using familyPoint_padded_eq 2

theorem paddedEvenOne_ne_paddedTopOne :
    paddedEvenOne ≠ paddedTopOne := by
  intro heq
  apply evenOne_ne_topOne
  apply Subtype.ext
  apply padPoint_injective
  exact congrArg Subtype.val heq

theorem paddedAncestor_top_zero :
    AncestorAt paddedFamily paddedStream 2 paddedFiniteRank_two
      0 paddedChildZero paddedTopZero :=
  edge_ancestorAt paddedEdge_child_top_zero

theorem not_paddedAncestor_top_one :
    ¬ AncestorAt paddedFamily paddedStream 2 paddedFiniteRank_two
        1 paddedChildOne paddedTopOne := by
  intro htop
  have heven :
      AncestorAt paddedFamily paddedStream 2 paddedFiniteRank_two
        1 paddedChildOne paddedEvenOne :=
    edge_ancestorAt paddedEdge_child_even_one
  have hlevel :
      levelOf paddedFiniteRank_two paddedEvenOne.1 =
        levelOf paddedFiniteRank_two paddedTopOne.1 := by
    simp [paddedEvenOne, paddedTopOne, padRemaining,
      level_padPoint, evenOne, topOne, level_even, level_top]
  have heq : paddedEvenOne = paddedTopOne :=
    ancestor_level_injective heven htop hlevel
  exact paddedEvenOne_ne_paddedTopOne heq

/-- A counterexample satisfying the paper's global infinite-language and
exact-presentation assumptions.  The child and both possible parents are
infinite.  In fact every indexed language is infinite.  Nevertheless the
still-consistent old parent disappears from the child's ancestor path after
one new observation. -/
theorem infinite_languages_still_consistent_ancestor_not_persistent :
    (∀ n, (paddedFamily n).Infinite) ∧
      Presents paddedStream (paddedFamily 3) ∧
      RemainingAt paddedFamily paddedStream 1
        (familyPoint paddedFamily 0) ∧
      paddedChildZero.1 = paddedChildOne.1 ∧
      AncestorAt paddedFamily paddedStream 2 paddedFiniteRank_two
        0 paddedChildZero paddedTopZero ∧
      ¬ AncestorAt paddedFamily paddedStream 2 paddedFiniteRank_two
        1 paddedChildOne paddedTopOne := by
  refine ⟨paddedFamily_all_infinite,
    paddedStream_presents_child, ?_, ?_,
    paddedAncestor_top_zero, not_paddedAncestor_top_one⟩
  · have h := (remaining_padPoint_iff 1 (familyPoint family 0)).mpr
      (remaining_top 1)
    simpa [familyPoint_padded_eq] using h
  · rfl

end PersistenceCounterexample
end GenLimit.KleinbergWei.DensityMeasures
