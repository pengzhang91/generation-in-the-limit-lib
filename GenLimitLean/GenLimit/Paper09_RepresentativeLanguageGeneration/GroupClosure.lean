import GenLimit.Paper09_RepresentativeLanguageGeneration.Definitions

/-!
# Group closure dimension

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Definition 3.1 and Theorem 3.3.

Definition 3.1 is represented without taking a maximum over a potentially
empty index set: its first alternative is written as existence of a coordinate
larger than the tolerance.  In its second alternative, `|ℕ \ S|` is interpreted as an extended
cardinality.  Since the right side is finite, the strict inequality can hold
only when the complement is finite; `groupClosureConditionTwo` records exactly
that finite case.

This module also proves the local obstruction used in the necessity half of
Theorem 3.3: a distribution supported on the unseen closure cannot approximate
a group whose unseen closure intersection is empty and whose empirical mass
exceeds the tolerance.
-/

namespace GenLimit.RepresentativeGeneration

/-! ## Countable partitions and empirical group profiles -/

/-- The unique group containing a point of a countable partition. -/
noncomputable def partitionIndex
    (groups : ℕ → Set α) (hpartition : IsCountablePartition groups)
    (x : α) : ℕ := by
  classical
  have hx : x ∈ ⋃ i, groups i := by
    rw [hpartition.2]
    exact Set.mem_univ x
  exact Classical.choose (Set.mem_iUnion.mp hx)

theorem mem_partitionIndex
    (groups : ℕ → Set α) (hpartition : IsCountablePartition groups)
    (x : α) :
    x ∈ groups (partitionIndex groups hpartition x) := by
  classical
  exact Classical.choose_spec
    (Set.mem_iUnion.mp (by
      rw [hpartition.2]
      exact Set.mem_univ x))

theorem partitionIndex_eq_of_mem
    (groups : ℕ → Set α) (hpartition : IsCountablePartition groups)
    {x : α} {i : ℕ} (hxi : x ∈ groups i) :
    partitionIndex groups hpartition x = i := by
  by_contra hne
  have hdisjoint :=
    hpartition.1 (partitionIndex groups hpartition x) i hne
  exact Set.disjoint_left.mp hdisjoint
    (mem_partitionIndex groups hpartition x) hxi

theorem mem_group_iff_partitionIndex_eq
    (groups : ℕ → Set α) (hpartition : IsCountablePartition groups)
    (x : α) (i : ℕ) :
    x ∈ groups i ↔ partitionIndex groups hpartition x = i := by
  constructor
  · exact partitionIndex_eq_of_mem groups hpartition
  · rintro rfl
    exact mem_partitionIndex groups hpartition x

/-- The empirical group profile, embedded in `ENNReal`. -/
noncomputable def empiricalGroupENN
    (S : Finset α) (groups : ℕ → Set α) (i : ℕ) : ENNReal :=
  ENNReal.ofReal (empiricalGroupProbability S groups i)

theorem empiricalGroupENN_eq_zero_of_not_mem_image
    (S : Finset α) (groups : ℕ → Set α)
    (hpartition : IsCountablePartition groups) {i : ℕ}
    (hi : i ∉ S.image (partitionIndex groups hpartition)) :
    empiricalGroupENN S groups i = 0 := by
  classical
  have hfilter :
      S.filter (fun x => x ∈ groups i) = ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨hxS, hxi⟩
    apply hi
    rw [Finset.mem_image]
    exact ⟨x, hxS,
      partitionIndex_eq_of_mem groups hpartition hxi⟩
  simp [empiricalGroupENN, empiricalGroupProbability, hfilter]

/-- For a nonempty sample and a partition, the empirical group profile has
total mass one.  The proof is the finite fiber-counting identity behind
published Definition 2.6. -/
theorem tsum_empiricalGroupENN_eq_one
    (S : Finset α) (groups : ℕ → Set α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty) :
    ∑' i, empiricalGroupENN S groups i = 1 := by
  classical
  let idx := partitionIndex groups hpartition
  rw [tsum_eq_sum (s := S.image idx) (fun i hi =>
    empiricalGroupENN_eq_zero_of_not_mem_image
      S groups hpartition hi)]
  have hcardPos : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  simp only [empiricalGroupENN, empiricalGroupProbability, if_pos hS,
    ENNReal.ofReal_div_of_pos hcardPos, ENNReal.ofReal_natCast]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have hfiber :
      ∀ i ∈ S.image idx,
        (S.filter (fun x => x ∈ groups i)).card =
          (S.filter (fun x => idx x = i)).card := by
    intro i hi
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ =>
      mem_group_iff_partitionIndex_eq groups hpartition x i)
  have hsum :
      ∑ i ∈ S.image idx,
          ((S.filter (fun x => x ∈ groups i)).card : ENNReal) =
        S.card := by
    calc
      _ = ∑ i ∈ S.image idx,
          ((S.filter (fun x => idx x = i)).card : ENNReal) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact_mod_cast hfiber i hi
      _ = S.card := by
        exact_mod_cast
          (Finset.card_eq_sum_card_image idx S).symm
  rw [hsum]
  apply ENNReal.mul_inv_cancel
  · exact_mod_cast Finset.card_ne_zero.mpr hS
  · simp

/-! ## Redistributing empirical group mass -/

/-- The unseen portion of the closure after observing the distinct sample
`S`. -/
def unseenClosure
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    Set α :=
  commonCore H S \ (↑S : Set α)

/-- The set called `S` inside published Definition 3.1 (renamed to avoid collision with
the finite sample): groups with no unseen closure point. -/
def unavailableGroups
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α) : Set ℕ :=
  {i | unseenClosure H S ∩ groups i = ∅}

/-- The empirical mass assigned to a set of group indices.  `ENNReal` makes
the countable sum total; for a partition and finite nonempty sample it agrees
with the usual finite probability sum. -/
noncomputable def empiricalMassOnGroupIndices
    (S : Finset α) (groups : ℕ → Set α)
    (I : Set ℕ) : ENNReal := by
  classical
  exact
    ∑' i : ℕ,
      if i ∈ I then
        ENNReal.ofReal (empiricalGroupProbability S groups i)
      else
        0

theorem empiricalMass_add_compl
    (S : Finset α) (groups : ℕ → Set α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty) (I : Set ℕ) :
    empiricalMassOnGroupIndices S groups I +
        empiricalMassOnGroupIndices S groups Iᶜ = 1 := by
  classical
  unfold empiricalMassOnGroupIndices
  rw [← ENNReal.tsum_add]
  calc
    _ = ∑' i, empiricalGroupENN S groups i := by
      apply tsum_congr
      intro i
      by_cases hi : i ∈ I
      · unfold empiricalGroupENN
        simp [hi]
      · unfold empiricalGroupENN
        simp [hi]
    _ = 1 :=
      tsum_empiricalGroupENN_eq_one S groups hpartition hS

/-- A finite-support way to place `total` mass on the available coordinates,
using at most `cap` at each coordinate. -/
structure BoundedMassAllocation
    (available : Set ℕ) (cap total : ENNReal) where
  weight : ℕ → ENNReal
  support_subset : Function.support weight ⊆ available
  weight_le_cap : ∀ i, weight i ≤ cap
  total_weight : ∑' i, weight i = total

private noncomputable def equalMassOn
    (F : Finset ℕ) (total : ENNReal) (i : ℕ) : ENNReal :=
  if i ∈ F then total / F.card else 0

private theorem exists_capacity_finset
    {available : Set ℕ} {cap total : ENNReal}
    (hcap : cap ≠ 0) (htotal : total ≠ ⊤)
    (havailable : available.Nonempty)
    (hfiniteCapacity :
      ∀ hfinite : available.Finite,
        total ≤ cap * hfinite.toFinset.card) :
    ∃ F : Finset ℕ,
      F.Nonempty ∧ (↑F : Set ℕ) ⊆ available ∧
        total ≤ cap * F.card := by
  classical
  rcases available.finite_or_infinite with hfinite | hinfinite
  · refine ⟨hfinite.toFinset, ?_, ?_, hfiniteCapacity hfinite⟩
    · simpa only [Set.Finite.toFinset_nonempty] using havailable
    · intro i hi
      exact hfinite.mem_toFinset.mp hi
  · obtain ⟨n, hnpos, hn⟩ :=
      ENNReal.exists_nat_pos_mul_gt hcap htotal
    obtain ⟨F, hFsub, hFcard⟩ :=
      hinfinite.exists_subset_card_eq n
    have hFpos : 0 < F.card := by omega
    refine ⟨F, Finset.card_pos.mp hFpos,
      hFsub, ?_⟩
    rw [hFcard]
    exact le_of_lt (by simpa [mul_comm] using hn)

private theorem boundedMassAllocation_of_capacity
    {available : Set ℕ} {cap total : ENNReal}
    (hcap : cap ≠ 0) (htotal : total ≠ ⊤)
    (havailable : available.Nonempty)
    (hfiniteCapacity :
      ∀ hfinite : available.Finite,
        total ≤ cap * hfinite.toFinset.card) :
    Nonempty (BoundedMassAllocation available cap total) := by
  classical
  obtain ⟨F, hFnonempty, hFsub, hcapacity⟩ :=
    exists_capacity_finset hcap htotal havailable hfiniteCapacity
  let weight := equalMassOn F total
  refine ⟨{
    weight := weight
    support_subset := ?_
    weight_le_cap := ?_
    total_weight := ?_ }⟩
  · intro i hi
    have hiF : i ∈ F := by
      by_contra hnot
      exact hi (by simp [weight, equalMassOn, hnot])
    exact hFsub hiF
  · intro i
    by_cases hiF : i ∈ F
    · simp only [weight, equalMassOn, if_pos hiF]
      exact ENNReal.div_le_of_le_mul hcapacity
    · simp [weight, equalMassOn, hiF]
  · rw [show ∑' i, weight i = ∑ i ∈ F, weight i by
      apply tsum_eq_sum
      intro i hi
      simp [weight, equalMassOn, hi]]
    have hsum :
        ∑ i ∈ F, weight i =
          ∑ _i ∈ F, total / (F.card : ENNReal) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [weight, equalMassOn, hi]
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    exact ENNReal.mul_div_cancel
      (a := (F.card : ENNReal)) (b := total)
      (by exact_mod_cast Finset.card_ne_zero.mpr hFnonempty)
      (by simp)

/-- Alternative (1) in published Definition 3.1. -/
def groupClosureConditionOne
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (S : Finset α) : Prop :=
  ∃ i, i ∈ unavailableGroups H groups S ∧
    ENNReal.ofReal alpha <
      ENNReal.ofReal (empiricalGroupProbability S groups i)

/-- Alternative (2) in published Definition 3.1.

The source writes `α |ℕ \ S|`.  With extended cardinality this is infinite
when the available-index set is infinite, so its strict comparison with the
finite empirical mass is false.  The dependent finite-set witness below is
the literal finite-complement branch. -/
def groupClosureConditionTwo
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (S : Finset α) : Prop :=
  ∃ hfinite : (unavailableGroups H groups S)ᶜ.Finite,
    ENNReal.ofReal alpha * hfinite.toFinset.card <
      empiricalMassOnGroupIndices S groups
        (unavailableGroups H groups S)

theorem empiricalMassOnGroupIndices_le_one
    (S : Finset α) (groups : ℕ → Set α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty) (I : Set ℕ) :
    empiricalMassOnGroupIndices S groups I ≤ 1 := by
  classical
  have hle :
      empiricalMassOnGroupIndices S groups I ≤
        ∑' i, empiricalGroupENN S groups i := by
    unfold empiricalMassOnGroupIndices
    apply ENNReal.tsum_le_tsum
    intro i
    by_cases hi : i ∈ I
    · unfold empiricalGroupENN
      simp [hi]
    · simp [hi]
  rwa [tsum_empiricalGroupENN_eq_one
    S groups hpartition hS] at hle

/-- Negating condition (2) is exactly the capacity inequality needed by the
paper's countable redistribution argument.  This theorem performs that
argument uniformly in the finite- and infinite-available-group cases. -/
theorem boundedMassAllocation_of_not_groupClosureConditionTwo
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ} {S : Finset α}
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha) (hS : S.Nonempty)
    (hnot :
      ¬groupClosureConditionTwo H groups alpha S) :
    Nonempty
      (BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S))) := by
  classical
  let unavailable := unavailableGroups H groups S
  let available := unavailableᶜ
  let total :=
    empiricalMassOnGroupIndices S groups unavailable
  have hcap : ENNReal.ofReal alpha ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr halpha
  have htotal : total ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact empiricalMassOnGroupIndices_le_one
      S groups hpartition hS unavailable
  have havailable : available.Nonempty := by
    by_contra hnone
    have hempty : available = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnone
    have hfinite : available.Finite := by
      rw [hempty]
      exact Set.finite_empty
    have htotalOne : total = 1 := by
      have hadd :=
        empiricalMass_add_compl S groups hpartition hS unavailable
      have hzero :
          empiricalMassOnGroupIndices S groups unavailableᶜ = 0 := by
        rw [show unavailableᶜ = available by rfl, hempty]
        unfold empiricalMassOnGroupIndices
        simp
      simpa [total, hzero] using hadd
    apply hnot
    refine ⟨hfinite, ?_⟩
    change
      ENNReal.ofReal alpha * hfinite.toFinset.card < total
    rw [htotalOne]
    have hfinsetEmpty : hfinite.toFinset = ∅ := by
      ext i
      simp only [hfinite.mem_toFinset, Finset.notMem_empty,
        iff_false]
      intro hi
      rw [hempty] at hi
      exact hi
    rw [hfinsetEmpty]
    simp
  apply boundedMassAllocation_of_capacity
    hcap htotal havailable
  intro hfinite
  exact le_of_not_gt (fun hlt =>
    hnot ⟨hfinite, hlt⟩)

/-- The redistributed group profile: unavailable groups are set to zero and
their total empirical mass is placed on available groups by `allocation`. -/
noncomputable def redistributedGroupWeight
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S)))
    (i : ℕ) : ENNReal := by
  classical
  exact if i ∈ unavailableGroups H groups S then 0
    else empiricalGroupENN S groups i + allocation.weight i

theorem tsum_redistributedGroupWeight_eq_one
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S))) :
    ∑' i, redistributedGroupWeight H groups S allocation i = 1 := by
  classical
  let unavailable := unavailableGroups H groups S
  have hpointwise :
      ∀ i,
        redistributedGroupWeight H groups S allocation i =
          (if i ∈ unavailable then 0
            else empiricalGroupENN S groups i) +
          allocation.weight i := by
    intro i
    by_cases hi : i ∈ unavailable
    · have hweight : allocation.weight i = 0 := by
        by_contra hne
        have havail := allocation.support_subset hne
        exact havail hi
      simp [redistributedGroupWeight, unavailable, hi, hweight]
    · simp [redistributedGroupWeight, unavailable, hi]
  calc
    _ = ∑' i,
        ((if i ∈ unavailable then 0
          else empiricalGroupENN S groups i) +
          allocation.weight i) := tsum_congr hpointwise
    _ = (∑' i, if i ∈ unavailable then 0
          else empiricalGroupENN S groups i) +
        ∑' i, allocation.weight i := ENNReal.tsum_add
    _ = empiricalMassOnGroupIndices S groups unavailableᶜ +
        empiricalMassOnGroupIndices S groups unavailable := by
      rw [allocation.total_weight]
      congr 1
      unfold empiricalMassOnGroupIndices
      apply tsum_congr
      intro i
      by_cases hi : i ∈ unavailable
      · unfold empiricalGroupENN
        simp [hi]
      · unfold empiricalGroupENN
        simp [hi]
    _ = 1 := by
      rw [add_comm]
      exact empiricalMass_add_compl
        S groups hpartition hS unavailable

noncomputable def redistributedGroupPMF
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S))) :
    _root_.PMF ℕ :=
  ⟨redistributedGroupWeight H groups S allocation,
    ENNReal.summable.hasSum_iff.mpr
      (tsum_redistributedGroupWeight_eq_one
        H groups S hpartition hS allocation)⟩

@[simp] theorem redistributedGroupPMF_apply
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S)))
    (i : ℕ) :
    redistributedGroupPMF H groups S hpartition hS allocation i =
      redistributedGroupWeight H groups S allocation i :=
  rfl

theorem redistributedGroupPMF_eq_zero_of_unavailable
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S)))
    {i : ℕ} (hi : i ∈ unavailableGroups H groups S) :
    redistributedGroupPMF
        H groups S hpartition hS allocation i = 0 := by
  rw [redistributedGroupPMF_apply]
  unfold redistributedGroupWeight
  rw [if_pos hi]

/-- Pick one unseen closure point from every available group. -/
noncomputable def unseenGroupRepresentative
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hS : S.Nonempty) (i : ℕ) : α := by
  classical
  by_cases hi : i ∈ (unavailableGroups H groups S)ᶜ
  · have hne :
        unseenClosure H S ∩ groups i ≠ ∅ := by
      simpa [unavailableGroups] using hi
    exact Classical.choose (Set.nonempty_iff_ne_empty.mpr hne)
  · exact hS.choose

theorem unseenGroupRepresentative_mem
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hS : S.Nonempty) {i : ℕ}
    (hi : i ∈ (unavailableGroups H groups S)ᶜ) :
    unseenGroupRepresentative H groups S hS i ∈
        unseenClosure H S ∩ groups i := by
  classical
  unfold unseenGroupRepresentative
  rw [dif_pos hi]
  exact Classical.choose_spec
    (Set.nonempty_iff_ne_empty.mpr (by
      simpa [unavailableGroups] using hi))

noncomputable def closureRedistributedPMF
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S))) :
    PMF α :=
  (redistributedGroupPMF H groups S hpartition hS allocation).map
    (unseenGroupRepresentative H groups S hS)

/-- Mapping the redistributed group PMF to one unseen representative per
available group realizes exactly the prescribed group profile. -/
theorem closureRedistributedPMF_groupMass
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S)))
    (i : ℕ) :
    (closureRedistributedPMF
        H groups S hpartition hS allocation).toOuterMeasure
        (groups i) =
      redistributedGroupPMF
        H groups S hpartition hS allocation i := by
  classical
  let q :=
    redistributedGroupPMF H groups S hpartition hS allocation
  let representative :=
    unseenGroupRepresentative H groups S hS
  change (q.map representative).toOuterMeasure (groups i) = q i
  rw [PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_apply]
  calc
    _ = (representative ⁻¹' groups i).indicator (⇑q) i := by
      apply tsum_eq_single i
      intro j hji
      by_cases hqj : q j = 0
      · simp [Set.indicator, hqj]
      · have hjAvailable :
            j ∈ (unavailableGroups H groups S)ᶜ := by
          by_contra hj
          have hjUnavailable :
              j ∈ unavailableGroups H groups S := by simpa using hj
          apply hqj
          exact redistributedGroupPMF_eq_zero_of_unavailable
            H groups S hpartition hS allocation hjUnavailable
        have hrepj :=
          unseenGroupRepresentative_mem
            H groups S hS hjAvailable
        have hnotGroup :
            representative j ∉ groups i := by
          intro hjiGroup
          have hdisjoint := hpartition.1 j i hji
          exact Set.disjoint_left.mp hdisjoint hrepj.2 hjiGroup
        have hnotPreimage :
            j ∉ representative ⁻¹' groups i := hnotGroup
        rw [Set.indicator_of_notMem hnotPreimage]
    _ = q i := by
      by_cases hiAvailable :
        i ∈ (unavailableGroups H groups S)ᶜ
      · have hrepi :=
          unseenGroupRepresentative_mem
            H groups S hS hiAvailable
        have hiPreimage :
            i ∈ representative ⁻¹' groups i := hrepi.2
        rw [Set.indicator_of_mem hiPreimage]
      · have hiUnavailable :
            i ∈ unavailableGroups H groups S := by
          simpa using hiAvailable
        have hqi : q i = 0 := by
          exact redistributedGroupPMF_eq_zero_of_unavailable
            H groups S hpartition hS allocation hiUnavailable
        by_cases hmem : representative i ∈ groups i
        · have hiPreimage :
              i ∈ representative ⁻¹' groups i := hmem
          rw [Set.indicator_of_mem hiPreimage, hqi]
        · have hiPreimage :
              i ∉ representative ⁻¹' groups i := hmem
          rw [Set.indicator_of_notMem hiPreimage, hqi]

noncomputable def closureRedistributedDistribution
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S))) :
    DiscreteDistribution α :=
  DiscreteDistribution.ofPMF
    (closureRedistributedPMF
      H groups S hpartition hS allocation)

theorem closureRedistributedDistribution_supportedOn
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S))) :
    SupportedOn
      (closureRedistributedDistribution
        H groups S hpartition hS allocation)
      (unseenClosure H S) := by
  classical
  let q :=
    redistributedGroupPMF H groups S hpartition hS allocation
  let representative :=
    unseenGroupRepresentative H groups S hS
  intro x hx
  have hxPMF :
      (q.map representative) x ≠ 0 := by
    intro hzero
    apply hx
    unfold closureRedistributedDistribution
    rw [DiscreteDistribution.ofPMF_mass]
    have hz :
        closureRedistributedPMF
          H groups S hpartition hS allocation x = 0 := by
      change (q.map representative) x = 0
      exact hzero
    rw [hz]
    simp
  have hxSupport :
      x ∈ (q.map representative).support := hxPMF
  obtain ⟨j, hjSupport, hjx⟩ :=
    (PMF.mem_support_map_iff representative q x).mp hxSupport
  have hjAvailable :
      j ∈ (unavailableGroups H groups S)ᶜ := by
    by_contra hj
    have hjUnavailable :
        j ∈ unavailableGroups H groups S := by simpa using hj
    have hjzero : q j = 0 :=
      redistributedGroupPMF_eq_zero_of_unavailable
        H groups S hpartition hS allocation hjUnavailable
    exact (PMF.mem_support_iff q j).mp hjSupport hjzero
  rw [← hjx]
  exact (unseenGroupRepresentative_mem
    H groups S hS hjAvailable).1

theorem closureRedistributedDistribution_groupProbability
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S)))
    (i : ℕ) :
    inducedGroupProbability
        (closureRedistributedDistribution
          H groups S hpartition hS allocation)
        groups i =
      (redistributedGroupPMF
        H groups S hpartition hS allocation i).toReal := by
  unfold inducedGroupProbability
  unfold closureRedistributedDistribution
  rw [groupMass_ofPMF,
    closureRedistributedPMF_groupMass]

theorem redistributedGroupPMF_coordinate_close
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (S : Finset α)
    (hpartition : IsCountablePartition groups)
    (hS : S.Nonempty)
    (allocation :
      BoundedMassAllocation
        (unavailableGroups H groups S)ᶜ
        (ENNReal.ofReal alpha)
        (empiricalMassOnGroupIndices S groups
          (unavailableGroups H groups S)))
    (hnotOne :
      ¬groupClosureConditionOne H groups alpha S)
    (i : ℕ) :
    ENNReal.ofReal
        |(redistributedGroupPMF
            H groups S hpartition hS allocation i).toReal -
          empiricalGroupProbability S groups i| ≤
      ENNReal.ofReal alpha := by
  classical
  have hempNonneg :
      0 ≤ empiricalGroupProbability S groups i := by
    unfold empiricalGroupProbability
    split <;> positivity
  by_cases hi :
      i ∈ unavailableGroups H groups S
  · have hempLe :
        empiricalGroupENN S groups i ≤
          ENNReal.ofReal alpha := by
      exact le_of_not_gt (fun hlt =>
        hnotOne ⟨i, hi, by
          simpa [empiricalGroupENN] using hlt⟩)
    have hqzero :=
      redistributedGroupPMF_eq_zero_of_unavailable
        H groups S hpartition hS allocation hi
    rw [hqzero]
    simp only [ENNReal.toReal_zero, zero_sub, abs_neg,
      abs_of_nonneg hempNonneg]
    simpa [empiricalGroupENN] using hempLe
  · have hpTop :
        empiricalGroupENN S groups i ≠ ⊤ := by
      unfold empiricalGroupENN
      exact ENNReal.ofReal_ne_top
    have hwTop :
        allocation.weight i ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (allocation.weight_le_cap i)
    rw [redistributedGroupPMF_apply]
    unfold redistributedGroupWeight
    rw [if_neg hi, ENNReal.toReal_add hpTop hwTop]
    unfold empiricalGroupENN
    rw [ENNReal.toReal_ofReal hempNonneg]
    simp only [add_sub_cancel_left,
      abs_of_nonneg ENNReal.toReal_nonneg]
    rw [ENNReal.ofReal_toReal hwTop]
    exact allocation.weight_le_cap i

/-- The uniform empirical distribution on the distinct observed sample. -/
noncomputable def empiricalPointPMF
    (S : Finset α) (hS : S.Nonempty) : PMF α := by
  classical
  let mass : α → ENNReal :=
    fun x => if x ∈ S then (S.card : ENNReal)⁻¹ else 0
  apply PMF.ofFinset mass S
  · calc
      ∑ x ∈ S, mass x =
          ∑ _x ∈ S, (S.card : ENNReal)⁻¹ := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [mass, hx]
      _ = (S.card : ENNReal) *
          (S.card : ENNReal)⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = 1 := ENNReal.mul_inv_cancel
        (by exact_mod_cast Finset.card_ne_zero.mpr hS)
        (by simp)
  · intro x hx
    simp [mass, hx]

@[simp] theorem empiricalPointPMF_apply
    [DecidableEq α] (S : Finset α) (hS : S.Nonempty) (x : α) :
    empiricalPointPMF S hS x =
      if x ∈ S then (S.card : ENNReal)⁻¹ else 0 :=
  by
    classical
    simp [empiricalPointPMF]

noncomputable def empiricalPointDistribution
    (S : Finset α) (hS : S.Nonempty) :
    DiscreteDistribution α :=
  DiscreteDistribution.ofPMF (empiricalPointPMF S hS)

theorem empiricalPointDistribution_groupProbability
    (S : Finset α) (hS : S.Nonempty)
    (groups : ℕ → Set α) (i : ℕ) :
    inducedGroupProbability
        (empiricalPointDistribution S hS) groups i =
      empiricalGroupProbability S groups i := by
  classical
  unfold inducedGroupProbability empiricalPointDistribution
  rw [groupMass_ofPMF, PMF.toOuterMeasure_apply]
  have houtside :
      ∀ x ∉ S,
        (groups i).indicator (⇑(empiricalPointPMF S hS)) x = 0 := by
    intro x hx
    by_cases hxi : x ∈ groups i
    · rw [Set.indicator_of_mem hxi,
        empiricalPointPMF_apply, if_neg hx]
    · rw [Set.indicator_of_notMem hxi]
  rw [tsum_eq_sum (s := S) houtside]
  have hsum :
      ∑ x ∈ S,
          (groups i).indicator (⇑(empiricalPointPMF S hS)) x =
        (S.filter (fun x => x ∈ groups i)).card *
          (S.card : ENNReal)⁻¹ := by
    calc
      _ = ∑ x ∈ S.filter (fun x => x ∈ groups i),
          (S.card : ENNReal)⁻¹ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxi : x ∈ groups i
        · rw [Set.indicator_of_mem hxi,
            empiricalPointPMF_apply, if_pos hx]
          simp [hxi]
        · rw [Set.indicator_of_notMem hxi]
          simp [hxi]
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hcardPos : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hENN :
      ((S.filter (fun x => x ∈ groups i)).card : ENNReal) *
          (S.card : ENNReal)⁻¹ =
        ENNReal.ofReal
          (((S.filter (fun x => x ∈ groups i)).card : ℝ) /
            (S.card : ℝ)) := by
    rw [← div_eq_mul_inv,
      ← ENNReal.ofReal_natCast
        (S.filter (fun x => x ∈ groups i)).card,
      ← ENNReal.ofReal_natCast S.card,
      ← ENNReal.ofReal_div_of_pos hcardPos]
  rw [hENN, ENNReal.toReal_ofReal (by positivity)]
  simp [empiricalGroupProbability, hS]

theorem empiricalPointDistribution_distance_zero
    (S : Finset α) (hS : S.Nonempty)
    (groups : ℕ → Set α) :
    groupSupDistance
        (empiricalPointDistribution S hS) S groups = 0 := by
  unfold groupSupDistance
  simp [empiricalPointDistribution_groupProbability S hS groups]

/-! ## Group-closure dimension -/

/-- A finite distinct sample witnessing published Definition 3.1 at its own cardinality.
Nonemptiness corresponds to the source's natural-number levels beginning at
one, and consistency is the printed requirement that the closure is not
bottom. -/
def IsGroupClosureWitness
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (S : Finset α) : Prop :=
  S.Nonempty ∧
    (consistentHypotheses H S).Nonempty ∧
    (groupClosureConditionOne H groups alpha S ∨
      groupClosureConditionTwo H groups alpha S)

/-- The group closure dimension is at least `d` when published Definition 3.1 has a
witness of exactly that many distinct points. -/
def GroupClosureDimensionAtLeast
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (d : ℕ) : Prop :=
  ∃ S : Finset α, S.card = d ∧
    IsGroupClosureWitness H groups alpha S

/-- Finite group closure dimension, avoiding a partial "largest natural"
operator: all published Definition 3.1 witnesses have cardinality bounded by one natural
number. -/
def HasFiniteGroupClosureDimension
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) : Prop :=
  ∃ d : ℕ, ∀ S : Finset α,
    IsGroupClosureWitness H groups alpha S → S.card ≤ d

/-- The source's `GCα(H,A) = ∞` convention. -/
def HasInfiniteGroupClosureDimension
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) : Prop :=
  ∀ d : ℕ, ∃ S : Finset α,
    d ≤ S.card ∧ IsGroupClosureWitness H groups alpha S

theorem not_finite_iff_infinite_groupClosureDimension
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) :
    ¬HasFiniteGroupClosureDimension H groups alpha ↔
      HasInfiniteGroupClosureDimension H groups alpha := by
  simp only [HasFiniteGroupClosureDimension,
    HasInfiniteGroupClosureDimension]
  constructor
  · intro h d
    push_neg at h
    obtain ⟨S, hS, hcard⟩ := h d
    exact ⟨S, Nat.le_of_lt hcard, hS⟩
  · intro h
    push_neg
    intro d
    obtain ⟨S, hcard, hS⟩ := h (d + 1)
    exact ⟨S, hS, lt_of_lt_of_le (Nat.lt_succ_self d) hcard⟩

/-! ## Sufficiency -/

/-- Feasibility of one post-threshold closure: an output distribution is
supported on the unseen closure and is representative of the sample. -/
def ClosureFeasibleAt
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (S : Finset α) : Prop :=
  ∃ μ : DiscreteDistribution α,
    SupportedOn μ (unseenClosure H S) ∧
      groupSupDistance μ S groups ≤ ENNReal.ofReal alpha

/-- For a distribution supported on the unseen closure, all of its mass is
carried by the finitely many available groups whenever that index set is
finite. -/
theorem sum_inducedGroupProbability_available_eq_one
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {S : Finset α}
    (hpartition : IsCountablePartition groups)
    (μ : DiscreteDistribution α)
    (hsupport : SupportedOn μ (unseenClosure H S))
    (hfinite : (unavailableGroups H groups S)ᶜ.Finite) :
    ∑ i ∈ hfinite.toFinset,
        inducedGroupProbability μ groups i = 1 := by
  classical
  let index := partitionIndex groups hpartition
  have hpointwise :
      ∀ x,
        ∑ i ∈ hfinite.toFinset,
            restrictedMass μ (groups i) x =
          μ.mass x := by
    intro x
    by_cases hxmass : μ.mass x = 0
    · simp [restrictedMass, hxmass]
    · have hxUnseen : x ∈ unseenClosure H S :=
        hsupport x hxmass
      have hindexAvailable :
          index x ∈ (unavailableGroups H groups S)ᶜ := by
        intro hunavailable
        have hempty :
            unseenClosure H S ∩ groups (index x) = ∅ :=
          hunavailable
        have hxinter :
            x ∈ unseenClosure H S ∩ groups (index x) :=
          ⟨hxUnseen, mem_partitionIndex groups hpartition x⟩
        rw [hempty] at hxinter
        simp at hxinter
      have hindexMem : index x ∈ hfinite.toFinset :=
        hfinite.mem_toFinset.mpr hindexAvailable
      calc
        _ = ∑ i ∈ hfinite.toFinset,
            if index x = i then μ.mass x else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [restrictedMass]
              by_cases hxi : x ∈ groups i
              · rw [if_pos hxi,
                  if_pos (partitionIndex_eq_of_mem
                    groups hpartition hxi)]
              · have hne : index x ≠ i := by
                  intro heq
                  apply hxi
                  exact (mem_group_iff_partitionIndex_eq
                    groups hpartition x i).mpr heq
                rw [if_neg hxi, if_neg hne]
        _ = μ.mass x := by
          simp [hindexMem]
  calc
    _ = ∑' x, ∑ i ∈ hfinite.toFinset,
          restrictedMass μ (groups i) x := by
      unfold inducedGroupProbability groupMass
      symm
      apply Summable.tsum_finsetSum
      intro i hi
      exact groupMass_summable μ (groups i)
    _ = ∑' x, μ.mass x := tsum_congr hpointwise
    _ = 1 := μ.total_mass

theorem empiricalMassOnGroupIndices_eq_sum_of_finite
    (S : Finset α) (groups : ℕ → Set α)
    {I : Set ℕ} (hfinite : I.Finite) :
    empiricalMassOnGroupIndices S groups I =
      ∑ i ∈ hfinite.toFinset, empiricalGroupENN S groups i := by
  classical
  unfold empiricalMassOnGroupIndices
  rw [tsum_eq_sum (s := hfinite.toFinset)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (hfinite.mem_toFinset.mp hi)]
    rfl
  · intro i hi
    have hnot : i ∉ I := by
      simpa only [hfinite.mem_toFinset] using hi
    simp [hnot]

/-- Failure of both witness alternatives yields an actual representative
distribution supported on the unseen closure.  This is the complete
countable mass-allocation step in the sufficiency proof of Theorem 3.3. -/
theorem closureFeasible_of_not_groupClosureConditions
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ} {S : Finset α}
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha) (hS : S.Nonempty)
    (hnotOne :
      ¬groupClosureConditionOne H groups alpha S)
    (hnotTwo :
      ¬groupClosureConditionTwo H groups alpha S) :
    ClosureFeasibleAt H groups alpha S := by
  classical
  let allocation :=
    Classical.choice
      (boundedMassAllocation_of_not_groupClosureConditionTwo
        hpartition halpha hS hnotTwo)
  let μ :=
    closureRedistributedDistribution
      H groups S hpartition hS allocation
  refine ⟨μ, ?_, ?_⟩
  · exact closureRedistributedDistribution_supportedOn
      H groups S hpartition hS allocation
  · unfold groupSupDistance
    apply iSup_le
    intro i
    rw [closureRedistributedDistribution_groupProbability
      H groups S hpartition hS allocation i]
    exact redistributedGroupPMF_coordinate_close
      H groups S hpartition hS allocation hnotOne i

/-- A cardinality bound on all group-closure witnesses forces feasibility
strictly above that bound.  This packages the contradiction step used by
the generator in the sufficiency direction of Theorem 3.3. -/
theorem closureFeasible_of_card_gt_dimensionBound
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ} {d : ℕ}
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha)
    (hbound : ∀ S : Finset α,
      IsGroupClosureWitness H groups alpha S → S.card ≤ d)
    {S : Finset α} (hS : S.Nonempty)
    (hversion : (consistentHypotheses H S).Nonempty)
    (hlarge : d < S.card) :
    ClosureFeasibleAt H groups alpha S := by
  have hnotWitness :
      ¬IsGroupClosureWitness H groups alpha S := by
    intro hwitness
    exact (Nat.not_lt_of_ge (hbound S hwitness)) hlarge
  apply closureFeasible_of_not_groupClosureConditions
    hpartition halpha hS
  · intro hone
    exact hnotWitness ⟨hS, hversion, Or.inl hone⟩
  · intro htwo
    exact hnotWitness ⟨hS, hversion, Or.inr htwo⟩

/-- The distribution used after one finite sample in the constructive half
of Theorem 3.3.  Above the group-closure dimension it uses the countable
redistribution construction.  Before that point (or outside the version
space) it uses the empirical distribution, which is exactly
representative.  The last branch merely totalizes the generator on the
empty history. -/
noncomputable def finiteGroupClosureSampleDistribution
    [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) (d : ℕ)
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha)
    (hbound : ∀ S : Finset α,
      IsGroupClosureWitness H groups alpha S → S.card ≤ d)
    (S : Finset α) :
    DiscreteDistribution α := by
  classical
  if hgood :
      S.Nonempty ∧
        (consistentHypotheses H S).Nonempty ∧
        d < S.card then
    exact Classical.choose
      (closureFeasible_of_card_gt_dimensionBound
        hpartition halpha hbound hgood.1 hgood.2.1 hgood.2.2)
  else if hS : S.Nonempty then
    exact empiricalPointDistribution S hS
  else
    exact DiscreteDistribution.ofPMF
      (PMF.pure (Classical.choice (inferInstance : Nonempty α)))

theorem finiteGroupClosureSampleDistribution_representative
    [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) (d : ℕ)
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha)
    (hbound : ∀ S : Finset α,
      IsGroupClosureWitness H groups alpha S → S.card ≤ d)
    (S : Finset α) (hS : S.Nonempty) :
    groupSupDistance
        (finiteGroupClosureSampleDistribution
          H groups alpha d hpartition halpha hbound S)
        S groups ≤ ENNReal.ofReal alpha := by
  classical
  by_cases hgood :
      S.Nonempty ∧
        (consistentHypotheses H S).Nonempty ∧
        d < S.card
  · simp only [finiteGroupClosureSampleDistribution, dif_pos hgood]
    exact (Classical.choose_spec
      (closureFeasible_of_card_gt_dimensionBound
        hpartition halpha hbound
        hgood.1 hgood.2.1 hgood.2.2)).2
  · simp only [finiteGroupClosureSampleDistribution,
      dif_neg hgood, dif_pos hS]
    rw [empiricalPointDistribution_distance_zero]
    exact bot_le

theorem finiteGroupClosureSampleDistribution_supportedOn
    [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) (d : ℕ)
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha)
    (hbound : ∀ S : Finset α,
      IsGroupClosureWitness H groups alpha S → S.card ≤ d)
    (S : Finset α) (hS : S.Nonempty)
    (hversion : (consistentHypotheses H S).Nonempty)
    (hlarge : d < S.card) :
    SupportedOn
      (finiteGroupClosureSampleDistribution
        H groups alpha d hpartition halpha hbound S)
      (unseenClosure H S) := by
  classical
  have hgood :
      S.Nonempty ∧
        (consistentHypotheses H S).Nonempty ∧
        d < S.card :=
    ⟨hS, hversion, hlarge⟩
  simp only [finiteGroupClosureSampleDistribution, dif_pos hgood]
  exact (Classical.choose_spec
    (closureFeasible_of_card_gt_dimensionBound
      hpartition halpha hbound hS hversion hlarge)).1

/-- The paper's constructive randomized generator for a finite
group-closure bound. -/
noncomputable def finiteGroupClosureGenerator
    [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) (d : ℕ)
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha)
    (hbound : ∀ S : Finset α,
      IsGroupClosureWitness H groups alpha S → S.card ≤ d) :
    RandomizedGenerator α :=
  fun _t xs =>
    finiteGroupClosureSampleDistribution
      H groups alpha d hpartition halpha hbound
      (GenLimit.Generic.sequenceSample xs)

theorem finiteGroupClosureGenerator_representative
    [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) (d : ℕ)
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha)
    (hbound : ∀ S : Finset α,
      IsGroupClosureWitness H groups alpha S → S.card ≤ d) :
    IsAlphaRepresentative
      (finiteGroupClosureGenerator
        H groups alpha d hpartition halpha hbound)
      groups alpha := by
  intro stream t ht
  have hsample :
      (GenLimit.Generic.sample stream t).Nonempty := by
    exact ⟨stream 0, GenLimit.Generic.value_mem_sample ht⟩
  simpa only [distributionAt, finiteGroupClosureGenerator,
    GenLimit.Generic.sequenceSample_prefix] using
      finiteGroupClosureSampleDistribution_representative
        H groups alpha d hpartition halpha hbound
        (GenLimit.Generic.sample stream t) hsample

theorem unseenClosure_subset_target_difference
    {H : GenLimit.Generic.LanguageClass α}
    {S : Finset α} {L : GenLimit.Generic.Language α}
    (hL : L ∈ consistentHypotheses H S) :
    unseenClosure H S ⊆ L \ (↑S : Set α) := by
  intro x hx
  exact ⟨commonCore_subset_of_consistent hL hx.1, hx.2⟩

/-- Once `d+1` distinct examples have been observed, every later output of
the finite-group-closure generator is supported on fresh points in the
target. -/
theorem finiteGroupClosureGenerator_consistentFrom
    [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) (d : ℕ)
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha)
    (hbound : ∀ S : Finset α,
      IsGroupClosureWitness H groups alpha S → S.card ≤ d)
    {L : GenLimit.Generic.Language α} (hLH : L ∈ H)
    {stream : GenLimit.Generic.Stream α}
    (hstream : GenLimit.Generic.StreamIn stream L)
    {t : ℕ}
    (ht : (GenLimit.Generic.sample stream t).card = d + 1) :
    IsConsistentFrom
      (finiteGroupClosureGenerator
        H groups alpha d hpartition halpha hbound)
      L stream t := by
  intro s hts
  let S := GenLimit.Generic.sample stream s
  have hsampleMono :
      GenLimit.Generic.sample stream t ⊆ S :=
    GenLimit.Generic.sample_mono hts
  have hcardLower : d + 1 ≤ S.card := by
    rw [← ht]
    exact Finset.card_le_card hsampleMono
  have hlarge : d < S.card := by omega
  have hS : S.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hversion :
      (consistentHypotheses H S).Nonempty := by
    exact ⟨L, hLH,
      GenLimit.Generic.sample_subset_of_streamIn hstream s⟩
  have hsupported :
      SupportedOn
        (distributionAt
          (finiteGroupClosureGenerator
            H groups alpha d hpartition halpha hbound)
          stream s)
        (unseenClosure H S) := by
    simpa only [distributionAt, finiteGroupClosureGenerator,
      GenLimit.Generic.sequenceSample_prefix, S] using
        finiteGroupClosureSampleDistribution_supportedOn
          H groups alpha d hpartition halpha hbound
          S hS hversion hlarge
  apply isConsistentAt_iff_supportedOn.mpr
  intro x hx
  exact unseenClosure_subset_target_difference
    (H := H) (S := S) ⟨hLH,
      GenLimit.Generic.sample_subset_of_streamIn hstream s⟩
    (hsupported x hx)

/-- Sufficiency in published Theorem 3.3, including the full countable mass-allocation
construction from Definition 3.1.  The nonempty-universe assumption is needed
only to totalize a randomized generator at the empty history. -/
theorem alphaRepresentativeUniformlyGeneratable_of_finite_groupClosureDimension
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha)
    (hfinite :
      HasFiniteGroupClosureDimension H groups alpha) :
    AlphaRepresentativeUniformlyGeneratable H groups alpha := by
  obtain ⟨d, hbound⟩ := hfinite
  refine ⟨
    finiteGroupClosureGenerator
      H groups alpha d hpartition halpha hbound,
    finiteGroupClosureGenerator_representative
      H groups alpha d hpartition halpha hbound,
    d + 1, ?_⟩
  intro L hLH stream hstream t ht
  exact finiteGroupClosureGenerator_consistentFrom
    H groups alpha d hpartition halpha hbound
    hLH hstream ht

/-! ## Necessity -/

/-- The coordinate obstruction behind alternative (1) of Definition 3.1. -/
theorem unavailable_coordinate_le_of_closureFeasible
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    {S : Finset α}
    (hfeasible : ClosureFeasibleAt H groups alpha S)
    {i : ℕ} (hi : i ∈ unavailableGroups H groups S) :
    ENNReal.ofReal (empiricalGroupProbability S groups i) ≤
      ENNReal.ofReal alpha := by
  obtain ⟨μ, hsupport, hdistance⟩ := hfeasible
  have hdisjoint : Disjoint (unseenClosure H S) (groups i) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    exact hi
  have hmass : inducedGroupProbability μ groups i = 0 := by
    exact groupMass_eq_zero_of_supportedOn_of_disjoint
      hsupport hdisjoint
  have hcoordinate :=
    coordinate_le_groupSupDistance μ S groups i
  have hle := hcoordinate.trans hdistance
  rw [hmass] at hle
  have hemp :
      0 ≤ empiricalGroupProbability S groups i :=
    empiricalGroupProbability_nonnegative S groups i
  simpa [abs_of_nonneg hemp] using hle

theorem inducedGroupProbability_le_empirical_add_of_distance
    {μ : DiscreteDistribution α}
    {groups : ℕ → Set α} {alpha : ℝ}
    {S : Finset α}
    (halpha : 0 ≤ alpha)
    (hdistance :
      groupSupDistance μ S groups ≤ ENNReal.ofReal alpha)
    (i : ℕ) :
    inducedGroupProbability μ groups i ≤
      empiricalGroupProbability S groups i + alpha := by
  have hcoordinate :
      ENNReal.ofReal
          |inducedGroupProbability μ groups i -
            empiricalGroupProbability S groups i| ≤
        ENNReal.ofReal alpha :=
    (coordinate_le_groupSupDistance μ S groups i).trans
      hdistance
  have habs :
      |inducedGroupProbability μ groups i -
        empiricalGroupProbability S groups i| ≤ alpha :=
    (ENNReal.ofReal_le_ofReal_iff halpha).mp hcoordinate
  have hsub :
      inducedGroupProbability μ groups i -
          empiricalGroupProbability S groups i ≤ alpha :=
    (le_abs_self
      (inducedGroupProbability μ groups i -
        empiricalGroupProbability S groups i)).trans habs
  linarith

/-- Therefore no closure-feasible sample can satisfy alternative (1) in
Definition 3.1. -/
theorem closureFeasible_not_groupClosureConditionOne
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    {S : Finset α}
    (hfeasible : ClosureFeasibleAt H groups alpha S) :
    ¬groupClosureConditionOne H groups alpha S := by
  rintro ⟨i, hi, hlarge⟩
  exact (not_lt_of_ge
    (unavailable_coordinate_le_of_closureFeasible
      hfeasible hi)) hlarge

/-- A closure-feasible sample cannot satisfy the aggregate-capacity
alternative (2) of Definition 3.1.  The proof sums the coordinatewise
representativeness bounds over the finite set of available groups and uses
that support on the unseen closure puts total mass one on exactly those
groups. -/
theorem closureFeasible_not_groupClosureConditionTwo
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    {S : Finset α}
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha) (hS : S.Nonempty)
    (hfeasible : ClosureFeasibleAt H groups alpha S) :
    ¬groupClosureConditionTwo H groups alpha S := by
  classical
  rintro ⟨hfinite, hcapacityFailure⟩
  obtain ⟨μ, hsupport, hdistance⟩ := hfeasible
  let available := (unavailableGroups H groups S)ᶜ
  let F := hfinite.toFinset
  have hqsumReal :
      ∑ i ∈ F, inducedGroupProbability μ groups i = 1 := by
    simpa only [F, available] using
      sum_inducedGroupProbability_available_eq_one
        hpartition μ hsupport hfinite
  have hqsumENN :
      ∑ i ∈ F,
          ENNReal.ofReal
            (inducedGroupProbability μ groups i) = 1 := by
    calc
      _ = ENNReal.ofReal
          (∑ i ∈ F,
            inducedGroupProbability μ groups i) := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro i hi
        exact groupMass_nonnegative μ (groups i)
      _ = 1 := by rw [hqsumReal]; simp
  have hcoordinate :
      ∀ i ∈ F,
        ENNReal.ofReal
            (inducedGroupProbability μ groups i) ≤
          empiricalGroupENN S groups i +
            ENNReal.ofReal alpha := by
    intro i hi
    have hreal :=
      inducedGroupProbability_le_empirical_add_of_distance
        halpha.le hdistance i
    calc
      _ ≤ ENNReal.ofReal
          (empiricalGroupProbability S groups i + alpha) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = empiricalGroupENN S groups i +
          ENNReal.ofReal alpha := by
        rw [ENNReal.ofReal_add
          (empiricalGroupProbability_nonnegative S groups i)
          halpha.le]
        rfl
  have hsumLe :
      ∑ i ∈ F,
          ENNReal.ofReal
            (inducedGroupProbability μ groups i) ≤
        ∑ i ∈ F,
          (empiricalGroupENN S groups i +
            ENNReal.ofReal alpha) :=
    Finset.sum_le_sum hcoordinate
  have havailableMass :
      empiricalMassOnGroupIndices S groups available =
        ∑ i ∈ F, empiricalGroupENN S groups i := by
    simpa only [available, F] using
      empiricalMassOnGroupIndices_eq_sum_of_finite
        S groups hfinite
  have honeLe :
      1 ≤ empiricalMassOnGroupIndices S groups available +
        ENNReal.ofReal alpha * F.card := by
    rw [← hqsumENN]
    calc
      _ ≤ ∑ i ∈ F,
          (empiricalGroupENN S groups i +
            ENNReal.ofReal alpha) := hsumLe
      _ = (∑ i ∈ F, empiricalGroupENN S groups i) +
          ENNReal.ofReal alpha * F.card := by
        rw [Finset.sum_add_distrib, Finset.sum_const,
          nsmul_eq_mul, mul_comm]
      _ = _ := by rw [← havailableMass]
  have hmassTotal :
      empiricalMassOnGroupIndices S groups available +
          empiricalMassOnGroupIndices S groups
            (unavailableGroups H groups S) = 1 := by
    have hadd :=
      empiricalMass_add_compl S groups hpartition hS
        (unavailableGroups H groups S)
    simpa only [available, add_comm] using hadd
  have hltOne :
      empiricalMassOnGroupIndices S groups available +
          ENNReal.ofReal alpha * F.card < 1 := by
    calc
      _ < empiricalMassOnGroupIndices S groups available +
          empiricalMassOnGroupIndices S groups
            (unavailableGroups H groups S) := by
        apply ENNReal.add_lt_add_left
          (ne_top_of_le_ne_top ENNReal.one_ne_top
            (empiricalMassOnGroupIndices_le_one
              S groups hpartition hS available))
        simpa only [F] using hcapacityFailure
      _ = 1 := hmassTotal
  exact (not_lt_of_ge honeLe) hltOne

/-- At its uniform threshold, a representative uniform generator supplies a
distribution supported on the unseen common closure.  This makes precise the
common-prefix step in the necessity proof of Theorem 3.3. -/
theorem alphaUniform_has_closureFeasible_threshold
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    (hUniform :
      AlphaRepresentativeUniformlyGeneratable H groups alpha) :
    ∃ d : ℕ, ∀ S : Finset α,
      S.Nonempty →
      (consistentHypotheses H S).Nonempty →
      S.card = d →
      ClosureFeasibleAt H groups alpha S := by
  classical
  obtain ⟨gen, hrepresentative, d, hconsistent⟩ := hUniform
  refine ⟨d, ?_⟩
  intro S hSnonempty hversion hcard
  let fallback : α := hSnonempty.choose
  let stream : GenLimit.Generic.Stream α :=
    GenLimit.Generic.historyThenFallback S.toList fallback
  have hfallbackS : fallback ∈ S := hSnonempty.choose_spec
  have hstream :
      ∀ L, L ∈ consistentHypotheses H S →
        GenLimit.Generic.StreamIn stream L := by
    intro L hL
    apply GenLimit.Generic.streamIn_historyThenFallback
    · intro x hx
      exact hL.2 (by simpa only [Finset.mem_toList] using hx)
    · exact hL.2 hfallbackS
  have hsample :
      GenLimit.Generic.sample stream S.card = S := by
    change
      GenLimit.Generic.sample
        (GenLimit.Generic.historyThenFallback S.toList fallback) S.card = S
    rw [← Finset.length_toList S,
      GenLimit.Generic.sample_historyThenFallback_length,
      Finset.toList_toFinset]
  let μ : DiscreteDistribution α :=
    distributionAt gen stream S.card
  have hsupported : SupportedOn μ (unseenClosure H S) := by
    intro x hxmass
    have hxinEvery :
        ∀ L, L ∈ consistentHypotheses H S → x ∈ L := by
      intro L hL
      have hat :
          IsConsistentAt gen L stream S.card :=
        hconsistent L hL.1 stream (hstream L hL)
          S.card (by simpa [hsample] using hcard) S.card le_rfl
      have hsupp :=
        isConsistentAt_iff_supportedOn.mp hat
      exact (hsupp x hxmass).1
    have hxNotSample : x ∉ (↑S : Set α) := by
      obtain ⟨L, hL⟩ := hversion
      have hat :
          IsConsistentAt gen L stream S.card :=
        hconsistent L hL.1 stream (hstream L hL)
          S.card (by simpa [hsample] using hcard) S.card le_rfl
      have hxNot :=
        (isConsistentAt_iff_supportedOn.mp hat x hxmass).2
      simpa only [hsample] using hxNot
    exact ⟨hxinEvery, hxNotSample⟩
  refine ⟨μ, hsupported, ?_⟩
  have hcardPos : 0 < S.card := Finset.card_pos.mpr hSnonempty
  have hrep := hrepresentative stream S.card hcardPos
  simpa [μ, hsample] using hrep

/-- The stronger form needed for the dimension bound: the same output is
closure-feasible at every nonempty sample whose cardinality is at least the
uniform threshold.  A threshold-sized subset is placed first in the
history; uniform consistency then persists until the full sample has been
shown. -/
theorem alphaUniform_has_closureFeasible_above_threshold
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    (hUniform :
      AlphaRepresentativeUniformlyGeneratable H groups alpha) :
    ∃ d : ℕ, ∀ S : Finset α,
      S.Nonempty →
      (consistentHypotheses H S).Nonempty →
      d ≤ S.card →
      ClosureFeasibleAt H groups alpha S := by
  classical
  obtain ⟨gen, hrepresentative, d, hconsistent⟩ := hUniform
  refine ⟨d, ?_⟩
  intro S hSnonempty hversion hcard
  obtain ⟨T, hTS, hTcard⟩ :=
    Finset.exists_subset_card_eq hcard
  let historyList : List α :=
    T.toList ++ (S \ T).toList
  have hhistoryFinset : historyList.toFinset = S := by
    simp only [historyList, List.toFinset_append,
      Finset.toList_toFinset]
    exact Finset.union_sdiff_of_subset hTS
  let fallback : α := hSnonempty.choose
  have hfallbackS : fallback ∈ S := hSnonempty.choose_spec
  let stream : GenLimit.Generic.Stream α :=
    GenLimit.Generic.historyThenFallback historyList fallback
  have hstream :
      ∀ L, L ∈ consistentHypotheses H S →
        GenLimit.Generic.StreamIn stream L := by
    intro L hL
    apply GenLimit.Generic.streamIn_historyThenFallback
    · intro x hx
      apply hL.2
      rw [← hhistoryFinset]
      change x ∈ historyList.toFinset
      simpa only [List.mem_toFinset] using hx
    · exact hL.2 hfallbackS
  have hfirstSample :
      GenLimit.Generic.sample stream T.card = T := by
    calc
      GenLimit.Generic.sample stream T.card =
          GenLimit.Generic.sample
            (GenLimit.Generic.historyThenFallback T.toList fallback) T.card := by
        apply GenLimit.Generic.sample_eq_of_eq_on_prefix
        intro n hn
        have hnT : n < T.toList.length := by
          simpa using hn
        have hnHistory : n < historyList.length := by
          simp only [historyList, List.length_append,
            Finset.length_toList]
          omega
        change GenLimit.Generic.historyThenFallback historyList fallback n =
          GenLimit.Generic.historyThenFallback T.toList fallback n
        simp only [GenLimit.Generic.historyThenFallback, dif_pos hnHistory,
          dif_pos hnT, historyList]
        exact List.getElem_append_left hnT
      _ = GenLimit.Generic.sample
          (GenLimit.Generic.historyThenFallback T.toList fallback)
          T.toList.length := by
        rw [Finset.length_toList]
      _ = T.toList.toFinset :=
        GenLimit.Generic.sample_historyThenFallback_length T.toList fallback
      _ = T := Finset.toList_toFinset T
  have hfullSample :
      GenLimit.Generic.sample stream historyList.length = S := by
    change
      GenLimit.Generic.sample
        (GenLimit.Generic.historyThenFallback historyList fallback)
        historyList.length = S
    rw [GenLimit.Generic.sample_historyThenFallback_length, hhistoryFinset]
  have htriggerCard :
      (GenLimit.Generic.sample stream T.card).card = d := by
    rw [hfirstSample, hTcard]
  have htime : T.card ≤ historyList.length := by
    simp [historyList]
  let μ : DiscreteDistribution α :=
    distributionAt gen stream historyList.length
  have hsupported :
      SupportedOn μ (unseenClosure H S) := by
    intro x hxmass
    have hxinEvery :
        ∀ L, L ∈ consistentHypotheses H S → x ∈ L := by
      intro L hL
      have hat :
          IsConsistentAt gen L stream historyList.length :=
        hconsistent L hL.1 stream (hstream L hL)
          T.card htriggerCard historyList.length htime
      have hsupp :=
        isConsistentAt_iff_supportedOn.mp hat
      exact (hsupp x hxmass).1
    have hxNotSample : x ∉ (↑S : Set α) := by
      obtain ⟨L, hL⟩ := hversion
      have hat :
          IsConsistentAt gen L stream historyList.length :=
        hconsistent L hL.1 stream (hstream L hL)
          T.card htriggerCard historyList.length htime
      have hxNot :=
        (isConsistentAt_iff_supportedOn.mp hat x hxmass).2
      simpa only [hfullSample] using hxNot
    exact ⟨hxinEvery, hxNotSample⟩
  refine ⟨μ, hsupported, ?_⟩
  have htimePos : 0 < historyList.length := by
    have hcardPositive : 0 < S.card :=
      Finset.card_pos.mpr hSnonempty
    have hcardHistory :
        historyList.toFinset.card = S.card := by
      rw [hhistoryFinset]
    exact lt_of_lt_of_le hcardPositive
      (by simpa [hcardHistory] using
        List.toFinset_card_le historyList)
  have hrep :=
    hrepresentative stream historyList.length htimePos
  simpa [μ, hfullSample] using hrep

/-- Consequently, alternative (1) of Definition 3.1 cannot occur at the
uniform threshold of a valid representative generator. -/
theorem alphaUniform_excludes_conditionOne_at_threshold
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    (hUniform :
      AlphaRepresentativeUniformlyGeneratable H groups alpha) :
    ∃ d : ℕ, ∀ S : Finset α,
      S.Nonempty →
      (consistentHypotheses H S).Nonempty →
      S.card = d →
      ¬groupClosureConditionOne H groups alpha S := by
  obtain ⟨d, hd⟩ :=
    alphaUniform_has_closureFeasible_threshold hUniform
  exact ⟨d, fun S hS hversion hcard =>
    closureFeasible_not_groupClosureConditionOne
      (hd S hS hversion hcard)⟩

/-- Necessity in published Theorem 3.3.  The stronger above-threshold feasibility
lemma rules out both alternatives of every witness larger than the
generator's uniform threshold. -/
theorem finite_groupClosureDimension_of_alphaRepresentativeUniformlyGeneratable
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha)
    (hUniform :
      AlphaRepresentativeUniformlyGeneratable H groups alpha) :
    HasFiniteGroupClosureDimension H groups alpha := by
  obtain ⟨d, hfeasible⟩ :=
    alphaUniform_has_closureFeasible_above_threshold hUniform
  refine ⟨d, ?_⟩
  intro S hWitness
  by_contra hnotBound
  have hlarge : d < S.card :=
    Nat.lt_of_not_ge hnotBound
  have hclosureFeasible :
      ClosureFeasibleAt H groups alpha S :=
    hfeasible S hWitness.1 hWitness.2.1 hlarge.le
  rcases hWitness.2.2 with hone | htwo
  · exact
      (closureFeasible_not_groupClosureConditionOne
        hclosureFeasible) hone
  · exact
      (closureFeasible_not_groupClosureConditionTwo
        hpartition halpha hWitness.1 hclosureFeasible) htwo

/-! ## Published characterization and corollary -/

/-- Published Theorem 3.3, in a form slightly stronger than the source statement:
countability of the point universe and UUS are not needed after the groups
have already been supplied as a countable partition.  Nonemptiness is
needed only because a randomized generator must return a probability
distribution even on the empty history. -/
theorem alphaRepresentativeUniformlyGeneratable_iff_finite_groupClosureDimension
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha) :
    AlphaRepresentativeUniformlyGeneratable H groups alpha ↔
      HasFiniteGroupClosureDimension H groups alpha := by
  constructor
  · exact
      finite_groupClosureDimension_of_alphaRepresentativeUniformlyGeneratable
        hpartition halpha
  · exact
      alphaRepresentativeUniformlyGeneratable_of_finite_groupClosureDimension
        hpartition halpha

theorem groupClosureWitness_anti_tolerance
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha beta : ℝ}
    (hab : alpha ≤ beta) {S : Finset α}
    (hWitness :
      IsGroupClosureWitness H groups beta S) :
    IsGroupClosureWitness H groups alpha S := by
  refine ⟨hWitness.1, hWitness.2.1, ?_⟩
  rcases hWitness.2.2 with hone | htwo
  · left
    obtain ⟨i, hi, hlarge⟩ := hone
    exact ⟨i, hi,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hab) hlarge⟩
  · right
    obtain ⟨hfinite, hlarge⟩ := htwo
    refine ⟨hfinite, lt_of_le_of_lt ?_ hlarge⟩
    exact mul_le_mul_right'
      (ENNReal.ofReal_le_ofReal hab) hfinite.toFinset.card

theorem finite_groupClosureDimension_mono_tolerance
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha beta : ℝ}
    (hab : alpha ≤ beta)
    (hfinite :
      HasFiniteGroupClosureDimension H groups alpha) :
    HasFiniteGroupClosureDimension H groups beta := by
  obtain ⟨d, hd⟩ := hfinite
  exact ⟨d, fun S hS =>
    hd S (groupClosureWitness_anti_tolerance hab hS)⟩

/-- Published Corollary 3.4: representative uniform generatability is equivalent to
finite group-closure dimension at every positive scale.  Scales above one
are discharged by monotonicity from scale one, matching the source's
unrestricted `α > 0` wording with Definition 2.10's `(0,1]` quantifier. -/
theorem representativelyUniformlyGeneratable_iff_all_finite_groupClosureDimension
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (hpartition : IsCountablePartition groups) :
    RepresentativelyUniformlyGeneratable H groups ↔
      ∀ alpha : ℝ, 0 < alpha →
        HasFiniteGroupClosureDimension H groups alpha := by
  constructor
  · intro hUniform alpha halpha
    by_cases ha : alpha ≤ 1
    · exact
        (alphaRepresentativeUniformlyGeneratable_iff_finite_groupClosureDimension
          hpartition halpha).mp
          (hUniform alpha halpha ha)
    · have hfiniteOne :
          HasFiniteGroupClosureDimension H groups 1 :=
        (alphaRepresentativeUniformlyGeneratable_iff_finite_groupClosureDimension
          hpartition (by norm_num)).mp
          (hUniform 1 (by norm_num) le_rfl)
      exact finite_groupClosureDimension_mono_tolerance
        (le_of_not_ge ha) hfiniteOne
  · intro hfinite alpha halpha _ha
    exact
      (alphaRepresentativeUniformlyGeneratable_iff_finite_groupClosureDimension
        hpartition halpha).mpr
        (hfinite alpha halpha)

end GenLimit.RepresentativeGeneration
