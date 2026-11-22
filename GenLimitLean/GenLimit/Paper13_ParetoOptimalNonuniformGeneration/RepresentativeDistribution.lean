import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.RepresentativeScan

/-! # The Section 5 representative distribution
The mass on unavailable groups is divided equally among all available
groups. Each available group uses a single fresh point in the selected
intersection. If no language is selected, use the empirical distribution. -/
namespace GenLimit.ParetoGeneration.Representative
open RepresentativeGeneration
open scoped ENNReal
variable {α : Type*} [DecidableEq α]

private theorem available_finite {k : ℕ} (groups : Fin k → Set α)
    (H : Set (Set α)) (S : Finset α) :
    (unavailableGroups H (extendFinitePartition groups) S)ᶜ.Finite := by
  apply (Finset.range k).finite_toSet.subset
  intro i hi
  apply Finset.mem_range.mpr
  apply active_extendFinitePartition_index_lt groups
  have hne : unseenClosure H S ∩ extendFinitePartition groups i ≠ ∅ := hi
  exact (Set.nonempty_iff_ne_empty.mpr hne).mono Set.inter_subset_right

private noncomputable def equalAllocation (A : Set ℕ) (hA : A.Finite) (hne : A.Nonempty)
    (total cap : ENNReal) (hcap : total ≤ cap * hA.toFinset.card) :
    BoundedMassAllocation A cap total := by
  classical
  let F := hA.toFinset
  let weight (i : ℕ) := if i ∈ F then total / F.card else 0
  refine ⟨weight,?_,?_,?_⟩
  · intro i hi
    by_contra h
    exact hi (by simp [weight,F,h])
  · intro i
    by_cases hi : i ∈ F
    · simp only [weight,if_pos hi]
      exact ENNReal.div_le_of_le_mul hcap
    · simp [weight,hi]
  · rw [tsum_eq_sum (s := F) (fun i hi ↦ by simp [weight,hi])]
    simp only [weight,Finset.sum_ite_mem,F,Finset.inter_self]
    rw [Finset.sum_const,nsmul_eq_mul]
    exact ENNReal.mul_div_cancel (a := (hA.toFinset.card : ENNReal)) (b := total)
      (by exact_mod_cast Finset.card_ne_zero.mpr (by simpa only [Set.Finite.toFinset_nonempty] using hne)) (by simp)

private theorem closure_of_feasible {F : ℕ → Set α} {g : ℕ → Set α} {ε : ℝ} {S : Finset α}
    {W : Finset ℕ} (hW : W.Nonempty) (h : Feasible F g ε S W) :
    ClosureFeasibleAt (F '' (↑W : Set ℕ)) g ε S := by
  obtain ⟨μ,hr,hm⟩ := h
  refine ⟨μ,fun x hx ↦ ⟨?_,?_⟩,hr⟩
  · rintro L ⟨⟨j,hj,rfl⟩,_⟩
    exact (hm j hj x hx).1
  · obtain ⟨j,hj⟩ := hW
    exact (hm j hj x hx).2

/-- This finite-partition version also handles zero capacity. -/
private theorem no_capacity_failure {H : Set (Set α)} {g : ℕ → Set α} {ε : ℝ} {S : Finset α}
    (hp : IsCountablePartition g) (hε : 0 ≤ ε) (hs : S.Nonempty) (hf : ClosureFeasibleAt H g ε S) :
    ¬ groupClosureConditionTwo H g ε S := by
  rcases hε.eq_or_lt with h | h
  · subst ε
    have hzero (i : ℕ) (hi : i ∈ unavailableGroups H g S) :
        ENNReal.ofReal (empiricalGroupProbability S g i) = 0 := by
      simpa using unavailable_coordinate_le_of_closureFeasible hf hi
    have massZero : empiricalMassOnGroupIndices S g (unavailableGroups H g S) = 0 := by
      unfold empiricalMassOnGroupIndices
      apply ENNReal.tsum_eq_zero.mpr
      intro i
      split
      next hi => exact hzero i hi
      next => rfl
    rintro ⟨hfin,hlt⟩
    simp [massZero] at hlt
  · exact closureFeasible_not_groupClosureConditionTwo hp h hs hf

private theorem available_nonempty {H : Set (Set α)} {g : ℕ → Set α} {S : Finset α} {ε : ℝ}
    (hp : IsCountablePartition g) (hs : S.Nonempty) (h2 : ¬ groupClosureConditionTwo H g ε S) :
    (unavailableGroups H g S)ᶜ.Nonempty := by
  by_contra hn
  have he := Set.not_nonempty_iff_eq_empty.mp hn
  have hfin : (unavailableGroups H g S)ᶜ.Finite := he ▸ Set.finite_empty
  have hadd := empiricalMass_add_compl S g hp hs (unavailableGroups H g S)
  have hem : empiricalMassOnGroupIndices S g (unavailableGroups H g S)ᶜ = 0 := by
    rw [he]; simp [empiricalMassOnGroupIndices]
  apply h2
  refine ⟨hfin,?_⟩
  have hc : hfin.toFinset = ∅ := by ext i; simp only [Set.Finite.mem_toFinset,Finset.notMem_empty,iff_false]; rw [he]; simp
  simpa [hc,hem,show empiricalMassOnGroupIndices S g (unavailableGroups H g S) = 1 by simpa [hem] using hadd]

private noncomputable def allocation {k : ℕ} (groups : Fin k → Set α) (hp : IsFinitePartition groups)
    (H : Set (Set α)) (S : Finset α) (hs : S.Nonempty) (ε : ℝ)
    (h2 : ¬ groupClosureConditionTwo H (extendFinitePartition groups) ε S) :=
  let g := extendFinitePartition groups
  let A := (unavailableGroups H g S)ᶜ
  let hA := available_finite groups H S
  equalAllocation A hA (available_nonempty hp hs h2)
    (empiricalMassOnGroupIndices S g (unavailableGroups H g S)) (ENNReal.ofReal ε)
    (le_of_not_gt (fun h ↦ h2 ⟨hA,h⟩))

/-- For finite partitions the actual scarcity tests characterize a feasible
insertion also at the exact-representation endpoint. -/
theorem scarcity_iff_finite {k : ℕ} (F : ℕ → Set α) (groups : Fin k → Set α)
    (hp : IsFinitePartition groups) (ε : ℝ) (hε : 0 ≤ ε) (S : Finset α) (hs : S.Nonempty)
    (W : Finset ℕ) (hw : W.Nonempty) (hc : ∀ j ∈ W, (↑S : Set α) ⊆ F j) :
    let g := extendFinitePartition groups
    let H := F '' (↑W : Set ℕ)
    Feasible F g ε S W ↔ ¬ groupClosureConditionOne H g ε S ∧ ¬ groupClosureConditionTwo H g ε S := by
  let g := extendFinitePartition groups
  let H := F '' (↑W : Set ℕ)
  constructor
  · intro hf
    have h := closure_of_feasible hw hf
    exact ⟨closureFeasible_not_groupClosureConditionOne h,no_capacity_failure hp hε hs h⟩
  · rintro ⟨h1,h2⟩
    let A := allocation groups hp H S hs ε h2
    let μ := closureRedistributedDistribution H g S hp hs A
    refine ⟨μ,iSup_le (fun i ↦ ?_),fun j hj x hx ↦ ?_⟩
    · rw [closureRedistributedDistribution_groupProbability H g S hp hs A i]
      exact redistributedGroupPMF_coordinate_close H g S hp hs A h1 i
    · have ht := closureRedistributedDistribution_supportedOn H g S hp hs A x hx
      exact ⟨ht.1 _ ⟨⟨j,hj,rfl⟩,hc j hj⟩,ht.2⟩

private noncomputable def output {k : ℕ} (F : ℕ → Set α) (groups : Fin k → Set α)
    (hp : IsFinitePartition groups) (ε : ℝ) (hε : 0 ≤ ε) (S : Finset α) (hs : S.Nonempty)
    (W : Finset ℕ) (hf : Feasible F (extendFinitePartition groups) ε S W) :
    DiscreteDistribution α :=
  if hw : W.Nonempty then
    let H := F '' (↑W : Set ℕ)
    let h2 := no_capacity_failure hp hε hs (closure_of_feasible hw hf)
    closureRedistributedDistribution H _ S hp hs (allocation groups hp H S hs ε h2)
  else empiricalPointDistribution S hs

private theorem output_spec {k : ℕ} (F : ℕ → Set α) (groups : Fin k → Set α)
    (hp : IsFinitePartition groups) (ε : ℝ) (hε : 0 ≤ ε) (S : Finset α) (hs : S.Nonempty)
    (W : Finset ℕ) (hf : Feasible F (extendFinitePartition groups) ε S W)
    (hc : ∀ j ∈ W, (↑S : Set α) ⊆ F j) :
    let μ := output F groups hp ε hε S hs W hf
    groupSupDistance μ S (extendFinitePartition groups) ≤ ENNReal.ofReal ε ∧
      ∀ j ∈ W, SupportedOn μ (F j \ (↑S : Set α)) := by
  classical
  dsimp only
  by_cases hw : W.Nonempty
  · let g := extendFinitePartition groups
    let H := F '' (↑W : Set ℕ)
    let h := closure_of_feasible hw hf
    let A := allocation groups hp H S hs ε (no_capacity_failure hp hε hs h)
    change groupSupDistance _ _ _ ≤ _ ∧ _
    rw [output,dif_pos hw]
    refine ⟨iSup_le (fun i ↦ ?_),?_⟩
    · rw [closureRedistributedDistribution_groupProbability H g S hp hs A i]
      exact redistributedGroupPMF_coordinate_close H g S hp hs A (closureFeasible_not_groupClosureConditionOne h) i
    · intro j hj x hx
      have ht := closureRedistributedDistribution_supportedOn H g S hp hs A x hx
      exact ⟨ht.1 _ ⟨⟨j,hj,rfl⟩,hc j hj⟩,ht.2⟩
  · simp only [output,dif_neg hw,empiricalPointDistribution_distance_zero]
    exact ⟨bot_le,fun j hj ↦ (hw ⟨j,hj⟩).elim⟩

/-- The published scan order, scarcity tests, and equal-mass redistribution. -/
noncomputable def generate {k : ℕ} [Nonempty α] (F : ℕ → Set α) (groups : Fin k → Set α)
    (hp : IsFinitePartition groups) (ε : ℝ) (hε : 0 ≤ ε) (f : ℕ → ℕ) (xs : List α) :
    DiscreteDistribution α := by
  classical
  let S := xs.toFinset
  let g := extendFinitePartition groups
  let order := scoreOrder (complexity F g ε) (f S.card)
  exact if hs : S.Nonempty then output F groups hp ε hε S hs
    (greedyListScanBy (accepts F g ε S) ∅ order) (scan_valid F g ε S hs order).1
    else DiscreteDistribution.ofPMF (PMF.pure (Classical.choice (inferInstance : Nonempty α)))

theorem theorem_7_algorithm {k : ℕ} [Nonempty α] (F : ℕ → Set α) (groups : Fin k → Set α)
    (hp : IsFinitePartition groups) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : BoundedRawScores F (extendFinitePartition groups) ε)
    (f : ℕ → ℕ) (hf : IsUnboundedScheduler f) (xs : List α) (hs : xs.toFinset.Nonempty) :
    let S := xs.toFinset
    let g := extendFinitePartition groups
    let μ := generate F groups hp ε hε f xs
    groupSupDistance μ S g ≤ ENNReal.ofReal ε ∧ ∀ i,
      max (schedulerEntryTime f hf i) (complexity F g ε i + 1) ≤ S.card →
      (↑S : Set α) ⊆ F i → SupportedOn μ (F i \ (↑S : Set α)) := by
  classical
  let S := xs.toFinset
  let g := extendFinitePartition groups
  let l := scoreOrder (complexity F g ε) (f S.card)
  let W := greedyListScanBy (accepts F g ε S) ∅ l
  have h := scan_valid F g ε S hs l
  have ho := output_spec F groups hp ε hε S hs W h.1 h.2
  simp only [generate,dif_pos hs]
  refine ⟨ho.1,fun i ht hc ↦ ho.2 i ?_⟩
  apply scan_includes_due F g ε hb.intrinsic S hs i ((le_max_right _ _).trans ht) hc l
    (sorted_scoreOrder _ _) ((mem_scoreOrder _ _ _).mpr ((schedulerEntryTime_le_iff f hf).mp ((le_max_left _ _).trans ht)))
  simp

end GenLimit.ParetoGeneration.Representative
