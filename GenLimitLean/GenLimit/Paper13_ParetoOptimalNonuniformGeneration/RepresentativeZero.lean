import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Representative

/-! # Failure at zero tolerance in the printed Theorem 7 -/
namespace GenLimit.ParetoGeneration.Representative
open RepresentativeGeneration
open scoped ENNReal

def singletonPartition (i : Fin 2) : Set ℕ := if i = 0 then {0} else {0}ᶜ

theorem singleton_partition_valid : IsFinitePartition singletonPartition := by
  apply isFinitePartition_of_pairwise_iUnion
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [singletonPartition]
  · apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨0,by simpa [singletonPartition] using hx⟩
    · exact Set.mem_iUnion.mpr ⟨1,by simpa [singletonPartition] using hx⟩

/-- Even an indexed family consisting of the whole universe alone has no
finite time bound at tolerance zero. Once 0 has been observed, freshness
forces zero output mass on its group, which still has positive empirical mass. -/
theorem theorem_7_zero_counterexample :
    IsFinitePartition singletonPartition ∧
    Realizable (fun _ : ℕ ↦ (Set.univ : Set ℕ)) (extendFinitePartition singletonPartition) 0 = ∅ := by
  classical
  refine ⟨singleton_partition_valid,Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro t ⟨_,G,hG⟩
  let xs := List.range (t 0 + 1)
  let S := xs.toFinset
  have h0 : 0 ∈ S := by simp [S,xs]
  have hS : S.Nonempty := ⟨0,h0⟩
  have large : t 0 ≤ S.card := by
    change t 0 ≤ (List.range _).toFinset.card
    rw [List.toFinset_card_of_nodup List.nodup_range,List.length_range]
    omega
  obtain ⟨hr,hvalid⟩ := hG xs hS
  let g := extendFinitePartition singletonPartition
  have hg : g 0 = ({0} : Set ℕ) := by simp [g,extendFinitePartition,singletonPartition]
  have hmass : inducedGroupProbability (G xs) g 0 = 0 := by
    rw [inducedGroupProbability,hg]
    apply groupMass_eq_zero_of_supportedOn_of_disjoint (hvalid 0 large (Set.subset_univ _))
    exact Set.disjoint_left.mpr (fun x hx he ↦ hx.2 (Set.mem_singleton_iff.mp he ▸ h0))
  have hemp : 0 < empiricalGroupProbability S g 0 := by
    rw [empiricalGroupProbability,if_pos hS]
    apply div_pos
    · exact_mod_cast Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨h0,by simp [hg]⟩⟩
    · exact_mod_cast Finset.card_pos.mpr hS
  have h := (coordinate_le_groupSupDistance (G xs) S g 0).trans hr
  rw [hmass,zero_sub,abs_neg,abs_of_pos hemp,ENNReal.ofReal_zero] at h
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr hemp)) (le_antisymm h zero_le')

end GenLimit.ParetoGeneration.Representative
