import GenLimit.Paper05_HallucinationsBreadthAndStability.Uniqueness
import GenLimit.Paper05_HallucinationsBreadthAndStability.StableApproximate
import GenLimit.Paper05_HallucinationsBreadthAndStability.CorrectedStability

/-! # Stable approximate breadth and unambiguous generation -/

namespace GenLimit.BreadthCharacterizations

open scoped symmDiff

/-- Raw stable supports with finite omissions force a tell-tale. Add the
finitely many omissions to the content of a support-locking history. -/
theorem theorem_3_15_approximate_countable [Countable α] (F : Generic.LanguageFamily α)
    (hne : ∀ i, (F i).Nonempty) :
    (∃ G, IsStableGenerator G F ∧ IsApproximateBreadthGenerator G F) ↔ Angluin.ConditionTwo F := by
  refine ⟨?_, conditionTwo_implies_stableApproximate⟩
  rintro ⟨G, stable, approx⟩ i
  classical
  let s := Support.exactPresentation (F i) (hne i)
  have hp : Generic.Presents s (F i) := Support.exactPresentation_presents _ _
  obtain ⟨xs, U, hxs, hl⟩ := Angluin.exists_lockingSequence_of_converges_with_base
    (M := G) hp (fun s hs => by
      obtain ⟨T, hT⟩ := stable i s hs
      exact ⟨supportAt G s T, T, fun t ht => hT t T ht le_rfl⟩)
  have locked {j} (hdata : Angluin.ListWithin xs (F j)) (hsub : F j ⊆ F i) :
      U ⊆ F j ∧ (F j \ U).Finite := by
    let r := Support.exactPresentation (F j) (hne j)
    have hr : Generic.Presents r (F j) := Support.exactPresentation_presents _ _
    obtain ⟨T, hT⟩ := approx j _ (Angluin.prependStream_presents hdata hr)
    have ha := hT (xs.length+T) (Nat.le_add_left ..)
    unfold ApproximateBreadthCorrectAt supportAt at ha
    rw [Angluin.streamPrefix_prependStream, hl _ (fun x hx => hsub
      (Angluin.streamPrefix_listWithin (Generic.streamIn_of_presents hr) T x hx))] at ha
    exact ha
  have hfin := (locked hxs (Set.Subset.refl _)).2
  refine ⟨xs.toFinset ∪ hfin.toFinset, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hxs x (List.mem_toFinset.mp hx)
    · exact (hfin.mem_toFinset.mp hx).1
  · intro j hTj hsub x hx
    have hdata : Angluin.ListWithin xs (F j) := fun y hy =>
      hTj (Finset.mem_union_left _ (List.mem_toFinset.mpr hy))
    by_cases hu : x ∈ U
    · exact (locked hdata hsub).1 hu
    · exact hTj (Finset.mem_union_right _ (hfin.mem_toFinset.mpr ⟨hx,hu⟩))

/-- The strict symmetric-difference comparison in Definition 4.1, with
duplicates of the same target excluded from competition. -/
def UnambiguousFor (F : Generic.LanguageFamily α) (U K : Set α) : Prop :=
  ∀ i, F i ≠ K → (U ∆ K).encard < (U ∆ F i).encard

def GeneratesUnambiguously (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) :=
  EventuallyGeneratesWith (fun xs K => UnambiguousFor F (G xs) K) F

theorem whole_unambiguous {F : Generic.LanguageFamily α} {G : SupportAlgorithm α}
    (h : IsWholeTargetGenerator G F) : GeneratesUnambiguously G F := by
  intro i s hp
  obtain ⟨T, hT⟩ := h i s hp
  refine ⟨T, fun t ht j hj => ?_⟩
  change (supportAt G s t ∆ F i).encard < (supportAt G s t ∆ F j).encard
  rw [show supportAt G s t = F i from hT t ht]
  simpa using Set.encard_pos.mpr (Set.symmDiff_nonempty.mpr (Ne.symm hj))

private theorem unambiguous_necessary [Countable α] {F : Generic.LanguageFamily α}
    (hne : ∀ i, (F i).Nonempty) {G : SupportAlgorithm α} (h : GeneratesUnambiguously G F) :
    Angluin.ConditionTwo F := by
  apply theorem_3_5 hne _ h
  intro xs i j hi hj
  by_contra hij
  exact lt_asymm (hi j (Ne.symm hij)) (hj i hij)

/-- Theorem 4.5's stable unambiguous clause. -/
theorem theorem_4_5_unambiguous [Countable α] (F : Generic.LanguageFamily α)
    (hne : ∀ i, (F i).Nonempty) :
    (∃ G, IsStableGenerator G F ∧ GeneratesUnambiguously G F) ↔ Angluin.ConditionTwo F := by
  refine ⟨fun ⟨_,_,h⟩ => unambiguous_necessary hne h, ?_⟩
  intro hc
  obtain ⟨G,hG,hs⟩ := conditionTwo_implies_stableWholeTarget hc
  exact ⟨G,hs,whole_unambiguous hG⟩

/-- Theorem 4.3's unambiguous clause. -/
theorem theorem_4_3_unambiguous [Countable α] (F : Generic.LanguageFamily α)
    (hne : ∀ i, (F i).Nonempty) :
    (∃ G, GeneratesUnambiguously G F) ↔ Angluin.ConditionTwo F := by
  refine ⟨fun ⟨_,h⟩ => unambiguous_necessary hne h, fun h => ?_⟩
  obtain ⟨G,_,hG⟩ := (theorem_4_5_unambiguous F hne).mpr h
  exact ⟨G,hG⟩

end GenLimit.BreadthCharacterizations
