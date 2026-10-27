import GenLimit.Paper03_HallucinationAndModeCollapse.SubsetIdentification
import GenLimit.Paper03_HallucinationAndModeCollapse.FiniteWitnessRates
import GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions

/-!
# Proposition 3.10: finite witnesses and exponential subset-oracle identification

The implemented last-critical selector is the source Appendix B.1 rule.
A target tell-tale and one positive counterexample to each earlier language
which fails to contain the target suffice for correct language prediction.
Those finite sets occur only in the proof; the procedure never receives them.
Lemma 8.1 gives exponential error bounds with distribution-dependent positive
constants. Membership and subset queries are the only oracle access used.

Loss compares languages, so duplicate indices are allowed and the selected
index may vary among names of the same target. A fixed-index online
postprocessing theorem and Appendix B.2's breadth generator are not asserted
by this statistical proposition.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.Support

theorem subsetIdentifier_last_critical {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C) (xs : List ℕ)
    (k : ℕ) (hk : k < xs.length) (hcrit : SubsetCritical C xs k) :
    subsetIdentifier O S xs < xs.length ∧
      SubsetCritical C xs (subsetIdentifier O S xs) ∧ k ≤ subsetIdentifier O S xs := by
  let data := (xs, (subsetIdentificationQueries xs).map (subsetIdentificationOracle O S))
  have ht : subsetTableCritical data k = true := (subsetTableCritical_iff O S xs k hk).mpr hcrit
  have hne : lastTrue subsetTableCritical data xs.length ≠ none := by
    intro hnone
    have hf := (lastTrue_eq_none_iff _ _ _).mp hnone k hk
    simp [ht] at hf
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hne
  have he : subsetIdentifier O S xs = j := by
    change (lastTrue subsetTableCritical data xs.length).getD 0 = j
    rw [hj]
    rfl
  rw [he]
  exact ⟨(lastTrue_spec hj).1,
    (subsetTableCritical_iff O S xs j (lastTrue_spec hj).1).mp (lastTrue_spec hj).2,
    lastTrue_ge_of_true hj hk ht⟩

/-- A finite source tell-tale and finitely many earlier-candidate
counterexamples give one distribution-independent positive witness. -/
theorem subsetIdentifier_finiteWitness (C : Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C)
    (hC : GenLimit.Angluin.ConditionTwo C) : FiniteWitnessIdentifies C (subsetIdentifier O S) := by
  classical
  intro i
  obtain ⟨T, hT⟩ := hC i
  let bad := (Finset.range i).filter (fun k => ¬C i ⊆ C k)
  have hex (k : {k // k ∈ bad}) : ∃ x, x ∈ C i ∧ x ∉ C k.1 :=
    Set.not_subset.mp (Finset.mem_filter.mp k.2).2
  let witness := fun k : {k // k ∈ bad} => Classical.choose (hex k)
  let W := T ∪ bad.attach.image witness
  refine ⟨W, ?_, i + 1, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hT.1 hx
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact (Classical.choose_spec (hex k)).1
  · intro xs hn hxs hobs
    have hi : SubsetCritical C xs i := by
      refine ⟨hxs, ?_⟩
      intro k hk hkc
      by_contra hnot
      have hkbad : k ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hnot⟩
      let b : {k // k ∈ bad} := ⟨k, hkbad⟩
      have hw := Classical.choose_spec (hex b)
      have hwW : witness b ∈ W := Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨b, Finset.mem_attach _ _, rfl⟩)
      exact hw.2 (hkc (witness b) (hobs (witness b) hwW))
    have hib : i < xs.length := by omega
    obtain ⟨_, hj, hij⟩ := subsetIdentifier_last_critical O S xs i hib hi
    let j := subsetIdentifier O S xs
    change C j = C i
    by_cases he : j = i
    · rw [he]
    · have hijlt : i < j := by omega
      have hsub : C j ⊆ C i := hj.2 i hijlt hxs
      apply Set.Subset.antisymm hsub
      apply hT.2 j _ hsub
      intro x hx
      exact hj.1 x (hobs x (Finset.mem_union_left _ hx))

theorem subsetIdentifier_exponential (C : Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C)
    (hC : GenLimit.Angluin.ConditionTwo C) :
    ExponentialIdentifies C (deterministicIdentifier (subsetIdentifier O S)) :=
  lemma_8_1 C _ (subsetIdentifier_finiteWitness C O S hC)

/-- Proposition 3.10 with a fixed certified finite-query program and
ordinary computation when both supplied oracles are computable. The program
depends on neither a tell-tale oracle nor the target distribution. -/
theorem proposition_3_10 (C : Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C)
    (hC : GenLimit.Angluin.ConditionTwo C) :
    ExponentialIdentifies C (deterministicIdentifier (subsetIdentifier O S)) ∧
      (Computable₂ O.query → Computable₂ S.query → Computable (subsetIdentifier O S)) :=
  ⟨subsetIdentifier_exponential C O S hC, subsetIdentifier_computable O S⟩

end GenLimit.HallucinationModeCollapse
