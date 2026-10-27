import GenLimit.Paper03_HallucinationAndModeCollapse.LabeledIdentificationModel
import GenLimit.Core.Basic
import GenLimit.Support.ComputableSearch
import GenLimit.Support.ComputableLists

/-!
# Bounded enumeration from labeled observations

At sample length `n`, test each index below `n` for agreement with every
observed label, and return the least consistent index (zero if none exists).
Only membership queries are used. This is the Boolean implementation of
Gold's informant compatibility test; no tell-tale or subset oracle is read.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.Support GenLimit.Gold.Informant

def labeledConsistent {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (xs : List LabeledDatum) (j : ℕ) : Bool :=
  xs.all (fun z => O.query j z.1 == z.2)

theorem labeledConsistent_iff {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (xs : List LabeledDatum) (j : ℕ) :
    labeledConsistent O xs j = true ↔ InformantCompatible xs (C j) := by
  simp only [labeledConsistent, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h z hz
    rw [← h z hz]
    exact O.query_spec
  · intro h z hz
    exact Bool.eq_iff_iff.mpr (O.query_spec.trans (h z hz).symm)

def labeledEnumerationLearner {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (xs : List LabeledDatum) : ℕ :=
  (firstTrue (labeledConsistent O) xs xs.length).getD 0

theorem labeledConsistent_computable {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (hO : Computable₂ O.query) :
    Computable₂ (labeledConsistent O) := by
  have hq : Computable (fun z : (List LabeledDatum × ℕ) × LabeledDatum => O.query z.1.2 z.2.1) :=
    hO.comp (Computable.snd.comp Computable.fst) (Computable.fst.comp Computable.snd)
  exact (ComputableLists.all (l := fun z : List LabeledDatum × ℕ => z.1)
    (f := fun z w => O.query z.2 w.1 == w.2) Computable.fst
    (Primrec.beq.to_comp.comp hq (Computable.snd.comp Computable.snd)).to₂).to₂

theorem labeledEnumerationLearner_computable {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (hO : Computable₂ O.query) :
    Computable (labeledEnumerationLearner O) :=
  Computable.option_getD
    ((firstTrue_computable (labeledConsistent_computable O hO)).comp Computable.id
      Computable.list_length) (Computable.const 0)

/-- A finite collection of candidate languages has finitely many correctly
labeled separating points. No effectiveness of this proof witness is needed
by the learner. -/
theorem finite_labeled_separators (C : Generic.LanguageFamily ℕ) (i : ℕ) (s : Finset ℕ) :
    ∃ T : Finset LabeledDatum, (∀ z ∈ T, CorrectLabel C i z) ∧
      ∀ xs : List LabeledDatum, (∀ z ∈ T, z ∈ xs) →
        ∀ j ∈ s, InformantCompatible xs (C j) → C j = C i := by
  classical
  have hw (j : ℕ) : ∃ T : Finset LabeledDatum, (∀ z ∈ T, CorrectLabel C i z) ∧
      ∀ xs : List LabeledDatum, (∀ z ∈ T, z ∈ xs) →
        InformantCompatible xs (C j) → C j = C i := by
    by_cases h : C j = C i
    · exact ⟨∅, by simp, fun _ _ _ => h⟩
    · have hdiff : ∃ x, ¬ (x ∈ C j ↔ x ∈ C i) := by
        by_contra hn
        push_neg at hn
        exact h (Set.ext hn)
      obtain ⟨x, hx⟩ := hdiff
      let z : LabeledDatum := (x, decide (x ∈ C i))
      have hz : CorrectLabel C i z := by simp [CorrectLabel, z]
      refine ⟨{z}, ?_, ?_⟩
      · simpa using hz
      · intro xs hxs hc
        exact False.elim (hx ((hc z (hxs z (by simp))).symm.trans hz))
  choose T hT hforce using hw
  refine ⟨s.biUnion T, ?_, ?_⟩
  · intro z hz
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hz
    exact hT j z hj
  · intro xs hxs j hj hc
    exact hforce j xs (fun z hz => hxs z (Finset.mem_biUnion.mpr ⟨j, hj, hz⟩)) hc

theorem labeledEnumeration_finiteWitness (C : Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) :
    FiniteLabeledWitnessIdentifies C (labeledEnumerationLearner O) := by
  intro i
  obtain ⟨T, hT, hforce⟩ := finite_labeled_separators C i (Finset.range (i + 1))
  refine ⟨T, hT, i + 1, ?_⟩
  intro xs hn hc hxs
  have hi : i < xs.length := by omega
  have ht : labeledConsistent O xs i = true := (labeledConsistent_iff O xs i).mpr hc
  have hne : firstTrue (labeledConsistent O) xs xs.length ≠ none := by
    intro hnone
    have hf := (firstTrue_eq_none_iff _ _ _).mp hnone i hi
    simp [ht] at hf
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hne
  have hji : j ≤ i := firstTrue_le_of_true hj hi ht
  have hjc : InformantCompatible xs (C j) :=
    (labeledConsistent_iff O xs j).mp (firstTrue_spec hj).2.1
  simpa [labeledEnumerationLearner, hj] using
    hforce xs hxs j (Finset.mem_range.mpr (by omega)) hjc

end GenLimit.HallucinationModeCollapse
