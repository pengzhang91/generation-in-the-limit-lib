import GenLimit.Paper03_HallucinationAndModeCollapse.SubsetIdentificationRates
import GenLimit.Paper03_HallucinationAndModeCollapse.OnlineBreadthConstruction
import GenLimit.Paper01_LanguageGeneration.Critical

/-! # Online identification and generation with the Appendix B subset oracle -/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Support

variable {C : Generic.LanguageFamily ℕ}

/-- The subset oracle decides equality of two indexed languages in two queries. -/
def sameName (S : SubsetOracle C) (i j : ℕ) : Bool := S.query i j && S.query j i

private theorem sameName_spec (S : SubsetOracle C) (i j : ℕ) :
    sameName S i j = true ↔ C i = C j := by
  simp only [sameName, Bool.and_eq_true, S.query_spec]
  exact ⟨fun h => Set.Subset.antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

def leastName (S : SubsetOracle C) (i : ℕ) : ℕ :=
  (firstTrue (sameName S) i (i+1)).getD i

private theorem leastName_spec (S : SubsetOracle C) (i : ℕ) :
    C (leastName S i) = C i ∧ ∀ j, C j = C i → leastName S i ≤ j := by
  have self := (sameName_spec S i i).mpr rfl
  have hn : firstTrue (sameName S) i (i+1) ≠ none := by
    intro hh
    simpa [self] using (firstTrue_eq_none_iff _ _ _).mp hh i (Nat.lt_succ_self _)
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hn
  simp only [leastName, hk, Option.getD_some]
  refine ⟨((sameName_spec S i k).mp (firstTrue_spec hk).2.1).symm, fun j hj => ?_⟩
  by_cases hji : j < i+1
  · exact firstTrue_le_of_true hk hji ((sameName_spec S i j).mpr hj.symm)
  · have := (firstTrue_spec hk).1
    omega

private theorem leastName_congr (S : SubsetOracle C) {i j : ℕ} (h : C i = C j) :
    leastName S i = leastName S j := by
  obtain ⟨hi, hli⟩ := leastName_spec S i
  obtain ⟨hj, hlj⟩ := leastName_spec S j
  exact le_antisymm (hli _ (hj.trans h.symm)) (hlj _ (hi.trans h))

def stableSubsetIdentifier (O : MembershipOracle C) (S : SubsetOracle C) : Learner ℕ ℕ :=
  leastName S ∘ subsetIdentifier O S

theorem stableSubsetIdentifier_computable (O : MembershipOracle C) (S : SubsetOracle C)
    (hO : Computable₂ O.query) (hS : Computable₂ S.query) :
    Computable (stableSubsetIdentifier O S) := by
  have he : Computable₂ (sameName S) :=
    (Primrec.and.to_comp.comp (hS.comp Computable.fst Computable.snd)
      (hS.comp Computable.snd Computable.fst)).to₂
  have hl : Computable (leastName S) := Computable.option_getD
    ((firstTrue_computable he).comp Computable.id Computable.succ) Computable.id
  exact hl.comp (subsetIdentifier_computable O S hO hS)

private theorem prefix_in_target {s : ℕ → ℕ} {K : Set ℕ} (hp : Generic.Presents s K)
    (t : ℕ) : ∀ x ∈ textPrefix s t, x ∈ K := by
  intro x hx
  obtain ⟨k, _, rfl⟩ := mem_textPrefix_iff.mp hx
  exact hp ▸ Set.mem_range_self k

/-- B.1. The fixed learner reads membership and inclusion bits. Finite
tell-tales certify convergence without entering the learning procedure. -/
theorem theorem_B_1 (O : MembershipOracle C) (S : SubsetOracle C)
    (hid : IdentifiableInLimit C) :
    Angluin.SemanticallyIdentifies (stableSubsetIdentifier O S) C := by
  intro i s hp
  obtain ⟨W, hW, n, hn⟩ := subsetIdentifier_finiteWitness C O S
    ((Angluin.semanticallyInferrable_iff_conditionTwo C).mp hid) i
  obtain ⟨T, hT⟩ := Generic.finset_eventually_subset_sample hp W (fun x hx => hW x hx)
  refine ⟨leastName S i, (leastName_spec S i).1, max T n, fun t ht => ?_⟩
  apply leastName_congr
  apply hn _ (by simpa using (Nat.le_max_right T n).trans ht) (prefix_in_target hp t)
  intro x hx
  exact mem_textPrefix_iff.mpr (Generic.mem_sample_iff.mp
    (Generic.sample_mono ((Nat.le_max_left T n).trans ht) (hT hx)))

private theorem selected_subset_eventually (O : MembershipOracle C) (S : SubsetOracle C)
    {s : ℕ → ℕ} {i : ℕ} (hp : Generic.Presents s (C i)) :
    ∃ T, ∀ t ≥ T, C (subsetIdentifier O S (textPrefix s t)) ⊆ C i := by
  obtain ⟨T, hT⟩ := target_eventually_critical (C := C) (z := i) hp
  refine ⟨max T (i+1), fun t ht => ?_⟩
  have hc := hT t ((Nat.le_max_left ..).trans ht)
  have hi : SubsetCritical C (textPrefix s t) i := by
    refine ⟨prefix_in_target hp t, fun k hk hcon => hc.2 k hk.le ?_⟩
    intro x hx
    exact hcon x (mem_textPrefix_iff.mpr (mem_sample_iff.mp hx))
  have hit : i < t := (Nat.le_max_right ..).trans ht
  obtain ⟨_, hj, hij⟩ := subsetIdentifier_last_critical O S _ i (by simpa using hit) hi
  rcases lt_or_eq_of_le hij with h | h
  · exact hj.2 i h hi.1
  · rw [h]

/-- One Appendix B.2 sampler, defined for every family before asking whether
it is identifiable. Every seed is decoded by the full-support fresh sampler. -/
noncomputable def subsetBreadth (O : OracleFamily) (S : SubsetOracle O.language) :
    StatisticalGenerator :=
  identifiedBreadth O (stableSubsetIdentifier (familyMembership O) S)

/-- B.2. The same trained law is eventually supported on unseen target points
in every family and has full fresh support in every identifiable family. -/
theorem corollary_B_2 (O : OracleFamily) (S : SubsetOracle O.language) :
    (∀ i s, Generic.Presents s (O.language i) → ∃ T, ∀ t ≥ T,
      let U := (subsetBreadth O S (textPrefix s t)).support
      U.Nonempty ∧ U ⊆ O.language i \ ↑(Generic.sample s t)) ∧
    (IdentifiableInLimit O.language →
      FreshBreadthInLimit (statisticalSupportView (subsetBreadth O S)) O.language) := by
  constructor
  · intro i s hp
    obtain ⟨T, hT⟩ := selected_subset_eventually (familyMembership O) S hp
    refine ⟨T, fun t ht => ⟨PMF.support_nonempty _, ?_⟩⟩
    change (identifiedBreadth O _ _).support ⊆ _
    rw [identifiedBreadth_support, observedPrefix_set]
    apply Set.diff_subset_diff_left
    change O.language (leastName S (subsetIdentifier _ S _)) ⊆ _
    rw [(leastName_spec S _).1]
    exact hT t ht
  · intro hid
    exact identifiedBreadth_online O _ (theorem_B_1 _ S hid)

end GenLimit.HallucinationModeCollapse
