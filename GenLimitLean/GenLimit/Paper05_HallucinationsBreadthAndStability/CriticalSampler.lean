import GenLimit.Paper05_HallucinationsBreadthAndStability.EffectiveBreadth
import GenLimit.Paper03_HallucinationAndModeCollapse.SubsetIdentificationRates

/-! # The three guarantees of the same subset-oracle function (Corollary 7.2) -/

namespace GenLimit.BreadthCharacterizations
open GenLimit.HallucinationModeCollapse GenLimit.CharikarPabbaraju

/-- Train with the KM last-critical subset-oracle program, then sample from
the selected language after deleting the observations (footnote 10). -/
noncomputable def criticalSampler (O : OracleFamily) (S : SubsetOracle O.language) : StatisticalGenerator :=
  identifiedBreadth O (subsetIdentifier (familyMembership O) S)

/-- Eventually the focus contains the observed set and is contained in the target. -/
theorem critical_focus_between (O : OracleFamily) (S : SubsetOracle O.language)
    {s : ℕ → ℕ} {z : ℕ} (hp : Generic.Presents s (O.language z)) :
    ∃ N, ∀ t ≥ N, let j := subsetIdentifier (familyMembership O) S (textPrefix s t)
      (Generic.sample s t : Set ℕ) ⊆ O.language j ∧ O.language j ⊆ O.language z := by
  obtain ⟨T,hT⟩ := exhaustiveTarget_eventually_critical hp
  refine ⟨max T (z+1),fun t ht ↦ ?_⟩
  have cons (i) : (∀ x ∈ textPrefix s t, x ∈ O.language i) ↔
      (Generic.sample s t : Set ℕ) ⊆ O.language i := by
    simp only [Set.subset_def, Finset.mem_coe, Generic.mem_sample_iff, mem_textPrefix_iff]
  have crit := hT t ((Nat.le_max_left ..).trans ht)
  have hz : SubsetCritical O.language (textPrefix s t) z := by
    refine ⟨(cons z).mpr (exhaustiveHistoryConsistent_prefix_iff.mp crit.1),fun i hi h ↦ ?_⟩
    exact crit.2 i hi.le (exhaustiveHistoryConsistent_prefix_iff.mpr ((cons i).mp h))
  have hzlt : z < (textPrefix s t).length := by
    rw [textPrefix_length]
    exact (Nat.le_max_right ..).trans ht
  obtain ⟨_,hj,hzj⟩ := subsetIdentifier_last_critical (familyMembership O) S _ z hzlt hz
  exact ⟨(cons _).mp hj.1, (eq_or_lt_of_le hzj).elim
    (fun e ↦ e ▸ Set.Subset.rfl) (fun h ↦ hj.2 z h hz.1)⟩

private theorem criticalSupport (O : OracleFamily) (S : SubsetOracle O.language) (s : ℕ → ℕ) (t : ℕ) :
    supportAt (lawSupport (criticalSampler O S)) s t =
      O.language (subsetIdentifier (familyMembership O) S (textPrefix s t)) \ (Generic.sample s t : Set ℕ) := by
  rw [supportAt,lawSupport,criticalSampler,identifiedBreadth_support]
  congr 1
  ext x
  exact mem_textPrefix_iff.trans Generic.mem_sample_iff.symm

/-- All three clauses use one trained probability law. Infinite coverage
actually holds without a hypothesis on the family, and approximate breadth
also holds when the strong tell-tale condition is available. -/
theorem corollary_7_2 (O : OracleFamily) (S : SubsetOracle O.language) :
    let G := lawSupport (criticalSampler O S)
    (Angluin.ConditionTwo O.language → IsExactBreadthGenerator G O.language) ∧
    (WeakAngluinCondition O.language → IsApproximateBreadthGenerator G O.language) ∧
    IsInfiniteCoverageGenerator G O.language := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro h z s hp
    obtain ⟨W,hW⟩ := h z
    obtain ⟨M,hM⟩ := Generic.finset_eventually_subset_sample hp W hW.1
    obtain ⟨N,hN⟩ := critical_focus_between O S hp
    refine ⟨max N M,fun t ht ↦ ?_⟩
    obtain ⟨hseen,hsub⟩ := hN t ((Nat.le_max_left ..).trans ht)
    have hw : (W : Set ℕ) ⊆ O.language _ := fun x hx ↦
      hseen (Generic.sample_mono ((Nat.le_max_right ..).trans ht) (hM hx))
    rw [ExactBreadthCorrectAt,criticalSupport,hW.eq_of_between hw hsub]
  · intro h z s hp
    obtain ⟨W,hW,hfinite⟩ := h z
    obtain ⟨M,hM⟩ := Generic.finset_eventually_subset_sample hp W hW
    obtain ⟨N,hN⟩ := critical_focus_between O S hp
    refine ⟨max N M,fun t ht ↦ ?_⟩
    let j := subsetIdentifier (familyMembership O) S (textPrefix s t)
    obtain ⟨hseen,hsub⟩ := hN t ((Nat.le_max_left ..).trans ht)
    have hw : (W : Set ℕ) ⊆ O.language j := fun x hx ↦
      hseen (Generic.sample_mono ((Nat.le_max_right ..).trans ht) (hM hx))
    have hf : (O.language z \ O.language j).Finite := by
      rcases eq_or_lt_of_le hsub with e | strict
      · change (O.language z \ O.language (subsetIdentifier ..)).Finite
        rw [e]; simp
      · exact hfinite j hw strict
    rw [ApproximateBreadthCorrectAt,criticalSupport]
    refine ⟨Set.Subset.trans Set.diff_subset hsub,(hf.union (Generic.sample s t).finite_toSet).subset ?_⟩
    intro x hx
    by_cases obs : x ∈ Generic.sample s t
    · exact Or.inr obs
    · exact Or.inl ⟨hx.1,fun hxj ↦ hx.2 ⟨hxj,obs⟩⟩
  · intro z s hp
    obtain ⟨N,hN⟩ := critical_focus_between O S hp
    refine ⟨N,fun t ht ↦ ?_⟩
    rw [InfiniteCoverageCorrectAt,criticalSupport]
    exact ⟨Set.Subset.trans Set.diff_subset (hN t ht).2,Set.disjoint_sdiff_left,
      (O.infinite' _).diff (Generic.sample s t).finite_toSet⟩

/-- Access guarantees for the very same law used in all three clauses. -/
theorem criticalSampler_oracles (O : OracleFamily) (S : SubsetOracle O.language) :
    OracleMOP (generationOracle O) (criticalSampler O S) ∧
      (Computable₂ O.query → Computable₂ S.query →
        HasComputableSampler (criticalSampler O S) ∧ UniformDecidableMOP (criticalSampler O S)) := by
  refine ⟨identifiedBreadth_oracleMOP O _, fun ho hs ↦ ?_⟩
  have hA := subsetIdentifier_computable (familyMembership O) S ho hs
  exact ⟨identifiedBreadth_computableSampler O ho _ hA, identifiedBreadth_uniformMOP O ho _ hA⟩

/-- Lemma 7.1 with the membership and subset oracles as algorithm inputs. -/
theorem lemma_7_1 (O : OracleFamily) (S : SubsetOracle O.language)
    (hw : WeakAngluinCondition O.language) :
    IsApproximateBreadthGenerator (lawSupport (criticalSampler O S)) O.language :=
  (corollary_7_2 O S).2.1 hw

end GenLimit.BreadthCharacterizations
