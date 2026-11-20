import GenLimit.NoRegretLanguageGeneration.Support
import GenLimit.NoRegretLanguageGeneration.CapacityTrees
import GenLimit.NoRegretLanguageGeneration.PredictionNoRegret
import GenLimit.NoRegretLanguageGeneration.FiniteClass
import GenLimit.NoRegretLanguageGeneration.SharpnessUnion

namespace PredictionToGeneration

open scoped ENNReal

theorem capacity_one_eq_query_leaf_sup [Nonempty X] (H : HypothesisClass X) (n : Nat) :
    capacity H (fun _ => 1) n = ⨆ tree : QueryTree X n, (leafCount H tree : ℝ≥0∞) := by
  simp only [capacity_eq_iSup_weightedLeaves, weightedLeaves_one]

/-- Literal real-logarithm and natural-floor form of the main finite-Ldim bound. -/
theorem finite_ldim_realizable_floor (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (d T : Nat) (hd : LdimLE H d) :
    MF H T ≤ ⌊Real.logb 2 (∑ i ∈ Finset.range (min d (2*T)+1), ((2*T).choose i : ℝ))⌋₊ := by
  have he : (∑ i ∈ Finset.range (min d (2*T)+1), ((2*T).choose i : ℝ)) =
      ((∑ i ∈ Finset.range (min d (2*T)+1), (2*T).choose i : Nat) : ℝ) := by simp
  rw [he, show (2:ℝ)=(2:Nat) by norm_num, Real.natFloor_logb_natCast]
  exact finite_ldim_realizable_log H hu hne d T hd

theorem finite_class_uniform_floor (F : Finset (Hypothesis X))
    (hu : UUS (fun h => h ∈ F)) (hne : F.Nonempty) :
    ∃ G : Generator X, UniformMistakeBound G (fun h => h ∈ F)
      ⌊Real.logb 2 (F.card : ℝ)⌋₊ := by
  rw [show (2:ℝ)=(2:Nat) by norm_num, Real.natFloor_logb_natCast]
  exact finite_class_uniform_bound F hu hne

/-- Universal constants in the manuscript's base-two logarithm convention. -/
theorem sharpness_base_two (d : Nat) (hd : 2≤d) :
    Countable {h // Sharpness.H d h} ∧ UUS (Sharpness.H d) ∧
      LdimLE (Sharpness.H d) d ∧ Shatters (Sharpness.H d) d ∧
      ∀ T : Nat, 3≤T →
        (d : ℝ)*Real.logb 2 (1+(T : ℝ)/d)/16 ≤ (MF (Sharpness.H d) T : ℝ) ∧
        (MF (Sharpness.H d) T : ℝ) ≤ 8*(d : ℝ)*Real.logb 2 (1+(T : ℝ)/d) := by
  obtain ⟨hc,hu,hld,hs,hbounds⟩ := Sharpness.sharpness d hd
  refine ⟨hc,hu,hld,hs,fun T hT => ?_⟩
  have hlo := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
  norm_num at hlo
  have hhi := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  norm_num at hhi
  have hlp : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0≤(d : ℝ)*Real.log (1+(T : ℝ)/d) :=
    mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg
      (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg T) (Nat.cast_nonneg d))))
  obtain ⟨hl,hr⟩ := hbounds T hT
  rw [Real.logb, ← mul_div_assoc]
  constructor
  · apply le_trans _ hl
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<16)).mpr
    apply (div_le_iff₀ hlp).mpr
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hlo)]
  · apply hr.trans
    rw [mul_assoc (8:ℝ), ← mul_div_assoc]
    apply (le_div_iff₀ hlp).mpr
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hhi)]

end PredictionToGeneration
