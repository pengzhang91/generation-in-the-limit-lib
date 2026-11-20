import GenLimit.NoRegretLanguageGeneration.MarkedUnion
import GenLimit.NoRegretLanguageGeneration.SharpnessParameters
import GenLimit.NoRegretLanguageGeneration.PredictionRates
import GenLimit.NoRegretLanguageGeneration.MarkedForcing
import GenLimit.NoRegretLanguageGeneration.SharpnessProductForcing

namespace PredictionToGeneration.Sharpness
open Classical

abbrev Index (d : Nat) := {p : Nat × Nat // 1 ≤ p.1 ∧ p.1 ≤ d - 1 ∧ 1 ≤ p.2}
abbrev ComponentPoint {d : Nat} (i : Index d) := SharpnessProduct.Point i.1.1 (2 ^ i.1.2)
def ComponentClass {d : Nat} (i : Index d) := SharpnessProduct.H i.1.1 (2 ^ i.1.2)
abbrev Point (d : Nat) := MarkedUnion.Point (Index d) ComponentPoint
noncomputable def H (d : Nat) : HypothesisClass (Point d) := MarkedUnion.Union ComponentClass

theorem uus (d : Nat) : UUS (H d) :=
  MarkedUnion.union_uus ComponentClass (fun _ => SharpnessProduct.uus _ _)

theorem countable_class (d : Nat) : Countable {h // H d h} := by
  apply MarkedUnion.union_countable ComponentClass
  intro i
  change Countable {h // SharpnessProduct.H i.1.1 (2 ^ i.1.2) h}
  letI := SharpnessProduct.finite_class i.1.1 (2 ^ i.1.2)
  infer_instance

theorem component_dimension {d : Nat} (i : Index d) :
    LdimLE (ComponentClass i) i.1.1 ∧ Shatters (ComponentClass i) i.1.1 := by
  apply SharpnessProduct.exact_dimension
  have hp : (2 : Nat) ^ 1 ≤ 2 ^ i.1.2 := Nat.pow_le_pow_right (by omega) i.2.2.2
  norm_num at hp
  exact hp

theorem exact_dimension (d : Nat) (hd : 2 ≤ d) : LdimLE (H d) d ∧ Shatters (H d) d := by
  have he : d - 1 + 1 = d := by omega
  constructor
  · rw [← he]
    apply MarkedUnion.union_ldim_upper
    intro i hi
    apply (component_dimension i).1
    exact SharpnessProduct.shatters_le _ (by have := i.2.2.1; omega) hi
  · let i : Index d := ⟨(d - 1, 1), by omega⟩
    let j : Index d := ⟨(d - 1, 2), by omega⟩
    have hij : i ≠ j := by intro he; have := congrArg (fun k : Index d => k.1.2) he; simp [i,j] at this
    have hs := MarkedUnion.union_shatters_succ ComponentClass i j hij (d - 1)
      (component_dimension i).2 (component_dimension j).2
    simpa [he] using hs

theorem nonempty_class (d : Nat) (hd : 2 ≤ d) : ∃ h, H d h :=
  SharpnessProduct.shatters_le _ (Nat.zero_le d) (exact_dimension d hd).2

theorem upper (d T : Nat) (hd : 2 ≤ d) :
    (MF (H d) T : ℝ) ≤ 8 * d * Real.log (1 + (T : ℝ) / d) := by
  have hu := finite_ldim_realizable_rate (H d) (uus d) (nonempty_class d hd) d T (by omega) (exact_dimension d hd).1
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hl
  have hp : (0 : ℝ) < Real.log 2 := by linarith
  rw [Real.logb] at hu
  have he : 4 * (d : ℝ) * (Real.log (1 + (T : ℝ) / d) / Real.log 2) =
      (4 * d * Real.log (1 + (T : ℝ) / d)) / Real.log 2 := by ring
  rw [he] at hu
  have hb := (le_div_iff₀ hp).mp hu
  have hm : 0 ≤ (MF (H d) T : ℝ) := Nat.cast_nonneg _
  nlinarith

end PredictionToGeneration.Sharpness


namespace PredictionToGeneration.Sharpness

theorem parameter_lower (d q m T : Nat) (hd : 2 ≤ d) (hq : 1 ≤ q)
    (hqd : q ≤ d - 1) (hm : 1 ≤ m) (hT : 1 + 2 * q * (2 ^ m - 1) ≤ T) :
    q * m ≤ MF (H d) T := by
  let i : Index d := ⟨(q, m), hq, hqd, hm⟩
  have hcomponent : MFForces (ComponentClass i) (2 * q * (2 ^ m - 1)) (q * m) :=
    SharpnessProduct.product_forces q m hq hm
  have hne : ∃ h, ComponentClass i h :=
    SharpnessProduct.shatters_le _ (Nat.zero_le q) (component_dimension i).2
  have hf := MarkedUnion.union_forces ComponentClass i (SharpnessProduct.uus q (2 ^ m)) hne
    (2 * q * (2 ^ m - 1)) (q * m) hcomponent
  have hb := (mf_spec (H d) (uus d) (nonempty_class d hd) (2 * q * (2 ^ m - 1) + 1)).2 (q * m) hf
  exact hb.trans (nat_mono_of_succ (MF (H d)) (mf_mono_succ (H d) (uus d) (nonempty_class d hd)) _ T (by omega))

theorem lower (d T : Nat) (hd : 2 ≤ d) (hT : 3 ≤ T) :
    (d : ℝ) * Real.log (1 + (T : ℝ) / d) / 8 ≤ (MF (H d) T : ℝ) := by
  obtain ⟨q, m, hq, hqd, hm, hbudget, hlog⟩ := choose_parameters d T hd hT
  have hb : (q * m : Nat) ≤ MF (H d) T := parameter_lower d q m T hd hq hqd hm hbudget
  have hb' : (q * m : Nat) ≤ (MF (H d) T : ℝ) := by exact_mod_cast hb
  linarith

/-- A single countable UUS class for each dimension realizes the logarithmic
rate at every horizon, with explicit universal constants. -/
theorem sharpness (d : Nat) (hd : 2 ≤ d) :
    Countable {h // H d h} ∧ UUS (H d) ∧ LdimLE (H d) d ∧ Shatters (H d) d ∧
      ∀ T : Nat, 3 ≤ T →
        (d : ℝ) * Real.log (1 + (T : ℝ) / d) / 8 ≤ (MF (H d) T : ℝ) ∧
        (MF (H d) T : ℝ) ≤ 8 * d * Real.log (1 + (T : ℝ) / d) :=
  ⟨countable_class d, uus d, (exact_dimension d hd).1, (exact_dimension d hd).2,
    fun T hT => ⟨lower d T hd hT, upper d T hd⟩⟩

theorem sharpness_theta (d : Nat) (hd : 2 ≤ d) :
    (fun T : Nat => (MF (H d) T : ℝ)) =Θ[Filter.atTop]
      (fun T : Nat => (d : ℝ) * Real.log (1 + (T : ℝ) / d)) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 8
    apply Filter.Eventually.of_forall
    intro T
    have hu := upper d T hd
    have hn : 0 ≤ (d : ℝ) * Real.log (1 + (T : ℝ) / d) := by
      have hdiv : (0 : ℝ) ≤ (T : ℝ) / d := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    have hm : (0 : ℝ) ≤ (MF (H d) T : ℝ) := Nat.cast_nonneg _
    simp only [Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hm]
    nlinarith [hu]
  · apply Asymptotics.IsBigO.of_bound 8
    filter_upwards [Filter.eventually_ge_atTop (3 : Nat)] with T hT
    have hl := lower d T hd hT
    have hn : 0 ≤ (d : ℝ) * Real.log (1 + (T : ℝ) / d) := by
      have hdiv : (0 : ℝ) ≤ (T : ℝ) / d := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    simp only [Real.norm_eq_abs, abs_of_nonneg hn]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    linarith

end PredictionToGeneration.Sharpness


