import GenLimit.NoRegretLanguageGeneration.PredictionRealizable
import GenLimit.NoRegretLanguageGeneration.PredictionAgnostic
import GenLimit.NoRegretLanguageGeneration.BinomialEstimate
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace PredictionToGeneration

theorem finite_ldim_realizable_rate (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h)
    (d T : Nat) (hd : 0<d) (hld : LdimLE H d) :
    (MF H T : ℝ) ≤ 4*(d : ℝ)*Real.logb 2 (1+(T : ℝ)/d) := by
  have hp : (2 : ℝ)^MF H T ≤ (sauer (2*T) d : ℝ) := by
    exact_mod_cast finite_ldim_exponential H hu hne d T hld
  have hl := Real.log_le_log (pow_pos (show (0:ℝ)<2 by norm_num) _) hp
  rw [Real.log_pow] at hl
  have hb := log_sauer_generation_le T d hd
  have hlog : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb]
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hlog).mpr (hl.trans hb)

/-- Optimizing the learning rate with the trivial horizon bound handles both
the small- and large-complexity regimes, including zero complexity. -/
theorem optimize_regret (v A T : ℝ) (hA : 0≤A) (hT : 0≤T) (hvT : v≤T)
    (hb : ∀ η : ℝ, 0<η → η≤1/2 → v≤A/η+η*T) : v≤2*Real.sqrt (A*T) := by
  by_cases hv : v≤0
  · exact hv.trans (by positivity)
  have hvp : 0<v := lt_of_not_ge hv
  have hTp : 0<T := hvp.trans_le hvT
  let r := Real.sqrt (A*T)
  have hr : 0≤r := Real.sqrt_nonneg _
  have hrsq : r^2=A*T := Real.sq_sqrt (mul_nonneg hA hT)
  by_cases hz : r=0
  · have hAz : A=0 := by rw [hz] at hrsq; nlinarith
    have he : 0<v/(2*T) := div_pos hvp (by linarith)
    have heh : v/(2*T)≤1/2 := (div_le_iff₀ (by linarith : (0:ℝ)<2*T)).mpr (by linarith)
    have ht := hb (v/(2*T)) he heh
    rw [hAz, zero_div] at ht
    have hid : v/(2*T)*T=v/2 := by field_simp; ring
    rw [hid] at ht
    linarith
  have hrp : 0<r := lt_of_le_of_ne hr (Ne.symm hz)
  by_cases hsmall : r/T≤1/2
  · have ht := hb (r/T) (div_pos hrp hTp) hsmall
    have he : A/(r/T)+(r/T)*T=2*r := by
      field_simp
      nlinarith [hrsq]
    rw [he] at ht
    exact ht
  · have ht : T≤2*r := by
      have := (lt_div_iff₀ hTp).mp (lt_of_not_ge hsmall)
      linarith
    exact hvT.trans ht

theorem finite_ldim_agnostic_rate (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h)
    (d T : Nat) (hd : 0<d) (hld : LdimLE H d) :
    (SMF H T : ℝ) ≤ 4*Real.sqrt ((d : ℝ)*(T : ℝ)*Real.logb 2 (1+(T : ℝ)/d)) := by
  let L := Real.logb 2 (1+(T : ℝ)/d)
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hlog : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0≤L := div_nonneg (Real.log_nonneg (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg T) hd0.le))) hlog.le
  have hA : Real.logb 2 (sauer (2*T) d : ℝ) ≤ 4*(d : ℝ)*L := by
    dsimp [L]
    rw [Real.logb, Real.logb]
    apply (div_le_iff₀ hlog).mpr
    convert log_sauer_generation_le T d hd using 1 <;> field_simp <;> ring
  have hbound := optimize_regret (SMF H T : ℝ) (4*(d : ℝ)*L) (T : ℝ)
    (by positivity) (Nat.cast_nonneg T) (by exact_mod_cast smf_le_horizon H T)
    (fun η hp hhalf => (finite_ldim_agnostic_bound H hu hne d T hld η hp hhalf).trans
      (add_le_add_right (div_le_div_of_nonneg_right hA hp.le) _))
  have he : (4*(d : ℝ)*L)*(T : ℝ)=4*((d : ℝ)*(T : ℝ)*L) := by ring
  rw [he, Real.sqrt_mul (by norm_num : (0:ℝ)≤4)] at hbound
  norm_num at hbound
  nlinarith [hbound]

end PredictionToGeneration

