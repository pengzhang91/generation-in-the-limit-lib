import GenLimit.NoRegretLanguageGeneration.AsymptoticBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PredictionToGeneration.Sharpness
open Classical

theorem forcing_parameter_bound {q T j : Nat} (hq : 1 ≤ q)
    (h : 2 * q * (2 ^ j - 1) ≤ T - 1) : j ≤ T + 1 := by
  have hp : j < 2 ^ j := Nat.lt_two_pow_self
  have hm : 2 ^ j - 1 ≤ 2 * q * (2 ^ j - 1) := by nlinarith
  omega

/-- Integer dyadic choices avoid any floor-of-real-log convention. Natural
logarithms are used; the universal factor eight is independent of d and T. -/
theorem choose_parameters (d T : Nat) (hd : 2 ≤ d) (hT : 3 ≤ T) :
    ∃ q m : Nat, 1 ≤ q ∧ q ≤ d - 1 ∧ 1 ≤ m ∧
      1 + 2 * q * (2 ^ m - 1) ≤ T ∧
      (d : ℝ) * Real.log (1 + (T : ℝ) / d) ≤ 8 * (q * m : Nat) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  by_cases hsmall : T ≤ 2 * d - 1
  · let q := (T - 1) / 2
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hqd : q ≤ d - 1 := by dsimp [q]; omega
    have hcost : 1 + 2 * q * (2 ^ 1 - 1) ≤ T := by dsimp [q]; norm_num; omega
    refine ⟨q, 1, hq, hqd, by omega, hcost, ?_⟩
    have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (T : ℝ) / d by positivity)
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hdpos)
    have htq : (T : ℝ) ≤ 4 * q := by exact_mod_cast (show T ≤ 4 * q by dsimp [q]; omega)
    have he : (d : ℝ) * (1 + (T : ℝ) / d - 1) = T := by
      field_simp
      ring
    rw [he] at hmul
    norm_num
    nlinarith
  · let q := d - 1
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hlarge : 2 * d ≤ T := by omega
    let P : Nat → Prop := fun j => 2 * q * (2 ^ j - 1) ≤ T - 1
    let m := thresholdMax P (T + 1)
    have hs := thresholdMax_spec P (by dsimp [P]; simp) (T + 1)
    have hm : P m := hs.1
    have hmpos : 1 ≤ m := hs.2 1 (by omega) (by dsimp [P, q]; norm_num; omega)
    have hn : ¬ P (m + 1) := by
      intro hh
      have hb := forcing_parameter_bound hq hh
      have hh' := hs.2 (m + 1) hb hh
      change m + 1 ≤ m at hh'
      omega
    have hcost : 1 + 2 * q * (2 ^ m - 1) ≤ T := by change 2 * q * (2 ^ m - 1) ≤ T - 1 at hm; omega
    refine ⟨q, m, hq, by dsimp [q]; omega, hmpos, hcost, ?_⟩
    have hnext : T ≤ 2 * q * (2 ^ (m + 1) - 1) := by dsimp [P] at hn; omega
    have hpowpos : (0 : ℝ) < 2 ^ (m + 1) := by positivity
    have hnext' : (T : ℝ) ≤ 2 * q * ((2 : ℝ) ^ (m + 1) - 1) := by
      have hp : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      exact_mod_cast hnext
    have hqd : (q : ℝ) ≤ d := by exact_mod_cast (show q ≤ d by dsimp [q]; omega)
    have hqnonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hratio : 1 + (T : ℝ) / d ≤ (2 : ℝ) ^ (m + 3) := by
      have hpge : (1 : ℝ) ≤ 2 ^ (m + 1) := by exact_mod_cast (Nat.one_le_two_pow (n := m + 1))
      have hprod := mul_le_mul_of_nonneg_right hqd (show (0 : ℝ) ≤ 2 ^ (m + 1) - 1 by linarith)
      have hdiv : (T : ℝ) / d ≤ 2 * (2 ^ (m + 1) - 1) := (div_le_iff₀ hdpos).mpr (by nlinarith)
      rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      norm_num
      nlinarith
    have hlog := Real.log_le_log (show (0 : ℝ) < 1 + (T : ℝ) / d by positivity) hratio
    rw [Real.log_pow] at hlog
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at this ⊢
      exact this
    have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
    have hlogbound : Real.log (1 + (T : ℝ) / d) ≤ 4 * m := by
      push_cast at hlog
      nlinarith
    have hdq : (d : ℝ) ≤ 2 * q := by exact_mod_cast (show d ≤ 2 * q by dsimp [q]; omega)
    have hmul := mul_le_mul_of_nonneg_left hlogbound (le_of_lt hdpos)
    push_cast
    nlinarith

end PredictionToGeneration.Sharpness


