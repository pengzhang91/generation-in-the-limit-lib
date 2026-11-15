import GenLimit.NoRegretLanguageGeneration.SauerBinomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace PredictionToGeneration
open Finset

theorem sauer_pos (n d : Nat) : 0 < sauer n d := by
  induction n generalizing d with
  | zero => simp [sauer]
  | succ n ih =>
    cases d with
    | zero => simp [sauer]
    | succ d => have := ih d; simp only [sauer]; omega

/-- Generating-function estimate for the truncated binomial sum. -/
theorem sauer_weighted_le (n d : Nat) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t^d*(sauer n d : ℝ) ≤ (t+1)^n := by
  rw [sauer_eq_truncated_choose]
  push_cast
  calc
    _ = ∑ i ∈ range (min d n+1), (n.choose i : ℝ)*t^d := by rw [mul_sum]; apply sum_congr rfl; intro i _; ring
    _ ≤ ∑ i ∈ range (min d n+1), (n.choose i : ℝ)*t^i := by
      apply sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact pow_le_pow_of_le_one ht ht1 (by simp only [mem_range] at hi; omega)
    _ ≤ ∑ i ∈ range (n+1), (n.choose i : ℝ)*t^i := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi; simp only [mem_range] at hi ⊢; omega
      · intro i _ _; positivity
    _ = (t+1)^n := by
      rw [add_pow]
      apply sum_congr rfl
      intro i _
      simp only [one_pow, mul_one]
      ring

/-- Uniform in both n and d; this avoids a separate large-d case. -/
theorem log_sauer_le (n d : Nat) (hd : 0 < d) :
    Real.log (sauer n d : ℝ) ≤ 2*(d : ℝ)*Real.log (1+(n : ℝ)/d) := by
  let t : ℝ := (d : ℝ)/((n : ℝ)+d)
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have hden : (0:ℝ)<(n : ℝ)+d := by linarith
  have ht : 0<t := div_pos hd0 hden
  have ht1 : t≤1 := (div_le_one hden).mpr (by linarith)
  have hs : (0:ℝ)<sauer n d := by exact_mod_cast sauer_pos n d
  have hweight := sauer_weighted_le n d t ht.le ht1
  have hlog := Real.log_le_log (mul_pos (pow_pos ht _) hs) hweight
  rw [Real.log_mul (pow_pos ht _).ne' hs.ne', Real.log_pow, Real.log_pow] at hlog
  have hlogt : Real.log (t+1) ≤ t := by
    have hh := Real.log_le_sub_one_of_pos (show 0<t+1 by linarith)
    linarith
  have hq : (0:ℝ)<1+(n : ℝ)/d := by positivity
  have htinverse : t = (1+(n : ℝ)/d)⁻¹ := by dsimp [t]; field_simp [ne_of_gt hd0, ne_of_gt hden]; ring
  have he : Real.log t = -Real.log (1+(n : ℝ)/d) := by rw [htinverse, Real.log_inv]
  have hlow := Real.one_sub_inv_le_log_of_pos hq
  have hnt : (n : ℝ)*t = (d : ℝ)*(1-(1+(n : ℝ)/d)⁻¹) := by
    dsimp [t]
    field_simp
    ring
  have hntle : (n : ℝ)*t ≤ (d : ℝ)*Real.log (1+(n : ℝ)/d) := by
    rw [hnt]
    exact mul_le_mul_of_nonneg_left hlow hd0.le
  have hup := mul_le_mul_of_nonneg_left hlogt hn0
  rw [he] at hlog
  nlinarith

theorem log_sauer_generation_le (T d : Nat) (hd : 0<d) :
    Real.log (sauer (2*T) d : ℝ) ≤ 4*(d : ℝ)*Real.log (1+(T : ℝ)/d) := by
  have hb := log_sauer_le (2*T) d hd
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have ht0 : (0:ℝ)≤T := Nat.cast_nonneg T
  have ha : 0≤(T : ℝ)/d := div_nonneg ht0 hd0.le
  have hl := Real.log_le_log (show (0:ℝ)<1+2*((T : ℝ)/d) by positivity)
    (show 1+2*((T : ℝ)/d) ≤ (1+(T : ℝ)/d)^2 by nlinarith [sq_nonneg ((T : ℝ)/d)])
  rw [Real.log_pow] at hl
  push_cast at hb hl
  have he : (2*(T : ℝ))/d = 2*((T : ℝ)/d) := by ring
  rw [he] at hb
  nlinarith [mul_le_mul_of_nonneg_left hl hd0.le]

end PredictionToGeneration

