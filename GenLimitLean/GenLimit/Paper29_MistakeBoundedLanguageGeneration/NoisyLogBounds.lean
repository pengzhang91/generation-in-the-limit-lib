import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Logarithmic constants for noisy multiplicative updates

Concavity bounds log(1 + g) on [0,3/4] and log(1 − g²) on the
corresponding interval of squared rates. Both bounds use endpoint chords.
-/
namespace GenLimit.MistakeBounded

theorem noisy_log_chord {z w : ℝ} (hz : 0 < z) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    w * Real.log z ≤ Real.log ((1-w)+w*z) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (show (1:ℝ) ∈ Set.Ioi 0 from (zero_lt_one : (0:ℝ) < 1))
    (show z ∈ Set.Ioi 0 from hz) (sub_nonneg.mpr hw1) hw (show 1-w+w = 1 by ring)
  simpa only [smul_eq_mul,Real.log_one,mul_zero,zero_add,mul_one] using h

theorem noisy_log_gain {g : ℝ} (hg : 0 ≤ g) (h3 : g ≤ 3/4) :
    g * Real.log 2 ≤ Real.log (1+g) := by
  have h := noisy_log_chord (z := 2) (by norm_num) hg (by linarith)
  convert h using 2
  ring

theorem noisy_log_loss {g : ℝ} (hg : 0 ≤ g) (h3 : g ≤ 3/4) :
    -Real.log (1-g) ≤ (1+2*g)*Real.log (1+g) := by
  have h1 := noisy_log_chord (z := 7/4) (w := 4*g/3) (by norm_num) (by positivity) (by linarith)
  have h2 := noisy_log_chord (z := 7/16) (w := 16*g^2/9) (by norm_num) (by positivity)
    (by nlinarith [mul_nonneg (show 0 ≤ 3/4-g by linarith) (show 0 ≤ 3/4+g by linarith)])
  rw [show 1-4*g/3 + (4*g/3)*(7/4) = 1+g by ring] at h1
  rw [show 1-16*g^2/9+(16*g^2/9)*(7/16)=(1-g)*(1+g) by ring,
    Real.log_mul (by linarith) (by linarith)] at h2
  have edge := Real.log_nonneg (show (1:ℝ) ≤ (7/16)^2*(7/4)^3 by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num),Real.log_pow,Real.log_pow] at edge
  norm_num only [Nat.cast_ofNat] at edge
  nlinarith [mul_nonneg (sq_nonneg g) edge, mul_le_mul_of_nonneg_left h1 hg]

end GenLimit.MistakeBounded
