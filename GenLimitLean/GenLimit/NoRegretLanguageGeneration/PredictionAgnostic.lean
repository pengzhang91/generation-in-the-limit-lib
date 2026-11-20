import GenLimit.NoRegretLanguageGeneration.PredictionAgnosticPotential
import GenLimit.NoRegretLanguageGeneration.LogEstimate
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace PredictionToGeneration
open scoped ENNReal

noncomputable def realFactor (lam : ℝ) : Bool → Bool → ℝ
  | false, true => 1+lam
  | true, false => 1-lam
  | _, _ => 1

noncomputable def realWeight (lam : ℝ) (h : Hypothesis X) : Trajectory X → ℝ
  | [] => 1
  | (z,x)::τ => realFactor lam (h z) (h x) * realWeight lam h τ

theorem realFactor_pos (lam : ℝ) (hlam : 0 ≤ lam) (hh : lam ≤ 1/2) (a b : Bool) :
    0 < realFactor lam a b := by cases a <;> cases b <;> dsimp [realFactor] <;> linarith

theorem realWeight_pos (lam : ℝ) (hlam : 0 ≤ lam) (hh : lam ≤ 1/2)
    (h : Hypothesis X) (τ : Trajectory X) : 0 < realWeight lam h τ := by
  induction τ with
  | nil => norm_num [realWeight]
  | cons p τ ih => exact mul_pos (realFactor_pos lam hlam hh _ _) ih

theorem realWeight_ofReal (lam : ℝ) (hlam : 0 ≤ lam) (hh : lam ≤ 1/2)
    (h : Hypothesis X) (τ : Trajectory X) :
    ENNReal.ofReal (realWeight lam h τ) = agnosticWeight (ENNReal.ofReal lam) h τ := by
  have he (a b : Bool) : ENNReal.ofReal (realFactor lam a b) = signedFactor (ENNReal.ofReal lam) a b := by
    cases a <;> cases b <;> simp [realFactor, signedFactor,
      ENNReal.ofReal_add zero_le_one hlam, ENNReal.ofReal_sub 1 hlam]
  induction τ with
  | nil => simp [realWeight, agnosticWeight]
  | cons p τ ih =>
    simp only [realWeight, agnosticWeight, ENNReal.ofReal_mul (realFactor_pos lam hlam hh _ _).le, he, ih]

theorem realFactor_eq_increment (lam : ℝ) (h : Hypothesis X) (z x : X) :
    realFactor lam (h z) (h x) = 1+lam*((loss h z : ℝ)-(loss h x : ℝ)) := by
  cases hz : h z <;> cases hx : h x <;> simp [realFactor, loss, hz, hx] <;> ring

theorem log_factor_lower (lam : ℝ) (hlam : 0 ≤ lam) (hh : lam ≤ 1/2)
    (h : Hypothesis X) (z x : X) :
    lam*((loss h z : ℝ)-(loss h x : ℝ))-lam^2 ≤ Real.log (realFactor lam (h z) (h x)) := by
  have hp := log_one_add_lower (u := lam) (by linarith)
  have hn := log_one_add_lower (u := -lam) (by linarith)
  simp only [neg_sq, ← sub_eq_add_neg] at hn
  cases hz : h z <;> cases hx : h x <;>
    simp [realFactor, loss, hz, hx] <;> nlinarith [sq_nonneg lam]

theorem log_weight_lower (lam : ℝ) (hlam : 0 ≤ lam) (hh : lam ≤ 1/2)
    (h : Hypothesis X) (τ : Trajectory X) :
    lam*(regret h τ : ℝ)-lam^2*(τ.length : ℝ) ≤ Real.log (realWeight lam h τ) := by
  induction τ with
  | nil => simp [regret, mistakes, demonstrationLoss, realWeight]
  | cons p τ ih =>
    rw [realWeight, Real.log_mul (realFactor_pos lam hlam hh _ _).ne' (realWeight_pos lam hlam hh h τ).ne']
    have ht := log_factor_lower lam hlam hh h p.1 p.2
    rw [regret_cons]
    push_cast
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The exact finite-horizon signed bound, using the paper's base-two logarithm. -/
theorem finite_ldim_agnostic_bound (H : HypothesisClass X) (hu : UUS H) (hne : ∃ h, H h)
    (d T : Nat) (hd : LdimLE H d) (η : ℝ) (hη : 0 < η) (hhalf : η ≤ 1/2) :
    (SMF H T : ℝ) ≤ Real.logb 2 (sauer (2*T) d : ℝ) / η + η*(T : ℝ) := by
  let lam := η * Real.log 2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlu : Real.log 2 ≤ 1 := by have ht := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num); linarith
  have hlam : 0 < lam := mul_pos hη hl
  have hlamhalf : lam ≤ 1/2 := by dsimp [lam]; nlinarith
  obtain ⟨G, hg⟩ := finite_ldim_agnostic_potential H hu hne d T hd (ENNReal.ofReal lam)
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨xs, h, hx, ht, hh, hm⟩ := smf_generator_lower_bound H hu hne T G
  have hw := hg xs hx ht h hh
  rw [← realWeight_ofReal lam hlam.le hlamhalf h (G.play xs)] at hw
  have hreal : realWeight lam h (G.play xs) ≤ (sauer (2*T) d : ℝ) := by exact_mod_cast hw
  have hpos := realWeight_pos lam hlam.le hlamhalf h (G.play xs)
  have hlog := Real.log_le_log hpos hreal
  have hlower := log_weight_lower lam hlam.le hlamhalf h (G.play xs)
  have hlen : (G.play xs).length = T := by
    have := congrArg List.length (G.demonstrations_play xs)
    simpa [demonstrations, ht] using this
  rw [hlen] at hlower
  have hmi : (SMF H T : ℝ) ≤ (regret h (G.play xs) : ℝ) := by exact_mod_cast hm
  have hbound : lam*(SMF H T : ℝ) ≤ Real.log (sauer (2*T) d : ℝ)+lam^2*(T : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hmi hlam.le]
  rw [Real.logb]
  calc
    (SMF H T : ℝ) ≤ (Real.log (sauer (2*T) d : ℝ)+lam^2*(T : ℝ))/lam :=
      (le_div_iff₀ hlam).mpr (by nlinarith [hbound])
    _ = Real.log (sauer (2*T) d : ℝ)/Real.log 2/η + lam*(T : ℝ) := by
      dsimp [lam]
      field_simp
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right
      (show lam ≤ η by dsimp [lam]; nlinarith) (Nat.cast_nonneg T)) _

end PredictionToGeneration


