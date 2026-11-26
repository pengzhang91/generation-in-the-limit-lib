import GenLimit.Paper24_PriceOfPrivacy.Testing
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The multiplicative lower tail for the occurrence count of a word in an
ordered IID sample. The probability exponent is linear in the word's mass. -/

namespace GenLimit.PriceOfPrivacy

open DiscreteIID Set
open scoped Classical ENNReal
noncomputable section

private def halfWeight (a : X) (x : X) : ℝ≥0∞ := if x = a then ENNReal.ofReal (1/2) else 1

private theorem half_moment (p : PMF X) (a : X) :
    moment p (halfWeight a) = ENNReal.ofReal (1-(p a).toReal/2) := by
  have eq : moment p (halfWeight a) = p a * ENNReal.ofReal (1/2) + p.toOuterMeasure {a}ᶜ := by
    rw [moment,PMF.toOuterMeasure_apply,←tsum_ite_eq a (p a * ENNReal.ofReal (1/2)),←ENNReal.tsum_add]
    apply tsum_congr
    intro x
    by_cases hx : x = a <;> simp [hx,halfWeight]
  have finite : p a * ENNReal.ofReal (1/2) + p.toOuterMeasure {a}ᶜ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (p.apply_ne_top a) ENNReal.ofReal_ne_top,
    event_ne_top p {a}ᶜ⟩
  apply (ENNReal.toReal_eq_toReal_iff' (eq ▸ finite) ENNReal.ofReal_ne_top).mp
  have qle : (p a).toReal ≤ 1 := by simpa [probability,PMF.toOuterMeasure_apply_singleton] using probability_le_one p {a}
  rw [eq,ENNReal.toReal_add (ENNReal.mul_ne_top (p.apply_ne_top a) ENNReal.ofReal_ne_top)
    (event_ne_top p {a}ᶜ),ENNReal.toReal_mul,ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/2),
    ←probability,probability_compl,ENNReal.toReal_ofReal (by linarith)]
  simp [probability,PMF.toOuterMeasure_apply_singleton]
  ring

private theorem half_product (a : X) (xs : List X) :
    productWeight (halfWeight a) xs = ENNReal.ofReal (Real.exp (-(xs.count a:ℝ)*Real.log 2)) := by
  induction xs with
  | nil => simp [productWeight]
  | cons x xs ih =>
    change halfWeight a x * productWeight (halfWeight a) xs = _
    rw [ih]
    by_cases hx : x = a
    · subst x
      rw [List.count_cons_self,Nat.cast_add,Nat.cast_one,
        show -((xs.count a:ℝ)+1)*Real.log 2 = -(Real.log 2)+(-(xs.count a:ℝ)*Real.log 2) by ring,
        Real.exp_add,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ) < 2),ENNReal.ofReal_mul (by positivity)]
      simp [halfWeight,one_div]
    · simp [halfWeight,hx]

/-- The atom mass may be replaced by any smaller nonnegative mass floor. -/
theorem count_lower_tail (p : PMF X) (a : X) (n : ℕ) (m : ℝ)
    (hm : 0 ≤ m) (mass : m ≤ (p a).toReal) :
    probability (samples p n) {xs | (xs.count a : ℝ) < n*m/2} ≤ Real.exp (-(n:ℝ)*m/8) := by
  let B := {xs : List X | (xs.count a : ℝ) < n*m/2}
  let c := Real.exp (-(n:ℝ)*m/2*Real.log 2)
  let q := samples p n
  have hc : 0 < c := Real.exp_pos _
  have small : ENNReal.ofReal c * q.toOuterMeasure B ≤ moment q (productWeight (halfWeight a)) := by
    rw [PMF.toOuterMeasure_apply,← ENNReal.tsum_mul_left,moment]
    apply ENNReal.tsum_le_tsum
    intro xs
    by_cases hx : xs ∈ B
    · simp only [indicator_of_mem hx,mul_comm (ENNReal.ofReal c)]
      apply mul_le_mul_left'
      rw [half_product]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by dsimp [B] at hx; linarith only [hx]) (Real.log_nonneg (by norm_num))
    · simp [hx]
  change _ ≤ moment (samples p n) _ at small
  rw [product_moment,half_moment] at small
  have qle : (p a).toReal ≤ 1 := by simpa [probability,PMF.toOuterMeasure_apply_singleton] using probability_le_one p {a}
  have scaled := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) small
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc.le,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by linarith)] at scaled
  change c * probability q B ≤ _ at scaled
  have base : 1-(p a).toReal/2 ≤ Real.exp (-m/2) := by linarith [Real.add_one_le_exp (-m/2)]
  have power := pow_le_pow_left₀ (show 0 ≤ 1-(p a).toReal/2 by linarith) base n
  have hl : Real.log 2 ≤ 3/4 := by linarith [Real.log_two_lt_d9]
  have bound : Real.exp (-m/2)^n ≤ c * Real.exp (-(n:ℝ)*m/8) := by
    rw [←Real.exp_nat_mul,←Real.exp_add,Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left hl (show 0 ≤ (n:ℝ)*m by positivity)]
  exact le_of_mul_le_mul_left (scaled.trans (power.trans bound)) hc

end
end GenLimit.PriceOfPrivacy
