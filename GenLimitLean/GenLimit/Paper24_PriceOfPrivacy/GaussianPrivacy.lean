import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Approximate differential privacy of an independent Gaussian score vector.
The density comparison uses a third translated Gaussian density to bound the
positive excess above exp(ε) times the neighboring law. -/

namespace GenLimit.PriceOfPrivacy.Gaussian

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

abbrev vectorLaw (s : ι → ℝ) (v : ℝ≥0) := Measure.pi (fun i => gaussianReal (s i) v)

private def density (s : ι → ℝ) (v : ℝ≥0) (z : ι → ℝ) :=
  ∏ i, gaussianPDFReal (s i) v (z i)

private theorem density_nonneg (s : ι → ℝ) (v : ℝ≥0) (z : ι → ℝ) : 0 ≤ density s v z :=
  Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg ..)

private theorem density_integrable (s : ι → ℝ) (v : ℝ≥0) :
    Integrable (density s v) (Measure.pi (fun _ : ι => (volume : Measure ℝ))) :=
  Integrable.fintype_prod (fun i => integrable_gaussianPDFReal (s i) v)

private theorem event_integral (s : ι → ℝ) {v : ℝ≥0} (hv : v ≠ 0) (B : Set (ι → ℝ))
    (meas : MeasurableSet B) : (vectorLaw s v).real B =
      ∫ z in B, density s v z ∂Measure.pi (fun _ : ι => (volume : Measure ℝ)) := by
  let base := Measure.pi (fun _ : ι => (volume : Measure ℝ))
  have eq : vectorLaw s v = base.withDensity (fun z => ENNReal.ofReal (density s v z)) := by
    apply Measure.pi_eq
    intro box hm
    rw [withDensity_apply _ (MeasurableSet.univ_pi hm),
      ← ofReal_integral_eq_lintegral_ofReal (density_integrable s v).integrableOn
        (ae_of_all _ (density_nonneg s v))]
    dsimp only [base,density]
    rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => gaussianPDFReal_nonneg (s i) v x))]
    exact Finset.prod_congr rfl (fun i _ => (gaussianReal_apply_eq_integral (s i) hv (box i)).symm)
  rw [Measure.real_def,eq,withDensity_apply _ meas,
    ←ofReal_integral_eq_lintegral_ofReal (density_integrable s v).integrableOn
      (ae_of_all _ (density_nonneg s v)),ENNReal.toReal_ofReal (integral_nonneg (density_nonneg s v))]

/-- Squared distance between two vectors of scores. -/
def energy (s t : ι → ℝ) := ∑ i, (s i - t i)^2

private def exponent (s z : ι → ℝ) (v : ℝ≥0) := -energy z s / (2*v)

private theorem density_formula (s z : ι → ℝ) (v : ℝ≥0) :
    density s v z = (Real.sqrt (2*Real.pi*v))⁻¹ ^ Fintype.card ι * Real.exp (exponent s z v) := by
  unfold density exponent energy
  simp only [gaussianPDFReal,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    ← Real.exp_sum,← Finset.sum_div,Finset.sum_neg_distrib]

private theorem split_exp (a b ε scale : ℝ) (hscale : 0 < scale) :
    Real.exp a ≤ Real.exp ε * Real.exp b +
      Real.exp ((1+scale)*a - scale*b - scale*ε)/(1+scale) := by
  let x := a-b-ε
  have hu : 1-Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  have hv : 1-Real.exp (-x) ≤ 1 := by linarith [Real.exp_pos (-x)]
  have le : 1 ≤ Real.exp (-x) + Real.exp (scale*x)/(1+scale) := by
    have h := (le_div_iff₀ (by positivity : 0 < 1+scale)).mpr
      (show (1-Real.exp (-x))*(1+scale) ≤ Real.exp (scale*x) by
        nlinarith [mul_le_mul_of_nonneg_left hu hscale.le,Real.add_one_le_exp (scale*x)])
    linarith
  calc
    Real.exp a = Real.exp a * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left le (Real.exp_pos _).le
    _ = _ := by
      rw [mul_add,mul_div_assoc',←Real.exp_add,←Real.exp_add,←Real.exp_add]
      rw [show a + -x = ε+b by dsimp [x]; ring,
        show a+scale*x = (1+scale)*a-scale*b-scale*ε by dsimp [x]; ring]

private theorem tilt (s t z : ι → ℝ) (v : ℝ≥0) (scale : ℝ) :
    (1+scale)*exponent s z v - scale*exponent t z v =
      exponent (fun i => s i + scale*(s i-t i)) z v + scale*(1+scale)*energy s t/(2*v) := by
  unfold exponent energy
  rw [mul_div_assoc',mul_div_assoc',←sub_div,←add_div]
  congr 1
  simp only [←Finset.sum_neg_distrib,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem event_renyi (s t : ι → ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (B : Set (ι → ℝ)) (meas : MeasurableSet B) (ε scale : ℝ) (hscale : 0 < scale) :
    (vectorLaw s v).real B ≤ Real.exp ε * (vectorLaw t v).real B +
      Real.exp (scale*(1+scale)*energy s t/(2*v)-scale*ε)/(1+scale) := by
  let m := fun i => s i + scale*(s i-t i)
  let cost := Real.exp (scale*(1+scale)*energy s t/(2*v)-scale*ε)/(1+scale)
  have pos : 0 ≤ cost := by dsimp [cost]; positivity
  have le (z) : density s v z ≤ Real.exp ε * density t v z + cost * density m v z := by
    simp only [density_formula]
    let a := (Real.sqrt (2*Real.pi*v))⁻¹ ^ Fintype.card ι
    have fact := mul_le_mul_of_nonneg_left (split_exp (exponent s z v) (exponent t z v) ε scale hscale)
      (show 0 ≤ a by dsimp [a]; positivity)
    rw [tilt,show exponent m z v + scale*(1+scale)*energy s t/(2*v)-scale*ε =
      (scale*(1+scale)*energy s t/(2*v)-scale*ε)+exponent m z v by ring,Real.exp_add] at fact
    change a*Real.exp _ ≤ Real.exp ε*(a*Real.exp _) + cost*(a*Real.exp _)
    dsimp only [cost]
    apply fact.trans_eq
    ring
  have h := integral_mono ((density_integrable s v).integrableOn (s := B))
    ((((density_integrable t v).integrableOn (s := B)).const_mul (Real.exp ε)).add
      (((density_integrable m v).integrableOn (s := B)).const_mul cost)) le
  simp only [Pi.add_apply] at h
  rw [integral_add (((density_integrable t v).integrableOn (s := B)).const_mul _)
    (((density_integrable m v).integrableOn (s := B)).const_mul _),
    integral_const_mul,integral_const_mul,←event_integral s hv B meas,←event_integral t hv B meas,
    ←event_integral m hv B meas] at h
  exact h.trans (add_le_add_left (mul_le_of_le_one_right pos measureReal_le_one) _)

/-- Gaussian event privacy at the classical variance 2 D² log(1.25/δ)/ε²
or larger, where D² bounds the squared distance between the means. -/
theorem event_private (s t : ι → ℝ) {v : ℝ≥0} (hv : v ≠ 0) (ε δ : ℝ)
    (he : ε ∈ Ioo 0 1) (hd : δ ∈ Ioo 0 1)
    (cal : 2*Real.log ((5/4)/δ)*energy s t ≤ ε^2*v)
    {B : Set (ι → ℝ)} (meas : MeasurableSet B) :
    (vectorLaw s v).real B ≤ Real.exp ε * (vectorLaw t v).real B + δ := by
  let l := Real.log ((5/4)/δ)
  have hratio : (5/4 : ℝ) ≤ (5/4)/δ := (le_div_iff₀ hd.1).mpr (by linarith [hd.2])
  have hl : 1/5 ≤ l := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 5/4)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) hratio)
  let scale := 2*l/ε
  have hlam := (lt_div_iff₀ he.1).mpr (show 0*ε < 2*l by linarith)
  change 0 < scale at hlam
  have lv : (2/5 : ℝ) ≤ scale := (le_div_iff₀ he.1).mpr (by linarith [he.2])
  have vp : (0:ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have le : scale*(1+scale)*energy s t/(2*v)-scale*ε ≤ -l+ε/2 := by
    have c : 2*l*energy s t ≤ ε^2*v := cal
    have lp : 0 < l := by linarith
    have ratio : energy s t/(2*v) ≤ ε^2/(4*l) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith only [c])
    calc
      _ = scale*(1+scale)*(energy s t/(2*v))-scale*ε := by ring
      _ ≤ scale*(1+scale)*(ε^2/(4*l))-scale*ε :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left ratio (by positivity)) _
      _ = _ := by dsimp only [scale]; field_simp [he.1.ne',lp.ne']; ring
  have half : Real.exp (ε/2) ≤ 7/4 := by
    have h : Real.exp (1/2) ^ 2 = Real.exp 1 := by
      rw [sq,←Real.exp_add]; norm_num
    have h' := Real.exp_le_exp.mpr (show ε/2 ≤ 1/2 by linarith [he.2])
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1/2)]
  have reciprocal : Real.exp (-l) = δ/(5/4) := by
    rw [Real.exp_neg,show l = Real.log ((5/4)/δ) from rfl,
      Real.exp_log (div_pos (by norm_num : (0:ℝ) < 5/4) hd.1),inv_div]
  apply (event_renyi s t hv B meas ε scale hlam).trans
  apply add_le_add_left
  apply (div_le_iff₀ (by positivity : 0 < 1+scale)).mpr
  calc
    _ ≤ Real.exp (-l+ε/2) := Real.exp_le_exp.mpr le
    _ = δ/(5/4) * Real.exp (ε/2) := by rw [Real.exp_add,reciprocal]
    _ ≤ δ/(5/4)*(7/4) := mul_le_mul_of_nonneg_left half (div_nonneg hd.1.le (by norm_num))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left lv hd.1.le]

end
end GenLimit.PriceOfPrivacy.Gaussian
