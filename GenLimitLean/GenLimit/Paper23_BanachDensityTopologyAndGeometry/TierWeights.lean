import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-! Quantitative local-lemma weights in Theorem 5.9. The parameter
p is 2d/α. Positive sizes start at one, and the dense tier has index zero. -/
namespace GenLimit.KleinbergWei.Banach.TierWeights
open Real Finset
open scoped Classical
noncomputable section

def capacityFactor (p : ℝ) (k j : ℕ) := exp (p*(log k + j*log 2))
def weight (p : ℝ) (k j : ℕ) :=
  (1/2 : ℝ)*exp (-((p+2)*log k + (p+1)*(j*log 2)))

/-- The threshold printed in 5.9, with the two square-root terms kept separate. -/
def threshold (ε p : ℝ) (k j : ℕ) : ℝ :=
  ε*k + sqrt (2*(p+1)*log 2) * sqrt ((k:ℝ)*j) +
    sqrt (2*(p+2)*log k + 4*log 2) * sqrt k

private theorem log_size {k : ℕ} (hk : 0 < k) : 0 ≤ log k :=
  log_nonneg (by exact_mod_cast hk)

theorem weight_bounds {p : ℝ} (hp : 0 ≤ p) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    0 ≤ weight p k j ∧ weight p k j ≤ 1/2 := by
  have scale : 0 ≤ (p+2)*log k + (p+1)*((j:ℝ)*log 2) := by
    have := log_size hk; positivity
  unfold weight
  exact ⟨by positivity,by nlinarith [exp_le_one_iff.mpr (neg_nonpos.mpr scale)]⟩

theorem cancel_capacity (p : ℝ) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    capacityFactor p k j * weight p k j =
      (1/2 : ℝ)*(1/(k:ℝ)^2)*(1/2:ℝ)^j := by
  have pos : (0:ℝ) < k := by exact_mod_cast hk
  have logtwo : exp (log 2) = 2 := exp_log (by norm_num)
  unfold capacityFactor weight
  rw [show -((p+2)*log k + (p+1)*(j*log 2)) =
    -(p*(log k+j*log 2)) - (2*log k+j*log 2) by ring,exp_sub,exp_neg]
  rw [exp_add,show exp (2*log k) = (k:ℝ)^2 by rw [two_mul,Real.exp_add,exp_log pos,pow_two],
      Real.exp_nat_mul,logtwo,one_div_pow]
  field_simp

theorem threshold_nonneg {ε : ℝ} (he : 0 ≤ ε) (p : ℝ) (k j : ℕ) :
    0 ≤ threshold ε p k j := by unfold threshold; positivity

theorem tail_fits {ε p : ℝ} (he : 0 ≤ ε) (hp : 0 ≤ p) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    2*exp (-(threshold ε p k j)^2/(2*k)) ≤ weight p k j * exp (-ε^2*k/2) := by
  have kp : (0:ℝ) < k := by exact_mod_cast hk
  have logk := log_size hk
  have logtwo : 0 ≤ log 2 := log_nonneg (by norm_num)
  let a := ε*k
  let b := sqrt (2*(p+1)*log 2) * sqrt ((k:ℝ)*j)
  let c := sqrt (2*(p+2)*log k+4*log 2)*sqrt k
  have az : 0 ≤ a := by dsimp [a]; positivity
  have bz : 0 ≤ b := by dsimp [b]; positivity
  have cz : 0 ≤ c := by dsimp [c]; positivity
  have bs : b^2 = 2*(p+1)*log 2*(k*j) := by
    rw [show b= _ from rfl,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
  have cs : c^2 = (2*(p+2)*log k+4*log 2)*k := by
    dsimp [c]; rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt kp.le]
  have sq : a^2 + b^2 + c^2 ≤ (a+b+c)^2 := by
    nlinarith only [mul_nonneg az bz,mul_nonneg az cz,mul_nonneg bz cz]
  rw [bs,cs] at sq
  change _ ≤ (threshold ε p k j)^2 at sq
  have exp_bound : log 2 - (threshold ε p k j)^2/(2*k) ≤
      -log 2 - ((p+2)*log k + (p+1)*(j*log 2)) - ε^2*k/2 := by
    apply (sub_le_iff_le_add').mpr
    rw [div_add' _ _ _ (by positivity : 2*(k:ℝ) ≠ 0),le_div_iff₀ (by positivity : 0 < 2*(k:ℝ))]
    dsimp only [a] at sq
    nlinarith only [sq]
  have ev := exp_le_exp.mpr exp_bound
  rw [exp_sub,exp_sub,exp_sub,exp_neg,exp_log (by norm_num : (0:ℝ)<2)] at ev
  unfold weight
  rw [show -(threshold ε p k j)^2 / (2*k) = -((threshold ε p k j)^2 / (2*k)) by ring,
    exp_neg,exp_neg,show -ε^2*k/2 = -(ε^2*k/2) by ring,exp_neg]
  simpa [div_eq_mul_inv,mul_assoc] using ev

end
end GenLimit.KleinbergWei.Banach.TierWeights
