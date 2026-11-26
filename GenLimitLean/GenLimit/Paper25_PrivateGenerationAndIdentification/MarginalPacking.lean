import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-! A packing inequality with marginal correctness. It only uses success
probability two thirds for each individual coordinate of a hidden bit
vector, as supplied by a shared prefix consistent with multiple targets
in the lower bound of Theorem 1.3. -/
namespace GenLimit.PrivateLimit.Packing

open Real Set
open scoped Classical
noncomputable section

abbrev Cube (h : ℕ) := Fin h → Bool

def matchCount {h : ℕ} (z w : Cube h) : ℝ := ∑ i, if z i = w i then 1 else 0

def weight {h : ℕ} (z w : Cube h) := Real.exp (Real.log 2 * matchCount z w)

def coefficient := (5/3:ℝ)*Real.log 2 - Real.log 3

theorem coefficient_pos : 0 < coefficient := by
  have h := Real.log_lt_log (by norm_num : (0:ℝ)<3^3) (by norm_num : (3:ℝ)^3<2^5)
  rw [Real.log_pow,Real.log_pow] at h
  unfold coefficient; norm_num at h; linarith

private theorem column {h : ℕ} (w : Cube h) : ∑ z, weight z w = 3^h := by
  let f (i : Fin h) (b : Bool) := if b=w i then (2:ℝ) else 1
  have prod (z : Cube h) : weight z w = ∏ i, f i (z i) := by
    unfold weight matchCount; rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _; by_cases he : z i = w i <;> simp [f,he,Real.exp_log (by norm_num : (0:ℝ)<2)]
  simp_rw [prod]
  rw [← Fintype.prod_sum f]
  have sm (i : Fin h) : ∑ b, f i b = 3 := by
    cases h' : w i <;> norm_num [f,Fintype.sum_bool,h']
  simp_rw [sm]; simp

/-- If every row is dominated by exp(E) times one reference law, and
every bit is correct with probability at least two thirds under its own
row, the privacy loss E is at least a positive constant times h. -/
theorem marginal_packing {h : ℕ} (p : Cube h → Cube h → ℝ) (q : Cube h → ℝ) (E : ℝ)
    (pos : ∀ z w, 0 ≤ p z w) (unit : ∀ z, ∑ w, p z w = 1) (reference : ∑ w, q w = 1)
    (correct : ∀ z i, 2/3 ≤ ∑ w, if z i = w i then p z w else 0)
    (dom : ∀ z w, p z w ≤ Real.exp E*q w) : coefficient*h ≤ E := by
  have mean (z : Cube h) : (h:ℝ)*(2/3) ≤ ∑ w, p z w*matchCount z w := by
    simp only [matchCount,Finset.mul_sum]
    rw [Finset.sum_comm]
    have le := Finset.sum_le_sum (s := Finset.univ) (fun i _ => correct z i)
    simpa [mul_ite] using le
  have row (z : Cube h) : Real.exp (Real.log 2*(h*(2/3:ℝ))) ≤ ∑ w, p z w*weight z w := by
    have j := convexOn_exp.map_sum_le (fun w _ => pos z w) (unit z)
      (fun w _ => Set.mem_univ (Real.log 2*matchCount z w))
    apply le_trans _ (show Real.exp (∑ w, p z w*(Real.log 2*matchCount z w)) ≤ _ from j)
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ Real.log 2 * ∑ w, p z w*matchCount z w := by gcongr; exact mean z
      _ = _ := by rw [Finset.mul_sum]; congr 1; ext; ring
  have cap (w : Cube h) : ∑ z, p z w*weight z w ≤ Real.exp E*q w*3^h := by
    rw [←column w,Finset.mul_sum]
    exact Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_right (dom z w) (Real.exp_pos _).le)
  have lower := Finset.sum_le_sum (s := Finset.univ) (fun z _ => row z)
  have upper := Finset.sum_le_sum (s := Finset.univ) (fun w _ => cap w)
  rw [Finset.sum_comm] at lower
  have hle := lower.trans upper
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,←Finset.sum_mul,←Finset.mul_sum,reference,mul_one] at hle
  rw [show (2:ℝ)^h = Real.exp (h*Real.log 2) by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)],←Real.exp_add,show (3:ℝ)^h = Real.exp (h*Real.log 3) by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<3)],←Real.exp_add,Real.exp_le_exp] at hle
  unfold coefficient; linarith

end
end GenLimit.PrivateLimit.Packing
