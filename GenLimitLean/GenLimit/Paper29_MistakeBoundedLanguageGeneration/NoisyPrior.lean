import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Summable priors attaining the literal constants of Lemma 7.2

Both tail estimates keep the first three terms and integrate from four.
The numerical certificates are rational inequalities after taking powers.
-/
namespace GenLimit.MistakeBounded
open scoped BigOperators

private theorem negpow_le (x y : ℝ) (k d : ℕ) (hx : 0 < x) (hy : 0 ≤ y) (hd : d ≠ 0)
    (cert : 1 ≤ x^k*y^d) : x ^ (-(k:ℝ)/d) ≤ y := by
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hx.le _) hy hd).mp
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hd), Real.rpow_neg hx.le,Real.rpow_natCast]
  exact (inv_le_iff_one_le_mul₀ (pow_pos hx k)).mpr (by simpa [mul_comm] using cert)

private theorem tail_integral (p : ℝ) (hp : 1 < p) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i:ℝ)+2)^(-p) ≤
      (2:ℝ)^(-p)+3^(-p)+4^(-p)+4^(1-p)/(p-1) := by
  have hanti : AntitoneOn (fun x : ℝ => x^(-p)) (Set.Icc 4 (4+(n:ℝ))) :=
    fun _ hx _ _ h => Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) h (by linarith)
  have h := hanti.sum_le_integral (a := n)
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) n] : (4:ℝ) ≤ 4+n)]
    simp⟩)] at h
  have ub : ∑ i ∈ Finset.range n, ((i:ℝ)+5)^(-p) ≤ (4:ℝ)^(1-p)/(p-1) := by
    have eq (i : ℕ) : (4:ℝ)+(i+1:ℕ) = (i:ℝ)+5 := by push_cast; ring
    simp only [eq,show -p+1 = 1-p by ring] at h
    apply h.trans
    have hpos := Real.rpow_nonneg (by positivity : 0 ≤ (4:ℝ)+n) (1-p)
    conv_lhs => rw [show 1-p = -(p-1) by ring,div_neg,← neg_div]
    exact div_le_div_of_nonneg_right (by simp only [neg_sub]; linarith) (by linarith)
  calc
    _ ≤ ∑ i ∈ Finset.range (3+n), ((i:ℝ)+2)^(-p) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun i _ _ => by positivity)
    _ = (2:ℝ)^(-p)+3^(-p)+4^(-p)+∑ i ∈ Finset.range n, ((i:ℝ)+5)^(-p) := by
      rw [Finset.sum_range_add]
      norm_num [Finset.sum_range_succ,Nat.cast_add,add_assoc,add_comm,add_left_comm]
    _ ≤ _ := by linarith

theorem noisy_prior_tail_small (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i:ℝ)+2)^(-(9/4:ℝ)) ≤ 1/2 := by
  have a := tail_integral (9/4) (by norm_num) n
  have h2 := negpow_le 2 (211/1000) 9 4 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have h3 := negpow_le 3 (85/1000) 9 4 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have h4 := negpow_le 4 (45/1000) 9 4 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have h5 := negpow_le 4 (177/1000) 5 4 (by norm_num) (by norm_num) (by decide) (by norm_num)
  norm_num1 at a h2 h3 h4 h5 ⊢
  linarith

theorem noisy_prior_tail_large (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i:ℝ)+2)^(-(9/5:ℝ)) ≤ 97/100 := by
  have a := tail_integral (9/5) (by norm_num) n
  have h2 := negpow_le 2 (29/100) 9 5 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have h3 := negpow_le 3 (14/100) 9 5 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have h4 := negpow_le 4 (9/100) 9 5 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have h5 := negpow_le 4 (34/100) 4 5 (by norm_num) (by norm_num) (by decide) (by norm_num)
  norm_num1 at a h2 h3 h4 h5 ⊢
  linarith

end GenLimit.MistakeBounded
