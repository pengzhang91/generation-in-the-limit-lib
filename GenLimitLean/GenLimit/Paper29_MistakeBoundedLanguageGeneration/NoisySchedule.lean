import GenLimit.Paper29_MistakeBoundedLanguageGeneration.NoisyFinite
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.NoisyPrior

/-! # Rates, prior weights and activation rounds for the exact noisy bound

Index z in Lean denotes language z+1. A target is activated in the first
round whose one-based index is at least floor(log₂(z+1)), including all
rounds for the first target.
-/
namespace GenLimit.MistakeBounded
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def noisyStart (i : ℕ) : ℕ := (Nat.log2 (i+1)).pred
def noisyActive (t : ℕ) := Finset.range (2^(t+2)-1)

theorem noisyActive_iff {t i : ℕ} : i ∈ noisyActive t ↔ noisyStart i ≤ t := by
  have h := Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : i+1 ≠ 0) (x := t+2)
  simp only [noisyActive,Finset.mem_range,noisyStart,Nat.log2_eq_log_two,Nat.pred_eq_sub_one]
  omega

def noisyExponent (g : ℝ) : ℝ := if g ≤ 1/2 then 9/4 else 9/5
def noisyRate (g : ℝ) : ℝ := if g ≤ 1/2 then g else 3/5
def noisyPrior (g : ℝ) : ℕ → ℝ
  | 0 => if g ≤ 1/2 then 3/4 else 51/100
  | i+1 => 1/2 * ((i:ℝ)+2)^(-noisyExponent g)

def noisyCountableRule (g : ℝ) (L : ℕ → Set α) : NoisyRule ℕ α :=
  ⟨L,noisyActive,noisyPrior g,noisyRate g⟩

theorem noisyPrior_pos (g : ℝ) (i : ℕ) : 0 < noisyPrior g i := by
  cases i with
  | zero => change 0 < (if g ≤ 1/2 then 3/4 else 51/100); split <;> norm_num
  | succ i => change 0 < 1/2 * ((i:ℝ)+2)^(-noisyExponent g); positivity

theorem noisyPrior_sum (g : ℝ) (n : ℕ) : ∑ j ∈ Finset.range n, noisyPrior g j ≤ 1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ']
    by_cases small : g ≤ 1/2
    · simp only [noisyPrior,noisyExponent,if_pos small,← Finset.mul_sum]
      linarith [noisy_prior_tail_small n]
    · simp only [noisyPrior,noisyExponent,if_neg small,← Finset.mul_sum]
      linarith [noisy_prior_tail_large n]

theorem noisyRate_spec {g : ℝ} (hg : 0 < g) (hu : g ≤ 3/4) :
    0 < noisyRate g ∧ noisyRate g < 1 ∧
      noisyExponent g * (g * Real.log 2) ≤ 2*Real.log (1+noisyRate g) ∧
      -Real.log (1-noisyRate g) ≤ (1+2*g)*Real.log (1+noisyRate g) := by
  have log2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases small : g ≤ 1/2
  · simp only [noisyRate,noisyExponent,if_pos small]
    refine ⟨hg,by linarith,?_,noisy_log_loss hg.le hu⟩
    have h := noisy_log_chord (z := 3/2) (w := 2*g) (by norm_num) (by positivity) (by linarith)
    rw [show 1-2*g+2*g*(3/2) = 1+g by ring] at h
    have endpoint := Real.log_le_log (by norm_num : 0 < (2:ℝ)^9)
      (show (2:ℝ)^9 ≤ (3/2)^16 by norm_num)
    rw [Real.log_pow,Real.log_pow] at endpoint
    norm_num1 at endpoint
    nlinarith [mul_le_mul_of_nonneg_left endpoint hg.le]
  · simp only [noisyRate,noisyExponent,if_neg small]
    refine ⟨by norm_num,by norm_num,?_,?_⟩
    · have endpoint := Real.log_le_log (by norm_num : 0 < (2:ℝ)^27)
        (show (2:ℝ)^27 ≤ (1+3/5)^40 by norm_num)
      rw [Real.log_pow,Real.log_pow] at endpoint
      norm_num only [Nat.cast_ofNat] at endpoint
      nlinarith [mul_le_mul_of_nonneg_right hu log2pos.le]
    · have ep := Real.log_nonneg (show (1:ℝ) ≤ (1+3/5)^2*(1-3/5) by norm_num)
      rw [Real.log_mul (by norm_num) (by norm_num),Real.log_pow] at ep
      norm_num only [Nat.cast_ofNat] at ep
      nlinarith [mul_nonneg (show 0 ≤ g-1/2 by linarith)
        (Real.log_nonneg (show (1:ℝ) ≤ 1+3/5 by norm_num))]

def noisyErrorsFrom (K : Set α) (s : ℕ → α) (a T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, if a ≤ t ∧ s t ∉ K then 1 else 0

theorem noisy_active_errors (g : ℝ) (L : ℕ → Set α) (s : ℕ → α) (i T : ℕ) :
    (noisyCountableRule g L).activeMistakes s i T = noisyErrorsFrom (L i) s (noisyStart i) T := by
  simp only [NoisyRule.activeMistakes,noisyCountableRule,noisyActive_iff,noisyErrorsFrom]

theorem errors_before_start (K : Set α) (s : ℕ → α) (a T : ℕ) :
    membershipErrors K s T ≤ min T a + noisyErrorsFrom K s a T := by
  induction T with
  | zero => simp [membershipErrors]
  | succ t ih =>
    have h₁ : membershipErrors K s (t+1) =
        membershipErrors K s t + (if s t ∈ K then 0 else 1) := by
      simp only [membershipErrors,Finset.sum_range_succ]
    have h₂ : noisyErrorsFrom K s a (t+1) = noisyErrorsFrom K s a t +
        (if a ≤ t ∧ s t ∉ K then 1 else 0) := by
      simp only [noisyErrorsFrom,Finset.sum_range_succ]
    rw [h₁,h₂]
    by_cases ht : a ≤ t <;> by_cases h : s t ∈ K <;>
      simp only [ht,h,not_true_eq_false,not_false_eq_true,and_true,and_false,
        if_false,if_true] <;> omega

end
end GenLimit.MistakeBounded
