import GenLimit.Paper29_MistakeBoundedLanguageGeneration.NoisySchedule
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Lemma 7.2 with its printed constants

Before an error, an active language has at most half the total weight.
This sharper bound, the one-based activation round, and a separate first
prior avoid the additive normalizing constant in the paper's derivation.
-/
namespace GenLimit.MistakeBounded
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem first_after_miss {g : ℝ} (hg : 0 < g) (hu : g ≤ 3/4) (m d : ℕ)
    (h : Real.log (noisyPrior g 0) + m * Real.log (1+noisyRate g) +
      d * Real.log (1-noisyRate g) ≤ Real.log (1/2)) :
    (m:ℝ)+1 ≤ (1+2*g)*d := by
  by_cases small : g ≤ 1/2
  · simp only [noisyPrior,noisyRate,if_pos small] at h
    have endpoint := Real.log_le_log (show (0:ℝ) < 1/2*(1+g) by positivity)
      (show (1:ℝ)/2*(1+g) ≤ 3/4 by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at endpoint
    have gain_pos := Real.log_pos (show (1:ℝ) < 1+g by linarith)
    have cost := mul_le_mul_of_nonneg_left (noisy_log_loss hg.le hu) (Nat.cast_nonneg (α := ℝ) d)
    apply (mul_le_mul_iff_left₀ gain_pos).mp
    nlinarith
  · simp only [noisyPrior,noisyRate,if_neg small] at h
    have twice : m < 2*d := by
      by_contra! hm
      have hlog := Real.log_nonneg (show (1:ℝ) ≤ (1+3/5)^2*(1-3/5) by norm_num)
      rw [Real.log_mul (by norm_num) (by norm_num),Real.log_pow] at hlog
      norm_num only [Nat.cast_ofNat] at hlog
      have hpos := Real.log_nonneg (show (1:ℝ) ≤ 1+3/5 by norm_num)
      have gap := Real.log_lt_log (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 < 51/100)
      have hm' : (2:ℝ)*d ≤ m := by exact_mod_cast hm
      nlinarith [mul_le_mul_of_nonneg_right hm' hpos,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hlog]
    have bound : (m:ℝ)+1 ≤ 2*d := by exact_mod_cast twice
    nlinarith [mul_nonneg (show 0 ≤ g-1/2 by linarith) (Nat.cast_nonneg (α := ℝ) d)]

private theorem later_before_miss {g : ℝ} (hg : 0 < g) (hu : g ≤ 3/4) (j m d : ℕ)
    (h : Real.log (noisyPrior g (j+1)) + m * Real.log (1+noisyRate g) +
      d * Real.log (1-noisyRate g) ≤ Real.log (1/2)) :
    (m:ℝ) ≤ (1+2*g)*d + (2/g)*Real.logb 2 ((j:ℝ)+2) := by
  obtain ⟨δpos,_,gain,loss⟩ := noisyRate_spec hg hu
  have gain_pos := Real.log_pos (show (1:ℝ) < 1+noisyRate g by linarith)
  have bpos := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have xpos : (0:ℝ) < j+2 := by positivity
  have xposlog := Real.log_nonneg (show (1:ℝ) ≤ j+2 by linarith [Nat.cast_nonneg (α := ℝ) j])
  rw [noisyPrior,Real.log_mul (by norm_num) (Real.rpow_pos_of_pos xpos _).ne',
    Real.log_rpow xpos] at h
  have scaled : noisyExponent g ≤ 2/g/Real.log 2 * Real.log (1+noisyRate g) := by
    rw [div_div,div_mul_eq_mul_div,le_div_iff₀ (mul_pos hg bpos)]
    linarith
  apply (mul_le_mul_iff_left₀ gain_pos).mp
  unfold Real.logb
  have term := mul_le_mul_of_nonneg_right scaled xposlog
  have cost := mul_le_mul_of_nonneg_left loss (Nat.cast_nonneg (α := ℝ) d)
  simp only [div_eq_mul_inv] at term ⊢
  nlinarith

/-- One causal generator simultaneously satisfies all comparator and horizon
bounds. The cutoff is the zero-based translation of floor(log₂ i), inclusive. -/
theorem noisy_infinite_generation [Infinite α] (L : ℕ → Set α) (inf : ∀ i, (L i).Infinite)
    (g : ℝ) (hg : 0 < g) (hu : g ≤ 3/4) :
    ∃ G : Generic.Generator α, (∀ t h (i : Fin t), G t h ≠ h i) ∧
      ∀ s, Function.Injective s → ∀ i T,
        (membershipErrors (L i) (Generic.output G s) T : ℝ) ≤
          (1+2*g)*noisyErrorsFrom (L i) s (noisyStart i) T +
          (1+2/g)*Real.logb 2 ((i:ℝ)+1) := by
  classical
  let R := noisyCountableRule g L
  refine ⟨R.generator,R.fresh,?_⟩
  intro s hs i T
  let out := Generic.output R.generator s
  let K := L i
  let a := noisyStart i
  let B := Real.logb 2 ((i:ℝ)+1)
  let pred := noisyErrorsFrom K out a
  let demo := noisyErrorsFrom K s a
  have Bpos : 0 ≤ B := Real.logb_nonneg (by norm_num)
    (by linarith [Nat.cast_nonneg (α := ℝ) i])
  have stat : ∀ t, (membershipErrors K out t : ℝ) ≤
      (1+2*g)*demo t + (1+2/g)*B := by
    intro t
    induction t with
    | zero => simp only [membershipErrors,Finset.range_zero,Finset.sum_empty,Nat.cast_zero]
              positivity
    | succ t ih =>
      have count := errors_before_start K out a t
      have cost : (demo t : ℝ) ≤ demo (t+1) := by
        apply Nat.cast_le.mpr
        change noisyErrorsFrom K s a t ≤ noisyErrorsFrom K s a (t+1)
        simp only [noisyErrorsFrom,Finset.sum_range_succ]
        exact Nat.le_add_right ..
      have lift := mul_le_mul_of_nonneg_left cost (show 0 ≤ 1+2*g by linarith)
      by_cases hx : out t ∈ K
      · simpa only [membershipErrors,Finset.sum_range_succ,if_pos hx,add_zero] using
          ih.trans (add_le_add_right lift _)
      · have inc : membershipErrors K out (t+1) = membershipErrors K out t + 1 := by
          simp [membershipErrors,Finset.sum_range_succ,hx]
        rw [inc,Nat.cast_add,Nat.cast_one]
        apply le_trans _ (add_le_add_right lift _)
        have aB : (a:ℝ) ≤ B := by
          have lb : (Nat.log2 (i+1):ℝ) ≤ B := by simpa only [B,Nat.cast_add,Nat.cast_one] using Real.log2_le_logb (i+1)
          apply le_trans _ lb
          exact_mod_cast (Nat.pred_le (Nat.log2 (i+1)))
        by_cases active : a ≤ t
        · obtain ⟨δpos,δlt,_,_⟩ := noisyRate_spec hg hu
          have h := R.miss_log_le_half s hs (fun k => (noisyPrior_pos g k).le)
            δpos δlt t (fun j hj k hk =>
              noisyActive_iff.mpr ((noisyActive_iff.mp hk).trans hj.le)) (noisyPrior_sum g _)
            i (noisyActive_iff.mpr active) (inf i) (noisyPrior_pos g i) hx
          change Real.log (noisyPrior g i) +
            (noisyCountableRule g L).activeMistakes out i t * Real.log (1+noisyRate g) +
            (noisyCountableRule g L).activeMistakes s i t * Real.log (1-noisyRate g) ≤ _ at h
          rw [noisy_active_errors,noisy_active_errors] at h
          change Real.log (noisyPrior g i) + pred t * _ + demo t * _ ≤ _ at h
          have pp : (membershipErrors K out t : ℝ) ≤ (a:ℝ)+pred t := by
            exact_mod_cast (count.trans (Nat.add_le_add_right (Nat.min_le_right ..) _))
          cases i with
          | zero =>
            have az : a = 0 := by decide
            have bz : B = 0 := by simp [B,Real.logb]
            rw [az,Nat.cast_zero,zero_add] at pp
            rw [bz,mul_zero,add_zero]
            linarith [first_after_miss hg hu (pred t) (demo t) h]
          | succ j =>
            have az : (a:ℝ)+1 ≤ B := by
              have hp : 0 < Nat.log2 (j+1+1) := by rw [Nat.log2_eq_log_two]; exact Nat.log_pos (by decide) (by omega)
              have eq : a+1 = Nat.log2 (j+1+1) := Nat.succ_pred_eq_of_pos hp
              have le := Real.log2_le_logb (j+1+1)
              simpa only [← eq,Nat.cast_add,Nat.cast_one,B,Nat.cast_succ] using le
            have hb := later_before_miss hg hu j (pred t) (demo t) h
            have bform : B = Real.logb 2 ((j:ℝ)+2) := by simp [B]; ring_nf
            rw [← bform] at hb
            nlinarith
        · have da : pred t = 0 := by
            apply Finset.sum_eq_zero
            intro k hk
            have lt := Finset.mem_range.mp hk
            change (if a ≤ k ∧ out k ∉ K then (1:ℕ) else 0) = 0
            simp [show ¬a ≤ k by omega]
          have cnt : membershipErrors K out t + 1 ≤ a := by
            change membershipErrors K out t ≤ min t a + pred t at count
            omega
          have cr : (membershipErrors K out t : ℝ)+1 ≤ a := by exact_mod_cast cnt
          nlinarith [mul_nonneg (show 0 ≤ 2/g by positivity) Bpos,
            mul_nonneg (show 0 ≤ 1+2*g by linarith) (Nat.cast_nonneg (demo t) (α := ℝ))]
  exact stat T

end
end GenLimit.MistakeBounded
