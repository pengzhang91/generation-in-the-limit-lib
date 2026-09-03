import GenLimit.Paper29_MistakeBoundedLanguageGeneration.Definitions
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The weighted-halving potential argument

This is an abstract weighted-halving lemma used by the potential strategy in
arXiv:2605.10809v1.  The paper's concrete Algorithm 1 recurrence and Appendix
Lemma A.1 still require an instantiation of this abstraction.  The target
weight is explicitly positive, as required before the printed Theorem 4.1
logarithm is finite.
-/

namespace GenLimit.MistakeBounded

/-- A potential never increases, and it loses at least a factor two on every
mistake. -/
structure HalvingPotential (trace : MistakeTrace) where
  potential : ℕ → ℝ
  nonnegative : ∀ t, 0 ≤ potential t
  step :
    ∀ t, potential (t + 1) ≤
      if trace t = true then potential t / 2 else potential t

theorem two_pow_count_mul_potential_le
    {trace : MistakeTrace} (P : HalvingPotential trace) :
    ∀ t, (2 : ℝ) ^ mistakeCount trace t * P.potential t ≤ P.potential 0 := by
  intro t
  induction t with
  | zero =>
      simp
  | succ t ih =>
      rw [mistakeCount_succ]
      by_cases hm : trace t = true
      · simp only [hm, if_true, pow_succ]
        calc
          (2 : ℝ) ^ mistakeCount trace t * 2 * P.potential (t + 1)
              = (2 : ℝ) ^ mistakeCount trace t *
                  (2 * P.potential (t + 1)) := by ring
          _ ≤ (2 : ℝ) ^ mistakeCount trace t * P.potential t := by
            apply mul_le_mul_of_nonneg_left
            · have hs := P.step t
              rw [if_pos hm] at hs
              linarith
            · positivity
          _ ≤ P.potential 0 := ih
      · have hmfalse : trace t = false := by
          cases h : trace t <;> simp_all
        simp only [hm]
        calc
          (2 : ℝ) ^ mistakeCount trace t * P.potential (t + 1)
              ≤ (2 : ℝ) ^ mistakeCount trace t * P.potential t := by
            apply mul_le_mul_of_nonneg_left
            · have hs := P.step t
              rw [if_neg hm] at hs
              exact hs
            · positivity
          _ ≤ P.potential 0 := ih

/-- The target's initial mass survives in every active potential. -/
def TargetWeightSurvives
    {trace : MistakeTrace} (P : HalvingPotential trace) (weight : ℝ) : Prop :=
  0 < weight ∧ ∀ t, weight ≤ P.potential t

/-- Abstract guarded halving bound: after `k` mistakes, the initial potential
is at least `2^k` times the positive surviving weight. -/
theorem halvingPotential_bound
    {trace : MistakeTrace} (P : HalvingPotential trace) {weight : ℝ}
    (hw : TargetWeightSurvives P weight) (t : ℕ) :
    (2 : ℝ) ^ mistakeCount trace t * weight ≤ P.potential 0 := by
  calc
    (2 : ℝ) ^ mistakeCount trace t * weight
        ≤ (2 : ℝ) ^ mistakeCount trace t * P.potential t := by
      exact mul_le_mul_of_nonneg_left (hw.2 t) (by positivity)
    _ ≤ P.potential 0 := two_pow_count_mul_potential_le P t

/-- Finite-class specialization underlying the logarithmic part of
Theorem 5.1: with unit surviving target weight and initial mass `N`, every
prefix with `k` mistakes satisfies `2^k ≤ N`. -/
theorem finite_class_halving_bound
    {trace : MistakeTrace} (P : HalvingPotential trace) (N : ℕ)
    (hinitial : P.potential 0 = N)
    (hsurvives : ∀ t, (1 : ℝ) ≤ P.potential t)
    (t : ℕ) :
    (2 : ℝ) ^ mistakeCount trace t ≤ N := by
  have h := halvingPotential_bound P ⟨by norm_num, hsurvives⟩ t
  simpa [hinitial] using h

end GenLimit.MistakeBounded
