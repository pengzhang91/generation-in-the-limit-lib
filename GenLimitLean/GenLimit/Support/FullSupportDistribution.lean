import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Full-support distributions with a heavy atom

Every nonempty subset of the natural numbers admits a PMF with exactly that
support and probability at least one half at a specified point. The
construction filters a geometric distribution and mixes it with a point mass.
-/

namespace GenLimit.DiscreteIID

noncomputable section

open ProbabilityTheory
open scoped ENNReal NNReal

/-- A full-support distribution on the natural numbers. -/
def positiveGeometric : PMF ℕ := geometricPMF (p := 1 / 2) (by norm_num) (by norm_num)

theorem positiveGeometric_support (x : ℕ) : x ∈ positiveGeometric.support := by
  change positiveGeometric x ≠ 0
  change ENNReal.ofReal (geometricPMFReal (1 / 2) x) ≠ 0
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (geometricPMFReal_pos (by norm_num) (by norm_num)))

theorem exists_fullSupport_heavyAtom (K : Set ℕ) (x : ℕ) (hx : x ∈ K) :
    ∃ p : PMF ℕ, p.support = K ∧ (1 / 2 : ℝ) ≤ (p x).toReal := by
  let q := positiveGeometric.filter K ⟨x, hx, positiveGeometric_support x⟩
  have hq : q.support = K := by
    ext y
    rw [PMF.mem_support_filter_iff]
    exact and_iff_left (positiveGeometric_support y)
  let coin := PMF.bernoulli (1 / 2) (by norm_num)
  let p := coin.bind (fun b => if b then PMF.pure x else q)
  have hp (y : ℕ) : p y = (1 / 2 : ℝ≥0∞) * q y + (1 / 2 : ℝ≥0∞) * PMF.pure x y := by
    simp [p, coin, PMF.bind_apply, tsum_bool, PMF.bernoulli_apply]
  refine ⟨p, ?_, ?_⟩
  · ext y
    change p y ≠ 0 ↔ y ∈ K
    rw [hp]
    simp only [ne_eq, add_eq_zero, mul_eq_zero, not_and_or]
    have hh : (1 / 2 : ℝ≥0∞) ≠ 0 := by norm_num
    simp only [hh, false_or]
    constructor
    · rintro (hy | hy)
      · exact hq ▸ hy
      · have : y = x := (PMF.mem_support_pure_iff x y).mp hy
        exact this ▸ hx
    · intro hy
      have hyq : y ∈ q.support := by rw [hq]; exact hy
      exact Or.inl hyq
  · have h : (1 / 2 : ℝ≥0∞) ≤ p x := by
      rw [hp, PMF.pure_apply_self, mul_one]
      exact le_add_left le_rfl
    have hr := ENNReal.toReal_mono (p.apply_ne_top x) h
    norm_num at hr
    exact hr

end
end GenLimit.DiscreteIID
