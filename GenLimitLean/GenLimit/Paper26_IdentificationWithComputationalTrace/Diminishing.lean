import GenLimit.Paper26_IdentificationWithComputationalTrace.Edits
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Positivity

namespace GenLimit.ComputationalTrace

/-- The learner is supplied the cutoff for every real rate in (0,1). -/
def AllRates {α : Type*} (cut : ℝ → ℕ) (n : ℕ) (xs ys : List α) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 → RateBound r (cut r) n xs ys

noncomputable def realCutoff (cut : ℕ → ℕ) (r : ℝ) := cut ⌈1 / r⌉₊

theorem DiminishingBound.allRates {α : Type*} {cut n} {xs ys : List α}
    (h : DiminishingBound cut n xs ys) : AllRates (realCutoff cut) n xs ys := by
  intro r hr _ hn
  let d := ⌈1 / r⌉₊
  obtain ⟨k,hk,he⟩ := h d hn
  have hd : 1 / r ≤ (d : ℝ) := Nat.le_ceil _
  have hpos : (0 : ℝ) < d + 2 := by positivity
  have hrate : 1 / ((d : ℝ) + 2) ≤ r := by
    rw [div_le_iff₀ hpos]
    have hh := (div_le_iff₀ hr).mp hd
    linarith only [hh, mul_comm (d : ℝ) r, show 0 ≤ 2 * r by positivity,
      mul_add r (d : ℝ) 2, mul_comm r 2]
  exact ⟨k,hk,he.trans (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg _))⟩

theorem AllRates.reciprocals {α : Type*} {cut n} {xs ys : List α}
    (h : AllRates cut n xs ys) : DiminishingBound (fun d => cut (1 / ((d : ℝ)+2))) n xs ys := by
  intro d
  exact h _ (by positivity) (by rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) d])

end GenLimit.ComputationalTrace
