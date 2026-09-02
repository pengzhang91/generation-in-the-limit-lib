import GenLimit.Paper17_InfiniteContamination.Definitions
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The exact density of the even numbers

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Definition 1 and Example 6.6.

The source works with positive naturals.  This module uses Lean's naturals,
whose canonical order begins at zero.  The finite prefix counts differ by at
most one, and the literal ordered lower and upper densities are both exactly
`1/2`.
-/

namespace GenLimit.InfiniteContamination

open Filter
open scoped Topology
open GenLimit.KleinbergWei

/-- The canonical order on Lean's natural numbers. -/
def naturalOrder : OrderedLanguage where
  carrier := Set.univ
  enumeration := fun n => n
  enumeration_injective := fun _ _ h => h
  range_enumeration := by
    ext n
    simp

/-- The even-number language from Example 6.6. -/
def evenNaturals : GenLimit.Language := {n | Even n}

theorem naturalOrder_prefixCount_even_two_mul (d : ℕ) :
    naturalOrder.prefixCount evenNaturals (2 * d) = d := by
  classical
  let E : Finset ℕ := (Finset.range d).image (fun k => 2 * k)
  have heq :
      (Finset.range (2 * d)).filter
          (fun i => naturalOrder.enumeration i ∈ evenNaturals) = E := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, naturalOrder,
      evenNaturals, Set.mem_setOf_eq, E, Finset.mem_image]
    constructor
    · rintro ⟨hx, heven⟩
      obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp heven
      exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, even_iff_exists_two_mul.mpr ⟨k, rfl⟩⟩
  unfold OrderedLanguage.prefixCount
  rw [heq]
  dsimp [E]
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ hab
    change 2 * a = 2 * b at hab
    omega

theorem naturalOrder_prefixCount_even_two_mul_add_one (d : ℕ) :
    naturalOrder.prefixCount evenNaturals (2 * d + 1) = d + 1 := by
  classical
  have hsplit :
      (Finset.range (2 * d + 1)).filter
          (fun i => naturalOrder.enumeration i ∈ evenNaturals) =
        insert (2 * d)
          ((Finset.range (2 * d)).filter
            (fun i => naturalOrder.enumeration i ∈ evenNaturals)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range,
      Finset.mem_insert, naturalOrder, evenNaturals, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, heven⟩
      by_cases hxd : x = 2 * d
      · exact Or.inl hxd
      · exact Or.inr ⟨by omega, heven⟩
    · rintro (rfl | ⟨hx, heven⟩)
      · exact ⟨by omega, even_two_mul d⟩
      · exact ⟨by omega, heven⟩
  unfold OrderedLanguage.prefixCount
  rw [hsplit, Finset.card_insert_of_notMem]
  · rw [show
      ((Finset.range (2 * d)).filter
          (fun i => naturalOrder.enumeration i ∈ evenNaturals)).card =
        naturalOrder.prefixCount evenNaturals (2 * d) by rfl]
    rw [naturalOrder_prefixCount_even_two_mul]
  · simp

/-- Exact finite-prefix formula: the first `n` naturals contain
`(n+1)/2` even values. -/
theorem naturalOrder_prefixCount_even (n : ℕ) :
    naturalOrder.prefixCount evenNaturals n = (n + 1) / 2 := by
  obtain ⟨d, h | h⟩ := Nat.even_or_odd' n
  · subst n
    rw [naturalOrder_prefixCount_even_two_mul]
    omega
  · subst n
    rw [naturalOrder_prefixCount_even_two_mul_add_one]
    omega

theorem naturalOrder_prefixRatio_even_bounds
    {n : ℕ} (hn : 0 < n) :
    (1 / 2 : ℝ) ≤ naturalOrder.prefixRatio evenNaturals n ∧
      naturalOrder.prefixRatio evenNaturals n ≤
        (1 / 2 : ℝ) + 1 / n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [OrderedLanguage.prefixRatio, if_neg hn0,
    naturalOrder_prefixCount_even]
  obtain ⟨d, h | h⟩ := Nat.even_or_odd' n
  · subst n
    have hdiv : (2 * d + 1) / 2 = d := by omega
    rw [hdiv]
    have hd : 0 < d := by omega
    have hden : (0 : ℝ) < 2 * d := by positivity
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one]
    constructor <;>
      field_simp <;>
      nlinarith
  · subst n
    have hdiv : (2 * d + 1 + 1) / 2 = d + 1 := by omega
    rw [hdiv]
    have hden : (0 : ℝ) < 2 * d + 1 := by positivity
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one]
    constructor <;>
      field_simp <;>
      nlinarith

theorem tendsto_naturalOrder_prefixRatio_even :
    Tendsto (naturalOrder.prefixRatio evenNaturals)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hrecip :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have herror :
      Tendsto
        (fun n : ℕ =>
          naturalOrder.prefixRatio evenNaturals n - (1 / 2 : ℝ))
        atTop (𝓝 0) := by
    refine squeeze_zero'
      (f := fun n : ℕ =>
        naturalOrder.prefixRatio evenNaturals n - (1 / 2 : ℝ))
      (g := fun n : ℕ => (1 : ℝ) / n) ?_ ?_ hrecip
    · filter_upwards [eventually_gt_atTop 0] with n hn
      linarith [naturalOrder_prefixRatio_even_bounds hn |>.1]
    · filter_upwards [eventually_gt_atTop 0] with n hn
      linarith [naturalOrder_prefixRatio_even_bounds hn |>.2]
  have hsum :
      Tendsto
        (fun n : ℕ =>
          (1 / 2 : ℝ) +
            (naturalOrder.prefixRatio evenNaturals n - (1 / 2 : ℝ)))
        atTop (𝓝 ((1 / 2 : ℝ) + 0)) :=
    tendsto_const_nhds.add herror
  convert hsum using 1
  · funext n
    ring
  · simp

/-- The exact lower-density calculation in Definition 1. -/
theorem evenNaturals_lowerDensity :
    naturalOrder.lowerDensity evenNaturals = (1 / 2 : ℝ) := by
  exact tendsto_naturalOrder_prefixRatio_even.liminf_eq

/-- The exact upper-density calculation in Definition 1. -/
theorem evenNaturals_upperDensity :
    naturalOrder.upperDensity evenNaturals = (1 / 2 : ℝ) := by
  exact tendsto_naturalOrder_prefixRatio_even.limsup_eq

end GenLimit.InfiniteContamination
