import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# Square-sparse schedules

Paper-independent arithmetic and asymptotic facts for using perfect squares
as a density-zero schedule. P17 and P31 use the square/non-square partition
directly, while P32 reuses the square-root asymptotics for its shifted and
scaled quadratic exploration schedule.
-/

namespace GenLimit.SparseSquares

open Filter
open scoped Topology

/-- Perfect-square natural numbers, including zero. -/
def IsSquare (n : ℕ) : Prop := ∃ k, k * k = n

/-- Natural numbers outside the perfect squares. -/
def IsNonSquare (n : ℕ) : Prop := ¬ IsSquare n

noncomputable local instance : DecidablePred IsSquare :=
  Classical.decPred _

theorem isSquare_iff_sqrt (n : ℕ) :
    IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n :=
  Nat.exists_mul_self n

@[simp] theorem isSquare_mul_self (k : ℕ) :
    IsSquare (k * k) := ⟨k, rfl⟩

/-- A canonical nonsquare strictly between consecutive squares. -/
def betweenSquares (k : ℕ) : ℕ :=
  (k + 1) * (k + 1) + (k + 1)

theorem betweenSquares_isNonSquare (k : ℕ) :
    IsNonSquare (betweenSquares k) := by
  unfold IsNonSquare IsSquare betweenSquares
  apply Nat.not_exists_sq (m := k + 1)
  · nlinarith
  · nlinarith

theorem betweenSquares_strictMono :
    StrictMono betweenSquares := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [betweenSquares]
  nlinarith

theorem isNonSquare_infinite :
    {n : ℕ | IsNonSquare n}.Infinite := by
  exact
    (Set.infinite_range_of_injective
      betweenSquares_strictMono.injective).mono
      (by rintro _ ⟨k, rfl⟩; exact betweenSquares_isNonSquare k)

/-- Fewer than `sqrt n + 1` square positions occur before `n`. -/
theorem count_isSquare_le_sqrt_add_one (n : ℕ) :
    Nat.count IsSquare n ≤ Nat.sqrt n + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let squares := (Finset.range n).filter IsSquare
  have hinj : Set.InjOn Nat.sqrt (squares : Set ℕ) := by
    intro a ha b hb hab
    have haSquare : IsSquare a := (Finset.mem_filter.mp ha).2
    have hbSquare : IsSquare b := (Finset.mem_filter.mp hb).2
    calc
      a = Nat.sqrt a * Nat.sqrt a :=
        ((isSquare_iff_sqrt a).mp haSquare).symm
      _ = Nat.sqrt b * Nat.sqrt b := by rw [hab]
      _ = b := (isSquare_iff_sqrt b).mp hbSquare
  have hcard :
      squares.card = (squares.image Nat.sqrt).card := by
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact hinj ha hb hab
  rw [show ((Finset.range n).filter IsSquare) = squares by rfl, hcard]
  calc
    (squares.image Nat.sqrt).card ≤
        (Finset.range (Nat.sqrt n + 1)).card := by
      apply Finset.card_le_card
      intro q hq
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_range]
      have htn : t < n :=
        Finset.mem_range.mp (Finset.mem_filter.mp ht).1
      exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt htn.le)
    _ = Nat.sqrt n + 1 := Finset.card_range _

theorem natSqrt_tendsto_atTop :
    Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b ^ 2)] with a ha
  exact (Nat.le_sqrt' (m := b) (n := a)).2 ha

theorem natSqrtCast_tendsto_atTop :
    Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp natSqrt_tendsto_atTop

/-- `sqrt n / n` tends to zero along natural prefixes. -/
theorem natSqrt_div_self_tendsto_zero :
    Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hinv :
      Tendsto (fun n : ℕ => ((Nat.sqrt n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp natSqrtCast_tendsto_atTop
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hsqrtPos : (0 : ℝ) < Nat.sqrt n := by
      exact_mod_cast (Nat.sqrt_pos.2 hn)
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
    change (Nat.sqrt n : ℝ) / (n : ℝ) ≤
      1 / (Nat.sqrt n : ℝ)
    rw [div_le_div_iff₀ hnPos hsqrtPos]
    have hsquare : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have hsquare' : Nat.sqrt n * Nat.sqrt n ≤ 1 * n := by
      simpa using hsquare
    exact_mod_cast hsquare'
  · simpa [one_div] using hinv

/-- `(sqrt n + 1) / n` also tends to zero. -/
theorem natSqrt_add_one_div_self_tendsto_zero :
    Tendsto
      (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / (n : ℝ))
      atTop (nhds 0) := by
  have hnInv :
      Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inverse_atTop_nhds_zero_nat
  simpa [add_div, one_div] using
    natSqrt_div_self_tendsto_zero.add hnInv

end GenLimit.SparseSquares
