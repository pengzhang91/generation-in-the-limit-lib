import GenLimit.Support.Asymptotics.NatLog
import GenLimit.Support.Asymptotics.Liminf
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The asymptotic counting argument for lower density

This module isolates the final analytic calculation in the proof of Theorem 3.14.
After the order-preserving reduction of the target language to `ℕ`, let `D n`
and `A n` count the first `n` target elements first announced by the generator
and adversary.  If these counts partition each prefix, and the charging
argument bounds `A n` by `D n + r + log₂ n`, then the generator has lower
density at least `1/2`.
-/

open Filter
open scoped Topology

namespace GenLimit

/-- A fixed constant plus `log₂ n` is negligible compared with `n`. -/
theorem tendsto_countingError_div (r : ℕ) :
    Tendsto (fun n : ℕ => ((r + Nat.log2 n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => (r : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [Nat.cast_add, add_div, zero_add] using hr.add tendsto_natLog2_div

/-- The lower comparison sequence used in Theorem 3.14 tends to `1/2`. -/
theorem tendsto_half_sub_countingError (r : ℕ) :
    Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) - ((r + Nat.log2 n : ℕ) : ℝ) / (2 * (n : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := (tendsto_countingError_div r).div_const (2 : ℝ)
  simpa [div_div, mul_comm] using tendsto_const_nhds.sub h

/-- The asymptotic counting core of Theorem 3.14.

`D n` and `A n` are the numbers among the first `n` target elements first
announced by the generator and adversary, respectively. The first assumption
says these two classes partition every prefix. The second is the charging
bound obtained from Fact 3.12 and Lemma 3.13.
-/
theorem lowerDensity_half_of_counting
    (D A : ℕ → ℕ) (r : ℕ)
    (hpartition : ∀ n, D n + A n = n)
    (hcharge : ∀ n, A n ≤ D n + r + Nat.log2 n) :
    (1 / 2 : ℝ) ≤ liminf (fun n : ℕ => (D n : ℝ) / (n : ℝ)) atTop := by
  have hD_le_n : ∀ n, D n ≤ n := fun n => by
    calc
      D n ≤ D n + A n := Nat.le_add_right _ _
      _ = n := hpartition n
  have hcount : ∀ᶠ n : ℕ in atTop,
      n ≤ 2 * D n + (r + Nat.log2 n) :=
    Filter.Eventually.of_forall fun n => by
      calc
        n = D n + A n := (hpartition n).symm
        _ ≤ D n + (D n + r + Nat.log2 n) :=
          Nat.add_le_add_left (hcharge n) _
        _ = 2 * D n + (r + Nat.log2 n) := by omega
  have h := GenLimit.lowerDensity_inv_of_eventual_counting_atTop
    id D (fun n => r + Nat.log2 n) 2 (by omega) tendsto_id
    hD_le_n (tendsto_countingError_div r) hcount
  simpa using h

end GenLimit
