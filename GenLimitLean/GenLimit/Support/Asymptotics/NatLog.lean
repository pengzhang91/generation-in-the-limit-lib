import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Natural logarithm asymptotics

Shared asymptotic facts for the discrete base-two logarithm.  These estimates
are used by both P30's sparse catch-up construction and P39's charging
argument.
-/

open Filter
open scoped Topology

namespace GenLimit

/-- The discrete base-two logarithm is negligible compared with `n`. -/
theorem tendsto_natLog2_div :
    Tendsto (fun n : ℕ => (Nat.log2 n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hlogb :
      Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [id_eq] using
      (Real.isLittleO_logb_id_atTop (b := (2 : ℝ))).natCast_atTop.tendsto_div_nhds_zero
  exact squeeze_zero
    (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n => div_le_div_of_nonneg_right (Real.log2_le_logb n) (Nat.cast_nonneg _))
    hlogb

end GenLimit
