import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Liminf transfer under vanishing additive error

A paper-independent endgame for asymptotic performance comparisons.  If a
bounded sequence is eventually at most another bounded-above sequence plus
an error tending to zero, then its liminf is at most the other's liminf.
-/

namespace GenLimit

open Filter

theorem liminf_le_liminf_of_eventually_le_add_tendsto_zero
    {u v error : ℕ → ℝ}
    (huNonneg : ∀ n, 0 ≤ u n) (huOne : ∀ n, u n ≤ 1)
    (hvOne : ∀ n, v n ≤ 1)
    (hcompare : ∀ᶠ n in atTop, u n ≤ v n + error n)
    (herror : Tendsto error atTop (nhds 0)) :
    liminf u atTop ≤ liminf v atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have herrorSmall : ∀ᶠ n in atTop, error n ≤ ε :=
    ((tendsto_order.1 herror).2 ε hε).mono fun _ h => h.le
  have hshift : ∀ᶠ n in atTop, u n - ε ≤ v n := by
    filter_upwards [hcompare, herrorSmall] with n hcomp herr
    linarith
  have hlim :
      liminf (fun n => u n - ε) atTop ≤ liminf v atTop := by
    exact liminf_le_liminf hshift
      (isBoundedUnder_of ⟨-ε, fun n => by linarith [huNonneg n]⟩)
      (isCoboundedUnder_ge_of_le atTop hvOne)
  rw [liminf_sub_const atTop u ε
    (isCoboundedUnder_ge_of_le atTop huOne)
    (isBoundedUnder_of ⟨0, huNonneg⟩)] at hlim
  linarith

end GenLimit
