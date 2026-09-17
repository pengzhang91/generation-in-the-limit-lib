import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
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

/-- A generic counting-to-lower-density transfer.  If `N` tends to infinity,
`D ≤ N`, and eventually `N ≤ qD + error` with `error / N → 0`, then the
lower limit of `D / N` is at least `1/q`. -/
theorem lowerDensity_inv_of_eventual_counting_atTop
    (N D error : ℕ → ℕ) (q : ℕ) (hq : 0 < q)
    (hN : Tendsto N atTop atTop)
    (hD : ∀ n, D n ≤ N n)
    (herror : Tendsto
      (fun n : ℕ => (error n : ℝ) / (N n : ℝ)) atTop (nhds 0))
    (hcount : ∀ᶠ n : ℕ in atTop, N n ≤ q * D n + error n) :
    (1 / (q : ℝ)) ≤
      liminf (fun n : ℕ => (D n : ℝ) / (N n : ℝ)) atTop := by
  let lower : ℕ → ℝ := fun n =>
    (1 / (q : ℝ)) - (error n : ℝ) / ((q : ℝ) * (N n : ℝ))
  have hscaled :
      Tendsto
        (fun n : ℕ => (error n : ℝ) / ((q : ℝ) * (N n : ℝ)))
        atTop (nhds 0) := by
    have hdiv := herror.div_const (q : ℝ)
    simpa [div_div, mul_comm] using hdiv
  have hlower : Tendsto lower atTop (nhds (1 / (q : ℝ))) := by
    simpa only [lower, sub_zero] using tendsto_const_nhds.sub hscaled
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < N n :=
    hN.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      lower n ≤ (D n : ℝ) / (N n : ℝ) := by
    filter_upwards [hNpos, hcount] with n hn hcountn
    have hnR : (0 : ℝ) < N n := by exact_mod_cast hn
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hcountR :
        (N n : ℝ) ≤ (q : ℝ) * (D n : ℝ) + (error n : ℝ) := by
      exact_mod_cast hcountn
    dsimp only [lower]
    rw [le_div_iff₀ hnR]
    field_simp [hqR.ne', hnR.ne']
    nlinarith
  have hratio_le_one :
      ∀ n, (D n : ℝ) / (N n : ℝ) ≤ 1 := by
    intro n
    by_cases hn : N n = 0
    · simp [hn]
    · have hnR : (0 : ℝ) < N n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnR]
      exact_mod_cast hD n
  calc
    (1 / (q : ℝ)) = liminf lower atTop := hlower.liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => (D n : ℝ) / (N n : ℝ)) atTop :=
      liminf_le_liminf hcompare hlower.isBoundedUnder_ge
        (isCoboundedUnder_ge_of_le atTop hratio_le_one)

end GenLimit
