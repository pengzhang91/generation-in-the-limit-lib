import GenLimit.Paper30_TimeSensitiveLanguageGeneration.RateEnvelope

/-!
# Appendix-D bridge from a real rate to a natural budget

The diagonal construction in `FeasibleProfileDiagonal` is deliberately
stated for a natural budget.  In the source application that budget is
`B(t) = floor(t H_el(t))`.  This file supplies that missing bridge without
silently obtaining growth from the assumption `H_el(t) → 0`.

Vanishing of a nonnegative real rate implies `B(t) / t → 0`.  Divergence of
`B` is separate: it follows either from the explicit premise
`t H_el(t) → ∞`, or, in the source's feasible regime, from
`D_el⁻¹(t) = o(t H_el(t))` together with divergence of the deadline inverse.
-/

namespace GenLimit.TimeSensitive

open Filter

/-- The source's natural hallucination budget
`B(t) = floor(t H_el(t))`. -/
noncomputable def flooredRateBudget
    (H : ℕ → ℝ)
    (t : ℕ) : ℕ :=
  ⌊(t : ℝ) * H t⌋₊

@[simp]
theorem flooredRateBudget_zero
    (H : ℕ → ℝ) :
    flooredRateBudget H 0 = 0 := by
  simp [flooredRateBudget]

theorem flooredRateBudget_cast_le
    (H : ℕ → ℝ)
    (hH : ∀ t, 0 ≤ H t)
    (t : ℕ) :
    (flooredRateBudget H t : ℝ) ≤ (t : ℝ) * H t := by
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg t) (hH t))

/-- Flooring can only decrease the normalized real rate. -/
theorem natRatio_flooredRateBudget_le
    (H : ℕ → ℝ)
    (hH : ∀ t, 0 ≤ H t)
    (t : ℕ) :
    natRatio (flooredRateBudget H) t ≤ H t := by
  by_cases ht : t = 0
  · simp [natRatio, ht, hH 0]
  · have htReal : (0 : ℝ) < t := by
      exact_mod_cast Nat.pos_of_ne_zero ht
    rw [natRatio, if_neg ht]
    calc
      (flooredRateBudget H t : ℝ) / (t : ℝ)
          ≤ ((t : ℝ) * H t) / (t : ℝ) :=
        div_le_div_of_nonneg_right
          (flooredRateBudget_cast_le H hH t) htReal.le
      _ = H t := by field_simp

/-- A nonnegative vanishing real rate has a vanishing normalized floored
budget.  No lower-growth assumption is used here. -/
theorem natRatio_flooredRateBudget_tendsto_zero
    (H : ℕ → ℝ)
    (hH : ∀ t, 0 ≤ H t)
    (hvanishing : Tendsto H atTop (nhds 0)) :
    Tendsto (natRatio (flooredRateBudget H)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t =>
      natRatio_nonneg (flooredRateBudget H) t
  · exact Filter.Eventually.of_forall fun t =>
      natRatio_flooredRateBudget_le H hH t
  · exact hvanishing

/-- An explicit lower-growth premise on `t H(t)` makes the floored natural
budget diverge.  Vanishing of `H` alone does not imply this premise. -/
theorem flooredRateBudget_tendsto_atTop
    (H : ℕ → ℝ)
    (hgrowth :
      Tendsto (fun t : ℕ => (t : ℝ) * H t) atTop atTop) :
    Tendsto (flooredRateBudget H) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp hgrowth

/-- Integer-scaled form of `a(t) = o(b(t))` when the comparison budget
`b` is real-valued.  This is the form of the source feasibility condition
`D_el⁻¹(t) = o(t H_el(t))` used by the natural diagonal. -/
def NatLittleOAlongRealBudget
    (a : ℕ → ℕ)
    (b : ℕ → ℝ) : Prop :=
  ∀ q, 0 < q →
    ∃ T, ∀ t, T ≤ t → ((q * a t : ℕ) : ℝ) ≤ b t

/-- Real-budget little-o survives taking the natural floor. -/
theorem natLittleOAlong_floor
    (a : ℕ → ℕ)
    (b : ℕ → ℝ)
    (hsmall : NatLittleOAlongRealBudget a b) :
    NatLittleOAlongBudget a (fun t => ⌊b t⌋₊) := by
  intro q hq
  obtain ⟨T, hT⟩ := hsmall q hq
  exact ⟨T, fun t ht => Nat.le_floor (hT t ht)⟩

theorem natLittleOAlong_flooredRateBudget
    (a : ℕ → ℕ)
    (H : ℕ → ℝ)
    (hsmall :
      NatLittleOAlongRealBudget a
        (fun t : ℕ => (t : ℝ) * H t)) :
    NatLittleOAlongBudget a (flooredRateBudget H) := by
  simpa [flooredRateBudget] using
    natLittleOAlong_floor a
      (fun t : ℕ => (t : ℝ) * H t) hsmall

/-- If a divergent natural scale is little-o of the real product, then the
floored product diverges.  This is the source-feasibility route to budget
divergence. -/
theorem flooredRateBudget_tendsto_atTop_of_littleO
    (a : ℕ → ℕ)
    (H : ℕ → ℝ)
    (ha : Tendsto a atTop atTop)
    (hsmall :
      NatLittleOAlongRealBudget a
        (fun t : ℕ => (t : ℝ) * H t)) :
    Tendsto (flooredRateBudget H) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  obtain ⟨T, hT⟩ := hsmall 1 Nat.zero_lt_one
  filter_upwards
    [(tendsto_atTop.1 ha) n, eventually_ge_atTop T] with t hat ht
  have haFloor :
      a t ≤ flooredRateBudget H t := by
    apply Nat.le_floor
    simpa using hT t ht
  exact hat.trans haFloor

namespace NaturalFeasibleProfile

/-- Build the natural Appendix-D profile from a raw real element-wise rate.

The extra premise `hfeasible` is stated explicitly: it is the
integer-scaled source condition
`D_el⁻¹(t) = o(t H_el(t))`.  It supplies both natural-budget divergence and
the inverse-little-o field.  Antitonicity, nonnegativity, and vanishing of
`H_el` are not needed merely to build this structure and are therefore not
hidden in the constructor. -/
noncomputable def ofRawRate
    (D : Deadline)
    (hD : D.NatSuperlinear)
    (hstrict : D.EventuallyStrict)
    (H : ℕ → ℝ)
    (hfeasible :
      NatLittleOAlongRealBudget
        (D.inverse hD.isUnbounded)
        (fun t : ℕ => (t : ℝ) * H t)) :
    NaturalFeasibleProfile where
  deadline := D
  deadlineSuperlinear := hD
  deadlineEventuallyStrict := hstrict
  budget := flooredRateBudget H
  budget_tendsto :=
    flooredRateBudget_tendsto_atTop_of_littleO
      (D.inverse hD.isUnbounded) H
      (D.inverse_tendsto_atTop hD.isUnbounded) hfeasible
  inverseLittleO :=
    natLittleOAlong_flooredRateBudget
      (D.inverse hD.isUnbounded) H hfeasible

/-- Source-facing constructor using the paper's stated discrete-convex
deadline premise to derive the eventual strictness needed by the proof. -/
noncomputable def ofRawRateDiscreteConvex
    (D : Deadline)
    (hD : D.NatSuperlinear)
    (hconvex : D.DiscreteConvex)
    (H : ℕ → ℝ)
    (hfeasible :
      NatLittleOAlongRealBudget
        (D.inverse hD.isUnbounded)
        (fun t : ℕ => (t : ℝ) * H t)) :
    NaturalFeasibleProfile :=
  ofRawRate D hD
    (hD.eventuallyStrict_of_discreteConvex D hconvex)
    H hfeasible

theorem ofRawRate_budget_ratio_tendsto_zero
    (D : Deadline)
    (hD : D.NatSuperlinear)
    (hstrict : D.EventuallyStrict)
    (H : ℕ → ℝ)
    (hfeasible :
      NatLittleOAlongRealBudget
        (D.inverse hD.isUnbounded)
        (fun t : ℕ => (t : ℝ) * H t))
    (hH : ∀ t, 0 ≤ H t)
    (hvanishing : Tendsto H atTop (nhds 0)) :
    Tendsto
      (natRatio
        (ofRawRate D hD hstrict H hfeasible).budget)
      atTop (nhds 0) := by
  simpa [ofRawRate] using
    natRatio_flooredRateBudget_tendsto_zero H hH hvanishing

/-- The raw prefix rate obtained from the floored budget is eventually
bounded by the original real rate. -/
theorem ofRawRate_prefixRate_eventually_le
    (D : Deadline)
    (hD : D.NatSuperlinear)
    (hstrict : D.EventuallyStrict)
    (H : ℕ → ℝ)
    (hfeasible :
      NatLittleOAlongRealBudget
        (D.inverse hD.isUnbounded)
        (fun t : ℕ => (t : ℝ) * H t))
    (hH : ∀ t, 0 ≤ H t) :
    ∀ᶠ t : ℕ in atTop,
      (ofRawRate D hD hstrict H hfeasible).prefixRate t ≤ H t := by
  let P := ofRawRate D hD hstrict H hfeasible
  filter_upwards [P.prefixRate_eventually_le_original] with t ht
  exact ht.trans (natRatio_flooredRateBudget_le H hH t)

/-- Appendix-D's deterministic rate package, now starting from the source's
raw real antitone vanishing rate.

This reaches every rate conclusion before the separate question whether
the composed prefix deadline is discretely convex. -/
theorem appendixD_raw_rate_monotone_prefix_estimates
    (D : Deadline)
    (hD : D.NatSuperlinear)
    (hstrict : D.EventuallyStrict)
    (H : ℕ → ℝ)
    (hH : ∀ t, 0 ≤ H t)
    (hHanti : Antitone H)
    (hvanishing : Tendsto H atTop (nhds 0))
    (hfeasible :
      NatLittleOAlongRealBudget
        (D.inverse hD.isUnbounded)
        (fun t : ℕ => (t : ℝ) * H t)) :
    let P := ofRawRate D hD hstrict H hfeasible
    Antitone P.monotonePrefixRate ∧
      Tendsto P.monotonePrefixRate atTop (nhds 0) ∧
      (∀ᶠ t : ℕ in atTop, P.monotonePrefixRate t ≤ H t) ∧
      Tendsto
        (fun t =>
          natRatio
              (P.prefixDeadline.inverse
                P.prefixDeadline_isUnbounded) t /
            P.monotonePrefixRate t)
        atTop (nhds 0) := by
  dsimp only
  let P := ofRawRate D hD hstrict H hfeasible
  have hbudget :
      Tendsto (natRatio P.budget) atTop (nhds 0) := by
    exact ofRawRate_budget_ratio_tendsto_zero
      D hD hstrict H hfeasible hH hvanishing
  exact P.appendixD_monotone_prefix_rate_of_upper
    hbudget H hHanti
    (ofRawRate_prefixRate_eventually_le
      D hD hstrict H hfeasible hH)

end NaturalFeasibleProfile

end GenLimit.TimeSensitive
