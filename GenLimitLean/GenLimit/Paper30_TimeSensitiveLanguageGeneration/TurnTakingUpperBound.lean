import GenLimit.Paper30_TimeSensitiveLanguageGeneration.TheoremFour
import GenLimit.Support.TurnTaking.Pairing

/-!
# Kleinberg--Wei turn-taking upper bound

The paper-independent finite pairing theorem now lives in
`GenLimit.Support.TurnTaking.Pairing`; this module preserves its P30-facing
name and supplies the timely-density analytic specialization behind the
optimality sentence cited by P30.  A timely generator-owned prefix is split
into ordinary credits and sparse catch-up exceptions.  Every ordinary credit
has an injective, disjoint adversary-owned partner in the same target prefix.
Consequently at most half the prefix, up to the sparse exception budget, can
be timely generator credit.

The theorem is deliberately phrased as a reusable certificate.  P30's
concrete finite-history instantiation and adaptive exact presentation are in
`OnlineTotalizedGCG`, `AdaptivePresentationExact`, and `AdaptiveUpperBound`.
P39 itself did not formalize that adversary construction.
-/

namespace GenLimit.TimeSensitive

open Filter

/-- Compatibility alias for the shared finite turn-taking pairing theorem. -/
alias turnTaking_finite_upper_bound :=
  GenLimit.TurnTaking.finite_upper_bound

/-- The normalized catch-up budget used by the asymptotic upper bound. -/
noncomputable def catchupRatio (exceptions : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (exceptions i : ℝ) / i

theorem catchupRatio_nonneg (exceptions : ℕ → ℕ) (i : ℕ) :
    0 ≤ catchupRatio exceptions i := by
  unfold catchupRatio
  split <;> positivity

/-- Analytic Kleinberg--Wei upper endpoint: an eventual finite pairing bound
with a vanishing catch-up fraction forces upper timely density at most one
half. -/
theorem upperTimelyDensity_le_half_of_turnTaking
    (S R : ℕ → α) (exceptions : ℕ → ℕ)
    (hfinite : ∀ᶠ i in atTop,
      2 * (timelyElements S R id i).card ≤ i + 2 * exceptions i)
    (hvanishing : Tendsto (catchupRatio exceptions) atTop (nhds 0)) :
    upperTimelyDensity S R id ≤ (1 / 2 : ℝ) := by
  let upper : ℕ → ℝ := fun i =>
    (1 / 2 : ℝ) + catchupRatio exceptions i
  have hupperTendsto : Tendsto upper atTop (nhds (1 / 2 : ℝ)) := by
    simpa [upper] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ))
        atTop (nhds (1 / 2 : ℝ))).add hvanishing
  have hcompare : ∀ᶠ i in atTop,
      timelyDensity S R id i ≤ upper i := by
    filter_upwards [hfinite, eventually_gt_atTop 0] with i hi hiPos
    have hiReal : (0 : ℝ) < i := by exact_mod_cast hiPos
    have hiCast :
        (2 : ℝ) * ((timelyElements S R id i).card : ℝ) ≤
          (i : ℝ) + 2 * (exceptions i : ℝ) := by
      exact_mod_cast hi
    simp only [timelyDensity, Nat.ne_of_gt hiPos, if_false,
      upper, catchupRatio]
    rw [div_le_iff₀ hiReal]
    field_simp
    nlinarith
  unfold upperTimelyDensity
  have hlimsup :
      limsup (timelyDensity S R id) atTop ≤ limsup upper atTop := by
    exact limsup_le_limsup hcompare
      (isCoboundedUnder_le_of_le atTop
        (fun i => timelyDensity_nonneg S R id i))
      hupperTendsto.isBoundedUnder_le
  exact hlimsup.trans_eq hupperTendsto.limsup_eq

end GenLimit.TimeSensitive
