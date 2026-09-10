import GenLimit.Paper30_TimeSensitiveLanguageGeneration.FeasibleProfileDiagonal

/-!
# Appendix-D monotone prefix-rate envelope

The natural geometric-mean rate in `FeasibleProfileDiagonal` has all of the
source's asymptotic inequalities, but it need not itself be nonincreasing.
Definition 2 asks hallucination rates to be nonincreasing.  This file takes
the supremum over every future tail.  For a nonnegative sequence converging
to zero, that tail supremum is nonincreasing, still converges to zero, and
dominates the original rate.

The last property is in the correct direction for feasibility:
enlarging the rate can only decrease
`(D_pfx⁻¹(t)/t) / H_pfx(t)`.  If the original element-wise rate is
nonincreasing and eventually bounds the raw prefix rate, it also bounds the
whole tail envelope.
-/

namespace GenLimit.TimeSensitive

open Filter

namespace NaturalFeasibleProfile

/-- Nonincreasing tail-supremum envelope of the raw prefix rate. -/
noncomputable def monotonePrefixRate
    (P : NaturalFeasibleProfile)
    (t : ℕ) : ℝ :=
  ⨆ u : Set.Ici t, P.prefixRate u.1

theorem prefixRate_bddAbove
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0)) :
    BddAbove (Set.range P.prefixRate) :=
  (P.prefixRate_tendsto_zero hvanishing).bddAbove_range

theorem monotonePrefixRate_tail_bddAbove
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0))
    (t : ℕ) :
    BddAbove
      (Set.range (fun u : Set.Ici t => P.prefixRate u.1)) := by
  obtain ⟨C, hC⟩ := P.prefixRate_bddAbove hvanishing
  refine ⟨C, ?_⟩
  rintro y ⟨u, rfl⟩
  exact hC ⟨u.1, rfl⟩

theorem prefixRate_le_monotonePrefixRate
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0))
    (t : ℕ) :
    P.prefixRate t ≤ P.monotonePrefixRate t := by
  exact le_ciSup
    (P.monotonePrefixRate_tail_bddAbove hvanishing t)
    ⟨t, Set.mem_Ici.mpr le_rfl⟩

theorem monotonePrefixRate_nonneg
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0))
    (t : ℕ) :
    0 ≤ P.monotonePrefixRate t :=
  (P.prefixRate_nonneg t).trans
    (P.prefixRate_le_monotonePrefixRate hvanishing t)

theorem monotonePrefixRate_antitone
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0)) :
    Antitone P.monotonePrefixRate := by
  intro s t hst
  apply ciSup_le
  intro u
  exact le_ciSup
    (P.monotonePrefixRate_tail_bddAbove hvanishing s)
    ⟨u.1, hst.trans u.2⟩

theorem monotonePrefixRate_tendsto_zero
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0)) :
    Tendsto P.monotonePrefixRate atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1
      (P.prefixRate_tendsto_zero hvanishing)) (ε / 2) hhalf
  refine ⟨N, ?_⟩
  intro t ht
  have hsup :
      P.monotonePrefixRate t ≤ ε / 2 := by
    apply ciSup_le
    intro u
    have hu := hN u.1 (ht.trans u.2)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (P.prefixRate_nonneg u.1)] at hu
    exact hu.le
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (P.monotonePrefixRate_nonneg hvanishing t)]
  linarith

theorem prefixRate_eventually_pos
    (P : NaturalFeasibleProfile) :
    ∀ᶠ t : ℕ in atTop, 0 < P.prefixRate t := by
  filter_upwards
    [(tendsto_atTop.1 P.prefixBudget_tendsto_atTop) 1,
      eventually_ge_atTop 1] with t hbudget ht
  have ht0 : t ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_one.trans_le ht)
  have hbudgetPos : 0 < P.prefixBudget t :=
    Nat.zero_lt_one.trans_le hbudget
  simp only [prefixRate, natRatio, ht0, if_false]
  positivity

/-- The inverse/rate little-o estimate survives monotone tail
regularization. -/
theorem prefixInverse_monotoneRate_ratio_tendsto_zero
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0)) :
    Tendsto
      (fun t =>
        natRatio
            (P.prefixDeadline.inverse
              P.prefixDeadline_isUnbounded) t /
          P.monotonePrefixRate t)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t =>
      div_nonneg
        (natRatio_nonneg
          (P.prefixDeadline.inverse
            P.prefixDeadline_isUnbounded) t)
        (P.monotonePrefixRate_nonneg hvanishing t)
  · filter_upwards [P.prefixRate_eventually_pos] with t hrate
    exact div_le_div_of_nonneg_left
      (natRatio_nonneg
        (P.prefixDeadline.inverse
          P.prefixDeadline_isUnbounded) t)
      hrate
      (P.prefixRate_le_monotonePrefixRate hvanishing t)
  · exact P.prefixInverse_rate_ratio_tendsto_zero

/-- A nonincreasing external rate that eventually bounds the raw prefix
rate also eventually bounds its entire tail envelope. -/
theorem monotonePrefixRate_eventually_le
    (P : NaturalFeasibleProfile)
    (H : ℕ → ℝ)
    (hH : Antitone H)
    (hbound :
      ∀ᶠ t : ℕ in atTop, P.prefixRate t ≤ H t) :
    ∀ᶠ t : ℕ in atTop, P.monotonePrefixRate t ≤ H t := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 hbound
  filter_upwards [eventually_ge_atTop T] with t ht
  apply ciSup_le
  intro u
  exact (hT u.1 (ht.trans u.2)).trans (hH u.2)

/-- Appendix-D's rate conclusions after enforcing the literal
nonincreasing-rate convention from Definition 2. -/
theorem appendixD_monotone_prefix_rate_estimates
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0)) :
    Antitone P.monotonePrefixRate ∧
      Tendsto P.monotonePrefixRate atTop (nhds 0) ∧
      Tendsto
        (fun t =>
          natRatio
              (P.prefixDeadline.inverse
                P.prefixDeadline_isUnbounded) t /
            P.monotonePrefixRate t)
        atTop (nhds 0) := by
  exact ⟨P.monotonePrefixRate_antitone hvanishing,
    P.monotonePrefixRate_tendsto_zero hvanishing,
    P.prefixInverse_monotoneRate_ratio_tendsto_zero hvanishing⟩

/-- Source-facing Lemma-8 package relative to an external nonincreasing
element-wise rate `H`. -/
theorem appendixD_monotone_prefix_rate_of_upper
    (P : NaturalFeasibleProfile)
    (hvanishing :
      Tendsto (natRatio P.budget) atTop (nhds 0))
    (H : ℕ → ℝ)
    (hH : Antitone H)
    (hbound :
      ∀ᶠ t : ℕ in atTop, P.prefixRate t ≤ H t) :
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
  exact ⟨P.monotonePrefixRate_antitone hvanishing,
    P.monotonePrefixRate_tendsto_zero hvanishing,
    P.monotonePrefixRate_eventually_le H hH hbound,
    P.prefixInverse_monotoneRate_ratio_tendsto_zero hvanishing⟩

end NaturalFeasibleProfile

end GenLimit.TimeSensitive
