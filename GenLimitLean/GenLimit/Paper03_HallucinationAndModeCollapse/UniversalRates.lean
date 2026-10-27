import GenLimit.Paper03_HallucinationAndModeCollapse.AngluinWitnessRates
import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalNecessity
import GenLimit.Paper03_HallucinationAndModeCollapse.IdentificationLowerBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup

/-!
# The identification-rate dichotomy

The mathematical alternatives of P03 Theorem 3.1. Exponents are nonnegative,
sublinear in the standard little-o sense, and diverge, as required for the
rate in Definition 13 to tend to zero. Upper bounds hold without horizontal
rescaling (the source's admissible choice `c = 1`). Nonmonotone exponents are
allowed. The explicit Angluin construction gives the stronger exponential
upper bound, so no exponent-dependent algorithm or schedule is needed.
-/

namespace GenLimit.HallucinationModeCollapse

noncomputable section

open GenLimit.Generic GenLimit.DiscreteIID Filter Asymptotics
open scoped Topology

/-- An exponent for an admissible vanishing almost-exponential rate. -/
structure AdmissibleSublinearExponent (g : ℕ → ℝ) : Prop where
  nonnegative : ∀ n, 0 ≤ g n
  sublinear : g =o[atTop] (fun n : ℕ => (n : ℝ))
  diverges : Tendsto g atTop atTop

/-- A distribution-independent learner attains this rate with a positive
distribution-dependent prefactor. This fixes the source's horizontal scale
to one, a stronger bound than allowing a distribution-dependent scale. -/
def AchievesIdentificationRate (C : Generic.LanguageFamily ℕ) (A : StatisticalIdentifier)
    (R : ℕ → ℝ) : Prop :=
  ∀ i p, ValidDistribution C i p → ∃ D : ℝ, 0 < D ∧
    ∀ n, identificationError C A p i n ≤ D * R n

def AlmostExponentialIdentifiable (C : Generic.LanguageFamily ℕ) : Prop :=
  ∀ g : ℕ → ℝ, AdmissibleSublinearExponent g →
    ∃ A : GenLimit.Learner ℕ ℕ,
      AchievesIdentificationRate C (deterministicIdentifier A) (fun n => Real.exp (-g n))

/-- Definition 13's no-rate alternative, literally using positive limsup. -/
def NoIdentificationRate (C : Generic.LanguageFamily ℕ) : Prop :=
  ∀ A : StatisticalIdentifier, ∃ i p, ValidDistribution C i p ∧
    0 < limsup (fun n => identificationError C A p i n) atTop

theorem admissible_log_exponent :
    AdmissibleSublinearExponent (fun n : ℕ => Real.log n) := by
  refine ⟨Real.log_natCast_nonneg, ?_, ?_⟩
  · exact Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The admissibility assumptions give precisely a `[0,1]`-valued rate
converging to zero, as required by source Definition 13. -/
theorem AdmissibleSublinearExponent.rate_valid {g : ℕ → ℝ}
    (hg : AdmissibleSublinearExponent g) :
    (∀ n, Real.exp (-g n) ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun n => Real.exp (-g n)) atTop (𝓝 0) := by
  refine ⟨fun n => ⟨(Real.exp_pos _).le, ?_⟩,
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hg.diverges⟩
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg.nonnegative n))

theorem exponential_rate_implies_sublinear_rate
    (C : Generic.LanguageFamily ℕ) (A : StatisticalIdentifier)
    (hA : ExponentialIdentifies C A) (g : ℕ → ℝ) (hg : AdmissibleSublinearExponent g) :
    AchievesIdentificationRate C A (fun n => Real.exp (-g n)) := by
  intro i p hp
  obtain ⟨c, hc, D, hD, hbound⟩ := hA i p hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hg.sublinear.bound hc)
  let M := ∑ n ∈ Finset.range N, g n
  have hM : 0 ≤ M := Finset.sum_nonneg (fun n _ => hg.nonnegative n)
  have hsmall (n : ℕ) (hn : n < N) : g n ≤ M :=
    Finset.single_le_sum (fun k _ => hg.nonnegative k) (Finset.mem_range.mpr hn)
  let D' := (D + 1) * Real.exp M
  have hD' : 0 < D' := mul_pos (by linarith) (Real.exp_pos _)
  have hDD : D ≤ D' := by
    have he : 1 ≤ Real.exp M := Real.one_le_exp hM
    dsimp [D']; nlinarith
  refine ⟨D', hD', fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hgn : g n ≤ c * (n : ℝ) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hg.nonnegative n)] using hN n hn
    exact (hbound n).trans (mul_le_mul hDD (Real.exp_le_exp.mpr (by linarith))
      (Real.exp_nonneg _) (le_of_lt hD'))
  · apply (identificationError_le_one C A p i n).trans
    have he : 1 ≤ Real.exp (M - g n) := Real.one_le_exp (by linarith [hsmall n (Nat.lt_of_not_ge hn)])
    dsimp [D']
    rw [mul_assoc, ← Real.exp_add]
    change 1 ≤ (D + 1) * Real.exp (M - g n)
    nlinarith

theorem identificationError_tendsto_zero_of_rate
    (C : Generic.LanguageFamily ℕ) (A : StatisticalIdentifier) (R : ℕ → ℝ)
    (hA : AchievesIdentificationRate C A R) (hR : Tendsto R atTop (𝓝 0))
    (i : ℕ) (p : PMF ℕ) (hp : ValidDistribution C i p) :
    Tendsto (fun n => identificationError C A p i n) atTop (𝓝 0) := by
  obtain ⟨D, _, hb⟩ := hA i p hp
  apply squeeze_zero (fun _ => probability_nonneg _ _) hb
  simpa using tendsto_const_nhds.mul hR

theorem almostExponentialIdentifiable_iff_conditionTwo (C : Generic.LanguageFamily ℕ) :
    AlmostExponentialIdentifiable C ↔ GenLimit.Angluin.ConditionTwo C := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := h _ admissible_log_exponent
    apply conditionTwo_of_eventual_small_error C (deterministicIdentifier A)
    intro i p hp
    have hR := Real.tendsto_exp_neg_atTop_nhds_zero.comp admissible_log_exponent.diverges
    have he := identificationError_tendsto_zero_of_rate C _ _ hA hR i p hp
    exact he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  · intro h g hg
    obtain ⟨A, hA⟩ := exponentialIdentifies_of_conditionTwo C h
    exact ⟨A, exponential_rate_implies_sublinear_rate C _ hA g hg⟩

/-- Lemma 5.8, in its source-facing limsup form. -/
theorem lemma_5_8 (C : Generic.LanguageFamily ℕ) (hC : ¬GenLimit.Angluin.ConditionTwo C)
    (A : StatisticalIdentifier) :
    ∃ i p, ValidDistribution C i p ∧
      (1 / 2 : ℝ) ≤ limsup (fun n => identificationError C A p i n) atTop := by
  obtain ⟨i, p, hp, hf⟩ := lemma_5_8_frequently C hC A
  refine ⟨i, p, hp, le_limsup_of_frequently_le hf ?_⟩
  exact isBoundedUnder_of ⟨1, identificationError_le_one C A p i⟩

theorem noIdentificationRate_of_not_conditionTwo
    (C : Generic.LanguageFamily ℕ) (hC : ¬GenLimit.Angluin.ConditionTwo C) :
    NoIdentificationRate C := by
  intro A
  obtain ⟨i, p, hp, hl⟩ := lemma_5_8 C hC A
  exact ⟨i, p, hp, lt_of_lt_of_le (by norm_num) hl⟩

theorem not_noIdentificationRate_of_almostExponential
    (C : Generic.LanguageFamily ℕ) (hC : AlmostExponentialIdentifiable C) :
    ¬NoIdentificationRate C := by
  intro hno
  obtain ⟨A, hA⟩ := hC _ admissible_log_exponent
  obtain ⟨i, p, hp, hpos⟩ := hno (deterministicIdentifier A)
  have hR := Real.tendsto_exp_neg_atTop_nhds_zero.comp admissible_log_exponent.diverges
  have he := identificationError_tendsto_zero_of_rate C _ _ hA hR i p hp
  rw [he.limsup_eq] at hpos
  exact lt_irrefl _ hpos

/-- Full mathematical dichotomy of Theorem 3.1. The alternatives are
exclusive; Angluin's condition characterizes the almost-exponential branch;
and every randomized learner has the fixed-distribution exponential lower
bound. Oracle/computable realizations of the positive witness are exposed
separately, rather than identifying semantic functions with programs. -/
theorem theorem_3_1_mathematical (C : Generic.LanguageFamily ℕ) (hC : NontrivialCollection C) :
    ((AlmostExponentialIdentifiable C ∧ ¬NoIdentificationRate C) ∨
      (¬AlmostExponentialIdentifiable C ∧ NoIdentificationRate C)) ∧
      (AlmostExponentialIdentifiable C ↔ GenLimit.Angluin.ConditionTwo C) ∧
      ∀ A : StatisticalIdentifier, ∃ i p, ValidDistribution C i p ∧
        ∃ᶠ n : ℕ in atTop, Real.exp (-2 * (n : ℝ)) ≤ identificationError C A p i n := by
  have hiff := almostExponentialIdentifiable_iff_conditionTwo C
  refine ⟨?_, hiff, lemma_5_1 C hC⟩
  by_cases h : GenLimit.Angluin.ConditionTwo C
  · have hu := hiff.mpr h
    exact Or.inl ⟨hu, not_noIdentificationRate_of_almostExponential C hu⟩
  · exact Or.inr ⟨fun hu => h (hiff.mp hu), noIdentificationRate_of_not_conditionTwo C h⟩

end
end GenLimit.HallucinationModeCollapse
