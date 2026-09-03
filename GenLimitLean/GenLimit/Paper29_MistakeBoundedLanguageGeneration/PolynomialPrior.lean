import GenLimit.Paper29_MistakeBoundedLanguageGeneration.CountableWeightedRun
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A concrete logarithmic countable-class instantiation

Section 6.1 of Kleinberg--Peale--Reingold instantiates Algorithm 1 with the
one-based prior `w₀(i) = 1 / i²` and the doubling active prefix `f(t)=2ᵗ`.
This module supplies both a robust elementary zero-based instantiation and
the source's exact analytic normalization.

* `polynomialPrior i = 1 / (i+1)²`;
* `doublingActiveCount t = 2ᵗ`;
* every finite prior prefix has mass at most `2`, by a telescoping estimate;
* target `i` is first active at `clog₂(i+1)`;
* a division-free dyadic budget of `2*clog₂(i+1)+1` is valid.

The coarse facts give at most `3*clog₂(i+1)+1` mistakes and remain available
without relying on the sharp constant.  The analytic layer additionally
proves:

* the exact Basel mass `∑ᵢ polynomialPrior i = π²/6`;
* every finite prior prefix is bounded by `π²/6`;
* the exact natural-number budget
  `⌊log₂ ((π²/6) / polynomialPrior i)⌋₊`;
* a source-aligned zero-based schedule `paperDoublingActiveCount t = 2^(t+1)`;
* the paper's displayed real bound
  `3 log₂(i+1) + log₂(π²/6)`.

The source proof writes an equality when it drops
`⌊log₂ i⌋` to `log₂ i`.  That line is only an inequality unless `i` is a
power of two.  The theorem itself is valid; the formal proof uses the
correct inequality.
-/

namespace GenLimit.MistakeBounded

open scoped BigOperators

/-- Zero-based form of the paper's polynomial prior `1 / i²`. -/
noncomputable def polynomialPrior (i : ℕ) : ℝ :=
  1 / ((i + 1 : ℕ) : ℝ) ^ 2

/-- Zero-based doubling schedule. -/
def doublingActiveCount (t : ℕ) : ℕ :=
  2 ^ t

/-- Source-aligned zero-based schedule.

The paper numbers rounds from one and uses `f(t)=2ᵗ`.  Lean rounds start at
zero, so source round `t+1` has active count `2^(t+1)`. -/
def paperDoublingActiveCount (t : ℕ) : ℕ :=
  2 ^ (t + 1)

theorem polynomialPrior_pos (i : ℕ) :
    0 < polynomialPrior i := by
  simp only [polynomialPrior]
  positivity

theorem polynomialPrior_nonnegative (i : ℕ) :
    0 ≤ polynomialPrior i :=
  le_of_lt (polynomialPrior_pos i)

/-- The zero-based polynomial prior is exactly the positive part of the
Basel series.  Mathlib's `hasSum_zeta_two` includes the zero term, which is
zero; shifting that series by one gives the paper's prior. -/
theorem polynomialPrior_hasSum :
    HasSum polynomialPrior (Real.pi ^ 2 / 6) := by
  change
    HasSum (fun i : ℕ => 1 / ((i + 1 : ℕ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 6)
  simpa [Nat.cast_add, Nat.cast_one] using
    ((hasSum_nat_add_iff' 1).mpr hasSum_zeta_two)

/-- Exact total mass of the polynomial prior. -/
theorem polynomialPrior_tsum :
    ∑' i : ℕ, polynomialPrior i = Real.pi ^ 2 / 6 :=
  polynomialPrior_hasSum.tsum_eq

/-- The elementary comparison
`1/(n+1)² ≤ 1/n - 1/(n+1)` for `n ≥ 1`. -/
theorem polynomialPrior_le_telescope
    (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤
      1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
  have hnReal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnOneReal : (0 : ℝ) < n + 1 := by positivity
  have hden :
      (n : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith
  have hcompare :
      (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤
        1 / ((n : ℝ) * ((n : ℝ) + 1)) :=
    one_div_le_one_div_of_le (mul_pos hnReal hnOneReal) hden
  have htelescope :
      (1 : ℝ) / (n : ℝ) - 1 / ((n : ℝ) + 1) =
        1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    field_simp
    ring
  have hresult :
      (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤
        1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
    rw [htelescope]
    exact hcompare
  simpa only [Nat.cast_add, Nat.cast_one] using hresult

/-- Telescoping prefix estimate:
the first `n+1` prior weights sum to at most `2 - 1/(n+1)`. -/
theorem polynomialPrior_prefix_succ_le (n : ℕ) :
    initialPrefixWeight polynomialPrior (n + 1) ≤
      2 - 1 / ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero =>
      norm_num [initialPrefixWeight, polynomialPrior]
  | succ n ih =>
      rw [initialPrefixWeight] at ih ⊢
      rw [Finset.sum_range_succ]
      have htel :=
        polynomialPrior_le_telescope (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      have htel' :
          polynomialPrior (n + 1) ≤
            1 / ((n : ℝ) + 1) -
              1 / (((n : ℝ) + 1) + 1) := by
        simpa [polynomialPrior, Nat.cast_add, Nat.cast_one] using htel
      norm_num [Nat.cast_add, Nat.cast_one] at ih htel' ⊢
      linarith

/-- Every finite prefix of the polynomial prior has total mass at most `2`.
The looser constant avoids any dependence on Euler's Basel-series identity. -/
theorem polynomialPrior_prefix_le_two (n : ℕ) :
    initialPrefixWeight polynomialPrior n ≤ 2 := by
  cases n with
  | zero => simp [initialPrefixWeight]
  | succ n =>
      have h := polynomialPrior_prefix_succ_le n
      have hnonnegative :
          (0 : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
      linarith

/-- Every finite polynomial-prior prefix is bounded by the exact Basel
mass `π²/6`. -/
theorem polynomialPrior_prefix_le_basel (n : ℕ) :
    initialPrefixWeight polynomialPrior n ≤ Real.pi ^ 2 / 6 := by
  rw [initialPrefixWeight, ← polynomialPrior_tsum]
  exact polynomialPrior_hasSum.summable.sum_le_tsum
    (Finset.range n) (fun i _hi => polynomialPrior_nonnegative i)

/-- The Basel mass is strictly below the elementary bound `2`. -/
theorem baselMass_lt_two :
    Real.pi ^ 2 / 6 < (2 : ℝ) := by
  have hpi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hpi_nonnegative : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  nlinarith

theorem doublingActiveCount_monotone :
    Monotone doublingActiveCount := by
  intro s t hst
  exact Nat.pow_le_pow_right (by omega) hst

/-- Under the doubling schedule, target `i` first appears at
`clog₂(i+1)`. -/
theorem doublingActiveCount_firstActivated (target : ℕ) :
    FirstActivated doublingActiveCount target
      (Nat.clog 2 (target + 1)) := by
  constructor
  · have hle :
        target + 1 ≤ 2 ^ Nat.clog 2 (target + 1) :=
      Nat.le_pow_clog (by omega) (target + 1)
    simpa [doublingActiveCount] using hle
  · intro t ht
    have hpow :
        2 ^ t < target + 1 :=
      (Nat.lt_clog_iff_pow_lt (by omega)).mp ht
    change 2 ^ t ≤ target
    omega

theorem paperDoublingActiveCount_monotone :
    Monotone paperDoublingActiveCount := by
  intro s t hst
  exact Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hst 1)

/-- Under the source-aligned schedule, the first active zero-based round is
`(clog₂(target+1)).pred`. -/
theorem paperDoublingActiveCount_firstActivated (target : ℕ) :
    FirstActivated paperDoublingActiveCount target
      (Nat.clog 2 (target + 1)).pred := by
  constructor
  · change
      target <
        2 ^ ((Nat.clog 2 (target + 1)).pred + 1)
    by_cases htarget : target = 0
    · subst target
      norm_num
    · have hkpos :
          0 < Nat.clog 2 (target + 1) :=
        Nat.clog_pos (by omega) (by omega)
      have hcancel :
          (Nat.clog 2 (target + 1)).pred + 1 =
            Nat.clog 2 (target + 1) := by
        simpa [Nat.succ_eq_add_one] using
          (Nat.succ_pred_eq_of_pos hkpos)
      rw [hcancel]
      have hle :
          target + 1 ≤ 2 ^ Nat.clog 2 (target + 1) :=
        Nat.le_pow_clog (by omega) (target + 1)
      omega
  · intro t ht
    change 2 ^ (t + 1) ≤ target
    have hkne : Nat.clog 2 (target + 1) ≠ 0 := by
      intro hk
      simp [hk] at ht
    have hlog :
        t + 1 < Nat.clog 2 (target + 1) := by
      exact
        (Nat.succ_le_iff.mpr ht).trans_lt
          (Nat.pred_lt hkne)
    have hpow :
        2 ^ (t + 1) < target + 1 :=
      (Nat.lt_clog_iff_pow_lt (by omega)).mp hlog
    omega

/-- The number of pre-activation rounds in the source-aligned schedule is
at most the integer base-two logarithm. -/
theorem paperDoublingActivation_le_log (target : ℕ) :
    (Nat.clog 2 (target + 1)).pred ≤
      Nat.log 2 (target + 1) := by
  by_cases htarget : target = 0
  · subst target
    norm_num
  · apply Nat.le_log_of_pow_le (by omega)
    exact
      (Nat.pow_pred_clog_lt_self (by omega)
        (show 1 < target + 1 by omega)).le

/-- The coarse dyadic budget used for the polynomial prior. -/
def polynomialDyadicBudget (target : ℕ) : ℕ :=
  2 * Nat.clog 2 (target + 1) + 1

/-- With total prior bound `2`, the coarse polynomial budget is valid. -/
theorem polynomialPrior_dyadicBudget (target : ℕ) :
    DyadicUpperBudget 2 (polynomialPrior target)
      (polynomialDyadicBudget target) := by
  let n := target + 1
  let k := Nat.clog 2 n
  have hnpos : 0 < n := by
    simp [n]
  have hnle : n ≤ 2 ^ k := by
    exact Nat.le_pow_clog (by omega) n
  have hsquares : n ^ 2 ≤ (2 ^ k) ^ 2 :=
    Nat.pow_le_pow_left hnle 2
  have hpowpos : 0 < (2 ^ k) ^ 2 := by positivity
  have hexponent :
      2 ^ (2 * k + 2) = 4 * (2 ^ k) ^ 2 := by
    calc
      2 ^ (2 * k + 2) = 2 ^ (k * 2 + 2) := by
        congr 1
        omega
      _ = 2 ^ (k * 2) * 2 ^ 2 := by rw [pow_add]
      _ = (2 ^ k) ^ 2 * 2 ^ 2 := by rw [pow_mul]
      _ = 4 * (2 ^ k) ^ 2 := by ring
  have hnat :
      2 * n ^ 2 < 2 ^ (2 * k + 2) := by
    calc
      2 * n ^ 2 ≤ 2 * (2 ^ k) ^ 2 :=
        Nat.mul_le_mul_left 2 hsquares
      _ < 4 * (2 ^ k) ^ 2 := by nlinarith
      _ = 2 ^ (2 * k + 2) := hexponent.symm
  have hreal :
      (2 : ℝ) * (n : ℝ) ^ 2 <
        (2 : ℝ) ^ (2 * k + 2) := by
    exact_mod_cast hnat
  rw [DyadicUpperBudget, polynomialPrior, polynomialDyadicBudget]
  change
    (2 : ℝ) <
      (2 : ℝ) ^ (2 * Nat.clog 2 (target + 1) + 1 + 1) *
        (1 / ((target + 1 : ℕ) : ℝ) ^ 2)
  rw [mul_one_div]
  apply (lt_div_iff₀ (by positivity :
    (0 : ℝ) < ((target + 1 : ℕ) : ℝ) ^ 2)).mpr
  simpa [n, k, Nat.add_assoc] using hreal

/-- Using the exact Basel mass removes the extra one from the elementary
dyadic budget. -/
theorem polynomialPrior_basel_dyadicBudget (target : ℕ) :
    DyadicUpperBudget (Real.pi ^ 2 / 6) (polynomialPrior target)
      (2 * Nat.clog 2 (target + 1)) := by
  let n := target + 1
  let k := Nat.clog 2 n
  have hnle : n ≤ 2 ^ k := by
    exact Nat.le_pow_clog (by omega) n
  have hsquares : n ^ 2 ≤ (2 ^ k) ^ 2 :=
    Nat.pow_le_pow_left hnle 2
  have hsquaresReal :
      (n : ℝ) ^ 2 ≤ ((2 ^ k : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hsquares
  have hnRealPos : (0 : ℝ) < n := by positivity
  have hproduct :
      (Real.pi ^ 2 / 6) * (n : ℝ) ^ 2 <
        (2 : ℝ) * ((2 ^ k : ℕ) : ℝ) ^ 2 := by
    calc
      (Real.pi ^ 2 / 6) * (n : ℝ) ^ 2 <
          2 * (n : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right baselMass_lt_two
          (sq_pos_of_pos hnRealPos)
      _ ≤ 2 * ((2 ^ k : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquaresReal (by norm_num)
  have hexponent :
      (2 : ℝ) ^ (2 * k + 1) =
        2 * ((2 ^ k : ℕ) : ℝ) ^ 2 := by
    calc
      (2 : ℝ) ^ (2 * k + 1) =
          (2 : ℝ) ^ (k * 2) * 2 := by
        rw [show 2 * k + 1 = k * 2 + 1 by omega, pow_add]
        norm_num
      _ = ((2 : ℝ) ^ k) ^ 2 * 2 := by rw [pow_mul]
      _ = 2 * ((2 ^ k : ℕ) : ℝ) ^ 2 := by
        norm_num
        ring
  rw [DyadicUpperBudget, polynomialPrior]
  change
    Real.pi ^ 2 / 6 <
      (2 : ℝ) ^ (2 * Nat.clog 2 (target + 1) + 1) *
        (1 / ((target + 1 : ℕ) : ℝ) ^ 2)
  rw [mul_one_div]
  apply (lt_div_iff₀ (by positivity :
    (0 : ℝ) < ((target + 1 : ℕ) : ℝ) ^ 2)).mpr
  simpa [n, k, hexponent] using hproduct

/-- The source's exact post-activation natural-number budget:
`⌊log₂ ((π²/6) / w₀(i))⌋₊`. -/
noncomputable def polynomialPriorLogBudget (target : ℕ) : ℕ :=
  ⌊Real.logb 2
    ((Real.pi ^ 2 / 6) / polynomialPrior target)⌋₊

/-- The exact floor-log budget satisfies the division-free condition used
by the concrete Theorem 4.1. -/
theorem polynomialPrior_logBudget_valid (target : ℕ) :
    DyadicUpperBudget (Real.pi ^ 2 / 6) (polynomialPrior target)
      (polynomialPriorLogBudget target) := by
  have hweight : 0 < polynomialPrior target :=
    polynomialPrior_pos target
  have htotal : 0 < Real.pi ^ 2 / 6 := by positivity
  have hratio :
      0 < (Real.pi ^ 2 / 6) / polynomialPrior target :=
    div_pos htotal hweight
  have hlog :
      Real.logb 2
          ((Real.pi ^ 2 / 6) / polynomialPrior target) <
        (polynomialPriorLogBudget target : ℝ) + 1 := by
    simpa [polynomialPriorLogBudget] using
      (Nat.lt_floor_add_one
        (Real.logb 2
          ((Real.pi ^ 2 / 6) / polynomialPrior target)))
  have hratioPow :
      (Real.pi ^ 2 / 6) / polynomialPrior target <
        (2 : ℝ) ^ (polynomialPriorLogBudget target + 1) := by
    have hratioRpow :
        (Real.pi ^ 2 / 6) / polynomialPrior target <
          (2 : ℝ) ^
            (((polynomialPriorLogBudget target : ℕ) + 1 : ℕ) : ℝ) := by
      exact
        (Real.logb_lt_iff_lt_rpow
          (by norm_num : (1 : ℝ) < 2) hratio).mp (by
            simpa [Nat.cast_add, Nat.cast_one] using hlog)
    simpa only [Real.rpow_natCast] using hratioRpow
  rw [DyadicUpperBudget]
  exact (div_lt_iff₀ hweight).mp hratioPow

/-- Concrete semantic `O(log i)` mistake theorem for Section 6.1.

For zero-based target `target`, Algorithm 1 with the polynomial prior and
doubling active prefix makes at most
`3 * clog₂(target+1) + 1` mistakes on every injective target-consistent
presentation. -/
theorem theorem_6_1_coarse_concrete_semantic_algorithm
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hObserved : ∀ t, observed t ∈ language target) :
    TotalMistakesAtMost
      (countableTargetTrace language
        (countableSemanticGenerated doublingActiveCount polynomialPrior
          language observed)
        target)
      (3 * Nat.clog 2 (target + 1) + 1) := by
  have h :=
    theorem_4_1_corrected_concrete_semantic_algorithm
      doublingActiveCount polynomialPrior language observed
      doublingActiveCount_monotone
      polynomialPrior_nonnegative
      hInjective
      polynomialPrior_prefix_le_two
      target
      (Nat.clog 2 (target + 1))
      (polynomialDyadicBudget target)
      (doublingActiveCount_firstActivated target)
      hObserved
      (polynomialPrior_pos target)
      (polynomialPrior_dyadicBudget target)
  have hbound :
      Nat.clog 2 (target + 1) + polynomialDyadicBudget target =
        3 * Nat.clog 2 (target + 1) + 1 := by
    simp [polynomialDyadicBudget]
    omega
  rwa [← hbound]

/-- The exact Basel mass sharpens the robust zero-based theorem by one
mistake, while retaining the original `2ᵗ` schedule. -/
theorem theorem_6_1_basel_concrete_semantic_algorithm
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hObserved : ∀ t, observed t ∈ language target) :
    TotalMistakesAtMost
      (countableTargetTrace language
        (countableSemanticGenerated doublingActiveCount polynomialPrior
          language observed)
        target)
      (3 * Nat.clog 2 (target + 1)) := by
  have h :=
    theorem_4_1_corrected_concrete_semantic_algorithm
      doublingActiveCount polynomialPrior language observed
      doublingActiveCount_monotone
      polynomialPrior_nonnegative
      hInjective
      polynomialPrior_prefix_le_basel
      target
      (Nat.clog 2 (target + 1))
      (2 * Nat.clog 2 (target + 1))
      (doublingActiveCount_firstActivated target)
      hObserved
      (polynomialPrior_pos target)
      (polynomialPrior_basel_dyadicBudget target)
  have hbound :
      Nat.clog 2 (target + 1) +
          2 * Nat.clog 2 (target + 1) =
        3 * Nat.clog 2 (target + 1) := by omega
  rwa [← hbound]

/-- Exact integer-valued Theorem 6.1 instantiation.

The first summand is the actual number of zero-based rounds before the
paper's `2ᵗ` schedule activates the one-based language `target+1`; the
second is exactly the floor-log budget printed in Theorem 4.1. -/
theorem theorem_6_1_logFloor_concrete_semantic_algorithm
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hObserved : ∀ t, observed t ∈ language target) :
    TotalMistakesAtMost
      (countableTargetTrace language
        (countableSemanticGenerated paperDoublingActiveCount
          polynomialPrior language observed)
        target)
      ((Nat.clog 2 (target + 1)).pred +
        polynomialPriorLogBudget target) := by
  exact
    theorem_4_1_corrected_concrete_semantic_algorithm
      paperDoublingActiveCount polynomialPrior language observed
      paperDoublingActiveCount_monotone
      polynomialPrior_nonnegative
      hInjective
      polynomialPrior_prefix_le_basel
      target
      (Nat.clog 2 (target + 1)).pred
      (polynomialPriorLogBudget target)
      (paperDoublingActiveCount_firstActivated target)
      hObserved
      (polynomialPrior_pos target)
      (polynomialPrior_logBudget_valid target)

/-- The exact floor-log budget is at most the real expression used in the
last arithmetic step of the source proof. -/
theorem polynomialPrior_logBudget_cast_le (target : ℕ) :
    (polynomialPriorLogBudget target : ℝ) ≤
      Real.logb 2 (Real.pi ^ 2 / 6) +
        2 * Real.logb 2 (target + 1) := by
  let n := target + 1
  let W : ℝ := Real.pi ^ 2 / 6
  have hnpos : (0 : ℝ) < n := by positivity
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ target + 1 by omega)
  have hWpos : 0 < W := by
    dsimp [W]
    positivity
  have hWone : (1 : ℝ) < W := by
    dsimp [W]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hpi_nonnegative : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    nlinarith
  have hratioEq :
      W / polynomialPrior target = W * (n : ℝ) ^ 2 := by
    simp [W, n, polynomialPrior, div_eq_mul_inv]
  have hratioOne :
      (1 : ℝ) ≤ W / polynomialPrior target := by
    rw [hratioEq]
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hlogNonnegative :
      0 ≤ Real.logb 2 (W / polynomialPrior target) :=
    Real.logb_nonneg (by norm_num) hratioOne
  have hfloor :
      (polynomialPriorLogBudget target : ℝ) ≤
        Real.logb 2 (W / polynomialPrior target) := by
    simpa [polynomialPriorLogBudget, W] using
      (Nat.floor_le hlogNonnegative)
  have hlogEq :
      Real.logb 2 (W / polynomialPrior target) =
        Real.logb 2 W + 2 * Real.logb 2 n := by
    rw [hratioEq, Real.logb_mul hWpos.ne'
      (pow_ne_zero 2 hnpos.ne'), Real.logb_pow]
    norm_num
  rw [hlogEq] at hfloor
  simpa [W, n] using hfloor

/-- The displayed real-valued bound in Theorem 6.1, with the paper's
one-based language index represented as `target+1`.

Because `mistakeCount` is natural-valued, the statement casts it to `ℝ`.
The source's erroneous equality
`⌊log₂ i⌋ + x = log₂ i + x` is replaced here by the valid inequality
`⌊log₂ i⌋ ≤ log₂ i`. -/
theorem theorem_6_1_displayed_real_bound_concrete_semantic_algorithm
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hObserved : ∀ t, observed t ∈ language target) :
    ∀ t,
      (mistakeCount
          (countableTargetTrace language
            (countableSemanticGenerated paperDoublingActiveCount
              polynomialPrior language observed)
            target)
          t : ℝ) ≤
        3 * Real.logb 2 (target + 1) +
          Real.logb 2 (Real.pi ^ 2 / 6) := by
  intro t
  have hNatural :=
    theorem_6_1_logFloor_concrete_semantic_algorithm
      language observed hInjective target hObserved
  have hActivation :
      ((Nat.clog 2 (target + 1)).pred : ℝ) ≤
        Real.logb 2 (target + 1) := by
    have hCast :
        ((Nat.clog 2 (target + 1)).pred : ℝ) ≤
          (Nat.log 2 (target + 1) : ℝ) := by
      exact_mod_cast paperDoublingActivation_le_log target
    exact hCast.trans (by
      simpa using
        (Real.natLog_le_logb (target + 1) 2))
  have hBudget :=
    polynomialPrior_logBudget_cast_le target
  calc
    (mistakeCount
          (countableTargetTrace language
            (countableSemanticGenerated paperDoublingActiveCount
              polynomialPrior language observed)
            target)
          t : ℝ) ≤
        (((Nat.clog 2 (target + 1)).pred +
          polynomialPriorLogBudget target : ℕ) : ℝ) := by
            exact_mod_cast hNatural t
    _ =
        ((Nat.clog 2 (target + 1)).pred : ℝ) +
          (polynomialPriorLogBudget target : ℝ) := by
            norm_num
    _ ≤
        Real.logb 2 (target + 1) +
          (Real.logb 2 (Real.pi ^ 2 / 6) +
            2 * Real.logb 2 (target + 1)) :=
      add_le_add hActivation hBudget
    _ =
        3 * Real.logb 2 (target + 1) +
          Real.logb 2 (Real.pi ^ 2 / 6) := by ring

end GenLimit.MistakeBounded
