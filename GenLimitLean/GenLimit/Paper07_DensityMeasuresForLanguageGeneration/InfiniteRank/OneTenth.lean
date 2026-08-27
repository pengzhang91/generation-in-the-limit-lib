import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.OneEighth

/-!
# Corrected one-tenth density endgame

Keep the four-way prefix partition and the singleton/good estimates from
Kleinberg--Wei's Theorem 6.12, but weaken the long-bad estimate to
`Long ≤ 4 * Output + error`.  This is the estimate obtained after thinning
long runs by one half and using a first-consumption charge with fibers of
size at most two.  The resulting finite accounting constant is `10`, hence
the ordered lower-density conclusion is `1/10`.

The constant is sharp for these raw inequalities: with zero errors, the
proportions `(Output, Good, Singleton, Long) = (1, 2, 3, 4)` saturate every
constraint.
-/

open Filter
open scoped Topology

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank

/-- A capacity-two charge for retained long-bad positions changes the
long-bad coefficient from two to four.  The unchanged singleton and good
estimates then give the corrected constant ten. -/
theorem theorem_6_12_finite_accounting_one_tenth
    (n o g s b eSingleton eGood eLong : ℕ)
    (hpartition : o + g + s + b = n)
    (hsingleton : 2 * s ≤ o + g + s + eSingleton)
    (hgood : g ≤ 2 * o + eGood)
    (hlong : b ≤ 4 * o + eLong) :
    n ≤ 10 * o + eSingleton + 2 * eGood + eLong := by
  omega

/-- Eventual finite-prefix accounting with the corrected long-bad
coefficient implies asymptotic lower density at least `1/10`. -/
theorem theorem_6_12_one_tenth_of_eventual_counting
    (O G Singleton Long : ℕ → ℕ)
    (eSingleton eGood eLong : ℕ)
    (hpartition : ∀ n, O n + G n + Singleton n + Long n = n)
    (hsingleton : ∀ᶠ n : ℕ in atTop,
      2 * Singleton n ≤ O n + G n + Singleton n + eSingleton)
    (hgood : ∀ᶠ n : ℕ in atTop, G n ≤ 2 * O n + eGood)
    (hlong : ∀ᶠ n : ℕ in atTop, Long n ≤ 4 * O n + eLong) :
    (1 / 10 : ℝ) ≤
      liminf (fun n : ℕ => (O n : ℝ) / (n : ℝ)) atTop := by
  apply lowerDensity_inv_of_eventual_counting O 10
    (eSingleton + 2 * eGood + eLong) (by omega)
  · intro n
    calc
      O n ≤ O n + G n + Singleton n + Long n := by omega
      _ = n := hpartition n
  · filter_upwards [hsingleton, hgood, hlong] with n hs hg hb
    simpa [Nat.add_assoc] using theorem_6_12_finite_accounting_one_tenth
      n (O n) (G n) (Singleton n) (Long n)
      eSingleton eGood eLong
      (hpartition n) hs hg hb

/-- Uniform form of
`theorem_6_12_one_tenth_of_eventual_counting`. -/
theorem theorem_6_12_one_tenth_of_counting
    (O G Singleton Long : ℕ → ℕ)
    (eSingleton eGood eLong : ℕ)
    (hpartition : ∀ n, O n + G n + Singleton n + Long n = n)
    (hsingleton : ∀ n,
      2 * Singleton n ≤ O n + G n + Singleton n + eSingleton)
    (hgood : ∀ n, G n ≤ 2 * O n + eGood)
    (hlong : ∀ n, Long n ≤ 4 * O n + eLong) :
    (1 / 10 : ℝ) ≤
      liminf (fun n : ℕ => (O n : ℝ) / (n : ℝ)) atTop :=
  theorem_6_12_one_tenth_of_eventual_counting
    O G Singleton Long eSingleton eGood eLong hpartition
    (Filter.Eventually.of_forall hsingleton)
    (Filter.Eventually.of_forall hgood)
    (Filter.Eventually.of_forall hlong)

/-- Ordered-language transfer for a direct eventual ten-to-one prefix
estimate. -/
theorem orderedLowerDensity_one_tenth_of_eventual_counting
    (K : OrderedLanguage) (A : Language) (error : ℕ)
    (hcount : ∀ᶠ n : ℕ in atTop,
      n ≤ 10 * K.prefixCount A n + error) :
    (1 / 10 : ℝ) ≤ K.lowerDensity A := by
  have h :=
    lowerDensity_inv_of_eventual_counting
      (K.prefixCount A) 10 error (by omega)
      (K.prefixCount_le A) hcount
  have hratio :
      K.prefixRatio A =
        (fun n : ℕ => (K.prefixCount A n : ℝ) / (n : ℝ)) := by
    funext n
    by_cases hn : n = 0
    · simp [hn, OrderedLanguage.prefixRatio]
    · simp [OrderedLanguage.prefixRatio, hn]
  unfold OrderedLanguage.lowerDensity
  rw [hratio]
  simpa using h

/-- Uniform ordered-language convenience wrapper. -/
theorem orderedLowerDensity_one_tenth_of_uniform_counting
    (K : OrderedLanguage) (A : Language) (error : ℕ)
    (hcount : ∀ n, n ≤ 10 * K.prefixCount A n + error) :
    (1 / 10 : ℝ) ≤ K.lowerDensity A :=
  orderedLowerDensity_one_tenth_of_eventual_counting K A error
    (Filter.Eventually.of_forall hcount)

/-- Direct ordered-language interface for the corrected four-way endgame. -/
theorem orderedLowerDensity_one_tenth_of_eventual_charges
    (K : OrderedLanguage)
    (Output Good Singleton Long : Language)
    (eSingleton eGood eLong : ℕ)
    (hpartition : ∀ n,
      K.prefixCount Output n +
          K.prefixCount Good n +
          K.prefixCount Singleton n +
          K.prefixCount Long n = n)
    (hsingleton : ∀ᶠ n : ℕ in atTop,
      2 * K.prefixCount Singleton n ≤
        K.prefixCount Output n +
          K.prefixCount Good n +
          K.prefixCount Singleton n +
          eSingleton)
    (hgood : ∀ᶠ n : ℕ in atTop,
      K.prefixCount Good n ≤ 2 * K.prefixCount Output n + eGood)
    (hlong : ∀ᶠ n : ℕ in atTop,
      K.prefixCount Long n ≤ 4 * K.prefixCount Output n + eLong) :
    (1 / 10 : ℝ) ≤ K.lowerDensity Output := by
  have h :=
    theorem_6_12_one_tenth_of_eventual_counting
      (K.prefixCount Output)
      (K.prefixCount Good)
      (K.prefixCount Singleton)
      (K.prefixCount Long)
      eSingleton eGood eLong
      hpartition hsingleton hgood hlong
  have hratio :
      K.prefixRatio Output =
        (fun n : ℕ => (K.prefixCount Output n : ℝ) / (n : ℝ)) := by
    funext n
    by_cases hn : n = 0
    · simp [hn, OrderedLanguage.prefixRatio]
    · simp [OrderedLanguage.prefixRatio, hn]
  unfold OrderedLanguage.lowerDensity
  rw [hratio]
  exact h

end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
