import GenLimit.Core.OrderedDensity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Theorem 6.12: verified one-eighth counting core

This file isolates the part of Kleinberg--Wei's infinite-rank proof which is
independent of the dynamic forest/queue argument.

For a target prefix, split its positions into:

* `o`: positions already output by the generator;
* `g`: good missing positions;
* `s`: singleton bad-run positions;
* `b`: positions in bad runs of length at least two.

The paper's two charging maps and elementary run counting are exactly the
three inequalities below.  The resulting factor `8` is pure Presburger
arithmetic.  A second theorem transfers the uniform finite-prefix estimate to
ordered lower density.

No finite-rank parameter and no conclusion of Claim 6.11 occurs here.
-/

open Filter
open scoped Topology

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank

/-- The exact finite-prefix accounting lemma behind the constant `1/8`.

The error terms permit removal of a finite initial prefix and the one boundary
position which can arise when a run is cut by the end of a prefix.
-/
theorem theorem_6_12_finite_accounting
    (n o g s b eSingleton eGood eLong : ℕ)
    (hpartition : o + g + s + b = n)
    (hsingleton : 2 * s ≤ o + g + s + eSingleton)
    (hgood : g ≤ 2 * o + eGood)
    (hlong : b ≤ 2 * o + eLong) :
    n ≤ 8 * o + eSingleton + 2 * eGood + eLong := by
  omega

/-- A map with fibers of size at most two gives the cardinal inequality used
for the paper's good-missing-string charge. -/
theorem card_le_two_mul_of_fibers
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (source : Finset α) (target : Finset β) (charge : α → β)
    (hmaps : ∀ x ∈ source, charge x ∈ target)
    (hfiber : ∀ y ∈ target,
      ((source.filter fun x => charge x = y).card) ≤ 2) :
    source.card ≤ 2 * target.card :=
  Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfiber

/-- An injective charge into output positions gives the second cardinal
inequality used for retained positions of long bad runs. -/
theorem card_le_of_injective_charge
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (source : Finset α) (target : Finset β) (charge : α → β)
    (hmaps : Set.MapsTo charge source target)
    (hinj : Set.InjOn charge source) :
    source.card ≤ target.card :=
  Finset.card_le_card_of_injOn charge hmaps hinj

/-- A generic analytic transfer: an eventual estimate
`n ≤ q * D n + error` forces lower density at least `1/q`.

The upper bound on `D` supplies the boundedness hypothesis required by the
`liminf` comparison theorem.
-/
theorem lowerDensity_inv_of_eventual_counting
    (D : ℕ → ℕ) (q error : ℕ) (hq : 0 < q)
    (hD : ∀ n, D n ≤ n)
    (hcount : ∀ᶠ n : ℕ in atTop, n ≤ q * D n + error) :
    (1 / (q : ℝ)) ≤
      liminf (fun n : ℕ => (D n : ℝ) / (n : ℝ)) atTop := by
  let lower : ℕ → ℝ := fun n =>
    (1 / (q : ℝ)) - (error : ℝ) / ((q : ℝ) * (n : ℝ))
  have herror :
      Tendsto
        (fun n : ℕ => (error : ℝ) / ((q : ℝ) * (n : ℝ)))
        atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun n : ℕ => (error : ℝ) / (n : ℝ))
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hdiv := hbase.div_const (q : ℝ)
    simpa [div_div, mul_comm] using hdiv
  have hlower : Tendsto lower atTop (𝓝 (1 / (q : ℝ))) := by
    simpa only [lower, sub_zero] using tendsto_const_nhds.sub herror
  have hcompare : ∀ᶠ n : ℕ in atTop,
      lower n ≤ (D n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0, hcount] with n hn hcountn
    have hnR : (0 : ℝ) < n := by
      exact_mod_cast hn
    have hqR : (0 : ℝ) < q := by
      exact_mod_cast hq
    have hcountR :
        (n : ℝ) ≤ (q : ℝ) * (D n : ℝ) + (error : ℝ) := by
      exact_mod_cast hcountn
    dsimp only [lower]
    rw [le_div_iff₀ hnR]
    field_simp [hqR.ne', hnR.ne']
    nlinarith
  have hratio_le_one :
      ∀ n, (D n : ℝ) / (n : ℝ) ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · have hnR : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnR]
      exact_mod_cast hD n
  calc
    (1 / (q : ℝ)) = liminf lower atTop := hlower.liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => (D n : ℝ) / (n : ℝ)) atTop :=
      liminf_le_liminf hcompare hlower.isBoundedUnder_ge
        (isCoboundedUnder_ge_of_le atTop hratio_le_one)

/-- Uniform-counting convenience wrapper for
`lowerDensity_inv_of_eventual_counting`. -/
theorem lowerDensity_inv_of_uniform_counting
    (D : ℕ → ℕ) (q error : ℕ) (hq : 0 < q)
    (hD : ∀ n, D n ≤ n)
    (hcount : ∀ n, n ≤ q * D n + error) :
    (1 / (q : ℝ)) ≤
      liminf (fun n : ℕ => (D n : ℝ) / (n : ℝ)) atTop :=
  lowerDensity_inv_of_eventual_counting D q error hq hD
    (Filter.Eventually.of_forall hcount)

/-- The paper-faithful asymptotic `1/8` conclusion from an exact four-way
prefix partition and three charging inequalities which hold after a finite
initial segment. -/
theorem theorem_6_12_one_eighth_of_eventual_counting
    (O G Singleton Long : ℕ → ℕ)
    (eSingleton eGood eLong : ℕ)
    (hpartition : ∀ n, O n + G n + Singleton n + Long n = n)
    (hsingleton : ∀ᶠ n : ℕ in atTop,
      2 * Singleton n ≤ O n + G n + Singleton n + eSingleton)
    (hgood : ∀ᶠ n : ℕ in atTop, G n ≤ 2 * O n + eGood)
    (hlong : ∀ᶠ n : ℕ in atTop, Long n ≤ 2 * O n + eLong) :
    (1 / 8 : ℝ) ≤
      liminf (fun n : ℕ => (O n : ℝ) / (n : ℝ)) atTop := by
  apply lowerDensity_inv_of_eventual_counting O 8
    (eSingleton + 2 * eGood + eLong) (by omega)
  · intro n
    calc
      O n ≤ O n + G n + Singleton n + Long n := by omega
      _ = n := hpartition n
  · filter_upwards [hsingleton, hgood, hlong] with n hs hg hb
    simpa [Nat.add_assoc] using theorem_6_12_finite_accounting
      n (O n) (G n) (Singleton n) (Long n)
      eSingleton eGood eLong
      (hpartition n) hs hg hb

/-- Uniform form of `theorem_6_12_one_eighth_of_eventual_counting`. -/
theorem theorem_6_12_one_eighth_of_counting
    (O G Singleton Long : ℕ → ℕ)
    (eSingleton eGood eLong : ℕ)
    (hpartition : ∀ n, O n + G n + Singleton n + Long n = n)
    (hsingleton : ∀ n,
      2 * Singleton n ≤ O n + G n + Singleton n + eSingleton)
    (hgood : ∀ n, G n ≤ 2 * O n + eGood)
    (hlong : ∀ n, Long n ≤ 2 * O n + eLong) :
    (1 / 8 : ℝ) ≤
      liminf (fun n : ℕ => (O n : ℝ) / (n : ℝ)) atTop :=
  theorem_6_12_one_eighth_of_eventual_counting
    O G Singleton Long eSingleton eGood eLong hpartition
    (Filter.Eventually.of_forall hsingleton)
    (Filter.Eventually.of_forall hgood)
    (Filter.Eventually.of_forall hlong)

/-- Ordered-language form of the generic eventual finite-prefix transfer. -/
theorem orderedLowerDensity_one_eighth_of_eventual_counting
    (K : OrderedLanguage) (A : Language) (error : ℕ)
    (hcount : ∀ᶠ n : ℕ in atTop,
      n ≤ 8 * K.prefixCount A n + error) :
    (1 / 8 : ℝ) ≤ K.lowerDensity A := by
  have h :=
    lowerDensity_inv_of_eventual_counting
      (K.prefixCount A) 8 error (by omega)
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
theorem orderedLowerDensity_one_eighth_of_uniform_counting
    (K : OrderedLanguage) (A : Language) (error : ℕ)
    (hcount : ∀ n, n ≤ 8 * K.prefixCount A n + error) :
    (1 / 8 : ℝ) ≤ K.lowerDensity A :=
  orderedLowerDensity_one_eighth_of_eventual_counting K A error
    (Filter.Eventually.of_forall hcount)

/-- Direct ordered-language interface for the dynamic part of Theorem 6.12.

A future implementation needs only instantiate the four prefix counts, prove
their partition identity, and establish the three eventual inequalities.  In
particular, the difficult backward injective charge for long bad runs appears
solely as `hlong`.
-/
theorem orderedLowerDensity_one_eighth_of_eventual_charges
    (K : OrderedLanguage)
    (O Good Singleton Long : Language)
    (eSingleton eGood eLong : ℕ)
    (hpartition : ∀ n,
      K.prefixCount O n +
          K.prefixCount Good n +
          K.prefixCount Singleton n +
          K.prefixCount Long n = n)
    (hsingleton : ∀ᶠ n : ℕ in atTop,
      2 * K.prefixCount Singleton n ≤
        K.prefixCount O n +
          K.prefixCount Good n +
          K.prefixCount Singleton n +
          eSingleton)
    (hgood : ∀ᶠ n : ℕ in atTop,
      K.prefixCount Good n ≤ 2 * K.prefixCount O n + eGood)
    (hlong : ∀ᶠ n : ℕ in atTop,
      K.prefixCount Long n ≤ 2 * K.prefixCount O n + eLong) :
    (1 / 8 : ℝ) ≤ K.lowerDensity O := by
  have h :=
    theorem_6_12_one_eighth_of_eventual_counting
      (K.prefixCount O)
      (K.prefixCount Good)
      (K.prefixCount Singleton)
      (K.prefixCount Long)
      eSingleton eGood eLong
      hpartition hsingleton hgood hlong
  have hratio :
      K.prefixRatio O =
        (fun n : ℕ => (K.prefixCount O n : ℝ) / (n : ℝ)) := by
    funext n
    by_cases hn : n = 0
    · simp [hn, OrderedLanguage.prefixRatio]
    · simp [OrderedLanguage.prefixRatio, hn]
  unfold OrderedLanguage.lowerDensity
  rw [hratio]
  exact h

end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
