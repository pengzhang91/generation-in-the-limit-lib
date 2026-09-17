import GenLimit.Core.OrderedDensity
import GenLimit.Support.Asymptotics.Liminf
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

/-- Finite-prefix accounting with an arbitrary coefficient on the long-bad
positions.  The paper's constants `8` and `10` are the special cases where
that coefficient is respectively `2` and `4`. -/
theorem theorem_6_12_finite_accounting_of_long_coefficient
    (k n o g s b eSingleton eGood eLong : ℕ)
    (hpartition : o + g + s + b = n)
    (hsingleton : 2 * s ≤ o + g + s + eSingleton)
    (hgood : g ≤ 2 * o + eGood)
    (hlong : b ≤ k * o + eLong) :
    n ≤ (6 + k) * o + eSingleton + 2 * eGood + eLong := by
  rw [Nat.add_mul]
  omega

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
  simpa using theorem_6_12_finite_accounting_of_long_coefficient
    2 n o g s b eSingleton eGood eLong
    hpartition hsingleton hgood hlong

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
  have herror :
      Tendsto
        (fun n : ℕ => (error : ℝ) / (n : ℝ))
        atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa using GenLimit.lowerDensity_inv_of_eventual_counting_atTop
    id D (fun _ => error) q hq tendsto_id hD herror hcount

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

/-- The common asymptotic accounting theorem behind the paper's `1/8`
endgame and the corrected `1/10` endgame. -/
theorem theorem_6_12_of_eventual_counting_with_long_coefficient
    (k : ℕ)
    (O G Singleton Long : ℕ → ℕ)
    (eSingleton eGood eLong : ℕ)
    (hpartition : ∀ n, O n + G n + Singleton n + Long n = n)
    (hsingleton : ∀ᶠ n : ℕ in atTop,
      2 * Singleton n ≤ O n + G n + Singleton n + eSingleton)
    (hgood : ∀ᶠ n : ℕ in atTop, G n ≤ 2 * O n + eGood)
    (hlong : ∀ᶠ n : ℕ in atTop, Long n ≤ k * O n + eLong) :
    (1 / ((6 + k : ℕ) : ℝ)) ≤
      liminf (fun n : ℕ => (O n : ℝ) / (n : ℝ)) atTop := by
  apply lowerDensity_inv_of_eventual_counting O (6 + k)
    (eSingleton + 2 * eGood + eLong) (by omega)
  · intro n
    calc
      O n ≤ O n + G n + Singleton n + Long n := by omega
      _ = n := hpartition n
  · filter_upwards [hsingleton, hgood, hlong] with n hs hg hb
    simpa [Nat.add_assoc] using theorem_6_12_finite_accounting_of_long_coefficient
      k n (O n) (G n) (Singleton n) (Long n)
      eSingleton eGood eLong
      (hpartition n) hs hg hb

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
  simpa using theorem_6_12_of_eventual_counting_with_long_coefficient
    2 O G Singleton Long eSingleton eGood eLong
    hpartition hsingleton hgood hlong

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

/-- Ordered-language form of the common four-way charging endgame, with the
long-bad coefficient left as a parameter. -/
theorem orderedLowerDensity_of_eventual_charges_with_long_coefficient
    (k : ℕ)
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
      K.prefixCount Long n ≤ k * K.prefixCount Output n + eLong) :
    (1 / ((6 + k : ℕ) : ℝ)) ≤ K.lowerDensity Output := by
  have h :=
    theorem_6_12_of_eventual_counting_with_long_coefficient
      k
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
  simpa using orderedLowerDensity_of_eventual_charges_with_long_coefficient
    2 K O Good Singleton Long eSingleton eGood eLong
    hpartition hsingleton hgood hlong

end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
