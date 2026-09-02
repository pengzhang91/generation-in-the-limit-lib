import GenLimit.Core.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Ordered relative density

This file records the ordered-density language shared by the three
Kleinberg--Wei papers.  In the notation of Definition 4.1 of
*Density Measures for Language Generation*, `enumeration` lists the elements
of the reference language `K` without repetition.  Density is measured in the
first `n` positions of that ordering, rather than in ambient natural-number
prefixes.
-/

namespace GenLimit
namespace KleinbergWei

open Filter

/-- A duplicate-free ordering of all strings in a language. -/
structure OrderedLanguage where
  carrier : Language
  enumeration : ℕ → ℕ
  enumeration_injective : Function.Injective enumeration
  range_enumeration : Set.range enumeration = carrier

namespace OrderedLanguage

/-- Number of the first `n` ordered strings of `K` which belong to `A`. -/
noncomputable def prefixCount (K : OrderedLanguage) (A : Language) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter fun i => K.enumeration i ∈ A).card

theorem prefixCount_le (K : OrderedLanguage) (A : Language) (n : ℕ) :
    K.prefixCount A n ≤ n := by
  classical
  simpa [prefixCount] using
    Finset.card_filter_le (s := Finset.range n) (p := fun i => K.enumeration i ∈ A)

theorem prefixCount_mono
    (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  unfold prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hAB hi.2⟩

@[simp] theorem prefixCount_empty (K : OrderedLanguage) (n : ℕ) :
    K.prefixCount (∅ : Language) n = 0 := by
  classical
  simp [prefixCount]

@[simp] theorem prefixCount_carrier (K : OrderedLanguage) (n : ℕ) :
    K.prefixCount K.carrier n = n := by
  classical
  have hmem : ∀ i, K.enumeration i ∈ K.carrier := by
    intro i
    rw [← K.range_enumeration]
    exact ⟨i, rfl⟩
  simp [prefixCount, hmem]

/-- The finite relative-density ratio in the first `n` positions.

The value at `n = 0` is set to zero; the asymptotic densities are unchanged
by this convention.
-/
noncomputable def prefixRatio
    (K : OrderedLanguage) (A : Language) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (K.prefixCount A n : ℝ) / n

@[simp] theorem prefixRatio_zero (K : OrderedLanguage) (A : Language) :
    K.prefixRatio A 0 = 0 := by
  simp [prefixRatio]

theorem prefixRatio_nonneg (K : OrderedLanguage) (A : Language) (n : ℕ) :
    0 ≤ K.prefixRatio A n := by
  by_cases hn : n = 0
  · simp [prefixRatio, hn]
  · simp only [prefixRatio, hn, if_false]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem prefixRatio_le_one (K : OrderedLanguage) (A : Language) (n : ℕ) :
    K.prefixRatio A n ≤ 1 := by
  by_cases hn : n = 0
  · simp [prefixRatio, hn]
  · simp only [prefixRatio, hn, if_false]
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    rw [div_le_one hnpos]
    exact_mod_cast K.prefixCount_le A n

theorem prefixRatio_mono
    (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixRatio A n ≤ K.prefixRatio B n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [prefixRatio, hn, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast K.prefixCount_mono hAB n)
      (Nat.cast_nonneg n)

/-- Definition 4.1: upper density of `A` in the ordered language `K`. -/
noncomputable def upperDensity (K : OrderedLanguage) (A : Language) : ℝ :=
  limsup (K.prefixRatio A) atTop

/-- Definition 4.1: lower density of `A` in the ordered language `K`. -/
noncomputable def lowerDensity (K : OrderedLanguage) (A : Language) : ℝ :=
  liminf (K.prefixRatio A) atTop

@[simp] theorem prefixRatio_empty (K : OrderedLanguage) (n : ℕ) :
    K.prefixRatio (∅ : Language) n = 0 := by
  simp [prefixRatio]

@[simp] theorem prefixRatio_carrier (K : OrderedLanguage) (n : ℕ) :
    K.prefixRatio K.carrier n = if n = 0 then 0 else 1 := by
  by_cases hn : n = 0
  · simp [prefixRatio, hn]
  · simp [prefixRatio, hn]

theorem upperDensity_nonneg (K : OrderedLanguage) (A : Language) :
    0 ≤ K.upperDensity A := by
  unfold upperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall (fun n => K.prefixRatio_nonneg A n)
  · exact isBoundedUnder_of ⟨1, fun n => K.prefixRatio_le_one A n⟩

theorem upperDensity_le_one (K : OrderedLanguage) (A : Language) :
    K.upperDensity A ≤ 1 := by
  unfold upperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop
      (fun n => K.prefixRatio_nonneg A n)
  · exact Eventually.of_forall (fun n => K.prefixRatio_le_one A n)

theorem lowerDensity_nonneg (K : OrderedLanguage) (A : Language) :
    0 ≤ K.lowerDensity A := by
  unfold lowerDensity
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => K.prefixRatio_le_one A n)
  · exact Eventually.of_forall (fun n => K.prefixRatio_nonneg A n)

theorem lowerDensity_le_one (K : OrderedLanguage) (A : Language) :
    K.lowerDensity A ≤ 1 := by
  unfold lowerDensity
  apply liminf_le_of_frequently_le
  · exact (Eventually.of_forall
      (fun n => K.prefixRatio_le_one A n)).frequently
  · exact isBoundedUnder_of
      ⟨0, fun n => K.prefixRatio_nonneg A n⟩

theorem lowerDensity_mono
    (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) :
    K.lowerDensity A ≤ K.lowerDensity B := by
  unfold lowerDensity
  apply liminf_le_liminf
  · exact Eventually.of_forall (K.prefixRatio_mono hAB)
  · exact isBoundedUnder_of
      ⟨0, fun n => K.prefixRatio_nonneg A n⟩
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => K.prefixRatio_le_one B n)

theorem upperDensity_mono
    (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) :
    K.upperDensity A ≤ K.upperDensity B := by
  unfold upperDensity
  apply limsup_le_limsup
  · exact Eventually.of_forall (K.prefixRatio_mono hAB)
  · exact isCoboundedUnder_le_of_le atTop
      (fun n => K.prefixRatio_nonneg A n)
  · exact isBoundedUnder_of
      ⟨1, fun n => K.prefixRatio_le_one B n⟩

@[simp] theorem upperDensity_carrier (K : OrderedLanguage) :
    K.upperDensity K.carrier = 1 := by
  have htendsto : Tendsto (K.prefixRatio K.carrier) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [prefixRatio_carrier, hn]
  exact htendsto.limsup_eq

@[simp] theorem lowerDensity_carrier (K : OrderedLanguage) :
    K.lowerDensity K.carrier = 1 := by
  have htendsto : Tendsto (K.prefixRatio K.carrier) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [prefixRatio_carrier, hn]
  exact htendsto.liminf_eq

/-- Shared analytic transfer for ordered lower density.

If, up to an asymptotically vanishing error, every source prefix ratio is at
most `q` times the corresponding output ratio, then the output lower density
is at least the source lower density divided by `q`. Paper-specific files
should prove their finite counting inequality and instantiate this theorem,
rather than duplicating the `liminf` argument. -/
theorem lowerDensity_div_le_of_eventually_prefixRatio_le
    (K : OrderedLanguage) (source output : Language)
    (q : ℝ) (hq : 0 < q) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (hprefix : ∀ᶠ n : ℕ in atTop,
      K.prefixRatio source n ≤ q * K.prefixRatio output n + error n) :
    K.lowerDensity source / q ≤ K.lowerDensity output := by
  unfold lowerDensity
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop
      (fun n => K.prefixRatio_le_one output n))
    (isBoundedUnder_of
      ⟨0, fun n => K.prefixRatio_nonneg output n⟩)).2
  intro y hy
  have hscaled :
      q * y < liminf (K.prefixRatio source) atTop := by
    have h := (lt_div_iff₀ hq).mp hy
    simpa [mul_comm] using h
  obtain ⟨r, hyr, hrDensity⟩ := exists_between hscaled
  have hrEventually :
      ∀ᶠ n : ℕ in atTop, r < K.prefixRatio source n :=
    eventually_lt_of_lt_liminf hrDensity
      (isBoundedUnder_of
        ⟨0, fun n => K.prefixRatio_nonneg source n⟩)
  have herrorEventually :
      ∀ᶠ n : ℕ in atTop, error n < r - q * y := by
    have hpositive : 0 < r - q * y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hprefix] with
      n hr hsmall hcount
  nlinarith

end OrderedLanguage
end KleinbergWei
end GenLimit
