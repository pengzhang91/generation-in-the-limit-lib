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

@[simp] theorem prefixCount_inter_carrier
    (K : OrderedLanguage) (A : Language) (n : ℕ) :
    K.prefixCount (A ∩ K.carrier) n = K.prefixCount A n := by
  classical
  unfold prefixCount
  congr 1
  ext i
  have hcarrier : K.enumeration i ∈ K.carrier := by
    rw [← K.range_enumeration]
    exact ⟨i, rfl⟩
  simp [hcarrier]

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

@[simp] theorem lowerDensity_inter_carrier
    (K : OrderedLanguage) (A : Language) :
    K.lowerDensity (A ∩ K.carrier) = K.lowerDensity A := by
  unfold lowerDensity prefixRatio
  congr 2
  funext n
  rw [K.prefixCount_inter_carrier]

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

/-! ## Finite perturbations of the measured set -/

/-- A finite exceptional set can contribute at most its cardinality to any
ordered prefix count. -/
theorem prefixCount_le_ncard_of_finite
    (K : OrderedLanguage) {F : Language} (hF : F.Finite) (n : ℕ) :
    K.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold prefixCount
  have hcardImage :
      (((Finset.range n).filter fun i => K.enumeration i ∈ F).image
          K.enumeration).card =
        ((Finset.range n).filter fun i => K.enumeration i ∈ F).card := by
    exact Finset.card_image_of_injective _ K.enumeration_injective
  rw [← hcardImage]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_image, Finset.mem_filter] at hx
  obtain ⟨i, ⟨_hiRange, hiF⟩, rfl⟩ := hx
  exact Set.Finite.mem_toFinset hF |>.2 hiF

/-- Prefix counts change by at most the finite asymmetric difference in the
first argument. -/
theorem prefixCount_le_add_ncard_diff
    (K : OrderedLanguage) {A B : Language}
    (hfinite : (A \ B).Finite) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n + hfinite.toFinset.card := by
  classical
  let aIndices :=
    (Finset.range n).filter fun i => K.enumeration i ∈ A
  let bIndices :=
    (Finset.range n).filter fun i => K.enumeration i ∈ B
  let diffIndices :=
    (Finset.range n).filter fun i => K.enumeration i ∈ A \ B
  have hsub : aIndices ⊆ bIndices ∪ diffIndices := by
    intro i hi
    simp only [aIndices, bIndices, diffIndices, Finset.mem_filter,
      Finset.mem_union] at hi ⊢
    by_cases hiB : K.enumeration i ∈ B
    · exact Or.inl ⟨hi.1, hiB⟩
    · exact Or.inr ⟨hi.1, hi.2, hiB⟩
  have hcard : aIndices.card ≤ bIndices.card + diffIndices.card := by
    exact (Finset.card_le_card hsub).trans
      (Finset.card_union_le bIndices diffIndices)
  have hdiff : diffIndices.card ≤ hfinite.toFinset.card := by
    simpa [diffIndices, prefixCount] using
      K.prefixCount_le_ncard_of_finite hfinite n
  simpa [aIndices, bIndices, diffIndices, prefixCount] using
    hcard.trans (Nat.add_le_add_left hdiff _)

/-- Ratio form of `prefixCount_le_add_ncard_diff`.  The finite error is
displayed explicitly because it vanishes along `atTop`. -/
theorem prefixRatio_le_add_finiteError
    (K : OrderedLanguage) {A B : Language}
    (hfinite : (A \ B).Finite) (n : ℕ) :
    K.prefixRatio A n ≤
      K.prefixRatio B n + (hfinite.toFinset.card : ℝ) / n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnnonneg : (0 : ℝ) ≤ n := by positivity
    have hcount :
        (K.prefixCount A n : ℝ) ≤
          K.prefixCount B n + hfinite.toFinset.card := by
      exact_mod_cast K.prefixCount_le_add_ncard_diff hfinite n
    simp only [prefixRatio, hn, if_false]
    rw [← add_div]
    exact div_le_div_of_nonneg_right hcount hnnonneg

/-- Removing finitely many points from the measured set does not change its
ordered lower density.  The target ordering `K` is fixed; no claim is made
about changing the reference language or its ordering. -/
theorem lowerDensity_diff_finite
    (K : OrderedLanguage) (A : Language) {F : Language}
    (hF : F.Finite) :
    K.lowerDensity (A \ F) = K.lowerDensity A := by
  apply le_antisymm
  · exact K.lowerDensity_mono Set.diff_subset
  · have hfinite : (A \ (A \ F)).Finite := by
      apply hF.subset
      intro x hx
      by_contra hxF
      exact hx.2 ⟨hx.1, hxF⟩
    have herror :
        Tendsto (fun n : ℕ => (hfinite.toFinset.card : ℝ) / (n : ℝ))
          atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hle :=
      K.lowerDensity_div_le_of_eventually_prefixRatio_le
        A (A \ F) 1 (by norm_num)
        (fun n : ℕ => (hfinite.toFinset.card : ℝ) / (n : ℝ))
        herror
        (Eventually.of_forall fun n => by
          simpa using K.prefixRatio_le_add_finiteError hfinite n)
    simpa using hle

/-- Finite symmetric perturbations of the measured set preserve ordered
lower density.  As above, the reference ordering `K` itself is unchanged. -/
theorem lowerDensity_eq_of_finite_symmetricDifference
    (K : OrderedLanguage) {A B : Language}
    (hAB : (A \ B).Finite) (hBA : (B \ A).Finite) :
    K.lowerDensity A = K.lowerDensity B := by
  calc
    K.lowerDensity A = K.lowerDensity (A \ (A \ B)) :=
      (K.lowerDensity_diff_finite A hAB).symm
    _ = K.lowerDensity (B \ (B \ A)) := by
      congr 1
      ext x
      simp only [Set.mem_diff]
      tauto
    _ = K.lowerDensity B :=
      K.lowerDensity_diff_finite B hBA

end OrderedLanguage
end KleinbergWei
end GenLimit
