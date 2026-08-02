import GenLimit.Core.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.LiminfLimsup

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

end OrderedLanguage
end KleinbergWei
end GenLimit
