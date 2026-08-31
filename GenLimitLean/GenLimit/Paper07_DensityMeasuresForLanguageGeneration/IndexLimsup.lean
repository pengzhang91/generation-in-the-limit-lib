import GenLimit.Core.OrderedDensity
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfinitelyOften
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Ring.Real

/-!
# #07 Index-density limsup

Corollary 2.2: the accurate selector names the target arbitrarily late, so
the limsup of its guessed-language upper densities is one.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

open Filter

/-- Ordered upper density of the language guessed at round t. -/
noncomputable def indexUpperDensityAt
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (ordering : OrderedLanguage) (t : ℕ) : ℝ :=
  ordering.upperDensity (C (guessIndex C stream t))

noncomputable def indexUpperDensityLimsup
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (ordering : OrderedLanguage) : ℝ :=
  limsup (indexUpperDensityAt C stream ordering) atTop

theorem indexUpperDensityLimsup_eq_one_of_frequently_accurate
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (ordering : OrderedLanguage)
    (hcarrier : ordering.carrier = C z)
    (haccurate : ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r) :
    indexUpperDensityLimsup C stream ordering = 1 := by
  have hfrequentAccurate :
      ∃ᶠ r : ℕ in atTop, AccurateAt C stream z r := by
    apply frequently_atTop.mpr
    intro t
    obtain ⟨r, htr, hr⟩ := haccurate t
    exact ⟨r, htr, hr⟩
  have hfrequentOne :
      ∃ᶠ r : ℕ in atTop,
        (1 : ℝ) ≤ indexUpperDensityAt C stream ordering r := by
    apply hfrequentAccurate.mono
    intro r hr
    have hguess : C (guessIndex C stream r) = ordering.carrier :=
      hr.trans hcarrier.symm
    simp [indexUpperDensityAt, hguess]
  apply le_antisymm
  · unfold indexUpperDensityLimsup
    apply limsup_le_of_le
    · exact isCoboundedUnder_le_of_le atTop
        (fun r => ordering.upperDensity_nonneg
          (C (guessIndex C stream r)))
    · exact Eventually.of_forall
        (fun r => ordering.upperDensity_le_one
          (C (guessIndex C stream r)))
  · unfold indexUpperDensityLimsup
    exact le_limsup_of_frequently_le hfrequentOne
      (isBoundedUnder_of
        ⟨1, fun r => ordering.upperDensity_le_one
          (C (guessIndex C stream r))⟩)

/-- Corollary 2.2. -/
theorem corollary_2_2
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (ordering : OrderedLanguage)
    (hcarrier : ordering.carrier = C z)
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    IndexValidInLimit C stream z ∧
      indexUpperDensityLimsup C stream ordering = 1 := by
  have hmain := theorem_2_1 hP hfirst
  exact
    ⟨hmain.1,
      indexUpperDensityLimsup_eq_one_of_frequently_accurate
        ordering hcarrier hmain.2⟩

end GenLimit.KleinbergWei.DensityMeasures
