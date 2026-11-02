import GenLimit.Paper21_GenerationInMetricSpaces.Example48Rows

/-!
# Example 4.8: the complete two-scale boundary

The source support has infinite positive index sets. The upper and lower
bounds concern the same class, including both equality boundaries.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir

/-- Example 4.8, arXiv v2: the class is `r`-UUS and generation in the
limit is possible exactly below both prescribed scale thresholds. -/
theorem example_4_8_classification {r ε ε' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hε' : 0 < ε') (hε'r : ε' ≤ r) :
    UniformlyUnboundedSupportAt hilbertDistance r (example48LanguageClass r ε ε') ∧
      ∀ γ γ' : ℝ, 0 < γ → γ ≤ r → 0 < γ' → γ' ≤ r →
        (GeneratableInLimitAt hilbertDistance γ γ' (example48LanguageClass r ε ε') ↔
          γ < ε ∧ γ' < ε') := by
  refine ⟨example_4_8_uus hr, ?_⟩
  intro γ γ' hγ _hγr hγ' _hγ'r
  constructor
  · intro hgen
    have hsmall' : γ' < ε' := by
      by_contra hlarge
      exact Example48Negative.not_limit_of_large_generator_scale hr hε hεr hε'
        hγ.le (le_of_not_gt hlarge) hgen
    refine ⟨?_, hsmall'⟩
    by_contra hlarge
    exact Example48Rows.not_limit_of_large_adversary_scale hr hε hε' hεr hε'r
      (le_of_not_gt hlarge) hγ'.le hsmall' hgen
  · rintro ⟨hsmall, hsmall'⟩
    exact example_4_8_positive hr hε hεr hε' hε'r hγ hsmall hγ' hsmall'

/-- The source-facing existence statement of Example 4.8. -/
theorem example_4_8 {r ε ε' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hε' : 0 < ε') (hε'r : ε' ≤ r) :
    ∃ H : GenLimit.Generic.LanguageClass Hilbert2,
      UniformlyUnboundedSupportAt hilbertDistance r H ∧
        ∀ γ γ' : ℝ, 0 < γ → γ ≤ r → 0 < γ' → γ' ≤ r →
          (GeneratableInLimitAt hilbertDistance γ γ' H ↔ γ < ε ∧ γ' < ε') :=
  ⟨example48LanguageClass r ε ε', example_4_8_classification hr hε hεr hε' hε'r⟩

end GenLimit.MetricSpaces.HilbertAxisReservoir
