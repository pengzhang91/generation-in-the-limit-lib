import GenLimit.Paper21_GenerationInMetricSpaces.Example49UniformLower

/-! # Example 4.9: all four generation regimes on the same source class -/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir

/-- Example 4.9 of arXiv v2. The three positive generator-scale regimes
and the failure regime include every stated threshold boundary. -/
theorem example_4_9 {r ε₁ ε₂ ε' : ℝ}
    (hr : 0 < r) (hε₁ : 0 < ε₁) (hε₁₂ : ε₁ ≤ ε₂) (hε₂r : ε₂ ≤ r)
    (hε' : 0 < ε') (_hε'r : ε' ≤ r) :
    ∃ H : GenLimit.Generic.LanguageClass Hilbert2,
      UniformlyUnboundedSupportAt dist r H ∧
      (∀ γ γ', ε₂ ≤ γ → γ ≤ r → 0 < γ' → γ' < ε' →
        UniformlyGeneratableAt dist γ γ' H) ∧
      (∀ γ γ', ε₁ ≤ γ → γ < ε₂ → 0 < γ' → γ' < ε' →
        NonuniformlyGeneratableAt dist γ γ' H ∧ ¬ UniformlyGeneratableAt dist γ γ' H) ∧
      (∀ γ γ', 0 < γ → γ < ε₁ → 0 < γ' → γ' < ε' →
        GeneratableInLimitAt dist γ γ' H ∧ ¬ NonuniformlyGeneratableAt dist γ γ' H) ∧
      (∀ γ γ', 0 < γ → γ ≤ r → ε' ≤ γ' → γ' ≤ r →
        ¬ GeneratableInLimitAt dist γ γ' H) := by
  refine ⟨Example49.family r ε₁ ε₂ ε', Example49.family_uus hr, ?_, ?_, ?_, ?_⟩
  · intro γ γ' hγ _ hγ' hγ'ε'
    exact Example49.uniform_positive hr hε₁.le (hε₁.le.trans hε₁₂) hε₁₂ hε' hγ hγ'ε'
  · intro γ γ' hε₁γ hγε₂ hγ' hγ'ε'
    exact ⟨Example49.nonuniform_positive hr hε₁.le hε' hε₁γ hγ'ε',
      Example49.not_uniform_of_small_adversary hr hε₁ (hε₁.trans_le hε₁₂) hε'
        (hε₁.le.trans hε₁γ) hγε₂ hγ'.le⟩
  · intro γ γ' hγ hγε₁ hγ' hγ'ε'
    exact ⟨Example49.limit_positive hr hε' (hγε₁.le.trans (hε₁₂.trans hε₂r)) hγ'ε',
      Example49.not_nonuniform_of_small_adversary hr hε₁ hε' hγ.le hγε₁ hγ'.le⟩
  · intro γ γ' hγ _ hε'γ' _
    exact Example49.not_limit_of_large_generator hr hε₁ hε' hγ.le hε'γ'

end GenLimit.MetricSpaces.HilbertAxisReservoir
