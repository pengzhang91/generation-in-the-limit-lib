import GenLimit.Paper21_GenerationInMetricSpaces.Example411Negative

/-! # Example 4.11: generation depends on an equivalent metric -/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir

/-- Example 4.11 of arXiv v2. The second distance is supplied by a genuine
metric structure and satisfies the stronger global bi-Lipschitz bounds.
The same source class is UUS for both metrics. -/
theorem example_4_11 {r : ℝ} (hr : 0 < r) :
    ∃ H : GenLimit.Generic.LanguageClass Hilbert2, ∃ metric' : MetricSpace Hilbert2,
      metric'.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace Hilbert2) ∧
      MutuallyLipschitzDominated dist (@dist Hilbert2 metric'.toDist) 1 2 ∧
      UniformlyUnboundedSupportAt dist r H ∧
      UniformlyUnboundedSupportAt (@dist Hilbert2 metric'.toDist) r H ∧
      (∀ ε : ℝ, 0 < ε → ε < r → UniformlyGeneratableAt dist ε ε H) ∧
      (∀ ε : ℝ, 0 < ε → ε < r →
        ¬ NonuniformlyGeneratableAt (@dist Hilbert2 metric'.toDist) ε ε H) :=
  ⟨Example411.family r, WeightedHilbert.weightedMetric, WeightedHilbert.weightedMetric_topology,
    WeightedHilbert.mutually_dominated,
    Example411.family_uus hr, Example411.family_weighted_uus hr,
    (fun _ hε _ => Example411.uniform_positive hr hε),
    (fun _ hε hεr => Example411.not_nonuniform hr hε hεr)⟩

end GenLimit.MetricSpaces.HilbertAxisReservoir
