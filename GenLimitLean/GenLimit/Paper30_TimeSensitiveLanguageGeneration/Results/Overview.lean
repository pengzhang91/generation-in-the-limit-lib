import GenLimit.Core.GenericGeneration
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.Impossibility
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.UniformHallucination
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.Results.Supporting

/-!
# Paper 30: main theorems

Ganju, McVoy, Dughmi, and Teng, *A Theory of Time-Sensitive Language Generation:
Sparse Hallucination Beats Mode Collapse* (arXiv:2605.11302v2).
-/

namespace GenLimit.TimeSensitive.Results

open Filter MeasureTheory
open scoped Topology

/-- Theorem 1. The full natural-number target has an exact presentation
with almost-sure lower timely density zero for any finite-valued deadline. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : RandomizedGenerator Ω) (D : ℕ → ℕ)
    (consistent : ∀ (z : ℕ) (s : Generic.Stream ℕ), Generic.Presents s (sparseFamily z) →
      ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, A.run s ω t ∈ sparseFamily z) :
    ∃ s : Generic.Stream ℕ, Generic.Presents s (sparseFamily 0) ∧
      ∀ᵐ ω ∂μ, lowerTimelyDensity (A.run s ω) id D = 0 :=
  A.eventually_consistent_obstruction μ D consistent

/-- Theorem 2. Even presentation-dependent vanishing expected loss suffices
for the adversarial lower-density obstruction under a linear deadline. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : RandomizedGenerator Ω) (D : ℕ → ℕ)
    (linear : ∃ c : ℕ, ∀ᶠ j in atTop, D j ≤ c*(j+1))
    (vanish : ∀ (z : ℕ) (s : Generic.Stream ℕ), Generic.Presents s (sparseFamily z) →
      Tendsto (A.expectedRate μ s (sparseFamily z)) atTop (𝓝 0)) :
    ∃ s : Generic.Stream ℕ, Generic.Presents s (sparseFamily 0) ∧
      ∀ᵐ ω ∂μ, lowerTimelyDensity (A.run s ω) id D = 0 :=
  A.linear_vanishing_obstruction μ D linear vanish

/-- Refutation of Theorem 3's uniform expected hallucination clause for
every vanishing rate on a fixed countably infinite family of infinite targets. -/
theorem theorem_3_uniform_bound_false {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : RandomizedGenerator Ω)
    {H : ℕ → ℝ} (vanishes : Tendsto H atTop (𝓝 0)) :
    ¬∀ᶠ t in atTop, ∀ (z : ℕ) (s : Generic.Stream ℕ), Generic.Presents s (sharedRoot z) →
      A.expectedRate μ s (sharedRoot z) t ≤ H t :=
  no_uniform_vanishing_rate μ A vanishes

/-- Theorem 4 (restated as Appendix Theorem 12). On every exact target presentation,
the repaired GCG is eventually consistent and has upper timely density at least one half.
An exact presentation attains equality. Both clauses use Lean's identity deadline,
which requires the element of zero-based rank `j` in the first `j` outputs,
one round earlier than the paper requires. -/
theorem theorem_4
    (F : CanonicallyOrderedFamily) (z : ℕ)
    (hfirst : KleinbergWei.DensityMeasures.FirstOccurrence F.language z) :
    (∀ stream : Generic.Stream ℕ, Generic.Presents stream (F.language z) →
      (∃ T, ∀ t, T ≤ t →
        totalizedGCGOutput F stream t ∈ F.language z) ∧
      (1 / 2 : ℝ) ≤
        upperTimelyDensity (totalizedGCGOutput F stream)
          (F.order z).enumeration id) ∧
    ∃ stream : Generic.Stream ℕ,
      Generic.Presents stream (F.language z) ∧
      (∃ T, ∀ t, T ≤ t →
        totalizedGCGOutput F stream t ∈ F.language z) ∧
      upperTimelyDensity (totalizedGCGOutput F stream)
        (F.order z).enumeration id = (1 / 2 : ℝ) :=
  totalizedGCG_theorem_4 F z hfirst

end GenLimit.TimeSensitive.Results
