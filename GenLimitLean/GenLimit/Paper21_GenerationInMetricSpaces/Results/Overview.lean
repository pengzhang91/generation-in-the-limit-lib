import GenLimit.Paper21_GenerationInMetricSpaces.BiLipschitzRepair
import GenLimit.Paper21_GenerationInMetricSpaces.DiscreteReduction
import GenLimit.Paper21_GenerationInMetricSpaces.EquivalentMetricDiagnostic
import GenLimit.Paper21_GenerationInMetricSpaces.Example48Positive
import GenLimit.Paper21_GenerationInMetricSpaces.FiniteClassCorollaries
import GenLimit.Paper21_GenerationInMetricSpaces.FiniteDimensionalCorollary
import GenLimit.Paper21_GenerationInMetricSpaces.FiniteUnionDiagnostic
import GenLimit.Paper21_GenerationInMetricSpaces.LipschitzTransfer
import GenLimit.Paper21_GenerationInMetricSpaces.NonuniformNecessityDiagnostic
import GenLimit.Paper21_GenerationInMetricSpaces.RealLineThresholdNegative
import GenLimit.Paper21_GenerationInMetricSpaces.ScaleMonotonicity
import GenLimit.Paper21_GenerationInMetricSpaces.Theorem36

/-!
# Paper 21: main-results overview

This module is the public results facade for Li--Raman--Tewari,
*On Generation in Metric Spaces* (arXiv:2602.07710v1).  The declarations
below are thin wrappers around the canonical proof and diagnostic modules;
no proof is duplicated here.

## Coverage boundary

Corollaries 3.2 and 3.4, Theorem 3.6, Theorems 4.1--4.2, Corollary 4.3,
Example 4.5, Theorems 4.6--4.7 and 4.10, and Proposition D.1 are exposed in
complete semantic form.  The exact uniformly-generatable-cover core of
Theorem 3.3 is also complete.

The ambient-center covering convention makes the printed necessity
directions of Theorems 3.1 and 3.3 invalid without an internalization
premise; Lean exposes the valid sufficiency directions, corrected necessity
theorems, and genuine-metric counterexamples.  Printed Theorem 3.5 is
refuted by an explicit separable metric counterexample, while Theorem 3.6
gives the corresponding valid union separation.  For Theorem 4.4, Lean
refutes the fixed-radius inference used by the printed proof and proves a
replacement theorem under mutual Lipschitz bounds; it does not claim to
refute the theorem's full topological-equivalence statement.

Example 4.8 currently contains its UUS and positive-generation regimes.  Its
two negative regimes, all four regimes of Example 4.9, and Example 4.11
remain open.  The development is semantic and classical: it claims no
extracted algorithm, runtime bound, or independent human correspondence
audit.
-/

namespace GenLimit.MetricSpaces.Results

/-! ## Scale-closure characterizations -/

/-- The valid sufficiency direction of Theorem 3.1. -/
abbrev theorem_3_1_sufficiency
    {α : Type*} [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x, ρ x x = 0) (hε : 0 ≤ ε)
    (hdim : HasFiniteScaleClosureDimension ρ ε ε' H) :=
  GenLimit.MetricSpaces.finite_scaleClosureDimension_implies_uniform
    hrefl hε hdim

/-- Theorem 3.1's necessity direction with the missing internalization
premise made explicit. -/
abbrev theorem_3_1_necessity_of_internalization
    {α : Type*} {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hInternal : ScaleClosureWitnessCoverInternalizationAt ρ ε ε' H)
    (hUniform : UniformlyGeneratableAt ρ ε ε' H) :=
  GenLimit.MetricSpaces.uniform_implies_finite_scaleClosureDimension_of_internalization
    hInternal hUniform

/-- Counterexample to the unqualified ambient-center necessity direction in
printed Theorem 3.1. -/
abbrev theorem_3_1_printed_necessity_is_false :=
  GenLimit.MetricSpaces.NecessityCounterexample.theorem_3_1_necessity_counterexample

/-- Corollary 3.2 for finite classes at ordered positive scales. -/
abbrev corollary_3_2
    {α : Type*} [Nonempty α]
    {ρ : Distance α} {r ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x, ρ x x = 0)
    (hr : 0 < r)
    (hUUS : UniformlyUnboundedSupportAt ρ r H)
    (hε : 0 < ε) (hε' : 0 < ε')
    (hεr : ε ≤ r) (hε'r : ε' ≤ r)
    (hε'ε : ε' ≤ ε) (hFinite : H.Finite) :=
  GenLimit.MetricSpaces.corollary_3_2
    hrefl hr hUUS hε hε' hεr hε'r hε'ε hFinite

/-- Theorem 3.3's exact semantic characterization by a nondecreasing cover
of uniformly generatable subclasses. -/
abbrev theorem_3_3_semantic
    {α : Type*} {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hself : ∀ x : α, ρ x x ≤ ε) :=
  GenLimit.MetricSpaces.nonuniform_iff_nondecreasing_uniform_cover
    (H := H) (ε' := ε') hself

/-- The source-faithful `(ii) -> (i)` direction of printed Theorem 3.3. -/
abbrev theorem_3_3_sufficiency
    {α : Type*} [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x : α, ρ x x = 0) (hε : 0 ≤ ε)
    (hcover : IsNondecreasingMetricCover H classes)
    (hfinite : ∀ n,
      HasFiniteScaleClosureDimension ρ ε ε' (classes n)) :=
  GenLimit.MetricSpaces.finite_scaleClosure_cover_implies_nonuniform
    hrefl hε hcover hfinite

/-- Theorem 3.3's reverse scale-closure direction with the missing
internalization premise made explicit. -/
abbrev theorem_3_3_necessity_of_internalization
    {α : Type*} {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hInternal : ∀ K : GenLimit.Generic.LanguageClass α,
      K ⊆ H → ScaleClosureWitnessCoverInternalizationAt ρ ε ε' K)
    (hNonuniform : NonuniformlyGeneratableAt ρ ε ε' H) :=
  GenLimit.MetricSpaces.nonuniform_implies_finite_scaleClosure_cover_of_internalization
    hInternal hNonuniform

/-- Counterexample to the unqualified ambient-center reverse direction in
printed Theorem 3.3. -/
abbrev theorem_3_3_printed_necessity_is_false :=
  GenLimit.MetricSpaces.Theorem33Counterexample.theorem_3_3_necessity_counterexample

/-- Corollary 3.4 for countable classes at ordered positive scales. -/
abbrev corollary_3_4
    {α : Type*} [Nonempty α]
    {ρ : Distance α} {r ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x, ρ x x = 0)
    (hr : 0 < r)
    (hUUS : UniformlyUnboundedSupportAt ρ r H)
    (hε : 0 < ε) (hε' : 0 < ε')
    (hεr : ε ≤ r) (hε'r : ε' ≤ r)
    (hε'ε : ε' ≤ ε) (hCountable : H.Countable) :=
  GenLimit.MetricSpaces.corollary_3_4
    hrefl hr hUUS hε hε' hεr hε'r hε'ε hCountable

/-! ## Finite unions and arbitrary metric spaces -/

/-- Explicit counterexample to printed Theorem 3.5 under its stated
finite-union hypotheses. -/
abbrev theorem_3_5_printed_statement_is_false :=
  GenLimit.MetricSpaces.FiniteUnionCounterexample.theorem_3_5_finite_union_implication_false

/-- Full Theorem 3.6 transport to every metric space with an infinite
radius-`r` packing. -/
abbrev theorem_3_6
    {α : Type*} [MetricSpace α] {r ε ε' : ℝ}
    (hr : 0 < r) (hε0 : 0 ≤ ε) (hεr : ε ≤ r / 2)
    (hε'0 : 0 ≤ ε') (hε'r : ε' ≤ r / 2)
    (hcover : ¬HasFiniteCover (fun x y : α => dist x y) r Set.univ) :=
  GenLimit.MetricSpaces.theorem_3_6
    hr hε0 hεr hε'0 hε'r hcover

/-! ## Scale and metric dependence -/

/-- Theorem 4.1: UUS is invariant across positive scales on doubling
spaces. -/
abbrev theorem_4_1
    {α : Type*} {ρ : Distance α}
    {H : GenLimit.Generic.LanguageClass α} {r : ℝ}
    (hDoubling : IsDoublingDistance ρ) (hr : 0 < r)
    (hUUS : UniformlyUnboundedSupportAt ρ r H) :=
  GenLimit.MetricSpaces.theorem_4_1_doubling_uus_scale_invariance
    hDoubling hr hUUS

/-- Theorem 4.2: uniform and non-uniform generation are invariant across
positive scales on doubling spaces. -/
abbrev theorem_4_2
    {α : Type*} {ρ : Distance α} {δ δ' ε ε' r : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle : ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (hr : 0 < r) (hUUS : UniformlyUnboundedSupportAt ρ r H)
    (hδ : 0 < δ) (hδε : δ < ε)
    (hδ' : 0 < δ') (hδ'ε' : δ' < ε') :=
  GenLimit.MetricSpaces.theorem_4_2_doubling_generation_scale_invariance
    hDoubling hrefl hsymm htriangle hr hUUS hδ hδε hδ' hδ'ε'

/-- Corollary 4.3 for finite-dimensional real normed spaces. -/
abbrev corollary_4_3
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : GenLimit.Generic.LanguageClass E}
    {r δ δ' ε ε' : ℝ}
    (hr : 0 < r)
    (hUUS : UniformlyUnboundedSupportAt
      (dist : E → E → ℝ) r H)
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hε : 0 < ε) (hε' : 0 < ε') :=
  GenLimit.MetricSpaces.corollary_4_3
    E hr hUUS hδ hδ' hε hε'

/-- Counterexample to the fixed-radius covering inference used by the
printed proof of Theorem 4.4. -/
abbrev theorem_4_4_proof_inference_is_false :=
  GenLimit.MetricSpaces.theorem_4_4_fixed_radius_inference_false

/-- Repaired Theorem 4.4 under explicit mutual Lipschitz domination. -/
abbrev theorem_4_4_bilipschitz_repair
    {α : Type*} {ρ₁ ρ₂ : Distance α} {M₁₂ M₂₁ : ℝ}
    {r₁ r₂ ε₁ ε₁' ε₂ ε₂' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling₁ : IsDoublingDistance ρ₁)
    (hDoubling₂ : IsDoublingDistance ρ₂)
    (hrefl₁ : ∀ x : α, ρ₁ x x = 0)
    (hsymm₁ : ∀ x y : α, ρ₁ x y = ρ₁ y x)
    (htriangle₁ : ∀ x y z : α, ρ₁ x z ≤ ρ₁ x y + ρ₁ y z)
    (hrefl₂ : ∀ x : α, ρ₂ x x = 0)
    (hsymm₂ : ∀ x y : α, ρ₂ x y = ρ₂ y x)
    (htriangle₂ : ∀ x y z : α, ρ₂ x z ≤ ρ₂ x y + ρ₂ y z)
    (hM₁₂ : 0 < M₁₂) (hM₂₁ : 0 < M₂₁)
    (hdom : MutuallyLipschitzDominated ρ₁ ρ₂ M₁₂ M₂₁)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hε₁ : 0 < ε₁) (hε₁' : 0 < ε₁')
    (hε₂ : 0 < ε₂) (hε₂' : 0 < ε₂') :=
  GenLimit.MetricSpaces.theorem_4_4_bilipschitz_repair
    (H := H)
    hDoubling₁ hDoubling₂ hrefl₁ hsymm₁ htriangle₁
    hrefl₂ hsymm₂ htriangle₂ hM₁₂ hM₂₁ hdom
    hr₁ hr₂ hε₁ hε₁' hε₂ hε₂'

/-- Complete positive and negative threshold statement of Example 4.5. -/
abbrev example_4_5
    {ε : ℝ} (hεpos : 0 < ε) (hεlt : ε < 1) :=
  GenLimit.MetricSpaces.RealLineThreshold.example_4_5_complete
    hεpos hεlt

/-- Theorem 4.6: generation in the limit is monotone under decreasing
adversary and generator novelty scales. -/
abbrev theorem_4_6
    {α : Type*} {ρ : Distance α}
    {H : GenLimit.Generic.LanguageClass α}
    {δ δ' ε ε' : ℝ}
    (hδε : δ ≤ ε) (hδ'ε' : δ' ≤ ε')
    (hgen : GeneratableInLimitAt ρ ε ε' H) :=
  GenLimit.MetricSpaces.theorem_4_6_limit_scale_monotonicity
    hδε hδ'ε' hgen

/-- The uniform-generation half of Theorem 4.7. -/
abbrev theorem_4_7_uniform
    {α : Type*} {ρ : Distance α}
    {H : GenLimit.Generic.LanguageClass α}
    {ε ε' δ δ' : ℝ}
    (hεδ : ε ≤ δ) (hδ'ε' : δ' ≤ ε')
    (hgen : UniformlyGeneratableAt ρ ε ε' H) :=
  GenLimit.MetricSpaces.theorem_4_7_uniform_scale_monotonicity
    hεδ hδ'ε' hgen

/-- The non-uniform-generation half of Theorem 4.7. -/
abbrev theorem_4_7_nonuniform
    {α : Type*} {ρ : Distance α}
    {H : GenLimit.Generic.LanguageClass α}
    {ε ε' δ δ' : ℝ}
    (hεδ : ε ≤ δ) (hδ'ε' : δ' ≤ ε')
    (hgen : NonuniformlyGeneratableAt ρ ε ε' H) :=
  GenLimit.MetricSpaces.theorem_4_7_nonuniform_scale_monotonicity
    hεδ hδ'ε' hgen

/-- The UUS and positive-generation regimes currently formalized for
Example 4.8. -/
abbrev example_4_8_positive
    {r ε ε' γ γ' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hε' : 0 < ε') (hε'r : ε' ≤ r)
    (hγ : 0 < γ) (hγε : γ < ε)
    (hγ' : 0 < γ') (hγ'ε' : γ' < ε') :=
  GenLimit.MetricSpaces.HilbertAxisReservoir.example_4_8_positive_package
    hr hε hεr hε' hε'r hγ hγε hγ' hγ'ε'

/-- Theorem 4.10's UUS and generation-in-the-limit transfer under one-sided
metric domination. -/
abbrev theorem_4_10
    {α : Type*} {ρ₁ ρ₂ : Distance α} {M r ε ε' : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : UniformlyUnboundedSupportAt ρ₂ r H)
    (hgen : GeneratableInLimitAt ρ₂ ε ε' H) :=
  GenLimit.MetricSpaces.theorem_4_10 hM hdom hUUS hgen

/-! ## Discrete specialization -/

/-- Proposition D.1 for generation in the limit. -/
abbrev proposition_D_1_limit
    {α : Type*} [DecidableEq α] {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    {H : GenLimit.Generic.LanguageClass α} :=
  GenLimit.MetricSpaces.proposition_D_1_limit
    hε0 hε1 hε'0 hε'1 (H := H)

/-- Proposition D.1 for uniform generation. -/
abbrev proposition_D_1_uniform
    {α : Type*} [DecidableEq α] {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    {H : GenLimit.Generic.LanguageClass α} :=
  GenLimit.MetricSpaces.proposition_D_1_uniform
    hε0 hε1 hε'0 hε'1 (H := H)

/-- Proposition D.1 for non-uniform generation. -/
abbrev proposition_D_1_nonuniform
    {α : Type*} [DecidableEq α] {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    {H : GenLimit.Generic.LanguageClass α} :=
  GenLimit.MetricSpaces.proposition_D_1_nonuniform
    hε0 hε1 hε'0 hε'1 (H := H)

end GenLimit.MetricSpaces.Results
