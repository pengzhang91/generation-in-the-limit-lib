import GenLimit.Paper21_GenerationInMetricSpaces.ExampleB3
import GenLimit.Paper21_GenerationInMetricSpaces.RowDiagonal
import GenLimit.Paper21_GenerationInMetricSpaces.BiLipschitzTransfer
import GenLimit.Paper21_GenerationInMetricSpaces.DiscreteReduction
import GenLimit.Paper21_GenerationInMetricSpaces.Example48Positive
import GenLimit.Paper21_GenerationInMetricSpaces.Example48
import GenLimit.Paper21_GenerationInMetricSpaces.Example49
import GenLimit.Paper21_GenerationInMetricSpaces.Example411
import GenLimit.Paper21_GenerationInMetricSpaces.FiniteClassCorollaries
import GenLimit.Paper21_GenerationInMetricSpaces.FiniteDimensionalCorollary
import GenLimit.Paper21_GenerationInMetricSpaces.FiniteUnion
import GenLimit.Paper21_GenerationInMetricSpaces.LipschitzTransfer
import GenLimit.Paper21_GenerationInMetricSpaces.NonuniformCharacterization
import GenLimit.Paper21_GenerationInMetricSpaces.RealLineThresholdNegative
import GenLimit.Paper21_GenerationInMetricSpaces.ThresholdTransfer
import GenLimit.Paper21_GenerationInMetricSpaces.ScaleMonotonicity

/-!
# Paper 21: main results for arXiv:2602.07710v2

This facade exposes the main results of Li--Raman--Tewari,
*On Generation in Metric Spaces* (arXiv:2602.07710v2).
Closure dimension characterizes uniform generation; non-uniform generation
is characterized by countable nondecreasing covers by finite-dimensional
subclasses. Further results show failure of finite-union closure and
invariance under changes of scale and bi-Lipschitz changes of metric in
doubling spaces.

The declarations below include all nine main theorems, three corollaries,
Proposition D.1, separation examples, and auxiliary lemmas on thresholds and
diagonal arguments. Generators are treated semantically; each wrapper
delegates to its canonical proof module.
-/

namespace GenLimit.MetricSpaces.Results

/-! ## Scale-closure characterizations -/

/-- Theorem 3.1: uniform generation is equivalent to finite scale-closure dimension.

`ρ` need not be a metric: the only assumption on `ρ : α → α → ℝ` is
`∀ x, ρ x x = 0`.

The paper assumes `r`-UUS and `0 < ε, ε' ≤ r`. Both directions here hold
without `r`-UUS for the conditional predicate `UniformlyGeneratableAt`, which
guarantees correctness after a covering-number threshold is reached.
For positive streams whose ranges `ε`-cover their targets, `r`-UUS and
`ε ≤ r` ensure that this threshold is eventually reached. Without threshold
reachability, the conditional guarantee can hold vacuously; see
`SemanticBoundary.lean`. -/
theorem theorem_3_1
    {α : Type*} [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x, ρ x x = 0) (hε : 0 ≤ ε) :
    UniformlyGeneratableAt ρ ε ε' H ↔ HasFiniteScaleClosureDimension ρ ε ε' H :=
  GenLimit.MetricSpaces.uniformlyGeneratableAt_iff_finite_scaleClosureDimension
    (H := H) (ε' := ε') hrefl hε

/-- Corollary 3.2: finite classes are uniformly generatable at ordered scales.

This version omits `r`-UUS and only requires `0 ≤ ε` and `ε' ≤ ε` on
the scales. See `theorem_3_1` for the discussion of threshold reachability. -/
theorem corollary_3_2
    {α : Type*} [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x, ρ x x = 0)
    (hε : 0 ≤ ε)
    (hε'ε : ε' ≤ ε) (hFinite : H.Finite) :
    UniformlyGeneratableAt ρ ε ε' H :=
  GenLimit.MetricSpaces.finite_languageClass_uniformlyGeneratable_of_le
    hrefl hε hε'ε hFinite

/-- Theorem 3.3: both directions of the finite-closure-dimension cover
characterization.

`ρ` need not be a metric: the only assumption on `ρ : α → α → ℝ` is
`∀ x, ρ x x = 0`.

This version omits `r`-UUS and only requires `0 ≤ ε` on the scales;
`ε'` is unrestricted. See `theorem_3_1` for the discussion of threshold
reachability. -/
theorem theorem_3_3
    {α : Type*} [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x, ρ x x = 0) (hε : 0 ≤ ε) :
    NonuniformlyGeneratableAt ρ ε ε' H ↔
      ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
        IsNondecreasingMetricCover H classes ∧
        ∀ n, HasFiniteScaleClosureDimension ρ ε ε' (classes n) :=
  GenLimit.MetricSpaces.nonuniform_iff_finite_scaleClosure_cover
    (H := H) (ε' := ε') hrefl hε

/-- Corollary 3.4: countable classes are non-uniformly generatable at ordered scales.

This version omits `r`-UUS and only requires `0 ≤ ε` and `ε' ≤ ε` on
the scales. See `theorem_3_1` for the discussion of threshold reachability. -/
theorem corollary_3_4
    {α : Type*} [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x, ρ x x = 0)
    (hε : 0 ≤ ε)
    (hε'ε : ε' ≤ ε) (hCountable : H.Countable) :
    NonuniformlyGeneratableAt ρ ε ε' H :=
  GenLimit.MetricSpaces.countable_languageClass_nonuniformlyGeneratable_of_le
    hrefl hε hε'ε hCountable

/-! ## Failure of finite-union closure -/

/-- Theorem 3.5: two uniformly generatable real-line classes whose union
is not generatable in the limit, for every allowed pair of scales. -/
theorem theorem_3_5
    {r ε ε' : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε' : 0 < ε')
    (hεr : ε ≤ r) (hε'r : ε' ≤ r) :
    ∃ H₁ H₂ : GenLimit.Generic.LanguageClass ℝ,
      UniformlyUnboundedSupportAt dist r H₁ ∧
      UniformlyUnboundedSupportAt dist r H₂ ∧
      UniformlyGeneratableAt dist ε ε' H₁ ∧
      UniformlyGeneratableAt dist ε ε' H₂ ∧
      ¬ GeneratableInLimitAt dist ε ε' (H₁ ∪ H₂) :=
  GenLimit.MetricSpaces.theorem_3_5_failure_of_finite_union
    hr hε hε' hεr hε'r

/-! ## Scale and metric dependence -/

/-- Theorem 4.1: UUS is invariant across positive scales on doubling
spaces. -/
theorem theorem_4_1
    {α : Type*} {ρ : Distance α}
    {H : GenLimit.Generic.LanguageClass α} {r : ℝ}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle : ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (hr : 0 < r)
    (hUUS : UniformlyUnboundedSupportAt ρ r H) :
    ∀ r' : ℝ, 0 < r' → UniformlyUnboundedSupportAt ρ r' H :=
  GenLimit.MetricSpaces.theorem_4_1_doubling_uus_scale_invariance
    hDoubling hrefl hsymm htriangle hr hUUS

/-- Theorem 4.2: uniform and non-uniform generation are invariant across
positive scales on doubling spaces.

These conditional generation equivalences hold without `r`-UUS. The proof
uses doubling and the scale-closure characterizations directly. See
`theorem_3_1` for the discussion of threshold reachability. -/
theorem theorem_4_2
    {α : Type*} {ρ : Distance α} {δ δ' ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling : IsDoublingDistance ρ)
    (hrefl : ∀ x : α, ρ x x = 0)
    (hsymm : ∀ x y : α, ρ x y = ρ y x)
    (htriangle : ∀ x y z : α, ρ x z ≤ ρ x y + ρ y z)
    (hδ : 0 < δ) (hδε : δ < ε)
    (hδ' : 0 < δ') (hδ'ε' : δ' < ε') :
    (UniformlyGeneratableAt ρ ε ε' H ↔
      UniformlyGeneratableAt ρ δ δ' H) ∧
    (NonuniformlyGeneratableAt ρ ε ε' H ↔
      NonuniformlyGeneratableAt ρ δ δ' H) := by
  have hε : 0 < ε := hδ.trans hδε
  have hε' : 0 < ε' := hδ'.trans hδ'ε'
  exact
    ⟨GenLimit.MetricSpaces.theorem_4_2_uniform_scale_invariance
        hDoubling hrefl hsymm htriangle
          hδ hδ' hε hε' hδε.le hδ'ε'.le,
      GenLimit.MetricSpaces.theorem_4_2_nonuniform_scale_invariance
        hDoubling hrefl hsymm htriangle
          hδ hδ' hε hε' hδε.le hδ'ε'.le⟩

/-- Corollary 4.3 for finite-dimensional real normed spaces. -/
theorem corollary_4_3
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : GenLimit.Generic.LanguageClass E}
    {r δ δ' ε ε' : ℝ}
    (hr : 0 < r)
    (hUUS : UniformlyUnboundedSupportAt
      (dist : E → E → ℝ) r H)
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hε : 0 < ε) (hε' : 0 < ε') :
    (UniformlyGeneratableAt (dist : E → E → ℝ) ε ε' H ↔
      UniformlyGeneratableAt (dist : E → E → ℝ) δ δ' H) ∧
    (NonuniformlyGeneratableAt (dist : E → E → ℝ) ε ε' H ↔
      NonuniformlyGeneratableAt (dist : E → E → ℝ) δ δ' H) :=
  GenLimit.MetricSpaces.corollary_4_3
    E hr hUUS hδ hδ' hε hε'

/-- Theorem 4.4 under the bi-Lipschitz hypothesis. -/
theorem theorem_4_4
    {α : Type*} {ρ₁ ρ₂ : Distance α} {M₁₂ M₂₁ : ℝ}
    {r₁ r₂ ε₁ ε₁' ε₂ ε₂' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hDoubling₁ : IsDoublingDistance ρ₁)
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
    (hε₂ : 0 < ε₂) (hε₂' : 0 < ε₂') :
    (UniformlyUnboundedSupportAt ρ₁ r₁ H ↔
      UniformlyUnboundedSupportAt ρ₂ r₂ H) ∧
    (UniformlyGeneratableAt ρ₁ ε₁ ε₁' H ↔
      UniformlyGeneratableAt ρ₂ ε₂ ε₂' H) ∧
    (NonuniformlyGeneratableAt ρ₁ ε₁ ε₁' H ↔
      NonuniformlyGeneratableAt ρ₂ ε₂ ε₂' H) :=
  GenLimit.MetricSpaces.theorem_4_4_bilipschitz
    (H := H)
    hDoubling₁ hrefl₁ hsymm₁ htriangle₁
    hrefl₂ hsymm₂ htriangle₂ hM₁₂ hM₂₁ hdom
    hr₁ hr₂ hε₁ hε₁' hε₂ hε₂'

/-- Complete positive and negative threshold statement of Example 4.5. -/
theorem example_4_5
    {ε : ℝ} (hεpos : 0 < ε) (hεlt : ε < 1) :
    UniformlyUnboundedSupportAt RealLineThreshold.realDistance 1
        RealLineThreshold.languageClass ∧
      GeneratableInLimitAt RealLineThreshold.realDistance ε 1
        RealLineThreshold.languageClass ∧
      ¬ GeneratableInLimitAt RealLineThreshold.realDistance 1 1
        RealLineThreshold.languageClass :=
  GenLimit.MetricSpaces.RealLineThreshold.example_4_5_complete
    hεpos hεlt

/-- Theorem 4.6: generation in the limit is monotone under decreasing
adversary and generator novelty scales. -/
theorem theorem_4_6
    {α : Type*} {ρ : Distance α}
    {H : GenLimit.Generic.LanguageClass α}
    {δ δ' ε ε' : ℝ}
    (hδε : δ ≤ ε) (hδ'ε' : δ' ≤ ε')
    (hgen : GeneratableInLimitAt ρ ε ε' H) :
    GeneratableInLimitAt ρ δ δ' H :=
  GenLimit.MetricSpaces.theorem_4_6_limit_scale_monotonicity
    hδε hδ'ε' hgen

/-- Theorem 4.7: uniform and non-uniform generation are preserved when the
adversary scale increases and the generator novelty scale decreases. -/
theorem theorem_4_7
    {α : Type*} {ρ : Distance α}
    {H : GenLimit.Generic.LanguageClass α}
    {ε ε' δ δ' : ℝ}
    (hεδ : ε ≤ δ) (hδ'ε' : δ' ≤ ε') :
    (UniformlyGeneratableAt ρ ε ε' H →
      UniformlyGeneratableAt ρ δ δ' H) ∧
    (NonuniformlyGeneratableAt ρ ε ε' H →
      NonuniformlyGeneratableAt ρ δ δ' H) :=
  ⟨GenLimit.MetricSpaces.theorem_4_7_uniform_scale_monotonicity
      hεδ hδ'ε',
    GenLimit.MetricSpaces.theorem_4_7_nonuniform_scale_monotonicity
      hεδ hδ'ε'⟩

/-- Example 4.8: the explicit class is `r`-UUS and has independent sharp
thresholds for limit generation. Below both thresholds, the displayed causal
generator witnesses generation. -/
theorem example_4_8
    {r ε ε' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r)
    (hε' : 0 < ε') (hε'r : ε' ≤ r) :
    let H := HilbertAxisReservoir.example48LanguageClass r ε ε'
    UniformlyUnboundedSupportAt HilbertAxisReservoir.hilbertDistance r H ∧
      (∀ γ γ' : ℝ, 0 < γ → γ ≤ r → 0 < γ' → γ' ≤ r →
        (GeneratableInLimitAt HilbertAxisReservoir.hilbertDistance γ γ' H ↔
          γ < ε ∧ γ' < ε')) ∧
      ∀ γ γ' : ℝ, 0 < γ → γ < ε → 0 < γ' → γ' < ε' →
        IsLimitGeneratorAt HilbertAxisReservoir.hilbertDistance γ γ'
          (HilbertAxisReservoir.example48CausalGenerator ε ε' γ') H := by
  obtain ⟨hUUS, hclassification⟩ :=
    GenLimit.MetricSpaces.HilbertAxisReservoir.example_4_8_classification
      hr hε hεr hε' hε'r
  refine ⟨hUUS, hclassification, ?_⟩
  intro γ γ' hγ hγε hγ' hγ'ε'
  exact GenLimit.MetricSpaces.HilbertAxisReservoir.example48CausalGenerator_isLimit
    hr hε hεr hε' hε'r hγ hγε hγ' hγ'ε'

/-- Example 4.9: all four scale-dependent generation regimes.

Here `dist` is Mathlib's standard `ℓ²` distance on
`HilbertAxisReservoir.Hilbert2`, inferred from the type of `H`. It is the same
function as `HilbertAxisReservoir.hilbertDistance` used in Example 4.8. -/
theorem example_4_9
    {r ε₁ ε₂ ε' : ℝ}
    (hr : 0 < r) (hε₁ : 0 < ε₁) (hε₁₂ : ε₁ ≤ ε₂) (hε₂r : ε₂ ≤ r)
    (hε' : 0 < ε') (hε'r : ε' ≤ r) :
    ∃ H : GenLimit.Generic.LanguageClass HilbertAxisReservoir.Hilbert2,
      UniformlyUnboundedSupportAt dist r H ∧
      (∀ γ γ', ε₂ ≤ γ → γ ≤ r → 0 < γ' → γ' < ε' →
        UniformlyGeneratableAt dist γ γ' H) ∧
      (∀ γ γ', ε₁ ≤ γ → γ < ε₂ → 0 < γ' → γ' < ε' →
        NonuniformlyGeneratableAt dist γ γ' H ∧ ¬ UniformlyGeneratableAt dist γ γ' H) ∧
      (∀ γ γ', 0 < γ → γ < ε₁ → 0 < γ' → γ' < ε' →
        GeneratableInLimitAt dist γ γ' H ∧ ¬ NonuniformlyGeneratableAt dist γ γ' H) ∧
      (∀ γ γ', 0 < γ → γ ≤ r → ε' ≤ γ' → γ' ≤ r →
        ¬ GeneratableInLimitAt dist γ γ' H) :=
  GenLimit.MetricSpaces.HilbertAxisReservoir.example_4_9 hr hε₁ hε₁₂ hε₂r hε' hε'r

/-- Theorem 4.10: UUS and generation in the limit transfer independently
under one-sided metric domination. Each implication takes its own source
property as a premise. -/
theorem theorem_4_10
    {α : Type*} {ρ₁ ρ₂ : Distance α} {M r ε ε' : ℝ}
    (hM : 0 < M) (hdom : DistanceDominatedBy ρ₂ ρ₁ M)
    {H : GenLimit.Generic.LanguageClass α} :
    (UniformlyUnboundedSupportAt ρ₂ r H →
      UniformlyUnboundedSupportAt ρ₁ (r / M) H) ∧
    (GeneratableInLimitAt ρ₂ ε ε' H →
      GeneratableInLimitAt ρ₁ (ε / M) (ε' / M) H) :=
  ⟨GenLimit.MetricSpaces.theorem_4_10_uus_transfer hM hdom,
    GenLimit.MetricSpaces.theorem_4_10_limit_transfer hM hdom⟩

/-- Example 4.11: the same Hilbert class is uniformly generatable for the
ordinary metric but not non-uniformly generatable for a bi-Lipschitz equivalent metric. -/
theorem example_4_11 {r : ℝ} (hr : 0 < r) :
    ∃ H : GenLimit.Generic.LanguageClass HilbertAxisReservoir.Hilbert2,
      ∃ metric' : MetricSpace HilbertAxisReservoir.Hilbert2,
        MutuallyLipschitzDominated dist
          (@dist HilbertAxisReservoir.Hilbert2 metric'.toDist) 1 2 ∧
        UniformlyUnboundedSupportAt dist r H ∧
        UniformlyUnboundedSupportAt (@dist HilbertAxisReservoir.Hilbert2 metric'.toDist) r H ∧
        (∀ ε : ℝ, 0 < ε → ε < r → UniformlyGeneratableAt dist ε ε H) ∧
        (∀ ε : ℝ, 0 < ε → ε < r →
          ¬ NonuniformlyGeneratableAt (@dist HilbertAxisReservoir.Hilbert2 metric'.toDist) ε ε H) := by
  obtain ⟨H, metric', _, hproperties⟩ :=
    GenLimit.MetricSpaces.HilbertAxisReservoir.example_4_11 hr
  exact ⟨H, metric', hproperties⟩

/-! ## Discrete specialization -/

/-- Proposition D.1: at independent scales `ε` and `ε'` in `[0, 1)`, the
discrete metric recovers the three discrete generation notions.

`discreteDistance`, defined in `DiscreteReduction.lean`, assigns distance `0`
to equal points and `1` to distinct points. The argument `(α := α)` specifies
the underlying type; `[DecidableEq α]` supplies the equality test.

The paper assumes a countable example space and `r`-UUS. These equivalences
hold for arbitrary `α` with `[DecidableEq α]`, without a UUS assumption.
The UUS/infinite-support equivalence used in the paper's proof is available
separately as `discrete_uus_iff`. -/
theorem proposition_D_1
    {α : Type*} [DecidableEq α] {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1) :
    (GeneratableInLimitAt (discreteDistance (α := α)) ε ε' H ↔
      GenLimit.LiRamanTewari.GeneratableInLimit H) ∧
    (UniformlyGeneratableAt (discreteDistance (α := α)) ε ε' H ↔
      GenLimit.LiRamanTewari.UniformlyGeneratable H) ∧
    (NonuniformlyGeneratableAt (discreteDistance (α := α)) ε ε' H ↔
      GenLimit.LiRamanTewari.NonuniformlyGeneratable H) :=
  ⟨GenLimit.MetricSpaces.proposition_D_1_limit
      hε0 hε1 hε'0 hε'1 (H := H),
    GenLimit.MetricSpaces.proposition_D_1_uniform
      hε0 hε1 hε'0 hε'1 (H := H),
    GenLimit.MetricSpaces.proposition_D_1_nonuniform
      hε0 hε1 hε'0 hε'1 (H := H)⟩

/-- Appendix Lemma C.1: transfer of target-dependent thresholds. -/
theorem lemma_C_1
    {α : Type*} {ρ : Distance α} {ε ε' : ℝ}
    {H family : GenLimit.Generic.LanguageClass α} {q : ℕ} (hq : 0 < q)
    (T : Fin q → GenLimit.Generic.Language α) (hempty : (⋂ i, T i) = ∅)
    (hTargets : ∀ S, S ∈ family → ∀ i, S ∪ T i ∈ H)
    {G : GenLimit.Generic.Generator α} (hG : IsNonuniformGeneratorAt ρ ε ε' G H) :
    ∀ S, S ∈ family → ∃ d : ℕ,
      ∀ stream : GenLimit.Generic.Stream α, GenLimit.Generic.StreamIn stream S →
      ∀ t, CoveringNumberAtLeast ρ ε (GenLimit.Generic.sample stream t : Set α) d →
      ∀ s, t ≤ s → MetricCorrectAt ρ ε' G S stream s :=
  GenLimit.MetricSpaces.lemma_C_1_threshold_transfer hq T hempty hTargets hG

/-- Appendix Lemma C.2: the full row-array obstruction to limit generation. -/
theorem lemma_C_2
    {α : Type*} {ρ : Distance α} {ε ε' : ℝ} {H : GenLimit.Generic.LanguageClass α}
    {fixed : List α} {row : ℕ → GenLimit.Generic.Stream α} {A : ℕ → Set α}
    (criterion : RowDiagonal.Criterion ρ ε ε' H fixed row A) :
    ¬ GeneratableInLimitAt ρ ε ε' H :=
  GenLimit.MetricSpaces.lemma_C_2_not_generatable criterion

/-- Example B.3: a two-hypothesis Hilbert obstruction at reversed scales. -/
theorem example_B_3
    {r ε ε' : ℝ} (hr : 0 < r)
    (hε : 0 < ε) (hεε' : ε < ε') (_hε'r : ε' ≤ r) :
    ∃ H : GenLimit.Generic.LanguageClass HilbertAxisReservoir.Hilbert2,
      H.ncard = 2 ∧ UniformlyUnboundedSupportAt dist r H ∧
      ¬ NonuniformlyGeneratableAt dist ε ε' H :=
  GenLimit.MetricSpaces.example_B_3 hr hε hεε' _hε'r

end GenLimit.MetricSpaces.Results
