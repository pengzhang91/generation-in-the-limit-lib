# Paper 21: On Generation in Metric Spaces

Jiaxun Li, Vinod Raman, and Ambuj Tewari,
[arXiv:2602.07710v2](https://arxiv.org/abs/2602.07710v2).
The formalized source is the unannotated 33-page PDF with SHA-256
`b4e14e33fce18aa5d970a49d4886a647d9de888e8de29fab12ff8cda0afacfbc`.

- Lean umbrella: `GenLimit.Paper21_GenerationInMetricSpaces`.
- Main-results facade: [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean).
- Scope: deterministic semantic mathematics, generally using classical choice.
  No extracted algorithm, computability theorem, or runtime bound is claimed.
- Human audit: Peng Zhang reported completion of Level 1 for all 20 theorems
  in `Results/Overview.lean` at checkpoint `7bdc137` on 2026-11-01 (reporting
  date; completion date not separately specified). Statement and defining-interface
  applicability is recorded in the [human-audit ledger](../AuditRecords/Human/README.md)
  and guarded by the [fingerprint manifest](../AuditRecords/Human/Fingerprints/P21_V2OverviewLevel1.json).
- Coverage: all nine main theorems, three corollaries, Proposition D.1,
  and all five examples (4.5, 4.8, 4.9, 4.11, B.3) are proved. Lemmas
  2.1, C.1, and C.2 and the orthogonal covering estimate are also complete.
  Appendix A supplies background reuse; Appendix E is outside this semantic
  scope. No implementation-level result is claimed.

## Claim-to-Lean map

Unless qualified below, facade names have prefix
`GenLimit.MetricSpaces.Results`; canonical proofs have prefix
`GenLimit.MetricSpaces`.

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definitions 2.1–2.7 and 3.1 | [`Definitions.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Definitions.lean) | Full semantic interface | Closed neighborhoods use `∀ η > r, ∃ center, distance < η`, including the empty-set case. Finite closure dimension is expressed as a bound on witnesses, rather than an extended-natural supremum. |
| Lemma 2.1 | `lemma_2_1_uus_mono`, [`ScaleMonotonicity.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ScaleMonotonicity.lean) | Full | The stronger weak-radius inequality is also available as `UniformlyUnboundedSupportAt.mono_radius`. |
| Theorem 3.1; Lemmas B.1–B.2 | `theorem_3_1`; [`UniformNecessity.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/UniformNecessity.lean), [`UniformSufficiency.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/UniformSufficiency.lean) | Full | Both directions for the internal-cover dimension. The core proof needs only a nonempty ambient type, reflexivity, and nonnegative adversary radius. |
| Corollary 3.2 | `corollary_3_2`, [`FiniteClassCorollaries.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteClassCorollaries.lean) | Full | Uses a finite upper bound over the finitely many version-space cores. The overview requires only reflexivity, a nonempty ambient type, nonnegative adversary scale, and ordered scales; the canonical corollary retains the source UUS and scale hypotheses. |
| Theorem 3.3; Lemmas B.4–B.5 | `theorem_3_3`, [`NonuniformCharacterization.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/NonuniformCharacterization.lean) | Full | A nondecreasing countable cover by finite-dimensional subclasses is equivalent to non-uniform generation. The intermediate uniform-cover equivalence remains available as `GenLimit.MetricSpaces.nonuniform_iff_nondecreasing_uniform_cover` in `NonuniformCharacterization.lean`, without a separate numbered overview wrapper. |
| Corollary 3.4 | `corollary_3_4`, [`FiniteClassCorollaries.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteClassCorollaries.lean) | Full | Finite prefixes of an ambient enumeration are intersected with the class, handling empty and finite classes as well. The overview uses the same weaker metric and scale hypotheses as Corollary 3.2; the canonical corollary retains the source UUS and scale hypotheses. |
| Theorem 3.5 | `theorem_3_5`, [`FiniteUnion.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteUnion.lean) | Full | For each allowed scale pair, two real-line classes are r-UUS and uniformly generatable, but their union is not limit-generatable. The proof constructs a target-valued diagonal and two fixed covered targets. |
| Definition 4.1; Theorem 4.1 | `IsDoublingDistance`, `theorem_4_1`, [`DoublingUUS.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/DoublingUUS.lean) | Full | Iterated ball covers internalize finite covers and prove stream-based UUS at all positive scales. |
| Theorem 4.2 | `theorem_4_2`, [`DoublingGeneration.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/DoublingGeneration.lean) | Full | Uniform and non-uniform generation; quantitative sample-cover comparison and internal closure-cover refinement are proved. The overview omits `r`-UUS and the unused radius `r` for these conditional generation equivalences; the canonical combined theorem retains the source hypotheses. |
| Corollary 4.3 | `corollary_4_3`, [`FiniteDimensionalCorollary.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteDimensionalCorollary.lean) | Full | Finite-dimensional real normed spaces. Compactness supplies doubling; a common smaller scale compares arbitrary positive pairs. |
| Theorem 4.4; Definition D.1 | `theorem_4_4`, `MutuallyLipschitzDominated`, [`BiLipschitzTransfer.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/BiLipschitzTransfer.lean) | Full | The two positive domination constants encode the source's two-sided bi-Lipschitz bounds. Only the first metric is assumed doubling. Radii may differ between metrics; raw generation equivalences hold even without UUS. |
| Example 4.5 | `example_4_5`, [`RealLineThreshold.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/RealLineThreshold.lean), [`RealLineThresholdNegative.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/RealLineThresholdNegative.lean) | Full | UUS and both threshold directions. A concrete target-valued diagonal proves the negative direction directly, without assuming Lemma C.2. |
| Theorem 4.6 | `theorem_4_6`, [`ScaleMonotonicity.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ScaleMonotonicity.lean) | Full | The same limit generator works when both scales decrease. |
| Theorem 4.7 | `theorem_4_7`, [`ScaleMonotonicity.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ScaleMonotonicity.lean) | Full | Increasing the adversary scale and decreasing the generator scale preserves each conditional guarantee. The overview combines the uniform and non-uniform implications in a conjunction, so each can be applied independently. |
| Example 4.8 | `example_4_8`, [`Example48Positive.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example48Positive.lean), [`Example48.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example48.lean), [`Example48Rows.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example48Rows.lean), [`Example48Negative.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example48Negative.lean) | Full | The positive-index source class is `r`-UUS. Limit generation holds exactly below both scale thresholds; both negative regimes include equality. The overview identifies `example48LanguageClass` explicitly and includes correctness of `example48CausalGenerator` below both thresholds. |
| Example 4.9 | `example_4_9`, [`Example49.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example49.lean), [`Example49Positive.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example49Positive.lean), [`Example49Negative.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example49Negative.lean), [`Example49UniformLower.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example49UniformLower.lean) | Full | Four disjoint coordinate families, positive-exponent towers, `r`-UUS, and all four regimes including equality boundaries. The lower bounds use common-part threshold transfer and finite-block diagonal selection. |
| Theorem 4.10 | `theorem_4_10`, [`LipschitzTransfer.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/LipschitzTransfer.lean) | Full | The overview states independent UUS and limit-generation implications with the exact rescaled radii. Each uses its corresponding source property together with the shared one-sided domination hypotheses. |
| Example 4.11 | `example_4_11`, [`WeightedHilbert.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/WeightedHilbert.lean), [`Example411.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example411.lean), [`Example411Negative.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example411Negative.lean) | Full | The genuine weighted metric has the same topology and global bounds `ρ/2 ≤ ρ′ ≤ ρ`. The same dyadic-layer class is `r`-UUS for both metrics, uniformly generatable for `ρ`, and not non-uniformly generatable for `ρ′` at every `ε ∈ (0,r)`. |
| Appendix A | [`DiscreteReduction.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/DiscreteReduction.lean), P02 definitions | Infrastructure only / background reuse | A.1–A.3 recall prior results; no new P21 wrappers for these background theorems are claimed. Proposition D.1 supplies the exact semantic comparison with P02. |
| Example B.3 | `example_B_3`, [`ExampleB3.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ExampleB3.lean) | Full | Exactly two target supports in genuine real Hilbert space, r-UUS, and failure of non-uniform generation at reversed scales. The proof combines Lemma C.1 with unbounded orthogonal prefix covering numbers. |
| Lemma C.1 | `lemma_C_1`, [`ThresholdTransfer.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ThresholdTransfer.lean) | Full | A maximum of finitely many target thresholds forces outputs into their common part. No UUS or coverage assumption is imposed on that common part. The finite family is explicitly nonempty. |
| Appendix C.1, estimate (1) | `GenLimit.MetricSpaces.orthogonal_covering_estimate`, [`OrthogonalCovering.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/OrthogonalCovering.lean) | Full | Canonical helper used through covering-number lemmas in Examples 4.9, 4.11, and B.3; no separate overview wrapper. Arbitrary ambient centers in any real inner product space. Natural-number lower bounds and prefix divergence for infinite orthogonal subfamilies are also proved. |
| Lemma C.2 | `lemma_C_2`, [`RowDiagonal.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/RowDiagonal.lean) | Full | `RowDiagonal.Criterion` packages all three source hypotheses, including target membership of every prescribed observation. Exact finite ledgers and an append-only history chain produce the final target and infinitely many failure rounds. Once the criterion is given, no extra UUS or metric law is needed. |
| Proposition D.1 | `proposition_D_1`, [`DiscreteReduction.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/DiscreteReduction.lean) | Full | At scales in `[0,1)`, UUS is equivalent to infinite support, coverage is enumeration, and all three generation notions recover the discrete semantics. The proof generalizes the source's countable ambient domain. The overview combines only the three generation equivalences at independent scales `ε, ε' ∈ [0,1)`, without a UUS assumption. The UUS/infinite-support equivalence remains separately available as `discrete_uus_iff`; the overview has no `r` parameter. |
| Appendix E | No executable endpoint | Outside scope | The oracle/computability discussion is not an extracted implementation or a complexity theorem in this development. |

## Formalization conventions and dependencies

Languages are sets, finite histories use zero-based `Fin t → α`, and positive
streams may repeat points. The abstract results do not assume separability;
each statement exposes the required distance properties and nonempty-domain
conditions. Example 4.11 indexes its first layer by zero (amplitude `4r`) and
halves even coordinates in the weighted metric.

Shared definitions and finite-history tools come from `Core.GenericGeneration`,
`Core.VersionSpace`, `Support.CountableCovers`, `Support.HistoryChain`, and
`Support.StreamPrefix`. P02 supplies the discrete generation interfaces for
Proposition D.1.

`CoveringGeometry`, `BlockDiagonal`, and `ReservoirGeneration` remain local to
P21 because they depend on its neighborhood, covering, and generation
predicates. Examples 4.9 and 4.11 reuse the semantic common-core choice
generator from `UniformSufficiency`. Assumption differences and the Example
4.8 proof detail are recorded in the following section.

## Assumption differences and proof detail

Some Lean statements use fewer assumptions than the paper. The tables list
the changes. Other assumptions still apply. Full statements are in
`Results/Overview.lean`.

### UUS and scale assumptions

| Result | Differences in Lean |
|---|---|
| Theorems 3.1 and 3.3 | No `r`-UUS assumption. The type is nonempty and `0 ≤ ε`. There is no restriction on `ε'`. |
| Corollaries 3.2 and 3.4 | No `r`-UUS assumption. The type is nonempty. The scales satisfy `0 ≤ ε` and `ε' ≤ ε`. The class is finite for 3.2 and countable for 3.4. |
| Theorems 4.2 and 4.4 | The uniform/non-uniform equivalences need no UUS assumption. Theorem 4.4 also gives the UUS equivalence. |
| Theorems 4.6 and 4.7 | No UUS assumption. The scale inequalities and the starting generation property are still needed. |
| Theorem 4.10 | The limit-generation implication needs no UUS assumption. The UUS implication assumes UUS for `ρ₂`. |
| Proposition D.1 | No UUS or countability assumption. Equality is decidable. Both scales lie in `[0,1)`. |

Uniform and non-uniform generation give correct outputs after the covering
number reaches a threshold. If this never happens, the condition alone need
not give any correct output. Consider a positive stream that `ε`-covers its
target. Under `r`-UUS and `ε ≤ r`, it reaches every finite threshold.
`SemanticBoundary.lean` proves this fact.

Theorem 4.1 keeps UUS as an assumption. Theorem 3.5 constructs classes with
`r`-UUS.

### Distance-function assumptions

`Distance α` means `α → α → ℝ`. The table lists the needed properties of
these functions. All other assumptions still apply.

| Result | Requirements on `ρ` |
|---|---|
| Theorems 3.1 and 3.3; Corollaries 3.2 and 3.4 | Only `ρ x x = 0` is needed. No other metric property is required. |
| Theorems 4.6 and 4.7 | Any function `ρ : α → α → ℝ` works. |
| Theorem 4.10 | Require `ρ₂ x y ≤ M * ρ₁ x y` and `0 < M`. No other metric property is needed. |
| Theorems 4.1 and 4.2 | Require `ρ x x = 0`, symmetry, the triangle inequality, and doubling. Distinct points may have distance zero. |
| Theorem 4.4 | Both functions have self-distance zero, symmetry, and the triangle inequality. The first is doubling. The mutual Lipschitz bounds are still needed. Distinct points may have distance zero. |
| Lemmas C.1 and C.2 | Any function `ρ : α → α → ℝ` works. Keep the other assumptions in each lemma. C.2 uses `RowDiagonal.Criterion`. |

For Theorems 4.1, 4.2, and 4.4, the listed conditions imply `0 ≤ ρ x y`:
`0 = ρ x x ≤ ρ x y + ρ y x = 2 * ρ x y`.
Thus real-valued pseudometrics are enough, with the other stated assumptions.

Theorem 3.5 and the examples use concrete metrics. Corollary 4.3 uses the
metric from a norm. Proposition D.1 uses the discrete metric.

### Example 4.8: zero-exponent convention

Case 2 in Appendix C.3 needs a clear exponent convention. Lean includes zero
in `ℕ`. Thus `g_(2*k^0+1) = g_3` belongs to every tower.

The paper starts with only `y₁ = 0`. With zero exponents, its cover at the
generator scale does not show how `g_3` is covered. Lean starts with
`[0, g_3]`. The fresh rows use positive exponents. This gives the required
cover. The target class and the example's conclusion stay the same.

If the authors intend `n ≥ 1`, this issue does not arise.

## Verification

Checks passed on 2026-11-01 with Lean 4.24.0 / Mathlib v4.24.0:
P21 targeted builds, full `lake build`, registry and declaration-index checks,
and generated/curated logical-dependency audits. P21 has no proof holes,
paper-local axioms, or build warnings. Existing unrelated build warnings and
historical audit-review flags remain recorded separately.
