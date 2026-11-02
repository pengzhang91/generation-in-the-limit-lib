# Paper 21: On Generation in Metric Spaces

Jiaxun Li, Vinod Raman, and Ambuj Tewari,
[arXiv:2602.07710v2](https://arxiv.org/abs/2602.07710v2), revision dated
2026-10-24 (the supplied PDF title page prints October 27, 2026).
The formalized source is the original, unannotated 33-page v2 PDF with SHA-256
`b4e14e33fce18aa5d970a49d4886a647d9de888e8de29fab12ff8cda0afacfbc`.
The authors' earlier emailed revision is not the pinned source.

- Lean umbrella: `GenLimit.Paper21_GenerationInMetricSpaces`.
- Main-results facade: [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean).
- Scope: deterministic semantic mathematics, generally using classical choice.
  No extracted algorithm, computability theorem, runtime bound, or independent
  human source-correspondence audit is claimed.
- Coverage: all nine main theorems, three corollaries, Proposition D.1,
  and all five examples (4.5, 4.8, 4.9, 4.11, B.3) are proved. Lemmas
  2.1, C.1, and C.2 and the orthogonal covering estimate are also complete.
  Appendix A supplies background reuse; Appendix E is outside this semantic
  scope. No implementation-level result is claimed.

## Changes for v2

Definition 2.3 now requires nonempty support and divergence of finite-prefix
covering numbers for every positive covering stream. The Lean interface
implements this directly; `eventually_coveringNumberAtLeast` proves the
source's eventual form. `InfiniteCoveringSupportAt` is only a geometric
helper, not a synonym for UUS.

Definition 2.2 still permits ambient cover centers. Definition 3.1 instead
requires a finite cover whose centers belong to the common closure. This
internal-center distinction is explicit in `HasFiniteInternalCover` and
`IsScaleClosureWitness`. Consequently Theorems 3.1 and 3.3 are now full
biconditionals without an extra internalization premise.

Theorem 3.5 is the revised real-line finite-union obstruction. Theorem 4.4
uses bi-Lipschitz equivalence and derives doubling of the second metric from
that of the first. Example 4.8 uses the actual v2 choice `u_k = 4r e_k` and
waits for a marker with `k ≥ 2`.

The current public tree contains the v2 development. The v1-only diagnostic
modules, old Theorem 3.6, and old repair-only API have been removed. Normal
Git history is retained; a separate local snapshot preserves the previous
source, dependencies' version pins, and PDF. No history rewrite is needed.

## Claim-to-Lean map

Unless qualified below, facade names have prefix
`GenLimit.MetricSpaces.Results`; canonical proofs have prefix
`GenLimit.MetricSpaces`.

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definitions 2.1–2.7 and 3.1 | [`Definitions.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Definitions.lean) | Full semantic interface | Closed neighborhoods use `∀ η > r, ∃ center, distance < η`, including the empty-set case. Finite closure dimension is expressed as a bound on witnesses, rather than an extended-natural supremum. |
| Lemma 2.1 | `lemma_2_1_uus_mono`, [`ScaleMonotonicity.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ScaleMonotonicity.lean) | Full | The stronger weak-radius inequality is also available as `UniformlyUnboundedSupportAt.mono_radius`. |
| Theorem 3.1; Lemmas B.1–B.2 | `theorem_3_1`; [`UniformNecessity.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/UniformNecessity.lean), [`UniformSufficiency.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/UniformSufficiency.lean) | Full | Both directions for the revised internal-cover dimension. The core proof needs only a nonempty ambient type, reflexivity, and nonnegative adversary radius. |
| Corollary 3.2 | `corollary_3_2`, [`FiniteClassCorollaries.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteClassCorollaries.lean) | Full | Uses a finite upper bound over the finitely many version-space cores. The overview requires only reflexivity, a nonempty ambient type, nonnegative adversary scale, and ordered scales; the canonical corollary retains the source UUS and scale hypotheses. |
| Theorem 3.3; Lemmas B.4–B.5 | `theorem_3_3`, [`NonuniformCharacterization.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/NonuniformCharacterization.lean) | Full | A nondecreasing countable cover by finite-dimensional subclasses is equivalent to non-uniform generation. The intermediate uniform-cover equivalence remains available as `GenLimit.MetricSpaces.nonuniform_iff_nondecreasing_uniform_cover` in `NonuniformCharacterization.lean`, without a separate numbered overview wrapper. |
| Corollary 3.4 | `corollary_3_4`, [`FiniteClassCorollaries.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteClassCorollaries.lean) | Full | Finite prefixes of an ambient enumeration are intersected with the class, handling empty and finite classes as well. The overview uses the same weaker metric and scale hypotheses as Corollary 3.2; the canonical corollary retains the source UUS and scale hypotheses. |
| Theorem 3.5 | `theorem_3_5`, [`FiniteUnion.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteUnion.lean) | Full | For each allowed scale pair, two real-line classes are r-UUS and uniformly generatable, but their union is not limit-generatable. The proof constructs a target-valued diagonal and two fixed covered targets. |
| Definition 4.1; Theorem 4.1 | `IsDoublingDistance`, `theorem_4_1`, [`DoublingUUS.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/DoublingUUS.lean) | Full | Iterated ball covers internalize finite covers and prove the revised stream-based UUS at all positive scales. |
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
| Example B.3 | `example_B_3`, [`ExampleB3.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ExampleB3.lean) | Full | Exactly two target supports in genuine real Hilbert space, revised r-UUS, and failure of non-uniform generation at reversed scales. The proof combines Lemma C.1 with unbounded orthogonal prefix covering numbers. |
| Lemma C.1 | `lemma_C_1`, [`ThresholdTransfer.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ThresholdTransfer.lean) | Full | A maximum of finitely many target thresholds forces outputs into their common part. No UUS or coverage assumption is imposed on that common part. The finite family is explicitly nonempty. |
| Appendix C.1, estimate (1) | `GenLimit.MetricSpaces.orthogonal_covering_estimate`, [`OrthogonalCovering.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/OrthogonalCovering.lean) | Full | Canonical helper used through covering-number lemmas in Examples 4.9, 4.11, and B.3; no separate overview wrapper. Arbitrary ambient centers in any real inner product space. Natural-number lower bounds and prefix divergence for infinite orthogonal subfamilies are also proved. |
| Lemma C.2 | `lemma_C_2`, [`RowDiagonal.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/RowDiagonal.lean) | Full | `RowDiagonal.Criterion` packages all three source hypotheses, including target membership of every prescribed observation. Exact finite ledgers and an append-only history chain produce the final target and infinitely many failure rounds. Once the criterion is given, no extra UUS or metric law is needed. |
| Proposition D.1 | `proposition_D_1`, [`DiscreteReduction.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/DiscreteReduction.lean) | Full | At scales in `[0,1)`, UUS is equivalent to infinite support, coverage is enumeration, and all three generation notions recover the discrete semantics. The proof generalizes the source's countable ambient domain. The overview combines only the three generation equivalences at independent scales `ε, ε' ∈ [0,1)`, without a UUS assumption. The UUS/infinite-support equivalence remains separately available as `discrete_uus_iff`; the overview has no `r` parameter. |
| Appendix E | No executable endpoint | Outside scope | The oracle/computability discussion is not an extracted implementation or a complexity theorem in this development. |

## Interface and reuse notes

The distance is usually an explicit real-valued kernel; each theorem states
only the metric laws used. The paper assumes a separable metric domain, but
the main abstract proofs do not need separability. The existence of a total
generator requires a nonempty ambient type in the relevant directions.
Languages are extensional sets, and finite histories use `Fin t → α` with
zero-based indexing. No injectivity is imposed on positive streams, matching
the quantified source definitions rather than an informal reading of “new”.

For Example 4.8, all three index sets are infinite subsets of the positive
naturals, as in the source. Exponents are natural numbers in the displayed
construction. The fixed observations `[0, g_3]` in Lemma C.2 account for
exponent zero; the fresh reservoirs use positive exponents. The lower-bound
rows use distinct odd-prime bases, including the zeroth row, which provides
the same disjoint prime-power construction as the source's base-two row.

Examples 4.9 and 4.11 use the same semantic common-core choice generator
from `UniformSufficiency`: a structured observation certifies a fresh
reservoir in every consistent target. This proves causal generator existence
without implementing real-number recognition. Example 4.9 retains the four
disjoint residue classes and positive power exponents of the source.
Example 4.11 indexes the first layer by zero, with amplitude `4r`; the
weighted metric multiplies even coordinates by `1/2` before taking the norm.
The critical layer satisfies `α/2 ≤ ε < α`, so even descendants are
non-novel even at equality. Disjoint positive odd-part index sets complete
the other layers. `BlockDiagonal` reuses one finite-block selection proof
for the lower bounds, while `ReservoirGeneration` shares the finite-sample
freshness argument. These helpers remain P21-local because they use its
metric-generation interfaces.

Uniform/non-uniform predicates keep UUS separate from the conditional
correctness guarantee. [`SemanticBoundary.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/SemanticBoundary.lean)
proves that v2 UUS supplies threshold reachability at admissible adversary
scales and hence limit correctness for the same generator. Its small raw
predicate counterexample concerns classes without UUS, not the v2 theorems.

Shared infrastructure is reused from `Core.GenericGeneration`,
`Core.VersionSpace`, `Support.CountableCovers`, `Support.HistoryChain`, and
`Support.StreamPrefix`. P02 supplies the earlier discrete interfaces for
Proposition D.1. There is no longer a P21 dependency on P10's union-separation
construction. `CoveringGeometry` remains P21-local because its statements
use P21's neighborhood and covering interfaces; moving it to Core would
invert that dependency. The local cross-paper equivalence record is updated
but remains untracked and is not linked as a public artifact.

## Verification and remaining scope

The paper umbrella, generated claim audit, declaration index, and repository
build are the integration checks. No paper-local axiom or proof hole is
used. The registry has fourteen full claim groups: nine cover the thirteen
main theorem/corollary/proposition items, and five cover the examples. The
additional auxiliary lemmas are mapped in the table above. The listed
semantic scope has no remaining formalization gap; Appendix A is background
reuse and Appendix E implementation/oracle discussion remains outside scope.

The development has targeted module and paper-umbrella verification, a final
full incremental `lake build`, and generated/curated logical-dependency
audits. Existing warnings outside P21 and historical human-audit review
flags are reported separately; kernel checking is not an independent human
source-correspondence audit.

Pre-commit verification on 2026-11-01 (Lean 4.24.0 / Mathlib v4.24.0):

- Each new proof module and the P21 umbrella passed its targeted build.
- The final repository-wide incremental `lake build` passed: 3863 jobs.
  P21 produced no warnings; the seven existing warnings are in P17 and P31.
- Registry validation and regeneration passed: 30 papers, 409 claims,
  557 claim-linked declarations. All fourteen P21 claim groups are full.
- Declaration-index regeneration passed: 11192 declarations, including all
  new public endpoints and their canonical proof declarations.
- `scripts/check_lean_audit.sh` passed both generated and curated audits.
  The new results use only `propext`, `Classical.choice`, and `Quot.sound`.
- The historical audit-fingerprint check passed with six existing
  `needs-review` warnings for P0, P01, and P39; no baseline was promoted.
- The P21 source scan found no `sorry`, `admit`, paper-local axiom, or unsafe
  declaration. No deleted v1 module remains in a Lean import.

The slim local v1 archive was rechecked: all 80 manifest hashes match.
It retains 68 unchanged project modules, the original version pins, and the
v1 PDF. The P03 commit remains
`7250f34a2cd16ece123b72a59b8df9823540a2c2`; no P03, Core, or shared Support
source was changed by this extension. No push was made.
