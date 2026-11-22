# Paper 14: A Characterization of List Language Identification in the Limit

This map records the correspondence between Moses Charikar, Chirag Pabbaraju,
and Ambuj Tewari, *A Characterization of List Language Identification in the
Limit*, and the Lean development under
`GenLimit.Paper14_ListLanguageIdentification`.

## Source edition and scope

- Formalization source: arXiv:2511.04103v1, submitted 6 November 2025.
- Lean umbrella: `GenLimit.Paper14_ListLanguageIdentification`.
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean).
- All three headline statements are proved. The statistical branch covers full-support sampling, randomized output kernels, exponential upper and lower bounds, and positive limsup error when list identification fails.
- The source collection `(L₁, L₂, ...)` is represented by
  `F : ℕ → GenLimit.Generic.Language α`.  This keeps indices and duplicate
  names for extensionally equal languages, which matter for the source's
  behavioral-correctness criterion.
- The paper assumes a countable universe and nonempty languages.  The generic
  Lean wrappers instead ask directly for an exact positive presentation of
  each indexed language.  On the canonical universe `ℕ`, `AllNonempty F`
  constructs these presentations automatically in
  `listIdentifiable_iff_kAngluin_nat`.
- The source takes `k ≥ 1`.  The underlying Lean characterization also handles
  `k = 0`; for a presentable target both sides are false, so this is a harmless
  totalization rather than a weakening.
- The source explicitly studies existence of list-valued functions without a
  computational restriction.  The Lean development likewise proves classical
  semantic results and does not claim an extracted algorithm or a runtime
  bound.

- Peng Zhang reported a **Level 1 human audit of Overview Theorems 1 and 2
  and all definitions involved in those statements** on 13 November 2026,
  against non-P38 checkpoint `9efdb94`. See the
  [human-audit ledger](../AuditRecords/Human/README.md#14-list-language-identification-overview-theorems-1-and-2-level-1)
  and [fingerprint manifest](../AuditRecords/Human/Fingerprints/P14_OverviewTheorems1And2Level1.json)
  for the arXiv-v1 source identity, exact statement/definition scope, and
  reviewed source hashes. Presentability, behavioral correctness, the
  zero-width extension, and the relative-Angluin layer convention remain
  explicit. Construction and proof correspondence are outside this review.

## Main-result correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definitions 1--2 | `ListIdentifier`, `TargetInGuess`, `IdentifiesFrom`, `ListIdentifies`, and `ListIdentifiable` in [`Definitions.lean`](../GenLimit/Paper14_ListLanguageIdentification/Definitions.lean) | Full semantic interface | A fixed-width output is `Fin k → ℕ`.  Correctness is extensional in the denoted language, so the correct index may vary after the convergence time exactly as in the paper's behavioral criterion. |
| Equations (4)--(6) | `Psi` and `KAngluinCondition` in [`Psi.lean`](../GenLimit/Paper14_ListLanguageIdentification/Psi.lean) | Full | Lean defines the recursive predicate at every natural depth, proves its monotonicity, and proves that depth one is Angluin's ordinary finite-tell-tale condition. |
| Claim 5.1 | `levelChoice_stabilizes` in [`Stabilization.lean`](../GenLimit/Paper14_ListLanguageIdentification/Stabilization.lean) | Full | The least eligible index stabilizes to the source's least target-compatible candidate on every exact positive presentation. |
| Algorithm 1 | `listIdentify`, `listIdentify_length_le`, and `listIdentify_eventually_contains_target` in [`Algorithm.lean`](../GenLimit/Paper14_ListLanguageIdentification/Algorithm.lean) | Full semantic construction | The recursive output has length at most `k`; `boundedToFixed` pads it to Definition 1's fixed-width interface without changing correctness. |
| Theorem 6 | `theorem6_kAngluin_sufficient` and `theorem6_kAngluin_listIdentifiable` in [`Algorithm.lean`](../GenLimit/Paper14_ListLanguageIdentification/Algorithm.lean) | Full | Both the at-most-`k` Algorithm-1 conclusion and the fixed-width existence theorem are available. |
| Theorem 7 | `theorem7_kAngluin_necessity` and `theorem7_kAngluin_necessity_nat` in [`GeneralNecessity.lean`](../GenLimit/Paper14_ListLanguageIdentification/GeneralNecessity.lean) | Full statement through a proof-equivalent formal route | The paper presents the contrapositive via Algorithm 2.  Lean proves the direct implication by behavioral locking and induction on list width, preserving the same bounded-depth strict-sublanguage adversary without encoding Algorithm 2 as an executable state machine. |
| Theorem 1 | `Results.theorem_1` in [`Results/Overview.lean`](../GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean), delegating to `listIdentifiable_iff_kAngluin` in [`GeneralNecessity.lean`](../GenLimit/Paper14_ListLanguageIdentification/GeneralNecessity.lean) | Full deterministic semantic statement | This combines the formal Theorems 6 and 7.  The generic presentation hypothesis is the exact proof-relevant form of the source's countable-universe/nonempty-language assumptions. |
| Theorem 2 | `Results.theorem_2` in [`Results/Overview.lean`](../GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean), delegating to `listIdentifiable_iff_stratification` in [`Stratification.lean`](../GenLimit/Paper14_ListLanguageIdentification/Stratification.lean) | Full deterministic semantic statement | `HasAngluinStratification` is a cover by exactly `k` sets of indices satisfying Angluin's condition relative to each layer.  Layers need not be disjoint, matching the theorem's union formulation; empty or repeated layers account for “at most `k`”. |
| Theorem 9 | `Results.theorem_9` | Full statement. An infinite IID fair-bit tape supplies one bit per symbol. Beyond k/(k+1), continuity from below gives eventually large marginal acceptance, and a deterministic k-list covers every such distinct language. |
| Theorem 10 | `Results.theorem_10` | Both directions for every success probability in [0,1]. Independent rows of fair bits sample positions in a fixed text. In the reverse direction, comparisons of unequal independent pairs supply fair bits independent of a held-out text. Each learner uses finite prefixes, and singleton targets have a deterministic fallback. |
| Theorem 3 and detailed Theorems 8, 11, 12, 13 | `Results.theorem_3`, `Statistical.theorem_8`, `Statistical.theorem_11`, `Statistical.theorem_12`, `Statistical.theorem_13` | Full statements | A Baire argument gives the sharp limsup threshold 1/(k+1). The exponential lower bound assumes k+1 distinct languages sharing a word. |

## Shared infrastructure and reuse

- [`Paper00A_PositiveDataInference/Semantic`](../GenLimit/Paper00A_PositiveDataInference/Semantic/)
  supplies the existing Angluin semantic definitions, the depth-one
  tell-tale bridge, and the stable finite-history learner interface.
- [`Core/Identification.lean`](../GenLimit/Core/Identification.lean) supplies
  the shared finite-history learner adapter and the generic
  `StabilizesTo` convergence predicate; [`Core/Text.lean`](../GenLimit/Core/Text.lean)
  supplies ordered finite prefixes and the bridge between list histories and
  length-indexed tuples.
- [`Support/Locking.lean`](../GenLimit/Support/Locking.lean) factors the
  universe- and learner-output-polymorphic locking diagonal, including the
  generic existence theorem used by the P14 necessity proof, out of obsolete
  paper-local dependency paths.
- The P14 lower bound consumes these shared locking primitives while keeping
  the list-width induction and behavioral target lock paper-local.

## Statistical proof

A finite positive witness forces the identifier for the target's relative Angluin layer to be correct. Its IID waiting time has an exponential tail. In the converse, a Baire argument locks a law-dependent margin for each previously selected language. A list of width `k` cannot contain all `k+1` locked targets. For the optimality bound, full-support distributions with a common heavy atom force an exponentially likely indistinguishable sample. The separate infinite-draw and randomized-stream equivalences of Theorems 9 and 10 have not been used in this proof.

All currently covered P14 declarations are kernel-checked and contain no
`sorry`, `admit`, or paper-local axioms. Human Level 1 review now covers
Overview Theorems 1 and 2 and their defining interfaces at the checkpoint
recorded above. Detailed Theorems 6--7, constructions, proofs, and the
statistical branch are not separately human-audited by this record.
