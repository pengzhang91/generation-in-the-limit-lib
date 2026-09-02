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
- Status: **partial**.  The deterministic characterization and stratification
  results (Theorems 1, 2, 6, and 7), Algorithm 1, Claim 5.1, and the recursive
  `k`-Angluin condition are formalized.  Statistical Theorem 3 and the
  probabilistic/rate development in Sections 8--10 are absent.
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
| Theorem 3 and Sections 8--10 | No declaration | None | Valid distributions, rate functions, randomized/probabilistic list identifiers, Top-`k` aggregation, exponential upper/lower rates, and the no-vanishing-rate result remain to be formalized. |

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

## Remaining roadmap

The substantive missing branch is statistical list identification:

1. define valid full-support distributions and list-identification rate
   semantics;
2. formalize probabilistic list identifiers and the deterministic Top-`k`
   aggregation bridge;
3. connect the deterministic characterization to an exponential-rate upper
   bound;
4. prove the exponential lower bound for nontrivial collections and the
   no-vanishing-rate result when the `k`-Angluin condition fails;
5. expose Theorem 3 through `Results/Overview.lean`.

All currently covered P14 declarations are kernel-checked and contain no
`sorry`, `admit`, or paper-local axioms.  No human statement-correspondence
audit has yet been recorded.
