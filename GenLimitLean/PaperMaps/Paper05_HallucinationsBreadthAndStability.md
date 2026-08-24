# #05 Hallucinations, Breadth, and Stability map

Lean module: `GenLimit.Paper05_HallucinationsBreadthAndStability`.
Declaration namespace: `GenLimit.BreadthCharacterizations`.

## Pinned source

- Alkis Kalavasis, Anay Mehrotra, and Grigoris Velegkas,
  *On Characterizations for Language Generation: Interplay of Hallucinations,
  Breadth, and Stability*.
- Formalization source:
  [arXiv:2412.18530v2](https://arxiv.org/abs/2412.18530v2).
- The website reading list uses the shorter title *Characterizations of
  Language Generation With Breadth* for the same arXiv entry.
- The source correspondence has not yet received a named human audit or a
  checksum-pinned external statement-faithfulness audit.

## Scope and status

The development formalizes the deterministic semantic support layer.  It
does not assert Turing computability, support-oracle computability,
probability-distribution realizability, or statistical rates.

The semantic form of Theorem 3.3 is complete.  The constructive direction of
Theorem 3.8 is complete, but its finite-non-uniqueness lower bound is absent.
The approximate-breadth equivalence in Theorem 3.15 is complete on the
library's natural-number universe by explicitly reusing P03's semantic
stable-approximate reduction.

The exact-breadth clause of printed Theorem 3.15 is not asserted: literal
Definition 3.1 requires support `K \ S_t`, while Definition 3.14 requires the
raw support to become constant.  Lean proves these requirements incompatible
on a complete presentation of an infinite target.  A separately named
whole-target/sample-restored theorem records a coherent repair without
presenting it as the literal source statement.

## Paper-to-Lean correspondence

| Paper item | Lean declaration | Module | Status |
|---|---|---|---|
| Definition 3.1, exact breadth | `ExactBreadthCorrectAt`, `IsExactBreadthGenerator`, `ExactBreadthGeneratable` | `Definitions` | Complete literal fresh-output predicate. |
| Definition 3.2, approximate breadth | `ApproximateBreadthCorrectAt`, `IsApproximateBreadthGenerator`, `ApproximateBreadthGeneratable` | `Definitions` | Complete semantic support predicate. |
| Theorem 3.3 | `Results.theorem_3_3_semantic`; internal `exactBreadthGeneratable_iff_conditionTwo` | `Results.Overview`, `ExactBreadth` | Complete semantic equivalence, reusing canonical Angluin tell-tales. Effectiveness is not claimed. |
| Theorem 3.5 | -- | -- | Not formalized: the general uniqueness lower-bound framework is absent. |
| Definition 3.7, weak Angluin condition | `IsWeakTellTale`, `WeakAngluinCondition` | `Definitions` | Complete indexed predicate. |
| Theorem 3.8 | `Results.theorem_3_8_sufficiency_semantic`; internal `weakAngluin_implies_approximateBreadthGeneratable` | `Results.Overview`, `ApproximateBreadth` | Constructive direction complete; reverse implication is not formalized. |
| Definitions 3.9 and Theorem 3.10 | -- | -- | Not formalized: finite non-uniqueness and its generic lower bound are absent. |
| Definition 3.14, stability | `IsStableGenerator` | `Definitions` | Complete literal raw-support stabilization predicate. |
| Theorem 3.15, approximate clause | `Results.theorem_3_15_approximate_semantic`; internal `stableApproximateGeneratable_iff_conditionTwo` | `Results.Overview`, `StableApproximate`, `Relationships` | Complete semantic equivalence on `ℕ`; necessity reuses P03 through an explicit noncomputable oracle adapter. |
| Theorem 3.15, exact clause | `Results.theorem_3_15_literal_exact_inconsistent`; supporting `no_stable_exactBreadth_for_infinite_family` | `Results.Overview`, `StabilityGap` | The printed literal conjunction is refuted under the source's infinite-language assumption. |
| Corrected stable exact statement | `Results.theorem_3_15_corrected_wholeTarget_semantic`; internal `stableWholeTargetGeneratable_iff_conditionTwo` | `Results.Overview`, `CorrectedStability` | Kernel-checked library repair using whole-target/sample-restored support; not labeled as source Theorem 3.15. |
| Theorems 4.3 and 4.5 | -- | -- | Not formalized: the general tables require the missing uniqueness and finite-non-uniqueness frameworks. |
| Theorems 5.2 and 5.3 | -- | -- | Statistical rate statements excluded. |
| Definition 8.3, infinite coverage | `InfiniteCoverageCorrectAt`, `IsInfiniteCoverageGenerator` | `Definitions` | Complete literal valid, unseen, infinite-support predicate. |
| Proposition 8.4 | -- | -- | Not formalized. |
| Theorem 8.7 | -- | -- | The source's concrete separation is not formalized; `StabilityGap` proves a stronger literal incompatibility caused by the convention mismatch. |
| Proposition 8.10 and Corollary 8.11(2) | `Results.proposition_8_10_literal_specification_inconsistent`; supporting `no_stable_infiniteCoverage_for_infinite_family` | `Results.Overview`, `StabilityGap` | Their literal stability/infinite-coverage conjunction is refuted independently of the additional dimension and oracle assumptions. |
| Proposition 8.14 and other Section 8 results | -- | -- | Not formalized. |

## Reuse and ownership

- `SupportAlgorithm` is a P05-local `List α → Set α` interface.  It is not
  moved into Core and does not inherit P03's Boolean support-membership oracle.
- Theorem 3.3 directly reuses
  `GenLimit.Angluin.constantTellTaleApproximation` and
  `semanticLearner_semanticallyIdentifies`; P05 has no duplicate tell-tale
  choice or approximation declarations.
- The constructive half of Theorem 3.8 reuses P04's last-critical-language
  infrastructure, but retains a P05-native support-valued algorithm because
  P04 exhaustive generation allows a different output interface.
- `Relationships` adds a semantic Boolean membership adapter solely to reuse
  P03's `stable_approximateBreadthInLimit_implies_identifiableInLimit`.  The
  adapter uses classical decidability and certifies no implementation.
- Pure P04/P05 comparison statements live in
  `GenLimit.Bridges.Paper04ToPaper05`, outside both native paper umbrellas.
- No P05-specific definition or theorem was added to the lightweight Core.

## Source qualifications exposed by Lean

The following is a Codex-assisted formalization finding, not a named human
audit result:

- Literal exact breadth removes the growing observed sample, so its support
  cannot eventually be raw-constant on a complete presentation of an
  infinite language.  This contradicts the exact clause of Theorem 3.15.
- The same raw-stability versus unseen-output conflict makes the literal
  conclusion of Proposition 8.10 and Corollary 8.11(2) impossible.
- The paper's stability discussion informally treats consistent exact support
  as the whole target.  Lean records that convention separately through
  `restoreObserved` and does not silently rewrite the source definitions.

These findings await human source-correspondence review.

## Suggested reading order

1. `Definitions.lean`
2. `ExactBreadth.lean`
3. `ApproximateBreadth.lean`
4. `Relationships.lean` and `StableApproximate.lean`
5. `StabilityGap.lean`
6. `CorrectedStability.lean`
7. `Results/Overview.lean`
8. `GenLimit.Bridges.Paper04ToPaper05`

## Verification

```text
lake build GenLimit.Paper05_HallucinationsBreadthAndStability
lake build GenLimit.Bridges.Paper04ToPaper05
```

No `sorry`, `admit`, or project-defined axiom occurs in the P05 modules.
