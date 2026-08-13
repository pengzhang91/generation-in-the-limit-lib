# #04 Exploring Facets of Language Generation in the Limit map

Lean module: `GenLimit.Paper04_ExploringFacetsOfLanguageGeneration`.
Declaration namespace: `GenLimit.CharikarPabbaraju`.

## Pinned source

- Moses Charikar and Chirag Pabbaraju, *Exploring Facets of Language
  Generation in the Limit*.
- Formalization source: [arXiv:2411.15364v2](https://arxiv.org/abs/2411.15364v2),
  dated 24 December 2024.
- The source correspondence has not yet received a named human audit or a
  checksum-pinned external statement-faithfulness audit.

## Completion status

Overview Theorems 1--5 and detailed Theorems 6--8 have kernel-checked Lean
proofs. Overview Theorem 2 is exposed through the stronger size-two lower
bound stated as detailed Theorem 7.

| Paper item | Lean declaration | Module | Status |
|---|---|---|---|
| Definition 1, effective generation in the limit | `IsEffectiveLimitGenerator`, `EffectivelyGeneratableInLimit` | `Preliminaries` | Complete effective statement and semantic-forgetting bridge. |
| Definitions 2--3, non-uniform and uniform generation | `IsNonuniformGenerator`, `NonuniformlyGeneratable`, `IsUniformGenerator`, `UniformlyGeneratable` | `Definitions` | Complete source-facing exact-presentation definitions. |
| Definition 4, closure dimension | `ClosureDimensionAtLeast`, `IndexedClosureDimensionAtLeast` | `Definitions` | Complete level-by-level encoding reusing Core closure witnesses. |
| Theorem 1 | `Results.theorem_1` | `Results.Overview` | Complete; derived from Theorem 6. |
| Theorem 2 | `Results.theorem_2` | `Results.Overview`, `MembershipQueryGlobalDiagonal` | Complete through the stronger size-two detailed Theorem 7. |
| Theorem 3 | `Results.theorem_3` | `Results.Overview`, `RegularRayEncoding` | Complete literal finite-alphabet, regular-language lower bound. |
| Theorem 4 | `Results.theorem_4` | `Results.Overview`, `ExhaustiveCharacterization` | Complete for countably indexed infinite languages; Proposition 6.2 is at its stated semantic strong-oracle layer. |
| Theorem 5 | `Results.theorem_5` | `Results.Overview`, `Feedback` | Complete GF-dimension characterization under UUS. |
| Theorem 6 | `Results.theorem_6`, `nonuniform_upper_bound_no_repetition` | `Results.Detailed`, `Nonuniform`, `NonuniformNoRepetition` | Complete quantitative bound and optional nonrepetition refinement. The greedy tests are resolved classically. |
| Theorem 7 | `Results.theorem_7`, `theorem_seven` | `Results.Detailed`, `MembershipQueryGlobalDiagonal` | Complete deterministic adaptive membership-query lower bound. The proof uses the alleged universal guarantee's termination clause on separated infinite completions at every finite stage. |
| Theorem 8 | `Results.theorem_8` | `Results.Detailed`, `Identification` | Complete by direct reuse of the formalized effective Angluin Theorem 1. |
| Claim 5.2 | `claim_5_2` | `BreadthClaim52` | Complete co-singleton exact-breadth separation. |
| Proposition 6.1 | `proposition6_1_exhaustive_necessary` | `ExhaustiveCharacterization` | Complete adversarial necessity proof. |
| Proposition 6.2 | `proposition6_2_exhaustive_sufficient_semantic_oracle` | `ExhaustiveCharacterization` | Complete at the semantic strong-oracle level named in the declaration. |
| Proposition 6.3 | `proposition6_3_membership_query_sufficient` | `MembershipExhaustive` | Semantic correctness of the explicit relative membership-query algorithm is complete; no separate `Computable` theorem for the dependent algorithm object is claimed. |
| Breadth necessary condition | `generation_with_breadth_implies_angluinExistence` | `Breadth` | Complete through the canonical Angluin semantic-necessity theorem. |
| Proposition 7.1 | `proposition7_1_gnf_eq_closure` | `NoFeedbackDimension` | Complete level-by-level equality for positive dimensions. |
| Example 9 | `example9_exhaustivelyGeneratable`, `coSingletonIntegerClass_no_telltale_for_univ` | `Exhaustive` | Complete exhaustive-generation/identification separation. |
| Example 10 | `example10_not_uniformlyGeneratable_withoutFeedback`, `example10_uniformlyGeneratableWithFeedback` | `FeedbackSeparation` | Complete one-query feedback separation. |
| Final Section 7 co-one/co-two example | `coOneTwoIntegerClass_not_uniformlyGeneratableWithFeedback` and supporting direct generation/adversary results | `FeedbackExample` | Complete for the stated semantic feedback model. |

## Refactored structure and ownership

- `Definitions` is the lightweight paper-facing vocabulary layer. The source
  definitions remain visible rather than being hidden behind P02 aliases.
- `Results.Overview` exposes completed overview Theorems 1--5.
- `Results.Detailed` exposes completed detailed Theorems 6--8.
- `MembershipQueryAssignments`, `MembershipQueryShadow`, and
  `MembershipQueryDiagonalRepair` isolate the small finite-oracle,
  finite-transcript, and completion/certificate layers used by Theorem 7.
- `MembershipQueryGlobalDiagonal` owns the completion-driven recursive
  construction. `Experimental` remains only as a compatibility entry point.
- `Common.IntegerSweep` owns the integer enumeration shared by P04 examples.
- `GenLimit.Support.Presentations` supplies paper-independent exact
  presentations and finite-prefix completion. `EnumerationProgress` supplies
  the canonical repetition-free enumeration of an infinite countable set.
- No P04-specific definition or proof was moved into `GenLimit.Core`.

## Reuse and theorem relationships

| Relationship | Formal record |
|---|---|
| P04 Definitions 2--3 and the shared P02/Core class predicates are equivalent on countable universes with nonempty indexed languages | `Definitions.nonuniformlyGeneratable_iff_generic`, `Definitions.uniformlyGeneratable_iff_generic` |
| P04 Theorem 1 is also a consequence of P02 Corollary 3.6 | `GenLimit.Bridge.Paper02ToPaper04.theorem_1_from_paper02_corollary_3_6` |
| P04 Theorem 8 is Angluin's effective Theorem 1 | `GenLimit.CharikarPabbaraju.theorem_8` delegates to `GenLimit.Angluin.theoremOne` |
| Exact breadth implies the Angluin tell-tale condition | `generation_with_breadth_implies_conditionTwo` reuses `GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable` |
| Theorem 3 is a concrete regular-language consequence of Proposition 6.1 | `theorem3_finiteAlphabet_regular_exhaustive_generation_lower_bound` |
| Proposition 7.1 identifies P04's no-feedback game dimension with the Core closure dimension | `proposition7_1_gnf_eq_closure` |
| Overview Theorem 2 is the countable-class consequence of the stronger size-two detailed Theorem 7 | `Results.theorem_2` delegates to `Results.theorem_7` |

The explicit P02/P04 comparison lives in
`GenLimit.Bridges.Paper02ToPaper04`; the native P04 Theorem 1 proof remains
independent. The feedback separation files directly reuse P02's already
formalized uniform closure-dimension characterization instead of duplicating
that theorem.

## Formalization boundaries

- Several construction theorems are semantic and noncomputable. In
  particular, Theorem 6's greedy generator classically decides infinitude of
  finite intersections. This does not certify an executable implementation of
  the paper's oracle discussion.
- Proposition 6.2 is deliberately named as a semantic strong-oracle result.
- Proposition 6.3 proves semantic correctness of an algorithm whose
  definition uses the family membership oracle and emitted tell-tale content;
  it does not package a Mathlib `Computable` certificate for the dependent
  algorithm type.
- Theorem 7 is proved by a completion-driven diagonal under the contradictory
  universal guarantee. This avoids the printed proof's unsupported inference
  that an infinite query loop must mention infinitely many distinct words:
  universality already forces finite termination on every temporary infinite
  completion used by the construction.
- The theorem is stated for pairs of infinite languages, matching the
  repository's standing generation scope. The local operational model makes
  adaptive finite query traces and possible nontermination explicit.
- Kernel checking establishes the Lean statements, not paper-to-Lean source
  correspondence. Human audit remains pending.

## Suggested reading order

1. `Definitions.lean`
2. `Results/Detailed.lean`
3. `Results/Overview.lean`
4. `Nonuniform.lean` and `NonuniformNoRepetition.lean`
5. `Exhaustive.lean`, `ExhaustiveCharacterization.lean`, and
   `RegularRayEncoding.lean`
6. `Breadth.lean` and `BreadthClaim52.lean`
7. `Feedback.lean`, `NoFeedbackDimension.lean`, and the two feedback examples
8. `MembershipQueryLowerBoundStatement.lean`,
   `MembershipQueryDiagonalRepair.lean`, and
   `MembershipQueryGlobalDiagonal.lean` for Theorem 7

## Verification

```text
lake build GenLimit.Paper04_ExploringFacetsOfLanguageGeneration
lake build GenLimit.Bridges.Paper02ToPaper04
```
