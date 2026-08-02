# Angluin 1980 dependency map

Lean umbrella: `GenLimit.Angluin`

Source: Dana Angluin, *Inductive Inference of Formal Languages from Positive
Data*, *Information and Control* **45**(2), pp. 117--135, 1980,
doi:10.1016/S0019-9958(80)90285-5.

This sibling development supplies the identification and finite-tell-tale
vocabulary used by Paper 08. It is not treated as one of the numbered papers
in the 36-paper audit, and no source PDF hash or independent external
statement-audit record is claimed here. The map records the formal boundary
of the imported Angluin layer so semantic results are not mistaken for the
full effective theorem.

## Current scope

The development contains two deliberately separate interfaces:

- the semantic interface uses arbitrary Lean functions as identifiers and
  proves convergence from exact positive presentations;
- the effective interface records a uniformly recursive indexed family,
  computable inference, and a computably enumerated finite tell-tale through
  Mathlib's `Computable` predicates.

The semantic stabilization arguments are complete. On the effective side,
the formalization proves Corollary 1's necessity and derives a semantic
identifier from Condition 1, but does not claim the complete effective
biconditional of Theorem 1 or the counterexample required by Theorem 2.

## Main entry points

- `GenLimit.Angluin.SemanticallyIdentifies`;
- `GenLimit.Angluin.IsTellTale` and `GenLimit.Angluin.ConditionTwo`;
- `GenLimit.Angluin.semanticLearner_semanticallyIdentifies`;
- `GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable`;
- `GenLimit.Angluin.ConditionOne.semantic_sufficiency`;
- `GenLimit.Angluin.effectiveInferrable_conditionTwo`; and
- `GenLimit.Angluin.corollaryOne`.

The generic `conditionTwo_of_semanticallyIdentifiable` theorem was factored
out of the Paper 08 implementation because its statement mentions only
Angluin vocabulary. Paper 08 retains the thin namespace-local wrapper
`GenLimit.HallucinationDetection.conditionTwo_of_identifiable` for source
correspondence.

## Representation

| Source object | Lean representation |
|---|---|
| Indexed language family | `GenLimit.Generic.LanguageFamily α = ℕ → Set α` |
| Semantic inference machine | `SemanticIdentifier α` |
| Exact positive presentation | `GenLimit.Generic.Presents stream (C i)` |
| Stable syntactic conjecture | `ConvergesTo M stream j` |
| Identification of a family | `SemanticallyIdentifies M C` |
| Finite tell-tale for index `i` | `IsTellTale C i T` |
| Nonuniform tell-tale existence | `ConditionTwo C` |
| Uniformly recursive family over `ℕ` | `EffectiveIndexedFamily` |
| Computable positive-data inference | `EffectiveInferrable F` |
| Computably enumerated finite tell-tales | `ConditionOne F` |

`ConvergesTo` requires stabilization to one fixed index, not merely to a
sequence of extensionally equal languages. Duplicate indices are allowed,
and the eventual index must denote the target language. Positive
presentations have no pause symbol, so the effective source interface records
the paper's nonempty-language assumption explicitly.

## Formalized boundary

| Source-facing item | Lean declaration | Status |
|---|---|---|
| Semantic identifier and convergence | `SemanticIdentifier`, `ConvergesTo`, `SemanticallyIdentifies` | Complete semantic interface |
| Finite tell-tale condition | `IsTellTale`, `ConditionTwo` | Complete set-theoretic interface |
| Least-index semantic learner | `semanticLearner`, `semanticLearner_semanticallyIdentifies` | Complete under an eventually stable tell-tale approximation |
| Semantic necessity of Condition 2 | `conditionTwo_of_semanticallyIdentifiable` | Complete; generalized from the Paper 08 locking argument |
| Effective family and machine predicates | `EffectiveIndexedFamily`, `EffectiveInferrable` | Definition complete |
| Condition 1 | `ConditionOne` | Definition complete, including uniform computability of the enumeration |
| Condition 1 sufficiency, set-theoretic part | `ConditionOne.semantic_sufficiency` | Complete semantic conclusion; computability of the constructed learner is not proved |
| Corollary 1 necessity | `effectiveInferrable_conditionTwo`, `corollaryOne` | Complete with effectivity assumptions retained |
| Full effective Theorem 1 | `TheoremOneStatement` | Statement recorded; full proof not claimed |
| Theorem 2 separation | `TheoremTwoStatement` | Statement recorded; witness/proof not claimed |

## Ownership and audit boundary

`GenLimit.Angluin` is a sibling paper/dependency development, not shared
`GenLimit.Core`: its notions and theorem statements belong specifically to
Angluin's identification theory. Native Paper 08 modules may import this
sibling because identification and Condition 2 are explicit objects of that
paper. No substantive Li--Raman--Tewari theorem is imported by either native
development; their sole comparison is isolated in
`GenLimit.Bridges.LiRamanTewariToHallucinationDetection`.

This map is documentation of implementation scope, not a human or external
source-to-Lean audit. Named human review status is recorded only in
[`../HUMAN_AUDIT.md`](../HUMAN_AUDIT.md).
