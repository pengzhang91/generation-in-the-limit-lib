# #0A Inductive Inference from Positive Data map

Lean umbrella: `GenLimit.Paper00A_PositiveDataInference`. Main-results entry
point: `GenLimit.Paper00A_PositiveDataInference.Results.Overview`. The
declaration namespace remains `GenLimit.Angluin` for API compatibility.

Source: Dana Angluin, *Inductive Inference of Formal Languages from Positive
Data*, *Information and Control* **45**(2), pp. 117--135, 1980,
doi:10.1016/S0019-9958(80)90285-5.

This numbered development supplies the identification and finite-tell-tale
vocabulary used by #08 and #28. No source PDF hash or independent external
statement-audit record is claimed here. The map records the formal boundary
and keeps the semantic characterization distinct from the effective theorem.

## Current scope

The development contains two deliberately separate interfaces:

- the semantic interface uses arbitrary Lean functions as identifiers and
  proves convergence from exact positive presentations;
- the effective interface records a uniformly recursive indexed family,
  computable inference, and a computably enumerated finite tell-tale through
  Mathlib's `Computable` predicates.

The filesystem mirrors that boundary:
`GenLimit/Paper00A_PositiveDataInference/Semantic/` owns the set-theoretic
characterization, while
`GenLimit/Paper00A_PositiveDataInference/Effective/` owns the computability
layer. `GenLimit.Paper00A_PositiveDataInference.Semantic` and
`GenLimit.Paper00A_PositiveDataInference.Effective` are the corresponding
umbrella imports; declarations remain under `GenLimit.Angluin`.

This effective interface is not a KM-style finite-query oracle model:
Angluin's learner consumes positive texts, while computability is imposed on
the family, inference procedure, and tell-tale enumeration.

The semantic sufficiency argument is native to this development. Semantic
necessity is reduced, over a countable domain, to Gold's already formalized
positive-text finite-tell-tale theorem by pulling the family back along a
surjection `ℕ → α`; Angluin no longer carries a duplicate semantic locking
module. On the effective side, a bounded least-index learner proves Condition
1 sufficient, while finite approximations to syntactic stabilization extract
a uniform computable tell-tale enumerator from any computable successful
learner. Together these give the full biconditional of Theorem 1. The
same effective layer now derives Corollaries 2 and 3 from Conditions 3 and
2+4, respectively. The counterexamples and conservative-learning results in
Theorems 2--5 are not yet formalized.

The source presents Corollaries 2 and 3 through mutable stage constructions.
Lean uses extensionally equivalent dovetailed emitters. For Corollary 2 it
emits the least target element and the first target-versus-candidate
disagreement certified by a finite prefix; finite thickness makes the output
set finite. For Corollary 3 it emits the least target element missing from
each indexed proper sublanguage; a Condition 2 tell-tale gives a finite bound
on all such outputs. These are proof-packaging differences, not changes to
either source statement or its effective assumptions.

## Main entry points

- `GenLimit.Angluin.SemanticallyIdentifies`;
- `GenLimit.Angluin.IsTellTale` and `GenLimit.Angluin.ConditionTwo`;
- `GenLimit.Angluin.semanticLearner_semanticallyIdentifies`;
- `GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable`;
- `GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo`;
- `GenLimit.Angluin.ConditionOne.effective_sufficiency`;
- `GenLimit.Angluin.effectiveInferrable_conditionOne`;
- `GenLimit.Angluin.theoremOne`;
- `GenLimit.Angluin.effectiveInferrable_conditionTwo`;
- `GenLimit.Angluin.corollaryOne`;
- `GenLimit.Angluin.conditionThree_conditionOne` and
  `GenLimit.Angluin.corollaryTwo`;
- `GenLimit.Angluin.conditionTwo_conditionFour_conditionOne` and
  `GenLimit.Angluin.corollaryThree`; and
- the stable wrappers in `GenLimit.Angluin.Results`.

The generic `conditionTwo_of_semanticallyIdentifiable` theorem remains in the
Angluin namespace because its statement mentions only Angluin vocabulary;
its proof reuses `GenLimit.Gold.Text.finite_tellTale_of_semantic_identification`.
Paper 08's Corollary 2.2 now invokes the canonical Angluin equivalence directly,
without retaining namespace-local copies of either direction.

## Representation

| Source object | Lean representation |
|---|---|
| Indexed language family | `GenLimit.Generic.LanguageFamily α = ℕ → Set α` |
| Semantic inference machine | `SemanticIdentifier α = GenLimit.Learner α ℕ` |
| Exact positive presentation | `GenLimit.Generic.Presents stream (C i)` |
| Stable syntactic conjecture | `GenLimit.StabilizesTo (fun t => M (GenLimit.textPrefix stream t)) j` |
| Identification of a family | `SemanticallyIdentifies M C` |
| Finite tell-tale for index `i` | `IsTellTale C i T` |
| Nonuniform tell-tale existence | `ConditionTwo C` |
| Uniformly recursive family over `ℕ` | `EffectiveIndexedFamily` |
| Computable positive-data inference | `EffectiveInferrable F` |
| Computably enumerated finite tell-tales | `ConditionOne F` |
| Finite thickness | `ConditionThree F.language` |
| Computable indexed-language inclusion | `ConditionFour F` |

The shared Core `StabilizesTo` predicate requires stabilization to one fixed
index, not merely to a sequence of extensionally equal languages. Duplicate
indices are allowed, and the eventual index must denote the target language.
Positive presentations have no pause symbol, so the effective source
interface records the paper's nonempty-language assumption explicitly.

## Formalized boundary

| Source-facing item | Lean declaration | Status |
|---|---|---|
| Semantic identifier and convergence | `SemanticIdentifier` (a Core `Learner` specialization), `GenLimit.IdentifiesInLimit`, `SemanticallyIdentifies` | Complete semantic interface |
| Finite tell-tale condition | `IsTellTale`, `ConditionTwo` | Complete set-theoretic interface |
| Least-index semantic learner | `semanticLearner`, `semanticLearner_semanticallyIdentifies` | Complete under an eventually stable tell-tale approximation |
| Semantic necessity of Condition 2 | `conditionTwo_of_semanticallyIdentifiable` | Complete; countable-domain pullback to Gold's finite-tell-tale necessity theorem |
| Semantic characterization | `semanticallyInferrable_iff_conditionTwo` | Complete: semantic identification iff nonuniform finite tell-tales |
| Effective family and machine predicates | `EffectiveIndexedFamily`, `EffectiveInferrable` | Definition complete |
| Condition 1 | `ConditionOne` | Definition complete, including uniform computability of the enumeration |
| Condition 1 sufficiency | `ConditionOne.effective_sufficiency` | Complete, including a computable bounded least-index learner |
| Condition 1 necessity | `effectiveInferrable_conditionOne` | Complete, including the uniform computable finite tell-tale enumerator |
| Corollary 1 necessity | `effectiveInferrable_conditionTwo`, `corollaryOne` | Complete with effectivity assumptions retained |
| Full effective Theorem 1 | `theoremOne` | Complete: `EffectiveInferrable F ↔ ConditionOne F` |
| Condition 3 | `ConditionThree` | Complete: finite distinct family languages above every nonempty finite sample |
| Corollary 2 | `conditionThree_conditionOne`, `corollaryTwo` | Complete; a total computable dovetailed emitter establishes Condition 1 |
| Condition 4 | `ConditionFour` | Complete: one computable Boolean inclusion function, uniform in both indices |
| Corollary 3 | `conditionTwo_conditionFour_conditionOne`, `corollaryThree` | Complete; Condition 2 bounds the direct least-missing-element emitter |
| Theorem 2 separation | `TheoremTwoStatement` | Statement recorded; witness/proof not claimed |
| Theorem 3 separation | — | Open; no halting-output witness is formalized |
| Theorem 4 conservative-inference separation | — | Open; no witness family or conservative-learning API is formalized |
| Theorem 5 conservative learner | — | Open; Condition 5 and the four-part learner guarantee are not formalized |

## Ownership and audit boundary

`GenLimit.Paper00A_PositiveDataInference` is a paper development, not shared
`GenLimit.Core`: its `GenLimit.Angluin` notions and theorem statements belong
specifically to Angluin's identification theory. Its semantic necessity proof imports Gold's
positive-text theorem rather than duplicating Gold's locking argument. Native
Paper 08 modules may import this dependency because identification and
Condition 2 are explicit objects of that paper. No substantive
Li--Raman--Tewari theorem is imported by either native development; their sole
comparison is isolated in
`GenLimit.Bridges.LiRamanTewariToHallucinationDetection`.

The paper-local computable search combinators and finite-emission bookkeeping
delegate to `GenLimit.Support.ComputableSearch` and
`GenLimit.Support.FiniteEnumeration`. Effective syntactic stabilization
delegates to `GenLimit.Support.Locking`; the public Angluin names remain
available as compatibility wrappers.

This map records implementation scope and the completed human status; it does
not claim an external source-to-Lean statement audit. The Level 1 human audit
of the semantic characterization is recorded in the authoritative
[`../AuditRecords/Human/README.md`](../AuditRecords/Human/README.md).
