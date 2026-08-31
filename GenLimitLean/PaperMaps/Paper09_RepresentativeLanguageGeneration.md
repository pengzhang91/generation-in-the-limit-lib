# #09 Representative Language Generation map

Native Lean module: `GenLimit.Paper09_RepresentativeLanguageGeneration`.
Declaration namespaces:
`GenLimit.RepresentativeGeneration` and
`GenLimit.RepresentativeGeneration.Published`.

## Pinned source

- Charlotte Peale, Vinod Raman, and Omer Reingold,
  *Representative Language Generation*;
- final ICML 2025 proceedings version, PMLR 267, pp. 48518--48541
  ([proceedings page](https://proceedings.mlr.press/v267/peale25a.html));
- pinned PDF SHA-256 recorded by the Lean umbrella and registry:
  `647dff8492c32479171e6acb4751a17a084407a39e502ec7ce6dfeebf9a6e61d`;
- machine-readable claim inventory:
  [`registry/papers/P09.json`](../../registry/papers/P09.json).

The final PMLR version is the formalization target. The source identity and
claim inventory are pinned, but no named human or external statement-
faithfulness audit currently covers P09.

## Scope and status

The registry's declared P09 source inventory contains the eleven distinct
theorem-, corollary-, and lemma-level results in Sections 3--4 of the final
PMLR version. Lean provides:

- full coverage of Theorem 3.3, Corollaries 3.4--3.5, Theorem 3.7,
  Corollary 3.8, and Lemmas 4.3, 4.6, and 4.9;
- partial coverage of Corollary 3.6, through the intended explicit
  countably infinite witness rather than the false arbitrary-finite-universe
  reading; and
- no source-claim coverage of printed Lemma 4.8 or Theorem 4.4. Lean checks
  an obstruction to the former and a counterexample to the latter, then
  proves separately named repairs under finite exact-profile support.

The exact-profile repairs are useful corrected mathematics, but are not
counted as formalizations of the two printed claims. Consequently P09 is
partial relative to its declared source-claim inventory even though every
maintained Lean declaration is kernel checked.

## Public entry points

The compact paper-facing surface is
`GenLimit.Paper09_RepresentativeLanguageGeneration.Results.Overview`:

- `GenLimit.RepresentativeGeneration.Published.theorem_3_3`;
- `GenLimit.RepresentativeGeneration.Published.corollary_3_4`;
- `GenLimit.RepresentativeGeneration.Published.corollary_3_5`;
- `GenLimit.RepresentativeGeneration.Published.corollary_3_6`;
- `GenLimit.RepresentativeGeneration.Published.theorem_3_7`;
- `GenLimit.RepresentativeGeneration.Published.corollary_3_8`;
- `GenLimit.RepresentativeGeneration.Published.lemma_4_3`;
- `GenLimit.RepresentativeGeneration.Published.lemma_4_6`;
- `GenLimit.RepresentativeGeneration.Published.lemma_4_9`;
- `GenLimit.RepresentativeGeneration.Published.printed_theorem_4_4_counterexample`;
- `GenLimit.RepresentativeGeneration.Published.corrected_lemma_4_8`; and
- `GenLimit.RepresentativeGeneration.Published.corrected_theorem_4_4`.

There are deliberately no misleading paper-facing declarations named
`lemma_4_8` or `theorem_4_4`.

## Representation

| Paper object | Lean representation |
|---|---|
| Countable example space | An arbitrary type `α`, with countability or nonemptiness assumptions added only where a result needs them |
| Hypothesis class `H` | `GenLimit.Generic.LanguageClass α = Set (Set α)` |
| Countable groups of interest | `groups : ℕ → Set α`; a partition satisfies `IsCountablePartition groups` |
| Finite partition | `groups : Fin k → Set α`, embedded into the countable API by `extendFinitePartition` and empty padding |
| Randomized generator | `RandomizedGenerator α`, returning a `DiscreteDistribution α` after each finite history |
| Empirical group proportion | `empiricalGroupProbability` on the finset of distinct observed examples |
| Output group proportion | `inducedGroupProbability` / `groupMass` |
| Worst group error | `groupSupDistance`, an `ENNReal.iSup` over the countable group coordinates |
| Positive version space and closure | Paper-facing aliases `consistentHypotheses`, `commonCore`, and `closure` for the canonical Core definitions |
| Eventual validity and freshness | Probability-one support on `L \ sample`, expressed by `IsConsistentAt` and `IsConsistentFrom` |

The generator returns a mathematical discrete distribution. Classical choice
and noncomputable distribution constructions are allowed; this interface does
not assert an efficient sampler or a computable representation of real-valued
probabilities.

## Definition and result correspondence

| Paper item | Lean declaration | Status |
|---|---|---|
| Definition 2.2, countable partition | `IsCountablePartition` | Complete |
| Definition 2.3, consistent hypotheses | `consistentHypotheses` | Complete; alias of Core `versionSpace` |
| Definition 2.4, closure | `closure`, `commonCore` | Complete; aliases of the canonical Core closure |
| Definitions 2.5--2.7, group probabilities and distance | `inducedGroupProbability`, `empiricalGroupProbability`, `groupSupDistance` | Complete with the supremum and empty-history qualifications below |
| Definition 2.8, representative generator | `IsAlphaRepresentative` | Complete for positive history lengths |
| Definitions 2.9--2.12, uniform, non-uniform, and limit notions | `AlphaRepresentativeUniformlyGeneratable`, `RepresentativelyUniformlyGeneratable`, `RepresentativelyNonuniformlyGeneratable`, `RepresentativelyGeneratableInLimit` | Complete semantic interfaces |
| Definition 3.1, group closure dimension | `IsGroupClosureWitness`, `GroupClosureDimensionAtLeast`, `HasFiniteGroupClosureDimension`, `HasInfiniteGroupClosureDimension` | Complete proposition-level encoding |
| Theorem 3.3 | `Published.theorem_3_3` | Full; fixed-scale group-closure characterization |
| Corollary 3.4 | `Published.corollary_3_4` | Full; characterization at every positive scale |
| Corollary 3.5 | `Published.corollary_3_5` | Full; finite class and finite partition |
| Corollary 3.6 | `Published.corollary_3_6` | Partial; explicit countably infinite separation witness |
| Theorem 3.7 | `Published.theorem_3_7` | Full; nondecreasing-cover characterization |
| Corollary 3.8 | `Published.corollary_3_8` | Full; countable class with a finite partition |
| Definitions 4.1--4.2, finite support | `finiteSupportSize`, `HasFiniteSupport` | Complete literal printed definitions |
| Lemma 4.3 | `Published.lemma_4_3` | Full, with one tolerance-independent partition |
| Definition 4.5 and Lemma 4.6, criticality | `IsCriticalAt`, `Published.lemma_4_6` | Complete; Lemma 4.6 is a recalled KM proof ingredient |
| Definition 4.7, feasibility | `IsAlphaFeasibleAt` | Complete |
| Lemma 4.8 | `distance_one_le_of_consistent_identity`; `Published.corrected_lemma_4_8` | Printed claim not covered; obstruction core plus a separately named exact-profile repair |
| Theorem 4.4 | `Published.printed_theorem_4_4_counterexample`; `Published.corrected_theorem_4_4` | Printed claim not covered; direct counterexample plus a separately named exact-profile repair |
| Lemma 4.9 | `Published.lemma_4_9` | Full in the documented semantic finite-dialogue model |

## Source qualifications and repairs

### Countable maximum and the empty history

Definition 2.7 prints a maximum over countably many group coordinates, but a
maximum need not be attained. Lean uses the intended supremum
`ENNReal.iSup`. The empirical distribution of distinct observations is not
defined at an empty history, so `empiricalGroupProbability` is totalized there
at zero and `IsAlphaRepresentative` imposes the paper condition only when
`0 < t`.

### Section 3 qualifications

- Corollary 3.5's source proof takes a maximum over a potentially empty
  family and treats a generally nonintegral bound as a natural threshold.
  Lean retains the statement and supplies a finite-exception proof.
- Corollary 3.6 follows text stated after fixing a generic countable example
  space, but its construction needs an infinite universe. Lean exposes the
  intended infinite countable witness as `UniformSeparationUniverse` rather
  than claiming the false finite-universe reading.
- Theorem 3.7's proof does not justify treating the component thresholds as
  nondecreasing. Lean pads thresholds by their class indices, making each
  eligible set finite before selecting its maximum.
- Lemma 4.3 prints one partition outside the tolerance quantifier, while its
  proof chooses a partition after fixing the tolerance. Lean constructs one
  tolerance-independent dominant-block partition and proves the printed
  quantifier order.

### Printed Lemma 4.8 and Theorem 4.4

The printed finite-support argument records intersections determined only by
positive group memberships. For overlapping groups, this does not determine
the full group-membership profile needed to preserve every empirical
proportion. The nested-tail construction in `TailCounterexample.lean` has
finite printed support but cannot be representatively generated in the
limit. It therefore kernel-checks a direct counterexample to the literal
Theorem 4.4 conclusion and supplies the obstruction behind Lemma 4.8.

`ExactProfileSupport.lean` replaces positive-membership intersections by
finite support for complete Boolean group profiles. Under that stronger
premise, `corrected_lemma_4_8` and `corrected_theorem_4_4` recover the intended
construction. The registry keeps both printed source claims marked disputed
pending named human source-correspondence review.

### Lemma 4.9 access model

The finite-query impossibility uses a deterministic adaptive dialogue over
target and group membership, followed by a semantic decoder for a possibly
infinite-support output distribution. Lean's finite-mass blocking diagonal
repairs the printed queue/fairness argument and specializes the construction
to `ℕ`. It does not claim arbitrary-countable-universe transport, a computable
real-valued distribution decoder, or an efficiency bound.

## Reuse and ownership

P09-specific probability distributions, group profiles, representative
generation predicates, group-closure dimension, finite support, and query
models remain inside `GenLimit.Paper09_RepresentativeLanguageGeneration`.
They are not promoted into Core.

The development reuses Core's generic languages, streams, samples, version
spaces, common cores, closure, and ordinary generation predicates.
`Relationships.lean` records the implications from representative uniform,
non-uniform, and limit generation to their ordinary counterparts. The
Corollary 3.6 separation construction reuses the #02 cofinite example through
an explicit P09 import rather than duplicating that witness.

## Module organization and reading order

```text
Distribution.lean              discrete distributions and group profiles
Definitions.lean               representative-generation semantics
Relationships.lean             Core aliases and representative-to-ordinary implications
GroupClosure.lean              Definition 3.1 and Theorem 3.3
NonuniformCharacterization.lean  Theorem 3.7
FinitePartitionCorollaries.lean  Corollaries 3.5 and 3.8
UniformSeparation.lean         Corollary 3.6
FiniteSupport.lean             literal Definitions 4.1--4.2
TailCounterexample.lean        printed finite-support obstruction
LimitFoundations.lean          criticality, feasibility, and Lemma 4.6
ExactProfileSupport.lean       corrected Lemma 4.8 and Theorem 4.4
FiniteQueryImpossibility.lean  finite adaptive-dialogue core
QueryImpossibility.lean        full Lemma 4.9 diagonal
Results/Overview.lean          compact published-result surface
```

A short reading path is:

```text
Definitions
  -> GroupClosure
  -> NonuniformCharacterization / FinitePartitionCorollaries
  -> TailCounterexample / ExactProfileSupport
  -> QueryImpossibility
  -> Results.Overview
```

## Verification and audit boundary

Focused checks are:

```text
lake build GenLimit.Paper09_RepresentativeLanguageGeneration
lake env lean RegistryAudit.lean
```

The P09 modules contain no `sorry`, `admit`, project-defined axiom, or
`unsafe` declaration. The generated registry audit checks the existence,
defining module, and project axiom allowlist for every claim-linked endpoint.
These kernel checks establish the Lean statements, not their correspondence
with the paper. The source identity and claim-by-claim qualifications are
recorded in [`registry/papers/P09.json`](../../registry/papers/P09.json); no
named human correspondence audit is currently claimed.
