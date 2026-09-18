# Cross-paper reuse in the Lean library

This note records reusable definitions, constructions, and proof ideas that
emerged from formalizing a closely related collection of language-generation
papers in one Lean library. Its purpose is mathematical and architectural: it
documents common structure that is easy to miss when each paper is read or
formalized in isolation.

The entries below do not claim that two papers state the same theorem. A shared
Lean kernel may capture only one common combinatorial step, representation, or
quantifier pattern inside otherwise different results. Explicit theorem-level
relationships are identified separately from implementation reuse.

## How to read the reuse map

The library uses four kinds of reuse:

1. **Shared vocabulary**: the same mathematical object is represented once in
   `Core` and exposed through paper-facing compatibility names.
2. **Shared construction**: papers keep their own algorithms, but delegate a
   recurring selector, presentation, finite-history, or query-tree operation
   to `Support`.
3. **Shared proof kernel**: theorem statements remain paper-specific while a
   common counting, stabilization, or finite-set argument is proved once.
4. **Explicit bridge**: Lean proves that two paper interfaces are equivalent
   under stated assumptions. This is the strongest form of recorded
   cross-paper relationship.

`Core` contains stable mathematical vocabulary intended to be broadly useful.
`Support` contains reusable constructions and proof machinery without claiming
that the corresponding paper-level notions are identical. `Bridges` records
comparisons that deliberately connect two paper developments.

## Shared interfaces

| Shared interface | Papers using it | What was unified |
|---|---|---|
| [`FiniteHistoryOperator`](GenLimitLean/GenLimit/Core/GenericGeneration.lean) | P02, P04, P08, P09, P14, P17, P18, P22, P27, P28 | A finite-history input/output operator. Existing paper-facing `Generator`, set-generator, identifier, and strategy names remain compatibility specializations. |
| [`EventualGeneration`](GenLimitLean/GenLimit/Core/EventualGeneration.lean) | P06, P12, P19 | Three distinct quantifier patterns: one uniform cutoff, one cutoff per target, and one cutoff per presentation. Keeping all three prevents an accidental strengthening when papers use different notions of eventual correctness. |
| [`HistoryChain`](GenLimitLean/GenLimit/Support/HistoryChain.lean) | P00, P02, P07, P09, P10, P12, P17, P21, P22 | Append-only finite histories and the limit stream that they determine. `PrefixChain` is deliberately weaker so that ledgers which may pause for a round can reuse prefix reasoning without satisfying a progress bound. |
| [`FiniteMembershipQueryTree`](GenLimitLean/GenLimit/Support/FiniteMembershipQueryTree.lean) | P08, P27 | A finite adaptive Boolean-query tree parameterized by query and leaf types. It supports both detector outputs and set-valued feedback strategies. |
| [`IsFiniteTellTale`](GenLimitLean/GenLimit/Support/FiniteTellTale.lean) | P0, P0A, P03, P04, P05 and related developments | The common finite tell-tale predicate. Paper-specific names can remain as compatibility abbreviations; the weaker tell-tale variants remain separate concepts. |
| Ordered-density API in [`OrderedDensity.lean`](GenLimitLean/GenLimit/Core/OrderedDensity.lean) | P07, P15, P23, P39 where applicable | Prefix counts, upper/lower density, finite-contamination invariance, and common density inequalities. Distinct window/Banach-density notions are not identified with this API. |

## Reusable constructions

| Construction | Main consumers | Reusable idea |
|---|---|---|
| [`Fresh.lean`](GenLimitLean/GenLimit/Support/Fresh.lean) | P01, P06, P07, P15, P21 | Choose an element of an infinite language outside a finite forbidden set, with both arbitrary-choice and least-element variants. |
| [`LeastCandidate.lean`](GenLimitLean/GenLimit/Support/LeastCandidate.lean) | P01, P04, P05, P07, P18, P39 | Least/greatest finite candidate with fallback, plus the least index extensionally equivalent to a given language. |
| [`Presentations.lean`](GenLimitLean/GenLimit/Support/Presentations.lean) and [`EnumerationProgress.lean`](GenLimitLean/GenLimit/Support/EnumerationProgress.lean) | P0/P0A, P02, P19, P21, P31 and other presentation arguments | Exact positive presentations, prefix-plus-tail presentations, injective enumerations of infinite sets, and finite progress through an enumeration. |
| [`FiniteEnumeration.lean`](GenLimitLean/GenLimit/Support/FiniteEnumeration.lean) | P0A, P04, P05 | Stage contents of a finite enumeration and eventual stabilization to the enumerated finite set. This isolates the common endgame behind several tell-tale arguments. |
| [`PriorityRound.lean`](GenLimitLean/GenLimit/Support/PriorityRound.lean) | P07, P15 | A priority queue round that emits a fresh least output while preserving the paper-specific state and validity invariants. |
| [`TurnTaking/Announcements.lean`](GenLimitLean/GenLimit/Support/TurnTaking/Announcements.lean) | P30, P39 | First-announcement times, predecessor pairing, and the adversary-first/generator-first partition used by turn-taking counting arguments. |
| [`Renaming.lean`](GenLimitLean/GenLimit/Support/Renaming.lean) | P19 and other transport developments | Transport of languages, classes, streams, samples, presentations, generators, and correctness along equivalences of universes. |

The `HistoryChain` extraction is a useful architectural lesson. Many papers
had independently proved almost the same finite-history plumbing. Moving it to
`Support` produced only a modest net line reduction because each paper still
has to instantiate the shared structure with its own hypotheses. Its main
benefit is therefore not code golf: it prevents many copies of the same
bookkeeping theorem from drifting apart and gives future formalizations a
discoverable construction-level API.

## Shared proof kernels

| Kernel | Papers connected | Common mathematical step |
|---|---|---|
| Finite-scope consistency and tell-tale stabilization | P0A, P04, P05 and the shared presentation layer | Once finitely many candidates or enumerated elements have stabilized, later prefixes have the required static property. |
| Finite subclass and closure cores | P06, P09, P21 | Restrict a class to a finite subfamily and transport version-space/common-core or closure information through that restriction. |
| Powerset uncountability | P02, P10, P22 | Reuse one Cantor-style obstruction rather than reconstructing an uncountable family separately in each hierarchy or diagonal argument. |
| Prefix causality | P30 and the generic sample API | Two streams agreeing through a finite prefix induce the same finite observation and therefore the same causal output. |
| Density counting and liminf endgames | P07, P15, P39 | Convert an eventual linear counting inequality into a lower-density conclusion; share finite-error and shifted-output bookkeeping without equating the papers' algorithms. |
| Announcement and predecessor accounting | P30, P39 | Pair delayed or newly announced elements with earlier rounds and transfer injectivity into a cardinality bound. |
| Exact-presentation and finite-progress lemmas | P0, P0A, P27, P28, P31 | Turn exact range equality or finite coverage into the concrete prefix witness needed by a later algorithm. |

## Explicit cross-paper relationships exposed by Lean

Some relationships go beyond code deduplication. They are mathematical
comparisons made precise by Lean.

### P12 and P19: the same fixed-noise eventual interface

[`Paper12ToPaper19.lean`](GenLimitLean/GenLimit/Bridges/Paper12ToPaper19.lean)
proves equivalences between the two developments after fixing a noise level:

- their noisy-enumeration predicates agree;
- their pointwise correctness predicates agree;
- their nonuniform noisy-generation predicates agree; and
- the corresponding existence-level generatability statements agree.

This is theorem-level reuse, not merely a shared helper. It shows that two
papers package the same fixed-level semantic interface differently.

### P07, P15, and P39: a common density-accounting skeleton

These papers use different algorithms and theorem statements, but several
endgames share the same structure: establish an eventual linear count bound,
control a finite or shifted error term, and pass to a liminf. Lean separates
that common skeleton from the paper-specific invariant that supplies the
counting inequality. The extraction therefore records a reusable proof idea
without claiming equality of the main theorems.

### P30 and P39: turn-taking combinatorics

The first-announcement partition and predecessor injection appear in two
different algorithmic settings. Formalization revealed that their counting
arguments depend on the same paper-independent combinatorial kernel even
though the surrounding machines and performance guarantees differ.

### P08 and P27: adaptive finite-query semantics

Both developments evaluate a finite binary tree whose next query depends on
earlier Boolean answers. The leaf result differs—a detector result in one case
and a feedback/query result in the other—but the adaptive-query semantics is
the same polymorphic tree.

### Fresh-element selection across generation models

P01, P06, P07, P15, and P21 repeatedly require the elementary but central
fact that an infinite target or candidate has an element outside a finite
observed/reserved set. Making this construction explicit shows how many
apparently different generators share the same exploration primitive.

### Provenance boundary

The relationships in this section were exposed or made explicit while
comparing the Lean developments. Unless a paper map or source audit separately
cites a statement from the paper, this note does **not** attribute the
cross-paper relationship to the paper authors. In particular, the P12–P19
bridge is a kernel-checked theorem of this library; this document does not
claim that either source paper explicitly states that equivalence. The same
caution applies to the shared density, turn-taking, query-tree, and
fresh-selection patterns.

## Important non-equivalences

The reuse map also records boundaries discovered during refactoring:

- P01 `Critical`, P07 `StrictCritical`, and P39 recursive criticality are not
  the same predicate and should not be merged.
- P22's carried-cutoff and witness-protection machines are intentionally
  different algorithms, not accidental duplicates.
- Ordered prefix density is not the same as P23's window/Banach density.
- A theorem using the shared `FiniteHistoryOperator` representation is not
  automatically equivalent to every other theorem using that representation.
- A shared semantic construction does not establish computability, runtime,
  query complexity, or a statistical rate unless the paper-specific theorem
  proves those properties separately.
- Similar proof text inside one paper may be better handled by local
  parameterization; it is not automatically a cross-paper abstraction.

These negative results are useful: a reuse audit should prevent false
identifications as well as find valid abstractions.

## Verification status

The extraction represented by the September 2026 reuse-refactor commits was
checked in three layers:

- affected modules and paper umbrellas were built incrementally;
- a final repository-wide `lake build` completed successfully (3,789 jobs);
- declaration-index, claim-registry, fingerprint, and Lean machine-audit
  checks passed.

The refactor changed implementation bodies covered by earlier human audits in
three places. P01, P02, and P10 are therefore conservatively marked
`needs-review`; their old reviewed fingerprints were not overwritten. This is
an applicability-maintenance task, not evidence that the refactored theorems
are incorrect. The tracked status and review notes are recorded under
[`AuditRecords/Human/Fingerprints`](GenLimitLean/AuditRecords/Human/Fingerprints/README.md).

## Maintenance rule

When a future formalization exposes another cross-paper relationship, add an
entry here only after checking the relevant definitions, theorem statements,
and proof dependencies. Record:

1. the shared Lean module or bridge;
2. the paper developments involved;
3. whether the relationship is vocabulary, construction, proof-kernel, or
   theorem-level reuse;
4. the assumptions under which it holds; and
5. any nearby notions that must remain distinct.

Line-count reduction is secondary. The main criterion is whether the shared
abstraction makes a genuine recurring mathematical or algorithmic idea easier
to find, use, and audit.
