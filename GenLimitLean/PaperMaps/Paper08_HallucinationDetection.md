# #08 Hallucination Detection map

Native Lean module: `GenLimit.Paper08_HallucinationDetection`. The declaration
namespace remains `GenLimit.HallucinationDetection` for API compatibility. The cross-paper
Theorem A.2 entry point is added by
`GenLimit.Bridges.Paper02ToPaper08` and the global
`GenLimit` umbrella.

Source: Amin Karbasi, Omar Montasser, John Sous, and Grigoris Velegkas,
*`(Im)possibility of Automated Hallucination Detection in Large Language
Models`*.

- pinned source: [`arXiv:2504.17004v2`](https://arxiv.org/abs/2504.17004v2);
- audited PDF SHA-256:
  `b4268bc32c32c7aa3660b8f54c425b8d1a2534f23cfab10774a5d2b592e847c0`;
- visually checked source locations: Definition 1 and Example 1 on pp. 5--6;
  Theorem 2.1, Corollary 2.2, Definition 2, Theorem 2.3, and Lemmas 3.1--3.2
  on pp. 7--9; the two proof algorithms on pp. 10--13; and Appendix
  Definitions 3--5 and Theorems A.1--A.2 on pp. 19--20.
- audit evidence and provenance:
  [#08 audit record](../AuditRecords/Paper08_HallucinationDetection/).

Every numbered definition, algorithm, lemma, corollary, and theorem in the
paper is represented, and every valid numbered result is kernel checked.  The
formal development also disproves one unnumbered prose inference immediately
after Example 1; see “Source inconsistency” below.

The checksum-pinned audit snapshot also contained ten #08-local history and
locking helpers (D33--D42). The later #0A refactor replaced their only use by
the Gold-backed semantic necessity theorem and removed that duplicated
auxiliary interface. This does not remove a numbered #08 paper claim.

## Main entry points

- `GenLimit.HallucinationDetection.lemma_3_1_identification_implies_detection`;
- `GenLimit.HallucinationDetection.lemma_3_2_detection_implies_identification`;
- `GenLimit.HallucinationDetection.theorem_2_1`;
- `GenLimit.HallucinationDetection.corollary_2_2`;
- `GenLimit.HallucinationDetection.theorem_2_3`;
- `GenLimit.HallucinationDetection.theorem_A_1`; and
- `GenLimit.HallucinationDetection.theorem_A_2`.

The first six substantive #08 modules are native and import the supporting
[#0A development](Paper00A_PositiveDataInference.md), whose declarations
retain the `GenLimit.Angluin` namespace, but no #02 Learning Theory theorem.
Theorem A.2 is the one genuine cross-paper dependency: its declaration is
physically owned by
`GenLimit.Bridges.Paper02ToPaper08`, where the paper's appendix generation
interface is connected to #02 Learning Theory Corollary 3.6.
The public namespace remains `GenLimit.HallucinationDetection` so the paper
entry point is stable, while the bridge location makes the dependency honest.
The separate `GenLimit.Bridges.Paper03ToPaper08` comparison records that exact
P03 fresh breadth implies detection and, under P03's family-membership oracle,
is equivalent to detection.  This derived result is not imported by either
native paper umbrella.

## Representation

| Paper object | Lean representation |
|---|---|
| Countable domain `X` | Arbitrary type `α` with `[Nonempty α] [Countable α]` |
| Countable collection `L = {L_1,L_2,...}` | `GenLimit.Generic.LanguageFamily α = ℕ → Set α` |
| Enumeration of `K` | `GenLimit.Generic.Presents stream K` |
| Candidate LLM output set `G` | `Set α` |
| One finite adaptive batch of membership queries to `G` | `OracleTree α` |
| Hallucination detector | `Detector α` |
| Identifier | `GenLimit.Angluin.SemanticIdentifier α` |
| Labeled enumeration of the domain | `IsLabeledEnumeration stream K` |
| Detector with negative examples | `NegativeExampleDetector α` |

`OracleTree` is an inductive finite decision tree.  An internal node asks
membership of one point in `G`; its two children are the yes and no
continuations.  Consequently every detector round makes finitely many
adaptive queries by construction.  The collection membership tests used by
Algorithms 1--2 remain semantic/oracular, matching the paper's standing
membership-oracle convention and its explicit absence of computational
restrictions.

## Definition and theorem correspondence

| Paper item | Lean declaration | Status |
|---|---|---|
| Definition 1, detector and convergence | `Detector`, `DetectorCorrectAt`, `DetectsHallucinations`, `HallucinationDetectable` | Complete |
| Finite adaptive query restriction | `OracleTree`, `OracleTree.eval` | Complete by type, not an unrestricted set-function abstraction |
| Definition 3, identification in the limit | `IdentifiableInLimit`, reusing `GenLimit.Angluin.SemanticallyIdentifies` | Complete semantic interface |
| Definition 3, literal consecutive-guess form | `ConsecutivelyIdentifiesFrom`, `ConsecutivelyIdentifies`, `definition_3_equivalence` | Complete, including equivalence to stable-index convergence |
| Algorithm 1 | `subsetTestTree`, `detectorFromIdentifier` | Complete |
| Lemma 3.1 | `lemma_3_1_identification_implies_detection` | Complete |
| Algorithm 2 | `DetectorCandidate`, `identifierFromDetector` | Complete |
| Lemma 3.2 | `lemma_3_2_detection_implies_identification` | Complete |
| Theorem 2.1 | `theorem_2_1` | Complete |
| Definition 4, Angluin's finite tell-tale condition | shared `GenLimit.Angluin.ConditionTwo` | Partial: the finite tell-tale predicate is complete, but the operational primitive enumerating a selected tell-tale is not modeled |
| Corollary 2.2 | `corollary_2_2` | Complete, including empty indexed languages; directly combines Theorem 2.1 with the canonical `GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo` |
| Definition 2, labeled negative-example detection | `IsLabeledEnumeration`, `DetectsWithNegativeExamples`, `DetectableWithNegativeExamples` | Complete |
| Theorem 2.3 algorithm | `negativeExampleTree`, `negativeExampleDetector` | Complete |
| Theorem 2.3 | `theorem_2_3` | Complete; Lean proves the stronger statement for every indexed collection |
| Example 1, multiples and containments | `multiplesFamily`, `example_1_L4_subset_L2`, `example_1_L3_not_subset_L2` | Complete |
| Definition 5, generation in the limit | `AppendixGenerationCorrectAt`, `AppendixGeneratesInLimit`, `AppendixGeneratableInLimit` | Complete |
| Theorem A.1 | `theorem_A_1` | Complete |
| Theorem A.2 | `theorem_A_2` | Complete; physically in `GenLimit.Bridges.Paper02ToPaper08` because it uses #02 Corollary 3.6 |

## Proof correspondence

For Lemma 3.1, Lean follows Algorithm 1.  The current identifier conjecture
is tested on the first `t` points of a fixed surjective enumeration of `X`.
If `G` is not contained in the target, its first counterexample eventually
enters the tested prefix; after the identifier stabilizes, the detector then
rejects forever.

For Lemma 3.2, `DetectorCandidate` is exactly the conjunction in Algorithm 2:
the index is at most the current time, the language is consistent with all
positive examples, and the detector says the candidate language is contained
in the target.  Lean chooses the least such index.  Every earlier wrong index
eventually fails either consistency or the detector test, while the least
index denoting the target eventually passes both.

For Theorem 2.3, the finite query tree asks only about negatively labeled
points already observed.  If `G ⊆ K`, none can belong to `G`.  If not, a point
of `G \ K` eventually appears in the complete labeled domain enumeration and
causes permanent rejection.

## Source inconsistency

Example 1 defines `L_i` as the positive multiples of `i`, correctly observes
`L_4 ⊆ L_2` and `L_3 ⊄ L_2`, and then claims that Theorem 2.1 plus Angluin's
characterization rules out a detector.  The inference is false.  For every
`i`, the singleton `{i}` is a finite tell-tale for `L_i`: any multiples
language containing `i` and contained in `L_i` must equal `L_i`.
`singleton_index_isTellTale`, `example_1_angluinCondition`, and
`example_1_hallucinationDetectable` kernel-check this counterdiagnosis.  The
formalization preserves the two correct displayed containments but does not
assert the contradictory prose sentence.

## Exact boundary and edge convention

The source permits finite languages but defines an enumeration as an infinite
sequence all of whose entries lie in the language.  Hence the empty language
has no legal enumeration.  Without a nonemptiness convention, identification
and detection for an empty indexed language are vacuous.  The exact
Corollary 2.2 nevertheless remains valid without an added nonemptiness
assumption: the empty finite set is a tell-tale for an empty target, while the
locking-sequence argument is used only for nonempty targets.  Lean separates
those cases explicitly.

The paper writes correctness for all `t > t*`; Lean writes an equivalent
tail bound `T ≤ t`.  The indexed family may contain repeated languages, and
the identifier stabilizes to one fixed index denoting the target, exactly as
required by Definition 3.

No computability claim is made for #08. The paper explicitly removes
computational restrictions and assumes membership-oracle access. The full
effective version of Angluin's 1980 Theorem 1 is formalized separately in
#0A and does not turn #08's detector or membership-oracle reductions into
effective algorithms.

## Verification

The source scan contains no `sorry`, `admit`, or project-defined axiom.
Repository CI builds the native #08 modules, the #0A identification theory, and
the explicit #02-to-#08 bridge, then checks their published entry points in
`Audit.lean`. The ChatGPT Pro record and pending human-review status live in
the [#08 audit record](../AuditRecords/Paper08_HallucinationDetection/) and
the [authoritative human-audit ledger](../AuditRecords/Human/README.md).
