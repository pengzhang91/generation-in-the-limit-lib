# #28 Contrastive Generation map

Native Lean module: `GenLimit.Paper28_ContrastiveGeneration`.
Declaration namespace retained for API compatibility:
`GenLimit.ContrastiveGeneration`.

Source: Xiaoyu Li, Andi Han, Jiaojiao Jiang, and Junbin Gao,
*Contrastive Identification and Generation in the Limit*.

- pinned source: [arXiv:2605.06211v1](https://arxiv.org/abs/2605.06211v1),
  submitted 2026-05-07;
- audit evidence, provenance, and repair chronology:
  [#28 audit record](../AuditRecords/Paper28_ContrastiveGeneration/).

## Main entry points

- `GenLimit.ContrastiveGeneration.theorem_4_7`;
- `GenLimit.ContrastiveGeneration.theorem_5_4` and its quantitative and sharp
  threshold variants;
- `GenLimit.ContrastiveGeneration.theorem_5_5`;
- `GenLimit.ContrastiveGeneration.proposition_5_8` and `proposition_5_11`;
- `GenLimit.ContrastiveGeneration.proposition_5_12`;
- `GenLimit.ContrastiveGeneration.theorem_5_13_5_14_punctured_witness` and
  `theorem_5_13_5_14_disjoint_witness`;
- `GenLimit.ContrastiveGeneration.theorem_6_5`, `theorem_6_6`, and
  `theorem_6_8`;
- `GenLimit.ContrastiveGeneration.absenceCountIdentifier_finitely_identifies`
  (added by the separately tracked interface repair); and
- `GenLimit.ContrastiveGeneration.proposition_6_3_defect_eq_forced_wrong_cut_infimum`.

## Representation

| Paper object | Lean representation |
|---|---|
| Countably infinite example space | Type `α` with countability/infinitude typeclasses where required |
| Countable hypothesis class | Indexed family `ℕ → Set α` for identification; extensional `Set (Set α)` for generation and geometry |
| Unordered contrastive pair `{x,y}` | Oriented `Edge α`; `Crosses` and incidence are swap-invariant, and dimension counts use `UnorderedEdge` |
| Valid contrastive presentation | Every edge crosses the target and every positive point eventually occurs; negatives need not be covered |
| Contrastive identifier | Total semantic function of a finite edge prefix, converging to a stable index denoting the target |
| Contrastive generator | Total semantic function of a finite edge prefix, eventually outputting a target point not yet observed |
| Finite corruption | Core's occurrence-count contamination bound, with exact positive-side coverage retained; the edge-validity specialization remains paper-local |
| Defect number | Extended-natural cardinality `ℕ∞` and an exact infimum over clean presentations |

The paper's learner observes unordered pairs. Lean learners receive an
orientation, although all semantic crossing predicates and the canonical
dimension carrier forget it. The source comparison judged semantic existence results
transportable by a classical orientation choice, but no target-scope theorem
states that transport or requires learner swap-invariance.

## Statement correspondence

| Paper item | Lean declaration | Correspondence status |
|---|---|---|
| Definition 4.1 and Proposition 4.2 | `NotEliminableFrom`, `proposition_4_2` | Pairwise geometric characterization preserved under the paper's enumeration assumptions |
| Theorem 4.3 and Lemma 4.4 | `theorem_4_3`, `lemma_4_4` | Four-region and shared-presentation equivalences kernel checked |
| Lemma 4.6 | `lemma_4_6_inclusion` | Contrastive identification implies text identification |
| Theorem 4.7 | `theorem_4_7_identifier_equivalence`, `theorem_4_7_geometric_equivalence`, `theorem_4_7` | Complete three-way semantic characterization |
| Definitions 5.1--5.3 and Theorem 5.4 | closure/dimension interfaces, `theorem_5_4_quantitative`, `theorem_5_4` | Exact qualitative and `d+1` quantitative characterization; sharpness is among positive thresholds |
| Theorem 5.5 | `theorem_5_5_necessity`, `theorem_5_5_sufficiency`, `theorem_5_5` | Complete increasing-cover characterization with noncomputable bound selection |
| Propositions 5.8 and 5.11 | `proposition_5_8`, `proposition_5_11` | Safe-core and eventual-core sufficient conditions |
| Proposition 5.12 | `proposition_5_12` | Conditional obstruction, with a shared presentation and exact finite intersection supplied as certificates |
| Theorems 5.13--5.14 | two `theorem_5_13_5_14_*_witness` declarations | Concrete component witnesses checked; the full clean strict diamond is not packaged |
| Definitions 6.1--6.2 | corrupted-presentation interfaces, `positiveDefectSet`, `defectNumber` | Occurrence-count corruption and extended-natural defect preserved |
| Proposition 6.3 | two `proposition_6_3_*` declarations | Exact defect-infimum equality and zero-defect/non-eliminability equivalence |
| Theorem 6.5 | `theorem_6_5` | Co-singleton text-fragility result |
| Algorithm 1 | `absenceCount`, `absenceCountIdentifier` | Correct finite-prefix absence statistic; arbitrary classical minimizer, not the paper's effective fixed-enumeration tie-breaker |
| Theorem 6.6 | `theorem_6_6`, `absenceCountIdentifier_finitely_identifies` | The immutable baseline has the exact existential `∃ I, ∀ k` conclusion; the current public repair additionally exposes the named absence-count witness for every budget, target, and presentation. The interface gap is resolved, but effective tie-breaking and computability remain unproved |
| Example 6.7 | `example_6_7_absence_counts`, `example_6_7_unique_minimizer` | Displayed finite trace and unique minimizer checked |
| Theorem 6.8 | `theorem_6_8` | Two-way corrupted-identification incomparability with explicit arithmetic witnesses |

## Scope not established by the Lean statements

This map does not claim a complete formalization of:

- a single theorem assembling the full clean strict diamond, especially the
  general inclusion from contrastive generation to text generation and the
  strictness of text identification inside text generation;
- transport between unordered paper observations and the oriented learner
  interface;
- the finite-family common-crossing/membership-pattern criteria and the
  displayed unbounded hollow witnesses for the punctured family;
- the headline general implication from pairwise infinite defect gaps to
  finite-corruption identification;
- corrupted generation, random contrastive presentations, probabilistic
  rates, or spectral claims; or
- a constructive, oracle-free Algorithm 1 with computable fixed-enumeration
  tie-breaking and a runtime theorem.

The paper's printed Example 5.9 also needs stronger set assumptions than its
main-text statement supplies; the appendix adds disjoint infinite sets and a
nonempty exterior. Lean does not formalize the under-specified printed
example, and instead uses a different valid punctured-family witness.

## Difficulty and assumption boundary

Several Lean statements generalize beyond the paper's countable setting, but
some sufficiency results take strong semantic certificates as hypotheses:
finite tell-tales, increasing finite-dimension covers, safe or eventual cores,
a shared presentation, or an exact finite intersection. These are legitimate
interfaces and do not literally assume the theorem conclusion, but they must
not be read as constructive algorithms for finding the certificates.

Theorem 5.4's least-threshold statement restricts comparison to positive
thresholds, making the empty-prefix `d = 0` convention explicit. Valid
presentations can also be absent for degenerate targets in broader Lean
universes, so some generalized implications can be vacuous outside the
paper's standing nontriviality assumptions.

No computability, runtime, oracle-complexity, or statistical guarantee follows
from the semantic functions alone. The source scan contains no `sorry`,
`admit`, or project-defined axiom, and repository CI checks the published
entry points through `Audit.lean`.

The ChatGPT Pro record and pending human-review status live in the
[#28 audit record](../AuditRecords/Paper28_ContrastiveGeneration/) and the
[authoritative human-audit ledger](../AuditRecords/Human/README.md).
