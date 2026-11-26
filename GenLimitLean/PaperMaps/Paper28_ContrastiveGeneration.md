# #28 Contrastive Generation map

Native Lean module: `GenLimit.Paper28_ContrastiveGeneration`.
Declaration namespace retained for API compatibility:
`GenLimit.ContrastiveGeneration`.

Public main-results facade: `GenLimit.Paper28_ContrastiveGeneration.Results.Overview`.

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

[UnorderedStrategies.lean](../GenLimit/Paper28_ContrastiveGeneration/UnorderedStrategies.lean) proves equivalence with strategies on the paper’s unordered pairs for clean identification, eventual generation, uniform and nonuniform generation, and identification under all finite corruption budgets. The fixed canonical orientation preserves every input prefix. The uniform theorem preserves the exact threshold.

## Statement correspondence

| Paper item | Lean declaration | Correspondence status |
|---|---|---|
| Definition 4.1 and Proposition 4.2 | `NotEliminableFrom`, `proposition_4_2` | Pairwise geometric characterization preserved under the paper's enumeration assumptions |
| Theorem 4.3 and Lemma 4.4 | `Results.theorem_4_3`, `lemma_4_4` | Four-region criterion, N1/N2/N3 alternatives for distinct supports, and pairwise shared presentations |
| Lemma 4.6 | `lemma_4_6_inclusion` | Contrastive identification implies text identification |
| Theorem 4.7 | `theorem_4_7_identifier_equivalence`, `theorem_4_7_geometric_equivalence`, `theorem_4_7` | Complete three-way semantic characterization |
| Definitions 5.1--5.3 and Theorem 5.4 | `Results.theorem_5_4` in the Overview, with the finite-bound equivalence `theorem_5_4_quantitative` in `ClosureDimension.lean` | Exact qualitative and `d+1` quantitative characterization; sharpness is among positive thresholds |
| Theorem 5.5 | `theorem_5_5_necessity`, `theorem_5_5_sufficiency`, `theorem_5_5` | Complete increasing-cover characterization with noncomputable bound selection |
| Propositions 5.8 and 5.11 | `proposition_5_8`, `proposition_5_11` | Safe-core and eventual-core sufficient conditions |
| Proposition 5.12 | `proposition_5_12` | Conditional obstruction, with a shared presentation and exact finite intersection supplied as certificates |
| Theorems 5.13–5.14 | `Results.theorem_5_13` and `Results.theorem_5_14` | All four strict inclusions and both directions of incomparability use the same domain of countable indexed families of infinite proper supports. |
| Definitions 6.1--6.2 | corrupted-presentation interfaces, `positiveDefectSet`, `defectNumber` | Occurrence-count corruption and extended-natural defect preserved |
| Proposition 6.3 | `Results.proposition_6_3` | Exact defect-infimum equality and zero-defect/non-eliminability equivalence |
| Theorem 6.5 | `theorem_6_5` | Co-singleton text-fragility result |
| Algorithm 1 | `absenceCount`, `absenceCountIdentifier` | Correct finite-prefix absence statistic; arbitrary classical minimizer, not the paper's effective fixed-enumeration tie-breaker |
| Theorem 6.6 | `theorem_6_6`, `absenceCountIdentifier_finitely_identifies` | The immutable baseline has the exact existential `∃ I, ∀ k` conclusion; the current public repair additionally exposes the named absence-count witness for every budget, target, and presentation. The interface gap is resolved, but effective tie-breaking and computability remain unproved |
| Example 6.7 | `example_6_7_absence_counts`, `example_6_7_unique_minimizer` | Displayed finite trace and unique minimizer checked |
| Theorem 6.8 | `theorem_6_8` | Two-way corrupted-identification incomparability with explicit arithmetic witnesses |

The introduction’s fourth main result follows from `Results.infinite_defect_identification`. A single identifier searches over pairs consisting of a candidate index and finitely many exceptional rounds. Pairwise infinite directed defect eventually excludes every wrong surviving candidate. The distinct co-singleton pair has a single common crossing edge and infinite directed defect. [InfiniteDefect.lean](../GenLimit/Paper28_ContrastiveGeneration/InfiniteDefect.lean)

## Supporting material outside the main results

This map does not claim a complete formalization of:

- the finite-family common-crossing/membership-pattern criteria and the
  displayed unbounded hollow witnesses for the punctured family;
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

The ChatGPT Pro record and the human-review status live in the
[#28 audit record](../AuditRecords/Paper28_ContrastiveGeneration/) and the
[authoritative human-audit ledger](../AuditRecords/Human/README.md).

## Human statement audit

Shuangping Li completed a Level 1 human audit of all 19
`Results/Overview.lean` statements and their defining interfaces on
13 November 2026 at checkpoint `c828be2`; the
[human-audit ledger](../AuditRecords/Human/README.md#28-contrastive-identification-and-generation-arxiv-v1-overview-level-1)
records the scope. Theorem 4.3 is reviewed in its coverage form, Theorem 4.7
as (i) iff (iii), and Theorem 5.13 through its strictness witnesses only.
Construction/proof correspondence is outside that audit.
