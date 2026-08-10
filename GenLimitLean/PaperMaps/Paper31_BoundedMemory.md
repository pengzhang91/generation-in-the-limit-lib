# #31 Bounded Memory map

Native Lean module: `GenLimit.Paper31_BoundedMemory`.
Declaration namespace retained for API compatibility: `GenLimit.BoundedMemory`.

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*.

- pinned source: [arXiv:2605.30324v1](https://arxiv.org/abs/2605.30324v1),
  submitted 2026-05-28;
- audit evidence, provenance, and repair chronology:
  [#31 audit record](../AuditRecords/Paper31_BoundedMemory/).

## Main entry points

- `GenLimit.BoundedMemory.theorem_1_1`;
- `GenLimit.BoundedMemory.theorem_3_1` and its necessity and sufficiency
  directions;
- `GenLimit.BoundedMemory.theorem_3_2_element`, `theorem_3_2_index`, and
  `theorem_3_2`;
- `GenLimit.BoundedMemory.lemma_4_3_lower_density_bound_from_partition` and
  `lemma_4_4_zero_lower_density_partition`;
- `GenLimit.BoundedMemory.symmetric_chain_decomposition_range` and
  `symmetric_chain_decomposition_fintype`;
- `GenLimit.BoundedMemory.lemma_4_7_sperner_hard_instance`,
  `lemma_4_8_sperner_achievability`, and
  `theorem_4_1_memoryless_minimax_upper_density`;
- `GenLimit.BoundedMemory.theorem_4_2_no_uniform_positive_lower_density`;
- `GenLimit.BoundedMemory.lemma_4_11_finite_exception`,
  `lemma_4_12_single_hard_instance`, and
  `theorem_4_10_window_minimax_upper_density`;
- `GenLimit.BoundedMemory.theorem_4_15_adaptive_buffer_lower_bound`;
- `GenLimit.BoundedMemory.proposition_5_1`, `theorem_5_2_ordered`, and
  `theorem_5_2`;
- `GenLimit.BoundedMemory.proposition_A_2`, `theorem_A_1_triangle`, and
  `theorem_A_1`; and
- `GenLimit.BoundedMemory.incremental_coding_compilation` and
  `incremental_element_generation`.

`lemma_A_3` was absent from the checked baseline list.

Current entry point added by the separately tracked repair:

- `GenLimit.BoundedMemory.lemma_A_3`.

## Representation and memory interfaces

| Paper object | Lean representation at the checked baseline |
|---|---|
| Countable example universe | Generic countable types for Theorem 3.1 and some obstructions; `ℕ` for Theorem 1.1, density, windows, buffers, and incremental element coding |
| Countable language collection | Extensional `Set (Set α)` or an enumeration `ℕ → Set ℕ`; finite quantitative families use `Fin k → Set ℕ` |
| Exact presentation | A stream whose range equals the target; finite repetition is stated pointwise and repetition-free streams are injective |
| Memoryless set generator | A semantic function `α → Set α`; eventual successful outputs must be infinite and target-contained, but the raw codomain does not enforce global infinitude |
| Ordered density | `OrderedLanguage.prefixRatio`, `lowerDensity`, and `upperDensity` on a separately supplied ordered realization of each target |
| Sliding window | A distinct `Fin W → α` window, with success required on injective exact presentations |
| Adaptive buffer | An ordered state of at most `b` observed examples; the next state may retain, discard, reorder, or repeat old/current entries |
| Exact incremental index model | The output index is also the entire persistent state; the three-language obstruction has exactly three states |
| Approximate incremental learner | A last-guess learner over a finite indexing, eventually outputting a language almost contained in the target |
| Incremental element generator | The next output depends only on the previous output and newest example; the unbounded natural output deliberately encodes full history |

The last row is not a hidden finite-bit-memory claim. The paper deliberately
uses the previous unbounded output as storage in Appendix A, and the Lean
coding theorem exposes that mechanism directly.

## Statement correspondence

| Paper result | Closest Lean declaration(s) | Correspondence status |
|---|---|---|
| Theorem 1.1, memoryless set generation under finitely repeating presentations | `theorem_1_1`, `theorem_1_1_enumerated`, `finitelyRepeatingGenerator_succeeds` | **Weaker**: exact success quantifiers, but fixed to `ℕ`; the base set-output type is not globally infinite |
| Theorem 3.1, arbitrary-repetition characterization | `singletonCore`, `InfiniteSingletonCores`, `arbitrary_memoryless_necessity`, `arbitrary_memoryless_sufficiency`, `theorem_3_1` | **Faithful**: exact intersection equivalence and pointwise amplification; the full-memory one-example formulation is not separately defined |
| Theorem 3.2, element output | `ElementCorrectAt`, `theorem_3_2_element` | **Faithful / stronger genericity**: exact freshness through the current round over any countable ambient type |
| Theorem 3.2, index output | modular hard languages, `theorem_3_2_index`, `theorem_3_2` | **Faithful**: literal two-language witness, finitely repeating presentations, and containment output |
| Lemma 4.3 | `lemma_4_3_lower_density_bound_from_partition` | **Stronger**: success is needed only on the partition pieces |
| Lemma 4.4 | `lemma_4_4_zero_lower_density_partition` | **Faithful**: exact infinite, disjoint, covering zero-lower-density partition |
| Fact 4.5, full Sperner theorem | specialized middle-layer declarations | **Absent as a full statement**; the exact special antichain consequence needed by the hard instance is present |
| Fact 4.6, symmetric-chain decomposition | `symmetric_chain_decomposition_range`, `symmetric_chain_decomposition_fintype` | **Faithful / stronger structure**: saturated decomposition and exact chain count |
| Lemma 4.7 | Sperner hard-family declarations, `lemma_4_7_sperner_hard_instance` | **Faithful for the chosen order; conditionally related globally** because the order is selected rather than inherited from one ambient order |
| Lemma 4.8 | canonical generator, `lemma_4_8_sperner_achievability` | **Stronger**: the same value is guaranteed for every target ordering |
| Theorem 4.1 | `theorem_4_1_memoryless_minimax_upper_density` | **Only conditionally related**: the same exact value is proved for an adversarial/order-robust game rather than the paper's fixed-global-order game |
| Theorem 4.2 | `theorem_4_2_no_uniform_positive_lower_density` | **Faithful for the chosen order; conditionally related globally** because the hard instance chooses its order |
| Lemma 4.11 | `lemma_4_11_finite_exception` | **Faithful**: one finite exceptional set is uniform over all distinct windows |
| Lemma 4.12 | window hard-family declarations, `lemma_4_12_single_hard_instance` | **Stronger quantifier order; conditionally related on order**: one hard instance precedes every `W` and generator, but uses a custom order |
| Theorem 4.10 | `theorem_4_10_window_minimax_upper_density` | **Only conditionally related**: exact value and window model, with the same order-game mismatch as Theorem 4.1 |
| Theorem 4.15 | adaptive-buffer declarations, `theorem_4_15_adaptive_buffer_lower_bound` | **Substantively faithful / stronger on order**, but fixed to `ℕ`; it is a lower bound, not an overclaimed equality |
| Proposition 5.1 | obstruction family, `proposition_5_1` | **Faithful / stronger presentation restriction**: failure already on finitely repeating presentations with exactly three states |
| Theorem 5.2 | topological relabeling, `theorem_5_2_ordered`, `theorem_5_2` | **Faithful extensionally; weaker on raw indexing**: the output family has equal range, but no learner is conjugated back to the input indexing |
| Theorem A.1 | `theorem_A_1_triangle`, `theorem_A_1` | **Faithful / stronger presentation restriction**: explicit three-language obstruction under finitely repeating presentations |
| Proposition A.2 | `appendixTriangleLanguages`, `proposition_A_2` | **Faithful**: exact triangle, antichain promise, and three-state failure |
| Lemma A.3 | baseline `elementCodingCell_infinite`, `_subset`, `_pairwiseDisjoint`, `_cofinal`; current `lemma_A_3` | **Faithful jointly; unbundled at the checked baseline**: the separately tracked public repair now packages the same concrete cells as one existential wrapper |
| Theorem A.4 | `EventuallyAlmostContainedHypotheses`, `incremental_coding_compilation` | **Faithful on `ℕ`; weaker universe**: exact conditional compiler with explicit history encoding in the previous output |
| Theorem A.5 | `incremental_element_generation_of_approximate_identification`, `incremental_element_generation` | **Faithful on `ℕ`; weaker universe**: the conditional premise is closed end to end using approximate identification |

## Principal qualifications and omissions

This map does not claim a complete formalization of:

- transport of Theorem 1.1, the density/window/buffer results, or Appendix
  element coding from `ℕ` to an arbitrary countable universe;
- one fixed ambient canonical order inherited by every target in Theorems
  4.1, 4.2, 4.10, and 4.15;
- an intrinsically infinite codomain for every memoryless set-generator
  output, although the explicit positive witnesses return infinite sets and
  successful runs impose eventual infinitude;
- a direct Theorem 5.2 learner on the original indexing rather than an
  equal-range relabeling;
- full-history set- and index-output interfaces and the one-example
  full-memory formulation of Theorem 3.1;
- Remark 4.9's countable-family zero uniform upper-density guarantee;
- the other three temporal density aggregates and their collapse results;
- the countable finite-predecessor extension of Theorem 5.2 or the weak
  Angluin obstruction;
- a full named Sperner theorem or a named strict buffer-versus-memoryless
  comparison corollary; or
- computability, oracle-free execution, runtime, bit complexity, query
  complexity, convergence rates, randomness, or probability guarantees.

The source indexes a width-`W` window by its final position, whereas Lean's
shared window API indexes by its first position. The resulting sequences
differ by the fixed shift `W - 1`, which preserves eventual statements and the
outer `limsup`; the source comparison treats this as harmless indexing rather than a
theorem-level mismatch.

## Link code, vacuity, and assumption boundary

The conditional helpers used by the main results are assembled rather than
silently substituted for their conclusions. In particular, the finite
intersection and exceptional-set lemmas close Theorem 1.1; the hard-instance
and achievability components close the density equalities; the greedy-buffer
stabilization lemmas close Theorem 4.15; and Theorem A.5 supplies Theorem
A.4's approximate-identification premise through Theorem 5.2.

Headline statements require infinite languages, so the relevant exact
finitely repeating or injective presentations exist and the results are
nonvacuous. Some generalized helpers omit infinitude; their obligations can be
vacuous for finite targets that admit no such presentation, but this does not
infect the headline theorems. No primary axiom, circular headline premise, or
hidden target-dependent runtime advice was identified. Generators and learners
are chosen for the family before the adversary chooses a target; family-wide
codebooks and orders are static semantic data, not target advice.

No statement-faithfulness conclusion certifies the Lean proof bodies or the
paper's proofs. Repository kernel checks establish only that the published
Lean declarations elaborate with the permitted foundations.

The ChatGPT Pro record and pending human-review status live in the
[#31 audit record](../AuditRecords/Paper31_BoundedMemory/) and the
[authoritative human-audit ledger](../AuditRecords/Human/README.md).
