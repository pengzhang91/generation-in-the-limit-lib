# #07 Density Measures for Language Generation map

Native Lean module: `GenLimit.Paper07_DensityMeasuresForLanguageGeneration`.
Declaration namespace retained for API compatibility:
`GenLimit.KleinbergWei.DensityMeasures`.

[Results/Overview.lean](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean) states all six results in Section 2, the detailed Theorems 3.1, 4.1, 4.9, 5.1, 6.2 and 6.12, and the outcomes for Claims 6.1 and 6.11. The numbered index-breadth results 2.3, 2.4 / 4.1 and 4.9 use the unordered sample of Section 2.1. Their docstrings identify the chronological versions in `VanishingBreadth.lean`. The counterexamples to the unordered-sample readings of accuracy and element density follow the numbered results. [Results/Supporting.lean](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Supporting.lean) preserves the source-specific proof lemmas.

Source: Jon Kleinberg and Fan Wei,
*Density Measures for Language Generation*.

- pinned source: [arXiv:2504.14370v1](https://arxiv.org/abs/2504.14370v1),
  submitted 2025-04-19.
- earlier AI source-comparison PDF SHA-256:
  `3a1f56b09c05e7ed84a37544f53d84393f0bb968ad013e5bbd110ff14c0a5038`.

## Human audit

Peng Zhang reported a **Level 1** human audit of `theorem_2_1` and its
statement-relevant definitions on 12 November 2026, against the non-P38
working tree at that date. The public
`GenLimit.KleinbergWei.DensityMeasures.Results.theorem_2_1` and canonical
`GenLimit.KleinbergWei.DensityMeasures.theorem_2_1` had identical normalized
statement types at the reviewed checkpoint. The current public theorem quantifies
over one rule on finite ordered histories and needs a separate Level 1 review. The review covers eventual index validity and arbitrarily
late target-language equality, with the exact-presentation and first-family-
occurrence conventions at the fixed semantic-selector interface.

The [human-audit ledger](../AuditRecords/Human/README.md#07-density-measures-theorem-21-level-1)
and [fingerprint manifest](../AuditRecords/Human/Fingerprints/P07_Theorem2_1Level1.json)
pin the reviewed Lean snapshot and supplied local PDF, whose SHA-256 is
`c17f179bf152196adb8dac7ed88d5001aa0a34554eb37af95578c03bee8afe69`.
That source snapshot is recorded separately from the earlier AI-comparison
PDF above. The Lean index statement does not need the paper's standing
infinitude assumption, so it also covers more general presented targets.

This is a statement/definition review, not construction or proof
correspondence. Other P07 statements, density guarantees, source-proof
repair certification, and P39's distinct patient-scope algorithm remain
outside this human audit. The newer set-only reading and its counterexamples are outside the reviewed scope.

The index minimax and obstruction proofs are in [VanishingBreadth.lean](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/VanishingBreadth.lean).
The chronological element bounds use the [P39-to-P07 bridge](../GenLimit/Bridges/Paper39ToPaper07.lean). Importing the P07 overview brings in both that proof and the unordered-sample results.

## Which observations does the algorithm receive?

Section 2.1 describes a function of the set of observed words. Sections 3–6 use information such as the newest word and the queue from the preceding round. A chronological rule can receive that information from its finite input history. Every permutation of a given history produces the same input to a rule of type `Finset ℕ → ℕ`. This distinction changes the answers. [Paper, Sections 2.1–2.3](https://arxiv.org/html/2504.14370v1#S2.SS1)

| Source result | Finite chronological history | Unordered set of observations |
|---|---|---|
| 2.1 / 3.1 and Corollary 2.2 | One rule is eventually valid and names the true language arbitrarily late, yielding density limsup one. | For each valid rule, `Results.index_set_counterexample` gives an injective text on which every sufficiently late guess differs from the target and the density limsup is zero. |
| 2.3, 2.4 / 4.1 and 4.9 | The square-family obstruction, tower equivalence and optimal truth index hold. | All three hold. The optimal rule uses the number of distinct observations as its search bound. |
| 2.5 / 5.1, 2.6 / 6.12 and finite-rank 6.2 | One finite-history element rule achieves lower density at least one half, implying all three printed bounds. | For each valid set-only generator, `Results.element_set_counterexample` gives an injective text with upper and lower output density zero. The fixed family has rank at most two and compatible natural orders. |

**The set-only counterexample.** Take the full universe as the target. Add one language for each finite initial segment, consisting of that segment together with all squares. Validity on a smaller language forces a finite sample after which the required property holds on every larger observed set inside that language. Before revealing the next integer, the adversary can reveal all other words needed for the next such sample. This keeps every sufficiently late round inside one of these locked intervals. On the full target, index guesses then have density zero, and fresh element outputs eventually lie among the squares. The construction also works when validity is required only on injective texts. [Diagonal](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/SetDrivenDiagonal.lean) · [First-occurrence transfer](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/SetDrivenTexts.lean) · [Counterexamples](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/SetDrivenObstruction.lean) · [Set-driven minimax](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/SetIndex.lean)

The registry groups these results into ten [source claim cards](../../registry/papers/P07.json). Four have full coverage. Five have a proved chronological statement and a refuted unordered-sample statement. The sixth partial card records the separate Claim 6.11 counterexample on texts with repetitions. Its restriction to injective texts remains open here.

## Main entry points

- `GenLimit.KleinbergWei.DensityMeasures.claim_3_2` and `lemma_3_3`;
- `GenLimit.KleinbergWei.DensityMeasures.theorem_3_1` and `theorem_2_1`;
- `GenLimit.KleinbergWei.DensityMeasures.corollary_2_2`;
- `GenLimit.KleinbergWei.DensityMeasures.FeasibleSequence` and
  `claim_4_2` through `claim_4_7`;
- `GenLimit.KleinbergWei.DensityMeasures.IsTruthIndex` and
  `isTruthIndex_unique`;
- `GenLimit.KleinbergWei.DensityMeasures.claim_6_1`, `claim_6_3`,
  `claim_6_4`, and the corrected `claim_6_6`;
- `GenLimit.KleinbergWei.DensityMeasures.property_6_5` and
  `FiniteRankParent.claim_6_7`, `claim_6_8`, and `corollary_6_9`;
- `GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.corollary_6_10`,
  the normalized fallback/output state, and the Claim 6.11 diagnostic;
- `GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.theorem_6_12_finite_accounting`,
  the conditional `1/8` endgame, and the corrected capacity-two `1/10`
  endgame; and
- the shared `GenLimit.KleinbergWei.TowerTopology` definitions and
  perfect-tower converse used by the Section 6 results.

## Representation and selector interfaces

| Paper object | Lean representation |
|---|---|
| Countable indexed language family | `LanguageFamily = ℕ → Language` over strings represented by `ℕ` |
| Exact target presentation | `Presents stream (C z)`; `FirstOccurrence C z` asserts that `z` is the first family index naming the target |
| Section 3 selector | The semantic, noncomputable `guessIndex`; round `t + 1` uses the stage-`t` sample and new value `stream t` |
| Index validity and accuracy | Eventual language containment in the target, plus equality with the target at arbitrarily late rounds; repeated family indices are allowed |
| Ordered density | Shared `GenLimit.Core.OrderedDensity` definitions on a separately supplied `OrderedLanguage` |
| Feasible sequence | Proper sublanguages carrying one exact presentation whose first `n + 1` values occur in stage `n` |
| Containment topology | Shared finite-containment basis in `GenLimit.Support.KleinbergWei.TowerTopology` |
| Cantor--Bendixson data | Finite natural-number derivatives and levels from `GenLimit.Support.KleinbergWei.CantorBendixson` |
| Finite-rank dynamics | A time-indexed remaining-language forest, weak components, frozen-origin pullbacks, and canonical least-common-ancestor fallback |
| Infinite-rank accounting | Rational inclusion levels, run thinning, prefix charges, tagged reservations, append-only history, and an observe--reserve--emit execution |

## Statement correspondence

| Paper result | Closest Lean declaration(s) | Correspondence status |
|---|---|---|
| Definition 3.1 | `StrictCritical` | **Repaired**: comparison is with earlier consistent indices only; including the current index would require a language to be a proper subset of itself |
| Claim 3.2 | `claim_3_2` | **Repaired proof bound**: persistence uses the required bound `i < n`, not the printed `i < r` |
| Lemma 3.3 | `lemma_3_3` | **Faithful semantically** for an exact presentation and the target's first occurrence |
| Theorem 3.1 / Overview Theorem 2.1 | `theorem_3_1`, `theorem_2_1` | The chronological selector is eventually valid and arbitrarily often accurate. The unordered-sample version has a counterexample. |
| Corollary 2.2 | `corollary_2_2` | With chronological observations, the limsup of the guessed languages’ upper densities is one. The unordered-sample counterexample has limsup zero. |
| Overview Theorem 2.3 | `Results.theorem_2_3` | Squares with finite additions give an infinite hard family with zero worst-case index breadth |
| Overview Theorem 2.4 / Theorem 4.1 | `Results.theorem_2_4`, `Results.theorem_4_1` | Vanishing breadth is equivalent to arbitrarily thin perfect towers in both directions |
| Theorem 4.9 | `exists_truthIndex`, `Results.theorem_4_9` | Existence, optimal selector, and matching adversarial presentation |
| Overview Theorem 2.5 / Theorem 5.1 | `OrderedFocus.theorem_5_1` | One prefix-dependent rule attains the upper-density guarantee for every c < 1 |
| Definition 4.4 and Claims 4.2--4.7 | `FeasibleSequence`, `claim_4_2`--`claim_4_7` | **Faithful zero-based forms**; Claim 4.3 is an explicit strictly monotone subsequence construction |
| Definition 4.5 | `IsTruthIndex`, `exists_truthIndex`, `isTruthIndex_unique` | The infimum threshold exists, is unique, and equals one in the absence of a tower |
| Definition 2.3 and Claim 6.1 | `PerfectTower`, `claim_6_1` | **Faithful under a supplied exact presentation**: limit points are equivalent to literal nonredundant perfect towers |
| Claim 6.6 | `no_perfectTower_starting_at_empty`, `claim_6_6` | **Repaired**: the prescribed first strict sublanguage must be nonempty |
| Claims 6.3 and 6.4 | `claim_6_3`, `claim_6_4` | **Finite-level core**: the terminal-level obstruction and convergence from the preceding finite level are proved |
| Property 6.5, Claims 6.7--6.8, Corollaries 6.9--6.10 | `property_6_5`, `FiniteRankParent.claim_6_7`, `claim_6_8`, `corollary_6_9`, `FiniteRankFallback.corollary_6_10` | **Finite-rank dynamic path**: all three parent cases, component structure, eventual purge, target ancestry, and canonical fallback validity are proved |
| Theorem 6.2 | `OrderedFocus.theorem_6_2` | With chronological observations, an independent generator proves the finite-rank bound. The unordered-sample version already fails at rank at most two. |
| Claim 6.11 | `ReplayCounterexample.not_claim_6_11_on_repeated_presentations` | The canonical rank-one run can have arbitrarily late adjacent bad inputs when repetitions are permitted |
| Theorem 6.12 / Overview Theorem 2.6 | `Results.theorem_6_12`, `Results.theorem_2_6` | The adapted P39 generator supplies the $1/8$ lower-density bound. [Lean proof and status of the P07 argument](#theorem-612-and-proposition-615) |

## Theorem 6.12 and Proposition 6.15

**Lean statement.** For every countable family of ordered languages whose orders agree on shared words, `Results.theorem_6_12` gives one rule `A : List ℕ → ℕ` on finite chronological histories. For every target in the family and every exact enumeration of it, the rule eventually emits fresh target words, and the set of target words it emits has lower density at least $1/8$ in the target's order. The statement covers every rank. [Public Lean declaration](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean)

**Proof used in Lean.** The witness is `OrderedFocus.historyRule O`, adapted from P39's patient-scope generator. P39 Theorem 3.15 gives lower density at least $1/2$. The bridge transfers that bound to P07's compatible orders, and `historyRule_density` gives it for the finite-history rule. The final step in `Results.theorem_6_12` is $1/8 \le 1/2$. [P39 generator theorem](../GenLimit/Paper39_DenseGeneration/Patient/Main.lean) · [Order transfer](../GenLimit/Bridges/Paper39ToPaper07.lean) · [Finite-history witness](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/FiniteHistory.lean)

**P07’s original algorithm.** Proposition 6.15 asserts the $1/8$ bound for the output of P07's own fallback algorithm. In the pinned arXiv v1 proof, Claim 6.18 gives an injective map $\Phi$ from retained bad words to unordered pairs of reserved words. Lemma 6.16 needs an injective map $\rho$ from those bad words to earlier, smaller **output words**. The final assignment uses the output at the first round in which either member of a pair is used. Even for disjoint pairs, the first uses could coincide if the adversary consumes a word from one pair in round $r$ while the algorithm emits a word from the other. Both bad words would then be assigned the same output $o_r$. The printed argument leaves the exclusion of this case unjustified. Whether such a collision occurs on an actual P07 run remains unresolved. [P07 v1, proof of Lemma 6.16](https://arxiv.org/html/2504.14370v1#S6.SS4)

Lean proves injectivity within each of the input-first and output-first cases. Given the other counting hypotheses, excluding collisions between the cases yields $1/8$, while allowing one charge of each kind per output yields $1/10$. Both estimates here are conditional on establishing their hypotheses for the original run. Its $1/8$ guarantee remains unverified. [Cross-case collision condition](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/InfiniteRank/ConsumptionBridge.lean) · [Injective counting bound](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/InfiniteRank/LongCharge.lean) · [Capacity-two counting bound](../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/InfiniteRank/CapacityCharge.lean)

## Principal qualifications and omissions

The selector is semantic and uses classical choice; no computability,
runtime, or finite-query guarantee is claimed. `corollary_2_2` concerns the
upper density of the languages named by the selector, not the density of a
generated element sequence.

Claim 4.7 uses non-strict containment of a finite set `F`. This is equivalent
to the source's strict-containment phrasing in the feasible-sequence setting:
the exact presentation together with proper approximants forces the terminal
language to be infinite.

The finite-rank forest path is checked through Corollary 6.10, including the
fallback/output invariants and a counterexample to the printed cross-round
ancestry argument. The infinite-rank development checks rational levels,
arbitrary-run thinning, prefix and token charging interfaces, collision-free
reservation histories, a recursive observe--reserve--emit execution, and the
conditional `1/8`/corrected `1/10` density endgames.

The adapted P39 generator selects the least unused word in its current focus language's order. The coding used to compare runs can depend on the target in the proof. The generator itself is uniform across targets.

On the literal bad set with repeated observations, the rank-one replay counterexample rules out the published dynamic implication. The argument leaves the injective-presentation version undecided. The original infinite-rank charging bridge and transfinite derivatives lie beyond these endpoint proofs.

## Reuse and provenance

The implementation reuses the repository's `Core.Basic`,
`Core.PartialPresentation`, and `Core.OrderedDensity` APIs. Eventual finite
sample coverage delegates to `Support.Presentations`, and the paper's
level-approximant construction delegates to the relative `ApproachedFrom`
machinery in `Support.KleinbergWei.TowerTopology`. The perfect-tower topology
and finite Cantor--Bendixson hierarchy are neutral Support modules shared with
#23 rather than duplicated under either paper.

The public-repository adaptation now combines the existing refactored modules
with the full #07 module set from `fifalsp/generation-in-the-limit-lib` at
commit `722cad8bd935292a66b731c7aae8b8337697e864`. Personal
`Shared.KleinbergWei` copies were deliberately not imported: ordered density
uses `Core.OrderedDensity`, and the #07/#23 topology lives once under
`Support.KleinbergWei`.
