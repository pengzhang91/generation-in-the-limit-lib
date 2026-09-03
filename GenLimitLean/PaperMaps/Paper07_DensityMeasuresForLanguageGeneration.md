# #07 Density Measures for Language Generation map

Native Lean module: `GenLimit.Paper07_DensityMeasuresForLanguageGeneration`.
Declaration namespace retained for API compatibility:
`GenLimit.KleinbergWei.DensityMeasures`.

Source: Jon Kleinberg and Fan Wei,
*Density Measures for Language Generation*.

- pinned source: [arXiv:2504.14370v1](https://arxiv.org/abs/2504.14370v1),
  submitted 2025-04-19.
- audited PDF SHA-256:
  `3a1f56b09c05e7ed84a37544f53d84393f0bb968ad013e5bbd110ff14c0a5038`.

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
| Theorem 3.1 / Overview Theorem 2.1 | `theorem_3_1`, `theorem_2_1` | **Faithful semantic selector**: eventual index validity and arbitrarily late equality with the target |
| Corollary 2.2 | `corollary_2_2` | **Faithful for index-density**: with an ordered realization whose carrier is the target, the limsup of the guessed languages' upper densities is one |
| Overview Theorem 2.3 | No declaration | **Open**: the hard instance and adversarial presentation forcing vanishing index breadth are not formalized |
| Overview Theorem 2.4 / Theorem 4.1 | `claim_4_2`--`claim_4_7` provide the feasible-sequence core | **Partial / infrastructure only**: the tower lemmas are checked, but neither direction of the index-breadth characterization is assembled |
| Theorem 4.9 | `IsTruthIndex`, `isTruthIndex_unique` | **Partial**: the threshold interface and conditional uniqueness are checked; existence and both minimax directions remain open |
| Overview Theorem 2.5 / Theorem 5.1 | No declaration | **Open**: the lazy accurate-selector element algorithm and its upper-density guarantee are not formalized; the source's `c/2` detailed form is equivalent to the overview's arbitrary bound below `1/2` |
| Definition 4.4 and Claims 4.2--4.7 | `FeasibleSequence`, `claim_4_2`--`claim_4_7` | **Faithful zero-based forms**; Claim 4.3 is an explicit strictly monotone subsequence construction |
| Definition 4.5 | `IsTruthIndex` | **Definition and conditional uniqueness only**: the epsilon/least-bound formulation and no-tower value are represented, but existence is not proved |
| Definition 2.3 and Claim 6.1 | `PerfectTower`, `claim_6_1` | **Faithful under a supplied exact presentation**: limit points are equivalent to literal nonredundant perfect towers |
| Claim 6.6 | `no_perfectTower_starting_at_empty`, `claim_6_6` | **Repaired**: the prescribed first strict sublanguage must be nonempty |
| Claims 6.3 and 6.4 | `claim_6_3`, `claim_6_4` | **Finite-level core**: the terminal-level obstruction and convergence from the preceding finite level are proved |
| Property 6.5, Claims 6.7--6.8, Corollaries 6.9--6.10 | `property_6_5`, `FiniteRankParent.claim_6_7`, `claim_6_8`, `corollary_6_9`, `FiniteRankFallback.corollary_6_10` | **Finite-rank dynamic path**: all three parent cases, component structure, eventual purge, target ancestry, and canonical fallback validity are proved |
| Theorem 6.2 | `FiniteRankFallback.corollary_6_10`, `FiniteRankFallback.no_rankClimbWitness` | **Partial / source-disputed**: fallback validity and rank arithmetic are checked, but Claim 6.11's false persistence step blocks the dynamic no-long-bad-run bridge and the `1/(3(r+1))` density theorem |
| Claim 6.11 | `FiniteRankFallback.no_rankClimbWitness`, `PersistenceCounterexample.infinite_languages_still_consistent_ancestor_not_persistent`, and frozen-frame results | **Boundary and repair**: the printed cross-round ancestry premise is refuted; a same-frozen-forest target-valid advancement invariant is proved, but the full density conclusion is not claimed |
| Theorem 6.12 / Overview Theorem 2.6 | `InfiniteRank.theorem_6_12_finite_accounting`, `orderedLowerDensity_one_eighth_of_longBadCharge`, and `orderedLowerDensity_one_tenth_of_longBadCapacityTwoCharge` | **Conditional endgames for the general theorem**: exact finite accounting and liminf transfer are proved; an injective charge yields `1/8`, while the charge justified by the source construction has capacity two and yields `1/10` |

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

Although Theorem 6.12 appears under the heading “Infinite rank case,” its
statement is the general all-instances result and is identified by the source
as equivalent to Overview Theorem 2.6; infinite rank is not a theorem
assumption. The source proves injectivity of a map into unordered pairs and
then asserts injectivity after choosing one output from each pair. Distinct
pairs can overlap, so that inference supplies only a capacity-two charge, not
the injective charge needed for `1/8`.

The missing headline results now have explicit zero- or partial-coverage
theorem cards instead of being absent from the inventory. The remaining
boundary is the dynamic bridge: seed/reset frames must be tied
to bad runs, dynamic partitions and fallback events must instantiate the
reservation schedule, ambient priority must be transported to target-order
positions, and consumption deadlines plus the stronger cross-class invariant
must be proved. The two directions of Theorem 4.1, Theorem 4.9's minimax
argument, element-based Section 5, transfinite derivatives, and truth-index
existence also remain out of scope.

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
