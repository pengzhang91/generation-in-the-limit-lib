# #07 Density Measures for Language Generation map

Native Lean module: `GenLimit.Paper07_DensityMeasuresForLanguageGeneration`.
Declaration namespace retained for API compatibility:
`GenLimit.KleinbergWei.DensityMeasures`.

Source: Jon Kleinberg and Fan Wei,
*Density Measures for Language Generation*.

- pinned source: [arXiv:2504.14370v1](https://arxiv.org/abs/2504.14370v1),
  submitted 2025-04-19.

## Main entry points

- `GenLimit.KleinbergWei.DensityMeasures.claim_3_2` and `lemma_3_3`;
- `GenLimit.KleinbergWei.DensityMeasures.theorem_3_1` and `theorem_2_1`;
- `GenLimit.KleinbergWei.DensityMeasures.corollary_2_2`;
- `GenLimit.KleinbergWei.DensityMeasures.FeasibleSequence` and
  `claim_4_2` through `claim_4_7`;
- `GenLimit.KleinbergWei.DensityMeasures.IsTruthIndex` and
  `isTruthIndex_unique`;
- `GenLimit.KleinbergWei.DensityMeasures.claim_6_1`, `claim_6_3`,
  `claim_6_4`, and the corrected `claim_6_6`; and
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

## Statement correspondence

| Paper result | Closest Lean declaration(s) | Correspondence status |
|---|---|---|
| Definition 3.1 | `StrictCritical` | **Repaired**: comparison is with earlier consistent indices only; including the current index would require a language to be a proper subset of itself |
| Claim 3.2 | `claim_3_2` | **Repaired proof bound**: persistence uses the required bound `i < n`, not the printed `i < r` |
| Lemma 3.3 | `lemma_3_3` | **Faithful semantically** for an exact presentation and the target's first occurrence |
| Theorem 3.1 / Overview Theorem 2.1 | `theorem_3_1`, `theorem_2_1` | **Faithful semantic selector**: eventual index validity and arbitrarily late equality with the target |
| Corollary 2.2 | `corollary_2_2` | **Faithful for index-density**: with an ordered realization whose carrier is the target, the limsup of the guessed languages' upper densities is one |
| Definition 4.4 and Claims 4.2--4.7 | `FeasibleSequence`, `claim_4_2`--`claim_4_7` | **Faithful zero-based forms**; Claim 4.3 is an explicit strictly monotone subsequence construction |
| Definition 4.5 | `IsTruthIndex` | **Definition and conditional uniqueness only**: the epsilon/least-bound formulation and no-tower value are represented, but existence is not proved |
| Definition 2.3 and Claim 6.1 | `PerfectTower`, `claim_6_1` | **Faithful under a supplied exact presentation**: limit points are equivalent to literal nonredundant perfect towers |
| Claim 6.6 | `no_perfectTower_starting_at_empty`, `claim_6_6` | **Repaired**: the prescribed first strict sublanguage must be nonempty |
| Claims 6.3 and 6.4 | `claim_6_3`, `claim_6_4` | **Finite-level core**: the terminal-level obstruction and convergence from the preceding finite level are proved |

## Principal qualifications and omissions

The selector is semantic and uses classical choice; no computability,
runtime, or finite-query guarantee is claimed. `corollary_2_2` concerns the
upper density of the languages named by the selector, not the density of a
generated element sequence.

Claim 4.7 uses non-strict containment of a finite set `F`. This is equivalent
to the source's strict-containment phrasing in the feasible-sequence setting:
the exact presentation together with proper approximants forces the terminal
language to be infinite.

The compact development does not formalize the headline positive-density
generation theorems, the finite- or infinite-rank generation algorithms,
Claim 6.11, Theorem 6.12, transfinite derivatives, or existence and minimax
properties of truth indices. The Section 6 topology covers precisely Claim
6.1, the corrected Claim 6.6, and the finite-level Claims 6.3--6.4.

## Reuse and provenance

The implementation reuses the repository's `Core.Basic`,
`Core.PartialPresentation`, and `Core.OrderedDensity` APIs. The perfect-tower
topology and finite Cantor--Bendixson hierarchy are neutral Support modules
shared with #23 rather than duplicated under either paper.

This compact public-repository adaptation was selected from the preliminary
Kleinberg--Wei development in `fifalsp/generation-in-the-limit-lib` at commit
`722cad8bd935292a66b731c7aae8b8337697e864`; its dependency boundary follows
the compact checkpoint at `95f7359a352a126142c92bb5cb76a3e216d9ff7e`,
extended by the Corollary 2.2 index-limsup module from `722cad8`. It is not a
claim that the larger experimental branch was imported wholesale.
