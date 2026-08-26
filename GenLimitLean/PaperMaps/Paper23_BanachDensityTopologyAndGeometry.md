# #23 Banach Density, Topology, and Geometry map

Native Lean module: `GenLimit.Paper23_BanachDensityTopologyAndGeometry`.
Declaration namespace retained for API compatibility:
`GenLimit.KleinbergWei.Banach`.

Source: Jon Kleinberg and Fan Wei,
*Validity, Sparse Holes, and Breadth in Language Generation: Banach Density,
Topology, and Geometry*.

- pinned source: [arXiv:2604.02385v2](https://arxiv.org/abs/2604.02385v2),
  revised 2026-07-17.

## Main entry points

- `GenLimit.KleinbergWei.Banach.lowerBanachDensity` and
  `lowerWindowDensity`;
- `GenLimit.KleinbergWei.Banach.claim_3_3` and `claim_3_5`;
- `GenLimit.KleinbergWei.Banach.claim_3_6`;
- `GenLimit.KleinbergWei.Banach.cbDerivative`, `FiniteRankAtMost`, and
  `derivative_monotone_decreasing`; and
- `GenLimit.KleinbergWei.Banach.claim_4_4` and `claim_7_1`.

## Representation and density interfaces

| Paper object | Lean representation |
|---|---|
| One-dimensional language | A set of natural-number positions |
| Finite interval density | `windowCount` and `windowRatio` on `[m, m + k)`; length zero has ratio zero |
| Window bound | A positive nondecreasing `ℕ → WithTop ℕ`; `⊤` represents an unrestricted start position |
| Lower window and Banach densities | Nested infima and an outer `liminf`, valued in `ℝ≥0∞` so all infima are total |
| Perfect tower and topology | The neutral finite-containment topology in `GenLimit.Support.KleinbergWei.TowerTopology` |
| Cantor--Bendixson data | Only finite natural-number derivatives and the empty-kernel predicate `FiniteRankAtMost` |
| Nice schedule | A zero-based finite schedule satisfying monotonicity, separation, lateness, and window-bound clauses |

## Statement correspondence

| Paper result | Closest Lean declaration(s) | Correspondence status |
|---|---|---|
| Definition 3.1, one-dimensional lower Banach density | `lowerBanachDensity` | **Faithful order-theoretic representation** in extended nonnegative reals |
| Definition 3.2 | `AdmissibleWindowBound`, `windowMinimum`, `lowerWindowDensity` | **Faithful one-dimensional absolute-density form** with positive start positions |
| Claim 3.3 | `claim_3_3` | **Faithful**: enlarging the allowed search windows can only decrease lower window density |
| Claim 3.5 | `claim_3_5` | **Faithful**: lower Banach density is the infimum over admissible window bounds and is attained by the constant-`⊤` bound |
| Perfect-tower definition and Claim 3.6 | `PerfectTower`, `claim_3_6` | **Faithful under a supplied exact presentation**: limit points are equivalent to literal nonredundant perfect towers |
| Definition 3.7 | `cbDerivative`, `FiniteRankAtMost` | **Finite fragment only**: natural-number derivatives and empty finite kernel, not transfinite ranks |
| Claim 4.4 / Appendix Claim 7.1 | `claim_4_4`, `claim_7_1` | **Faithful zero-based form for monotone functions**: niceness is equivalent to universal unboundedness |

## Principal qualifications and omissions

The paper writes real-valued ratios; Lean uses `ℝ≥0∞` so the nested infima
are total. Actual nonzero finite-window ratios are finite and lie in
`[0,1]`, and assigning zero to the unused length-zero case does not affect
the outer asymptotic statements.

The source labels both the lower Banach density in Section 3.1 and the
perfect-tower notion in Section 3.3 as “Definition 3.1.” Lean disambiguates
them by declaration name and section-qualified documentation.

This slice formalizes absolute one-dimensional densities. It does not
formalize relative densities, online generators, validity or breadth
theorems, sparse-hole algorithms, the later finite-rank structural-tree
claims, transfinite Cantor--Bendixson ranks, or higher-dimensional geometry.
In particular, the presence of the density definitions and Claim 3.6 is not
a claim that a headline Banach-density generation theorem has been proved.

## Reuse and provenance

The containment topology, exact perfect-tower converse, Hausdorff proof,
presentation local basis, and finite derivative hierarchy live in neutral
`GenLimit.Support.KleinbergWei` modules shared with #07. The paper module
contains only its specializations and paper-facing theorem names.

This compact public-repository adaptation was selected from the preliminary
Kleinberg--Wei development in `fifalsp/generation-in-the-limit-lib` at commit
`722cad8bd935292a66b731c7aae8b8337697e864`; its dependency boundary follows
the compact checkpoint at `95f7359a352a126142c92bb5cb76a3e216d9ff7e`.
It is not a wholesale import of the experimental branch.
