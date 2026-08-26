# #15 Partial Enumeration map

Native Lean module: `GenLimit.Paper15_PartialEnumeration`.
Declaration namespace retained for API compatibility:
`GenLimit.KleinbergWei.PartialEnumeration`.

Source: Jon Kleinberg and Fan Wei,
*Language Generation and Identification From Partial Enumeration: Tight
Density Bounds and Topological Characterizations*.

- pinned source: [arXiv:2511.05295v1](https://arxiv.org/abs/2511.05295v1),
  submitted 2025-11-07.

## Main entry points

- `GenLimit.KleinbergWei.PartialEnumeration.theorem_2_1`;
- `GenLimit.KleinbergWei.PartialEnumeration.theorem_1_7`;
- `GenLimit.KleinbergWei.PartialEnumeration.selectedIntersection_eventually_subset_target`;
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.specializes_iff_subset`;
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.tellTale_iff_tdPoint`
  and `theorem_4_9_topological_core`; and
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.corollary_4_11_topological_core`.

## Representation and generation interfaces

| Paper object | Lean representation |
|---|---|
| Indexed language family | `LanguageFamily = ℕ → Language` over strings represented by `ℕ` |
| Infinite partial enumeration | An exact presentation `Presents stream E` of an infinite set `E`, together with `E ⊆ C z` |
| Finite-scope witness | The largest visible prefix whose consistent-candidate intersection is infinite |
| Element output | A semantic fresh choice from that selected intersection |
| Generation conclusion | The shared `FreshGeneratesInLimit` predicate, exposed under the paper-local abbreviation `GeneratesFromPartialEnumeration` |
| Semi-index output | A finite set of consistent indices; its denotation is their language intersection |
| Full-enumeration topology | Basic opens `U_F = {L ∈ X | F ⊆ L}` in the paper-local `FullTopology` namespace |
| Tell-tale | A finite subset of `K` excluding every proper class member between it and `K` |

## Statement correspondence

| Paper result | Closest Lean declaration(s) | Correspondence status |
|---|---|---|
| Theorem 2.1 / Overview Theorem 1.5 | `theorem_2_1` | **Faithful existential conclusion**: a semantic finite-scope witness eventually emits fresh elements of `C z`; no roundwise identity with the displayed three-case algorithm is claimed |
| Overview Theorem 1.7 | `theorem_1_7` | **Faithful conjunction core**: every selected finite intersection is infinite and is eventually contained in `C z` |
| Section 4.1 topology | `FullTopology.topology`, `specializes_iff_subset` | **Faithful**: the source-oriented specialization order is language inclusion |
| Theorem 4.8 tell-tale core | `IsTellTale`, `tellTale_iff_tdPoint` | **Repaired reading**: Lean uses the intended proper-sublanguage/between-language condition instead of the malformed self-referential display in arXiv v1 |
| Theorem 4.9 | `theorem_4_9_topological_core` | **Topological core only**: pointwise finite tell-tales are equivalent to the paper-local `T_D` condition |
| Corollary 4.11 | `tOneSpace_iff_inclusionAntichain`, `corollary_4_11_topological_core` | **Order/topology core only**: `T₁` is equivalent to the class being an inclusion antichain |

## Principal qualifications and omissions

The Theorem 2.1 witness is noncomputable and proves the semantic existential
conclusion. It deliberately does not claim round-for-round agreement with
the source's displayed three-case algorithm. The family-wide infinitude
assumption is retained in the source-facing theorem signature, while the
proof needs only the presented set `E` to be infinite.

The compact development does not include Lemmas 2.3 or 2.5, Theorems 2.2 or
2.4, Overview Theorem 1.8, the Section 3 density bounds, or the learner and
identification components surrounding the Section 4 topology. Theorem 4.9
and Corollary 4.11 are therefore named explicitly as topological cores.

The partial-enumeration intersection topology and its Theorems 4.12--4.13
are omitted. The pinned source describes its opens incompatibly as holding
for “some” `τ_C` and for “every” `τ_C`, while also calling the result the
coarsest topology; this slice does not choose one interpretation silently.

## Reuse and provenance

`GeneratesFromPartialEnumeration` is an abbreviation for the existing
`GenLimit.FreshGeneratesInLimit` predicate in `Core.OnlineGeneration`.
Element and semi-index results share
`selectedIntersection_eventually_subset_target`, so the stabilization proof
is not duplicated. The paper-local full-enumeration topology remains
separate from the containment topology shared by #07 and #23 because their
basic neighborhoods are different.

`FullTopology.IsTellTale` is extensionally the same set-class predicate as
`GenLimit.Gold.Text.IsTellTale`. Its four-line paper-facing definition stays
local because the canonical declaration currently lives inside the heavyweight
#0 paper path; importing that path would break #15's independent-paper
boundary. A future neutral extraction could make this reuse definitional.

This compact public-repository adaptation was selected from the preliminary
Kleinberg--Wei development in `fifalsp/generation-in-the-limit-lib` at commit
`722cad8bd935292a66b731c7aae8b8337697e864`; its dependency boundary follows
the compact checkpoint at `95f7359a352a126142c92bb5cb76a3e216d9ff7e`.
It is not a wholesale import of the experimental branch.
