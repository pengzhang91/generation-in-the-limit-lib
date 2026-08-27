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
- `GenLimit.KleinbergWei.PartialEnumeration.lemma_2_3_generation_equivalence`;
- `GenLimit.KleinbergWei.PartialEnumeration.lemma_2_5_concrete_algorithmOne`,
  `theorem_2_2_accurate_conjunction`, `theorem_2_4_semiIndex`, and
  `theorem_1_8`;
- `GenLimit.KleinbergWei.PartialEnumeration.theorem_2_2_freshOutput`;
- `GenLimit.KleinbergWei.PartialEnumeration.WarmupChargeCertificate.theorem_3_1_alpha_third`
  and the conditional
  `PodCapacityOneCertificate.pod_capacity_one_alpha_half`;
- `GenLimit.KleinbergWei.PartialEnumeration.selectedIntersection_eventually_subset_target`;
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.specializes_iff_subset`;
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.tellTale_iff_tdPoint`
  and `theorem_4_9_topological_core`;
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.separation_hierarchy`; and
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
| Concrete Algorithm 1 | An explicit uncompressed raw-index stuttering run with eventual validity, comparability, and infinitely many full resets |
| Density accounting | Ordered input/output prefixes plus finite-exception charging certificates; capacity two gives `α / 3`, capacity one gives `α / 2` |
| Full-enumeration topology | Basic opens `U_F = {L ∈ X | F ⊆ L}` in the paper-local `FullTopology` namespace |
| Tell-tale | A finite subset of `K` excluding every proper class member between it and `K` |

## Statement correspondence

| Paper result | Closest Lean declaration(s) | Correspondence status |
|---|---|---|
| Theorem 2.1 / Overview Theorem 1.5 | `theorem_2_1` | **Faithful existential conclusion**: a semantic finite-scope witness eventually emits fresh elements of `C z`; no roundwise identity with the displayed three-case algorithm is claimed |
| Overview Theorem 1.7 | `theorem_1_7` | **Faithful conjunction core**: every selected finite intersection is infinite and is eventually contained in `C z` |
| Lemma 2.3 | `lemma_2_3_element_to_semiIndex`, `lemma_2_3_semiIndex_to_element`, `lemma_2_3_generation_equivalence` | **Pathwise generation equivalence** between element and semi-index traces; equality of optimal densities remains separate |
| Lemma 2.5, Theorems 2.2/2.4, Overview 1.8 | `lemma_2_5_concrete_algorithmOne`, `theorem_2_2_accurate_conjunction`, `theorem_2_4_semiIndex`, `theorem_1_8` | **Complete theorem-level semantic path** via an explicit raw-index stuttering realization of Algorithm 1 |
| Theorem 3.1 warm-up | `theorem_3_1_warmup_finite_accounting`, `theorem_3_1_alpha_third` | **Corrected complete charging endgame**: capacity-two bad-position charging gives output lower density at least `α / 3` |
| Theorem 3.5 endpoint | `PodCapacityOneCertificate.pod_capacity_one_alpha_half` | **Conditional endpoint**: a capacity-one pod certificate yields `α / 2`; the dynamic pod construction is not claimed |
| Section 4.1 topology | `FullTopology.topology`, `specializes_iff_subset` | **Faithful**: the source-oriented specialization order is language inclusion |
| Section 4.1 separation hierarchy | `FullTopology.separation_hierarchy` | **Complete abstract implication chain**: `T₁ → T_D → T₀` for the full-enumeration topology |
| Theorem 4.8 tell-tale core | `IsTellTale`, `tellTale_iff_tdPoint` | **Repaired reading**: Lean uses the intended proper-sublanguage/between-language condition instead of the malformed self-referential display in arXiv v1 |
| Theorem 4.9 | `theorem_4_9_topological_core` | **Topological core only**: pointwise finite tell-tales are equivalent to the paper-local `T_D` condition |
| Corollary 4.11 | `tOneSpace_iff_inclusionAntichain`, `corollary_4_11_topological_core` | **Order/topology core only**: `T₁` is equivalent to the class being an inclusion antichain |

## Principal qualifications and omissions

The Theorem 2.1 witness is noncomputable and proves the semantic existential
conclusion. It deliberately does not claim round-for-round agreement with
the source's displayed three-case algorithm. The family-wide infinitude
assumption is retained in the source-facing theorem signature, while the
proof needs only the presented set `E` to be infinite.

Lemma 2.3's two pathwise reductions and the complete theorem-level Algorithm
1 package are included. The realization is intentionally uncompressed:
eliminated raw indices may add stuttering rounds, and the early fallback is
totalized, so no false round-for-round equality with the displayed compressed
trace is asserted.

The warm-up `α / 3` density accounting is complete from its explicit
certificate. The optimal `α / 2` endpoint is checked from a capacity-one pod
certificate; constructing that certificate from the paper's full dynamic
priority-list/pod algorithm remains open.

The partial-enumeration intersection topology and its Theorems 4.12--4.13
are omitted. The pinned source describes its opens incompatibly as holding
for “some” `τ_C` and for “every” `τ_C`, while also calling the result the
coarsest topology; this development does not choose one interpretation
silently. Corollary 4.10's learner/separation-in-the-limit equivalence is also
not claimed; `separation_hierarchy` proves only the standard topological
`T₁ → T_D → T₀` implications.

## Reuse and provenance

`GeneratesFromPartialEnumeration` is an abbreviation for the existing
`GenLimit.FreshGeneratesInLimit` predicate in `Core.OnlineGeneration`.
Element and semi-index results share
`selectedIntersection_eventually_subset_target`, so the stabilization proof
is not duplicated. The paper-local full-enumeration topology remains
separate from the containment topology shared by #07 and #23 because their
basic neighborhoods are different.

`FullTopology.IsTellTale` and `GenLimit.Gold.Text.IsTellTale` are both
abbreviations of `GenLimit.Generic.IsFiniteTellTale` in
`Core.FiniteTellTale`. Thus #15 reuses the #0 set-class notion definitionally
without importing the #0 paper path.

The public-repository adaptation now combines the existing refactored modules
with the full #15 module set from `fifalsp/generation-in-the-limit-lib` at
commit `722cad8bd935292a66b731c7aae8b8337697e864`. Density accounting imports
the same canonical `Core.OrderedDensity` interface used by #07 and #31; no
paper-local ordered-density copy is retained.
