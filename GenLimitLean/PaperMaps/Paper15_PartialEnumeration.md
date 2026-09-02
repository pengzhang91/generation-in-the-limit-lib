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
- `GenLimit.KleinbergWei.PartialEnumeration.WarmupPriority.lemma_3_2_eventual_validity`,
  with the concrete `algorithmOneWarmupOutput` run and legacy-queue drainage;
- `GenLimit.KleinbergWei.PartialEnumeration.WarmupPriority.sourceLatestReturnCharge_injectiveOn`
  and `sourceLatestReturnChargeRank_lt`, the corrected conditional Lemma 3.4
  value/rank charge, plus `sourceLatestReturnBadChargeFragment` and machine-
  checked diagnostics for the missing revisit premise;
- `GenLimit.KleinbergWei.PartialEnumeration.WarmupChargeCertificate.theorem_3_1_alpha_third`
  and the conditional
  `PodCapacityOneCertificate.pod_capacity_one_alpha_half`;
- `GenLimit.KleinbergWei.PartialEnumeration.fixedPod_finite_counting` and
  `GrowingPodRatioCertificate.alpha_half` for the source-shaped pod endgame;
- `GenLimit.KleinbergWei.PartialEnumeration.selectedIntersection_eventually_subset_target`;
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.specializes_iff_subset`;
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.tellTale_iff_tdPoint`
  and `theorem_4_9_topological_core`;
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.separation_hierarchy`;
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.theorem_4_9_fullText`,
  `corollary_4_10_fullText`, and `corollary_4_11_fullText`; and
- `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.possiblySubset_corollary_4_10_counterexample`.

## Representation and generation interfaces

| Paper object | Lean representation |
|---|---|
| Indexed language family | `LanguageFamily = ℕ → Language` over strings represented by `ℕ` |
| Infinite partial enumeration | Shared Core predicate `InfinitePartialPresentation stream (C z)`; equivalently, an exact presentation `Presents stream E` of an infinite set `E`, together with `E ⊆ C z` |
| Finite-scope witness | The largest visible prefix whose consistent-candidate intersection is infinite |
| Element output | A semantic fresh choice from that selected intersection |
| Generation conclusion | The shared `FreshGeneratesInLimit` predicate, exposed under the paper-local abbreviation `GeneratesFromPartialEnumeration` |
| Semi-index output | A finite set of consistent indices; its denotation is their language intersection |
| Concrete Algorithm 1 | An explicit uncompressed raw-index stuttering run with eventual validity, comparability, and infinitely many full resets |
| Warm-up Section 3 execution | A recursive used-set/priority-queue/token state driven by the concrete Algorithm 1 intersections; the output is the least unused priority/current candidate. The source's missing strict-downward token is explicitly normalized to `2` |
| Density accounting | Ordered input/output prefixes plus finite-exception charging certificates; capacity two gives `α / 3`, capacity one gives `α / 2` |
| Growing-pod endgame | Correct finite four-class arithmetic, fixed-`s` vanishing-error ratio certificates, and a same-run certificate quantified over every fixed `s` |
| Full-enumeration topology | Basic opens `U_F = {L ∈ X | F ⊆ L}` in the paper-local `FullTopology` namespace |
| Tell-tale | A finite subset of `K` excluding every proper class member between it and `K` |
| Full-text learner | A causal language-valued finite-history learner from the earlier extensional Angluin interface; countability is derived from successful identification of nonempty languages rather than built into the definition |

## Statement correspondence

| Paper result | Closest Lean declaration(s) | Correspondence status |
|---|---|---|
| Theorem 2.1 / Overview Theorem 1.5 | `theorem_2_1` | **Faithful existential conclusion**: a semantic finite-scope witness eventually emits fresh elements of `C z`; no roundwise identity with the displayed three-case algorithm is claimed |
| Overview Theorem 1.7 | `theorem_1_7` | **Faithful conjunction core**: every selected finite intersection is infinite and is eventually contained in `C z` |
| Lemma 2.3 | `lemma_2_3_element_to_semiIndex`, `lemma_2_3_semiIndex_to_element`, `lemma_2_3_generation_equivalence` | **Pathwise generation equivalence** between element and semi-index traces; equality of optimal densities remains separate |
| Lemma 2.5, Theorems 2.2/2.4, Overview 1.8 | `lemma_2_5_concrete_algorithmOne`, `theorem_2_2_accurate_conjunction`, `theorem_2_4_semiIndex`, `theorem_1_8` | **Complete theorem-level semantic path** via an explicit raw-index stuttering realization of Algorithm 1 |
| Lemma 3.2 | `WarmupPriority.lemma_3_2_eventual_validity` | **Complete for the concrete Algorithm 1 selector and recursive priority run**: proves freshness/injectivity and drains every invalid legacy queue entry instead of assuming it disappears |
| Lemma 3.4 / Theorem 3.1 warm-up | `sourceLatestReturnCharge_injectiveOn`, `sourceLatestReturnChargeRank_lt`, `sourceLatestReturnBadChargeFragment`, `theorem_3_1_warmup_finite_accounting`, `theorem_3_1_alpha_third` | **Conditional charge and complete endgame**: the actual latest-return output is proved injective and smaller both as a value and, under the universal-order convention, as a target rank. These facts construct every bad-charge certificate field except coverage by `LateReturnEligibleRank`; the capacity-two density endgame is complete. The source does not establish that coverage because resets can skip unvisited levels |
| Theorem 3.5 endpoint | `fixedPod_finite_counting`, `FixedPodRatioCertificate.lowerDensity`, `GrowingPodRatioCertificate.alpha_half`; alternatively `PodCapacityOneCertificate.pod_capacity_one_alpha_half` | **Source-shaped conditional endpoint plus stronger ideal endpoint**: the corrected finite-`s` algebra and same-run `s → ∞` passage are complete; the dynamic pod construction does not yet supply the fixed-`s` certificates |
| Section 4.1 topology | `FullTopology.topology`, `specializes_iff_subset` | **Faithful**: the source-oriented specialization order is language inclusion |
| Section 4.1 separation hierarchy | `FullTopology.separation_hierarchy` | **Complete abstract implication chain**: `T₁ → T_D → T₀` for the full-enumeration topology |
| Theorem 4.8 tell-tale core | `IsTellTale`, `tellTale_iff_tdPoint` | **Repaired reading**: Lean uses the intended proper-sublanguage/between-language condition instead of the malformed self-referential display in arXiv v1 |
| Theorem 4.9 | `theorem_4_9_topological_core`, `indexedClassIdentifiableOnFullTexts_iff_tdSpace_range`, `theorem_4_9_fullText` | **Complete semantic/full-text theorem under the paper's nonempty-language assumption**: language-valued causal identification forces countability and is equivalent to countability plus the paper-local `T_D` condition. The indexed range theorem is retained separately |
| Corollaries 4.10--4.11 | `corollary_4_10_fullText`, `corollary_4_11_fullText` | **Complete repaired exact-full-text variants**: finite-history refutation is equivalent to `T₁` and hence to an inclusion antichain; the printed stronger arbitrary-partial-text wording is formally refuted by `possiblySubset_corollary_4_10_counterexample` |

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

The warm-up priority-list state machine and Lemma 3.2 are concrete. The proof
includes the step omitted by the source: a finite legacy queue cannot retain
an invalid value forever, because least-output priority would inject an
infinite output tail into a finite initial interval. The source does not set a
token in its strict-downward case; the validity run normalizes this to `2`, as
suggested by its adjacent-step prose, without claiming equivalence to a
distance-sensitive charging schedule.

The corrected Lemma 3.4 latest-return charge is now an actual function into
the concrete output run, with proved injectivity, target validity after the
validity cutoff, and strict target-rank order on its exact eligibility domain.
It constructs the full conditional bad-charge fragment expected by the later
density certificate. The missing domain theorem is a mathematical gap in the
printed proof: a changed-chain positive reset can skip several unselected
levels, so two earlier full times do not imply that a later reset target was
ever selected. Moreover, an equal post-observation state can return only at
the observation round, after input-first purging has made the input
unavailable. `latestReturn_succ_eq_of_eq` and
`current_input_mem_does_not_force_output_le` expose these failures in Lean.
A proof of Theorem 3.1 therefore needs a new skipped-level queue/token charge
or a stronger revisit invariant; the capacity-two `α / 3` endgame is complete
once such a certificate is supplied.

For the optimal theorem, Lean now checks both the paper's corrected finite
four-class arithmetic and the quantifier-sensitive passage from every
fixed-`s` bound on one output run to exact density `α / 2`. This is weaker
and more source-faithful than the existing ideal capacity-one certificate.
The remaining dynamic bridge is genuinely substantive: the printed proof of
Lemma 3.6 treats a large element of the cumulative pod union as if it belonged
to the newly created pod, which does not follow without a new historical
capture invariant.

The partial-enumeration intersection topology and its Theorems 4.12--4.13
are omitted. The pinned source describes its opens incompatibly as holding
for “some” `τ_C` and for “every” `τ_C`, while also calling the result the
coarsest topology; this development does not choose one interpretation
silently.

The full-enumeration learner layer reuses the earlier semantic and extensional
Angluin theorems to prove Theorem 4.9 and repaired exact-full-text Corollaries
4.10--4.11. The source
defines separation using an enumeration “possibly a subset of” the target,
but its proof needs an exact text. The two-language counterexample module
shows that the stronger reading is false even when the shared partial
language and both candidates are infinite.

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
`Support.FiniteTellTale`. Thus #15 reuses the #0 set-class notion definitionally
without importing the #0 paper path. The complete full-text learner theorem
then imports the existing Angluin-to-extensional bridge: the indexed result
uses #0A's semantic characterization, while the set-valued result reuses the
language-valued learner and its theorem that identification of nonempty
languages forces countability. Neither convergence proof is reconstructed.

All three Paper 15 density endpoints instantiate
`OrderedLanguage.lowerDensity_div_le_of_eventually_prefixRatio_le` from
`Core.OrderedDensity`, so the delicate `liminf` transfer is proved once.
`OrderedOccurrences` similarly packages the first late occurrence and its
injectivity for use in the warm-up charge construction. The ambient-order
inverse and successor facts formerly local to #07 now live in
`Support.KleinbergWei.OrderedPositions`, retaining legacy theorem names while
avoiding another copy in #15 without enlarging Core.

The public-repository adaptation now combines the existing refactored modules
with the full #15 module set from `fifalsp/generation-in-the-limit-lib` at
commit `722cad8bd935292a66b731c7aae8b8337697e864`. Density accounting imports
the same canonical `Core.OrderedDensity` interface used by #07 and #31; no
paper-local ordered-density copy is retained.
