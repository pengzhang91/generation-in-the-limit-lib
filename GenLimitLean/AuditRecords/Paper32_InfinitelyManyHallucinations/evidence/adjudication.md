# P32 informed adjudication

The substantive gaps from Stage2 remain: the complete half-density and batched-pod results, strict/fractional novelty constructions and their corollary, and the copying theorem’s tightness clause. The explanations disclose most of these gaps accurately. Native no-novelty exploration and copying constructions remain recovered; they must not be reported as absent.

The claimed refutation of Appendix LemmaD.1 is rejected: the paper already assumes the guess language infinite. Its Lean implication matches that context; the finite diagnostic is supplementary. A separate local cardinality assertion in AppendixB.2 does fail within the infinite domain and admits an inequality repair. No genuine source-to-Lean translation mismatch is established by this statement-only review.

## Provenance and limits

This is the continuing source-first/Stage2 reviewer’s informed adjudication, not a third independent blind review. The coordinator specifically asked to re-test D.1’s global infinite-guess assumption, the zero-offset certificate distinction, and the native recovered constructions. Those prompts are disclosed focus points, not mathematical evidence. Full types and source inventory remain in the frozen [Stage2 comparison](source-comparison.md), [Stage2 claim rows](stage2-claims.json) and [source inventory](source-inventory.md); they are cross-referenced rather than duplicated.

Source is only [arXiv:2606.28354v1 PDF](https://arxiv.org/pdf/2606.28354v1) and [same-version primary HTML](https://arxiv.org/html/2606.28354v1), dated 8 June 2026, 34 pages. Printed/PDF page numbers coincide at the cited locations. Expected PDF SHA-256 `67aefbbc734d010380daf4da5d2f19ceed51592e8f9004c322fefc0e43359975` remains unverified; no raw PDF bytes or successful formula images were obtained. Six earlier screenshot requests failed; exact-v1 HTML mathematical markup remains the formula fallback.

Only the stage3 prompt, supplied PaperMap/registry, frozen audit evidence and code-only kernel interfaces were consulted locally. No raw Lean proof bodies, source/registry edits, compilation, prior external audit or human ledger were used. Statements about human review inside explanation files were read incidentally and grant no human-review credit here. All mathematical checks below are **informal, not Lean-checked in this adjudication**; existing theorem interfaces are evidence of statement scope, not a new proof certification.

## Explanation inventory

| Explanation anchor | Assessment against frozen evidence |
|---|---|
| PaperMap:16–35; registry /paper/formalization_scope | Accept normalized Nat universe, semantic scope and explicit finite-history access. No extraction/runtime/oracle-complexity guarantee follows. |
| PaperMap:42; registry /claims/0 | Accept the finite-residual cardinality issue and alternative capacity-preserving native interfaces. Reject finite-guess language as a missing source premise; infinite guess was already global. |
| PaperMap:44; registry /claims/1 | Trace-level Proposition3.3 is accurately described, with the literal raw-output qualification in M2 retained. |
| PaperMap:47,50–54,78–85; registry /claims/2,4,6 | Accurate disclosure of the dynamic/same-witness/upper-bound gaps. Disclosure does not complete those claims; certificate fields remain premises. |
| PaperMap:49; registry /claims/3 | Native construction and same-witness performance support the alternative-clock explanation. |
| PaperMap:48; registry /claims/7 | Alternate quadratic schedule is legitimate; no effective real-parameter selector is established by the existential type. |
| PaperMap:55; registry /claims/8 | Copying part complete; full-coverage label must distinguish the omitted source tightness clause, acknowledged elsewhere in the same claim. |
| PaperMap:56; registry /claims/9 | Source-refutation/correction labels are unsupported in full source context; D17 matches and D18 is outside-domain. |

Pinned explanation SHA-256: PaperMap `a8fe7406d3ba303dcafd2d72b2b29c0ed211cc8765ba36dbfe037957097202b9`; registry `db9e841b3d45205d1e0890e5a08b6c0cd377233651d0ebbd196c9bed6c753c9a`. Their exact byte versions are recorded in adjudication-run.json. Their descriptions of checked proofs were not used as proof certification.

## Slot dispositions

| Slot | Stage2 correspondence | Final disposition |
|---|---|---|
| C01 | faithful-generalization | matches-source-context |
| C02 | faithful-generalization | qualified-model-or-representation |
| C03 | partial | substantive-formalization-gap |
| C04 | faithful-generalization | qualified-model-or-representation |
| C05 | partial | substantive-formalization-gap |
| C06 | faithful-generalization | matches-source-context |
| C07 | partial | substantive-formalization-gap |
| C08 | faithful-generalization | qualified-model-or-representation |
| C09 | partial | mixed |
| C10 | faithful-generalization | mixed |

For C09 and C10, mixed separates matching native mathematics from a source-component gap or metadata error; it does not mean a proven Lean translation defect.

## Discrepancy dossiers and mathematical checks

### M1 — Lemma D.1 standing domain

**Validation:** Informal mathematical check; not Lean-checked in this adjudication. Source hypothesis and existing theorem types were directly rechecked.

§2.2 p.3 assumes T,G infinite for the rest of the paper. AppendixD p.19 explicitly uses |G_n|→∞. If tail precision tends to1, for each ε>0 the later error increments satisfy e_n≤εs_n, hence total errors≤C+ε|G_n|. Dividing by diverging |G_n| gives P=1. The finite one-shot diagnostic violates infinite G (and its formal target ∅ also violates infinite T), so it refutes only an out-of-domain extension. No statement repair is needed; an explicit local reminder of the standing hypothesis is optional.

### M2 — Repeated raw invalid output versus incremental validity

**Validation:** Informal counterexample under the literal raw-output interpretation; not Lean-checked.

Use coded universe Nat, T={1,2,…}, family {T}, A_n={1,…,n}, and raw proposals {0,n} for n≥1. A generator can obtain n as max(A_n), so only the printed current-set interface is needed. Generated G_n={0,…,n}, both T and G are infinite, A is valid and infinite, and increments are bounded by2. t_1=1/2 and t_n=1 for n≥2; only one distinct invalid point is generated. Yet every raw proposal contains invalid0. Thus literal Eq.19 fails while eventual incremental validity and attained tail precision1 hold. Minimal repairs are to define validity of ΔG, as Lean does, or separately exclude re-proposals of old invalid strings. This qualifies the source model; it is not a false Lean equivalence.

### M3 — Bounded-precision appendix cardinality

**Validation:** Informal local source-proof counterexample and repair; not a certification of either full proof and not Lean-checked.

Take T=G=Nat, f(n)=1, G_n={0,…,n−1}, and R={2,4,8,…}. All source infinite-language assumptions hold and H_n=0, so this is AppendixB.2 Case2. T∖G=∅, so the finite residual exhaustion Z_j is empty. Eq.55 gives T*_2=Y_(2−r(2))=Y_1, of size1, although the following sentence claims size2. The theorem statement is unaffected. The smallest local repair is an increment inequality: with m_n=|G_n| and a_n=m_n−r(m_n), a single-step finite Z satisfies |ΔZ|≤Δr, so |ΔT*_n|≤Δa_n+Δr=Δm_n≤f(n). The finite-residual equality in Case1 Eq.50 likewise needs ≤ rather than equality after saturation. Native validPartExhaustion, its finite-valid-part precision-zero theorem, and sparsePrecisionTarget exhaustion/boundedness/precision interfaces support an alternative capacity-preserving construction. A finite-guess case is outside the source theorem domain; a finite valid part is a legitimate native proof split, not a new source premise.

### M4 — Zero-offset sparse certificates versus finite early contamination

**Validation:** Informal premise separation; not Lean-checked and not claimed to be a run of the named source algorithm.

Every ExplorationSet excludes1, so r(1)=0. A first invalid singleton therefore violates errors(Q_1)≤r(|Q_1|), even if P→1. A legal single-step strict-novel macro-trace illustrates the distinction: T={2,4,6,…}, A_n={4,8,…,4n}, Q_1={1}, and for n≥2 append4(n−1)−2. T,A,Q have infinite limits; every later output is valid and never adversary-revealed, so novelty holds and P=Qtail=1. In the natural even target order R(A)=R(Q)=1/2, target∖A⊆Q, and the source max bound holds. There is exactly one invalid output, so errors≤r(n)+1, but no reviewed SparseExplorationCertificate can hold at n=1. This separates the current all-prefix zero-offset premise from the source O(1) estimate; it does not prove that a completed source-specific implementation cannot discharge a revised or shifted obligation.

### M5 — Named witnesses and semantic access

**Validation:** Direct existing types/definition bodies, plus elementary interpretation; no new Lean check or proof certification.

NoNoveltyExploration:176 supplies the same named generator in boundedness:305, universe coverage:372 and precision:689. NoNovelty:35 states generatedExhaustion parrotGenerator A=A, with bounds and metrics at67,80,92,100. These witness identities survive the explanations; no unrelated-witness assembly is used. Both are semantic finite-history interfaces; no executable extraction, oracle bound or uniform program follows. chooseSubsetUpTo uses classical finite-subset choice. Source safe procedures also lack blanket computability assumptions.

### M6 — Alternative quadratic schedule

**Validation:** Informal construction check, not Lean-checked; existing definition and existence types support the scope.

For γ<1 choose integer M≥max(2,ceil(1/(1−γ))). Times M(k+1)^2 are infinite, exceed1 and are nonconsecutive. If r(m)≥1, Mr(m)^2≤m implies r(m)≤m/M≤(1−γ)m; below the first time r(m)=0. Also r(m)/m→0. Thus the quadratic construction supplies the same schedule property as the source exponential example. The existential endpoint does not itself identify its chosen witness or provide a computable map from an arbitrary real representation of γ.

The source anchors for M1 are §2.2 p.3 and AppendixD p.19, Eqs.89–96; the source explicitly invokes infinite G in the proof. M2 uses §3/Eqs.17,19 and Proposition3.3, pp.5–6,18–19. M3 concerns AppendixB.2 pp.14–15, Eqs.50,55 and the following cardinality sentence. M4 uses the source finite-error estimate in AppendixH pp.29–30 against the inspected SparseExplorationCertificate.mk at Certificates:26 and Strict/Gamma constructors at221/250.

The frozen inventory’s tentative cumulative-prefix E_j skip-test concern stays resolved as in Stage2: all preceding ambient enumeration elements are already in the monotone seen set at pointer j, so testing E_j or its next singleton is equivalent. It is not an additional source error.

## Component resolutions and remaining work

### C01

PaperMap:42 and registry /claims/0 mostly explain the correct alternative construction. Registry wording that an explicit finite-guess case is needed is not justified by a theorem whose standing guess limit is infinite. The native finite-valid-part split is different from a finite guess. No new source assumption is required.

- **Theorem2.1 and Lemma2.2 statements; P/R definitions: matches-source-context.** Stage2’s formulas and faithful domain generalizations stand. Making infinite G explicit is contextual, not correction of a false theorem.
- **Appendix B.2 finite-residual exact-cardinality assertions: justified-source-correction.** M3 confirms a local proof-presentation error within the infinite domain. A bounded-increment inequality repairs it without changing the theorem. Native alternative construction interfaces were checked, not their proofs.

**Minimal follow-up:** Describe the infinite-guess premise as inherited source context. If describing the appendix proof repair, identify finite residual saturation and the needed increment inequalities; do not describe the theorem itself as refuted or require a finite-guess case.

### C02

PaperMap:44 and registry /claims/1 correctly say exhaustion-level semantic equivalence, but that explanation does not prove literal equivalence to unrestricted repeated raw proposals. This is a disclosed trace-level modeling choice with a source ambiguity, not a discovered Lean theorem error.

- **Proposition2.4 binary value and exact attainment: matches-source-context.** Both clauses and the source footnote attainment sense match, with harmless finite/empty/c=0 extensions.
- **Proposition3.3 / EventuallyValid: qualified-model-or-representation.** The trace/increment interpretation matches Lean and the source proof’s intended reading. The literal raw-output version is separated by M2; its repair/interpretation must remain explicit.

**Minimal follow-up:** Document the distinction between raw repeated proposals and newly added increments beside EventuallyValid/Def.3.2 correspondence. If claiming literal Eq.19 equivalence, add the missing freshness restriction or change the source reading to incremental validity.

### C03

PaperMap:47 and registry /claims/2 explicitly disclose precisely the Stage2 gaps. Disclosure is accurate and prevents mistaking the endgame for a false theorem, but does not complete the source results. The registry’s upper-component summary adds eventual validity, while the literal P32 Theorem3.6 restatement does not repeat it; retain the printed scope.

- **Fixed-output half-density limit step D08: matches-source-context.** Correct conditional endgame scope; every all-s estimate concerns the same fixed output.
- **Theorem3.5 complete growing-pod learner; Theorem3.6 matching upper bound: substantive-formalization-gap.** Same-witness construction/certificate production and upper obstruction remain unrepresented in the checked interfaces.

**Minimal follow-up:** Finish the P15 growing-pod run and attach its quantitative certificates to that same output. Formalize the matching upper theorem, retaining the exact source quantifier/premise scope.

### C04

PaperMap:16–35,49 and registry /claims/3 accurately disclose the normalized Nat universe, history dependence, alternate clock and semantic scope. M5 supports the claimed witness properties from actual interfaces. The unnamed Overview existential is not identified by hidden proof; the separate named support suffices.

- **Theorem4.3 existence, same f-bound and R=P=1: matches-source-context.** Recovered native named generator has all same-witness supporting conclusions; the source semantic performance claim is covered/generalized.
- **Algorithm1 identity and generator access: qualified-model-or-representation.** Quadratic adversary-cardinality batching with finite history is an explicit alternative to output-cardinality pseudocode, not a literal transcription or executable extraction theorem.

**Minimal follow-up:** Keep the alternative-construction and semantic-access qualifications visible. No source-statement repair or additional theorem facade is required for this scoped performance result.

### C05

PaperMap:50–51 and registry /claims/4 are candid and consistent with Stage2. The explanatory word certified does not supply the missing input certificate. Family-wide success on indistinguishable A/T targets remains essential in the source partial upper argument.

- **Certified lower density factor and returned trace properties: matches-source-context.** The conditional analytic implication has the correct1/(k+1) factor. Its certificate already supplies novelty,P=1,Qtail=1 and the eventual vanishing-overhead ratio bound.
- **Lemma4.5 dynamic k-batched construction and Lemma4.6 upper bound: substantive-formalization-gap.** No source-shaped certificate producer/algorithm or matching adaptive upper construction found; documented as open.

**Minimal follow-up:** Construct BatchedPodsCertificate for the actual k-batched run, including single-step output and raw-batch novelty when claimed. Formalize the adaptive matching upper-bound instance and its family-wide perfect-tail premise.

### C06

PaperMap:52 and registry /claims/5 agree with the checked interface. The bound is a deterministic liminf/limsup consequence; no distributional or computational assertion is implicated.

- **Lemma4.7 complement recall: matches-source-context.** Same complement inclusion, target order, upper adversarial density and lower output density; a faithful generalization to arbitrary extensional sets.

**Minimal follow-up:** No scoped discrepancy to repair. Preserve the upper-versus-lower density distinction.

### C07

PaperMap:53–54 and registry /claims/6 accurately mark the dynamic algorithms partial, but do not discuss the early-error offset. Direct constructor reinspection confirms Stage2’s zero-offset distinction. The cumulative E_j skip-notation concern stays resolved by the pointer invariant; it is not revived as a source defect. I.3/I.4 remain separate contextual perfect-tail claims, not the indexed following CorollaryI.2.

- **Raw novelty and conditional strict/γ accounting: matches-source-context.** GeneratorNovel is raw proposal novelty on a fixed run; certificate implications preserve max(1−β,α/3), historical prefix novelty and R=P=1.
- **Algorithms6–7 and CorollaryI.2: substantive-formalization-gap.** Complete two-batched safe traces and certificate production remain missing; the full-exhaustion corollary is only conditional on an already certified trace.
- **All-prefix error envelope: substantive-formalization-gap.** The zero-offset SparseExplorationCertificate premise is stronger than the source r(n)+O(1) estimate. M4 remains an explicit assembly obligation, not discharged by generic statements that sparse-error precision is available.

**Minimal follow-up:** Supply actual safe/exploration traces with same-witness novelty/coverage/precision. Accommodate finite early contamination, or prove that the concrete implementation satisfies the stronger current envelope before instantiating Strict/Gamma certificates. Add an explicit full-exhaustion CorollaryI.2 assembly once the unconditional Algorithm7 result exists.

### C08

PaperMap:48 and registry /claims/7 correctly disclose the alternative schedule. This is faithful existence mathematics; explicit-quadratic-construction metadata should not be read as an executable extraction or arbitrary-real computation guarantee.

- **γ-admissible schedule existence: matches-source-context.** All infinitude, nonconsecutivity, exclusion of1, vanishing density and finite-prefix quota fields are present. Wider γ<1 domain and ignored index0 are harmless generalizations.
- **Quadratic versus exponential witness: qualified-model-or-representation.** An alternate quadratic family has the required property by M6. The existential type alone does not identify its selected witness or assert an effective real-parameter selector.

**Minimal follow-up:** Keep construction identity/effectiveness separate from the existential endpoint. No source correction is required.

### C09

PaperMap:55 and registry /claims/8 support the construction but label coverage full without a tightness component. The note acknowledging tightness exclusion is evidence of disclosure, not proof of that clause. Stage2’s partial whole-slot finding stands.

- **Named copying lower guarantee and metric conjunction: matches-source-context.** Recovered exact generated trace equality and recall equality confirm all four properties for one parrotGenerator; cumulative raw copying is trace-equivalent to incremental copying.
- **TheoremE.1 c-step tightness clause: substantive-formalization-gap.** Still not formalized in the checked interfaces. A note in the same registry claim acknowledges the exclusion.
- **Full-coverage metadata for entire indexed source theorem: interface-assembly-issue.** The full source theorem includes tightness. Coverage should distinguish the complete copying component from the omitted upper/tightness component.

**Minimal follow-up:** Split copying and c-step tightness components in coverage metadata. Formalize the indistinguishable-target upper guarantee if claiming coverage of all of TheoremE.1.

### C10

PaperMap:56 and registry /claims/9 source_assessment=refuted, formalization coverage=none and corrects/refutes link roles conflict with the actual source domain. Re-reading exact v1 §2.2 and AppendixD directly confirms M1. Another note in the same registry claim itself recognizes that the diagnostic violates the standing infinite-guess assumption; no external human ledger or human-review credit is used.

- **Appendix LemmaD.1 in full source context; D17: matches-source-context.** Infinite G is a standing source assumption and is explicit in Lean. The implication matches; no false source statement was repaired.
- **D18 finite diagnostic: matches-source-context.** Valid supplementary diagnostic of an unrestricted finite-output extension, outside the source domain. It does not refute LemmaD.1.
- **PaperMap/registry refutation and source-correction labels: interface-assembly-issue.** Reject the explanation as a source refutation: it ignores §2.2’s global infinite-guess assumption. Metadata needs correction, not the Lean implication or source lemma.

**Minimal follow-up:** Reclassify the source-context lemma as covered by D17, with its standing infinite-guess premise explicit. Describe D18 as a finite-domain extension diagnostic; remove source-refutation/source-statement-false wording and corresponding corrects/refutes roles where they assert refutation of the contextual paper claim.

## All 18 target coverage

`I.` abbreviates `GenLimit.InfinitelyManyHallucinations.`. Dossiers D01–D18 and exact full types are unchanged in the frozen Stage2 report and Stage1 interface. Every target is covered once below.

| Slot / dossier | Exact declaration after I. | Original module anchor | Target resolution |
|---|---|---|---|
| C01 / D01 | `I.Results.lemma_2_2` | Results.Overview:49 | matches-source-context; See frozen Stage2 dossier and slot adjudication. |
| C01 / D02 | `I.Results.theorem_2_1` | Results.Overview:44 | matches-source-context; See frozen Stage2 dossier and slot adjudication. |
| C01 / D03 | `I.lowerMembershipPrecision` | Definitions:172 | matches-source-context; See frozen Stage2 dossier and slot adjudication. |
| C01 / D04 | `I.lowerRecall` | Definitions:183 | matches-source-context; See frozen Stage2 dossier and slot adjudication. |
| C02 / D05 | `I.Results.proposition_2_4_constant_step` | Results.Overview:55 | matches-source-context; See frozen Stage2 dossier and slot adjudication. |
| C02 / D06 | `I.Results.proposition_2_4_single_step` | Results.Overview:52 | matches-source-context; See frozen Stage2 dossier and slot adjudication. |
| C02 / D07 | `I.Results.proposition_3_3` | Results.Overview:58 | qualified-model-or-representation; Incremental validity matches; literal repeated raw proposals need M2 qualification. |
| C03 / D08 | `I.Results.theorem_3_5_fixed_pod_endgame` | Results.Overview:89 | substantive-formalization-gap; Fixed-output scalar endgame only; full lower learner and matching upper remain absent. |
| C04 / D09 | `I.Results.theorem_4_3` | Results.Overview:68 | qualified-model-or-representation; Full semantic performance via recovered named alternative construction; history/clock qualified. |
| C05 / D10 | `I.Results.lemma_4_5_of_trace_certificate` | Results.Overview:73 | substantive-formalization-gap; Certificate input includes novelty,P=1,Qtail=1 and the ratio envelope; no dynamic producer. |
| C06 / D11 | `I.Results.lemma_4_7` | Results.Overview:61 | matches-source-context; See frozen Stage2 dossier and slot adjudication. |
| C07 / D12 | `I.GeneratorNovel` | Definitions:258 | qualified-model-or-representation; Raw novelty on one run; global generator novelty requires all-adversary quantification. |
| C07 / D13 | `I.Results.theorem_4_8_of_trace_certificate` | Results.Overview:78 | substantive-formalization-gap; Correct conditional assembly; missing safe run and zero-offset envelope instantiation. |
| C07 / D14 | `I.Results.theorem_4_9_of_trace_certificate` | Results.Overview:83 | substantive-formalization-gap; Correct conditional assembly; missing safe run and zero-offset envelope instantiation. |
| C08 / D15 | `I.Results.gamma_admissible_exploration_exists` | Results.Overview:98 | qualified-model-or-representation; Full schedule existence; alternate quadratic witness/effective selection qualified. |
| C09 / D16 | `I.Results.appendix_valid_generation_without_novelty` | Results.Overview:94 | mixed; Copying conjunction complete; whole source theorem still lacks c-step tightness. |
| C10 / D17 | `I.Results.appendix_lemma_D_1_of_limit_infinite` | Results.Overview:108 | matches-source-context; Explicit infinite guess matches global source context, not a theorem correction. |
| C10 / D18 | `I.Results.tail_precision_one_finite_guess_counterexample` | Results.Overview:102 | interface-assembly-issue; Finite diagnostic is outside source scope; source-refutation attribution rejected. |

## Scope of the result

The deterministic density statistics, lower/upper limits, distinct-set novelty, constants and infinite-limit assumptions remain as reconstructed in Stage2. Semantic countability does not imply computability: neither the source’s infinite-set safe routines nor arbitrary Lean functions/classical choices establish an ordinary executable learner. Native same-witness interfaces support C04/C09; partial certificates do not imply Algorithms2,6,7 or the separate perfect-tail repetition construction exist in Lean. No claimed source correction excuses those independent gaps.

All 10 slots and all 18 targets have dispositions; completion of this adjudication is separate from completion of the formalization. All three earlier freezes and their nine outputs remain byte-identical. No source, registry, PaperMap, Lean or coordinator aggregate metadata was changed. Stop here for coordinator adjudication freeze.
