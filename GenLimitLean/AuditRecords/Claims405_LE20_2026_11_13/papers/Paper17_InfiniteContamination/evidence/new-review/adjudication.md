# P17 C03 informed adjudication

**Final disposition: mixed.** The omitted increasing threshold envelope is a disclosed, mathematically justified choice for the modified semantic rank construction. The same-witness membership supplement resolves the standalone rank endpoint's zero-outside issue. Exact identity with the printed Algorithm 8, including the proposed round shift, is not established and is contradicted as an identity of output procedures by the example below. Thus the native result is a qualified representation of the source mechanism; the documentation/registry overstates literal equivalence. This is not evidence of a false Lean theorem or a source error.

Audit completion is separate from that disposition: C03 is adjudicated, with no proof-body/full construction audit, no Lean build, and no human certification. No other P17 claim is re-audited.

## Context and immutable evidence

This is the **continuing Stage2 reviewer after its independent comparison froze**, not a third blind review. The Stage2 freeze is `stage2-freeze.json`, dated 2026-11-14T00:28:03.572314+00:00, SHA256 `16169acecb0fafd0fc6ace9fb8da830ea86d036cd4118c66224dd8f7f4af4ab3`. All its named outputs, original Stage1 outputs and the separate supporting-theorem supplement remain unchanged.

The source is arXiv:2511.07417v1, 2025-11-10, original PDF SHA256 `e1ef3e6d24cc382782446f24cb4377b885034812d3d678cf8d9789a703f5e0a9`. Claim6.17 is printed p.45/PDF48, Algorithm8 printed p.44/PDF47, standing conversion setup printed p.43/PDF46. The prior source-first visual checks and 71-page context reading are retained; pp.43-45 were reread from the same pinned base-page text in this stage. No annotated-source payload was used.

Requested model/settings are gpt-6.1-sol/xhigh; backend identity/revision and effective setting are not independently exposed. Parent messages supplied scope, freeze/resume authorization and questions to investigate, not the mathematical argument or counterexample below. Original Stage1 and supplement both disclose retained broader Lean-only exposure before narrowing, and are not relabeled fresh here.

## Scoped targets and final coverage

| Slot / target | Source correspondence | Mathematical evidence / final disposition |
|---|---|---|
| C03 / `GenLimit.InfiniteContamination.claim_6_17_algorithmEight_rank` (`AlgorithmEight:756`) | Eventual rank bound for the native semantic variant, not established as the literal printed procedure | Exact type/definitions checked. Local informal argument below supports the variant's own bound. **Qualified model/representation** for the mechanism; **coverage/documentation gap** for an assertion of exact literal Algorithm8 equivalence. |
| C03 supporting target / `GenLimit.InfiniteContamination.algorithmEight_generates_of_eventually_selected` (`AlgorithmEight:698`) | Eventual target membership and both freshness conditions for exactly the same native generator | Reconstructed in a separate source-withheld supplement, not original Stage1. Its premises are included among the rank premises. Combining the two statement thresholds supplies the source-style membership component for the variant. **Matches source context**, with no new proof audit. |

Both entries belong to the same original ID, `claim:mvyz25:claim-6-17`; the second is supporting evidence, not another claim slot. Uninspected names mentioned in the PaperMap/comments are not counted as reconstructed or reviewed endpoints.

## Source and Lean statements retained

The source fixes a countable collection of infinite languages, a target K, an enumeration (potentially contaminated), a set generator with infinite A_n, and finite L_n. It assumes A_n is contained in the intersection of L_n minus the n observed inputs for every round; eventually K belongs to L_n and mu_low(A_n,K)>=rho. In the nontrivial branch rho>0, Claim6.17 asserts

`exists n_star, forall n>=n_star, w_n in first_ceil(2*n*(1+2^(-k(n)))/rho)(K)`.

Here w_n is the actual output of printed Algorithm8. Its density threshold is first least positive, then replaced by max(m_n,m_(n-1)+1); k(n) is the latest fitting stage <=n, fallback1; w_n is the least historical-set point outside all n observed inputs and n-1 prior outputs. Canonical order is increasing, input enumerations ordinarily have no repeats, and rho is known. No additional numerical contamination/displacement bound is required in this conditional conversion.

The Lean rank target has fixed setGen, global infinitude on every history, finite selection, indexed ordered family, rho>0, the global core-minus-sample invariant, carrier equalities and increasing orders. For every target and arbitrary stream, eventual selection and eventual pointwise set lower-density>=rho imply eventual

`rank_K(output(g,stream,t)) <= ceil_Nat(2*(t+1)*delta_(s_t)/rho)`,

where `delta_s=1+(1/2)^(s+1)`, g is the named `algorithmEightGenerator`, and s_t is the greatest admissible stage <=t, with fallback0. Each stage cutoff c_s is an independent classically chosen valid finite density threshold, maximized across the finite selection. Current history length is t; the selected original set uses s observations. The output removes t sampled observations and t earlier outputs, including the empty-history output. Thresholds remain instance-dependent existential witnesses, with eventual-for-all-time quantifiers and no effective/uniform rate.

For nonmembers rank_K is zero, so the rank statement alone is weaker than prefix membership. The supporting theorem gives membership and both freshness conjuncts for the same g under fewer hypotheses. At max(N_rank,N_membership), carrier equality yields the full membership-plus-native-bound conjunction. No unnamed existential generator is substituted.

## Existing explanations: inventory and checks

All explanations below were opened only after the Stage2 freeze. Comments establish disclosure, not correctness.

| Explanation | Pinned artifact / anchor | Check |
|---|---|---|
| The implementation retains the adaptive mechanism; the increasing envelope is unnecessary because every fixed cutoff eventually fits | `owner/lean-snapshot/GenLimit/Paper17_InfiniteContamination/AlgorithmEight.lean`, module comment starting line6; SHA256 `e12d25319aa3b96bb1b6fdbc8db3cdd01a0add466c92793263dfc930834a6bec` | This is an explicit pre-existing disclosure. Actual `densityCutoff`, `finiteDensityCutoff`, stage/budget/index definitions contain no increasing-envelope update. The rank-level explanation is justified below. The comment's additional density-endpoint assertion is outside this C03-only audit. |
| Slack exponent is shifted for one-based rounds; cutoff comment maps Lean t to paper t+1 | Same file, comments at lines36 and528; actual definitions at38 and530 | The arithmetic substitution is visible, but the history semantics are not shifted along with it. The output-identity example below disproves a literal interpretation on the same input. |
| Output and claim are described as literal Algorithm8 | Same file, comments at304 and755; generator at331 | Least-fresh structural rule agrees, but calling the entire procedure literal overstates the threshold/time identity. |
| Full semantic interface, increasing ambient order explicit; global infinitude disclosed; development is semantic/classical | `P17/stage3-context/PaperMap.md`, lines28-29,36,50; SHA256 `dab69d581721f865202f9878b54d0e2e68eed289e56fbe035c89966959510adf` | Ambient order and global infinitude are genuinely explicit in checked definitions/types. Semantic scope is disclosed. Full literal Algorithm8 equivalence does not follow from those qualifications. No kernel/proof assertion in the PaperMap is independently certified here. |
| C03 is accepted with ambient-order qualification, coverage full, link faithful-equivalent | `P17/stage3-context/current-registry.json`, claim object with id `claim:mvyz25:claim-6-17`; SHA256 `238adb3cae7bb33f1baf07eeb6a06262e2703cd38058846fc01dafc7fa0162d0` | This accurately records an order qualification but omits the threshold variant and history convention. Its literal equivalence classification is stronger than the checked evidence. The note about kernel checking is not source-correspondence evidence. |

Raw owner-source access in this stage was restricted to extracted comments, declaration header locators, and selected **definition** bodies. No theorem proof body was displayed or used. The Generic output definition (`Core/GenericGeneration:87`, file SHA256 `a92d4e3f0101d187a45b46e3c6921fea54f9bd8cd5435ed28241de3fe318dd92`) confirms that time t supplies only observations with indices below t.

## Mathematical checks

These are **informal mathematical arguments, not Lean-checked additions or proof-body certification**.

### A. An increasing cutoff envelope is unnecessary for the variant's rank guarantee

Fix a stream and rho>0. Every c_s is a finite natural, delta_s>1, and for a fixed s the inequality

`c_s/delta_s <= 2*(t+1)/rho`

holds for all sufficiently large t. Taking t>=s makes s a candidate for the greatest-stage selector. Therefore for each S, all sufficiently large t have s_t>=S. The selected stage tends to infinity even if the sequence c_s is neither least nor increasing. This uses the greatest admissible stage rule, not an assumption that the numerical cutoffs are monotone.

For sufficiently late t, s=s_t is positive and beyond the eventual selection/density thresholds. Thus K is selected at s, A_s is contained in K, and its lower density in K is at least rho. Positive-stage admissibility gives the budget inequality. Put

`B_t=ceil(2*(t+1)*delta_s/rho)`.

Then B_t>=c_s. The defining density-cutoff property, applied to the selected target, gives at least `(rho/delta_s)*B_t >= 2*(t+1)` points of A_s in the first B_t target positions. At most 2t distinct points are excluded by the t observations and t prior outputs. A point remains in that prefix. Because A_s is contained in K and its enumeration increases in the same ambient order, the least permitted A_s point has target rank<=B_t. This establishes the local rank argument for the **variant's own selected stage and displayed bound**, with the actual hypotheses checked. It does not prove equality of its sequence with the paper's sequence.

This explains why changing least thresholds and dropping the envelope need not be an erroneous mathematical translation of the underlying method. No source repair is required: the paper's stronger normalization can remain unchanged.

### B. The proposed round shift does not identify the two output procedures

Take the singleton collection K=N (use an order-preserving +1 relabel to the paper's positive naturals). At every finite history h, let the set output be N minus the finite sample of h; select K at every stage, use increasing identity orders, and set rho=1. Every output set is infinite; the global core-minus-sample invariant holds; all densities are1; target selection is permanent. Let the observed Lean stream be x_t=t. It is injective and fully enumerates K, with no noise or omissions; these choices are effective even without nonstandard oracle power.

For every selected s<=t, the selected A_s excludes only an earlier sample prefix. The current forbidden set excludes all observations below t and, inductively, all previous outputs0,...,t-1. Consequently the least permitted native output is y_t=t, independently of the chosen thresholds.

Under the comment's proposed n=t+1 identification on this same enumeration, the paper has **already seen x_n=t** before outputting w_n (or value t+1 after the +1 relabel). The source output rule forbids that value, whereas the native procedure outputs it. The proposed identification thus fails at every round in this example, not only at the initial boundary.

This refutes literal output identity under that shift. It does **not** refute either eventual rank bound: different output procedures can satisfy comparable rank/density guarantees. It also does not show the printed source claim is wrong. Identifying source n with history length t aligns the observations instead, but leaves the native t+1 factor and s+1 slack shift as changes of the finite-time statement. No exact bridge is among the reconstructed interfaces.

### C. Model and access qualifications remain separate

The source permits collection queries, including density and density-rate oracles, and forbids target-as-target/future-input access. The native function uses only the observed history and fixed setGen/selection/orders/rho, so no illicit future/target argument is introduced. However it uses semantic sets, exact lower-density values, classical selection of cutoffs, classical decisions and least-natural selection. There is no explicit uniform finite-query oracle program, set representation, density-modulus interface, query bound, ordinary-computability theorem or complexity bound in these targets. The PaperMap discloses this semantic scope. It is a qualification, not evidence that ordinary computation was proved or that the source demanded ordinary computation without oracles.

Global infinitude/core assumptions on every history are stronger than the source's literal fixed-run presentation. Arbitrary, possibly repeating streams broaden the conditional domain. No total strength ordering is imposed on these opposing changes. The required assumptions are sufficient hypotheses of these endpoints; no necessity claim is inferred.

## Disposition by component and minimal follow-up

- **Threshold variant:** qualified model/representation. The pre-existing explanation is disclosed and the local mathematical justification is sound at the checked rank level. No source correction or Lean bug finding is needed.
- **Membership unbundled from rank:** matches source context for the same native witness, using the separately frozen source-withheld supplement. No coverage gap remains for this component.
- **Exact printed Algorithm8 and finite-time formula:** literal procedure equality is not established; the claimed t-to-t+1 identity fails on the explicit example. Record a representation/coverage and documentation gap for claims of literal equivalence, rather than a false-theorem finding. Source Claim6.17 about its exact printed output is not certified by the inspected variant interfaces alone.
- **Semantic access/global conditions:** qualified model/representation, explicitly preserving the computational and hypothesis boundaries.

The smallest useful follow-up is to document C03 as the alternative semantic construction, including independent cutoffs and the actual history convention, and qualify the registry's faithful-equivalent/full wording accordingly. If exact printed-algorithm coverage is intended, supply a separately reconstructed explicit correspondence/transfer interface or formalize its maintained threshold/output convention. Those are future choices; no Lean, registry, source, Git or human-record change was made here.

There is no justified source-error repair to propose. The remaining uncertainty is the intended equivalence/coverage policy and any unreviewed correspondence interface, not whether the displayed definitions contain the envelope or consume t observations. No broader density theorem, proof body, imported result or census name is silently used to close that gap.
