# P32 independent Stage 2 source comparison

Four grouped slots are partial: C03, C05, C07 and C09. The other six preserve the indexed source mathematics, with explicit generalizations or harmless representation choices. The main gaps are algorithm/certificate production, same-witness density assembly, and the separate optimality/tightness components. No reviewed arithmetic/metric formula establishes a genuine translation bug. The raw-output validity issue is a source/model ambiguity.

## Identity, isolation and evidence

Source: Strauss–Butoi–Cotterell, *Generating in the Limit with Infinitely Many Hallucinations*, [arXiv:2606.28354v1 PDF](https://arxiv.org/pdf/2606.28354v1), 8 June 2026, 34 pages; [same-version primary HTML](https://arxiv.org/html/2606.28354v1). Printed/PDF pages coincide for the cited locations. Expected PDF SHA-256 `67aefbbc734d010380daf4da5d2f19ceed51592e8f9004c322fefc0e43359975` was **not verified**. No raw PDF bytes or successful formula images were obtained: six source-first screenshots failed. HTML mathematical markup resolved stars, denominators and schedules against PDF extracted text; visual/layout verification remains unavailable.

The independent [source inventory](source-inventory.md) was frozen at 07:22:37 UTC, before Stage1 access. Stage1 was frozen at 07:32:26 UTC on 14 November2026. Both freezes and all six frozen outputs were rehashed and preserved. The supplied source snapshot hash is `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc`; it is supplied metadata, not independently checked against raw source.

All 10 source slots and 18 requested targets were rechecked against exact types and defining bodies. The recursive interface has 83 rows; the native census has 1,807 rows, including 475 P32 rows. Native supporting types were searched before making coverage findings; this is not individual review of every helper. No raw Lean comments, theorem proof bodies, owner/stage3 explanations, registry/PaperMap, prior audit, Git mutation, compilation or human certification was used.

## Shared mathematical and representation context

Finite nonempty alphabet; T,G infinite. Exhaustions start empty and have finite monotone stages. In generation claims 𝒯 is countable with infinite members, T∈𝒯, and A⊆T is infinite; recall is relative to a fixed target enumeration in §§3–4. Metrics count distinct strings with real liminf/limsup, not probability or token-frequency losses. No blanket computability assumption; the safe routines use semantic infinite-set operations.

Write P=lowerMembershipPrecision, Qtail=lowerTailPrecision, R=lowerRecall and R⁺=upperRecall. Cumulative precision uses |valid∩G_n|/|G_n|; recall uses target-prefix denominator; tail precision uses only ΔG_n and assigns1 to empty increments. Lean cumulative empty fractions are0, irrelevant eventually for the source infinite domain. Source lower/upper stars remain liminf/limsup. There are no probability laws, support assumptions, random losses, confidence levels or convergence rates in this scope.

Lean represents strings by Nat and languages by Set Nat; no word operations matter here. OrderedLanguage supplies an injective enumeration with range equal to its carrier. Thus ordered recall is the source enumeration instance; C01 also has a general exhaustion recall theorem. Positive steps are indexed by n+1; capacity at0 is unused. Dropped source family/infinitude assumptions are assessed by their actual mathematical role rather than treated automatically as errors.

BatchGenerator receives time, the finite adversary-stage history through that time and prior generated cumulative guesses. The source displayed signature gives only current A and prior G, while its pseudocode has counters/state. This explicit online interface is a model elaboration. Arbitrary mathematical functions and classical finite filtering/choice do not supply executable programs. Safe routines in the paper also use infinite-set membership/equality/infinitude operations without a blanket computability assumption.

## Full source-to-interface matrix

| Slot | Independent source scope and precise locator | Classification | Material result |
|---|---|---|---|
| C01 | Theorem2.1/Lemma2.2, Eqs.9,12; pp.4,14–17 | faithful-generalization | Bounded precision and unrestricted recall suprema agree; finite/zero-capacity extensions. |
| C02 | Propositions2.4/3.3; pp.4,6,18–19 | faithful-generalization | Both attainment clauses and incremental validity equivalence; literal raw-output interpretation qualified. |
| C03 | Theorems3.5/3.6, Eqs.21–22; p.6 | partial | Only fixed-output scalar half-density endgame; complete learner and matching upper result absent. |
| C04 | Theorem4.3, Eq.26; pp.7–8,21; Algorithm1 | faithful-generalization | Full performance theorem, with named native alternative construction and same-witness support. |
| C05 | Lemmas4.5/4.6, Eqs.27–28; pp.8–9,24–28 | partial | Conditional certified lower factor; no batched pods construction or upper result. |
| C06 | Lemma4.7, Eqs.29–31; p.9 | faithful-generalization | Complement inclusion implies lower recall ≥1−upper recall. |
| C07 | Theorems4.8/4.9, CorollaryI.2; pp.10,29–32; Eqs.32–33,141 | partial | Correct conditional max and γ formulas; no source algorithm/certificate production or unconditional corollary. |
| C08 | LemmaI.1/Definitions4.1–4.2; pp.7,30; Eq.137 | faithful-generalization | Complete admissible schedule existence; all-prefix and asymptotic requirements retained. |
| C09 | TheoremE.1 incl. tightness; p.20; Eqs.97–103 | partial | Copying witness complete and trace-equivalent; c-step tightness absent. |
| C10 | LemmaD.1; p.19; Eqs.89–96 | faithful-generalization | Infinite-G hypothesis matches source standing assumption; extra finite example lies outside source scope. |

## Per-slot comparisons

### C01

D01–D04 use the correct denominators and supremum domains. Theorem2.1 keeps one fixed guess trace and optimizes target exhaustions with the same f; Lemma2.2 fixes one target exhaustion and optimizes guess exhaustions. An infinite f-bounded guess forces unbounded cumulative f-capacity, so omitting the separate capacity-divergence premise does not weaken the source case. Source f:ℕ→ℕ is positive; Lean Nat-valued f may vanish. Finite L/guess extensions and empty cumulative score0 are beyond the source standing domain. Nat coding of strings and zero/successor indexing preserve the set-based claims.

**Algorithm scope.** Semantic supremum identities only. No selected maximum, algorithm to optimize, or effective membership test follows. Classical finite filtering is not an oracle contract. Upper-limit variants in B.2/C.2 are contextual; these two indexed theorem endpoints are lower-limit results.

**Strength and gaps.** At source assumptions the formulas agree; weaker domain assumptions extend the statements. No changed scale, denominator or asymptotic direction. The lowerRecall definition uses an injective enumeration rather than an arbitrary target exhaustion, but the independently checked lemma_2_2 covers the latter. This is a representation choice, not missing general recall mathematics. No assertion of an attaining witness is exposed by the two target equality types.

### C02

D05–D07 preserve attainment rather than falsely asserting eventual constancy when the lower value is0. TailPrecisionOneFromFiniteTime is an all-late exact-one predicate, not merely Q=1. Empty increments score1. Nat c=0 and finite/empty traces harmlessly extend Proposition2.4. The actual EventuallyValid definition constrains increments; it does not forbid endlessly proposing an old invalid string whose repetition disappears under union.

**Algorithm scope.** No cutoff-finding procedure or rate. BatchGenerator receives time/history, but these three statements concern arbitrary traces and do not impose a learner access model.

**Strength and gaps.** Generalizes the incremental statements beyond infinite source traces. The raw-output issue is a change of interpretation, not an ordered stronger/weaker theorem. Literal Eq.19 raw proposals and the Lean incremental predicate are different unless raw outputs are fresh additions. The source proof itself uses the incremental reading, so classify this as a source/model qualification, not a demonstrated Lean bug.

### C03

D08 is ∀K,B,α, [∀s≥2, α/(2+4/s)≤density_K(B)]⇒α/2≤density_K(B). The output B is fixed before s; every approximate bound is a premise. Native Paper15 support supplies GrowingPodRatioCertificate.alpha_half and PodCapacityOneCertificate.pod_capacity_one_alpha_half, with explicit ratio/charging certificate premises. It also supplies a fresh/eventually-valid partial-enumeration output, but no checked interface connects that same output to the all-s half-density certificates. These facts cannot be assembled by choosing unrelated witnesses.

**Algorithm scope.** No Algorithm2/pods construction is specified by D08. Native partial-enumeration eventual-validity results and certificate endgames are distinct interfaces; construction and proof correspondence remain incomplete.

**Strength and gaps.** The scalar implication is mathematically consistent with a proof endgame, but its additional hypotheses and missing learner/worst-case conclusions prevent a total strength comparison with the full source theorem pair. The indexed pair is not discharged by a limiting arithmetic lemma. The upper Theorem3.6 is missing from the checked density-result signatures; its printed version does not repeat a perfect-tail hypothesis, which must not be silently inserted. Existence or eventual validity of some other native output does not establish the same-witness half-density conjunction.

### C04

D09 quantifies ∀target,L,f ∃G ∀A, Infinite(A.limit)∧A.limit⊆L∧BoundedBy f A⇒same-Q boundedness,R=1,P=1. target.carrier need not equal L, and no family parameter is needed. The source instance is obtained by setting L to the target language. The native noNoveltyExplorationGenerator spacing has independent theorems for f-boundedness, universe coverage and P=1 for every spacing≥2; the same named generator supports all three. Thus this is not merely a conditional certificate facade or target-dependent oracle witness.

**Algorithm scope.** BatchGenerator has index, finite cumulative history and previous guesses. The concrete rule consults only current/previous adversary stages, their cardinalities and previous guesses. Exploration emits indices k whose spacing·(k+1)^2 threshold was crossed by adversary cardinality. Remaining increment capacity is filled from new valid adversarial strings. chooseSubsetUpTo uses Classical.choose over finite subsets, so no executable/complexity guarantee is inferred. D09’s existential does not identify its witness; the named native supporting statements separately permit same-witness assembly.

**Strength and gaps.** The source performance result is covered and generalized by decoupled validity/coverage targets and no family constraint; no stronger tail precision or novelty is claimed. Different algorithm identity is assessed separately. Generator access explicitly includes time/history, while the source displayed function signature has only current A and prior G although its pseudocode uses state. Record this model elaboration. Alternative sparse schedule/budget rule differs from Algorithm1; no claim of line-by-line implementation or proof audit. Zero-capacity f and finite L cases with no infinite admissible A are vacuous, not counterexamples.

### C05

D10 takes a Type-valued certificate carrying h_n→0 and eventually a_n≤(k+1)g_n+h_n, plus trace novelty,P=1,Q=1. With α≤liminf a_n it concludes α/(k+1)≤liminf g_n and repeats those three properties. Taking α=R(A) yields the advertised scalar lower factor, but no Algorithm2 run or certificate producer from a k-batched adversary is supplied. Direct native certificate-type searches found only constructors, projections, eliminators and these conditional summaries, not a construction theorem. The source partial upper proof also requires family-wide Q=1 on indistinguishable targets A,T; Q=1 on a single T-run alone would not suffice.

**Algorithm scope.** Trace accounting theorem, not batched pods algorithm correctness. No adversary validity, k-step input, single-step output, countable family, or progress hypothesis is present except whatever is explicitly packaged in the certificate; k is any Nat.

**Strength and gaps.** The conditional density inference generalizes across arbitrary certified traces and k, while the added certificate hypotheses and missing construction/upper result make it strictly incomplete as a formalization of the grouped source claims. The assumed eventual ratio inequality substitutes for the source charging analysis. Novelty and both precision conclusions are assumed inside the certificate. Algorithm/certificate production and the optimality half of the grouped claim are unrepresented in checked interfaces.

### C06

D11 is ∀K,A,B, K.carrier∖A⊆B⇒1−upperRecall K A≤lowerRecall K B. Both statistics use K’s same injective enumeration. The upper quantity is a limsup, as required by liminf(1−a_n)=1−limsup a_n. Removing generation and A⊆T assumptions is legitimate because only the set inclusion matters; off-target points do not affect prefix counts.

**Algorithm scope.** Pure deterministic set-density implication, no learner construction or computable coverage test. Pointwise eventual appearance is represented by inclusion in the final output set; no uniform finite completion time is asserted.

**Strength and gaps.** Generalizes the indexed source set implication without changing its bound or enumeration dependence. No material discrepancy. Replacing upperRecall by lowerRecall, or assuming a common finite coverage time, would be wrong; neither occurs.

### C07

D12 defines raw run novelty and its native traceNovel theorem connects it to Novel(A,Q). D13’s StrictNoveltyCertificate requires size(Q_n)→∞, errors(Q_n)≤r(|Q_n|) for every n, Novel(A,Q), target∖A.limit⊆Q.limit and R(A)/3≤R(Q). Its conclusion Novel∧P=1∧max(1−R⁺(A),R(A)/3)≤R(Q) has the right constants and limsup placement. D14’s GammaNoveltyCertificate requires the same sparse growth/error envelope, γ-admissibility, |Q_n∖N_n|≤r(|Q_n|) at every n, and univ⊆Q.limit; its conclusion γ-novel∧R=1∧P=1 is correct conditional content. Native searches found no algorithm producing either certificate from single-step adversarial input.

**Algorithm scope.** Algorithms6–7, their safe/exploration interleaving and their family-uniform success are not represented by these conditional endpoints. Historical novelty N_n is correctly frozen at first generation; it is not instantaneous Q_n∖A_n. The supplied types assert neither single-step output nor one output every round, and no Q=1. Generic clock/history access is more explicit than the source displayed generator signature.

**Strength and gaps.** Conditional trace statements are more general in their allowed representations/parameters, but rely on stronger premises and omit learner existence, step bounds and source algorithms. This is incomplete coverage, not a false max/γ formula or a proven translation bug. SparseExplorationCertificate requires a zero-offset error bound at every prefix. The source proof permits errors≤r(n)+O(1), accounting for finitely many invalid safe outputs. A trace whose first singleton is invalid cannot satisfy this certificate because every ExplorationSet has r(1)=0. Certificate production therefore needs extra work or a finite-contamination treatment; it cannot be assumed to follow verbatim from the source estimate. Strict certificate already assumes novelty and the one-third bound; gamma certificate already assumes full ambient coverage. No checked native certificate constructor establishes these hypotheses for Algorithms6–7. CorollaryI.2 must not be confused with the distinct perfect-tail CorollaryI.4.

### C08

D15 is γ<1⇒∃E:ExplorationSet,∀m∈Nat,r_E(m)≤(1−γ)m. Constructor fields contain every exploration-set property, not merely admissibility. Source γ∈[0,1) is covered. At m=0 the count is0 and the added inequality is trivial. Unlike the positive-integer source domain, the carrier may include0, but deleting0 preserves all positive-prefix counts, infinitude and every required property.

**Algorithm scope.** The existential does not name E or give a uniform computable map from a representation of γ. Native support separately defines quadraticTime spacing k=spacing·(k+1)^2 and a quadraticExplorationSet, whereas the source proof uses M·2^i. These are alternative sparse schedules; the inspected existential type does not identify its witness with either one.

**Strength and gaps.** Same source existence property after harmless domain/index representation; broader real-γ range. No γ=1 endpoint claim or quantitative decay rate. The wider γ<1 range is a generalization, not an omitted lower-bound obligation. Natural index0 is excluded from explorationCount and all source-positive rounds; it creates no quota or density discrepancy. No generator or certified output trace follows merely from schedule existence.

### C09

D16 retains infinite A, A.limit⊆L, f-bound and α≤R(A), and gives the same parrot-generated Q its f-bound,R(Q)≥α,P=Qtail=1. Native generatedExhaustion_parrotGenerator states Q=A exactly and lowerRecall_parrotGenerator gives equality of recall, not merely the target lower bound. The raw generator returns cumulative A_n rather than ΔA_n, but union with prior output yields the identical cumulative trace and increment; all returned points remain valid. No family or target.carrier=L assumption is needed for this copying argument.

**Algorithm scope.** An explicit named finite-data rule needing only current adversary stage; no target-membership oracle. Increments, rather than potentially large cumulative raw proposal batches, satisfy f. The source c-step tightness requires universal perfect-tail success on both A and T and an indistinguishable reveal stream; none of these follow from the copying witness.

**Strength and gaps.** Constructive lower part is covered/generalized and same-witness assembly is explicit; the optimality assertion remains uncovered. The grouped source theorem includes its tightness sentence; that component is not present in the checked interfaces. Cumulative versus incremental copying is trace-equivalent here; it is not a novelty guarantee or a changed error metric.

### C10

D17: ∀L,Q,Infinite(Q.limit)⇒Qtail(L,Q)=1⇒P(L,Q)=1. This does not require eventual exact t_n=1, only its liminf. D18: with L=∅ and Q_0=∅,Q_n={0} for n>0, Qtail=1 and P=0. Its limit is finite and its target is empty. Source §2.2 already assumes both T,G infinite, and AppendixD explicitly uses |G_n|→∞; the formal diagnostic therefore does not reveal a missing source assumption or repair a false source lemma.

**Algorithm scope.** Semantic weighted cumulative-error implication and explicit diagnostic exhaustion only; no learner, cutoffs, rates or algorithm audit.

**Strength and gaps.** The implication is generalized only by allowing finite/arbitrary L while retaining the essential infinite guess. The diagnostic is supplementary mathematics with the specified two equalities. No source translation defect established. Explicitly stating a global source hypothesis in Lean is faithful, not an added restriction. The extra counterexample is outside both source infinite-target and infinite-guess assumptions; it illustrates failure of a fully unrestricted extension.

## Eighteen target dossiers

Every normalized type below was checked against the exported full type. Implicit parameters are universally quantified; every conjunction is retained. `I.` abbreviates `GenLimit.InfinitelyManyHallucinations.`. Constructor predicates are fully expanded immediately below the table. Exact machine types remain in stage1/01-target-statements.md.

| Dossier / slot | Exact declaration after I. and original anchor | Complete normalized content |
|---|---|---|
| D01 / C01 | `Results.lemma_2_2` — Results.Overview:49 | ∀T̲,B: sup_(Q̲.limit=B) liminf |T_n∩Q_n|/|T_n| = liminf |T_n∩B|/|T_n|. No bounds/infinite hypotheses. |
| D02 / C01 | `Results.theorem_2_1` — Results.Overview:44 | ∀f,L,Q̲: Infinite(Q.limit)→BoundedBy f Q→sup_(T̲.limit=L,BoundedBy f T) liminf |T_n∩Q_n|/|Q_n|=P(L,Q). |
| D03 / C01 | `lowerMembershipPrecision` — Definitions:172 | P(L,Q):=liminf_n membershipFraction L Q_n; empty cumulative fraction0; otherwise |L∩Q_n|/|Q_n|. |
| D04 / C01 | `lowerRecall` — Definitions:183 | R(K,B):=K.lowerDensity B=liminf_n |{i<n:e_K(i)∈B}|/n; n=0 fraction0; K has injective full target enumeration. |
| D05 / C02 | `Results.proposition_2_4_constant_step` — Results.Overview:55 | BoundedBy (const c) Q→∃N:t_N=Qtail(L,Q) ∧ ∀n≥N,Qtail(L,Q)≤t_n; c any Nat. |
| D06 / C02 | `Results.proposition_2_4_single_step` — Results.Overview:52 | IsSingleStep Q→(Qtail=0∨Qtail=1) ∧ same equality-at-N/permanent-lower-bound attainment predicate. |
| D07 / C02 | `Results.proposition_3_3` — Results.Overview:58 | ∀L,Q: (∃N∀n≥N,ΔQ_n⊆L)↔(∃N∀n≥N,t_n=1). No generator or finite step bound. |
| D08 / C03 | `Results.theorem_3_5_fixed_pod_endgame` — Results.Overview:89 | ∀K,B,α: (∀s∈Nat,s≥2→α/(2+4/s)≤density_K(B))→α/2≤density_K(B). Same B for all s; α any Real. |
| D09 / C04 | `Results.theorem_4_3` — Results.Overview:68 | ∀K,L,f∃G∀A: Infinite(A.limit)→A.limit⊆L→BoundedBy f A→let Q=generated G A; BoundedBy f Q ∧ R(K,Q.limit)=1 ∧ P(L,Q)=1. |
| D10 / C05 | `Results.lemma_4_5_of_trace_certificate` — Results.Overview:73 | ∀K,L,A,Q,k,cert: ∀α≤R(K,A.limit), α/(k+1)≤R(K,Q.limit) ∧ Novel A Q ∧ P=1 ∧ Qtail=1. cert carries overhead→0/eventual ratio bound plus the last three conclusions. |
| D11 / C06 | `Results.lemma_4_7` — Results.Overview:61 | ∀K,A,B: K.carrier∖A⊆B→1−R⁺(K,A)≤R(K,B). No A⊆K.carrier premise. |
| D12 / C07 | `GeneratorNovel` — Definitions:258 | For fixed G,A and every n≥0, raw G(n+1,history through n+1,generatedStages n) is disjoint from A_(n+1)∪generatedStages n. No progress or all-adversary quantifier. |
| D13 / C07 | `Results.theorem_4_8_of_trace_certificate` — Results.Overview:78 | ∀E,K,L,A,Q: StrictNoveltyCertificate E K L A Q→Novel A Q ∧ P=1 ∧ max(1−R⁺(K,A.limit),R(K,A.limit)/3)≤R(K,Q.limit). |
| D14 / C07 | `Results.theorem_4_9_of_trace_certificate` — Results.Overview:83 | ∀E,γ,K,L,A,Q: GammaNoveltyCertificate E γ L A Q→GammaNovel γ A Q ∧ R(K,Q.limit)=1 ∧ P=1. γ any Real; certificate implies any necessary quota restrictions. |
| D15 / C08 | `Results.gamma_admissible_exploration_exists` — Results.Overview:98 | ∀γ∈Real: γ<1→∃E:ExplorationSet,∀m∈Nat,r_E(m)≤(1−γ)m. Full exploration fields are constructor premises. |
| D16 / C09 | `Results.appendix_valid_generation_without_novelty` — Results.Overview:94 | ∀K,L,f,α,A: Infinite(A.limit)→A.limit⊆L→BoundedBy f A→α≤R(K,A.limit)→let Q=generated parrotGenerator A; BoundedBy f Q ∧ α≤R(K,Q.limit) ∧ P=1 ∧ Qtail=1. |
| D17 / C10 | `Results.appendix_lemma_D_1_of_limit_infinite` — Results.Overview:108 | ∀L,Q: Infinite(Q.limit)→Qtail(L,Q)=1→P(L,Q)=1. No boundedness/attainment requirement. |
| D18 / C10 | `Results.tail_precision_one_finite_guess_counterexample` — Results.Overview:102 | Qtail(∅,oneShotInvalidExhaustion)=1 ∧ P(∅,oneShotInvalidExhaustion)=0; Q_0=∅ and Q_n={0} for every n>0. |

**Certificate scope, checked at constructors.** BatchedPodsCertificate.mk (Certificates:177): choose overhead h→0; eventually a_n≤(k+1)g_n+h_n; Novel(A,Q); P=1; Qtail=1. StrictNoveltyCertificate.mk (:221): sparse subcertificate; Novel; target∖A.limit⊆Q.limit; R(A)/3≤R(Q). GammaNoveltyCertificate.mk (:250): sparse subcertificate; E.GammaAdmissible γ; every-prefix |Q_n∖N_n|≤r(|Q_n|); univ⊆Q.limit. SparseExplorationCertificate.mk (:26): |Q_n|→∞ and every-prefix errors(Q_n)≤r(|Q_n|). These fields are premises, not algorithm conclusions.

## Native support and same-witness checks

- C03: Paper15 PodLimit:98 is the same scalar endgame; GrowingPodRatioCertificate.mk/:alpha_half at156/167 and PodCapacityOneCertificate.mk/:pod_capacity_one_alpha_half at DensityAccounting447/598 remain conditional on quantitative certificates. FiniteScope:151 gives fresh/eventually-valid generation, and Supporting:28 gives eventual validity of algorithmOneWarmupOutput; neither checked interface attaches the half-density certificates to that same output. The source lower/upper theorem pair is therefore still partial.

- C04: NoNoveltyExploration:176 defines the named generator. Its bounds at305, universe coverage at372 and membership precision at689 all name that exact generator; Recall:44 converts coverage to recall1. Thus a genuine same-witness construction exists beyond the existential Overview facade. Native batch:165 allocates crossed quadratic exploration indices and the remaining adversarial increment budget, using finite subset choice at121. It differs from source Algorithm1’s rule; no proof-body or executable-program certification is made.

- C05/C07: searches of every native type mentioning BatchedPodsCertificate, StrictNoveltyCertificate or GammaNoveltyCertificate found only the conditional summaries, structure constructors/projections and eliminators. No checked result produces those certificates from the paper’s k-batched/single-step algorithm inputs. Density dependency searches across P32 and Paper15 yielded 32 non-generated theorem candidates; the decisive lower/upper and certificate candidates were inspected. No source3.6/4.6 or E.1 tightness counterpart was found. This is a census-qualified absence finding.

- C09: NoNovelty:35 states generatedExhaustion parrotGenerator A=A. The exact same witness has f-bound at100, recall equality at92, P=1 at67 and Qtail=1 at80. This strengthens the visible lower-bound dossier and rules out a false claim that the copying construction is absent.

## Source questions and boundaries

1. **Raw output versus new increments:** source Def.3.2/Eq.19 and AppendixD identify raw proposal validity with validity of ΔG. An old invalid string repeated forever distinguishes these under Eq.17. Lean’s incremental predicate agrees with the proof’s intended new-output reading. This needs source/model clarification, not a Lean bug label.

2. **Resolved inventory concern about skip notation:** the frozen inventory tentatively flagged cumulative E_j versus singleton ΔE_j tests in Algorithms6–7. At pointer j, every earlier enumeration element is already in the monotone seen set: A_m∪G_(m−1) in Algorithm6, G_(m−1) in Algorithm7. Thus E_j⊆seen iff ΔE_j⊆seen. The cumulative-prefix notation agrees with the proof’s next-string description; it is not a source error. The frozen inventory is preserved, with this refinement recorded here.

3. **Finite residual in bounded precision proof:** AppendixB.2 permits finite T∖G but later uses enumeration-size equalities. This is a proof-presentation corner, not a finding against the stated equality or reviewed Lean statements.

4. **No false infinity correction:** LemmaD.1 already inherits infinite T,G from §2.2 and explicitly uses infinite G in its proof. D17 makes this explicit. D18 uses finite G and empty target; it is supplementary and does not refute the source.

5. **Early contamination and certificates:** source safe rounds can make finitely many early errors, so its analysis gives r(n)+O(1). The reviewed Strict/Gamma sparse subcertificates have no additive constant and require the bound at every prefix. An initial invalid singleton makes them fail since r(1)=0. Whether the intended completed formalization should use finite-contamination accounting remains a Stage3 question; no certificate-production proof was inspected or assumed.

## Stage1 corrections and coverage checklist

No material error was found in Stage1’s eighteen target reconstructions. The source inventory’s tentative skip-test concern is resolved as described above; no frozen artifact was edited. The native same-witness construction for C04 and trace equality for C09 supplement its target-focused report; they do not identify the unnamed existential D09 witness by theorem name or hidden proof. Stage1 correctly treated C03/C05/C07 as conditional statements.

- Ten frozen source slots and all 18 requested targets accounted for, with grouped source components separated.
- All four partial slots identify their construction and/or upper-bound gaps; absent facades were checked against native support.
- Constants1/2,1/(k+1),1/3, max, γ<1, full/partial adversaries, finite-prefix novelty, liminf/limsup, f-bounds and infinite-limit premises retained.
- Semantic/oracle access, time/history model, cardinality-based statistics, no probability laws, no algorithm rates, named versus existential witnesses and same-witness assembly distinguished.
- Frozen inputs preserved; no mathematical edit, proof audit, compilation, developer explanation or human certification.

Comparison complete. STOP awaiting coordinator comparison freeze before any developer explanation/adjudication.
