# P32 source-first inventory

Source: [exact v1 PDF](https://arxiv.org/pdf/2606.28354v1) and [same-version primary HTML](https://arxiv.org/html/2606.28354v1), Strauss–Butoi–Cotterell, 8 June 2026, 34 pages. Exactly ten claim slots. No source-to-Lean classification has been attempted.

The expected PDF SHA-256 is registry metadata only. No raw PDF bytes or successful formula images were obtained in this run. Six screenshot attempts failed (cache miss, then content-type/transport rejection). Formula interpretation uses exact-v1 HTML mathematical markup checked against PDF extracted text. Printed and one-based PDF page numbers coincide at all cited locations.

## Standing context and notation

**universe.** Finite nonempty alphabet Σ; languages are subsets of Σ*. T and G are infinite after §2.2. In the generation game, the family 𝒯 is countable, every member is infinite, T∈𝒯, A⊆T is infinite (§3, PDF p.5). These are standing assumptions even when not repeated in individual statements.

**exhaustions.** S̲=(S_n): S_0=∅, every S_n finite, S_n⊆S_(n+1), ⋃_n S_n=S. ΔS_n=S_n∖S_(n−1). Enumeration: |ΔS_n|=1 for every n≥1. Single-step: |ΔS_n|≤1, allowing pauses. f-bounded: |ΔS_n|≤f(n), f:ℕ→ℕ₀ with cumulative capacity Σ_(i≤N)f(i)→∞. c-step is the constant bound c. Infinite limit sets ensure denominators are eventually positive; no explicit early 0/0 convention is needed for asymptotic claims.

**metrics.** π_*(T̲,G̲)=liminf |T_n∩G_n|/|G_n|; ρ_*(T̲,G̲)=liminf |T_n∩G_n|/|T_n|. Superscript * replaces liminf by limsup. P(T,G̲):=π̂_*(T,G̲)=sup_(T̲∈E(T))π_*(T̲,G̲). R(T̲,G):=ρ̂_*(T̲,G)=sup_(G̲∈E(G))ρ_*(T̲,G̲). R⁺ uses limsup. Lemmas B.1–B.2 and 2.2/C.1 identify these with membership ratios. Precision counts distinct generated strings; recall depends on the chosen target exhaustion and the final generated set, not synchronized arrival times.

**tail.** t_n=1 when ΔG_n=∅; otherwise t_n=|T∩ΔG_n|/|ΔG_n|. Q(T,G̲):=τ̂_*(T,G̲)=liminf t_n; Q⁺=limsup t_n. Empty steps are perfect, not errors. Q=1 need not be attained for unbounded increments (Example 1, PDF p.5).

**game.** 𝒢:(finite subsets of Σ*)×(finite subsets of Σ*)→(finite subsets of Σ*); G_0=∅ and G_n=G_(n−1)∪𝒢(A_n,G_(n−1)). The generator observes A_n and G_(n−1), with 𝒯 supplied in the background; it is not given the unknown target as an oracle. Def.3.1 requires guarantees for every admissible target and adversary. A full adversary has A=T; a partial adversary has A⊊T.

**novelty.** Strict novelty: 𝒢(A_n,G_(n−1))∩(A_n∪G_(n−1))=∅. N_0=∅; N_n=N_(n−1)∪(ΔG_n∖A_n). γ-novelty: |N_n|/|G_n|≥γ for every nonempty prefix, γ∈[0,1]. A string is counted as novel according to first-generation time, even if revealed later. γ=1 is strict novelty in the intended new-output setting; γ=0 imposes no quota.

**exploration.** R_exp⊂ℕ infinite; 1∉R_exp; no consecutive members; r(m)=|R_exp∩{1,…,m}|; r(m)/m→0. γ-admissibility additionally means r(m)≤(1−γ)m for every m≥1, γ∈[0,1). Main §4 assumes a fixed enumeration T̲ and single-step A̲,G̲, except Theorem4.3 allows f-bounds and Definition4.4 permits k-step adversaries.

**effective semantic status.** No blanket computability, recursive enumerability, membership decision procedure, or complexity bound is assumed for 𝒯, its languages, or adversarial exhaustions. Appendix A, PDF p.12, distinguishes computable exhaustions from arbitrary ones and proves only computable exhaustion⇒r.e. limit. Appendix F supplies a fixed listing of 𝒯 and an enumeration-induced order on Σ*; Algorithms3–5 manipulate complete infinite consistent lists, equality of intersection chains/sets, infinitude, inclusion, and least elements. The safe-generator results therefore provide semantic constructions, or oracle-relative procedures if these operations are supplied; they do not establish unconditional Turing computability from a countable family alone. Copying and sparse exhaustive exploration have an effective description on finite revealed data with computable scheduling/enumeration, without needing a target-membership oracle.

**order strength.** §4 initially says total order; Appendix F fixes an enumeration-induced order. Appendix I.2 explicitly uses finitely many predecessors for every string (PDF p.34). The latter stronger order property belongs to the procedural context.

**locators.** For every cited page ≥2, printed page number equals one-based PDF page; the web parser Pk is zero-based, hence Pk corresponds to PDF/printed page k+1. Source evidence: exact v1 PDF and same-version primary HTML only.

## C01 — claim:sbc26:precision-recall-supremum-characterizations

**Locators:** Theorem 2.1; §2.2; Appendix B.2; printed/PDF pp. 4, 14, 15; Eqs. 9, 49–58 | Lemma 2.2; §2.2; Appendix C.2; printed/PDF pp. 4, 16, 17; Eqs. 12, 71–78 | Definitions and adjacent variants; §2; B.1–B.2; C.1–C.2; printed/PDF pp. 3, 4, 13, 14, 17; Eqs. 3–12, 42, 48, 79, 80.

- Theorem2.1: ∀f:ℕ→ℕ with Σ_(i≤N)f(i)→∞, ∀infinite T,G, ∀G̲∈E_f(G), sup_(T̲∈E_f(T))π_*(T̲,G̲)=liminf_n |T∩G_n|/|G_n|.

- Lemma2.2: ∀infinite T,G, ∀T̲∈E(T), sup_(G̲∈E(G))ρ_*(T̲,G̲)=liminf_n |T_n∩G|/|T_n|.

- Context: B.1/B.2 give unrestricted precision suprema for lower/upper limits; C.1 gives upper recall; C.2 states the bounded recall analogue. These contextual variants are not replacements for the two indexed items.

**Assumptions:** Global universe/exhaustions/metrics; Theorem2.1 specifically writes f:ℕ→ℕ (positive), whereas the preliminary f-bound definition permits ℕ₀. Lemma2.2 does not impose a step bound.

**Context:** The unrestricted proofs choose target/guess exhaustions that include the relevant finite intersection at each time. The bounded precision proof splits bounded versus unbounded cumulative errors; finite T∖G is expressly allowed by footnote4. Examples2–3 show lower and upper limits can differ.

**Effectivity:** Semantic equalities and existential exhaustions; no computable maximizer or oracle-free optimization guarantee.

**Source qualifications:** Do not replace E_f(T) in Theorem2.1 by all exhaustions, or require Lemma2.2’s optimizing exhaustion to be f-bounded. The source states upper analogues separately. Bounded-proof cardinality equalities use enumeration notation even when the footnote allows a finite residual language; the stated claim is retained without silently adding an infinite-residual hypothesis.

**Formula verification:** Exact-version primary HTML mathematical markup cross-checked against PDF extracted text; no successful visual image.

## C02 — claim:sbc26:tail-precision-attainment-and-validity

**Locators:** Proposition 2.4; §2.2; Appendix D; printed/PDF pp. 4, 18; Eqs. 13–15, 81–85 | Proposition 3.3 / Definition 3.2; §3.1; Appendix D; printed/PDF pp. 5, 6, 18, 19; Eqs. 19, 86–88.

- Single-step G̲ ⇒ Q(T,G̲)∈{0,1}.

- c-step G̲, c≥1 ⇒ ℓ:=Q(T,G̲) lies in {i/j:1≤j≤c,0≤i≤j}; ∃n, t_n=ℓ ∧ ∀N≥n, t_N≥ℓ. The minimizing recurrent value occurs infinitely often.

- Proposition3.3 claims eventual validity ⇔ Q=1 attained in finite time; for value1 this means ∃n₀∀n≥n₀,t_n=1. Def.3.2 writes eventual validity as ∃n₀∀n≥n₀,𝒢(A_n,G_(n−1))⊆T.

**Assumptions:** Global tail/game conventions. Finite c is essential for attainment. Proposition3.3 concerns the generated exhaustion against the specified adversarial run and has no stated bounded-step hypothesis.

**Context:** The footnote defines attainment by one occurrence and a subsequent lower bound, not eventual constancy at arbitrary ℓ. Example1 gives t_n=(n−1)/n with one error per round and Q=1 never reached.

**Effectivity:** Semantic finite-range and finite-error statements; no effective stopping-time bound.

**Source qualifications:** Attainment at ℓ<1 does not assert t_n eventually equals ℓ. Source-internal output ambiguity: Eq.17 permits re-outputting old elements, but Def.3.2/Proposition3.3 equate raw output validity, finite G∖T, and eventual ΔG_n⊆T. Those equivalences require treating outputs as newly added strings or excluding perpetual repeats of an old invalid string. Record the literal raw-output definition and intended incremental reading separately.

**Formula verification:** Exact-version primary HTML mathematical markup cross-checked against PDF extracted text; no successful visual image.

## C03 — claim:sbc26:restated-half-density-bounds

**Locators:** Theorems 3.5 and 3.6; §3.2; printed/PDF pp. 6; Eqs. 20–22 | Safe generator context; Appendix F; Algorithms2–5; printed/PDF pp. 22, 23, 24, 25.

- Theorem3.5: for a countable family of infinite languages and fixed target enumeration T̲, a novel generator achieves Q=1 and, for every single-step A̲↑A⊆T, produces single-step G̲ with R(T̲,G)≥R(T̲,A)/2. P=1 follows from D.1; Q=1 is attained by Proposition2.4.

- Theorem3.6 as printed: ∀novel generator, ∃countable family 𝒯, target T∈𝒯, target enumeration T̲ and single-step A̲↑A⊆T such that, if the generated exhaustion is single-step, R(T̲,G)≤R(T̲,A)/2.

**Assumptions:** Global countable infinite family, infinite A, fixed T̲, strict novelty, single-step input/output. Theorem3.5 requires perfect tail precision. Theorem3.6’s printed statement does not separately repeat that restriction.

**Context:** Both are attributed restatements: Kleinberg–Wei2025b Theorems3.5 and3.3 respectively. This source gives no independent proof of the restated upper result. Full adversarial revelation makes R(T̲,A)=1.

**Effectivity:** Semantic safe generator using the Appendix F operations; no general computability assumption. The upper statement is a worst-case obstruction, not a fixed-instance bound.

**Source qualifications:** Retain the existence/for-every-adversary direction of the lower result and the worst-case existential instance in the upper result. Do not silently insert a perfect-tail hypothesis into the literal Theorem3.6 restatement or omit its single-step output proviso. No other edition of the cited prior paper was consulted.

**Formula verification:** Exact-version primary HTML mathematical markup cross-checked against PDF extracted text; no successful visual image.

## C04 — claim:sbc26:theorem-4-3-no-novelty

**Locators:** Theorem 4.3; §4.1; Appendix E.2; printed/PDF pp. 7, 8, 21; Eqs. 26, 104–107 | Algorithm 1 / exploration definition; Definition4.1; Appendix E.2; printed/PDF pp. 7, 21.

- For any countable family of infinite languages and target T with fixed enumeration T̲, ∃generator ∀f-bounded A̲↑A⊆T with infinite A, the induced G̲ is f-bounded and R(T̲,G)=P(T,G̲)=1.

- Construction: initialize with A₁; otherwise copy ΔA; at sparsely triggered output-cardinality thresholds substitute one next ambient-enumeration element, only when a nonempty new adversarial batch supplies at least one unit of capacity. Proof gives G=Σ*.

**Assumptions:** Global universe, infinite target/adversarial/guess limits; f:ℕ→ℕ₀, unbounded cumulative capacity; no novelty quota; no perfect-tail requirement; full or partial A allowed.

**Context:** Exploration is scheduled by |G_n| reaching successive R_exp values, not by a fixed fraction of clock rounds. Error count is bounded by r(|G_n|), giving P=1 while all ambient strings are eventually explored.

**Effectivity:** Effective finite-data copying/exploration for computable ambient enumeration and sparse schedule; no access to target membership or candidate-family decisions is needed by Algorithm1. Arbitrary inputs themselves need not be computable.

**Source qualifications:** Recall1 means membership coverage and is compatible with G=Σ*, not equality G=T. Infinite A is a standing assumption omitted in the local theorem sentence. A generator need not have Q=1; this theorem does not assert a value for Q.

**Formula verification:** Exact-version primary HTML mathematical markup cross-checked against PDF extracted text; no successful visual image.

## C05 — claim:sbc26:k-batched-density-bounds

**Locators:** Lemma 4.5; §4.2; Appendix G.1; printed/PDF pp. 8, 9, 24, 25, 26, 27; Eqs. 27a–27b, 111–124 | Lemma 4.6; §4.2; Appendix G.2; printed/PDF pp. 9, 27, 28; Eqs. 28, 125–129 | Definitions / procedures; Definition4.4; Appendix F; Algorithms2–5; printed/PDF pp. 8, 22, 23, 24, 25.

- Lower: k∈ℕ, k≥2; k-step A̲↑A⊆T; Algorithm2 with growing pod sizes (e.g. s_n=n) produces novel single-step G̲ with R(T̲,G)≥R(T̲,A)/(k+1), P=Q=1.

- Upper: in the k-batched setting, a countable family admits a worst-case target and k-step adversarial exhaustion for which every eligible novel single-step generator that guarantees Q=1 across the family has R(T̲,G)≤R(T̲,A)/(k+1). The adversarial run may depend on the generator.

- The upper proof treats full A=T first, then a family containing both A and T. Indistinguishability plus the Q=1 requirement for target A forces only finitely many outputs outside A.

**Assumptions:** Global infinite languages, countable family, infinite A, fixed enumeration T̲; k-batched means input ≤k new strings/round and output ≤1. Lower lemma explicitly k≥2. Upper lemma does not repeat that bound; the natural k≥1 case includes the single-step factor1/2. Perfect-tail success for all possible targets is used in the partial upper proof.

**Context:** Appendix F fixes a family listing, enumeration-induced order, consistent intersection chains, identified/aggressive intersections, and a pod pool. G.1 charges missed revealed strings to growing pods with multiplicity≤k; G.2 reveals least unused strings with sparse repetition steps. Finite pre-stabilization errors do not change density.

**Effectivity:** Lower is a semantic/oracle safe procedure with infinite-set tests, not a Turing algorithm from countability alone. Upper is worst-case, requiring family-wide correctness for the partial indistinguishability step.

**Source qualifications:** The local upper statement compresses quantifiers; G.2 clarifies adversarial strategy depends on the chosen generator and partial-instance reasoning uses success on both A and T, not merely Q=1 on the T-run. The main lower sketch writes an O(n) remainder; the appendix uses fixed-parameter O(kN+ks) and then s→∞. The inventory uses the complete stated guarantees, not a stronger uniform instance quantification.

**Formula verification:** Exact-version primary HTML mathematical markup cross-checked against PDF extracted text; no successful visual image.

## C06 — claim:sbc26:lemma-4-7-complement-recall

**Locators:** Lemma 4.7 with proof; §4.2; printed/PDF pp. 9; Eqs. 29–31b.

- T∖A⊆G ⇒ R(T̲,G)≥1−R⁺(T̲,A). Consequently R⁺(T̲,A)≤β ⇒ R(T̲,G)≥1−β.

**Assumptions:** Global infinite T,G and fixed target exhaustion (an enumeration in §4); A⊆T is the adversarial limit. Every x∈T∖A is generated at some x-dependent finite time. No common finishing time, precision, novelty, computability, or batch hypothesis is needed for the set inequality.

**Context:** The finite-prefix inequality is |G∩T_n|/|T_n|≥1−|A∩T_n|/|T_n|. Taking liminf changes the subtracted quantity to limsup.

**Effectivity:** Pure set/density implication; the inclusion is a premise, not an effective discovery algorithm.

**Source qualifications:** The adversarial measure is upper recall. Replacing it by lower recall changes the claim. Coverage is eventual pointwise inclusion, not completion of an infinite complement in one finite round.

**Formula verification:** Exact-version primary HTML mathematical markup cross-checked against PDF extracted text; no successful visual image.

## C07 — claim:sbc26:novelty-generation-tradeoffs

**Locators:** Theorem 4.8; §4.2; Appendix H.1; Algorithm6; printed/PDF pp. 10, 29, 30; Eqs. 32, 130–136 | Theorem 4.9; §4.3; Appendix I.1; Algorithm7; printed/PDF pp. 10, 31, 32; Eqs. 33, 138–140 | Corollary I.2 (indexed following corollary); Appendix I.1; printed/PDF pp. 31; Eqs. 141 | Adjacent perfect-tail context, not the indexed following corollary; Appendix I.2; Theorem I.3 / Corollary I.4; Algorithm8; printed/PDF pp. 32, 33, 34; Eqs. 142–148.

- Theorem4.8: Algorithm6, for every target T and single-step A̲↑A⊆T, gives novel single-step G̲ with P=1 and R(T̲,G)≥max{1−R⁺(T̲,A), R(T̲,A)/3}.

- Theorem4.9: ∀γ∈[0,1), Algorithm7, for every target and single-step full or partial A̲, gives γ-novel single-step G̲ with R=P=1.

- CorollaryI.2: same Algorithm7 and γ∈[0,1), specialized to A=T, still R=P=1; no perfect-tail conclusion.

- Related context: TheoremI.3 instead interleaves safe/repetition rounds with L=ceil(1/(1−γ)), recovers every revealed point, gives R≥α when R(T̲,A)≥α, P=Q=1, and a tightness clause. CorollaryI.4 specializes that different result to full A=T and obtains R=P=Q=1.

**Assumptions:** Global countable infinite family, infinite A,T,G and fixed T̲; single-step adversary/output. Algorithm6 uses an exploration set; Algorithm7 a γ-admissible set. Both use an ambient enumeration, growing pod sizes and the semantic safe routine. γ=1 is excluded from Theorem4.9.

**Context:** No adjacent exploration times means the safe routine sees at most two adversarial revelations per invocation. Algorithm6 explores ambient strings not yet seen by either player, hence covers T∖A; safe rounds supply the 1/3 term. These contributions can overlap, so the bound is a maximum. Algorithm7 permits previously revealed strings during exploration but excludes already generated strings; G=Σ* and every prefix satisfies the novelty quota. Sparse exploration leaves at most r(n)+O(1) invalid outputs among n distinct outputs.

**Effectivity:** Semantic/oracle safe generator, with explicit sparse enumeration/repetition schedules; no general computability theorem for arbitrary countable 𝒯.

**Source qualifications:** The indexed corollary following4.9 is CorollaryI.2, Eq.141, not I.4. I.4 belongs to the separate perfect-tail TheoremI.3. Neither4.8 nor4.9 requires or guarantees Q=1; do not infer additive recall, γ=1 coverage, or a target-membership oracle. Algorithms6–7 write a skip condition with cumulative E_j whereas proofs describe skipping ΔE_j (the individual next string); retain this pseudocode/prose discrepancy rather than silently resolving it.

**Formula verification:** Exact-version primary HTML mathematical markup cross-checked against PDF extracted text; no successful visual image.

## C08 — claim:sbc26:gamma-admissible-exploration-exists

**Locators:** Lemma I.1; Appendix I; printed/PDF pp. 30; Eqs. 137 | Definitions 4.1 and 4.2; §4; printed/PDF pp. 7.

- ∀γ∈[0,1), ∃γ-admissible exploration set R_exp. Explicitly choose integer M≥max{2,ceil(1/(1−γ))}, set R_exp={M·2^i:i∈ℕ₀}; then ∀m≥1, r(m)≤m/M≤(1−γ)m, r(m)/m→0, R_exp is infinite, 1∉R_exp, and it has no consecutive members.

**Assumptions:** Definition4.2 gives γ∈[0,1). The lemma sentence abbreviates this as γ<1. M is a positive integer (required for R_exp⊂ℕ).

**Context:** The set is a scaled powers-of-two sequence, M·2^i, not M^(2^i) or M·2i. Both asymptotic sparsity and a quota in every finite prefix are required.

**Effectivity:** Explicit arithmetic construction; a schedule is computable once a suitable integer M is supplied. No uniform procedure for obtaining such M from an arbitrary representation of a real γ is specified.

**Source qualifications:** Do not omit 1∉R_exp, nonconsecutivity, infinitude, or the asymptotic sparsity inherited from Definition4.1. Do not extend to γ=1, when finite-prefix quota would force r(m)=0.

**Formula verification:** Exact-version primary HTML mathematical markup cross-checked against PDF extracted text; no successful visual image.

## C09 — claim:sbc26:appendix-parrot-baseline

**Locators:** Theorem E.1; Appendix E.1; printed/PDF pp. 20; Eqs. 97–103.

- ∀countable infinite-language family, target T and fixed T̲, ∃generator ∀f-bounded A̲↑A⊆T with R(T̲,A)≥α, induced G̲ is f-bounded and R(T̲,G)≥α, P=Q=1.

- Copying witness: G_n=A_n, ΔG_n=ΔA_n, G=A. Thus exact equality R(T̲,G)=R(T̲,A), with all outputs valid from the start.

- The theorem also claims adversarial tightness for c-step outputs: choose an infinite strict sublanguage A⊊T with R(T̲,A)=α<1 and a family containing both; a generator with perfect tail precision for every possible true language cannot guarantee recall above α on this indistinguishable reveal stream.

**Assumptions:** Global infinite A,T,G; no novelty requirement; f-bound for the constructive statement. Tightness uses finite constant output bound c and family-wide perfect-tail correctness, not arbitrary unbounded f.

**Context:** The finite range of c-step t_n forces eventual validity relative to target A. The same observed history for target A or T then permits only finitely many generated points outside A, proving the obstruction.

**Effectivity:** Copying has an effective description on finite revealed sets, without target oracle. The tightness argument is semantic indistinguishability.

**Source qualifications:** The tightness clause is part of the indexed theorem and must not be dropped. Eq.98 writes the raw copying output as ΔA_n, which is historical notation; for new increments an equivalent finite-data witness is A_n∖G_(n−1) along the copying run. Copying adversarial strings violates strict novelty whenever it adds a point.

**Formula verification:** Exact-version primary HTML mathematical markup cross-checked against PDF extracted text; no successful visual image.

## C10 — claim:sbc26:tail-precision-implies-precision

**Locators:** Lemma D.1; Appendix D; printed/PDF pp. 19; Eqs. 89–96.

- For any exhaustion G̲↑G with infinite G, Q(T,G̲)=1 ⇒ P(T,G̲)=1; equivalently the cumulative membership ratio converges to1. No fixed step bound or finite-time attainment is required.

**Assumptions:** Global infinite T,G; finite monotone prefixes and disjoint increments; empty-step t_n=1. |G_n|→∞ is used explicitly. No novelty or adversary premise.

**Context:** With s_n=|ΔG_n|, e_n=|ΔG_n∖T|, eventual e_n≤εs_n implies |G_n∖T|≤C+ε|G_n|. Divide by |G_n| and let ε→0.

**Effectivity:** Semantic weighted cumulative-error estimate; no stopping-time or computability guarantee.

**Source qualifications:** The infinite-G hypothesis is inherited from §2.2 and explicitly invoked in the proof. Finite G could retain an early invalid point despite all later empty steps having t_n=1. At s_n=0, e_n/s_n is shorthand only; use e_n=0 and the inequality e_n≤εs_n.

**Formula verification:** Exact-version primary HTML mathematical markup cross-checked against PDF extracted text; no successful visual image.

## Freeze boundary

Inventory complete for C01–C10. Stop here. Await coordinator freeze and explicit authorization before consulting Stage1, interfaces, Lean, or any comparison context.
