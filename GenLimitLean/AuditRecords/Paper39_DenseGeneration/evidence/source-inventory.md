# P39 independent source inventory

Completed 2026-11-14T06:46:46.906859+00:00. Exactly 44 source slots across three separate editions. This file records source meaning only; no Lean or Stage 1 comparison has occurred.

All source statements were read with their relevant model, definitions and proofs, including v1 Appendices A–D and v2 Appendices A–E where needed. Local decisive pages were visually checked. V1 mathematical text is available, but raw-byte and visual verification remain qualified as described below.

## Source editions and access

- **earlier-supplied-manuscript**: 53 PDF pages. Raw PDF hash verified: True. Expected SHA-256: `1a9a81a7aa02719f5cfe852746f3db853d47d42f699e8f62cc78f451ef7cb23e`.
- **arxiv-2608-01320-v1**: 54 PDF pages. Raw PDF hash verified: False. Expected SHA-256: `295b7ea54afd3859c4ff3baef4cf8e1e655824f3efd240699d7df429cf68b676`.
  Primary source: [exact v1 PDF](https://arxiv.org/pdf/2608.01320v1); supplement: [same-version author HTML](https://arxiv.org/html/2608.01320v1).
- **arxiv-2608-01320-v2**: 60 PDF pages. Raw PDF hash verified: True. Expected SHA-256: `8dfc7ada39b62bb79d380331deeb4377035ec35d26b8334c2c6c6a91cb711b08`.

Printed-page numbers below are the author’s page labels; PDF page numbers are one-based. The claim index was used only as a locator. In particular, several v1 claims occur one printed page later than the index suggests.

## Standing assumptions by edition

### earlier-supplied-manuscript

Section 2, printed 6–7 / PDF 8–9; Section 3.1, printed 9–12 / PDF 11–14.

- Universe is the positive integers with its usual order. Every candidate language is infinite. The indexed family X={L_1,L_2,...} is countable and fully accessible to both players.
- The author explicitly gives both players a membership oracle taking (x,i) and deciding x∈L_i.
- An unknown target K=L_i* is fixed. At each positive round the adversary announces an element of K, then the generator announces one positive integer. Every element of K must eventually occur in the adversary stream. Repetitions are not explicitly forbidden in this edition.
- Unless a setting changes this explicitly, the generator is deterministic and the adversary may depend on previous outputs.
- Eventual validity means there exists a play-dependent finite t0 such that every output from t0 onward lies in K and is new relative to both players. No uniform or computable t0 is specified.

**Criticality:** Recursive: a consistent L_i is critical exactly when it is contained in every earlier critical language. The first critical language is the least-indexed consistent language.

**Access/effectivity:** The membership oracle is explicit, but criticality uses exact inclusion between infinite languages. The cited descriptions do not supply an effective reduction of those inclusion tests to membership queries, or a time bound. The mathematical guarantees are semantic under the described language access.

### arxiv-2608-01320-v1

Section 2, printed 7–8 / PDF 9–10; Section 3.1, printed 10–12 / PDF 12–14.

- Universe is the positive integers; all candidate languages are infinite. The indexed countable family L={L_1,L_2,...} is fully accessible to both players. The cited model does not specify a representation or an explicit membership-oracle interface.
- The adversary fixes K=L_i* and announces an element of K before the generator responds with one positive integer each round. Every element of K must occur at some finite adversary round. This edition does not explicitly prohibit repeated adversary values.
- The default generator is deterministic and the adversary may be adaptive.
- Eventual validity requires a finite, adversary-dependent threshold after which every output is in K and has not previously been announced by either player.

**Criticality:** All-earlier-consistent: L_i is critical iff it is consistent and L_i⊆L_j for every consistent j<i. This is the literal v1 Definition 3.2, independently confirmed in the same-version author HTML.

**Access/effectivity:** The family is fully accessible, and algorithms use exact inclusion/criticality. No effective presentation, computable convergence bound, or running-time bound is part of the cited theorem context. Semantic guarantees must be kept distinct from an implementation using a specified finite interface.

### arxiv-2608-01320-v2

Section 2, printed 6–8 / PDF 8–10; Section 3.1, printed 9–12 / PDF 11–14.

- Universe is the positive integers. All candidate languages are infinite. The countable indexed family L={L_1,L_2,...} is fully accessible to both players. The cited model does not specify an effective representation or explicit membership-oracle interface.
- An unknown K=L_i★ is chosen. Each round the adversary announces one element of K, then the generator responds with one positive integer. The adversary must announce every element of K exactly once: this edition explicitly requires enumeration without repetition.
- The generator is deterministic and the adversary may be adaptive unless a later setting says otherwise.
- Eventual validity means a finite play-dependent threshold after which all outputs are in K and new relative to either player. No effective threshold is asserted.

**Criticality:** Recursive: begin with the least-indexed consistent language; thereafter a consistent L_i is critical iff it is contained in every earlier critical L_j. The footnote and Remark 3.7 explicitly distinguish this from the all-earlier-consistent definition.

**Access/effectivity:** Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

## Definitions used by the slot records

- **ownership_density**: A is the set of values whose first announcement belongs to the adversary; D is the set whose first announcement belongs to the generator. The adversary moves first each round. μ_n(S)=|S∩{1,...,n}|. Under full enumeration, A and D∩K partition K. The density is liminf_n μ_n(D∩K)/μ_n(K). Infinite K makes the denominator eventually positive and unbounded.
- **consistency_scope_focus**: Consistency at a round means containing every adversary value observed so far, including the current announcement when updated. The scope of size s is the first s candidate indices. The focus is the highest-indexed critical language in that scope.
- **switch_loss**: An adversary value is a switch loss when it is outside the focus at the end of the preceding round. Its arrival falsifies that old focus. Being a switch loss does not itself require first ownership by the adversary; charging bounds restrict to previously unannounced losses.
- **patient_schedule**: Start s_0=1 and τ=1. Retain scope between rounds. After an adversary announcement update consistency and criticality. Falsification invokes backtracking and increments τ. Otherwise, after 2^τ preceding steps with unchanged focus, expand scope by one; increment τ if that expansion changes focus. Output the least integer in the resulting focus not announced by either player. Backtracking, when no consistent language is in scope, expands to find one; otherwise truncate to the greatest old critical index still critical, or the least consistent index if no old critical one survives.
- **target_normalization**: After eventual focus containment in K is established, the density proofs identify the ordered target with the positive integers by target rank. In that analysis [n] denotes the first n target elements; finitely many early announcements are absorbed in a fixed constant. This is an analysis normalization, not knowledge of K given to the generator.
- **partial_closure**: Partial enumeration replaces coverage of K by coverage of an infinite K′⊆K; K′ need not be a candidate. Density remains relative to K. The transformed family lists intersections over nonempty finite sets I of original indices, in binary indicator order: code(I)=Σ_{i∈I}2^(i−1), and L′_I=⋂_{i∈I}L_i. The source discards finite intersections, or assumes all displayed transformed languages infinite for exposition.
- **random_density**: The adversary is oblivious: its deterministic target enumeration is fixed before the generator random choices. Randomness is in independent uniform permutations of finite blocks/groups. Density is liminf_n E[μ_n(D∩K)]/μ_n(K); the expectation is inside the liminf. This is an expected coverage guarantee, not an asserted almost-sure density theorem.
- **blocks**: A reserved integer lies in one of the disjoint finite blocks. W contains integers neither announced by either player nor reserved. A newly announced unreserved adversary integer triggers a new block; associate it with that block, giving C_r=B_r plus its trigger when present. Completeness under an order concerns inclusion of a block or its designated initial head in the target prefix.
- **multi_order_v1**: Fix a positive finite k and k permutations σ_i of the positive integers, interpreted as element-to-rank maps: [n]_i=σ_i^(-1)({1,...,n}). Set μ_i,n(S)=|S∩[n]_i|. Deterministic density is min_i liminf_n μ_i,n(D∩K)/μ_i,n(K); randomized density puts E around the numerator inside each liminf. The same generator serves every order.
- **multi_order_v2**: Fix a positive finite k and k bijections σ_i of the positive integers, interpreted as rank-to-element enumerations: [n]_i=σ_i({1,...,n}). Set μ_i,n(S)=|S∩[n]_i|. The guarantee is min_i of the target-relative liminf, with expectation in each numerator for the randomized setting. A single generator serves all k orders.
- **auxiliary_tools**: The block arguments use f(m)=1−(1−1/(m+1))^m from Ranking for online matching, with f(m)→1−1/e, and finite low-crossing partitions into groups of size s, with crossing count ≤4(m/s)^(1−1/k). The latter construction is proved in the edition’s Appendix A.

## Slots

### C01 — Earlier-manuscript patient-scope algorithm

Edition: **earlier-supplied-manuscript**. Section 3.2, patient-scope and backtracking boxes. Printed 13; PDF pages 15.

Start s_0=1 and τ=1. Retain scope between rounds. After an adversary announcement update consistency and criticality. Falsification invokes backtracking and increments τ. Otherwise, after 2^τ preceding steps with unchanged focus, expand scope by one; increment τ if that expansion changes focus. Output the least integer in the resulting focus not announced by either player. Backtracking, when no consistent language is in scope, expands to find one; otherwise truncate to the greatest old critical index still critical, or the least consistent index if no old critical one survives.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus, patient_schedule.

Scope: Initialization, round update order, exponential wait, scope expansion, output minimum, and all backtracking branches are in scope.

Guarantee/access: The membership oracle is explicit, but criticality uses exact inclusion between infinite languages. The cited descriptions do not supply an effective reduction of those inclusion tests to membership queries, or a time bound. The mathematical guarantees are semantic under the described language access.

Proof context: Criticality is the recursive Definition 3.2 on printed 9–10 / PDF 11–12; scope and focus are Definitions 3.5–3.6.

Source ambiguity or qualification:
- The preceding 2^τ steps are described in prose; no separate endpoint convention or machine state specification is supplied. Exact inclusion remains a semantic operation despite the supplied membership oracle.

Visual checks: [page_15.png](visual-checks/earlier/page_15.png).

### C02 — Target-relative lower density

Edition: **earlier-supplied-manuscript**. Definition 2.2 and surrounding ownership notation. Printed 7; PDF pages 9.

Lower density is liminf_n |D∩K∩[n]|/|K∩[n]|. It measures ownership within the target, equivalently the liminf fraction in its first m ordered elements.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.

Definitions: ownership_density.

Scope: Definition and the ownership partition used by later proofs.

Guarantee/access: Semantic asymptotic definition; no algorithm-existence or effectivity assertion by itself.

Source ambiguity or qualification:
- Early ambient prefixes can have zero denominator; the asymptotic ratio is taken where it is positive.

Visual checks: [page_9.png](visual-checks/earlier/page_9.png).

### C03 — No deterministic algorithm can guarantee lower density above one half

Edition: **earlier-supplied-manuscript**. Paragraph following Definition 2.2. Printed 7; PDF pages 9.

No deterministic generator has a worst-case lower-density guarantee strictly above 1/2; the text supports this by an adversary selecting the least as-yet unannounced target element.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.

Definitions: ownership_density.

Scope: Worst-case upper bound, including a generator that knows K.

Guarantee/access: Semantic impossibility claim about all deterministic strategies; no complexity assumption.

Source ambiguity or qualification:
- The proposed least-free rule alone need not enumerate target elements already first announced by the generator. This edition does not state catch-up rounds in this paragraph, even though full adversary enumeration is a standing assumption.

Visual checks: [page_9.png](visual-checks/earlier/page_9.png).

### C04 — Earlier-manuscript recursive criticality

Edition: **earlier-supplied-manuscript**. Definition 3.2, footnote 1, Remark 3.3, Definitions 3.5–3.6. Printed 9–10; PDF pages 11, 12.

Recursive: a consistent L_i is critical exactly when it is contained in every earlier critical language. The first critical language is the least-indexed consistent language.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus.

Scope: Recursive definition, least-consistent base case, descending inclusion chain, scope and focus needed to apply it.

Guarantee/access: Semantic inductive definition in index order, using exact language inclusion.

Source ambiguity or qualification:
- The footnote explicitly changes the earlier-consistent-language definition of KM to the recursive earlier-critical-language definition.

Visual checks: [page_11.png](visual-checks/earlier/page_11.png), [page_12.png](visual-checks/earlier/page_12.png).

### C05 — Public-v1 criticality by all earlier consistent languages

Edition: **arxiv-2608-01320-v1**. Definition 3.2, Remark 3.3, Definitions 3.5–3.6. Printed 10; PDF pages 12.

All-earlier-consistent: L_i is critical iff it is consistent and L_i⊆L_j for every consistent j<i. This is the literal v1 Definition 3.2, independently confirmed in the same-version author HTML.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus.

Scope: All earlier consistent indices, together with focus and chain terminology.

Guarantee/access: Semantic predicate requiring exact inclusion, not an effective membership test.

Proof context: Author HTML Section 3.1 independently displays the same all-consistent quantifier.

Source ambiguity or qualification:
- Literal v1 criticality quantifies over all earlier consistent languages; later chain-dynamics and charging prose must be read with that edition-specific definition. It is not silently replaced by recursive criticality.
- Remark 3.3 additionally asserts suffix removal and placement of new critical languages after all survivors; the definition and the asserted dynamics should both be retained for later source comparison.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C06 — Earlier-manuscript validity of the patient-scope algorithm

Edition: **earlier-supplied-manuscript**. Lemma 3.11 and its proof. Printed 14; PDF pages 16.

For every target and permitted full enumeration, patient-scope eventually produces only target elements fresh relative to both players. The proof obtains permanent criticality and eventual permanent inclusion of the target index in scope, hence eventual focus containment F⊆K.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus, patient_schedule.

Scope: Eventual target membership and novelty; the proof’s stronger eventual focus containment is relevant.

Guarantee/access: The membership oracle is explicit, but criticality uses exact inclusion between infinite languages. The cited descriptions do not supply an effective reduction of those inclusion tests to membership queries, or a time bound. The mathematical guarantees are semantic under the described language access.

Proof context: Uses Lemma 3.4 (printed 10 / PDF 12) and finiteness of earlier indices, whose non-superset languages are eventually falsified.

Visual checks: [page_16.png](visual-checks/earlier/page_16.png).

### C07 — Public-v1 validity of the patient-scope algorithm

Edition: **arxiv-2608-01320-v1**. Lemma 3.11 and proof across page break. Printed 14–15; PDF pages 16, 17.

The v1 patient-scope algorithm is asserted to generate K in the limit: all sufficiently late outputs are in K and fresh. The proof uses eventual criticality of K and eventual permanent scope size at least its index.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus, patient_schedule.

Scope: Validity and proof-derived eventual focus containment, using v1 criticality.

Guarantee/access: The family is fully accessible, and algorithms use exact inclusion/criticality. No effective presentation, computable convergence bound, or running-time bound is part of the cited theorem context. Semantic guarantees must be kept distinct from an implementation using a specified finite interface.

Proof context: Lemma 3.4 appears on printed 10 / PDF 12; the algorithm boxes are printed 13 / PDF 15.

Source ambiguity or qualification:
- Literal v1 criticality quantifies over all earlier consistent languages; later chain-dynamics and charging prose must be read with that edition-specific definition. It is not silently replaced by recursive criticality.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C08 — Earlier-manuscript non-switch comparison with derived partner support

Edition: **earlier-supplied-manuscript**. Fact 3.12; Fact 3.10 proof and Theorem 3.14 proof. Printed 14–16; PDF pages 16, 17, 18.

If at round t>1 an adversary-first value a_t is not a switch loss, then a_t∈F_(t−1) and d_(t−1)≤a_t. Freshness makes the values distinct. Once the preceding focus lies in K, this supplies a smaller generator-owned value in K; different such t have different partners.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.
- There is a preceding round and its generator output. For target-supported partners the preceding focus must already be contained in K.

Definitions: switch_loss, patient_schedule, target_normalization.

Scope: The fact’s old-focus membership and numerical comparison, plus the partner’s support/ownership and injectivity used in the density proof.

Guarantee/access: The membership oracle is explicit, but criticality uses exact inclusion between infinite languages. The cited descriptions do not supply an effective reduction of those inclusion tests to membership queries, or a time bound. The mathematical guarantees are semantic under the described language access.

Source ambiguity or qualification:
- The fact states the non-strict inequality; strictness and target membership of the partner require novelty and eventual validity context.

Visual checks: [page_16.png](visual-checks/earlier/page_16.png), [page_17.png](visual-checks/earlier/page_17.png), [page_18.png](visual-checks/earlier/page_18.png).

### C09 — Public-v1 non-switch announcement comparison

Edition: **arxiv-2608-01320-v1**. Fact 3.12; analogous Fact 3.10 proof. Printed 15; PDF pages 17.

For an adversary-first announcement a_t at t>1 that is not a switch loss, a_t belongs to the preceding focus and is at least the preceding patient-scope output d_(t−1).

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.
- A preceding round/output exists.

Definitions: switch_loss, patient_schedule.

Scope: Both membership in the old focus and comparison with the previous output.

Guarantee/access: The family is fully accessible, and algorithms use exact inclusion/criticality. No effective presentation, computable convergence bound, or running-time bound is part of the cited theorem context. Semantic guarantees must be kept distinct from an implementation using a specified finite interface.

Proof context: Fact 3.10 and proof: printed 12 / PDF 14; the density proof later uses distinct valid partners.

Source ambiguity or qualification:
- The source gives an omitted-proof reference to Fact 3.10; target membership of d_(t−1) comes from eventual focus containment rather than this fact alone.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C10 — Earlier-manuscript logarithmic charging bound for switch losses

Edition: **earlier-supplied-manuscript**. Lemma 3.13 and Figure 4 charging proof. Printed 15–16; PDF pages 17, 18.

After the eventual generation regime, the number w of previously unannounced switch-loss values in a target-rank prefix [n] is at most log_2 n. Each loss is charged a disjoint block of 2^τ_j smaller generator outputs, with distinct positive τ_j; n≥Σ_j2^τ_j≥2^w.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.

Definitions: switch_loss, patient_schedule, target_normalization.

Scope: Logarithmic loss bound and its disjoint exponential-charge mechanism.

Guarantee/access: The membership oracle is explicit, but criticality uses exact inclusion between infinite languages. The cited descriptions do not supply an effective reduction of those inclusion tests to membership queries, or a time bound. The mathematical guarantees are semantic under the described language access.

Source ambiguity or qualification:
- The phrase describing when generation starts is not a named exact round boundary in this edition. The proof uses eventual focus containment in K and the preceding-round output, so a finite initial exception may need to include the adjacent round.
- The proof asserts that the returning focus contains the loss and that the associated waiting interval occurred earlier; these are algorithm-history facts, not freestanding numerical hypotheses in the lemma.

Visual checks: [page_17.png](visual-checks/earlier/page_17.png), [page_18.png](visual-checks/earlier/page_18.png).

### C11 — Public-v1 logarithmic charging bound for switch losses

Edition: **arxiv-2608-01320-v1**. Lemma 3.13 and charging proof. Printed 15–16; PDF pages 17, 18.

The source asserts at most log_2 n previously unannounced switch-loss values in each normalized target prefix after eventual generation. Its proof charges distinct exponential waiting periods, obtaining n≥Σ_j2^τ_j≥2^w.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Definitions: switch_loss, patient_schedule, target_normalization.

Scope: Loss bound and source’s history-based charging support.

Guarantee/access: The family is fully accessible, and algorithms use exact inclusion/criticality. No effective presentation, computable convergence bound, or running-time bound is part of the cited theorem context. Semantic guarantees must be kept distinct from an implementation using a specified finite interface.

Proof context: The source uses i<j and L_j⊆L_i⊆K for a backtrack, and says the loss lies in L_i so all charged outputs are smaller.

Source ambiguity or qualification:
- Literal v1 criticality quantifies over all earlier consistent languages; later chain-dynamics and charging prose must be read with that edition-specific definition. It is not silently replaced by recursive criticality.
- The phrase describing when generation starts is not a named exact round boundary in this edition. The proof uses eventual focus containment in K and the preceding-round output, so a finite initial exception may need to include the adjacent round.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C12 — Earlier-manuscript deterministic 1/2 lower-density achievability

Edition: **earlier-supplied-manuscript**. Theorem 3.14 and proof; Section 2 upper-bound paragraph. Printed 16; upper bound 7; PDF pages 18, 9.

Patient-scope guarantees lower density at least 1/2 for every permitted full enumeration and also has eventual validity. Optimality is worst-case: no deterministic strategy guarantees more than 1/2. The proof gives μ_n(D∩K)≥μ_n(A)−r−log_2 n after target-rank normalization, for a finite play-dependent r.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.

Definitions: ownership_density, target_normalization, switch_loss, patient_schedule.

Scope: Achievability, validity context, quantitative proof inequality, and worst-case optimality.

Guarantee/access: The membership oracle is explicit, but criticality uses exact inclusion between infinite languages. The cited descriptions do not supply an effective reduction of those inclusion tests to membership queries, or a time bound. The mathematical guarantees are semantic under the described language access.

Source ambiguity or qualification:
- The phrase describing when generation starts is not a named exact round boundary in this edition. The proof uses eventual focus containment in K and the preceding-round output, so a finite initial exception may need to include the adjacent round.
- Achieves the optimal constant is a uniform lower bound, not a claim that every individual play has density exactly 1/2.
- The upper-bound paragraph omits enumeration catch-up details.

Visual checks: [page_9.png](visual-checks/earlier/page_9.png), [page_18.png](visual-checks/earlier/page_18.png).

### C13 — Public-v1 deterministic 1/2 lower-density guarantee and optimality

Edition: **arxiv-2608-01320-v1**. Theorem 3.14 and proof; Section 2 upper bound. Printed 16–17; upper bound 8; PDF pages 18, 19, 10.

The v1 patient-scope algorithm is asserted to guarantee target-relative lower density at least 1/2, with eventual validity, against every permitted adversary. The proof uses μ_n(D∩K)≥μ_n(A)−r−log_2 n in target ranks and the ownership partition of K. The constant is declared worst-case optimal.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Definitions: ownership_density, target_normalization, patient_schedule, switch_loss.

Scope: Achievability and optimality, including the displayed counting inequality and required validity.

Guarantee/access: The family is fully accessible, and algorithms use exact inclusion/criticality. No effective presentation, computable convergence bound, or running-time bound is part of the cited theorem context. Semantic guarantees must be kept distinct from an implementation using a specified finite interface.

Source ambiguity or qualification:
- Literal v1 criticality quantifies over all earlier consistent languages; later chain-dynamics and charging prose must be read with that edition-specific definition. It is not silently replaced by recursive criticality.
- The phrase describing when generation starts is not a named exact round boundary in this edition. The proof uses eventual focus containment in K and the preceding-round output, so a finite initial exception may need to include the adjacent round.
- The simple Section 2 upper-bound rule has no stated catch-up enumeration in v1.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C14 — Earlier-manuscript counterexample to direct patient-scope under partial enumeration

Edition: **earlier-supplied-manuscript**. Example 3.15 and partial-enumeration setup. Printed 16–17; PDF pages 18, 19.

Take L_1=(positive odds)∪4N+, L_i={2k:k≥i−1} for i>1, K=L_2=2N+, and enumerate only K′=4N+. The source says L_1 remains the unique critical language, patient-scope outputs only odds, target coverage is zero, and eventual target validity fails.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace full enumeration of K by enumeration of an infinite subset K′⊆K; the target is still K, and K′ need not belong to the candidate family. All density and eventual-validity conclusions remain relative to K. The edition’s repetition convention otherwise applies.

Definitions: partial_closure, consistency_scope_focus, patient_schedule.

Scope: Concrete family, target, enumerated subset, persistent focus, zero target density, and invalidity.

Guarantee/access: The membership oracle is explicit, but criticality uses exact inclusion between infinite languages. The cited descriptions do not supply an effective reduction of those inclusion tests to membership queries, or a time bound. The mathematical guarantees are semantic under the described language access.

Source ambiguity or qualification:
- No order of enumerating 4N+ is specified here. The only-odd-output assertion needs that schedule made concrete; taking the increasing enumeration is the natural witness, but this edition does not state it.

Visual checks: [page_18.png](visual-checks/earlier/page_18.png), [page_19.png](visual-checks/earlier/page_19.png).

### C15 — Public-v1 counterexample to direct patient-scope under partial enumeration

Edition: **arxiv-2608-01320-v1**. Example 3.17 and partial-enumeration setup. Printed 17–18; PDF pages 19, 20.

With L_1=(positive odds)∪4N+, L_i={2k:k≥i−1} (i>1), K=2N+, and adversary set K′=4N+, the source asserts that only L_1 is critical, all generator outputs are odd, and the direct algorithm has zero target density and fails validity.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace full enumeration of K by enumeration of an infinite subset K′⊆K; the target is still K, and K′ need not belong to the candidate family. All density and eventual-validity conclusions remain relative to K. The edition’s repetition convention otherwise applies.

Definitions: partial_closure, consistency_scope_focus, patient_schedule.

Scope: Family, target/subset, focus obstruction, density and validity failures.

Guarantee/access: The family is fully accessible, and algorithms use exact inclusion/criticality. No effective presentation, computable convergence bound, or running-time bound is part of the cited theorem context. Semantic guarantees must be kept distinct from an implementation using a specified finite interface.

Source ambiguity or qualification:
- The enumeration order of the multiples of 4 is not specified; the literal only-odd-output assertion needs a schedule such as increasing order.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C16 — Earlier-manuscript finite-intersection closure restores partial-enumeration validity

Edition: **earlier-supplied-manuscript**. Finite-intersection construction and Lemma 3.16. Printed 17–18; PDF pages 19, 20.

Run patient-scope on the finite-intersection family X′ while the adversary enumerates an infinite K′⊆K. The generator is asserted eventually valid in K. The proof finds a permanently critical intersection with binary code I in [2^(i*−1),2^i*) and hence L′_I⊆K.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace full enumeration of K by enumeration of an infinite subset K′⊆K; the target is still K, and K′ need not belong to the candidate family. All density and eventual-validity conclusions remain relative to K. The edition’s repetition convention otherwise applies.

Definitions: partial_closure, patient_schedule, consistency_scope_focus.

Scope: Preprocessing and binary index convention, persistent critical subset, eventual focus containment and fresh target outputs.

Guarantee/access: The earlier edition explicitly computes each intersection membership oracle by finitely conjoining original membership queries. Discarding finite intersections and deciding language inclusion are not given effective implementations; validity itself is semantic.

Source ambiguity or qualification:
- The presentation keeps binary-coded indices while saying finite intersections may be discarded. It does not specify a computable test for finiteness or fully detail reindexing after removal; its displayed proof assumes the intersections under consideration are infinite.

Visual checks: [page_19.png](visual-checks/earlier/page_19.png), [page_20.png](visual-checks/earlier/page_20.png).

### C17 — Public-v1 finite-intersection closure validity

Edition: **arxiv-2608-01320-v1**. Finite-intersection construction and Lemma 3.18. Printed 18–19; PDF pages 20, 21.

Patient-scope on L′ is asserted to generate K in the limit when the adversary enumerates only infinite K′⊆K. The displayed proof stabilizes a finite prefix of consistency statuses and claims a permanent critical intersection whose code contains the target’s highest bit, so that it is a subset of K.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace full enumeration of K by enumeration of an infinite subset K′⊆K; the target is still K, and K′ need not belong to the candidate family. All density and eventual-validity conclusions remain relative to K. The edition’s repetition convention otherwise applies.

Definitions: partial_closure, patient_schedule, consistency_scope_focus.

Scope: Closure family and indexing, eventual critical subset, eventual validity.

Guarantee/access: The family is fully accessible, and algorithms use exact inclusion/criticality. No effective presentation, computable convergence bound, or running-time bound is part of the cited theorem context. Semantic guarantees must be kept distinct from an implementation using a specified finite interface.

Source ambiguity or qualification:
- The presentation keeps binary-coded indices while saying finite intersections may be discarded. It does not specify a computable test for finiteness or fully detail reindexing after removal; its displayed proof assumes the intersections under consideration are infinite.
- Literal v1 criticality quantifies over all earlier consistent languages; later chain-dynamics and charging prose must be read with that edition-specific definition. It is not silently replaced by recursive criticality.
- The proof’s step from containment in the last critical intersection to existence of a later critical intersection must be retained with the literal all-consistent definition; no alternative recursive definition is supplied in v1.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C18 — Earlier-manuscript alpha-over-two density from partial enumeration

Edition: **earlier-supplied-manuscript**. Theorem 3.17 and proof. Printed 18–19; PDF pages 20, 21.

If liminf_n μ_n(K′)/μ_n(K)=α for infinite K′⊆K, running patient-scope on X′ guarantees liminf_n μ_n(D∩K)/μ_n(K)≥α/2, together with eventual validity. The proof uses K′⊆A∪(D∩K) and μ_n(D∩K)≥μ_n(A)−r−log_2 n after target normalization.

Assumptions: the **earlier-supplied-manuscript** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace full enumeration of K by enumeration of an infinite subset K′⊆K; the target is still K, and K′ need not belong to the candidate family. All density and eventual-validity conclusions remain relative to K. The edition’s repetition convention otherwise applies.
- α∈[0,1] is the lower density of K′ in K; the procedure does not need α as input.

Definitions: partial_closure, ownership_density, target_normalization, patient_schedule.

Scope: Density relative to K, intersection preprocessing, validity, counting argument, and α/2 conclusion.

Guarantee/access: The membership oracle is explicit, but criticality uses exact inclusion between infinite languages. The cited descriptions do not supply an effective reduction of those inclusion tests to membership queries, or a time bound. The mathematical guarantees are semantic under the described language access.

Source ambiguity or qualification:
- The presentation keeps binary-coded indices while saying finite intersections may be discarded. It does not specify a computable test for finiteness or fully detail reindexing after removal; its displayed proof assumes the intersections under consideration are infinite.
- The phrase describing when generation starts is not a named exact round boundary in this edition. The proof uses eventual focus containment in K and the preceding-round output, so a finite initial exception may need to include the adjacent round.

Visual checks: [page_19.png](visual-checks/earlier/page_19.png), [page_20.png](visual-checks/earlier/page_20.png), [page_21.png](visual-checks/earlier/page_21.png).

### C19 — Public-v1 alpha-over-two density from partial enumeration

Edition: **arxiv-2608-01320-v1**. Theorem 3.19 and proof. Printed 19; PDF pages 21.

For infinite K′⊆K of lower target-relative density α, the source asserts that patient-scope applied to L′ has lower density at least α/2 in K and eventual validity. Its counting argument combines the adversary/generator cover of K′ with the earlier logarithmic-loss inequality.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace full enumeration of K by enumeration of an infinite subset K′⊆K; the target is still K, and K′ need not belong to the candidate family. All density and eventual-validity conclusions remain relative to K. The edition’s repetition convention otherwise applies.
- α is the lower density of K′ relative to K, in [0,1]; it is not supplied to the algorithm.

Definitions: partial_closure, ownership_density, target_normalization, patient_schedule.

Scope: Partial model, preprocessing, validity and α/2 guarantee.

Guarantee/access: The family is fully accessible, and algorithms use exact inclusion/criticality. No effective presentation, computable convergence bound, or running-time bound is part of the cited theorem context. Semantic guarantees must be kept distinct from an implementation using a specified finite interface.

Source ambiguity or qualification:
- The presentation keeps binary-coded indices while saying finite intersections may be discarded. It does not specify a computable test for finiteness or fully detail reindexing after removal; its displayed proof assumes the intersections under consideration are infinite.
- Literal v1 criticality quantifies over all earlier consistent languages; later chain-dynamics and charging prose must be read with that edition-specific definition. It is not silently replaced by recursive criticality.
- The phrase describing when generation starts is not a named exact round boundary in this edition. The proof uses eventual focus containment in K and the preceding-round output, so a finite initial exception may need to include the adjacent round.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C20 — Randomization achieves lower density one minus one over e

Edition: **arxiv-2608-01320-v1**. Theorem 4.2; Section 4; Appendix B including Lemmas B.1–B.3. Printed 20–27; 39–43; PDF pages 22, 23, 24, 25, 26, 27, 28, 29, 41, 42, 43, 44, 45.

For every indexed family there is a randomized generator valid in the limit and having expected lower density at least 1−1/e against every oblivious target enumeration. The exact constant is attained by the Appendix B variable-block algorithm, not by merely fixing a large finite block parameter.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace the default deterministic-generator/adaptive-adversary setting by a randomized generator and an oblivious adversary whose deterministic target enumeration is fixed independently of realized coins.

Definitions: random_density, blocks, target_normalization, auxiliary_tools, patient_schedule.

Scope: The existence theorem, separate validity lemma, full appendix algorithm, and exact asymptotic constant.

Guarantee/access: Semantic randomized existence under full language access and exact inclusion. Independent finite permutations are explicit; no computational running-time or almost-sure density claim is stated.

Proof context: The main algorithm has block parameter m and guarantee (1−1/(m+1))f(m+1). Appendix B grows blocks, uses O(log n) incomplete blocks of size O(sqrt(n)), and a finite small-block exception C_ε. Its scope trigger counts 2^τ unreserved adversary announcements; the prose does not explicitly reset that counter in the box.

Source ambiguity or qualification:
- Literal v1 criticality quantifies over all earlier consistent languages; later chain-dynamics and charging prose must be read with that edition-specific definition. It is not silently replaced by recursive criticality.
- Appendix B sets block size to ceil(sqrt(m)), where m is the smallest available integer as an ambient value. Its proof then identifies K with N+; that relabeling does not automatically preserve ambient values or chosen block sizes. No focus-rank definition is supplied in this edition.
- The block proof treats a finite pre-validity count as an additive term; it does not give v2’s explicit conditional-history and Fatou treatment. Preserve the expected-density statement rather than strengthening it to a pathwise density claim.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C21 — No randomized algorithm beats one minus one over e

Edition: **arxiv-2608-01320-v1**. Theorem 4.4, Section 4.3, Lemma 4.12, Remark 4.13. Printed 20; 26–28; PDF pages 22, 28, 29, 30.

For each randomized generator, an oblivious enumeration can force expected lower density at most 1−1/e, already for the known target K=N+. The proof concatenates doubly exponentially growing blocks and chooses each block permutation using the generator’s distribution and the online-matching upper bound.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace the default deterministic-generator/adaptive-adversary setting by a randomized generator and an oblivious adversary whose deterministic target enumeration is fixed independently of realized coins.
- The hard case is explicitly presented in Section 4.3 as the single-language game with known target N+; it is a special case used to establish the general impossibility.

Definitions: random_density, ownership_density, auxiliary_tools.

Scope: Universal impossibility, single-target hard case, block asymptotics, and the fixed-order/nonadaptive qualification.

Guarantee/access: Semantic impossibility for arbitrary randomized strategies; no resource restriction.

Proof context: Block sizes are 2^(2^i); the number of earlier outputs is o(current block size). The selected block endpoints give the subsequence controlling liminf.

Source ambiguity or qualification:
- The hard order may depend on the randomized algorithm as a probability distribution but not on its realized random choices. The paper calls matching instances upper triangular while its neighborhood formula has empty last row and one fewer neighbor each step.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C22 — One-half density is simultaneously achievable under finitely many orders

Edition: **arxiv-2608-01320-v1**. Theorem 5.2, Definition 5.1, Section 5, Appendix C including Lemmas C.1–C.3. Printed 28–34; 43–47; PDF pages 30, 31, 32, 33, 34, 35, 36, 45, 46, 47, 48, 49.

For every positive finite k and fixed k orders, one deterministic generator is asserted valid in the limit and simultaneously guarantees target-relative lower density at least 1/2 in each order, against every adaptive adversary. The exact construction is the variable-block paired algorithm in Appendix C.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Definitions: multi_order_v1, blocks, target_normalization, auxiliary_tools, patient_schedule.

Scope: Same algorithm for all finitely many orders, validity, exact constant and Appendix C construction.

Guarantee/access: The family is fully accessible, and algorithms use exact inclusion/criticality. No effective presentation, computable convergence bound, or running-time bound is part of the cited theorem context. Semantic guarantees must be kept distinct from an implementation using a specified finite interface.

Proof context: Use m=min_iρ_i(W∩F), b=ceil(sqrt(m)); reserve the union of b available minima per order, pad to even size, and pair using low-crossing partitions. At most log_2 n+1 incomplete heads and a finite small-block exception yield the stated asymptotic ratio.

Source ambiguity or qualification:
- Literal v1 criticality quantifies over all earlier consistent languages; later chain-dynamics and charging prose must be read with that edition-specific definition. It is not silently replaced by recursive criticality.
- Appendix C defines ρ_i(S) using ambient-order rank, then relabels K; this is not the focus-relative rank used in v2. The block-size invariance under relabeling is not established here.
- The main fixed-parameter algorithm gives only h(m)/2, with h(m)=1−(4(km+1)^(1−1/k)+1)/m. Appendix C is needed for the exact half.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C23 — Randomized one-minus-one-over-e density under finitely many orders

Edition: **arxiv-2608-01320-v1**. Theorem 5.9, Definition 5.8 and Appendix D including Lemmas D.1–D.3. Printed 35; 47–52; PDF pages 37, 49, 50, 51, 52, 53, 54.

For any fixed positive finite collection of orders, a single randomized generator is asserted valid in the limit and guarantees min_i liminf_n E[μ_i,n(D∩K)]/μ_i,n(K)≥1−1/e for every oblivious enumeration.

Assumptions: the **arxiv-2608-01320-v1** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace the default deterministic-generator/adaptive-adversary setting by a randomized generator and an oblivious adversary whose deterministic target enumeration is fixed independently of realized coins.

Definitions: multi_order_v1, random_density, blocks, target_normalization, auxiliary_tools.

Scope: Simultaneity in all k orders, separate validity, expected density, full grouped variable-block algorithm and exact constant.

Guarantee/access: The family is fully accessible, and algorithms use exact inclusion/criticality. No effective presentation, computable convergence bound, or running-time bound is part of the cited theorem context. Semantic guarantees must be kept distinct from an implementation using a specified finite interface.

Proof context: Take b=ceil(m^(2/3)), g=ceil(m^(1/3)), reserve a union of k b-heads, pad block size to a multiple of g, and partition into low-crossing groups of size g with independent random permutations. The local factor φ(m)=(1−1/g)f(g)(1−4g((kb+g)/g)^(1−1/k)/b) tends to 1−1/e. Incomplete-head errors are O(n^(2/3)log n).

Source ambiguity or qualification:
- Literal v1 criticality quantifies over all earlier consistent languages; later chain-dynamics and charging prose must be read with that edition-specific definition. It is not silently replaced by recursive criticality.
- The appendix uses ambient ρ_i(W∩F), then target relabeling; focus-relative rank and its invariance are not defined in v1.
- Lemma D.3 describes group counts and fractions somewhat interchangeably, and folds a block trigger into a group; the expected-density claim is clear, while those local accounting steps are compressed.
- The random stabilization time is discarded as a finite prefix without an explicit conditional-history/Fatou argument in this edition.
- Exact v1 PDF screenshot requests returned metadata/placeholders or a cache-miss error, not image data available for inspection; PDF text was read and formulas cross-checked with same-v1 author HTML where accessible.

Visual status: exact-edition remote screenshots were attempted but usable images were not delivered; see run record.

### C24 — ArXiv v2 patient-scope and backtracking algorithms

Edition: **arxiv-2608-01320-v2**. Section 3.2, patient-scope/backtracking boxes and Figure 4. Printed 13–14; PDF pages 15, 16.

Start s_0=1 and τ=1. Retain scope between rounds. After an adversary announcement update consistency and criticality. Falsification invokes backtracking and increments τ. Otherwise, after 2^τ preceding steps with unchanged focus, expand scope by one; increment τ if that expansion changes focus. Output the least integer in the resulting focus not announced by either player. Backtracking, when no consistent language is in scope, expands to find one; otherwise truncate to the greatest old critical index still critical, or the least consistent index if no old critical one survives.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus, patient_schedule.

Scope: Initialization, update order, exponential wait, counter changes, scope expansion, output and all backtracking branches.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Proof context: Uses recursive criticality from printed 10 / PDF 12 and fixed-scope stability in Remark 3.7.

Source ambiguity or qualification:
- The wait condition is given as preceding time steps in prose rather than a separate exact-round machine specification.

Visual checks: [page_15.png](visual-checks/v2/page_15.png), [page_16.png](visual-checks/v2/page_16.png).

### C25 — ArXiv v2 target-relative lower density

Edition: **arxiv-2608-01320-v2**. Definition 2.2, ownership notation and Definition 2.1. Printed 7; PDF pages 9.

Density is liminf_n μ_n(D∩K)/μ_n(K), with μ_n(S)=|[n]∩S| and ownership determined by the first announcement of each value. Full enumeration gives μ_n(A)+μ_n(D∩K)=μ_n(K).

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: ownership_density.

Scope: Target-relative normalization, ownership partition, distinction from eventual validity.

Guarantee/access: Semantic asymptotic definition, with no effective or oracle claim by itself.

Source ambiguity or qualification:
- The denominator may vanish for early ambient prefixes, but K is infinite and it is eventually positive.

Visual checks: [page_9.png](visual-checks/v2/page_9.png).

### C26 — ArXiv v2 deterministic one-half upper bound

Edition: **arxiv-2608-01320-v2**. Paragraph following Definition 2.2. Printed 7–8; PDF pages 9, 10.

No deterministic algorithm can uniformly guarantee target-relative lower density greater than 1/2. The stated adversary normally takes the least unused target element and inserts sufficiently sparse catch-up rounds so that all remaining target elements are enumerated.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: ownership_density.

Scope: Worst-case half upper bound and full enumeration through catch-up rounds.

Guarantee/access: Semantic adversarial impossibility without a computational restriction.

Source ambiguity or qualification:
- This is an unnumbered explanatory upper-bound argument; no explicit numerical catch-up schedule is given.

Visual checks: [page_9.png](visual-checks/v2/page_9.png), [page_10.png](visual-checks/v2/page_10.png).

### C27 — ArXiv v2 recursive criticality

Edition: **arxiv-2608-01320-v2**. Definition 3.2 and footnote 1. Printed 10; PDF pages 12.

Recursive: begin with the least-indexed consistent language; thereafter a consistent L_i is critical iff it is contained in every earlier critical L_j. The footnote and Remark 3.7 explicitly distinguish this from the all-earlier-consistent definition.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus.

Scope: Least-consistent base and recursive subset condition over earlier critical languages.

Guarantee/access: Semantic induction in candidate-index order with exact set inclusion.

Source ambiguity or qualification:
- The footnote distinguishes earlier consistent languages from earlier critical languages; the latter is essential to this edition.

Visual checks: [page_12.png](visual-checks/v2/page_12.png).

### C28 — ArXiv v2 critical-chain dynamics

Edition: **arxiv-2608-01320-v2**. Remark 3.3. Printed 10; PDF pages 12.

At each round the recursively critical languages form a descending inclusion chain. After an adversary announcement, old critical languages that cease to be critical constitute a suffix of the old chain; any newly critical language has greater index than every surviving old critical language.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus.

Scope: Descending-chain property, removal of an old suffix, and index placement of new critical languages.

Guarantee/access: Semantic structural consequence; no effective maintenance cost is asserted.

Source ambiguity or qualification:
- This is an assertion about recursive criticality in v2, with consistency updated after an announcement. It is not a claim about an arbitrary chosen chain.

Visual checks: [page_12.png](visual-checks/v2/page_12.png).

### C29 — ArXiv v2 eventual target criticality

Edition: **arxiv-2608-01320-v2**. Lemma 3.4 and proof. Printed 10; PDF pages 12.

For every K=L_i★ and complete adversary enumeration, there is a finite time after which K is always recursively critical. Each of the finitely many earlier languages not containing K is eventually eliminated by an announced witness in K\L_j.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus.

Scope: Permanent eventual criticality and the finite-earlier-witness argument.

Guarantee/access: Semantic eventual-existence lemma; no computable convergence bound.

Source ambiguity or qualification:
- The threshold depends on the enumeration and is not asserted computable or uniform. Full coverage of K is used.

Visual checks: [page_12.png](visual-checks/v2/page_12.png).

### C30 — ArXiv v2 recursive-criticality fixed-scope stability

Edition: **arxiv-2608-01320-v2**. Remark 3.7 across page break. Printed 10–11; PDF pages 12, 13.

With v2 recursive criticality, if scope does not shrink, a focus change requires either falsification of the old focus or a scope expansion that includes a new critical language. In particular, fixed scope and survival of the old focus imply the same focus after the announcement.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus.

Scope: The fixed-scope stability clause and its explanation by contrast with the all-earlier-consistent definition stated in the source.

Guarantee/access: Semantic transition property of the recursive chain, independent of computational implementation.

Source ambiguity or qualification:
- The no-shrink qualifier and the possibility of expansion must be preserved.

Visual checks: [page_12.png](visual-checks/v2/page_12.png), [page_13.png](visual-checks/v2/page_13.png).

### C31 — ArXiv v2 switch loss

Edition: **arxiv-2608-01320-v2**. Definition 3.10; Fact 3.11 and proof. Printed 12; PDF pages 14.

An adversary value is a switch loss when it is outside the focus at the end of the preceding round. Its arrival falsifies that old focus. Being a switch loss does not itself require first ownership by the adversary; charging bounds restrict to previously unannounced losses.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.
- The previous-round focus is defined.

Definitions: consistency_scope_focus, switch_loss.

Scope: Failure of the previous focus to contain the current adversary value, with the equivalent falsification interpretation.

Guarantee/access: Semantic event definition; it is not a guarantee about an algorithm by itself.

Source ambiguity or qualification:
- The definition includes announcements regardless of first ownership; the later charging lemma concerns only previously unannounced switch-loss values.

Visual checks: [page_14.png](visual-checks/v2/page_14.png).

### C32 — ArXiv v2 patient-scope validity

Edition: **arxiv-2608-01320-v2**. Lemma 3.12 and proof. Printed 15; PDF pages 17.

Patient-scope eventually outputs only fresh elements of K for every legal full enumeration. The proof additionally fixes T★ after which every focus is contained in K, following eventual permanent criticality and scope inclusion of the target index.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus, patient_schedule.

Scope: Validity, novelty and explicit eventual focus-containment threshold used in charging.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Source ambiguity or qualification:
- T★ is play-dependent and denotes the regime of focus containment; no effective bound is given.

Visual checks: [page_17.png](visual-checks/v2/page_17.png).

### C33 — ArXiv v2 preceding-focus membership and output comparison

Edition: **arxiv-2608-01320-v2**. Fact 3.13; reference to Fact 3.11; Theorem 3.15 use. Printed 15–17; PDF pages 17, 18, 19.

For an adversary-first value a_t that is not a switch loss, a_t∈F_(t−1) and d_(t−1)≤a_t. With the preceding focus contained in K, the preceding fresh output is a distinct smaller generator-owned element of K. These preceding outputs are distinct for different late adversary-first rounds.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.
- t>1; for a target-supported partner, the preceding focus is in the post-T★ regime.

Definitions: switch_loss, patient_schedule, target_normalization.

Scope: Old-focus membership and stated non-strict comparison; valid partner support/injection supplied by surrounding proof context.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Source ambiguity or qualification:
- The strict comparison used in the theorem follows from distinct ownership; Fact 3.13 itself states at least-as-large.

Visual checks: [page_17.png](visual-checks/v2/page_17.png), [page_19.png](visual-checks/v2/page_19.png).

### C34 — ArXiv v2 logarithmic switch-loss bound

Edition: **arxiv-2608-01320-v2**. Lemma 3.14 and Figure 5 proof. Printed 15–16; PDF pages 17, 18.

After T★, for each target-rank prefix [n] the number w of previously unannounced switch-loss values is ≤log_2 n. Backtracking from L_j to L_i gives i<j, L_j⊆L_i⊆K, and ℓ∈L_i; each loss is charged disjoint earlier outputs from a 2^τ′ waiting interval. Distinct τ′ yield n≥Σ2^τ′≥2^w.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: switch_loss, patient_schedule, target_normalization.

Scope: Post-T★ loss bound, history-derived support, distinct exponential charges, and logarithmic conclusion.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Source ambiguity or qualification:
- The source has already normalized K by target rank. The output count concerns loss values first announced by the adversary, not all focus changes.

Visual checks: [page_17.png](visual-checks/v2/page_17.png), [page_18.png](visual-checks/v2/page_18.png).

### C35 — ArXiv v2 deterministic one-half density and optimality

Edition: **arxiv-2608-01320-v2**. Theorem 3.15 and proof; Section 2 upper bound. Printed 16–17; 7–8; PDF pages 18, 19, 9, 10.

Patient-scope is valid in the limit and guarantees density at least 1/2 against every permitted adversary. In target ranks, μ_n(D∩K)≥μ_n(A)−M_0−log_2 n, where M_0 counts adversary-first values through T★+1. Combining with the ownership partition gives the asymptotic half; the Section 2 adversary gives worst-case optimality.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: ownership_density, target_normalization, patient_schedule, switch_loss.

Scope: Validity, quantitative finite-prefix inequality, asymptotic lower bound and worst-case optimality.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Source ambiguity or qualification:
- The theorem gives a guaranteed lower bound; individual plays can have greater density. T★+1 is explicitly included to cover the preceding-output boundary.

Visual checks: [page_9.png](visual-checks/v2/page_9.png), [page_10.png](visual-checks/v2/page_10.png), [page_18.png](visual-checks/v2/page_18.png), [page_19.png](visual-checks/v2/page_19.png).

### C36 — ArXiv v2 q-output density extension

Edition: **arxiv-2608-01320-v2**. Remark 3.16. Printed 17; PDF pages 19.

For a fixed positive integer q, allow q generator outputs per round and announce the q smallest currently unannounced focus elements. The resulting algorithm guarantees target-relative lower density at least q/(q+1); apart from negligible switch losses, each adversary-first value is charged q distinct smaller generator-first values with disjoint charges.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace one generator output per round by the fixed positive integer budget q; the adversary still announces one value per round.
- q is a positive integer and is fixed across rounds.

Definitions: ownership_density, patient_schedule, switch_loss, target_normalization.

Scope: Modified q-output rule, q-partner charging and density q/(q+1).

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Source ambiguity or qualification:
- The extension is stated in a remark without a separate full proof or explicit rewritten counter-update machine. q is a fixed per-round output budget.

Visual checks: [page_19.png](visual-checks/v2/page_19.png).

### C37 — ArXiv v2 infinitely-often accurate focus

Edition: **arxiv-2608-01320-v2**. Remark 3.17. Printed 17; PDF pages 19.

Viewing its focus as its language hypothesis, patient-scope equals the true language at infinitely many time steps. Once K is permanently critical and in scope, it either remains the focus or each excursion to a proper subset is eventually falsified by complete enumeration and backtracking returns to K.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: consistency_scope_focus, patient_schedule.

Scope: Semantic language equality infinitely often and the excursion/backtracking argument.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Source ambiguity or qualification:
- Accuracy concerns equality of hypothesis languages as sets; the source does not require eventual convergence to one fixed candidate index. This full-enumeration argument is not asserted for arbitrary K′⊂K.

Visual checks: [page_19.png](visual-checks/v2/page_19.png).

### C38 — ArXiv v2 failure on the untransformed family

Edition: **arxiv-2608-01320-v2**. Example B.1 and preceding partial-enumeration setup. Printed 18; 39–40; PDF pages 20, 41, 42.

Take L_1=(positive odds)∪4N+, L_i={2k:k≥i−1} for i>1, K=2N+, K′=4N+, and adversary sequence 4,8,12,... . The direct patient-scope focus stays L_1, the outputs are odd, no outputs lie in K, and the algorithm fails validity and has zero target density.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace full enumeration of K by enumeration of an infinite subset K′⊆K; the target is still K, and K′ need not belong to the candidate family. All density and eventual-validity conclusions remain relative to K. The edition’s repetition convention otherwise applies.

Definitions: partial_closure, consistency_scope_focus, patient_schedule.

Scope: Family, target, explicit increasing partial enumeration, focus obstruction, zero coverage and invalidity.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Source ambiguity or qualification:
- Unlike the earlier editions, this example explicitly fixes increasing enumeration of the multiples of 4.

Visual checks: [page_20.png](visual-checks/v2/page_20.png), [page_41.png](visual-checks/v2/page_41.png), [page_42.png](visual-checks/v2/page_42.png).

### C39 — ArXiv v2 partial-enumeration validity

Edition: **arxiv-2608-01320-v2**. Finite-intersection construction, Lemma B.2 and proof. Printed 40–41; PDF pages 42, 43.

Under enumeration of infinite K′⊆K, patient-scope on L′ eventually generates fresh elements in K. The proof stabilizes a finite range and obtains a permanently critical intersection whose code lies in [2^(i★−1),2^i★), hence lies inside K. It explicitly concludes existence of T★ after which all foci lie in K.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace full enumeration of K by enumeration of an infinite subset K′⊆K; the target is still K, and K′ need not belong to the candidate family. All density and eventual-validity conclusions remain relative to K. The edition’s repetition convention otherwise applies.

Definitions: partial_closure, patient_schedule, consistency_scope_focus.

Scope: Intersection preprocessing and index coding, persistent critical subset, validity and explicit focus-containment regime.

Guarantee/access: Semantic validity under full family access. Finite intersections have their ordinary set-theoretic meaning; no effective procedure for detecting finite intersections or exact inclusion is specified.

Source ambiguity or qualification:
- The presentation keeps binary-coded indices while saying finite intersections may be discarded. It does not specify a computable test for finiteness or fully detail reindexing after removal; its displayed proof assumes the intersections under consideration are infinite.

Visual checks: [page_42.png](visual-checks/v2/page_42.png), [page_43.png](visual-checks/v2/page_43.png).

### C40 — ArXiv v2 partial-enumeration density guarantee

Edition: **arxiv-2608-01320-v2**. Theorem B.3 and proof. Printed 41; PDF pages 43.

If the infinite enumerated subset K′ has target-relative lower density α, patient-scope on L′ guarantees lower density at least α/2 in K and eventual validity. In target ranks, μ_n(D∩K)≥μ_n(A)−M_0−log_2 n, where M_0 counts adversary-first values through T★+1; K′⊆A∪(D∩K) gives the result.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace full enumeration of K by enumeration of an infinite subset K′⊆K; the target is still K, and K′ need not belong to the candidate family. All density and eventual-validity conclusions remain relative to K. The edition’s repetition convention otherwise applies.
- α∈[0,1] is the lower density of K′ in K; the generator does not use α or K′ as input.

Definitions: partial_closure, ownership_density, target_normalization, patient_schedule.

Scope: Partial-enumeration scope, closure construction, validity, exact initial exception and α/2 bound.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Source ambiguity or qualification:
- The presentation keeps binary-coded indices while saying finite intersections may be discarded. It does not specify a computable test for finiteness or fully detail reindexing after removal; its displayed proof assumes the intersections under consideration are infinite.

Visual checks: [page_20.png](visual-checks/v2/page_20.png), [page_42.png](visual-checks/v2/page_42.png), [page_43.png](visual-checks/v2/page_43.png).

### C41 — ArXiv v2: Randomization achieves lower density one minus one over e

Edition: **arxiv-2608-01320-v2**. Theorem 4.2; Section 4; Appendix C, Lemmas C.1–C.5 and proof. Printed 18–26; 41–46; PDF pages 20, 21, 22, 23, 24, 25, 26, 27, 28, 43, 44, 45, 46, 47, 48.

There is a randomized generator with expected lower density at least 1−1/e for every oblivious target enumeration. Its validity holds for every realization of its permutations. Appendix C supplies the exact variable-block algorithm: with a=min(W∩F), set m=|F∩[a]| and reserve ceil(sqrt(m)) available focus elements.

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace the default deterministic-generator/adaptive-adversary setting by a randomized generator and an oblivious adversary whose deterministic target enumeration is fixed independently of realized coins.

Definitions: random_density, blocks, target_normalization, auxiliary_tools, patient_schedule.

Scope: Exact existence theorem, pathwise validity, focus-relative block size, full appendix error and expectation argument.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Proof context: Scope growth waits for 2^τ newly reserved blocks since the last focus change. Creation histories H_r make block data and completeness measurable and preserve conditional uniform permutations. Relevant blocks have O(log n) distinct foci; small blocks contribute O_ε(log n), and incomplete blocks O(sqrt(n)log n). The proof applies total expectation, monotone convergence and Fatou, allowing random T★ and finite M_0.

Source ambiguity or qualification:
- The density is liminf of expected coverage, while the separate validity guarantee is realization-wise.
- The fixed-size algorithm gives only (1−1/(m+1))f(m+1); it cannot by itself instantiate the exact-constant theorem.

Visual checks: [page_20.png](visual-checks/v2/page_20.png), [page_21.png](visual-checks/v2/page_21.png), [page_44.png](visual-checks/v2/page_44.png), [page_48.png](visual-checks/v2/page_48.png).

### C42 — ArXiv v2: No randomized algorithm beats one minus one over e

Edition: **arxiv-2608-01320-v2**. Theorem 4.4; Section 4.3, Lemma 4.12 and Remark 4.13. Printed 19; 25–26; PDF pages 21, 27, 28.

For each randomized generator, a fixed oblivious enumeration forces expected lower density at most 1−1/e, already for target K=N+. The source constructs doubly exponentially growing blocks and hard within-block permutations so that the expected ratio at block endpoints is ≤1−1/e+o(1).

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace the default deterministic-generator/adaptive-adversary setting by a randomized generator and an oblivious adversary whose deterministic target enumeration is fixed independently of realized coins.
- The hard case is explicitly presented in Section 4.3 as the single-language game with known target N+; it is a special case used to establish the general impossibility.

Definitions: random_density, ownership_density, auxiliary_tools.

Scope: General randomized upper bound, known single target, full block construction and nonadaptivity justification.

Guarantee/access: Semantic impossibility for every randomized strategy, with no computational restriction.

Proof context: Block size is 2^(2^i), prior outputs are o(block size), and a strictly upper-triangular matching hard instance yields the block bound. The endpoint subsequence controls the liminf.

Source ambiguity or qualification:
- The hard order depends on the generator’s distribution, not realized coins; this distinction is explicitly explained in Remark 4.13.

Visual checks: [page_21.png](visual-checks/v2/page_21.png).

### C43 — ArXiv v2: One-half density is simultaneously achievable under finitely many orders

Edition: **arxiv-2608-01320-v2**. Theorem 5.2, Definition 5.1; Section 5; Appendix D, Lemmas D.1–D.5. Printed 27–34; 47–52; PDF pages 29, 30, 31, 32, 33, 34, 35, 36, 49, 50, 51, 52, 53, 54.

For every positive finite k and k fixed orders, a single deterministic generator is valid in the limit and guarantees density at least 1/2 in each order against every adaptive adversary. Appendix D achieves the exact constant by variable-size paired blocks based on m=min_iρ_i^F(W∩F), where ρ_i^F is rank within the current focus; take b=ceil(sqrt(m)).

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Definitions: multi_order_v2, blocks, target_normalization, auxiliary_tools, patient_schedule.

Scope: Simultaneous finite-order density, validity, focus-relative ranks, exact appendix algorithm and low-crossing/error arguments.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Proof context: Reserve the union of the b least available focus elements in each order, pad to even cardinality, and pair via Theorem 2.5. Complete heads have local factor approaching half; O(log n) relevant foci bound small-block errors, and incomplete heads contribute O(k sqrt(n)log n). The focus-relative rank definition is preserved by target relabeling.

Source ambiguity or qualification:
- The finite k is fixed; no guarantee for infinitely many arbitrary orders is stated.
- The main fixed-size paired algorithm has only h(m)/2. Appendix D supplies a single procedure reaching half as its block sizes grow.

Visual checks: [page_29.png](visual-checks/v2/page_29.png), [page_50.png](visual-checks/v2/page_50.png), [page_54.png](visual-checks/v2/page_54.png).

### C44 — ArXiv v2: Randomized one-minus-one-over-e density under finitely many orders

Edition: **arxiv-2608-01320-v2**. Theorem 5.9, Definition 5.8; Appendix E, Lemmas E.1–E.5 and proof. Printed 35; 52–58; PDF pages 37, 54, 55, 56, 57, 58, 59, 60.

For any positive finite number of fixed orders, one randomized generator has min_i liminf_n E[μ_i,n(D∩K)]/μ_i,n(K)≥1−1/e against every oblivious enumeration. Validity holds for every permutation realization. Use focus-relative m=min_iρ_i^F(W∩F), heads of size b=ceil(m^(2/3)), and low-crossing groups of size g=ceil(m^(1/3)).

Assumptions: the **arxiv-2608-01320-v2** standing profile, subject to the setting changes stated here.

Setting overrides:
- Replace the default deterministic-generator/adaptive-adversary setting by a randomized generator and an oblivious adversary whose deterministic target enumeration is fixed independently of realized coins.

Definitions: multi_order_v2, random_density, blocks, target_normalization, auxiliary_tools.

Scope: Same generator for all orders, realization-wise validity, expected density, full grouped algorithm and exact limit.

Guarantee/access: Algorithms use semantic exact inclusion and critical-chain updates under full access to the language family. The cited statements do not claim a computable implementation from membership queries alone or any complexity bound.

Proof context: Reserve the union of k b-heads, pad to a multiple of g, partition into low-crossing groups, and use independent uniform permutations. Conditional block estimates have φ(m)=(1−1/g)f(g)(1−4g((kb+g)/g)^(1−1/k)/b)→1−1/e. O(log n) relevant foci control small blocks, incomplete-head contributions are O(k n^(2/3)log n), and total expectation/monotone convergence/Fatou handle random stabilization.

Source ambiguity or qualification:
- The operation is minimum over individual expected-density liminfs, not expectation of a minimum or an almost-sure density guarantee.
- The number of orders is fixed and finite.

Visual checks: [page_37.png](visual-checks/v2/page_37.png), [page_55.png](visual-checks/v2/page_55.png), [page_57.png](visual-checks/v2/page_57.png), [page_60.png](visual-checks/v2/page_60.png).

## Limitations and stop boundary

- The exact v1 PDF was available as page-indexed web text, but its raw bytes could not be retrieved: curl returned DNS failure. The expected v1 hash is metadata only, not verified bytes.
- Exact v1 PDF screenshot requests through two web wrappers returned only textual image placeholders/metadata or a cache-miss error, with no usable image blocks. Therefore no v1 decisive formula is claimed visually inspected. The supplementary exact-v1 author HTML was authorized by the coordinator and used to disambiguate formulas; some algorithm boxes are absent from that HTML text and were read in PDF extraction.
- Source ambiguities are preserved per slot, especially v1 all-earlier-consistent criticality, the ambient-rank variable blocks, finite-intersection removal/indexing, and early-generation boundary language. No source-to-Lean correspondence has been examined.

The source inventory is complete for all 44 slots with qualified v1 access. Stop here for coordinator freeze; access to Lean and Stage 1 requires the subsequent comparison authorization.
