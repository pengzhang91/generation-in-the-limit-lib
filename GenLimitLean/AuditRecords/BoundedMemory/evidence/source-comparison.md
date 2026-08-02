# 31 — Paper31_BoundedMemory — Author-paper versus Lean statement-faithfulness audit

## 1. Scope, source verification, and audit method

### 1.1 Verified author source

The attached PDF was verified before comparison.

| Field | Verified value |
|---|---|
| Title | **On Language Generation in the Limit with Bounded Memory** |
| Authors | **Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas** |
| arXiv identifier/version | **arXiv:2605.30324v1** |
| arXiv subject/date shown in the PDF | **[cs.DS], 28 May 2026** |
| Embedded arXiv identifier | `https://arxiv.org/abs/2605.30324v1` |
| Embedded DOI | `10.48550/arXiv.2605.30324` |
| PDF pages | 46 |
| Encryption | none |
| Verified local SHA-256 | `6c446edfa4f8ebc2978d144d213e88f61f29d06922721b016ba89faf64470049` |

The title, author list, version, and date agree between the first page, the arXiv footer, and the embedded PDF metadata. This audit therefore treats the attached file as the exact pinned source requested by the user. Page references below use **PDF page number / printed paper page number**; for example, “PDF p. 15 / paper p. 13” refers to the fifteenth PDF page, whose printed page number is 13.

### 1.2 Lean source used for comparison

The Lean side is taken from the completed Stage 1 artifact `31-bounded-memory-lean-statement-reconstruction.md`, SHA-256:

`a12a4c7cdf3e191c98d31fa7199939571cf82959ad0a61b17510384cca3ce78d`.

That artifact reconstructs declaration signatures from the repository snapshot at commit `dfcd13534f9d51642a9f88904268e95454c88f7f`. This Stage 2 audit uses those reconstructed statement types, not comments, filenames, declaration names as intended-meaning evidence, or proof bodies.

### 1.3 What is and is not being audited

This is a **statement-faithfulness** audit. For each paper result, it asks whether the closest Lean declarations have the same objects, quantifiers, hypotheses, presentation regime, memory interface, output interface, and conclusion. It also checks whether conditional helper declarations are actually assembled into an end-to-end theorem.

This is **not** a proof-correctness audit. A faithful theorem statement could still have an incorrect proof body, and a kernel-accepted proof could establish a statement that is weaker or different from the paper. The report does not re-run Lean, inspect proof terms, or certify mathematical correctness of the proofs. It evaluates only what the declaration types say, using the Stage 1 reconstruction.

### 1.4 Verdict vocabulary

- **Faithful:** the Lean declaration states the same mathematical claim, up to harmless indexing or definitional presentation.
- **Weaker:** the Lean conclusion covers fewer universes, families, presentations, or outputs, or assumes extra substantive premises.
- **Stronger:** the Lean statement implies the paper claim after a straightforward identification, because it has fewer premises, more adversarial quantifiers, or a stronger conclusion.
- **Orthogonal:** the Lean statement proves a different kind of fact rather than a comparable strengthening or weakening.
- **Only conditionally related:** the claims coincide only after adding a nontrivial transport or interface equivalence not itself stated in Lean.
- **Absent:** no declaration or assembled collection of declarations states the paper claim.

## 2. Executive assessment

The formalization is **mostly faithful with qualifications**. The central semantic theorems are present: memoryless generation under finitely repeating presentations; the singleton-core characterization under arbitrary repetitions; element- and index-output separations; the memoryless and sliding-window density values; the adaptive-buffer lower bound; the three-language exact-identification obstruction; finite-family approximate identification; and the appendix coding results.

The most important qualifications are structural rather than cosmetic:

1. **Several headline results are fixed to `ℕ`, not an arbitrary countable universe.** Theorem 3.1 and some obstruction lemmas are generic, but Theorem 1.1, the density theory, window and buffer theorems, and incremental element coding lack a generic transport theorem.
2. **The density minimax game is not literally the paper's fixed-global-order model.** The paper fixes one canonical order of the ambient universe and every target inherits that order. Lean instead quantifies over a separate `OrderedLanguage` realization of each target after the generator is chosen. This makes achievability order-robust, but lets hard-instance theorems choose an order. The resulting equality has the same numerical value but is formally a different game until an order-transport theorem is added.
3. **`MemorylessSetGenerator` does not intrinsically output an infinite set at every input.** Infinitude is imposed only in eventual validity. The explicit positive generators do output infinite sets globally, so the main existence claims survive, but the base interface is weaker than the paper's codomain `[X]^∞`.
4. **Theorem 5.2 is stated for a relabeled family with equal set range, not directly for the input indexing.** This is faithful at the paper's extensional “collection” level, and the Stage 1 artifact records a bijective relabeling candidate, but the final declaration does not transport the learner back to the original index type.
5. **The appendix's incremental element model is not finite-memory in bits.** This is not a hidden defect relative to the paper: the paper explicitly says the previous output can encode the entire history and that the memory restriction collapses. Lean makes this mechanism explicit and is highly faithful on this point.
6. **Computability, oracle access, runtime, bit complexity, rates, and randomness are absent.** This aligns with the paper's semantic theorems and its concluding statement that computational and representation assumptions remain open; the Lean results must not be advertised as machine-level bounded-space algorithms.

No headline theorem is reduced to a tautological restatement of its conclusion, and the major conditional components for density, windows, buffers, and coding are assembled into end-to-end declarations. The main unassembled or absent paper-level claims are the countable-family zero uniform-density remark, a direct fixed-order minimax formulation, a direct original-index version of Theorem 5.2, and some informal extensions or alternative density aggregates.

## 3. Formal setting: paper versus Lean

### 3.1 Universe, languages, and collections

**Paper.** The paper fixes an arbitrary countable universe `X`, typically `Σ*`, together with a single canonical ordering `(x_1,x_2,...)`. A language is an infinite subset of `X`; collections are finite or countable sets of such languages. See PDF pp. 13–14 / paper pp. 11–12.

**Lean.** The Stage 1 artifact records two regimes:

- generic definitions over an arbitrary type `α`, with countability supplied by a `[Countable α]` instance where needed;
- many primary theorems fixed to `Set ℕ` and families indexed by `Fin k` or `ℕ`.

The generic layer does not provide a single transport theorem carrying all `ℕ`-specific results back to arbitrary countable `α`.

**Verdict:** **weaker** as an end-to-end paper formalization, because the paper's arbitrary countable universe is not uniformly recovered for Theorem 1.1, Sections 4 and A.2–A.3.

**Smallest repair.** Add transport declarations of the form

```lean
theorem theorem_1_1_countable
    [Countable α]
    (H : Set (Set α))
    (hH : H.Countable)
    (hInf : ∀ K, K ∈ H → K.Infinite) :
    FinitelyRepeatingMemorylessGeneratable H
```

and analogous fixed-order density/window/buffer/coding transports. The proof may choose an equivalence with `ℕ` in the nonempty case and conjugate languages, presentations, and generators; the empty family remains trivial.

### 3.2 Exact presentations

**Paper.** An enumeration of `K` is an infinite stream whose values all lie in `K` and whose range covers every element of `K`; repetitions are allowed unless a theorem restricts them. The sample `S_t` is the set of examples observed through round `t`. See Definitions 1 and 5, PDF pp. 4 and 14 / paper pp. 2 and 12.

**Lean.** `GenLimit.Generic.Presents stream K` is exactly `Set.range stream = K`. Thus no outside element occurs and every target element occurs at least once. `FinitelyRepeating` says every point has a finite time fiber; injective streams are used for repetition-free results.

**Verdict:** **faithful**.

The existential convergence threshold may depend on the whole target stream in both presentations of the mathematics. The runtime learner does not receive future information merely because the proof quantifies an eventual threshold afterward.

### 3.3 Full-history generation

**Paper.** Definition 5 defines full-history element-, set-, and index-based generation in the limit. A full-history generator may inspect the complete observed prefix. Theorem 3.1 also gives an equivalent formulation in which, after any one example, a full-memory set-based generator can already emit an infinite set safe for every compatible target. See PDF pp. 14 and 16–17 / paper pp. 12 and 14–15.

**Lean.** The generic dependency layer has an element-valued finite-history function `Generator α`, but the primary Paper 31 modules do not define a full-history set-valued or index-valued generator interface matching Definition 5. Theorem 3.1 formalizes the equivalent `InfiniteSingletonCores` condition directly, not the “one observed example in the unrestricted full-memory model” formulation.

**Verdict:** **absent** for the full three-output Definition 5 interface and **only conditionally related** for the one-example full-memory formulation.

**Smallest repair.** Define

```lean
def OneExampleSetSafe (H : Set (Set α)) : Prop :=
  ∃ A : α → Set α,
    ∀ x, x ∈ ⋃₀ H →
      (A x).Infinite ∧
      ∀ K, K ∈ H → x ∈ K → A x ⊆ K
```

and prove `OneExampleSetSafe H ↔ InfiniteSingletonCores H`, then include it in the Theorem 3.1 equivalence. Separately, add full-history set/index generator types if Definition 5 itself is intended to be covered.

### 3.4 Set-, element-, and index-valued outputs

**Paper.** A memoryless set generator has codomain `[X]^∞`, so every output is infinite, even before eventual correctness. Element output is a point of `X`; index output is an index naming a language in the collection. See Definition 3, PDF p. 6 / paper p. 4, and Section 3, PDF p. 15 / paper p. 13.

**Lean.** The interfaces are:

- `MemorylessSetGenerator α := α → Set α`, with infinitude checked inside eventual `ValidSetOutput`;
- `MemorylessElementGenerator α := α → α`;
- `MemorylessIndexGenerator α ι := α → ι`.

Window and buffer generators do package global output infinitude, unlike the memoryless set interface.

**Verdict:** memoryless set output is **weaker at the interface level**; element and index output are **faithful**.

The weakness does not invalidate the positive Theorem 1.1 witness or canonical density witness, because separate declarations establish their outputs are infinite for every input. It slightly enlarges the strategy space of generic memoryless minimax predicates by allowing finite outputs on finitely many relevant rounds or off all target ranges.

**Smallest repair.** Replace the raw type by either `α → {S : Set α // S.Infinite}` or a structure containing `output` and `output_infinite : ∀ x, (output x).Infinite`. Then remove the redundant infinitude conjunct from per-round validity.

### 3.5 Fixed canonical order and ordered density

**Paper.** One canonical ordering of the ambient `X` is fixed before the family. Each target `K` inherits the subsequence order of its elements, and `μ_up` and `μ_low` are the `limsup` and `liminf` of prefix proportions in that inherited order. See Definition 8, PDF p. 19 / paper p. 17.

**Lean.** `OrderedLanguage` bundles a carrier and any injective exact enumeration of that carrier. Main minimax guarantees quantify over **every** ordered realization of the target after choosing the generator. Hard instances may choose a particular ordered realization.

**Verdict:** **only conditionally related**. The analytic formulas are faithful, but the game order differs. Achievability statements are stronger because one generator must meet the bound for every order. Upper-bound statements need only exhibit one order, whereas the paper's theorem is intended relative to whatever ambient canonical order was fixed at the outset.

**Smallest repair.** Introduce one ambient-order parameter, for example a `CanonicalUniverseOrder α`, derive each target's inherited `OrderedLanguage`, and define all minimax guarantees relative to that fixed order. Prove hard instances parameterized by the ambient order rather than choosing a target order existentially. This is the highest-priority statement repair.

### 3.6 Computability and static family access

The paper's algorithms are semantic: it explicitly notes in the conclusion that its constructions assume full access to the collection and leaves oracle, computational, and representation assumptions open (PDF p. 38 / paper p. 36). Lean likewise uses arbitrary set membership, finiteness/infinitude tests, noncomputable topological orders, choice of enumerations and codewords, and `sSup`/`limsup`. The imported `MembershipOracle` interface is not used by the primary theorems.

**Verdict:** **faithful** to the paper's stated level of abstraction. Any claim that the Lean statements provide computable or runtime-bounded algorithms would be unfaithful to both sources.

### 3.7 Breadth versus ordered density

The paper discusses breadth as part of the surrounding generation hierarchy but deliberately adopts the Kleinberg--Wei ordered-density viewpoint for its quantitative theorems. It does not introduce a separate new breadth predicate whose characterization must be proved in this paper. Lean correspondingly formalizes upper/lower ordered density and does not define an independent breadth model.

**Verdict:** **faithful absence**, not a missing headline theorem. What is absent, and recorded later, is the full four-way temporal density comparison and some countable-family consequences.

## 4. Generation with no memory

### 4.1 Theorem 1.1 — universal memoryless set generation under finitely repeating presentations

#### (a) Paper claim

Theorem 1.1 (PDF pp. 6 and 15–16 / paper pp. 4 and 13–14) has the following quantifier order.

1. Fix a countable collection `L` of infinite languages over a countable universe `X`.
2. There exists one deterministic memoryless set-based generator `G : X → [X]^∞`, chosen for the whole collection.
3. For every target `K ∈ L` and every finitely repeating exact enumeration `(x_t)` of `K`,
4. there exists a finite threshold `t*`, depending on `K` and the enumeration,
5. such that for every `t ≥ t*`, `G(x_t) ⊆ K`.

The generator sees only the current example. It has no round number, sample history, prior output, target index, or separate state. The output set is infinite by its codomain, so it necessarily contains unseen target elements even though the statement does not explicitly subtract the finite sample.

#### (b) Closest Lean declarations

The principal declaration is:

- `theorem_1_1` in `FinitelyRepeating.lean`.

Expanded through the Stage 1 definitions, it says:

1. for every `H : Set (Set ℕ)`;
2. if `H.Countable` and every `K ∈ H` is infinite;
3. then there exists `G : ℕ → Set ℕ` such that
4. for every `K ∈ H` and every `stream : ℕ → ℕ`,
5. if `Set.range stream = K` and every point occurs only finitely often,
6. then there exists `T` such that for every `t ≥ T`, `(G (stream t)).Infinite` and `G (stream t) ⊆ K`.

The explicit witness is separately exposed by:

- `finitelyRepeatingGenerator`;
- `finitelyRepeatingGenerator_infinite`;
- `finitelyRepeatingGenerator_succeeds`;
- `theorem_1_1_enumerated`.

Its output on `x` is a longest-prefix common core, where the search depth is bounded by the numerical value of `x`, and infinitude of arbitrary intersections is tested noncomputably.

#### (c) Verdict

**Weaker**, but close.

#### (d) Exact reason

The logical success quantifiers match, and the explicit witness genuinely receives only the current example. The two literal mismatches are:

- the Lean theorem is fixed to `X = ℕ`, with no generic countable-universe transport;
- the base type `MemorylessSetGenerator` does not require every output to be infinite, although this theorem's explicit witness is globally infinite and the success predicate requires eventual infinitude.

There is no mismatch concerning computability: neither source proves an effective algorithm for arbitrary extensional languages. The generator is nonuniform in the family in both sources.

#### Smallest repair

Add the generic countable transport theorem described in §3.1, and strengthen the memoryless set-generator codomain as in §3.4. No change to the core construction is required.

#### Finite-intersection and exceptional-set subclaims

The paper's proof introduces `J_n(x)`, the largest depth `n(x)`, and the finite envelope `U_z` formed by the union of all finite intersections among the first `z` languages. The Stage 1 declarations mirror this structure rather than assuming it as a link hypothesis:

- `prefixCore`, `selectedDepth`, and `finitelyRepeatingGenerator` formalize `J_n(x)`, `n(x)`, and the output rule;
- `indexedIntersection`, `prefixSignature`, and `prefixCore_eq_indexedIntersection` identify the finitely many possible first-`z` intersections;
- `finiteIntersectionPiece`, `finiteIntersectionEnvelope`, and `finiteIntersectionEnvelope_finite` construct and prove finiteness of the analogue of `U_z`;
- `badPoints_subset` proves every bad target point lies either below the target index numerically or in that finite envelope;
- `badPoints_finite` and `finitelyRepeating_avoids_finite_set` close the endgame.

These are faithful proof-level statements. The key hidden resource is semantic access to whether an arbitrary intersection is infinite. No finite-intersection condition is supplied as an assumption that already contains the conclusion.

### 4.2 Theorem 3.1 — characterization under arbitrary repetitions

#### (a) Paper claim

Theorem 3.1 (PDF pp. 16–17 / paper pp. 14–15) fixes a countable collection `L` of infinite languages. Under arbitrary exact presentations, including points repeated infinitely often, the following are equivalent:

1. there exists a memoryless set-based generator for the collection;
2. after any single observed example `x`, a full-memory set-based generator can already output an infinite set safe for every language containing `x`;
3. equivalently, for every `x ∈ ⋃L`, the intersection
   `I_x = ⋂{K ∈ L : x ∈ K}`
   is infinite.

The necessity relies on an adversary repeating `x` infinitely often. The sufficiency uses any infinite subset of `I_x`, and can be correct from the first round.

#### (b) Closest Lean declarations

- `singletonCore H x` is exactly the common intersection of all `K ∈ H` containing `x`.
- `InfiniteSingletonCores H` requires this core to be infinite for every `x ∈ ⋃₀ H`.
- `arbitrary_memoryless_necessity` proves generatability implies infinite singleton cores under `[Countable α]`.
- `arbitrary_memoryless_sufficiency` proves the converse for arbitrary `α`.
- `theorem_3_1` states, under `[Countable α]`, `H.Countable`, and infinitude of every member,
  `ArbitraryPresentationMemorylessGeneratable H ↔ InfiniteSingletonCores H`.
- `arbitrary_success_implies_pointwise` records the stronger pointwise consequence forced by repeated-point presentations.

#### (c) Verdict

**Faithful** for the exact intersection characterization; the alternative full-memory one-example formulation is **absent as an interface**.

#### (d) Exact reason

The core set, union restriction, arbitrary-presentation quantifiers, eventual success, and pointwise amplification all match. The displayed `H.Countable` and family-wide infinitude hypotheses are redundant relative to the stronger exported component implications, but retaining them does not weaken the paper theorem. The ambient countability assumption is appropriate for constructing a repeated-point exact presentation.

The only missing part is a named full-memory one-example set-output predicate. Lean proves the equivalent core condition, so the mathematical characterization is present, but not all three paper formulations are literally represented.

#### Smallest repair

Add `OneExampleSetSafe` and the two equivalences proposed in §3.3. This does not require altering `theorem_3_1`'s mathematical proof.

### 4.3 Theorem 3.2 — necessity of set-valued output

#### (a) Paper claim

Theorem 3.2 (PDF pp. 16 and 17–18 / paper pp. 14 and 15–16) has two parts under finitely repeating exact presentations.

1. For every infinite target language `K`, no memoryless element generator `G : X → X` can eventually output a fresh point of `K` on every presentation. Freshness is with respect to all examples seen through the current round.
2. There exists a collection of two infinite languages for which no memoryless index generator succeeds. The paper uses
   `L_1 = {n : n ≡ 0 or 1 mod 4}` and
   `L_2 = {n : n ≡ 0 or 2 mod 4}`.

#### (b) Closest Lean declarations

- `ElementCorrectAt` requires `G(stream t) ∈ K` and absence from `sample stream (t+1)`, which includes the current observation.
- `IsFinitelyRepeatingElementGeneratorOn` has the paper's eventual quantifiers.
- `theorem_3_2_element` proves failure for every infinite `K` in any countable ambient type and every `G`.
- `indexLanguageZero`, `indexLanguageOne`, and `indexLanguages` are the same modular languages.
- `IsFinitelyRepeatingIndexGenerator` requires eventual containment of the output language in the target.
- `theorem_3_2_index` proves every `G : ℕ → Fin 2` fails on this family.
- `theorem_3_2` packages language infinitude and both negative clauses.

#### (c) Verdict

**Faithful**; the element clause is slightly stronger in ambient-type generality.

#### (d) Exact reason

The freshness timing is exact, the two-language witness is literal, both languages are certified infinite and incomparable, and the counterexample streams are exact and finitely repeating. Index success uses one-sided subset validity, exactly as set-based index generation requires; because the two languages are incomparable, a wrong index is invalid.

The obstruction does not rule out hidden states or synonym indices, but the paper's memoryless index model also has no persistent state and restricts outputs to the collection indices.

#### Smallest repair

No substantive repair is needed. A purely presentational package `∃ langs : Fin 2 → Set ℕ, ...` could make the existential wording match the paper, but the fixed explicit witness already proves it.

## 5. Density definitions and finite-family memoryless results

### 5.1 Definitions 8 and 9 — upper/lower density and minimax upper density

#### (a) Paper definitions

Definition 8 (PDF p. 19 / paper p. 17) lists the target `K` in the order inherited from the fixed canonical order on `X`. For any set `S`, it defines

- `μ_up(S;K) = limsup_n |S ∩ K_{≤n}|/n`;
- `μ_low(S;K) = liminf_n |S ∩ K_{≤n}|/n`.

The chosen temporal payoff is `limsup_t μ_up(G_t;K)`, meaning dense outputs need only occur infinitely often.

Definition 9 (PDF pp. 19–20 / paper pp. 17–18) defines `ρ_up^M(k)` as the supremum of `σ ∈ [0,1]` such that, for every size-`k` collection, a family-specific generator in memory model `M` both generates every target and guarantees the payoff at least `σ` for every target and permitted presentation.

#### (b) Closest Lean declarations

The exact analytic operators are present in the shared `OrderedDensity` module. The memoryless closure defines:

- `memorylessRunUpperDensity` as the outer `limsup` of inner upper densities;
- `MemorylessUpperDensityGuarantee k σ` with the family-generator-target-order-stream quantifiers;
- `memorylessAdmissibleUpperDensities k` as `[0,1]` intersected with guaranteed values;
- `memorylessMinimaxUpperDensity k` as `sSup` of that set.

Analogous definitions exist for windows and buffers.

#### (c) Verdict

The analytic definitions are **faithful**. The minimax game is **only conditionally related** because Lean makes the target order a universally quantified post-strategy input rather than deriving it from one fixed ambient order.

#### (d) Exact reason and repair

See §3.5. Once a global-order transport is added, the Lean `limsup`, admissible-set, and `sSup` machinery matches the paper exactly.

### 5.2 Lemma 4.3 — partition lower-density bound

#### (a) Paper claim

Lemma 4.3 (PDF p. 21 / paper p. 19) says: if a target `K` is partitioned inside a countable collection by finitely many infinite languages `L_1,...,L_m`, and a memoryless set generator succeeds on the collection under repetition-free presentations, then along any repetition-free presentation of `K`, after a finite time every output has lower density at most `max_i μ_low(L_i;K)`.

#### (b) Closest Lean declaration

`lemma_4_3_lower_density_bound_from_partition` takes:

- an `OrderedLanguage K`;
- a finite indexed partition `pieces` of `K.carrier`;
- infinitude of every piece;
- a generator `G`;
- repetition-free success of `G` on every piece;
- an injective exact presentation of the target.

It concludes an eventual pointwise bound by `maximumPartitionLowerDensity K pieces`.

#### (c) Verdict

**Stronger**.

#### (d) Exact reason

Lean does not require a separately represented ambient collection, success on the target `K`, or success on any languages beyond the partition pieces. Those extra paper assumptions are unnecessary for the proof's finite-bad-input mechanism. The density and stream conclusions match exactly.

#### Smallest repair

None is required. A wrapper with the paper's collection premise could be added for theorem-number fidelity, but it would only specialize the stronger lemma.

### 5.3 Lemma 4.4 — zero-lower-density partitions

#### (a) Paper claim

For any canonically ordered countably infinite target `K` and integer `m ≥ 2`, Lemma 4.4 (PDF pp. 21–22 / paper pp. 19–20) constructs a partition of `K` into `m` pairwise disjoint infinite sets, each with lower density zero in `K`.

#### (b) Closest Lean declaration

`lemma_4_4_zero_lower_density_partition` takes any `OrderedLanguage K`, `m`, and `2 ≤ m`, and returns `pieces : Fin m → Set ℕ` satisfying pairwise disjointness, exact coverage of `K.carrier`, infinitude, and lower density zero for every piece.

#### (c) Verdict

**Faithful**, and generic over the supplied target order.

#### (d) Exact reason

All promises are explicit in the conclusion. The rapidly growing block schedule is separately formalized, but effectiveness is not claimed. The only ambient restriction is `ℕ`, already covered by the missing countable-universe transport.

#### Smallest repair

Only the generic universe transport is needed.

### 5.4 Theorem 4.2 — no positive lower-density guarantee

#### (a) Paper claim

Theorem 4.2 (PDF p. 20 / paper p. 18) fixes `k ≥ 3` and asserts the existence of a size-`k` collection of infinite languages and a target `K` such that every successful memoryless set generator has eventual lower density zero on every repetition-free enumeration of `K`. Consequently, no positive `σ` is achieved infinitely often.

The quantifier order is:

1. `k ≥ 3`;
2. choose the hard collection and target;
3. for every successful generator;
4. for every repetition-free exact presentation of the target;
5. there is a threshold after which each output has lower density zero.

#### (b) Closest Lean declarations

- `zeroLowerDensityHardFamily` explicitly places the target carrier and the zero-density partition pieces into one injective finite family.
- `theorem_4_2_indexed` gives the indexed hard result.
- `theorem_4_2_no_uniform_positive_lower_density` gives the size-`k` version for every `k ≥ 3`.

The conclusion includes both eventual exact zero and the logically redundant denial of a positive frequent lower bound.

#### (c) Verdict

**Faithful in the chosen-order instance; only conditionally related to the paper's fixed-global-order formulation**.

#### (d) Exact reason

All family-size, infinitude, injectivity, generator, target, stream, and eventuality quantifiers match. The hard presentation is valid and nonvacuous. The main qualification is again that the theorem existentially supplies an `OrderedLanguage`, rather than taking the inherited order from an externally fixed ambient order. The more general Lemma 4.4 already works for any supplied target order, so the mismatch is mainly an endgame packaging issue.

#### Smallest repair

Package a theorem parameterized by an arbitrary fixed `OrderedLanguage K` (or by the ambient canonical order) and build the hard family around `K.carrier`. The existing partition lemma supplies the substantive construction.

### 5.5 Facts 4.5 and 4.6 — Sperner and symmetric-chain decomposition

#### Paper claims

- Fact 4.5 states the full Sperner theorem: the maximum antichain size in the Boolean lattice on `n` elements is `binom(n,⌊n/2⌋)`.
- Fact 4.6 states that the Boolean lattice can be partitioned into exactly that many symmetric inclusion chains.

See PDF p. 23 / paper p. 21.

#### Closest Lean declarations

The formalization contains:

- a direct middle-layer construction and the specialized antichain theorem `middleSignature_eq_of_subset`;
- a full constructive symmetric-chain framework culminating in `symmetric_chain_decomposition_range` and `symmetric_chain_decomposition_fintype`;
- a chain-count theorem `decomposition_ncard` giving the central binomial coefficient.

#### Verdict

- Full Fact 4.5: **absent as a Paper 31 declaration**, although the exact special case needed by the hard instance is present and an imported Mathlib theorem may supply more general order-theoretic infrastructure.
- Fact 4.6: **faithful and stronger in structure**, because Lean formalizes saturated symmetric chains with rank symmetry and unique coverage.

#### Smallest repair

Add a named theorem with the full maximum-antichain statement over an arbitrary finite type, either as a wrapper around the imported theorem or as a corollary of the existing decomposition. This is a packaging omission, not a gap in the main minimax proof statements.

### 5.6 Lemma 4.7 — Sperner hard instance

#### (a) Paper claim

For every `k ≥ 2`, Lemma 4.7 (PDF pp. 23–24 / paper pp. 21–22) constructs a size-`k` family and target `K` such that every successful memoryless set generator, on any repetition-free exact presentation of `K`, eventually outputs sets of upper density at most

`1 / binom(k-1, floor((k-1)/2))`.

The target is partitioned into equal-upper-density pieces indexed by the middle layer, and each side language is the union of pieces whose signatures contain its coordinate. The family is explicit, all languages are infinite and distinct, and the target presentation is valid.

#### (b) Closest Lean declarations

- `roundRobinPiece` gives explicit equal-density pieces in the identity order.
- `middleSignature` enumerates all middle-layer signatures.
- `spernerHardLanguage` and `spernerHardFamily` give the side languages and universal target.
- `spernerHardFamily_injective` and `spernerHardFamily_infinite` certify the collection promises.
- `eventually_sperner_upperDensity_bound` proves the eventual pointwise bound.
- `lemma_4_7_sperner_hard_instance` packages an ordered target, injective size-`k` family, target index, and the universal quantifiers over successful generators and injective exact presentations.

#### (c) Verdict

**Faithful for the explicit chosen order; only conditionally related to an arbitrary externally fixed canonical order.**

#### (d) Exact reason

The combinatorial construction, density value, family size, infinitude, distinctness, target validity, and quantifier order all match. Lean's conclusion is even pointwise eventual, hence stronger than merely bounding the outer run `limsup`. The only substantive mismatch is the order interface discussed in §3.5.

#### Smallest repair

Parameterize the round-robin pieces by an arbitrary inherited target enumeration rather than fixing the identity order, and state the hard instance relative to a fixed ambient order.

### 5.7 Lemma 4.8 — achievability of the Sperner bound

#### (a) Paper claim

For every finite collection of `k ≥ 2` infinite languages, there exists a memoryless set generator that generates every target under finitely repeating presentations and, on every target and presentation, achieves the reciprocal central-binomial upper density infinitely often. See PDF pp. 24–26 / paper pp. 22–24.

The generator is the canonical intersection of all languages containing the current point, with an arbitrary infinite fallback when that intersection is finite. The density proof partitions the target into relative-signature regions and uses a symmetric-chain decomposition.

#### (b) Closest Lean declarations

- `canonicalDensityGenerator` is the finite-family common-core generator with `Set.univ` fallback.
- `canonicalDensityGenerator_succeeds` proves eventual generation under finitely repeating presentations.
- relative regions, minimal infinite signatures, antichain bounds, finite envelopes, and core unions are formalized in `SpernerAchievability.lean`.
- `canonicalDensityGenerator_frequently_sperner_dense` proves the frequent density lower bound for every ordered realization and every exact presentation.
- `lemma_4_8_sperner_achievability` packages success and density.

#### (c) Verdict

**Stronger**.

#### (d) Exact reason

The Lean density guarantee is uniform over every duplicate-free order of the target, not merely the one inherited from a fixed ambient order. It also needs no finite-repetition assumption for the density recurrence itself, only for eventual validity. The canonical generator and numerical bound otherwise match exactly.

Some premises in the packaged lemma (`n ≥ 1` and family-wide infinitude) are redundant relative to separately exported component declarations, but this does not weaken the paper result.

#### Smallest repair

No mathematical repair is needed for achievability. A wrapper in the fixed-global-order model would make the interface literal.

### 5.8 Theorem 4.1 — exact memoryless minimax upper density

#### (a) Paper claim

Theorem 4.1 (PDF p. 20 and proof at pp. 23–26 / paper pp. 18 and 21–24) states, for every `k ≥ 1`,

`ρ_up^mem(k) = 1 / binom(k-1, floor((k-1)/2))`.

The lower bound is uniform over every size-`k` family, target, and finitely repeating presentation. The upper bound is witnessed by an explicit hard family. The payoff is the temporal `limsup` of per-output upper density.

#### (b) Closest Lean declarations

- `memorylessSpernerValue k` is the same reciprocal central-binomial real.
- `memorylessSpernerValue_guaranteed` and `_admissible` prove the lower bound.
- `admissibleUpperDensity_le_spernerValue` proves the upper bound.
- `memorylessAdmissibleUpperDensities_bddAbove` justifies the supremum.
- `theorem_4_1_memoryless_minimax_upper_density` proves exact equality for every `k ≥ 1`.

The family side of `MemorylessUpperDensityGuarantee` uses an injective `Fin k` family of infinite languages, which correctly represents a collection of exactly `k` distinct languages.

#### (c) Verdict

**Only conditionally related** as a literal minimax theorem, despite having the same value and correctly assembled proof interfaces.

#### (d) Exact reason

The Lean theorem computes the value of an **order-robust/adversarial-order** game: after the generator is selected, the guarantee must hold for every `OrderedLanguage` realization of each target. The upper bound may refute a candidate by choosing one convenient order. The paper fixes one ambient canonical order before the family. Equality in Lean's game gives the paper's lower bound at every fixed order, but does not by itself give the paper's upper bound for each arbitrary fixed order. Existing hard-instance components make that transport plausible, but the transport theorem is not stated.

This is not a numerical error or missing combinatorics. It is a quantifier-placement mismatch in the object being optimized.

#### Smallest repair

Define `MemorylessUpperDensityGuaranteeAtOrder` with an ambient order fixed outside the family and generator quantifiers; prove the same equality for every such order. Reuse the current order-robust achievability and parameterize the hard construction by that order.

## 6. Sliding-window memory

### 6.1 Definition 11 — window-`W` generator

#### (a) Paper definition

For `W ≥ 1` and repetition-free presentations, a window generator is a deterministic function from ordered `W`-tuples of distinct examples to infinite output sets. At round `t ≥ W`, it receives exactly `(x_{t-W+1},...,x_t)`. It has no other state. See PDF p. 26 / paper p. 24.

#### (b) Closest Lean declarations

- `DistinctWindow α W` is an injective function `Fin W → α`.
- `WindowSetGenerator α W` maps such windows to sets and proves every output infinite.
- `windowAt` forms the ordered block of consecutive stream values from a start position.
- `IsRepetitionFreeWindowGeneratorOn` requires eventual containment for every injective exact presentation.

#### (c) Verdict

**Faithful** for every positive `W`.

#### (d) Exact reason

Tuple order, distinctness, output infinitude, no persistent state, repetition-free presentations, and eventual containment all match. Lean indexes windows by start position rather than round endpoint, a harmless finite shift.

No theorem is stated for `W = 0`; the paper also defines windows only for `W ≥ 1`.

### 6.2 Lemma 4.11 — finite exceptional set for bad windows

#### (a) Paper claim

If a width-`W` generator succeeds on an infinite language under repetition-free presentations, there is a finite exceptional set `B_L ⊆ L` such that every distinct `W`-tuple drawn from `L \ B_L` yields an output contained in `L`. See PDF p. 27 / paper p. 25.

#### (b) Closest Lean declaration

`lemma_4_11_finite_exception` assumes `[Countable α]`, `W > 0`, `L.Infinite`, and repetition-free success. It returns a finite `B : Finset α`, proves every member lies in `L`, and gives the uniform safe-window conclusion for all distinct windows outside `B`.

#### (c) Verdict

**Faithful**.

#### (d) Exact reason

The conclusion is uniform over all windows and not merely windows on one stream. The adversarial construction used in the contrapositive is explicit, injective, and exactly presents `L`.

#### Smallest repair

None.

### 6.3 Lemma 4.12 — one hard instance for all finite window widths

#### (a) Paper claim

For each `k ≥ 2`, there exists one size-`k` family, one target, and one fixed repetition-free exact target enumeration such that, for every finite `W ≥ 1` and every successful width-`W` generator, all sufficiently late outputs on that fixed enumeration have upper density at most the memoryless Sperner value. The hard family, target, and presentation are chosen before `W` and the generator. See PDF pp. 28–30 / paper pp. 26–28 and Remark 4.13.

#### (b) Closest Lean declarations

- `windowSeparator`, `windowPositivePiece`, and `windowHardLanguage` define an explicit hard family.
- `windowHardFamily_injective` and `windowHardFamily_infinite` certify distinct infinite members.
- `windowHardTargetOrder` is a custom permutation order.
- the fixed hard presentation is the identity stream, certified injective and exact for the universal target.
- sparse-square geometry shows every sufficiently late consecutive window meets at most one positive piece.
- `lemma_4_12_single_hard_instance` chooses the ordered target, family, target index, stream, and injectivity proof before universally quantifying positive `W` and successful window generators.

#### (c) Verdict

**Stronger in hard-instance quantifier order, but only conditionally related in the density-order model.**

#### (d) Exact reason

The crucial quantifier order is exactly the paper's strong order. The family is explicit; all members are infinite and distinct; the identity stream is a valid repetition-free exact presentation; and the eventual density bound is correct at the statement level.

The witness differs from the paper's literal block construction: Lean moves the sparse separator into a specially chosen density order and uses the identity stream. That is a valid hard instance in Lean's model, but the theorem does not state a version relative to an arbitrary pre-fixed ambient order.

#### Smallest repair

Parameterize the construction by the fixed ambient order. One option is to formalize the paper's block enumeration directly. Another is to transport the current square/nonsquare witness through an order isomorphism and prove the transported stream remains exact and repetition-free.

### 6.4 Theorem 4.10 — exact sliding-window minimax value

#### (a) Paper claim

For every `k ≥ 1` and `W ≥ 1`,

`ρ_up^win(k,W) = 1 / binom(k-1, floor((k-1)/2))`.

A window does not improve the worst-case upper-density guarantee. The lower bound is obtained by ignoring all but the most recent example; the upper bound is Lemma 4.12. See PDF p. 27 / paper p. 25 and proof at PDF p. 30 / paper p. 28.

#### (b) Closest Lean declarations

- `WindowUpperDensityGuarantee`, `windowAdmissibleUpperDensities`, and `windowMinimaxUpperDensity` define the game and payoff.
- `canonicalWindowGenerator` lifts the memoryless canonical generator by using one position of the window.
- `canonicalWindowGenerator_succeeds` and `canonicalWindowRunUpperDensity_eq` provide the lower bound.
- `windowAdmissibleUpperDensity_le_spernerValue` provides the upper bound from the fixed hard instance.
- `theorem_4_10_window_minimax_upper_density` proves equality for `k ≥ 1` and `W > 0`.

The lifted generator uses the **first** element of the start-indexed window, whereas the paper describes using the most recent element. This changes only a finite time shift and not the theorem.

#### (c) Verdict

**Only conditionally related** as a literal minimax theorem, for the same order-quantifier reason as Theorem 4.1. Within Lean's order-robust game, the result is fully assembled and exact.

#### (d) Exact reason

All memory and stream quantifiers match. The only substantive model discrepancy is the per-target `OrderedLanguage` quantification. The construction-level first-versus-last window position is harmless but should be aligned if exact algorithmic correspondence is desired.

#### Smallest repair

First perform the fixed-global-order repair. Optionally redefine the canonical lift to use the final position of the window and prove equality after the corresponding finite shift.

## 7. Adaptive buffers of chosen examples

### 7.1 Definition 12 — `b`-buffer set generator

#### (a) Paper definition

For capacity `b`, the persistent state is an ordered tuple of at most `b` examples. From the previous tuple and the current example, the learner computes both its infinite set output and its next tuple. Every entry of the next tuple must be either an old stored example or the current example; the learner may keep, discard, reorder, or replace entries. The buffer is the only persistent state. The paper restricts the density theorem to repetition-free presentations. See PDF p. 31 / paper p. 29.

#### (b) Closest Lean declarations

- `BufferState α b` is a list with length at most `b`.
- `BufferSetGenerator` contains `output`, global output infinitude, `update`, and `update_supported`.
- `update_supported` requires every updated entry to occur in the old list or equal the current input.
- `bufferState` starts empty and updates causally.
- `bufferOutputAt` uses the previous state and current input.
- `IsRepetitionFreeBufferGeneratorOn` quantifies injective exact presentations and eventual containment.

#### (c) Verdict

**Faithful** as a bounded-number-of-example-tokens model.

#### (d) Exact reason

The support condition, capacity, timing, no-synthesis promise, no extra persistent state, and presentation regime match. Neither source bounds the bit length of an example. Lean also permits duplication of stored entries; the paper's tuple definition does not prohibit duplicates, so this is not a mismatch.

The whole language family can be hard-coded into the static transition/output functions. This is also consistent with the paper's semantic, family-specific algorithms, though not with a machine-level space bound on program description.

### 7.2 The greedy residual construction

The paper's proof of Theorem 4.15 stores a current example exactly when the buffer is not full and the example strictly shrinks the residual set of compatible languages. Once the buffer stabilizes, either it is not full and every residual language contains the target, yielding density one, or it is full and the residual family has size at most `k-b`, allowing the memoryless Sperner guarantee.

The following Lean declarations reproduce and assemble this logic:

- `bufferResidual`, `bufferResidualAfter`, and `ShouldStore`;
- `greedyBufferUpdate` and `greedyBufferGenerator`;
- `greedyBufferState_eventually_constant`;
- `greedyBuffer_residual_length_bound`, giving `card residual + buffer length ≤ k`;
- target-preservation and residual-antitonicity lemmas;
- padded residual family declarations linking the stabilized buffer output to `canonicalDensityGenerator`;
- `greedyBuffer_frequently_sperner_dense_of_residual_card_le` for the full-buffer branch;
- the stable nonfull branch culminating in eventual density one.

No helper assumption is left unclosed in the main lower-bound theorem. The stabilization time and residual-cardinality facts are proved for the displayed greedy generator rather than supplied as unexplained endgame hypotheses.

### 7.3 Theorem 4.15 — adaptive-buffer lower bound

#### (a) Paper claim

For every finite collection size `k` and buffer capacity `b ≥ 0`, Theorem 4.15 (PDF pp. 31–33 / paper pp. 29–31) proves

`ρ_up^buf(k,b) ≥ 1 / binom(k-b-1, floor((k-b-1)/2))`

when `0 ≤ b ≤ k-3`, and `ρ_up^buf(k,b) ≥ 1` when `b ≥ k-2`. Since density is at most one, the high regime has value one. The paper claims only a lower bound in the low regime, not a matching upper bound.

The quantifier order is:

1. fix `k,b`;
2. for every size-`k` finite collection of infinite languages;
3. choose one family-specific `b`-buffer generator;
4. for every target and repetition-free exact presentation;
5. obtain eventual validity and a temporal `limsup` upper-density payoff at least the stated value.

#### (b) Closest Lean declarations

- `BufferUpperDensityGuarantee k b σ` has the corresponding family-generator-target-order-stream order.
- `adaptiveBufferLowerValue k b` is the same piecewise formula, using natural-number truncated subtraction.
- `adaptiveBuffer_low_regime_guaranteed` and `adaptiveBuffer_high_regime_guaranteed` prove the two branches.
- `adaptiveBufferLowerValue_admissible` puts the value in the admissible set.
- `theorem_4_15_adaptive_buffer_lower_bound` proves
  `adaptiveBufferLowerValue k b ≤ bufferMinimaxUpperDensity k b`
  for every `k ≥ 1` and every `b`.

#### (c) Verdict

**Stronger on density-order robustness, weaker on universe generality; substantively faithful.**

#### (d) Exact reason

Because this is a positive lower bound, requiring the same generator to work for every ordered realization is a genuine strengthening and therefore implies the paper's bound for any fixed order. The buffer semantics, formula, family size, presentations, and output model match. The restriction to `ℕ` remains.

The natural-subtraction branch test behaves differently syntactically for tiny `k`, but both branches evaluate to one there, so there is no numerical mismatch.

#### Smallest repair

Add the arbitrary-countable-universe transport and a fixed-order wrapper. No upper-bound theorem should be added merely for symmetry: the paper does not claim one in the low regime.

## 8. Last-guess incremental identification

### 8.1 Definitions 13–15 — incremental learner and approximate identification

#### (a) Paper definitions

An incremental learner has output/state space `Ω`, initial state `ω_0`, and update `A : Ω × X → Ω`. It receives only its previous output and the current example. For a finite indexed collection, the paper sets `Ω = {1,...,N}` and explicitly forbids extra hidden states, synonym indices, or hypotheses outside the collection. See Definition 13, PDF pp. 33–34 / paper pp. 31–32.

Almost-containment is `A ⪯_F B` iff `A \ B` is finite. Almost-equivalence is finite symmetric difference. Approximate identification requires that, for every exact presentation of target `K`, all sufficiently late output languages are almost-equivalent to `K`. See Definitions 14 and 15, PDF p. 34 / paper p. 32.

#### (b) Closest Lean declarations

- `IncrementalLearner α ι := ι → α → ι`;
- `incrementalRun` with state `0` equal to the initial state and state `t+1` after processing `stream t`;
- `AlmostContained`, `AlmostEquivalent`, and `StrictAlmostContained`;
- `ApproximatelyIdentifiesRun`;
- `IncrementallyApproximatelyIdentifiable`.

For finite families the index/state type is exactly `Fin (N+1)`. Arbitrary repetitions are allowed because only exact presentation is assumed.

#### (c) Verdict

**Faithful**.

#### (d) Exact reason

The state is exactly the previous guess, the update is causal, no time counter or separate memory is present, and the approximate conclusion is finite symmetric difference rather than one-sided containment. The transition may be noncomputable because arbitrary language membership is hard-coded, but the paper makes no effectiveness claim.

### 8.2 Proposition 5.1 — exact identification fails for three languages

#### (a) Paper claim

Proposition 5.1 (PDF pp. 34–36 / paper pp. 32–34) uses

- `C = {3n : n ∈ ℕ}`;
- `L_1 = C ∪ {1}`;
- `L_2 = C ∪ {2}`;
- `L_3 = C ∪ {1,2}`.

It states that no incremental index learner with exactly these three output states identifies the collection under arbitrary positive presentations; in fact the impossibility already holds under finitely repeating presentations. The hard texts are exact and repeat the distinguished points only finitely many times.

#### (b) Closest Lean declarations

- `ExactlyIdentifiesRun` requires eventual equality to the target index.
- `IncrementallyExactlyIdentifiableOnFinitelyRepeating` quantifies one learner and initial index, then every target and finitely repeating exact presentation.
- `exactObstructionCore`, `exactObstructionCoreStream`, and `exactObstructionLanguages` are the literal paper sets.
- separate declarations certify core infinitude, stream injectivity/exactness, language infinitude, and family injectivity.
- `proposition_5_1` concludes the family is not incrementally exactly identifiable on finitely repeating presentations.

#### (c) Verdict

**Faithful and stronger in presentation regime**.

#### (d) Exact reason

Failure on the restricted finitely repeating class implies failure when arbitrary presentations are allowed. The state/output space is exactly `Fin 3`, matching the paper's representation-sensitive model. The counterexample family and finite prefixes are literal and all promises are stated.

The theorem does not rule out four states, synonym indices, or hidden natural-valued memory. Neither does the paper proposition.

#### Smallest repair

None.

### 8.3 Theorem 5.2 — approximate identification of every finite collection

#### (a) Paper claim

Theorem 5.2 (PDF pp. 35–37 / paper pp. 33–35) states:

1. fix any finite collection `L = {L_1,...,L_N}` of infinite languages;
2. choose a topological ordering of the strict almost-containment relation `A ≺_F B`;
3. there exists an incremental index learner, with only the previous index as persistent state;
4. for every target and every exact presentation, repetitions unrestricted;
5. all sufficiently late output languages are almost-equivalent to the target.

The displayed learner starts at the first index, stays if the current example belongs to its current hypothesis, and otherwise advances by one, capped at `N`.

#### (b) Closest Lean declarations

- `AlmostOrder`, `almostOrderIso`, `relabeledIndex`, and `topologicallyRelabeled` construct a noncomputable linear extension.
- `relabeledIndex_bijective` and `range_topologicallyRelabeled` show it is a genuine reindexing with the same represented set range.
- `orderedIncrementalLearner` is the stay-or-advance update.
- monotonicity, one-step adjacency, target absorption, and finite-state stabilization are separately stated.
- `theorem_5_2_ordered` proves approximate identification for any family satisfying the supplied topological-order property.
- `theorem_5_2` says that for every `raw : Fin (N+1) → Set α` of infinite languages, there exists `langs` with `Set.range langs = Set.range raw` and `IncrementallyApproximatelyIdentifiable langs`.

#### (c) Verdict

**Faithful at the paper's extensional collection level; weaker at the literal input-index interface.**

#### (d) Exact reason

The paper treats a finite collection as something that may be enumerated in the chosen topological order. Lean's existential relabeling therefore captures the paper-level claim. The actual displayed relabeling is bijective and has the correct order.

However, the final theorem does not state `IncrementallyApproximatelyIdentifiable raw`; it states the property only for some equal-range family. Since the learner state/output is an index, the property is representation-sensitive. A conjugation through the bijection is required to return a learner on the original index set, and that transport theorem is not packaged.

The family-wide infinitude hypothesis is syntactically present but unused by the ordered argument. This is harmless source-faithful redundancy, not circularity.

The paper's Observation 5.3 is separately represented by `ordered_run_target_absorbing`. Claims 5.4 and 5.5, the two directions of eventual almost-containment between the stabilized hypothesis and target, are not packaged as separate public declarations in the Stage 1 ledger; their conjunction is delivered by `theorem_5_2_ordered`. This is an assembly choice, not a missing end-to-end conclusion.

#### Smallest repair

Prove a reindexing invariance theorem for incremental approximate identification under a finite equivalence of index types, then derive:

```lean
theorem theorem_5_2_raw
    (raw : Fin (N + 1) → Set α)
    (hInfinite : ∀ i, (raw i).Infinite) :
    IncrementallyApproximatelyIdentifiable raw
```

by conjugating the ordered learner through `relabeledIndex_bijective`.

### 8.4 Countable-family extension and weak Angluin obstruction

The paper remarks that the proof extends to some countable families when the strict almost-containment order has a topological enumeration with only finitely many predecessors per target, and that violation of the weak Angluin condition blocks approximate identification even with full information (PDF p. 35 / paper p. 33).

No Stage 1 declaration states either extension or obstruction.

**Verdict:** **absent**.

**Smallest repair.** Add a countable indexed-order interface with a finite-predecessor condition and state the incremental theorem under it. The weak-Angluin obstruction requires importing or formalizing that condition and a full-information impossibility result; it is not a small corollary of the current finite proof.

## 9. Appendix A — further results on incremental generation

### 9.1 Theorem A.1 and Proposition A.2 — exact index-generation obstruction

#### (a) Paper claims

Theorem A.1 says there exists a collection of three infinite languages not exactly identifiable by any incremental index learner. Proposition A.2 proves the stronger generation obstruction for the explicit triangle family: for distinct `a,b,c` outside an infinite set `T`,

- `L_1 = T ∪ {a,b}`;
- `L_2 = T ∪ {a,c}`;
- `L_3 = T ∪ {b,c}`.

No incremental index generator with exactly three persistent/output states can eventually output a language contained in the target on all presentations; the impossibility already uses finitely repeating presentations. See PDF pp. 42–43 / paper pp. 40–41.

#### (b) Closest Lean declarations

- `IncrementalIndexGeneratesRun` and `IncrementallyIndexGenerableOnFinitelyRepeating` formalize one-sided index-output validity with state equal to output index.
- `appendixTriangleLanguages` is the literal triangle family.
- `appendixTriangleLanguages_infinite` and `_antichain` certify all promises.
- `proposition_A_2` states failure of incremental index generation under finitely repeating exact presentations.
- `theorem_A_1_triangle` converts this to exact-identification failure.
- `theorem_A_1` packages an explicit existential `Fin 3` family over `ℕ`, with injectivity and infinitude.

#### (c) Verdict

**Faithful and stronger in presentation regime**.

#### (d) Exact reason

The family is explicit, its members are infinite and pairwise inclusion-incomparable, the state space is exactly the three indices, and the adversarial texts are exact and finitely repeating. The antichain conversion from one-sided generation to exact index convergence is stated separately and correctly limits the scope of the obstruction.

#### Smallest repair

None.

### 9.2 Lemma A.3 — disjoint infinite cofinal subsets

#### (a) Paper claim

For every finite collection of infinite languages over the canonically ordered universe, there exist subsets `C_i ⊆ L_i` that are infinite, pairwise disjoint, and cofinal in the canonical order. See PDF p. 44 / paper p. 42.

#### (b) Closest Lean declarations

The codebook module defines `elementCodingCell langs hInfinite i` and proves separately:

- `elementCodingCell_infinite`;
- `elementCodingCell_subset`;
- `elementCodingCell_pairwiseDisjoint`;
- `elementCodingCell_cofinal`.

The underlying `elementCode` construction is stronger than Lemma A.3: it injectively allocates codewords for the full triple `(language index, complete history, salt)`, not only empty-history cells.

#### (c) Verdict

**Faithful jointly, but not packaged as the paper's existential lemma**.

#### (d) Exact reason

Every promised property is present for a concrete family of cells. The restriction to `ℕ` is the only mathematical narrowing. There is no circularity: cell membership is derived from the global code allocation and family infinitude.

#### Smallest repair

Add a short wrapper:

```lean
theorem lemma_A_3
    (langs : Fin (N + 1) → Set ℕ)
    (hInf : ∀ i, (langs i).Infinite) :
    ∃ C : Fin (N + 1) → Set ℕ,
      (∀ i, (C i).Infinite ∧ C i ⊆ langs i) ∧
      Pairwise (Disjoint on C) ∧
      ∀ i x, ∃ y ∈ C i, x < y
```

and later transport it to arbitrary countable ordered universes.

### 9.3 Theorem A.4 — coding compilation

#### (a) Paper claim

Fix a finite collection of infinite languages and a full-information index learner `M`. Assume that for every target and every exact presentation, the hypotheses output by `M` are eventually almost-contained in the target. Then there exists an incremental element generator whose previous output and current example are its only formal inputs, and whose outputs eventually lie in `K \ S_t`. The previous output encodes the entire observed prefix. See PDF pp. 45–46 / paper pp. 43–44.

The quantifier order is:

1. fix the collection and full-information learner `M`;
2. assume one uniform semantic property of `M` over every target and presentation;
3. construct one incremental element generator for the entire collection;
4. for every target and presentation, obtain eventual fresh target outputs.

#### (b) Closest Lean declarations

- `FullInformationIndexLearner N := List ℕ → Fin (N+1)`;
- `EventuallyAlmostContainedHypotheses langs M` has the exact target-stream-eventual quantifiers;
- `IncrementalElementGeneratesRun` requires the state after `t` processed inputs to lie in the target and outside the range of the first `t` inputs;
- `IncrementallyElementGenerable` quantifies one natural-state learner and initial state for all targets and exact presentations;
- `codingCompiledGenerator` decodes the prior state into the full prior history, appends the current input, evaluates `M`, and returns a fresh language-respecting codeword above both old state and input;
- `codingCompiled_run_is_code` explicitly states that every run state stores the exact complete history and current hypothesis;
- `incremental_coding_compilation` proves the end-to-end conditional theorem.

#### (c) Verdict

**Faithful on `ℕ`; weaker in arbitrary-countable-universe generality.**

#### (d) Exact reason

The premise, output freshness, causal arity, codebook behavior, family uniformity, and absence of a finite-repetition restriction all match. The theorem is intentionally not a finite-bit memory result: the natural-valued output/state is an unbounded code. This is exactly the caveat emphasized by the paper, not a hidden loophole introduced by Lean.

The full-information learner is a substantive supplied witness and does much of the learning work, but Theorem A.4 is explicitly conditional in the paper. The next theorem closes this condition.

#### Smallest repair

Add a transport theorem for an arbitrary countably infinite universe equipped with a canonical ordering and an encoding of finite histories into cofinal codewords. No change to the conditional structure is appropriate.

### 9.4 Theorem A.5 — incremental element generation for every finite collection

#### (a) Paper claim

Every finite collection of infinite languages admits an incremental element generator. This follows by applying Theorem A.4 to the approximate-identification learner from Theorem 5.2. The paper warns that the result does not represent a meaningful bounded-information model because the last output stores the full history. See PDF p. 46 / paper p. 44.

#### (b) Closest Lean declarations

- `incremental_element_generation_of_approximate_identification` converts approximate identification to the one-sided premise needed by the compiler.
- `incrementallyElementGenerable_of_range_eq` transports element generation across equal set ranges.
- `incremental_element_generation` concludes that every `Fin (N+1)` family of infinite subsets of `ℕ` is incrementally element-generable on all exact presentations.

#### (c) Verdict

**Faithful on `ℕ`; weaker in universe generality.**

#### (d) Exact reason

The helper chain is assembled end to end: the full-information premise is not left assumed in the final theorem. The equal-range transfer compensates for Theorem 5.2's relabeling. The resulting learner is target-independent and family-specific. Its natural state/output encodes unbounded information, exactly as the paper says.

#### Smallest repair

Add the generic ordered-countable transport. No finite-state strengthening should be claimed without changing the theorem's mathematics.

## 10. Memory and access model comparison

| Model | Paper runtime information | Lean runtime information | Is the persistent state genuinely finite? | Statement-faithfulness assessment |
|---|---|---|---|---|
| Full-history element generator | entire finite observed prefix | generic dependency function on a finite sequence | no | Element-valued dependency interface exists, but the paper's full-history set/index interfaces are absent. |
| Memoryless set generator | current example only; output always an infinite set | current example only; output is a raw set, eventual validity includes infinitude | no persistent state; static function may encode the whole family | No-history access is faithful; codomain is slightly weaker than paper. |
| Memoryless element generator | current example only | current example only | no persistent state | Faithful. Freshness includes the current example. |
| Memoryless index generator | current example only; output one family index | current example only; output `ι` | no persistent state | Faithful. |
| Sliding window `W` | ordered last `W` examples; no other state | ordered injective `Fin W` tuple; no other state | `W` example tokens, but unbounded bits per token | Faithful for repetition-free streams. |
| Adaptive buffer `b` | at most `b` chosen past examples plus current example | list of length at most `b` plus current example; update may retain old/current values | `b` example tokens, not bounded bits | Faithful. Lean and paper permit unbounded-information examples. |
| Incremental index learner | previous output index and current example; no extra states | previous `Fin N` index and current example | yes, exactly `N` states, ignoring static program description | Faithful and genuinely finite-state at the dynamic-state level. Transition may be noncomputable. |
| Incremental element generator | previous output element and current example | previous natural output/state and current natural input | no; state space is countably infinite and encodes full history | Faithful to Appendix A's deliberately collapsing model, not to bounded-bit memory. |
| Density evaluator | one global ambient canonical order fixed before the family | arbitrary target-specific `OrderedLanguage` supplied after strategy choice | not runtime state | Material quantifier/model mismatch; needs P0 repair. |
| Family access | constructions assume full semantic access to collection | family is hard-coded into arbitrary functions and noncomputable predicates | static description unbounded | Faithful to the paper's semantic level, not an effective algorithm. |

### 10.1 Precise answer to the “memory bound” question

- **Memoryless Lean generators are true no-history interfaces:** their dynamic input is only the current example. They are not bounded-description or computable machines; the function itself may encode the entire family and semantic answers about arbitrary sets.
- **Window and buffer bounds are counts of stored example tokens, not bit bounds.** A natural number or arbitrary element may carry unbounded information. This is exactly the coarser memory notion the paper distinguishes from space-efficient bit models.
- **Incremental index learners are genuinely finite-state dynamically** because the only state is one of the `N` output indices. The negative three-language results depend essentially on this exact state restriction.
- **Incremental element learners are not finite-state.** Lean explicitly proves that the previous natural output losslessly records the complete observed history. This is an intentional answer/history-encoding channel, fully aligned with Appendix A.

## 11. Link-code, supplied-witness, and hidden-assumption audit

| Declaration or interface | Supplied premise/witness | What it contributes | Risk assessment |
|---|---|---|---|
| `theorem_1_1` | `H.Countable`; every member infinite | noncomputable enumeration of the family; nonvacuous infinite outputs | Essential semantic assumptions, not circular. No effective enumeration is produced. |
| `selectedDepth` | current natural `x`; semantic infinitude tests | uses `x` as a numerical depth bound and selects the deepest infinite prefix core | Representation-sensitive and noncomputable. The paper's footnote makes the same natural-number identification. |
| `theorem_3_1` | `H.Countable`; all members infinite | source-faithful hypotheses | Redundant relative to exported necessity/sufficiency components; no hard work is hidden in them. |
| `InfiniteSingletonCores` | direct core-infinitude condition | exactly the combinatorial characterization | Not tautological: it is an extensional family condition, not success restated. |
| `canonicalDensityGenerator` | complete finite family hard-coded | computes the intersection of all languages containing the current point | Family access and infinitude tests are semantic/noncomputable, matching the paper's abstraction. |
| `OrderedLanguage` in minimax guarantees | target carrier, injective enumeration, exact-range proof | supplies the density order to the evaluator | Generator does not receive it. Universal post-strategy quantification changes the minimax game. |
| `hTopo` in `theorem_5_2_ordered` | strict almost-containment implies increasing indices | makes the stay-or-advance learner sound | It does the structural work, but the main theorem constructs it through a linear extension; no circularity remains. |
| `theorem_5_2` equal-range family | existential relabeling | allows topological ordering of a collection | Paper-level faithful, but original-index learner transport is unassembled. |
| `EventuallyAlmostContainedHypotheses` in coding compilation | a full-history learner `M` with one-sided eventual correctness | supplies the learning content needed by Theorem A.4 | Substantive but explicitly conditional in the paper. Theorem A.5 closes it using Theorem 5.2. |
| `elementCode`/`decodeElementCode` | family infinitude and noncomputable global allocation | codewords lie in named languages and encode `(index,history,salt)` | Deliberate answer/history encoding; not bounded memory. Not hidden because run-code theorem exposes it. |
| `incrementallyElementGenerable_of_range_eq` | exact equality of family ranges | transfers the same generator to a different indexing | Uses classical choice of a representing index only in the proof/evaluator; no target advice is passed at runtime. |
| `lemma_4_11_finite_exception` | success on every repetition-free presentation | extracts a finite bad set uniform over all windows | Genuine compactness consequence; main window theorem uses it, not assumes it without closure. |
| buffer stabilization lemmas | displayed greedy update and finite capacity | prove finite store times and bounded residual size | Fully assembled into Theorem 4.15; not an unproved diagnostic condition. |
| stable nonfull buffer branch | stabilization and nonfull final state | yields residual languages containing the target and density one | The main theorem proves the branch conditions by case analysis. |
| exact-identification obstructions | state/output type exactly `Fin 3` | creates a four-prefix/three-state contradiction | Essential representation assumption, explicitly matching the paper. Does not cover larger hidden-state models. |
| injective `Fin k` families in minimax theorems | distinctness of indexed languages | represents a collection of cardinality exactly `k` | Appropriate, not an extra promise beyond “collection of size `k`.” |

### 11.1 Vacuity

Headline theorems quantify infinite languages, so their exact finitely repeating or injective presentations exist in the countable setting and the main results are nonvacuous. Some helper declarations omit language infinitude; for a finite target, no injective or finitely repeating exact infinite stream exists, so those helper success obligations can be vacuous. This does not infect the headline results because the minimax families and paper collections are explicitly infinite-language families.

### 11.2 Circularity and tautology

No primary axiom is introduced. No headline conclusion simply repeats an assumption. The notable redundancies are:

- the countability/infinitude premises in the displayed Theorem 3.1 are stronger than the separate necessity/sufficiency declarations need;
- the infinitude premise in Theorem 5.2 is unused by the ordered approximate-identification argument;
- the “no positive frequent lower density” clause in the Lean Theorem 4.2 follows from its stronger eventual-zero clause;
- some packaged density lemmas carry premises omitted by stronger component declarations.

These are interface redundancies, not circular proofs or answer-encoding hypotheses.

### 11.3 Target-dependent advice

No main positive generator or learner receives the target index at runtime. It is selected for the whole family before the adversary chooses the target. Thresholds may depend on target and presentation, as in the paper. The codebook and topological order are family-dependent, not target-dependent. Density orders are evaluator inputs, not generator advice.

### 11.4 Rates, randomness, and runtime

No declaration supplies a convergence rate, sample threshold bound, update-time bound, query bound, random bits, probability space, expected payoff, or high-probability guarantee. All results are deterministic semantic eventuality statements. This matches the paper's theorem level.

## 12. Introductory theorem-number crosswalk

The arXiv v1 introduction uses informal headline labels in addition to the formal section labels:

- **Informal Theorem 1.2(1)** is formal Theorem 4.1, the exact memoryless minimax value.
- **Informal Theorem 1.2(2)** is formal Theorem 4.10, the exact sliding-window value.
- **Informal Theorem 1.2(3)** is formal Theorem 4.15, an adaptive-buffer lower bound, not an exact low-regime characterization. Lean preserves this distinction and does not overclaim an equality.
- **Theorem 1.3** is the introductory form of formal Theorem 5.2. The Lean comparison in §8.3 therefore covers both labels.

There is no unresolved theorem-number drift in the attached v1.

## 13. Main-result verdict table

| Paper result | Closest Lean declaration(s) | Verdict | Core reason |
|---|---|---|---|
| Theorem 1.1: every countable collection of infinite languages has a memoryless set generator under finitely repeating presentations | `theorem_1_1`, `theorem_1_1_enumerated`, `finitelyRepeatingGenerator_succeeds` | **Weaker** | Exact success quantifiers, but fixed to `ℕ`; base set-output type is not globally infinite. |
| Theorem 3.1: arbitrary-repetition characterization by infinite singleton intersections | `singletonCore`, `InfiniteSingletonCores`, `arbitrary_memoryless_necessity`, `_sufficiency`, `theorem_3_1` | **Faithful** | Exact equivalence and pointwise amplification. The full-memory one-example formulation is not separately defined. |
| Theorem 3.2, element part | `ElementCorrectAt`, `theorem_3_2_element` | **Faithful / stronger genericity** | Exact freshness through current round; works over any countable ambient type. |
| Theorem 3.2, index part | modular hard languages, `theorem_3_2_index`, `theorem_3_2` | **Faithful** | Literal two-language witness, exact finitely repeating presentations, correct containment output model. |
| Lemma 4.3 | `lemma_4_3_lower_density_bound_from_partition` | **Stronger** | Needs success only on partition pieces, not an ambient collection or target. |
| Lemma 4.4 | `lemma_4_4_zero_lower_density_partition` | **Faithful** | Exact partition, infinitude, disjointness, coverage, and zero lower density. |
| Fact 4.5, full Sperner theorem | specialized middle-layer declarations | **Absent as full statement** | The exact special antichain consequence needed by the hard instance is present. |
| Fact 4.6, symmetric-chain decomposition | `symmetric_chain_decomposition_range`, `_fintype` | **Faithful / stronger structure** | Full saturated symmetric decomposition and exact chain count. |
| Lemma 4.7 | Sperner hard-family declarations, `lemma_4_7_sperner_hard_instance` | **Faithful for chosen order; conditionally related globally** | Explicit valid hard family and presentation; order is selected rather than inherited from a fixed ambient order. |
| Lemma 4.8 | canonical generator and `lemma_4_8_sperner_achievability` | **Stronger** | Same generator and value, with density guarantee for every target ordering. |
| Theorem 4.1 | `theorem_4_1_memoryless_minimax_upper_density` | **Only conditionally related** | Same exact value, but computes an adversarial/order-robust minimax game rather than the fixed-global-order game. |
| Theorem 4.2 | `theorem_4_2_no_uniform_positive_lower_density` | **Faithful for chosen order; conditionally related globally** | Exact hard family and eventual-zero conclusion; main theorem existentially chooses the order. |
| Lemma 4.11 | `lemma_4_11_finite_exception` | **Faithful** | Uniform finite exceptional set over all distinct windows outside it. |
| Lemma 4.12 | window hard-family declarations, `lemma_4_12_single_hard_instance` | **Stronger quantifier order; conditionally related on order** | Hard family, target, and stream fixed before `W` and generator; custom order differs from paper's fixed ambient order. |
| Theorem 4.10 | `theorem_4_10_window_minimax_upper_density` | **Only conditionally related** | Exact value and window model, but same density-order game mismatch as Theorem 4.1. |
| Theorem 4.15 | adaptive-buffer guarantee declarations, `theorem_4_15_adaptive_buffer_lower_bound` | **Substantively faithful / stronger on order** | Exact buffer semantics and piecewise lower bound; one generator works for every target order; fixed to `ℕ`. |
| Proposition 5.1 | obstruction family and `proposition_5_1` | **Faithful / stronger presentation restriction** | Literal family; failure already on finitely repeating presentations; exactly three states. |
| Theorem 5.2 | topological relabeling, `theorem_5_2_ordered`, `theorem_5_2` | **Faithful extensionally; weaker on raw indexing** | Equal-range relabeling matches a collection, but final theorem does not conjugate the learner back to `raw`. |
| Theorem A.1 | `theorem_A_1_triangle`, `theorem_A_1` | **Faithful / stronger presentation restriction** | Explicit three-language obstruction under finitely repeating presentations. |
| Proposition A.2 | `appendixTriangleLanguages`, `proposition_A_2` | **Faithful** | Exact triangle, antichain promise, and three-state index-generation failure. |
| Lemma A.3 | `elementCodingCell_*` declarations | **Faithful jointly; unbundled** | All properties present for a concrete code-cell family; no single existential wrapper. |
| Theorem A.4 | `EventuallyAlmostContainedHypotheses`, `incremental_coding_compilation` | **Faithful on `ℕ`; weaker universe** | Exact conditional compiler and explicit full-history encoding in last output. |
| Theorem A.5 | `incremental_element_generation_of_approximate_identification`, `incremental_element_generation` | **Faithful on `ℕ`; weaker universe** | Conditional premise is closed end to end using approximate identification. |

## 14. Omissions and unassembled claims

| Paper statement or aspect | Lean status | Significance | Minimal repair |
|---|---|---|---|
| Full-history set- and index-valued generation interface from Definition 5 | Absent | Prevents literal formalization of all baseline output models and the first formulation of Theorem 3.1 | Add full-history set/index generator types and success predicates. |
| One-example full-memory formulation in Theorem 3.1 | Equivalent core condition present, interface absent | Mathematical result is present but one advertised equivalence is not | Define `OneExampleSetSafe` and prove equivalence. |
| One global ambient canonical order inherited by every target | Replaced by target-specific `OrderedLanguage` quantification | Changes the minimax game and hard-instance quantifiers | P0 fixed-order interface and transport. |
| Arbitrary countable universe for Theorem 1.1, density, windows, buffers, and appendix coding | Mostly fixed to `ℕ` | Narrows headline scope and leaves representation dependence untransported | Generic countable transport theorems. |
| Direct approximate-identification theorem for the input indexed family | Only equal-range relabeling is concluded | Paper is extensional, but literal indexed theorem is missing | Conjugate learner through the relabeling bijection. |
| Remark 4.9: no positive uniform upper-density guarantee for countable collections | No end-to-end declaration found in Stage 1 | One of the paper's finite-versus-countable conclusions is missing | Define a countable-family guarantee and formalize the disjoint-union hard construction. |
| Formal definitions/results for the other three temporal density aggregates | Only the chosen `limsup_t μ_up` payoff and a lower-density obstruction are developed | Paper discusses collapse of the other aggregates, but Lean does not package the full four-way comparison | Add the three payoffs and corresponding zero-guarantee theorems. |
| Countable-family approximate identification under finite-predecessor topological orders | Absent | Paper records a beyond-finite extension | Add a countable order and finite-predecessor theorem. |
| Weak Angluin obstruction for approximate identification | Absent | Paper cites it as the opposite extreme | Import/formalize the condition and full-information obstruction. |
| Full Sperner maximum-antichain fact | Only needed special consequence present | No gap in the main bound, but a numbered paper fact is not mirrored | Add a wrapper theorem. |
| Lemma A.3 as one packaged existential theorem | Components present | Low risk; all mathematical content is available | Add a wrapper. |
| Explicit strict-improvement corollary comparing buffer and memoryless values | Formulae present, no named comparison theorem identified | Paper emphasizes adaptive chosen examples strictly improve the guarantee in relevant regimes | Prove arithmetic comparison with precise `k,b` side conditions. |
| Machine-level bit memory, computability, runtime, query complexity, convergence rates, randomization | Intentionally absent | Not a paper theorem; must not be inferred from semantic statements | Optional future refinement only, clearly separated from faithfulness repairs. |

## 15. Prioritized repair backlog

### P0 — required for literal headline-statement fidelity

1. **Fix the density-order quantifier model.**
   - Add one ambient canonical-order parameter outside the family and strategy quantifiers.
   - Derive target orders by restriction/filtering.
   - Restate and prove Theorems 4.1, 4.2, 4.10, and 4.15 in that fixed-order model.
   - Parameterize hard families by the fixed order or provide a transport theorem.

2. **Transport all `ℕ`-specific headline theorems to arbitrary countable universes.**
   - At minimum: Theorem 1.1, Theorems 4.1/4.2/4.10/4.15, and Theorems A.4/A.5.
   - The transport must preserve exact presentations, finite repetition/injectivity, output infinitude, freshness, and density under the transported order.

3. **State Theorem 5.2 directly on the input indexing.**
   - Prove invariance of incremental approximate identification under a finite index equivalence.
   - Conjugate the topologically ordered learner back to `raw`.

4. **Make memoryless set output intrinsically infinite.**
   - Use an infinite-set subtype or a structure with a global infinitude field.
   - Reconcile all memoryless success and minimax interfaces with the paper's codomain `[X]^∞`.

### P1 — important completeness and paper-map repairs

1. Add full-history set/index generator interfaces and the one-example full-memory equivalence for Theorem 3.1.
2. Package Lemma A.3 as a single existential result.
3. Formalize Remark 4.9 for countable collections.
4. Add the other three temporal density aggregates and the paper's zero/collapse conclusions.
5. Add the countable finite-predecessor extension of Theorem 5.2, if it is intended as a formal claim rather than discussion.
6. Add the full Sperner theorem as a named paper-facing declaration.

### P2 — alignment, diagnostics, and optional refinements

1. Change the canonical window lift to use the most recent entry, matching the paper's displayed construction, and prove the finite-shift equality.
2. Add explicit corollaries comparing adaptive-buffer and memoryless guarantees, with exact arithmetic side conditions.
3. Remove or document redundant hypotheses and redundant endgame conjuncts without weakening source-facing wrappers.
4. Add empty-collection wrappers where “every finite collection” is intended to include the empty set.
5. Add optional effective/oracle versions only as new theorems with explicit representation, decidability, query, and resource assumptions. Do not retrofit machine-level claims onto the current semantic declarations.

## 16. Overall verdict

### Verdict: **mostly faithful with qualifications**

The Lean statements capture the paper's central mathematical landscape and almost all numbered principal results. In particular, the exact presentation regimes, memoryless/no-history interface, distinct-window and chosen-buffer models, finite-state last-guess learner, output-type separations, singleton-core condition, almost-containment order, Sperner value, and appendix coding collapse are all represented with substantial precision. The main conditional constructions are assembled into end-to-end theorems rather than left as disconnected diagnostics.

The formalization is not fully faithful because two model-level issues affect literal theorem meaning: the density order is quantified differently, and a significant portion of the development is specialized to `ℕ` without a transport theorem. The final Theorem 5.2 also stops at an equal-range relabeling rather than stating the indexed input-family conclusion. These are concrete, repairable statement/interface gaps; they do not indicate that the core combinatorial or learning-theoretic content is absent.

The memory audit does **not** reveal a hidden claim of bounded-bit computation. Memoryless, window, buffer, and index-incremental models constrain dynamic access exactly as the paper describes, while static functions may encode the whole family. The incremental element appendix intentionally uses an unbounded natural output as a full-history code, and Lean exposes that fact explicitly. Thus the largest “answer-encoding” phenomenon is faithful to the paper rather than an accidental formal weakening.

### Confidence

**High confidence (approximately 0.93) in the statement comparison.** The paper was read in full, including the appendix; metadata and hash were verified; and the Lean side was taken from the detailed Stage 1 declaration reconstruction. Confidence is lower only on the normative classification of the density-order mismatch—whether one calls the order-robust game a strengthening or a different game—so the report uses the conservative verdict “only conditionally related” for the exact minimax equalities.

### Unresolved source-version questions

None. The attached source is internally and externally identified as arXiv:2605.30324v1 dated 28 May 2026, and its SHA-256 matches the user-supplied value. The introductory informal labels (Theorems 1.2 and 1.3) consistently point to the formal Section 4 and Section 5 results in this version. No alternate version was used.

### Proof-correctness separation

Nothing in this report certifies the Lean proof bodies, the repository build, or the mathematical correctness of the paper proofs. The verdict concerns only whether the reconstructed Lean declaration types state the same claims as the pinned author paper.
