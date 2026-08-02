# 08 — Paper08_AutomatedHallucinationDetection — Lean Statement Reconstruction

## 1. Scope, provenance, and method

This reconstruction is based **only** on the attached deterministic source bundle
`08__Paper08_AutomatedHallucinationDetection__lean-source-bundle.txt`. No author paper, web source, connector, other Project file, or prior conversation is used.

The attachment has 145,824 bytes and whole-bundle SHA-256
`60e5b14e054663034a0d71380a2bf44f2f3578758d35512b9a1dc97999cdfc06`.
It contains 18 embedded Lean files. The byte count and SHA-256 of every embedded file body agree with the bundle manifest. The primary Paper 08 files are:

- `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`
- `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`
- `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`
- `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`
- `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`
- `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`
- the declaration-free umbrella file `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection.lean`.

The mathematical evidence used below is restricted to public declaration types and the defining right-hand sides of formal definitions. Lean comments, docstrings, prose annotations, and theorem proof terms/tactics are not treated as evidence for a claim. Declaration and module names are reported exactly because the audit requires provenance, but no intended mathematics is inferred merely from those names. Imported declarations are described only as interfaces needed to read primary statements; imported theorems are not relabeled as Paper 08 results.

The report inventories all 72 public primary declarations in those six substantive modules (counting the `OracleTree` inductive declaration once and describing both constructors under it). Local instances are excluded because they are not public declarations. There are no public `axiom` declarations in the primary Paper 08 modules.

### Reading conventions

Throughout, `α : Type u` denotes an arbitrary universe-polymorphic example type. Write

- `C : ℕ → Set α` for an indexed language family and `C_i` for `C i`;
- `stream : ℕ → α` for an infinite stream;
- `Presents stream L` for exact presentation, meaning `Set.range stream = L`;
- `sample stream t` for the finite set of distinct values at times strictly below `t`;
- `sequenceSample xs` for the finite set of distinct entries of `xs : Fin t → α`;
- `identifierOutput M stream t` for the index output by a semantic identifier on the prefix before time `t`.

These conventions abbreviate imported interfaces; their exact imported definitions are recorded in §11.

## 2. Formal setting reconstructed from the declarations

### 2.1 Languages, families, streams, and presentations

A language over `α` is an arbitrary set `Set α`. A family is an **indexed** sequence `C : ℕ → Set α`; repetitions are permitted. A positive-data stream is `ℕ → α`. Exact presentation requires equality of sets between the stream range and the target language. Repetitions and arbitrary ordering are allowed, but every target element must occur and no non-target element may occur.

An exact presentation of the empty language cannot exist, because a function from `ℕ` has nonempty range whenever it exists. Consequently, all positive-presentation success requirements are vacuous for empty indexed languages. This edge case is materially used by the shape of the principal equivalences.

### 2.2 Finite adaptive access to a candidate set

The candidate set being tested is an arbitrary `G : Set α`. The detector does not receive `G` as an extensional object. Instead, at each round it returns a finite binary query tree. Internal nodes ask whether a specified `x : α` belongs to `G`; the next node may depend on that Boolean answer. A leaf returns a Boolean.

Thus each individual round uses finitely many candidate-membership queries, because every `OracleTree` value is finite inductive data. There is, however, no public numerical query bound, no uniform bound as a function of time, no cost model, and no requirement that the function constructing the tree be computable.

### 2.3 Positive-data hallucination detection

At time `t`, a detector receives only the finite positive prefix `Fin t → α`; its returned tree is then evaluated against the candidate-set membership oracle for `G`. Correctness is exact:

\[
  \text{output} = \mathtt{true} \quad\Longleftrightarrow\quad G \subseteq K,
\]

where `K` is the target language. Detection in the limit requires this equivalence at every sufficiently late round, separately for each target index, exact presentation, and candidate set.

The stabilization time is quantified **after** the target index, the full presentation stream, and `G`. Therefore it may depend on all of them. There is no uniform stabilization time over candidate sets, streams, targets, or the family.

### 2.4 Semantic identification

An identifier is an arbitrary Lean function from finite positive histories to natural-number indices. It succeeds when, on every exact presentation of `C_z`, its guesses eventually become syntactically constant at some index `j` with `C_j = C_z`. The stable index may depend on the presentation. Duplicate family indices are therefore allowed, but eventual syntactic stability—not merely extensional correctness of changing guesses—is required.

No `Computable`, partial-recursive, oracle-Turing-machine, runtime, or code-extraction predicate occurs in the Paper 08 identification statements.

### 2.5 Finite tell-tales

The imported predicate `IsTellTale C i T` means

\[
T \subseteq C_i
\quad\text{and}\quad
\forall j,\; T\subseteq C_j \to C_j\subseteq C_i \to C_i\subseteq C_j.
\]

Hence every family language that contains `T` and is itself contained in `C_i` must equal `C_i`. `ConditionTwo C` means that such a finite `T : Finset α` exists separately for every index `i`. It is purely existential; it gives no computable or uniformly enumerable method for obtaining the tell-tales.

### 2.6 Negative-example model

A labeled stream has type `ℕ → α × Bool`. It is valid for target `K` exactly when its first coordinates cover the whole domain and every label is correct. A negative-example detector sees a finite prefix of this complete labeled stream and also receives finite adaptive membership-query access to the candidate set `G`.

The existence of a valid labeled enumeration is not built into the definition. For an uncountable `α`, and for an empty `α`, there is no such stream. Universal correctness over valid streams is therefore vacuous in those cases. This is especially important for the assumption-free statement of `theorem_2_3`.

### 2.7 Effectivity and classical status

Several constructions are explicitly declared `noncomputable`, including arbitrary-set oracle evaluation, the detector built from a semantic identifier, the identifier built from a detector, selection of tell-tales, and target-dependent presentations. No public theorem upgrades these semantic objects to computable functions. The countability typeclass used in principal theorems supplies set-theoretic enumerability, not a declared computable enumeration.

No primary statement is probabilistic. There are no distributions, error probabilities, confidence parameters, expectations, sample-complexity rates, or approximate correctness notions.

## 3. Primary declarations in `Definitions.lean`

**Bundle file label for every declaration in this section:**
`GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

### 3.1 Query-tree and detector interfaces

#### 3.1.1 `GenLimit.HallucinationDetection.OracleTree`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For every type `α`, this inductive type has exactly two constructor forms:

- `GenLimit.HallucinationDetection.OracleTree.answer : Bool → OracleTree α`;
- `GenLimit.HallucinationDetection.OracleTree.query : α → OracleTree α → OracleTree α → OracleTree α`.

A value is therefore a finite rooted binary tree whose leaves carry Booleans and whose internal nodes carry query points in `α`.

**Access and assumptions.** The syntax itself contains no target, stream, family index, or set. A query tree may encode arbitrary points of `α`; its branch behavior is supplied only at evaluation.

**Classification.** Constructive finite data type; oracle syntax; not a machine or runtime model.

**Risk audit.** Finiteness is guaranteed structurally, but depth/size is unbounded and no quantitative bound is part of the interface.

#### 3.1.2 `GenLimit.HallucinationDetection.OracleTree.eval`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For arbitrary `G : Set α`, `eval G` maps an `OracleTree α` to `Bool` recursively:

- `eval G (answer b) = b`;
- `eval G (query x yes no)` evaluates `yes` when `x ∈ G`, and evaluates `no` otherwise.

**Access and assumptions.** It has exact membership-oracle access to the arbitrary set `G`. The first subtree is the membership-true branch. There is no supplied decidable-membership instance; the definition is explicitly `noncomputable` and uses classical proposition decidability internally.

**Classification.** Semantic/extensional oracle evaluation; noncomputable; finite per tree; not machine-level.

**Risk audit.** Exact arbitrary-set membership is stronger than access to a finite representation or computable oracle. No oracle cost is modeled.

#### 3.1.3 `GenLimit.HallucinationDetection.Detector`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For every `α`,

\[
\mathrm{Detector}(α)
= \forall t:\mathbb N,\; (\mathrm{Fin}\,t\to α)\to \mathrm{OracleTree}(α).
\]

A detector maps every finite history of length `t` to a finite adaptive query tree.

**Access and assumptions.** At runtime the function receives the time and the complete prefix, but not a target index, target set, future data, candidate set as data, certificate, or explicit bound. Candidate-set information can enter only through later tree evaluation. When a detector witnesses a family-specific existential property, it may nevertheless be noncomputably hardwired to the whole family.

**Classification.** Semantic function interface with finite-query output; no computability or complexity requirement.

#### 3.1.4 `GenLimit.HallucinationDetection.detectorOutput`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For `D : Detector α`, `G : Set α`, `stream : ℕ → α`, and `t : ℕ`,

\[
\mathrm{detectorOutput}(D,G,stream,t)
= \mathrm{OracleTree.eval}\;G\bigl(D\;t\;(i\mapsto stream(i))\bigr),
\]

where the displayed function has domain `Fin t` and therefore exposes exactly the prefix before `t`.

**Access and assumptions.** The detector sees the prefix; the evaluator sees the exact membership oracle for `G`. The definition is explicitly noncomputable.

**Classification.** Semantic execution wrapper.

#### 3.1.5 `GenLimit.HallucinationDetection.DetectorCorrectAt`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For `D : Detector α`, sets `G,K : Set α`, a stream, and time `t`, this proposition is exactly

\[
\mathrm{detectorOutput}(D,G,stream,t)=\mathtt{true}
\quad\Longleftrightarrow\quad G\subseteq K.
\]

**Access and assumptions.** `K` appears only in the correctness specification, not as a direct detector input. The stream influences the left side only through its prefix.

**Classification.** Semantic/extensional, exact Boolean specification.

**Risk audit.** This is a definition of correctness, not an independently proved algorithmic guarantee. It has no tolerance for false positives/negatives and no approximation parameter.

#### 3.1.6 `GenLimit.HallucinationDetection.DetectsHallucinations`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For `D : Detector α` and `C : ℕ → Set α`, the full quantifier order is

\[
\forall z:\mathbb N,\;
\forall stream:\mathbb N\to α,\;
\mathrm{Presents}(stream,C_z)\to
\forall G:Set\,α,\;
\exists T:\mathbb N,\;
\forall t:\mathbb N,\;
T\le t\to
\mathrm{DetectorCorrectAt}(D,G,C_z,stream,t).
\]

Equivalently, for each fixed target index, exact positive presentation, and candidate set, all sufficiently late answers are exactly correct about `G ⊆ C_z`.

**Access and assumptions.** `D` is one detector for the entire indexed family. It receives only positive prefixes and finite adaptive oracle access to `G`. The threshold `T` may depend on `z`, the entire stream, and `G`; it is not required to be available to the detector.

**Classification.** Semantic/extensional limiting correctness; conditional on an exact presentation; not computable, runtime-bounded, or probabilistic.

**Risk audit.** Empty targets impose no obligation. Convergence is pointwise in `G`, not uniform over candidate sets. The definition quantifies over arbitrary candidate sets, including noncomputable ones.

#### 3.1.7 `GenLimit.HallucinationDetection.HallucinationDetectable`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For `C : ℕ → Set α`,

\[
\mathrm{HallucinationDetectable}(C)
\quad:\Longleftrightarrow\quad
\exists D:\mathrm{Detector}(α),\;\mathrm{DetectsHallucinations}(D,C).
\]

**Access and assumptions.** The existential detector may depend on the entire family `C`; no code, oracle implementation, or uniform bound accompanies it.

**Classification.** Semantic existential property.

#### 3.1.8 `GenLimit.HallucinationDetection.IdentifiableInLimit`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For `C : ℕ → Set α`,

\[
\mathrm{IdentifiableInLimit}(C)
\quad:\Longleftrightarrow\quad
\exists M:\mathrm{SemanticIdentifier}(α),\;
\mathrm{SemanticallyIdentifies}(M,C).
\]

After expansion of the imported interface, this means one arbitrary function `M` maps every finite positive history to an index, and for every `z` and every exact presentation of `C_z`, there is an index `j` such that `C_j = C_z` and the guesses eventually equal `j` at every later time.

**Access and assumptions.** `M` gets only the finite history at runtime and no target index. The witness `M` may be noncomputably hardwired to `C`. Stable indices may vary with the presentation.

**Classification.** Semantic/extensional identification; no effectivity.

### 3.2 Labeled histories and negative-example detection

#### 3.2.1 `GenLimit.HallucinationDetection.LabeledStream`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For every `α`,

\[
\mathrm{LabeledStream}(α)=\mathbb N\to α\times Bool.
\]

**Access and assumptions.** This abbreviation carries only an infinite sequence of point/Boolean pairs; it contains no target-validity proof, oracle, or enumeration-rate guarantee.

**Classification.** Constructive data interface.

#### 3.2.2 `GenLimit.HallucinationDetection.IsLabeledEnumeration`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For `stream : ℕ → α × Bool` and `K : Set α`, this is the conjunction

1. `Set.range (fun n => (stream n).1) = Set.univ`; and
2. for every `n`, `(stream n).2 = true ↔ (stream n).1 ∈ K`.

Thus every domain point occurs at least once among the first coordinates, and every occurrence is labeled with exact target membership.

**Access and assumptions.** Repetition and arbitrary order are permitted. No computability or fairness rate is required. Completeness is an extensional infinite condition. The existence of such a stream itself forces the domain to be nonempty and at most countable, but those are not explicit typeclass hypotheses in the definition.

**Classification.** Semantic/extensional validity predicate.

**Risk audit.** Where no such stream exists, any theorem universally quantified over valid labeled enumerations is vacuous.

#### 3.2.3 `GenLimit.HallucinationDetection.NegativeExampleDetector`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For every `α`,

\[
\mathrm{NegativeExampleDetector}(α)
=\forall t:\mathbb N,\;(\mathrm{Fin}\,t\to α\times Bool)\to\mathrm{OracleTree}(α).
\]

**Access and assumptions.** The detector receives the finite labeled prefix and later gets finite adaptive membership-query access to `G`. It receives no target index or future labeled values.

**Classification.** Semantic finite-query interface; no computability or complexity requirement.

#### 3.2.4 `GenLimit.HallucinationDetection.negativeDetectorOutput`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For a negative-example detector `D`, candidate set `G`, labeled stream, and time `t`, this evaluates `D t` on the prefix before `t` and then evaluates the resulting query tree against the exact membership oracle for `G`.

**Access and assumptions.** The detector receives exactly the labeled prefix before `t`; evaluation then receives exact candidate-membership answers for `G`. The target set is not an input.

**Classification.** Semantic execution wrapper; explicitly noncomputable because arbitrary-set membership is classically decided.

#### 3.2.5 `GenLimit.HallucinationDetection.NegativeDetectorCorrectAt`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For `D`, candidate `G`, target `K`, labeled stream, and `t`, this proposition is

\[
\mathrm{negativeDetectorOutput}(D,G,stream,t)=\mathtt{true}
\quad\Longleftrightarrow\quad G\subseteq K.
\]

**Access and assumptions.** `K` occurs only on the specification side of the iff. The left side depends on the labeled prefix and candidate oracle.

**Classification.** Exact semantic/extensional correctness.

#### 3.2.6 `GenLimit.HallucinationDetection.DetectsWithNegativeExamples`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For `D : NegativeExampleDetector α` and `C : ℕ → Set α`, the quantifier order is

\[
\forall z,\;
\forall stream:\mathrm{LabeledStream}(α),\;
\mathrm{IsLabeledEnumeration}(stream,C_z)\to
\forall G:Set\,α,\;
\exists T,\;
\forall t,\;T\le t\to
\mathrm{NegativeDetectorCorrectAt}(D,G,C_z,stream,t).
\]

**Access and assumptions.** A single `D` handles the whole family. `T` may depend on `z`, the full labeled stream, and `G`. The stream supplies eventual labels for every point in `α`; the detector also has candidate-membership queries.

**Classification.** Semantic limiting correctness, conditional on a complete labeled enumeration; not probabilistic or effective.

**Risk audit.** The property is vacuous for target/domain combinations admitting no complete labeled enumeration. No uniform time bound is asserted.

#### 3.2.7 `GenLimit.HallucinationDetection.DetectableWithNegativeExamples`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`.

For `C : ℕ → Set α`,

\[
\mathrm{DetectableWithNegativeExamples}(C)
\quad:\Longleftrightarrow\quad
\exists D:\mathrm{NegativeExampleDetector}(α),\;
\mathrm{DetectsWithNegativeExamples}(D,C).
\]

**Access and assumptions.** The existential detector may depend on the whole family `C`; its runtime access is exactly the finite labeled prefix plus the candidate-set query-tree interface.

**Classification.** Semantic existential property.


## 4. Primary declarations in `Reductions.lean`

**Bundle file label for every declaration in this section:**
`GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

### 4.1 From semantic identification to detection

#### 4.1.1 `GenLimit.HallucinationDetection.domainPrefix`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

For `enumerate : ℕ → α` and `t : ℕ`, `domainPrefix enumerate t` is the list `List.ofFn (fun i : Fin t => enumerate i)`. It contains, in index order, exactly `enumerate 0, …, enumerate (t-1)`.

**Access and assumptions.** The function `enumerate` is supplied explicitly. No surjectivity or computability is part of this definition.

**Classification.** Constructive finite-list definition.

#### 4.1.2 `GenLimit.HallucinationDetection.mem_domainPrefix_iff`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

For implicit `enumerate : ℕ → α`, `t : ℕ`, and `x : α`,

\[
x\in\mathrm{domainPrefix}(enumerate,t)
\quad\Longleftrightarrow\quad
\exists i:\mathbb N,\;i<t\land enumerate(i)=x.
\]

**Access and assumptions.** Only the supplied enumeration function, finite cutoff, and queried point occur; there is no target, candidate oracle, or future-data access.

**Classification.** Extensional representation lemma; no extra assumptions.

**Risk audit.** This is a direct list-membership characterization, not a learning result.

#### 4.1.3 `GenLimit.HallucinationDetection.subsetTestTree`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

For `L : Set α`, this explicitly noncomputable recursive function maps a list of domain points to an `OracleTree α`:

- on `[]`, return `answer true`;
- on `x :: xs`, if `x ∈ L`, recurse on `xs` without querying `G`;
- if `x ∉ L`, query `x`; on a positive candidate-oracle answer return `false`, and on a negative answer continue with the tail.

**Access and assumptions.** The construction has exact extensional membership access to `L` at tree-construction time. At evaluation it will have membership-query access to `G`. There is no decidable-membership assumption; the definition is noncomputable.

**Classification.** Finite semantic oracle construction; structurally at most one query per list entry; not a certified runtime bound or effective algorithm.

**Risk audit.** The hardwired set `L` is not represented finitely and need not be decidable.

#### 4.1.4 `GenLimit.HallucinationDetection.eval_subsetTestTree_eq_true_iff`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

For all `G,L : Set α` and lists `xs : List α`,

\[
\mathrm{OracleTree.eval}\;G\bigl(\mathrm{subsetTestTree}\;L\;xs\bigr)=\mathtt{true}
\]

if and only if

\[
\forall x:\alpha,\;x\in xs\to x\in G\to x\in L.
\]

Equivalently, every point from the finite list that lies in `G` also lies in `L`.

**Access and assumptions.** The left side evaluates exact membership in `G`; the tree itself was formed using exact membership in `L`; `xs` is finite.

**Classification.** Exact semantic/extensional correctness lemma for the finite tree.

**Risk audit.** The conclusion checks `G ⊆ L` only on the listed points, not globally.

#### 4.1.5 `GenLimit.HallucinationDetection.detectorFromIdentifier`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

Given

1. `C : ℕ → Set α`,
2. `enumerate : ℕ → α`, and
3. `M : SemanticIdentifier α`,

this explicitly noncomputable detector is

\[
(t,xs)\longmapsto
\mathrm{subsetTestTree}\bigl(C_{M(t,xs)},\;\mathrm{domainPrefix}(enumerate,t)\bigr).
\]

It uses the identifier’s current index, takes the corresponding family language as its current target conjecture, and tests the candidate set only on the first `t` enumerated domain points.

**Access and assumptions.** `C`, `enumerate`, and `M` are hardwired. Runtime input is only the positive prefix; candidate access is through the returned tree. Exact membership in the current conjectured set is used while constructing the tree.

**Classification.** Semantic/noncomputable reduction construction; finite per round; no machine-level or uniform runtime claim.

#### 4.1.6 `GenLimit.HallucinationDetection.lemma_3_1_identification_implies_detection`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

The binders occur in this order:

1. `C : ℕ → Set α`;
2. `enumerate : ℕ → α`;
3. `henumerate : Function.Surjective enumerate`;
4. `hID : IdentifiableInLimit C`.

The conclusion is `HallucinationDetectable C`.

In full natural language: for an arbitrary example type, if a specific surjection from `ℕ` onto the domain is supplied and the indexed family is semantically identifiable from exact positive presentations, then there exists a semantic finite-query detector that detects candidate-set containment in the limit.

**Access and assumptions.** The supplied surjection covers the entire domain and may be noncomputable. The identifier is semantic. The resulting detector may depend on `C`, the surjection, and the identifying function. No separate `[Nonempty α]` or `[Countable α]` is needed because the supplied surjective map already carries the relevant enumerability information; when no such map can be supplied, the implication cannot be instantiated.

**Classification.** Conditional semantic reduction; extensional; non-effective; non-probabilistic.

**Risk audit.** The theorem does not construct a computable detector from a computable identifier. It assumes a full domain enumeration as auxiliary input. Its detector’s convergence time remains pointwise in the stream and candidate set. It is not an implication from identification on an arbitrary unenumerated domain.

### 4.2 From detection to semantic identification

#### 4.2.1 `GenLimit.HallucinationDetection.DetectorCandidate`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

For a family `C`, detector `D`, implicit time `t`, history `xs : Fin t → α`, and index `i : ℕ`, `DetectorCandidate C D xs i` is the conjunction

1. `i ≤ t`;
2. every distinct value in `xs` belongs to `C_i`; and
3. `OracleTree.eval (C i) (D t xs) = true`.

The second condition is positive-data consistency. The third runs the detector’s tree with the family language `C_i` itself as the candidate-set oracle.

**Access and assumptions.** Testing the third conjunct gives the reduction exact membership-oracle access to `C_i`. The family and detector are hardwired; no target index is supplied. The bound `i ≤ t` limits eligible indices extensionally to a finite range.

**Classification.** Semantic/extensional candidate predicate; non-effective over arbitrary sets.

**Risk audit.** This is a strong oracle-level bridge: the recovered identifier may evaluate the detector against exact candidate languages from the family. No representation or decidability of those languages is required.

#### 4.2.2 `GenLimit.HallucinationDetection.identifierFromDetector`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

For `C : ℕ → Set α` and `D : Detector α`, this explicitly noncomputable semantic identifier maps `(t,xs)` to

- the least natural `i` satisfying `DetectorCandidate C D xs i`, when any such `i` exists;
- `0` otherwise.

The least witness is selected with `Nat.find`.

**Access and assumptions.** The function has the entire family and detector hardwired and uses exact set membership through `DetectorCandidate`. The bounded condition `i ≤ t` makes the set of possible candidates finite, but no decidability or executable search procedure is included in the type.

**Classification.** Noncomputable semantic least-index construction; not a machine-level learner.

**Risk audit.** The default `0` carries no correctness meaning when no candidate exists. Correctness theorems must separately establish eventual candidate existence.

#### 4.2.3 `GenLimit.HallucinationDetection.identifierFromDetector_candidate`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

For implicit `C`, `D`, `t`, and `xs`, assume

\[
\exists i,\;\mathrm{DetectorCandidate}(C,D,xs,i).
\]

Then the selected index `identifierFromDetector C D t xs` itself satisfies `DetectorCandidate C D xs`.

**Access and assumptions.** All access is inherited from the supplied candidate-existence premise and the definition of `identifierFromDetector`; no new oracle or witness is introduced.

**Classification.** Semantic helper lemma characterizing the least witness.

**Risk audit.** The premise already supplies candidate existence; this theorem does not establish that the premise holds in a learning run.

#### 4.2.4 `GenLimit.HallucinationDetection.identifierFromDetector_le_of_candidate`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

For implicit `C`, `D`, `t`, `xs`, and `i`, if `i` is a `DetectorCandidate`, then

\[
\mathrm{identifierFromDetector}(C,D,t,xs)\le i.
\]

**Access and assumptions.** The premise supplies one eligible index. The conclusion uses only the least-index property and introduces no additional data access.

**Classification.** Least-witness order lemma.

**Risk audit.** This is a direct minimality property, not an independent convergence statement.

#### 4.2.5 `GenLimit.HallucinationDetection.lemma_3_2_detection_implies_identification`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

For every `C : ℕ → Set α`,

\[
\mathrm{HallucinationDetectable}(C)
\quad\Longrightarrow\quad
\mathrm{IdentifiableInLimit}(C).
\]

There are no nonemptiness or countability assumptions on `α` in this direction.

**Access and assumptions.** The hypothesis supplies only a semantic detector witness, and the conclusion supplies only a semantic identifier witness. The theorem type does not identify the witness with any particular definition. Separately, this module publicly defines the noncomputable `identifierFromDetector`, whose access profile is recorded in §4.2.2.

**Classification.** Conditional semantic/extensional reduction; non-effective; no runtime or probability claim.

**Risk audit.** The result does not show that an executable detector yields an executable identifier. Empty target entries remain vacuous on both sides. The premise `HallucinationDetectable C` supplies correctness pointwise for each fixed candidate set, including each `C_i`; it supplies no uniform rate.

### 4.3 Principal equivalence

#### 4.3.1 `GenLimit.HallucinationDetection.theorem_2_1`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`.

For implicit typeclass instances `[Nonempty α]` and `[Countable α]`, and then for every `C : ℕ → Set α`,

\[
\mathrm{HallucinationDetectable}(C)
\quad\Longleftrightarrow\quad
\mathrm{IdentifiableInLimit}(C).
\]

**Binder and assumption ledger.** The example type must be nonempty and countable in Mathlib’s set-theoretic sense. The language family is indexed by natural numbers. No member language is required to be nonempty, infinite, decidable, enumerable, or computable. No family-membership oracle is an explicit input to the detector or identifier interfaces, although the existential witnesses may be hardwired to the family and the reductions use arbitrary-set membership semantically.

**Access.** The biconditional’s type exposes only the two semantic properties and the `[Nonempty α] [Countable α]` instances. It does not expose a domain enumeration, family-membership oracle, or concrete witness. The separate public reduction declarations in §§4.1–4.2 have the more specific access profiles recorded there.

**Classification.** Semantic/extensional biconditional; conditional on nonempty countable domain; nonconstructive/non-effective; not machine-level, runtime-bounded, or probabilistic.

**Statement-level risk flags.**

- Empty indexed languages contribute vacuously to both limiting notions because no exact positive presentation exists.
- `Countable α` does not assert a computable encoding or enumeration.
- The equivalence is pointwise in presentation and candidate set; it contains no uniform sample-complexity or query-complexity bound.
- Duplicate indices are permitted, and the identification side asks for eventual stability at one extensionally correct index.
- The statement does not characterize effective or efficient automated detection.


## 5. Primary declarations in `AngluinCondition.lean`

**Bundle file label for every declaration in this section:**
`GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

### 5.1 Finite tell-tales imply semantic identification

#### 5.1.1 `GenLimit.HallucinationDetection.chosenTellTale`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

For `C : ℕ → Set α`, a proof `h : GenLimit.Angluin.ConditionTwo C`, and `i : ℕ`, this explicitly noncomputable function returns

\[
\mathrm{Classical.choose}(h(i)) : \mathrm{Finset}\,α.
\]

Since `h(i)` has type `∃ T : Finset α, IsTellTale C i T`, the returned finite set is one chosen tell-tale for index `i`.

**Access and assumptions.** The function receives the whole family and a global existence proof furnishing a tell-tale existential for every index. It uses classical choice. It does not compute a tell-tale from finite observations.

**Classification.** Noncomputable choice function; semantic/answer-encoding auxiliary input.

**Risk audit.** The proof argument `h` contains exactly the existential information needed to choose every tell-tale. No uniform enumerability, decidability, or algorithm is extracted.

#### 5.1.2 `GenLimit.HallucinationDetection.chosenTellTale_spec`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

For the same `C`, `h`, and `i`,

\[
\mathrm{IsTellTale}\bigl(C,i,\mathrm{chosenTellTale}(C,h,i)\bigr).
\]

**Access and assumptions.** The family, global `ConditionTwo` proof, and index are supplied. No online observations, oracle queries, or effective chooser occur in the theorem type.

**Classification.** Choice-specification lemma.

**Risk audit.** This conclusion is the direct specification returned by `Classical.choose_spec`; it packages the supplied existential rather than proving `ConditionTwo` for a new family.

#### 5.1.3 `GenLimit.HallucinationDetection.constantTellTaleApproximation`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

For `C` and `h : ConditionTwo C`, this explicitly noncomputable function has type

\[
\mathbb N\to\mathbb N\to\mathrm{Finset}\,α
\]

and is defined by

\[
(i,stage)\longmapsto \mathrm{chosenTellTale}(C,h,i).
\]

It is constant in the stage variable.

**Access and assumptions.** All tell-tales are selected in advance from `h`. There is no staged discovery process.

**Classification.** Noncomputable semantic approximation object.

**Risk audit.** Calling this an “approximation” does not make it effective: the final tell-tale is present from stage zero and is selected by choice.

#### 5.1.4 `GenLimit.HallucinationDetection.constantTellTaleApproximation_spec`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

For `C` and `h : ConditionTwo C`, the function `constantTellTaleApproximation C h` satisfies the imported predicate `IsTellTaleApproximation C`.

Expanded, it asserts both:

1. for all indices `i` and stages `n ≤ m`, the stage-`n` finite set is a subset of the stage-`m` finite set; and
2. for every `i`, there exists a finite tell-tale `T` and a stage `N` such that every stage `n ≥ N` equals `T`.

For this constant approximation, the stable tell-tale is the chosen one and stabilization can occur at stage zero.

**Access and assumptions.** The family and a proof of `ConditionTwo` are supplied globally. The statement has no stream, target oracle, or finite-data input.

**Classification.** Semantic packaging lemma; non-effective because the underlying approximation is noncomputable.

**Risk audit.** The statement’s eventual stabilization is tautological for a constant function and carries no information about effective enumeration.

#### 5.1.5 `GenLimit.HallucinationDetection.identifiable_of_conditionTwo`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

For every `C : ℕ → Set α`,

\[
\mathrm{ConditionTwo}(C)
\quad\Longrightarrow\quad
\mathrm{IdentifiableInLimit}(C).
\]

No nonemptiness or countability assumption on `α` is present in this statement.

**Access and assumptions.** `ConditionTwo` supplies only existential finite tell-tales, one per index. The conclusion is existence of a semantic identifier; its type contains no computability requirement. The public auxiliary construction selecting the tell-tales is explicitly noncomputable.

**Classification.** Conditional semantic sufficiency theorem; extensional; non-effective.

**Risk audit.** This is substantially weaker than effective identification from a uniformly computable tell-tale enumeration. The hypothesis can encode the required finite certificates nonconstructively. Empty targets cause no positive-presentation obligation and also admit an empty tell-tale.

### 5.2 Re-encoding finite histories and convergence

#### 5.2.1 `GenLimit.HallucinationDetection.listIdentifierOf`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

For `M : SemanticIdentifier α`, define a list-based identifier by

\[
\mathrm{listIdentifierOf}(M)(xs)=M\bigl(xs.length,xs.get\bigr).
\]

Here `xs.get : Fin xs.length → α` is the finite tuple represented by the list.

**Access and assumptions.** No information is added; this is a representation conversion.

**Classification.** Constructive interface adapter.

#### 5.2.2 `GenLimit.HallucinationDetection.listIdentifierOf_streamPrefix`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

For `M`, `stream`, and `t`,

\[
\mathrm{listIdentifierOf}(M)
  (\mathrm{streamPrefix}(stream,t))
=
\mathrm{identifierOutput}(M,stream,t).
\]

**Access and assumptions.** Both sides use the same supplied identifier and the same finite stream prefix under different encodings; no additional information is available.

**Classification.** Extensional representation identity.

**Risk audit.** This is a bridge between two encodings of the same finite prefix, not an identification theorem.

#### 5.2.3 `GenLimit.HallucinationDetection.ListConvergesTo`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

For `M : List α → ℕ`, `stream : ℕ → α`, and `j : ℕ`,

\[
\mathrm{ListConvergesTo}(M,stream,j)
\quad:\Longleftrightarrow\quad
\exists T,\;\forall t,\;T\le t\to
M(\mathrm{streamPrefix}(stream,t))=j.
\]

**Access and assumptions.** The proposition is parameterized by a complete stream for specification purposes, while `M` is evaluated only on each finite prefix. The existential threshold may depend on the full stream.

**Classification.** Syntactic eventual-convergence definition; semantic; no effectivity.

### 5.3 Presentations and locking sequences

#### 5.3.1 `GenLimit.HallucinationDetection.presentationFromDomainEnumeration`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

Given

1. `enumerate : ℕ → α`,
2. `L : Set α`, and
3. `hL : L.Nonempty`,

this explicitly noncomputable stream is

\[
n\longmapsto
\begin{cases}
  enumerate(n), & enumerate(n)\in L,\\
  \mathrm{Classical.choose}(hL), & enumerate(n)\notin L.
\end{cases}
\]

**Access and assumptions.** The construction directly tests exact membership in the target `L` and uses a chosen target point as padding. It does not model a learner that lacks target access.

**Classification.** Noncomputable target-dependent witness construction.

**Risk audit.** This is a proof-side presentation generator, not an available data source for the detector. Both membership in `L` and a witness of nonemptiness are supplied.

#### 5.3.2 `GenLimit.HallucinationDetection.presentationFromDomainEnumeration_presents`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

The binders occur in this order:

1. `enumerate : ℕ → α`;
2. `henumerate : Function.Surjective enumerate`;
3. `L : Set α`;
4. `hL : L.Nonempty`.

The conclusion is

\[
\mathrm{Presents}
  (\mathrm{presentationFromDomainEnumeration}(enumerate,L,hL),L).
\]

Thus a supplied surjective enumeration and a supplied nonempty target yield an exact presentation via the preceding target-filtering construction.

**Access and assumptions.** The statement supplies the enumeration, its surjectivity proof, the target set, and a target nonemptiness witness. The defined stream itself has exact target-membership access as described above.

**Classification.** Conditional semantic existence/correctness theorem.

**Risk audit.** It assumes a global domain surjection and exact target-membership tests in the defined stream. It gives no computable presentation unless additional effective data are supplied and proved usable.

#### 5.3.3 `GenLimit.HallucinationDetection.exists_lockingSequence_of_identifies_with_presentation`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

Implicitly fix

- `M : List α → ℕ`,
- `L : Set α`, and
- `base : ℕ → α`.

Assume, in order:

1. `hbaseP : Presents base L`; and
2. `hIdentifies : ∀ stream : ℕ → α, Presents stream L → ∃ j, ListConvergesTo M stream j`.

Then there exist `xs : List α` and `j : ℕ` such that

\[
\mathrm{IsLockingSequence}(M,L,xs,j).
\]

Expanded, every entry of `xs` lies in `L`, and for every finite tail all of whose entries lie in `L`, `M (xs ++ tail) = j`.

**Access and assumptions.** A concrete exact presentation of `L` is supplied. The convergence hypothesis ranges over **every** exact presentation of `L`, and the limiting index may depend on the stream. The hypothesis does not say that the limiting number denotes `L` in any family.

**Classification.** Conditional semantic existence theorem; nonconstructive in content; no computability or bound on locking-sequence length.

**Risk audit.** The conclusion is only a syntactic lock. Correctness of the locked index is absent and must be supplied by a separate family-linked hypothesis. The theorem is nonvacuous only when the supplied exact presentation exists.

#### 5.3.4 `GenLimit.HallucinationDetection.lockingSequence_correct_with_presentation`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

Implicitly fix

- `C : ℕ → Set α`,
- `M : List α → ℕ`,
- indices `z,j : ℕ`,
- `xs : List α`, and
- `base : ℕ → α`.

Assume, in order:

1. `base` exactly presents `C_z`;
2. for every stream exactly presenting `C_z`, there exists `ell` with `C_ell = C_z` and `ListConvergesTo M stream ell`; and
3. `xs` is a locking sequence for `M` on `C_z` with locked index `j`.

Then

\[
C_j=C_z.
\]

**Access and assumptions.** Correct semantic identification is assumed on every presentation of the fixed target. A base presentation and a lock are separately supplied.

**Classification.** Conditional semantic correctness lemma.

**Risk audit.** The conclusion does not merely repeat an assumption: correctness is assumed for whatever limiting index occurs on each presentation, while the theorem links the separately supplied locked index `j` to the target. Nevertheless, the assumptions are strong and target-specific; there is no method for finding `xs`, `j`, or a convergence bound in the statement.

#### 5.3.5 `GenLimit.HallucinationDetection.lockingSequence_isTellTale_with_presentations`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

Implicitly fix `C : ℕ → Set α` and `M : List α → ℕ`. Assume, in order:

1. for every index `z` and every stream exactly presenting `C_z`, there exists `j` such that `C_j=C_z` and `M` converges on that stream to `j` in the list sense;
2. every family member `C_i` has some exact presentation;
3. for implicit `z,j` and `xs`, `xs` is a locking sequence for `M` on `C_z` with locked index `j`; and
4. `C_j=C_z`.

Then `xs.toFinset` is an `IsTellTale C z` witness. Explicitly:

- every element occurring in `xs` belongs to `C_z`; and
- for every `k`, if every element of `xs` belongs to `C_k` and `C_k ⊆ C_z`, then `C_z ⊆ C_k`.

**Access and assumptions.** The theorem assumes full identification over the family, exact presentability of every indexed language, a supplied locking sequence, and a supplied correctness equality for its index.

**Classification.** Conditional semantic locking-to-certificate theorem.

**Risk audit.** The `hcorrect` equality is a strong link condition, but it is not the conclusion in disguise: the output is a finite tell-tale property involving all sublanguages in the family. The all-members-presentable premise excludes empty family members and is stronger than necessary for later use.

#### 5.3.6 `GenLimit.HallucinationDetection.lockingSequence_isTellTale_with_nonempty_presentations`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

Implicitly fix `C` and `M`. Assume, in order:

1. the same all-target semantic identification property as in the preceding theorem;
2. for every index `i`, if `C_i` is nonempty then it has an exact presentation;
3. implicit `z,j,xs` with `xs ≠ []`;
4. `xs` is a locking sequence for `M` on `C_z` with index `j`; and
5. `C_j=C_z`.

Then `xs.toFinset` is a tell-tale for index `z`.

**Access and assumptions.** Only nonempty candidate languages must be presentable. The nonempty-history premise ensures that any candidate containing the history is itself nonempty.

**Classification.** Conditional semantic variant handling empty family members.

**Risk audit.** The nonempty-list witness is essential to avoid needing presentations of empty candidates. The theorem still presupposes both a lock and its extensional correctness.

#### 5.3.7 `GenLimit.HallucinationDetection.append_mem_isLockingSequence`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

Implicitly fix `M : List α → ℕ`, `L : Set α`, `xs : List α`, and `j : ℕ`. If

1. `xs` is a locking sequence for `M` on `L` with index `j`, and
2. an implicit `x : α` satisfies `x ∈ L`,

then `xs ++ [x]` is also a locking sequence for `M` on `L` with index `j`.

**Access and assumptions.** An existing lock and a supplied target member are the only inputs; the theorem neither searches for the member nor obtains new oracle access.

**Classification.** Constructive conditional structural lemma.

**Risk audit.** It preserves an already supplied lock; it does not establish existence of a target point or a lock.

### 5.4 Identification and the finite-tell-tale condition

#### 5.4.1 `GenLimit.HallucinationDetection.conditionTwo_of_identifiable`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

With implicit typeclass assumptions `[Nonempty α]` and `[Countable α]`, for every `C : ℕ → Set α`,

\[
\mathrm{IdentifiableInLimit}(C)
\quad\Longrightarrow\quad
\mathrm{ConditionTwo}(C).
\]

Thus semantic positive-data identification implies existence of a finite tell-tale for every indexed language.

**Hidden assumptions.** The domain is nonempty and set-theoretically countable. Family members need not be nonempty: an empty member can satisfy the conclusion with the empty finite set. No decidable equality, computable enumeration, effective family membership, or computable identifier is required by the type.

**Access.** The semantic witness identifier may be hardwired to `C`. The theorem’s conclusion is only existential tell-tale availability, not a uniform function exposed as data.

**Classification.** Conditional semantic necessity theorem; extensional; non-effective.

**Risk audit.** Positive-data identification of an empty target is vacuous, while the tell-tale conclusion for it is trivial. The result is not the effective Angluin necessity theorem and does not produce uniformly enumerable certificates.

#### 5.4.2 `GenLimit.HallucinationDetection.corollary_2_2`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`.

With `[Nonempty α]` and `[Countable α]`, for every `C : ℕ → Set α`,

\[
\mathrm{HallucinationDetectable}(C)
\quad\Longleftrightarrow\quad
\mathrm{ConditionTwo}(C).
\]

This is the strongest finite-certificate characterization stated in the primary modules.

**Binder and assumption ledger.** The domain is nonempty and countable; the family is naturally indexed; candidate and target sets are arbitrary; target languages may be empty, finite, infinite, undecidable, or noncomputable; tell-tales are finite sets existing separately for each index.

**Access.** On the detection side, one semantic detector sees positive prefixes and finite adaptive membership queries to each candidate `G`. On the tell-tale side, only existence is asserted. The theorem type does not expose a certificate chooser or a concrete detector. Separately, this module defines the noncomputable `chosenTellTale` interface described in §5.1.1.

**Classification.** Semantic/extensional biconditional; conditional on countable nonempty domain; non-effective; no machine, runtime, or probability content.

**Statement-level risk flags.**

- `ConditionTwo` is not an effective or uniformly enumerable condition.
- Empty targets are vacuous for detection and have a trivial empty tell-tale.
- No uniform stabilization or query bound follows.
- The equivalence can be used logically to derive non-detectability from failure of `ConditionTwo`, but this module does not itself supply a concrete family with a proved failure.
- The biconditional concerns arbitrary set oracles and semantic functions, not deployable automated detectors.


## 6. Primary declarations in `Appendix.lean`

**Bundle file label for every declaration in this section:**
`GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

### 6.1 Consecutive-guess identification

#### 6.1.1 `GenLimit.HallucinationDetection.ConsecutivelyIdentifiesFrom`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For `M : SemanticIdentifier α`, `C : ℕ → Set α`, `z : ℕ`, and `stream : ℕ → α`, this proposition is

\[
\exists T:\mathbb N,\;
\forall t:\mathbb N,\;T<t\to
\Bigl(
  \mathrm{identifierOutput}(M,stream,t)
  =\mathrm{identifierOutput}(M,stream,t-1)
\Bigr)
\land
\Bigl(
  C_{\mathrm{identifierOutput}(M,stream,t)}=C_z
\Bigr).
\]

The strict inequality means the first constrained round is `T+1`. At every constrained round, the current index equals the immediately preceding index and denotes the target language extensionally.

**Access and assumptions.** This local predicate does not itself assume that `stream` presents `C_z`; that premise is added by `ConsecutivelyIdentifies`. The identifier sees only finite prefixes.

**Classification.** Semantic/extensional eventual-adjacent-stability definition.

**Risk audit.** Correctness is extensional at each late round, while stability is syntactic. No computability or convergence-rate bound is present.

#### 6.1.2 `GenLimit.HallucinationDetection.ConsecutivelyIdentifies`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For `M` and `C`, the full statement is

\[
\forall z,\;
\forall stream:\mathbb N\to α,\;
\mathrm{Presents}(stream,C_z)\to
\mathrm{ConsecutivelyIdentifiesFrom}(M,C,z,stream).
\]

**Access and assumptions.** One identifier works for all indexed targets and exact positive presentations. The threshold may depend on `z` and the entire stream.

**Classification.** Semantic limiting-identification property.

**Risk audit.** Empty targets again impose no obligation.

#### 6.1.3 `GenLimit.HallucinationDetection.ConsecutivelyIdentifiable`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For `C`,

\[
\mathrm{ConsecutivelyIdentifiable}(C)
\quad:\Longleftrightarrow\quad
\exists M:\mathrm{SemanticIdentifier}(α),\;
\mathrm{ConsecutivelyIdentifies}(M,C).
\]

**Access and assumptions.** The existential identifier may depend on `C`; at runtime it sees only finite positive prefixes. No bound or target index is supplied.

**Classification.** Semantic existential property.

#### 6.1.4 `GenLimit.HallucinationDetection.semanticallyIdentifies_implies_consecutivelyIdentifies`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For implicit `M` and `C`,

\[
\mathrm{SemanticallyIdentifies}(M,C)
\quad\Longrightarrow\quad
\mathrm{ConsecutivelyIdentifies}(M,C).
\]

The same identifier `M` appears on both sides.

**Access and assumptions.** The same supplied identifier and family occur in premise and conclusion; no auxiliary oracle, certificate, or new function is added.

**Classification.** Conditional semantic implication.

**Risk audit.** This is a relation between two convergence specifications, not a construction of a new identifier.

#### 6.1.5 `GenLimit.HallucinationDetection.consecutivelyIdentifies_implies_semanticallyIdentifies`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For implicit `M` and `C`,

\[
\mathrm{ConsecutivelyIdentifies}(M,C)
\quad\Longrightarrow\quad
\mathrm{SemanticallyIdentifies}(M,C).
\]

Again the same identifier occurs on both sides. Eventual equality of each guess to its predecessor forces one fixed syntactic tail index, and the consecutive specification already states that late guesses denote the target.

**Access and assumptions.** The same supplied identifier and family occur in premise and conclusion; the theorem changes only the convergence specification.

**Classification.** Conditional semantic implication.

**Risk audit.** No effectivity is gained. The conclusion’s stable index may depend on the target presentation, just as in the premise.

#### 6.1.6 `GenLimit.HallucinationDetection.definition_3_equivalence`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For every `C : ℕ → Set α`,

\[
\mathrm{ConsecutivelyIdentifiable}(C)
\quad\Longleftrightarrow\quad
\mathrm{IdentifiableInLimit}(C).
\]

No typeclass assumptions on `α` occur.

**Access and assumptions.** Both sides quantify over the same semantic identifier interface and exact positive presentations; no domain typeclass, oracle, or effective representation is added.

**Classification.** Semantic/extensional equivalence of two convergence formulations.

**Risk audit.** This is not an equivalence between different access models: both sides use the same arbitrary semantic identifier interface and exact positive presentations.

#### 6.1.7 `GenLimit.HallucinationDetection.theorem_A_1`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

With `[Nonempty α]` and `[Countable α]`, for every `C : ℕ → Set α`,

\[
\mathrm{ConsecutivelyIdentifiable}(C)
\quad\Longleftrightarrow\quad
\mathrm{ConditionTwo}(C).
\]

**Hidden assumptions.** The domain is nonempty and countable. Family languages may be empty; no effective family representation or certificate enumeration is assumed.

**Access.** The theorem type exposes only the semantic identifier property, the finite-tell-tale property, and the two domain typeclasses; it supplies no concrete identifier or certificate function.

**Classification.** Semantic/extensional biconditional; non-effective; conditional on the domain typeclasses.

**Risk audit.** It inherits the empty-target vacuity and non-effective tell-tale issues of `corollary_2_2`. It provides no new computational guarantee beyond the equivalence of semantic formulations.

### 6.2 Appendix generation notion

#### 6.2.1 `GenLimit.HallucinationDetection.AppendixGenerationCorrectAt`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For `G : Generator α`, `L : Set α`, `stream : ℕ → α`, and `t : ℕ`, this is the disjunction

\[
\mathrm{output}(G,stream,t)
  \in L\setminus sample(stream,t)
\quad\lor\quad
L\setminus sample(stream,t)=\varnothing.
\]

Thus, if any target point remains unseen, the output must be a fresh target point. If no target point remains unseen, the output is completely unrestricted by this predicate.

**Access and assumptions.** `G` sees only the finite stream prefix. `L` is used only in the correctness specification.

**Classification.** Semantic/extensional round-wise generation criterion.

**Risk audit.** The second disjunct is deliberately weak: after a finite target is exhausted, outputs need not belong to the target and need not be fresh. For an empty target, it is true at every round, though no exact positive presentation exists in the positive-stream model.

#### 6.2.2 `GenLimit.HallucinationDetection.AppendixGeneratesInLimit`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For `G : Generator α` and `C : ℕ → Set α`, the quantifier order is

\[
\forall z,\;
\forall stream:\mathbb N\to α,\;
\mathrm{Presents}(stream,C_z)\to
\exists T,\;
\forall t,\;T\le t\to
\mathrm{AppendixGenerationCorrectAt}(G,C_z,stream,t).
\]

**Access and assumptions.** One generator handles all indexed targets and exact presentations. `T` may depend on the target index and full stream. No target index, target oracle, certificate, or bound is supplied to the runtime generator.

**Classification.** Semantic eventual-generation property; no effectivity, runtime, or probability claim.

#### 6.2.3 `GenLimit.HallucinationDetection.AppendixGeneratableInLimit`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For `C`,

\[
\mathrm{AppendixGeneratableInLimit}(C)
\quad:\Longleftrightarrow\quad
\exists G:\mathrm{Generator}(α),\;
\mathrm{AppendixGeneratesInLimit}(G,C).
\]

**Access and assumptions.** The existential generator may depend on the entire family `C`; its runtime input is only a finite positive prefix.

**Classification.** Semantic existential property.

#### 6.2.4 `GenLimit.HallucinationDetection.infiniteMembers`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For `C : ℕ → Set α`, this language class is

\[
\{L:Set\,α\mid L\in\mathrm{Set.range}(C)\land L\text{ is infinite}\}.
\]

Thus it contains exactly the extensionally distinct infinite sets occurring somewhere in the indexed family.

**Access and assumptions.** The definition has extensional access to the full range of `C` and to set infinitude; it is not an online construction.

**Classification.** Extensional set definition.

**Risk audit.** Family repetitions disappear at the class level. No index witness is retained in the resulting set except existentially through range membership.

#### 6.2.5 `GenLimit.HallucinationDetection.infiniteMembers_countable`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For every `C : ℕ → Set α`, the set `infiniteMembers C` is countable as a set of languages.

No assumptions on `α` are required.

**Access and assumptions.** Only the indexed family `C` is supplied. The theorem concerns the extensional set of languages in its range and provides no enumeration procedure.

**Classification.** Extensional cardinality theorem.

**Risk audit.** This is countability of the **collection of languages**, not countability of each language or of the domain `α`.

#### 6.2.6 `GenLimit.HallucinationDetection.infiniteMembers_uus`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

For every `C`, `GenLimit.LiRamanTewari.UUS (infiniteMembers C)` holds. Expanded, every language belonging to `infiniteMembers C` is infinite.

**Access and assumptions.** Only the family `C` is supplied. No stream, generator, oracle, or additional cardinality assumption is present.

**Classification.** Direct extensional consequence of the definition.

**Risk audit.** This is essentially a projection of the defining conjunction and not an independent structural theorem about `C`.

#### 6.2.7 `GenLimit.HallucinationDetection.theorem_A_2`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`.

With `[Nonempty α]` and `[Countable α]`, for **every** indexed family `C : ℕ → Set α`,

\[
\mathrm{AppendixGeneratableInLimit}(C).
\]

Equivalently, there exists one semantic generator `G` such that, for every index and every exact positive presentation of its target, all sufficiently late outputs are fresh target points whenever unseen target points remain, and are unrestricted once the target has been exhausted.

**Hidden assumptions.** The domain is nonempty and set-theoretically countable. The family is naturally indexed and hence has a countable range. No target language is assumed infinite, nonempty, decidable, or computable. No effective family enumeration beyond the existing index function is required in the statement.

**Access.** The existential generator may depend on the entire family `C` but, at runtime, receives only finite positive histories. No target index or target-membership oracle is an explicit input. The statement provides no threshold, threshold-computation procedure, or bound.

**Classification.** Universal semantic existence theorem under nonempty-countable-domain typeclasses; non-effective; not runtime-bounded or probabilistic.

**Statement-level risk flags.**

- The theorem’s universality depends materially on the weak exhausted-target disjunct: every finite target eventually reaches a state in which correctness places no restriction on output.
- Empty target entries are vacuous because they admit no exact positive presentation.
- The stabilization time is presentation-dependent and unbounded.
- The theorem does not say the generator can recognize that a finite target has been exhausted.


## 7. Primary declarations in `ExampleOne.lean`

**Bundle file label for every declaration in this section:**
`GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`.

This section reports only the formal family and propositions. It does not use the file’s comments to compare the code with any external prose.

#### 7.1 `GenLimit.HallucinationDetection.multiplesFamily`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`.

This is a language family over `ℕ` defined by

\[
\mathrm{multiplesFamily}(i)
=\{x:\mathbb N\mid i+1\text{ divides }x+1\}.
\]

Both family indices and domain elements are ordinary Lean natural numbers; the `+1` shifts appear explicitly in the definition.

**Classification.** Constructive arithmetic set-family definition.

**Access and assumptions.** No oracle, presentation, or typeclass assumption is involved.

#### 7.2 `GenLimit.HallucinationDetection.mem_multiplesFamily`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`.

For implicit `i,x : ℕ`,

\[
x\in\mathrm{multiplesFamily}(i)
\quad\Longleftrightarrow\quad
i+1\mid x+1.
\]

This is definitional equality exposed as an iff theorem.

**Access and assumptions.** The statement is purely arithmetic in the supplied naturals `i` and `x`; no data or oracle access is involved.

**Classification.** Extensional membership lemma.

**Risk audit.** It is a direct restatement of the preceding definition.

#### 7.3 `GenLimit.HallucinationDetection.multiplesFamily_allNonempty`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`.

The family satisfies `GenLimit.Angluin.AllNonempty multiplesFamily`, i.e.

\[
\forall i:\mathbb N,\;\bigl(\mathrm{multiplesFamily}(i)\bigr).\mathrm{Nonempty}.
\]

**Access and assumptions.** This is an unconditional property of the explicitly defined family over `ℕ`; it supplies no runtime object.

**Classification.** Extensional arithmetic theorem.

#### 7.4 `GenLimit.HallucinationDetection.singleton_index_isTellTale`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`.

For every `i : ℕ`, the singleton finite set `{i}` is a tell-tale for index `i` in `multiplesFamily`:

\[
\mathrm{IsTellTale}(\mathrm{multiplesFamily},i,\{i\}).
\]

Expanded, this asserts both:

1. `i ∈ multiplesFamily i`; and
2. for every `j`, if `i ∈ multiplesFamily j` and `multiplesFamily j ⊆ multiplesFamily i`, then `multiplesFamily i ⊆ multiplesFamily j`.

Together with the assumed inclusion in item 2, the second clause forces equality of those two family languages.

**Access and assumptions.** The index `i` is supplied, and the certificate is the explicitly displayed singleton `{i}`. No presentation or oracle is required by the theorem type.

**Classification.** Extensional finite-certificate theorem.

**Risk audit.** The theorem gives a certificate separately for each index but does not state a computable detector or stabilization bound. Here the certificate function `i ↦ {i}` is visibly explicit at the mathematical level.

#### 7.5 `GenLimit.HallucinationDetection.example_1_angluinCondition`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`.

The family satisfies

\[
\mathrm{ConditionTwo}(\mathrm{multiplesFamily}).
\]

Expanded, for every index `i` there exists a finite tell-tale for `multiplesFamily i`.

**Access and assumptions.** This is an unconditional extensional property of the fixed family; it does not expose a detector, presentation, or stabilization bound.

**Classification.** Semantic/extensional family property; constructive witness is available through the preceding theorem, although `ConditionTwo` itself is only existential.

#### 7.6 `GenLimit.HallucinationDetection.example_1_L4_subset_L2`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`.

The exact formal statement is

\[
\mathrm{multiplesFamily}(3)\subseteq\mathrm{multiplesFamily}(1).
\]

**Access and assumptions.** The statement is a closed arithmetic containment fact over the fixed family and uses no online information.

**Classification.** Extensional arithmetic containment theorem.

#### 7.7 `GenLimit.HallucinationDetection.example_1_L3_not_subset_L2`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`.

The exact formal statement is

\[
\neg\bigl(\mathrm{multiplesFamily}(2)\subseteq
          \mathrm{multiplesFamily}(1)\bigr).
\]

**Access and assumptions.** The statement is a closed arithmetic noncontainment fact over the fixed family and uses no online information.

**Classification.** Extensional arithmetic noncontainment theorem.

#### 7.8 `GenLimit.HallucinationDetection.example_1_hallucinationDetectable`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`.

The exact conclusion is

\[
\mathrm{HallucinationDetectable}(\mathrm{multiplesFamily}).
\]

**Hidden assumptions.** There are no explicit typeclass assumptions because the domain is concretely `ℕ`, for which the needed nonempty/countable instances are available. The resulting detector is semantic and may be noncomputable; no detector term, query bound, or stabilization rate appears in the theorem type.

**Classification.** Unconditional semantic detectability theorem for the explicitly defined family.

**Risk audit.** This is a positive existence result, not a concrete executable detector theorem. The same module contains no theorem that this family is non-detectable.

## 8. Primary declarations in `NegativeExamples.lean`

**Bundle file label for every declaration in this section:**
`GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`.

### 8.1 Finite labeled prefixes and the explicit query tree

#### 8.1.1 `GenLimit.HallucinationDetection.labeledPrefix`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`.

For `stream : LabeledStream α` and `t : ℕ`,

\[
\mathrm{labeledPrefix}(stream,t)
=\mathrm{List.ofFn}(i\mapsto stream(i)),\qquad i:\mathrm{Fin}\,t.
\]

It is the chronological list of the first `t` labeled values.

**Access and assumptions.** The definition reads exactly the supplied labeled stream values at indices below `t`; it has no target-validity proof or candidate oracle.

**Classification.** Constructive finite-list definition.

#### 8.1.2 `GenLimit.HallucinationDetection.mem_labeledPrefix_iff`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`.

For implicit `stream`, `t`, and `q : α × Bool`,

\[
q\in\mathrm{labeledPrefix}(stream,t)
\quad\Longleftrightarrow\quad
\exists i:\mathbb N,\;i<t\land stream(i)=q.
\]

**Access and assumptions.** Only the supplied labeled stream, cutoff, and pair occur; no oracle, target index, or future bound is introduced.

**Classification.** Extensional representation lemma.

**Risk audit.** This is a direct prefix-membership fact, not a detector guarantee.

#### 8.1.3 `GenLimit.HallucinationDetection.negativeExampleTree`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`.

This recursive function maps a list of labeled points to an `OracleTree α`:

- on `[]`, return `answer true`;
- on `(_x,true) :: xs`, ignore the point and recurse;
- on `(x,false) :: xs`, query candidate membership of `x`; if the oracle says `x ∈ G`, return `false`, and otherwise continue with the tail.

**Access and assumptions.** Tree construction uses only the supplied finite labeled list. It does not need target membership beyond the labels. At evaluation it receives exact membership-query access to `G`.

**Classification.** Constructive finite oracle-tree algorithm at the syntax level; structurally at most one query per negative-labeled list entry; no public machine/runtime theorem.

#### 8.1.4 `GenLimit.HallucinationDetection.eval_negativeExampleTree_eq_true_iff`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`.

For every `G : Set α` and `xs : List (α × Bool)`,

\[
\mathrm{OracleTree.eval}\;G
  (\mathrm{negativeExampleTree}(xs))=\mathtt{true}
\]

if and only if

\[
\forall x:\alpha,\;\forall b:Bool,\;
(x,b)\in xs\to b=\mathtt{false}\to x\notin G.
\]

Thus the tree accepts exactly when no point labeled false in the list belongs to the candidate set.

**Access and assumptions.** Evaluation has exact membership-oracle access to `G`; the finite list and its Boolean labels are supplied directly.

**Classification.** Exact semantic/extensional correctness theorem for the finite tree.

#### 8.1.5 `GenLimit.HallucinationDetection.negativeExampleDetector`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`.

This detector has type `NegativeExampleDetector α` and is defined by

\[
(t,xs)\longmapsto
\mathrm{negativeExampleTree}(\mathrm{List.ofFn}(xs)).
\]

The value `t` is used through the type/length of `xs`; the term’s first binder is otherwise ignored.

**Access and assumptions.** The detector sees the entire finite labeled prefix and queries `G` exactly at negatively labeled points selected by the recursive tree. It is a single polymorphic definition independent of `C`.

**Classification.** Constructive finite-query detector syntax. Overall execution against arbitrary sets remains semantic because `OracleTree.eval` is noncomputable.

### 8.2 Universal negative-example detectability

#### 8.2.1 `GenLimit.HallucinationDetection.theorem_2_3`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`.

For an arbitrary type `α` and every family `C : ℕ → Set α`, with **no** `[Nonempty α]`, `[Countable α]`, decidability, enumerability, or computability assumptions,

\[
\mathrm{DetectableWithNegativeExamples}(C).
\]

After expansion, there exists one negative-example detector such that, for every target index `z`, every complete correctly labeled enumeration of the whole domain for `C_z`, and every candidate set `G`, there is a time after which the detector returns `true` exactly when `G ⊆ C_z` at every round.

**Access.** The detector receives all labels in the finite prefix and finite adaptive membership-query access to `G`. The validity premise promises that every domain point appears eventually and is labeled exactly by membership in the target. The threshold may depend on the target index, the entire labeled enumeration, and `G`.

**Classification.** Universal semantic existence theorem; no computability predicate, machine model, uniform runtime, or probabilistic claim. A separate explicit negative-example detector definition appears in the same module, but the theorem type itself only states an existential witness.

**Statement-level risk flags.**

- For uncountable `α`, no complete labeled enumeration `ℕ → α × Bool` can cover the domain, so the universal correctness requirement is vacuous.
- For empty `α`, no labeled stream exists, so it is likewise vacuous.
- Countability is therefore not needed in the theorem type because countability is implicit in the **premise that a valid labeled enumeration is supplied**, and absent-premise cases impose no obligations.
- Even when valid streams exist, no bound is given on when a particular counterexample point appears.
- Exact target labels for every domain point constitute much stronger information than positive data alone.
- Candidate sets remain arbitrary and are accessed through an exact membership oracle.


## 9. Explicit quantifier-and-access ledger

The following ledger expands the highest-level notions and records what is and is not available to the formal object.

| Formal object/property | Exact outer quantifier order | Runtime input/access | Information that may be hardwired or used only in existence proofs | Dependence of convergence/certificate witnesses |
|---|---|---|---|---|
| `Detector α` | `∀ t, (Fin t → α) → OracleTree α` | Time, complete positive prefix, then adaptive membership answers from candidate `G` during tree evaluation | An existential detector witnessing a property may depend on the whole family `C` | No bound is part of the interface |
| `DetectsHallucinations D C` | `∀ z, ∀ stream, Presents stream (C z) → ∀ G, ∃ T, ∀ t, T ≤ t → …` | `D` sees only each finite prefix and candidate-oracle answers | The specification mentions `C_z`; `D` itself is fixed for `C` | `T` may depend on `z`, the full stream, and `G`; not uniform and not supplied to `D` |
| `HallucinationDetectable C` | `∃ D, DetectsHallucinations D C` | As above | `D` may be noncomputably hardwired to `C` | Pointwise thresholds inherited from `DetectsHallucinations` |
| `SemanticIdentifier α` | `∀ t, (Fin t → α) → ℕ` | Time and complete positive prefix only | An existential witness may depend on the whole indexed family | No bound is part of the interface |
| `SemanticallyIdentifies M C` | `∀ z, ∀ stream, Presents stream (C z) → ∃ j, C j = C z ∧ ∃ T, ∀ t ≥ T, output = j` | `M` sees only prefixes | `M` may be hardwired to `C`; duplicates are allowed | Both `j` and `T` may depend on `z` and the entire presentation |
| `ConditionTwo C` | `∀ i, ∃ T : Finset α, IsTellTale C i T` | No online algorithm is specified | The finite certificate may depend on the index and full extensional family | No uniform chooser, enumeration stage, size bound, or computability witness |
| `chosenTellTale C h` | `∀ i, Finset α` after supplying `h : ConditionTwo C` | Not an online learner | Uses `h` and classical choice to hardwire one certificate per index | Certificates are available from stage zero in the constant approximation |
| `detectorFromIdentifier C enumerate M` | Produces one detector from supplied `C`, `enumerate`, and `M` | Positive prefix; candidate queries | Exact membership in the current conjectured `C_i`; full domain enumeration | Detection threshold inherits identifier convergence and the enumeration position of a counterexample |
| `identifierFromDetector C D` | Produces one identifier from supplied `C` and `D` | Positive prefix | Evaluates `D` against exact candidate-language oracles `C_i`; searches least bounded eligible index | No executable search or rate is asserted |
| `NegativeExampleDetector α` | `∀ t, (Fin t → α × Bool) → OracleTree α` | Time, complete labeled prefix, candidate membership answers | The explicit detector is family-independent | No bound is part of the interface, though its particular tree has at most one query per negative-labeled entry |
| `DetectsWithNegativeExamples D C` | `∀ z, ∀ stream, IsLabeledEnumeration stream (C z) → ∀ G, ∃ T, ∀ t ≥ T, …` | Finite labeled prefix and candidate oracle | Validity premise promises eventual exact labels for every domain point | `T` may depend on `z`, the full enumeration, and `G`; no occurrence-rate bound |
| `ConsecutivelyIdentifiesFrom M C z stream` | `∃ T, ∀ t, T < t → adjacent equality ∧ extensional target equality` | Prefixes only | Family is part of the specification; identifier may be family-dependent | `T` depends on target/presentation in the collection-level notion |
| `AppendixGeneratesInLimit G C` | `∀ z, ∀ stream, Presents stream (C z) → ∃ T, ∀ t ≥ T, …` | Prefix only | Existential `G` may depend on all of `C` | `T` may depend on `z` and full presentation; no target-uniform threshold |
| `presentationFromDomainEnumeration enumerate L hL` | A stream defined from supplied `enumerate`, `L`, and `hL` | Not a detector/generator runtime object | Exact target-membership tests and a chosen target witness | No effective construction is claimed |
| Locking lemmas | Usually quantify over a supplied identifier, exact presentation(s), convergence property, lock, and correctness equality | No new runtime interface | Strong auxiliary witnesses and global correctness hypotheses are supplied | Existence conclusions have no length or search bound |

### 9.1 Access conclusions

1. **Target index.** Neither the positive detector nor the public identifier/generator interface receives the true index `z` at runtime.
2. **Target language.** The target appears in correctness predicates. Some proof-side constructions and reductions have exact extensional access to family languages or a selected target, but that access is not exposed as a runtime target oracle in `Detector` or `Generator`.
3. **Candidate set.** Detectors receive candidate information only through a finite adaptive exact membership oracle represented by `OracleTree.eval`.
4. **Enumeration.** The separate identification-to-detection reduction lemma takes a supplied surjective `ℕ → α`. The principal biconditional exposes only `[Nonempty α] [Countable α]` and no enumeration witness or computability condition.
5. **Presentation prefix versus future.** Runtime objects see only prefixes. Existential stabilization times may depend on the entire infinite stream, and the statements do not require those times to be known or computable.
6. **Certificates.** `ConditionTwo` supplies finite tell-tales only existentially. A separate public definition, `chosenTellTale`, selects them noncomputably; the principal theorem types do not expose that chooser.
7. **Bounds.** No public claim supplies sample-complexity, query-depth, tree-size, locking-sequence-length, tell-tale-size, or runtime bounds.

## 10. Statement-level risk and faithfulness flags

These flags concern the strength and logical shape of the Lean statements themselves. They do not compare the code to any external paper.

### 10.1 Semantic rather than effective characterizations — high significance

The central properties quantify over arbitrary Lean functions and arbitrary sets. Neither `theorem_2_1` nor `corollary_2_2` mentions `Computable`, `EffectiveIndexedFamily`, `EffectiveInferrable`, `ConditionOne`, a machine encoding, or a recursive oracle. Therefore the formal characterization is at a semantic/extensional oracle level.

The imported Angluin development contains separate effective interfaces, but the primary Paper 08 theorem statements use `SemanticIdentifier` and `ConditionTwo`, not those effective notions.

### 10.2 Exact arbitrary-set oracles — high significance

`OracleTree.eval` branches on exact propositions `x ∈ G` for an arbitrary set. This allows candidate sets with no finite representation and no computable membership procedure. Each tree is finite, but the oracle is idealized and cost-free in the formal model.

### 10.3 Family-language oracle access inside one reduction — high significance

`identifierFromDetector` tests `DetectorCandidate` by evaluating the detector tree against `C_i` as the candidate oracle and by checking prefix consistency with `C_i`. For arbitrary set-valued `C`, this is noncomputable exact access to each family language. The theorem is therefore a semantic reduction, not automatically an implementation reduction.

### 10.4 Nonconstructive certificate selection — high significance

`chosenTellTale` takes a proof of `ConditionTwo` and uses `Classical.choose` to select one tell-tale per index. `constantTellTaleApproximation` exposes the selected final certificate at every stage. This is logically valid at the semantic level but can encode the answer and supplies no method for discovering certificates from data.

### 10.5 Pointwise rather than uniform convergence — high significance

In positive and negative detection, the threshold lies inside the quantifiers over stream and candidate set. In identification and appendix generation, it lies inside the quantifier over presentation. None of the main statements gives one threshold for all streams, all candidate sets, all targets, or all family members.

### 10.6 Empty-language vacuity — high significance

Because `Presents stream L` means `range stream = L`, no stream presents `∅`. Every positive-presentation obligation for an empty target is therefore vacuous. The finite-tell-tale side simultaneously treats `∅` trivially via the empty tell-tale. This makes the equivalences formally total over families that contain empty languages, but the empty case carries no observational learning content.

### 10.7 Complete-labeled-enumeration vacuity — high significance

`theorem_2_3` has no countability assumption because its correctness condition is conditional on `IsLabeledEnumeration`. When the domain has no complete natural-number enumeration, there are no valid streams, and detectability is vacuous. The theorem is nonvacuous only for domains for which such streams actually exist.

### 10.8 Complete labels are a very strong information source — high significance

A valid labeled enumeration eventually supplies the exact target-membership label of every domain point. The explicit negative-example detector only needs to wait until some candidate point outside the target appears with label `false`. No rate at which points appear is assumed, so the theorem remains qualitative.

### 10.9 Weak finite-target appendix criterion — high significance

`AppendixGenerationCorrectAt` imposes no output restriction once `L \ sample = ∅`. This makes every finite target automatically harmless after its elements have all appeared. The universal `theorem_A_2` should be read with this disjunction fully expanded; it is not a theorem that the generator forever emits valid or fresh elements for finite targets.

### 10.10 No explicit quantitative finite-query theorem — medium significance

`OracleTree` guarantees a finite interaction in each round. The two named recursive trees visibly use at most one query per list entry, but no primary declaration states a query-count bound, tree-depth bound, total runtime, or computable construction time. Arbitrary detectors may return trees of unbounded size as a function of the history.

### 10.11 Set-theoretic countability, not effective coding — medium significance

`[Countable α]` is sufficient to obtain a set-theoretic surjection from `ℕ` under `[Nonempty α]`. No `Encodable α`, computable enumeration, decidable equality, or recursive presentation is required by the principal theorem types.

### 10.12 Indexed-family and duplicate-index effects — medium significance

The family is `ℕ → Set α`, not a set of distinct languages. Identification may stabilize to any index extensionally equal to the target, and the stable index may depend on the presentation. Tell-tales are index-sensitive but their defining condition is extensional in the associated language and the family’s containment relations.

### 10.13 Strong supplied hypotheses in locking lemmas — medium significance

The locking-to-tell-tale lemmas accept exact presentations, all-stream convergence, supplied locks, and a supplied equality `C_j=C_z`. These are not circular in the strict sense—the tell-tale conclusion contains a new universal containment property—but they are strong link conditions and do not by themselves construct the required inputs.

### 10.14 Packaging and near-tautological helper declarations — low significance

Several public helpers mainly expose representations or chosen witnesses:

- `mem_domainPrefix_iff` and `mem_labeledPrefix_iff` characterize list membership;
- `chosenTellTale_spec` restates the specification of a chosen existential witness;
- `constantTellTaleApproximation_spec` packages a constant function as eventually stable;
- `identifierFromDetector_candidate` and `identifierFromDetector_le_of_candidate` expose `Nat.find` correctness/minimality;
- `listIdentifierOf_streamPrefix` identifies two encodings of the same prefix;
- `mem_multiplesFamily` is definitional;
- `infiniteMembers_uus` projects an explicit defining conjunct.

These are useful interfaces but should not be counted as independent headline mathematical results.

### 10.15 No apparent inconsistency among the primary statement types

No primary theorem simultaneously asserts a proposition and its negation, and no public axiom is introduced. The containment and noncontainment facts in `ExampleOne.lean` concern different indexed languages and are compatible with the positive detectability theorem. This statement-level audit found no inconsistency in the declared propositions.

The audit does **not** re-run Lean or validate proof bodies, so this is not an independent kernel-compilation or proof-correctness certification.

## 11. Dependency and interface ledger

This section separates imported meanings from Paper 08’s primary claims.

### 11.1 `GenLimit.Core.Countable` / `GenLimit.Generic`

The primary modules rely on these imported definitions:

- `Language α := Set α`.
- `LanguageClass α := Set (Set α)`.
- `LanguageFamily α := ℕ → Set α`.
- `Stream α := ℕ → α`.
- `Generator α := ∀ t : ℕ, (Fin t → α) → α`.
- `Presents stream L := Set.range stream = L`.
- `StreamIn stream L := Set.range stream ⊆ L`.
- `sequenceSample xs`: the finite set of distinct values in `xs : Fin t → α`; this definition is noncomputable over arbitrary `α` because it uses classical equality.
- `sample stream t`: the finite set of distinct stream values before `t`; likewise noncomputable as a `Finset` construction over arbitrary `α`.
- `output G stream t := G t (fun i => stream i)`.
- `CorrectAt G L stream t := output G stream t ∈ L ∧ output G stream t ∉ sample stream t`.

Imported prefix/sample lemmas provide monotonicity, eventual appearance of presented elements, finite-set exhaustion of finite targets, and exact sample-cardinality times for infinite presentations. These are dependency facts, not Paper 08 declarations.

### 11.2 `GenLimit.Dependency_Angluin1980.Definitions`

The key semantic interfaces are:

- `SemanticIdentifier α := ∀ t, (Fin t → α) → ℕ`.
- `identifierOutput M stream t := M t (fun i => stream i)`.
- `ConvergesTo M stream j := ∃ T, ∀ t ≥ T, identifierOutput M stream t = j`.
- `IdentifiesFrom M C z stream := ∃ j, C_j=C_z ∧ ConvergesTo M stream j`.
- `SemanticallyIdentifies M C := ∀ z stream, Presents stream C_z → IdentifiesFrom M C z stream`.
- `AllNonempty C := ∀ i, (C_i).Nonempty`.
- `IsTellTale C i T := T⊆C_i ∧ ∀j, T⊆C_j → C_j⊆C_i → C_i⊆C_j`.
- `ConditionTwo C := ∀ i, ∃ T : Finset α, IsTellTale C i T`.
- `IsTellTaleApproximation C A`: stagewise monotonicity plus eventual equality, for each index, to a finite tell-tale.

The same dependency file also defines effective objects—`EffectiveIndexedFamily`, `EffectiveInferrable`, and `ConditionOne`—with explicit Mathlib `Computable` predicates. None of those effective predicates appears in the primary Paper 08 theorem statements. This distinction is central to reading the formal claims correctly.

### 11.3 Imported tell-tale-approximation interface

The primary declaration `constantTellTaleApproximation_spec` mentions the imported predicate `IsTellTaleApproximation`. Its statement requires stagewise monotonicity and, for every index, eventual exact equality to some finite `IsTellTale` witness. No computability predicate is part of that interface.

Other semantic-learner theorems in the imported module occur only outside the primary declaration types; in accordance with the audit rule, they are not used here as evidence for a Paper 08 mathematical claim.

### 11.4 Imported list and locking interfaces

From the Angluin dependency modules:

- `streamPrefix stream t` is the chronological list of the first `t` stream values.
- `ListWithin xs L := ∀ x, x ∈ xs → x ∈ L`.
- `IsLockingSequence M L xs j := ListWithin xs L ∧ ∀ tail, ListWithin tail L → M (xs ++ tail)=j`.
Paper 08’s generic locking declaration types reuse these interfaces over arbitrary `α`. Other imported diagonal/locking constructions that occur only in proof bodies are deliberately excluded from statement evidence.

### 11.5 Imported Li–Raman–Tewari interface appearing in a primary type

The primary theorem `infiniteMembers_uus` mentions the imported definition

- `UUS H := ∀ L, L ∈ H → L.Infinite`.

No other Li–Raman–Tewari notion appears in a primary Paper 08 declaration type. Other imported generation theorems or constructions that occur only in theorem proof bodies are therefore not used as semantic evidence in this reconstruction and are not counted as Paper 08 results.

### 11.6 Mathlib typeclass and logical interfaces

- `[Nonempty α]` supplies an element of `α` but no distinguished computable encoding.
- `[Countable α]` is set-theoretic countability. Together with nonemptiness it supports existence of a surjection `ℕ → α`.
- `Function.Surjective enumerate` means every `x : α` has some natural preimage.
- `Set.Countable`, `Set.Finite`, `Set.Infinite`, and `Finset` are extensional cardinality/finite-set interfaces.
- Classical proposition decidability and choice appear in explicitly noncomputable primary definitions. No public `[DecidableEq α]` or candidate-membership decider is required.

## 12. What the primary Lean statements establish, in compressed theorem form

Under a nonempty countable example type:

1. semantic finite-query hallucination detectability is equivalent to semantic positive-data identification (`theorem_2_1`);
2. semantic detectability is equivalent to the existence, for each indexed language, of a finite tell-tale (`corollary_2_2`);
3. the consecutive-adjacent-guess formulation is equivalent to the stable-index formulation and hence to the same tell-tale condition (`definition_3_equivalence`, `theorem_A_1`);
4. every indexed family satisfies the appendix’s finite-language-aware generation property (`theorem_A_2`).

Without domain typeclass assumptions:

5. detection implies semantic identification (`lemma_3_2_detection_implies_identification`);
6. a supplied surjective domain enumeration plus semantic identification implies detection (`lemma_3_1_identification_implies_detection`);
7. finite tell-tale existence implies semantic identification (`identifiable_of_conditionTwo`);
8. every family is detectable in the negative-example model, conditional on complete correctly labeled domain enumerations (`theorem_2_3`).

For the explicitly defined arithmetic family `multiplesFamily`:

9. every indexed language is nonempty;
10. `{i}` is a finite tell-tale for index `i`;
11. the family satisfies `ConditionTwo` and is semantically hallucination-detectable;
12. `multiplesFamily 3 ⊆ multiplesFamily 1`, while `multiplesFamily 2 ⊄ multiplesFamily 1`.

## 13. What the primary Lean statements do **not** establish

The declarations do not establish any of the following:

1. **Computable detectors or identifiers.** No principal theorem has a `Computable` conclusion or assumes a computable family/member oracle in its type.
2. **Efficient algorithms.** There is no Turing/RAM/circuit model, source code extraction theorem, polynomial-time bound, or finite-memory bound.
3. **Uniform query complexity.** Although each `OracleTree` is finite, no theorem bounds tree depth, number of candidate queries, or total work uniformly in time/history.
4. **Uniform sample complexity.** Stabilization times may depend on the full presentation and candidate set; no numerical rate is supplied.
5. **Effective tell-tales.** `ConditionTwo` gives finite certificates only existentially. It does not provide a computable, uniformly enumerable, or size-bounded certificate family.
6. **The effective Angluin characterization.** The primary equivalence is not stated with `ConditionOne`, `EffectiveIndexedFamily`, or `EffectiveInferrable`.
7. **Decidable target or family membership.** Languages are arbitrary sets. Exact membership is used semantically in noncomputable constructions and oracle evaluations.
8. **Probabilistic or approximate detection.** There are no distributions, random models, confidence levels, error rates, or approximation guarantees.
9. **Robustness to noisy or incomplete data.** Positive streams are exact presentations; labeled streams are complete and perfectly labeled.
10. **A detector that receives only an LLM’s text output or logits.** No model architecture, prompt, probability distribution, semantic truth predicate, or natural-language representation occurs in the formal types.
11. **One stabilization time valid for all candidate sets or all streams.** All convergence is pointwise in the relevant quantified objects.
12. **Nonvacuous positive-data behavior for empty targets.** Empty target entries have no exact presentations.
13. **Nonvacuous negative-example behavior on arbitrary uncountable domains.** `theorem_2_3` is conditional on a complete natural-number-indexed labeled enumeration and is vacuous when none exists.
14. **Perpetually valid generation for finite targets in Theorem A.2.** After the target is exhausted, the appendix criterion permits arbitrary output.
15. **A concrete negative family in the primary modules.** The characterization can imply impossibility from failure of `ConditionTwo`, but no primary Paper 08 declaration proves `¬HallucinationDetectable C` for a particular displayed family.
16. **Comparison with the author paper.** This stage contains no claim that the formal statements match, strengthen, weaken, or contradict any external source.
17. **Independent proof validation.** Proof bodies were deliberately excluded from semantic evidence and the bundle was not independently compiled in this audit.

## 14. Concise audit conclusion

The primary Lean code states a coherent family of **semantic, extensional, finite-candidate-query** results. Its central characterization is:

\[
\mathrm{HallucinationDetectable}(C)
\iff
\mathrm{IdentifiableInLimit}(C)
\iff
\mathrm{ConditionTwo}(C)
\]

for naturally indexed families over nonempty countable domains, where detection uses finite adaptive membership queries to an arbitrary candidate set, identification is by an arbitrary semantic function on positive prefixes, and `ConditionTwo` is mere existence of finite tell-tales.

The most consequential formal limitations are the absence of effectivity and quantitative bounds, noncomputable access to arbitrary sets and chosen certificates, pointwise convergence, vacuity for empty positive targets, vacuity of the negative-example theorem when no complete labeled enumeration exists, and the unrestricted-output disjunct for exhausted finite targets in the appendix generation notion.

Within the statement-only scope, no contradiction or circular definition was found. Several helper declarations are definitional or packaging lemmas, and several locking lemmas rely on strong supplied witnesses, but the principal equivalences and existence theorems do not merely restate their assumptions. The remaining uncertainty is proof-level rather than statement-level: this reconstruction does not inspect proof bodies or independently certify compilation.
