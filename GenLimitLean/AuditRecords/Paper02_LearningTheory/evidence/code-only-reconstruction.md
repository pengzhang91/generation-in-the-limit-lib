# 02 — Paper02_GenerationThroughTheLensOfLearningTheory — Generation through the Lens of Learning Theory — Lean Statement Reconstruction

## Audit status and provenance

This document is a Stage 1, code-only reconstruction of the mathematics stated by the current Lean source bundle.

- Audited bundle: `02__Paper02_GenerationThroughTheLensOfLearningTheory__lean-source-bundle.txt`
- Exact byte size verified: `295728`
- Exact SHA-256 verified: `46a46f86c03e8fa7300b7efa3d223141942bee91d95476c7afa818bf889c7146`
- Repository provenance recorded in the bundle: branch `main`, commit `dfcd13534f9d51642a9f88904268e95454c88f7f`
- Root umbrella: `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory.lean`
- Bundle contents: 21 local source files, comprising 2 dependency files, 18 files in the same-named target subtree, and the umbrella file.
- Unresolved local imports: none, according to the manifest.
- Public target-subtree declaration census: 291 declarations — 185 theorems, 95 definitions, 10 abbreviations, and 1 inductive type.
- No target-subtree `axiom` declarations occur.

All mathematical interpretations below come from declaration types, proposition expressions, and semantic bodies of definitions. Comments, docstrings, theorem names, module names, and informal labels were not used as evidence for what a proposition means. Declaration names and source paths are reported only as identifiers. Theorem proof bodies were not used as evidence.

For compactness, throughout this report

```text
P02/...
```

means the exact path prefix

```text
GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/...
```

The two files under `GenLimitLean/GenLimit/Core/` are dependency scope only. Their definitions are unfolded where needed, but their standalone theorems are not counted as target-paper claims.

## Abstract

The target Lean development defines deterministic generation from positive data over a generic example type `α`. A language is a set of examples, a language class is a set of languages, a stream is a function `ℕ → α`, and a generator is an unrestricted function that maps each ordered finite history to one output. Correctness at time `t` means that the output belongs to the target language and is absent from the distinct input observations seen strictly before `t`. The output history is not fed back to the generator, and freshness is measured only against observed inputs, not against earlier generator outputs.

Three ordinary generation notions are formalized. Limit generation is tested on exact presentations of a target language. Uniform generation uses one generator and one class-wide threshold in the number of distinct observed examples; after any prefix having exactly that size, every later output must be valid and unseen. Nonuniform generation uses one generator but allows the threshold to depend on the target language, while remaining independent of the stream. Under the assumption that every target language is infinite, the code proves the implication chain uniform generation ⇒ nonuniform generation ⇒ generation in the limit.

The central ordinary characterization is in terms of a positive version space and its common core. A finite sample is a closure witness when some class member contains it and the intersection of all class members containing it is finite. Finite closure dimension is proved equivalent to uniform generatability on a nonempty countable example type under the infinite-support assumption. For a class of closure dimension `d`, the optimal uniform threshold is proved to lie between `d` and `d + 1`; exact equality is not asserted. Nonuniform generatability is characterized by the existence of a monotone countable cover by finite-closure-dimension subclasses. A finite, not necessarily monotone, cover by finite-closure-dimension subclasses is only proved sufficient for generation in the limit.

The development supplies explicit separations. It constructs an uncountable uniformly generatable class; a countable class that is nonuniformly but not uniformly generatable; a class generatable in the limit but not nonuniformly generatable; two closure-dimension-zero classes whose union is not nonuniformly generatable; and a countable sequence of closure-dimension-zero classes whose union is not generatable in the limit.

A separate prediction section defines VC and Littlestone shattering combinatorially. Crucially, the predicates named `PACLearnableViaVC` and `OnlineLearnableViaLittlestone` are definitionally identical to finite VC dimension and finite Littlestone dimension, respectively. No probabilistic PAC model, iid sample, risk, online loss, regret, or learning algorithm is formalized or linked by theorem. The six-way landscape proved there is therefore a combinatorial landscape involving the two dimension-finiteness proxies and uniform generation, not a formal theorem about literal PAC or online learnability.

The code also defines Eventually Unbounded Closure (EUC): along every exact presentation of every class member, the class common core becomes infinite at some finite time. EUC itself implies generation in the limit. Monotone countable covers and finite covers by EUC classes are proved sufficient for generation in the limit. A stronger arbitrary-stream predicate is separately defined and a concrete class is proved to satisfy EUC while failing the arbitrary-stream predicate; the universal equivalence between the two formal predicates is therefore refuted inside the target development.

Finally, the development formalizes prompted multiclass generation. A prompted generator sees triples consisting of an example, its true label, and the current prompt. It must output a globally unobserved example having the current prompted label. Prompted uniform generation has a class-wide threshold; prompted nonuniform generation permits a threshold depending on the target hypothesis but not on the prompt or either stream. A prompted closure dimension yields characterizations parallel to the ordinary setting. With finitely many prompts, every finite hypothesis class has finite prompted closure dimension, and every countable class satisfying prompted infinite-support assumptions is prompted-nonuniformly generatable and prompted-generatable in the limit. With an infinite prompt type, the code constructs a two-hypothesis class satisfying the prompted infinite-support assumption that is neither prompted-uniformly nor prompted-nonuniformly generatable.

## 1. Formal setting and exact definitions

### 1.1 Dependency-layer primitives actually used by Paper 02

The generic dependency layer is `GenLimitLean/GenLimit/Core/Countable.lean`.

Let `α` be an arbitrary Lean type.

- A **language** is a subset of `α`:
  \[
  \mathrm{Language}(\alpha)=\mathcal P(\alpha).
  \]
- A **language class** is a set of languages:
  \[
  \mathrm{LanguageClass}(\alpha)=\mathcal P(\mathcal P(\alpha)).
  \]
- A **stream** is a function `stream : ℕ → α`.
- A **generator** is a family of functions
  \[
  G_t:(\mathrm{Fin}(t)\to\alpha)\to\alpha,
  \]
  equivalently `G : ∀ t : ℕ, (Fin t → α) → α`.
- `Presents stream L` means
  \[
  \operatorname{range}(\text{stream})=L.
  \]
  Repetitions are allowed, but every point of `L` must occur at least once.
- `StreamIn stream L` means
  \[
  \operatorname{range}(\text{stream})\subseteq L.
  \]
  It does **not** require the stream to enumerate all of `L`.
- For a finite history `xs : Fin t → α`, `sequenceSample xs` is the finite set of its distinct values.
- For a stream and time `t`,
  \[
  S_t(\text{stream}) := \mathrm{sample}(\text{stream},t)
  =\{\text{stream}(s):s<t\}.
  \]
  Thus the sample is a set of distinct observations and excludes the observation at index `t`.
- `output G stream t` is `G` applied to the ordered prefix `stream|_{\{0,\ldots,t-1\}}`.
- `CorrectAt G L stream t` means
  \[
  G(\text{stream}_{<t})\in L
  \quad\text{and}\quad
  G(\text{stream}_{<t})\notin S_t(\text{stream}).
  \]

Two access-model consequences are immediate from these definitions.

1. The generator sees the **ordered prefix with repetitions**, even though the threshold and freshness predicates use only the set of distinct observations.
2. Earlier generator outputs are not part of the history unless they independently occur in the exogenous input stream. The formal freshness condition does not require outputs at different times to be pairwise distinct.

The fixed-`ℕ` dependency file `GenLimitLean/GenLimit/Core/Basic.lean` also defines an indexed language family and a Boolean membership oracle. No declaration in the Paper 02 subtree takes such an oracle, indexed family, or consistency predicate as an input. The target statements use the generic set-of-languages interface above.

### 1.2 Infinite-support assumption

**Declaration:** `UUS`  
**Source:** `P02/Definitions.lean:19`

For a language class `H`,

\[
\mathrm{UUS}(H)
\quad\Longleftrightarrow\quad
\forall L\in H,\; L\text{ is infinite}.
\]

This is a property of the target languages, not of the streams. A `StreamIn` stream may still have finite range or be constant.

### 1.3 Positive version space, common core, and option-valued closure

**Declarations:** `versionSpace`, `commonCore`, `closure`  
**Source:** `P02/Definitions.lean:23-35`

For a finite set `S ⊆ α`,

\[
V_H(S)=\{L\in H:S\subseteq L\}.
\]

The common core is

\[
\operatorname{core}_H(S)
=\{x\in\alpha:\forall L\in V_H(S),\;x\in L\}
=\bigcap_{L\in V_H(S)}L
\]

with the Lean universal-quantifier convention. In particular, if the version space is empty, `commonCore H S` is the whole universe `Set.univ`, because the defining universal implication is vacuous.

The option-valued closure is

\[
\operatorname{closure}_H(S)=
\begin{cases}
\texttt{some}(\operatorname{core}_H(S)),&V_H(S)\neq\varnothing,\\
\texttt{none},&V_H(S)=\varnothing.
\end{cases}
\]

The dimension predicates below do not inspect the `Option` object directly. They explicitly require a nonempty version space and then ask whether the common core is finite or infinite.

The public structural facts state exactly:

- `mem_versionSpace_iff`: membership in `versionSpace H S` is equivalent to being in `H` and containing `S`.
- `closure_eq_none_iff`: closure is `none` exactly when the version space is empty.
- `closure_eq_some_iff`: closure is `some C` exactly when the version space is nonempty and `C` equals the common core.
- `sample_subset_commonCore`: every point of `S` lies in the common core, even in the empty-version-space case.
- `commonCore_subset_of_mem_versionSpace`: if `L ∈ V_H(S)`, then `core_H(S) ⊆ L`.

### 1.4 Ordinary generation notions, fully expanded

#### Generation in the limit

**Declarations:** `IsLimitGenerator`, `GeneratableInLimit`  
**Source:** `P02/Definitions.lean:98-105`

A fixed generator `G` is a limit generator for `H` iff

\[
\forall L\in H,\;
\forall x:\mathbb N\to\alpha,\;
\bigl(\operatorname{range}(x)=L\bigr)
\Rightarrow
\exists T\;\forall s\ge T,
\quad G(x_{<s})\in L\setminus S_s(x).
\]

The class is generatable in the limit iff there exists one such `G` for the whole class.

The stabilization time `T` may depend on the target language and on the particular exact presentation stream. No threshold in the number of distinct examples is part of this definition.

#### Uniform generation at threshold `d`

**Declarations:** `IsUniformGeneratorAt`, `UniformlyGeneratable`  
**Source:** `P02/Definitions.lean:111-120`

A fixed `G` works uniformly at threshold `d` iff

\[
\forall L\in H,
\forall x:\mathbb N\to\alpha,
\operatorname{range}(x)\subseteq L,
\forall t,
\bigl|S_t(x)\bigr|=d
\Rightarrow
\forall s\ge t,
G(x_{<s})\in L\setminus S_s(x).
\]

The class is uniformly generatable iff

\[
\exists G\;\exists d\in\mathbb N,
\quad G\text{ works uniformly at threshold }d.
\]

The quantifier over the trigger time `t` is universal: every prefix having exactly `d` distinct observations triggers correctness at all later times. A stream that never reaches `d` distinct observations imposes no threshold-triggered obligation. The threshold counts distinct input examples, not rounds.

#### Nonuniform generation

**Declarations:** `IsNonuniformGenerator`, `NonuniformlyGeneratable`  
**Source:** `P02/Definitions.lean:123-132`

A fixed `G` is a nonuniform generator iff

\[
\forall L\in H,
\exists d_L\in\mathbb N,
\forall x:\mathbb N\to\alpha,
\operatorname{range}(x)\subseteq L,
\forall t,
|S_t(x)|=d_L
\Rightarrow
\forall s\ge t,
G(x_{<s})\in L\setminus S_s(x).
\]

The class is nonuniformly generatable iff one generator `G` satisfies this. The threshold may depend on `L`, but it is chosen before the stream and therefore must be uniform over all streams whose range is contained in that target.

### 1.5 Closure dimension

**Declarations:** `IsClosureWitness`, `ClosureDimensionAtMost`, `HasClosureDimension`, `HasFiniteClosureDimension`, `HasInfiniteClosureDimension`  
**Source:** `P02/Closure.lean:22-53`

A finite set `S` is a closure witness for `H` iff

\[
V_H(S)\neq\varnothing
\quad\text{and}\quad
\operatorname{core}_H(S)\text{ is finite}.
\]

`ClosureDimensionAtMost H d` means

\[
\forall S\subseteq_{\mathrm{fin}}\alpha,
\quad |S|>d\ \wedge\ V_H(S)\neq\varnothing
\Rightarrow
\operatorname{core}_H(S)\text{ is infinite}.
\]

`HasClosureDimension H d` is the conjunction of that upper-bound property with

\[
d=0
\quad\text{or}\quad
\exists S,\ |S|=d\text{ and }S\text{ is a closure witness}.
\]

Thus for positive `d`, a witness of exact size `d` is required. For `d=0`, no size-zero witness is required; the first conjunct alone controls all nonempty finite samples.

Finite closure dimension means `∃ d, HasClosureDimension H d`.

Infinite closure dimension means

\[
\forall d\in\mathbb N,
\exists S\subseteq_{\mathrm{fin}}\alpha,
\quad d\le |S|,
\quad V_H(S)\neq\varnothing,
\quad \operatorname{core}_H(S)\text{ finite}.
\]

This is an unbounded-witness formulation, not a literal extended-natural value stored in a datatype.

### 1.6 Uniform generation sample complexity

**Declarations:** `uniformGenerationSampleComplexity`, `optimalUniformGenerationSampleComplexity`  
**Source:** `P02/UniformSampleComplexity.lean:42-49,139-147`

For a fixed generator `G`,

\[
d_G(H)=
\begin{cases}
\min\{d\in\mathbb N:G\text{ works uniformly at }d\},&\text{if the set is nonempty},\\
\top,&\text{otherwise},
\end{cases}
\]

as an element of `WithTop ℕ`.

The class-optimal value is

\[
d^*(H)=
\begin{cases}
\min\{d\in\mathbb N:\exists G,\ G\text{ works uniformly at }d\},&\text{if nonempty},\\
\top,&\text{otherwise}.
\end{cases}
\]

The minimum is over thresholds, not over an ordering of generators.

### 1.7 Countable monotone covers and finite covers

**Declaration:** `IsNondecreasingCover`  
**Source:** `P02/NonuniformCharacterization.lean:30-33`

For classes `H_n`, this means both

\[
H_m\subseteq H_n\quad(m\le n)
\]

and exact equality

\[
H=\bigcup_{n\in\mathbb N}H_n.
\]

**Declaration:** `IsFiniteCover`  
**Source:** `P02/GenerationInLimitCharacterization.lean:24-27`

For `classes : Fin n → LanguageClass α`, this means

\[
H=\bigcup_{i\in\mathrm{Fin}(n)}H_i.
\]

No monotonicity is imposed. The index size `n` may be zero, in which case the union is empty.

### 1.8 Upward cones and explicit ordinary example classes

**Declaration:** `upwardCone`  
**Source:** `P02/FiniteConeCover.lean:22`

\[
\operatorname{Up}(S)=\{L\subseteq\alpha:S\subseteq L\}.
\]

The code also proves that this equals

\[
\{S\cup A:A\subseteq\alpha\}.
\]

The principal explicit ordinary classes are:

1. **Subset-cone-plus-singleton class** (`subsetConeClass`, `limitNonuniformSeparationClass`, `P02/LimitVsNonuniformSeparation.lean:26-33`):
   \[
   \mathcal C(P,N)=\{N\cup A:A\subseteq P\}
   \quad\text{and}\quad
   \mathcal H(P,N)=\mathcal C(P,N)\cup\{P\}.
   \]

2. **Countable-union construction** (`P02/CountableUnionSeparation.lean:29-49`): the universe is
   \[
   \mathbb N\sqcup(\mathbb N\times\mathbb N).
   \]
   Write `a_n = inl n` and `T_n={inr(n,k):k∈ℕ}`. The core indexed by zero is the full anchor row `A={a_n:n∈ℕ}`, while the core indexed by `n+1` is `{a_n}∪T_n`. The component class is the upward cone over that core, and the hard class is the union of all components.

3. **Block class** (`P02/EarlierSectionThreeExamples.lean:112-127`): the universe is
   \[
   (\mathbb N\times\mathbb N)\sqcup(\mathrm{Bool}\times\mathbb N).
   \]
   For `d`, the finite block is
   \[
   B_d=\{\operatorname{inl}(d,j):j<d\},
   \]
   and for `b∈Bool`, the infinite tail is
   \[
   T_b=\{\operatorname{inr}(b,n):n\in\mathbb N\}.
   \]
   The language `L_{b,d}` is `B_d∪T_b`, and the class is the range of `(b,d)↦L_{b,d}`.

### 1.9 VC and Littlestone combinatorics, and the two direct proxies

**Declarations:** `VCShatters`, `HasFiniteVCDimension`, `HasInfiniteVCDimension`, `PACLearnableViaVC`  
**Source:** `P02/Prediction.lean:34-53`

A sequence `xs : Fin d → α` is VC-shattered by `H` iff every Boolean labeling of its indices is realized by membership in some language in `H`:

\[
\forall b:\mathrm{Fin}(d)\to\mathrm{Bool},
\exists L\in H,
\forall i,
\bigl(xs_i\in L\iff b_i=\mathrm{true}\bigr).
\]

Finite VC dimension is encoded only as existence of an upper bound:

\[
\exists d,
\forall xs:\mathrm{Fin}(d+1)\to\alpha,
\ xs\text{ is not shattered}.
\]

Infinite VC dimension is

\[
\forall d,
\exists xs:\mathrm{Fin}(d)\to\alpha,
\ xs\text{ is shattered}.
\]

The definition

```lean
PACLearnableViaVC H := HasFiniteVCDimension H
```

is a direct definitional alias. It does not mention probability, distributions, samples, hypotheses returned by an algorithm, risk, confidence, accuracy, or sample complexity.

**Declarations:** `LittlestoneTree`, `labelClass`, `LittlestoneShattered`, `HasShatteredLittlestoneTree`, `HasFiniteLittlestoneDimension`, `HasInfiniteLittlestoneDimension`, `OnlineLearnableViaLittlestone`  
**Source:** `P02/Prediction.lean:110-151`

A depth-zero tree is a leaf. A depth-`d+1` tree is a node labeled by `x∈α` with left and right subtrees of depth `d`. For `b∈Bool`,

\[
H[x=b]=\{L\in H:(x\in L\iff b=\mathrm{true})\}.
\]

A leaf is shattered iff its current class is nonempty. A node is shattered iff its left subtree is shattered by `H[x=false]` and its right subtree by `H[x=true]`.

Finite Littlestone dimension is encoded as

\[
\exists d,\text{ no shattered tree of depth }d+1,
\]

and infinite Littlestone dimension as existence of a shattered tree at every finite depth.

The definition

```lean
OnlineLearnableViaLittlestone H := HasFiniteLittlestoneDimension H
```

is likewise a direct alias, with no online prediction protocol, loss sequence, mistake bound, regret, or learner.

### 1.10 Eventually Unbounded Closure and its stronger streamwise variant

**Declaration:** `EventuallyUnboundedClosure`  
**Source:** `P02/EventuallyUnboundedClosure.lean:22-26`

A class `H` has EUC iff

\[
\forall L\in H,
\forall x:\mathbb N\to\alpha,
\operatorname{range}(x)=L
\Rightarrow
\exists t,
\operatorname{core}_H(S_t(x))\text{ is infinite}.
\]

Only exact presentations of actual members of `H` are quantified.

**Declaration:** `StreamwiseEventuallyUnboundedClosure`  
**Source:** `P02/EventuallyUnboundedClosureDiagnostics.lean:16-21`

The stronger predicate quantifies over every stream, whether or not it presents a member of `H`:

\[
\forall x:\mathbb N\to\alpha,
\exists t,
\quad V_H(S_t(x))=\varnothing
\quad\text{or}\quad
\operatorname{core}_H(S_t(x))\text{ is infinite}.
\]

These two predicates are not definitionally identical, and the target development proves that they are not universally equivalent.

### 1.11 Prompted multiclass generation

Let `α` be the example type and `ι` the prompt/label type.

**Declarations:** `MulticlassHypothesis`, `MulticlassHypothesisClass`, `promptSupport`, `PUUS`  
**Source:** `P02/PromptedDefinitions.lean:19-31`

A hypothesis is a total function `h : α → ι`; a class is a set of such functions. For `y∈ι`,

\[
\operatorname{supp}(h,y)=\{x\in\alpha:h(x)=y\}.
\]

`PUUS H` means

\[
\forall h\in H,\forall y\in\iota,
\operatorname{supp}(h,y)\text{ is infinite}.
\]

**Declarations:** `PromptedObservation`, `PromptedGenerator`, `promptedHistory`  
**Source:** `P02/PromptedDefinitions.lean:34-48`

A revealed observation is a triple

\[
(x,\ell,y)\in\alpha\times\iota\times\iota,
\]

where in an actual history `ℓ=h(x)` and `y` is the prompt. A prompted generator maps an ordered history of such triples to an example. At history length `t`, the actual history is

\[
i\longmapsto (x_i,h(x_i),y_i),\qquad i<t.
\]

Thus the generator is explicitly given the true labels of all revealed examples as well as the prompt stream.

**Declaration:** `promptedSample`  
**Source:** `P02/PromptedDefinitions.lean:52-56`

For a fixed label `y`,

\[
S^y_t(h,x)=\{x_i:i<t\text{ and }h(x_i)=y\}
\]

as a finite set of distinct examples. It is filtered by the true label, not by the prompts that occurred.

**Declaration:** `PromptedCorrectAt`  
**Source:** `P02/PromptedDefinitions.lean:79-86`

At `s=0`, prompted correctness is vacuous. For `s>0`, it requires

\[
G\bigl((x_i,h(x_i),y_i)_{i<s}\bigr)
\in
\operatorname{supp}(h,y_{s-1})
\setminus S_s(x).
\]

Freshness is against **all** distinct examples observed before length `s`, not merely the observations having the current label.

**Declarations:** `IsPromptedUniformGeneratorAt`, `PromptedUniformlyGeneratable`  
**Source:** `P02/PromptedDefinitions.lean:94-109`

A fixed `G` works at threshold `d` iff, for every `h∈H`, every example stream `x`, every prompt stream `y`, every distinguished prompt `y*`, and every time `t` with

\[
|S^{y^*}_t(h,x)|=d,
\]

then for every `s≥t` with `s>0`, whenever the current prompt `y_{s-1}` equals `y*`, the prompted output is correct. The class is prompted-uniformly generatable iff one `G` and one `d` work for all these choices.

There is no condition that the example stream reach `d` examples of every label. Unreached thresholds produce vacuous branches.

**Declarations:** `IsPromptedNonuniformGenerator`, `PromptedNonuniformlyGeneratable`  
**Source:** `P02/PromptedDefinitions.lean:113-127`

One generator must work for all `h∈H`, but after choosing `h` it may choose a threshold `d_h`. That threshold is chosen before both streams and before `y*`; it therefore cannot depend on the prompt.

**Declarations:** `PromptSupportPresented`, `IsPromptedLimitGenerator`, `PromptedGeneratableInLimit`  
**Source:** `P02/PromptedDefinitions.lean:131-151`

The support-presentation condition is inclusion, not equality:

\[
\operatorname{supp}(h,y^*)\subseteq\operatorname{range}(x).
\]

Additional examples of other labels may appear in the example stream.

A fixed prompted generator is a limit generator iff, whenever the full support of `y*` is contained in the example stream, there exists a time `t` such that at every later positive round whose current prompt is `y*`, the output is correct. If no later round uses `y*`, the conditional obligation is vacuous.

**Declarations:** `promptedVersionSpace`, `promptedCommonCore`, `promptedClosure`  
**Source:** `P02/PromptedDefinitions.lean:154-171`

For a finite `S` and prompt `y`,

\[
V^y_H(S)=\{h\in H:\forall x\in S,\ h(x)=y\},
\]

and

\[
\operatorname{pcore}^y_H(S)
=\{x:\forall h\in V^y_H(S),\ h(x)=y\}.
\]

Again, the common core is the whole universe when the prompted version space is empty, while `promptedClosure` returns `none` in that case and `some` of the core otherwise.

### 1.12 Prompted closure dimension

**Declarations:** `IsPromptedClosureWitness`, `PromptedClosureDimensionAtMost`, `HasPromptedClosureDimension`, `HasFinitePromptedClosureDimension`, `HasInfinitePromptedClosureDimension`  
**Source:** `P02/PromptedClosure.lean:15-44`

A pair `(S,y)` is a prompted closure witness iff

\[
V^y_H(S)\neq\varnothing
\quad\text{and}\quad
\operatorname{pcore}^y_H(S)\text{ is finite}.
\]

`PromptedClosureDimensionAtMost H d` means

\[
\forall y\in\iota,
\forall S\subseteq_{\mathrm{fin}}\alpha,
|S|>d\ \wedge\ V^y_H(S)\neq\varnothing
\Rightarrow
\operatorname{pcore}^y_H(S)\text{ infinite}.
\]

`HasPromptedClosureDimension H d` adds either `d=0` or an exact-size witness `|S|=d` for some prompt `y`. Finite prompted closure dimension means existence of such a `d`; infinite prompted closure dimension means prompted closure witnesses exist with arbitrarily large cardinality, with the witnessing prompt allowed to depend on the requested size.

## 2. Reconstructed substantive theorem statements

This section records the substantive public claims in the target subtree. Supporting identities, membership lemmas, monotonicity facts, and named-generator specifications are included when they materially determine the statement-level content; a complete public-declaration ledger appears in Appendix B.

### 2.1 Ordinary quantifier hierarchy

**Source:** `P02/Hierarchy.lean`

#### `uniform_implies_nonuniform` (`:14`)

For every example type `α` and language class `H`, uniform generatability implies nonuniform generatability. No infinite-support, nonemptiness, or countability hypothesis occurs in the statement. After unfolding the two predicates, the premise has a class-wide threshold while the conclusion permits target-dependent thresholds.

#### `nonuniform_implies_limit` (`:22`)

For every `H` satisfying `UUS H`, nonuniform generatability implies generation in the limit. Fully expanded: if one generator has, for each target `L∈H`, a target-dependent threshold that works over every stream contained in `L`, then on every exact presentation of `L` there is a time after which every output is a valid unobserved point of `L`. The statement uses UUS to guarantee that an exact presentation reaches the finite threshold in distinct sample size.

#### `uniform_implies_limit` (`:36`)

For every `H` satisfying UUS, uniform generatability implies generation in the limit. This is a separately declared implication with the same assumptions as the preceding implication chain would require.

### 2.2 Closure dimension and uniform generation

**Source:** `P02/Closure.lean`

#### Downward closure of witnesses

- `closure_witness_mono` (`:55`): if `S⊆T` and `T` has nonempty version space and finite common core, then `S` also has nonempty version space and finite common core.
- `exists_closure_witness_card_eq` (`:69`): if closure witnesses occur with arbitrarily large sizes, then for every `d` there is a witness of **exactly** size `d`.

These are structural consequences of the definitions and make the unbounded-witness formulation interchangeable with exact cardinalities for later statements.

#### `closure_witness_defeats_uniform_threshold` (`:82`)

Assume `α` is countable, `H` satisfies UUS, `S` is a closure witness, and `|S|=d`. Then for every proposed generator `G`, `G` does not satisfy `IsUniformGeneratorAt G H d`.

The conclusion negates the fully universal threshold property. It is stronger than merely saying that some generator fails: the generator is an arbitrary input to the theorem. The hypotheses do not mention a particular target language, but the witness contains a nonempty positive version space from which the negated universal property is forced.

#### `closure_dimension_necessity` (`:178`)

On a countable example type, if `H` satisfies UUS and has infinite closure dimension, then `H` is not uniformly generatable.

Equivalently, under these hypotheses, uniform generatability rules out arbitrarily large finite-core positive samples.

#### `finite_closure_dimension_iff_not_infinite` (`:190`)

For every class `H`, with no typeclass or UUS assumptions,

\[
\mathrm{HasFiniteClosureDimension}(H)
\iff
\neg\mathrm{HasInfiniteClosureDimension}(H).
\]

This theorem validates that the two relational encodings used in the code are logical complements. It does not introduce a separate extended-natural-valued dimension object.

#### `core_diff_sample_infinite` (`:240`)

If `ClosureDimensionAtMost H d`, `|S|>d`, and `V_H(S)` is nonempty, then

\[
\operatorname{core}_H(S)\setminus S
\]

is infinite. This strengthens the defining conclusion “the core is infinite” by removing the finite sample.

#### Named closure generator and specification

`closureGenerator` (`:251`) is a noncomputable generator parameterized by `H`, `d`, and a proof of `ClosureDimensionAtMost H d`. On a finite history with distinct-value set `S`:

- if `|S|>d` and `V_H(S)` is nonempty, it chooses a point in `core_H(S)\S`;
- otherwise it returns an arbitrary point supplied by `[Nonempty α]`.

`closureGenerator_spec` (`:264`) states exactly the first branch: under the two branch conditions, its output belongs to `core_H(S)\S`.

#### `closureGenerator_isUniformGeneratorAt` (`:281`)

Assume `[Nonempty α]`, `[Countable α]`, `UUS H`, and `HasClosureDimension H d`. Then the named closure generator works uniformly at threshold `d+1`.

The UUS hypothesis is syntactically present in the theorem type. The conclusion is about every `StreamIn` stream, not only exact presentations.

#### `closure_dimension_sufficiency` (`:308`)

Under the same nonempty/countable/UUS assumptions, if `H` has closure dimension `d`, then there exists a generator working uniformly at threshold `d+1`.

#### `finite_closure_dimension_implies_uniform` (`:317`)

Under `[Nonempty α]`, `[Countable α]`, and UUS, finite closure dimension implies uniform generatability. The numerical dimension is existentially unpacked, and the threshold supplied is one larger than the chosen finite dimension.

#### `uniform_generatability_iff_finite_closure_dimension` (`:329`)

For a nonempty countable example type and a class `H` satisfying UUS,

\[
\mathrm{UniformlyGeneratable}(H)
\iff
\mathrm{HasFiniteClosureDimension}(H).
\]

Fully unfolded, the left side asserts existence of one history-based deterministic generator and one finite threshold satisfying the universal `StreamIn` condition. The right side asserts a finite bound `d` beyond which every consistent finite positive sample has infinite common core, together with the exact-witness/zero convention described above.

No computability, oracle, or algorithmic efficiency assumption is part of either side.

### 2.3 Exact uniform sample-complexity API and quantitative bounds

**Source:** `P02/UniformSampleComplexity.lean`

The public statements are as follows.

#### Threshold monotonicity

`uniform_threshold_mono` (`:29`) states that if `d≤n` and a fixed generator works at threshold `d`, then it also works at threshold `n`. The dependency layer separately states that distinct sample cardinality rises by at most one per round and that every lower cardinality is attained before a reached higher cardinality, which makes this exact-size formulation coherent.

#### Fixed-generator value

- `uniformGenerationSampleComplexity_eq_top_iff` (`:52`): `d_G(H)=⊤` iff no natural threshold works for `G`.
- `uniformGenerationSampleComplexity_lt_top_iff` (`:62`): `d_G(H)<⊤` iff some natural threshold works.
- `uniformGenerationSampleComplexity_le_coe_iff` (`:72`): for natural `d`,
  \[
  d_G(H)\le d\iff G\text{ works at threshold }d.
  \]
  This equivalence relies on threshold monotonicity; it is stronger than merely saying that the minimum is at most a known valid threshold.
- `uniformGenerationSampleComplexity_eq_coe_iff` (`:94`): `d_G(H)=d` iff `d` is valid and every `e<d` is invalid.
- `uniformlyGeneratable_iff_exists_sampleComplexity_lt_top` (`:122`): `H` is uniformly generatable iff some generator has finite fixed-generator sample complexity.

#### Class-optimal value

- `optimalUniformGenerationSampleComplexity_eq_top_iff` (`:150`): `d^*(H)=⊤` iff `H` is not uniformly generatable.
- `optimalUniformGenerationSampleComplexity_le_coe_iff` (`:174`): for natural `d`,
  \[
  d^*(H)\le d
  \iff
  \exists G,\ G\text{ works at threshold }d.
  \]

#### Closure-dimension lower and upper bounds

Assume the hypotheses shown in each declaration.

- `closure_dimension_le_uniform_threshold` (`:203`): on a countable example type, under UUS and `HasClosureDimension H d`, every valid threshold `e` for every generator satisfies `d≤e`.
- `closure_dimension_le_uniformGenerationSampleComplexity` (`:219`): under the same countability/UUS/dimension assumptions, for every generator `G`,
  \[
  d\le d_G(H)
  \]
  in `WithTop ℕ`; this includes generators with value `⊤`.
- `closureGenerator_uniformGenerationSampleComplexity_le` (`:235`): under nonemptiness, countability, UUS, and dimension `d`, the named closure generator has value at most `d+1`.
- `closure_dimension_le_optimalUniformGenerationSampleComplexity` (`:246`): under countability, UUS, and dimension `d`,
  \[
  d\le d^*(H).
  \]
- `optimalUniformGenerationSampleComplexity_le_closureDimension_succ` (`:264`): under nonemptiness, countability, UUS, and dimension `d`,
  \[
  d^*(H)\le d+1.
  \]
- `optimal_uniform_generation_sample_complexity_bounds` (`:281`) packages the two inequalities:
  \[
  d\le d^*(H)\le d+1.
  \]

The code does not state `d^*(H)=d`, `d^*(H)=d+1`, or a case split deciding which endpoint occurs.

### 2.4 Nonuniform characterization by monotone covers

**Source:** `P02/NonuniformCharacterization.lean`

#### `nonuniform_characterization_necessity` (`:36`)

Assume `[Countable α]`, UUS, and that `H` is nonuniformly generatable. Then there exists a sequence of subclasses `(H_n)` such that

\[
H_0\subseteq H_1\subseteq\cdots,
\qquad
H=\bigcup_n H_n,
\]

and every `H_n` is uniformly generatable.

The theorem statement retains UUS, even though the cover conclusion itself is phrased only in terms of generation predicates.

#### `nonuniform_characterization_sufficiency` (`:103`)

Assume `[Nonempty α]`, `[Countable α]`, UUS, an exact nondecreasing cover `H=⋃_n H_n`, and uniform generatability of every `H_n`. Then `H` is nonuniformly generatable.

One generator must serve the entire union. The conclusion is not a family of per-component generators; it is the existential single-generator property defined in Section 1.4.

#### `nonuniform_generatability_iff_nondecreasing_finite_closure_cover` (`:167`)

For a nonempty countable example type and UUS class `H`,

\[
\mathrm{NonuniformlyGeneratable}(H)
\iff
\exists(H_n)_{n\in\mathbb N},
\begin{cases}
H_m\subseteq H_n& m\le n,\\
H=\bigcup_nH_n,\\
\mathrm{HasFiniteClosureDimension}(H_n)&\forall n.
\end{cases}
\]

This is the principal nonuniform characterization. The subclasses are allowed to overlap, and the same language may occur in many components.

#### `finite_language_class_has_finite_closure_dimension` (`:191`)

Every finite language class has finite closure dimension. This statement has no UUS, countability, or nonemptiness assumptions. It concerns only the finite-core combinatorics.

#### `countable_classes_are_nonuniformly_generatable` (`:220`)

If `α` is nonempty and countable, `H` is countable as a set of languages, and every `L∈H` is infinite, then `H` is nonuniformly generatable.

The countability assumption is on the class `H` in addition to the typeclass `[Countable α]`. No enumeration is supplied as explicit input to the resulting generator.

### 2.5 Finite-cover sufficiency for generation in the limit

**Source:** `P02/GenerationInLimitCharacterization.lean`

#### `finite_closure_dimension_cover_implies_generatable_in_limit` (`:524`)

Assume `[Nonempty α]`, `[Countable α]`, UUS, and that for some natural `n` there are subclasses `H_i`, indexed by `Fin n`, satisfying

\[
H=\bigcup_{i\in\mathrm{Fin}(n)}H_i
\]

and every `H_i` has finite closure dimension. Then `H` is generatable in the limit.

This is only a sufficient condition in the code. No converse is stated. The cover is finite but need not be nested. The conclusion allows the stabilization time to depend on the target and exact presentation, as in the definition of limit generation.

### 2.6 Upward-cone consequences and ordinary separation examples

#### Upward cones

**Source:** `P02/FiniteConeCover.lean`

- `mem_upwardCone_iff` (`:25`) restates the definition: `L∈upwardCone S` iff `S⊆L`.
- `upwardCone_eq_union_class` (`:31`) proves exact equality
  \[
  \operatorname{Up}(S)=\{L:\exists A,\ L=S\cup A\}.
  \]
- `upwardCone_has_closure_dimension_zero` (`:41`): if `S` is infinite, then `Up(S)` has closure dimension zero.
- `upwardCone_has_finite_closure_dimension` (`:50`) packages the preceding statement as finite closure dimension.
- `finite_union_of_infinite_upwardCones_generatable_in_limit` (`:67`): on a nonempty countable example type, for any finite family of infinite bases `S_i`,
  \[
  \bigcup_i\operatorname{Up}(S_i)
  \]
  is generatable in the limit.
- `finite_union_of_paper_cone_classes_generatable_in_limit` (`:82`) is the specialization to `α=ℕ` with each component displayed as
  \[
  \{L:\exists A,\ L=S_i\cup A\}.
  \]
  It is a restatement through the exact equality above, not a different class.

#### A limit-versus-nonuniform separation

**Source:** `P02/LimitVsNonuniformSeparation.lean`

Let `P,N⊆α` be infinite and disjoint, and define

\[
\mathcal H(P,N)=\{N\cup A:A\subseteq P\}\cup\{P\}.
\]

The public statements establish:

- `separation_class_uus` (`:109`): if `P` and `N` are infinite, every member of `H(P,N)` is infinite.
- `separation_class_generatable_in_limit` (`:120`): if `P,N` are infinite and disjoint, `H(P,N)` is generatable in the limit.
- `separation_class_not_nonuniformly_generatable` (`:332`): under the same hypotheses, `H(P,N)` is not nonuniformly generatable.

The named `partitionLimitGenerator` (`:64`) has the following definition on a finite history with distinct set `S`: if `S⊆P`, choose a fresh point of `P`; otherwise choose a fresh point of `N`. It is noncomputable and parameterized by proofs that `P` and `N` are infinite.

Two component closure statements are also public:

- `subsetConeClass_has_closure_dimension_zero` (`:373`): if `N` is infinite, the class `\{N∪A:A⊆P\}` has closure dimension zero.
- `singleton_infinite_language_has_closure_dimension_zero` (`:385`): if `P` is infinite, the singleton class `{P}` has closure dimension zero.
- `two_zero_closure_classes_union_not_nonuniform` (`:397`): for infinite disjoint `P,N`, both component classes have closure dimension zero, yet their union is not nonuniformly generatable.

The concrete sets

\[
P=\{z\in\mathbb Z:0<z\},
\qquad
N=\{z\in\mathbb Z:z\le0\}
\]

are defined at lines `411` and `414`, and are proved infinite and disjoint by `paperPositiveIntegers_infinite`, `paperNonpositiveIntegers_infinite`, and `paper_integer_partition_disjoint`.

The resulting existential packages are:

- `exists_generatable_in_limit_not_nonuniformly_generatable` (`:452`): there exists a language class over `ℤ` that satisfies UUS, is generatable in the limit, and is not nonuniformly generatable.
- `exists_two_zero_closure_classes_union_not_nonuniform` (`:469`): there exist two language classes over `ℤ`, each of closure dimension zero, whose union is not nonuniformly generatable.

#### A countable union of zero-closure classes that is not limit-generatable

**Source:** `P02/CountableUnionSeparation.lean`

For the explicit anchor/private-tail construction in Section 1.8:

- `countableUnionCore_infinite` (`:81`): every core `C_n` is infinite.
- `countableUnionClasses_uus` (`:101`): every upward-cone component class satisfies UUS.
- `countableUnionClasses_closure_dimension_zero` (`:106`): every component has closure dimension zero.
- `countableUnionHardClass_not_generatable_in_limit` (`:578`): the countable union of these components is not generatable in the limit.
- `exists_countable_sequence_zero_closure_union_not_limit` (`:607`) packages the result as existence of a sequence `(H_n)` on the explicit countable universe such that every `H_n` satisfies UUS and has closure dimension zero, while `⋃_n H_n` is not generatable in the limit.

This statement rules out closure of limit generatability under arbitrary countable unions even for zero-dimensional components. It does not contradict the finite-cover theorem, whose finiteness assumption is essential in the formal statement.

#### An uncountable uniformly generatable class

**Source:** `P02/EarlierSectionThreeExamples.lean`

- `upwardCone_not_countable` (`:63`): on a countable example type, if `P` is infinite and disjoint from `N`, then `Up(N)` is not countable as a set of languages.
- `exists_uncountable_uniformly_generatable_class` (`:93`): there exists a language class over `ℤ` that is uncountable, satisfies UUS, and is uniformly generatable. The same module separately defines the upward cone over the nonpositive integers and states the properties needed to exhibit such a class.

Thus countability of the language class is not necessary for uniform generatability in the formal model.

#### A countable nonuniform-but-not-uniform class

**Source:** `P02/EarlierSectionThreeExamples.lean`

For the block class `\{B_d\cup T_b:b∈Bool,d∈ℕ\}`:

- `blockFinset_card` (`:128`): `|B_d|=d`.
- `blockTail_infinite` (`:136`): each tail `T_b` is infinite.
- `blockSeparationClass_countable` (`:141`): the class is countable.
- `blockSeparationClass_uus` (`:144`): every language in the class is infinite.
- `commonCore_blockSeparationClass_eq` (`:157`): the common core of the class at the sample `B_d` is exactly `B_d`.
- `blockSeparationClass_infinite_closure_dimension` (`:172`): the class has infinite closure dimension.
- `exists_countable_nonuniform_not_uniform_class` (`:183`): there exists a countable UUS class on `BlockUniverse` that is nonuniformly generatable but not uniformly generatable.

At statement level, the packaged existential includes all four properties explicitly; the preceding public declarations separately state countability, UUS, infinite closure dimension, and the final separation.

### 2.7 The combinatorial prediction landscape

**Source:** `P02/Prediction.lean`

The following statements must be read with the definitional expansions

\[
\mathrm{PACLearnableViaVC}(H)
\equiv
\mathrm{HasFiniteVCDimension}(H)
\]

and

\[
\mathrm{OnlineLearnableViaLittlestone}(H)
\equiv
\mathrm{HasFiniteLittlestoneDimension}(H).
\]

They are not bridge theorems to external learning definitions.

#### General structural statements

- `vcShatters_mono` (`:56`): shattering is monotone under enlargement of the language class.
- `pairShattered_of_vcShatters` (`:70`): two distinct indexed points inside a shattered sequence realize all four pair labelings.
- `vcShatters_injective` (`:83`): every VC-shattered sequence is injective.
- `not_pacViaVC_of_infinite` (`:98`): infinite VC dimension implies the negation of the finite-VC alias.
- `littlestoneShattered_mono` (`:154`): Littlestone shattering is monotone under class enlargement.
- `littlestoneShattered_nonempty` (`:174`): a class shattering any tree is nonempty.
- `no_depth_one_of_subsingleton` (`:185`): a subsingleton class does not shatter a depth-one tree.
- `not_onlineViaLittlestone_of_infinite` (`:202`): infinite Littlestone dimension implies the negation of the finite-Littlestone alias.
- `uniformlyGeneratable_of_common_infinite_base` (`:211`): on a nonempty countable example type, if every language in `H` contains one fixed infinite set `B`, then `H` satisfies UUS and is uniformly generatable.

#### Region (i): uniform generation with infinite VC dimension

The class `finiteAugmentationClass` consists of

\[
N\cup A,
\quad
A\subseteq P,
\quad
A\text{ finite},
\]

where `P` is the positive-integer set and `N` the nonpositive-integer set in `ℤ`.

The code proves:

- `finiteAugmentationClass_countable` (`:234`): the class is countable.
- `finiteAugmentationClass_uus_and_uniform` (`:246`): it satisfies UUS and is uniformly generatable.
- `finiteAugmentationClass_infiniteVC` (`:270`): it has infinite VC dimension.
- `theorem_4_1_i_combinatorial_core` (`:306`): there exists a countable class over `ℤ` that is uniformly generatable and not `PACLearnableViaVC`, i.e. does not have finite VC dimension.

The existential conclusion itself does not include UUS, although the explicit `finiteAugmentationClass` has a separate UUS theorem.

#### Region (ii): finite Littlestone dimension but not uniform generation

The witness is the block class from Section 2.6.

- `blockSeparationClass_onlineViaLittlestone` (`:366`) states that the class has finite Littlestone dimension through the direct alias `OnlineLearnableViaLittlestone`. The theorem signature does not expose a numerical dimension value.
- `blockSeparationClass_not_uniform` (`:450`) states failure of uniform generatability.
- `theorem_4_1_ii_combinatorial_core` (`:457`) packages existence of a countable class on `BlockUniverse` with finite Littlestone dimension and no uniform generator.

#### Region (iii): finite Littlestone dimension and uniform generation

For `a∈ℕ`,

\[
L_a=N\cup\{a+1\}\subseteq\mathbb Z,
\]

and `singletonSpikeClass` is the range of `a↦L_a`.

- `singletonSpikeClass_countable` (`:475`): the class is countable.
- `singletonSpikeClass_uus_and_uniform` (`:479`): it satisfies UUS and is uniformly generatable.
- `singletonSpikeClass_onlineViaLittlestone` (`:507`) states that the class has finite Littlestone dimension. No numerical value is exposed by the theorem signature.
- `theorem_4_1_iii_combinatorial_core` (`:530`) packages a countable class over `ℤ` with both the finite-Littlestone proxy and uniform generatability.

#### Region (v): finite VC dimension, uniform generation, infinite Littlestone dimension

The threshold class on `ℕ` is

\[
\mathcal T=\{\{x:a\le x\}:a\in\mathbb N\}.
\]

The code proves:

- `thresholdClass_countable` (`:550`): `T` is countable.
- `thresholdLanguage_infinite` (`:553`) and `thresholdClass_uus` (`:561`): every threshold tail is infinite.
- `thresholdClass_uniform` (`:566`): `T` is uniformly generatable.
- `thresholdClass_pacViaVC` (`:604`): `T` has finite VC dimension through the direct alias `PACLearnableViaVC`. The theorem signature does not state an exact or upper-bound numerical value.
- `thresholdClass_infiniteLittlestone` (`:677`): `T` has shattered Littlestone trees of every finite depth.
- `thresholdClass_not_onlineViaLittlestone` (`:689`): `T` does not have finite Littlestone dimension.
- `theorem_4_1_v_combinatorial_core` (`:696`): there exists a countable class over `ℕ` with finite VC dimension, uniform generatability, and infinite Littlestone dimension.

#### Region (iv): finite VC dimension, infinite Littlestone dimension, and no uniform generation

`ThresholdBlockUniverse` is the disjoint sum `ℕ ⊕ BlockUniverse`. `thresholdBlockClass` is the union of the threshold class embedded into the left summand and the block class embedded into the right summand.

The code proves:

- `thresholdBlockClass_countable` (`:738`): the union is countable.
- `thresholdBlockClass_uus` (`:743`): every member language is infinite.
- `thresholdBlockClass_infiniteClosure` (`:831`): it has infinite closure dimension.
- `thresholdBlockClass_not_uniform` (`:857`): it is not uniformly generatable.
- `thresholdBlockClass_pacViaVC` (`:1003`): it has finite VC dimension through the direct alias `PACLearnableViaVC`. No numerical dimension value is part of the theorem statement.
- `thresholdBlockClass_infiniteLittlestone` (`:1109`) and `thresholdBlockClass_not_online` (`:1120`): it has infinite Littlestone dimension and fails the finite-Littlestone alias.
- `theorem_4_1_iv_combinatorial_core` (`:1127`): there exists a countable class on the disjoint-sum universe having finite VC dimension, infinite Littlestone dimension, and no uniform generator.

#### Region (vi): infinite VC dimension and no uniform generation

The cofinite class on `ℕ` is

\[
\mathcal C_{\mathrm{cof}}
=\{A^c:A\subseteq\mathbb N\text{ finite}\}.
\]

The code proves:

- `cofiniteClass_countable` (`:1143`): the class is countable.
- `cofiniteClass_uus` (`:1153`): every cofinite language is infinite.
- `cofiniteClass_infiniteVC` (`:1159`): it has infinite VC dimension.
- `commonCore_cofiniteClass_eq` (`:1191`): for every finite sample `S`, its common core is exactly `S`.
- `cofiniteClass_infiniteClosure` (`:1208`): it has infinite closure dimension.
- `cofiniteClass_not_uniform` (`:1219`): it is not uniformly generatable.
- `cofiniteClass_not_pacViaVC` (`:1224`): it fails the finite-VC alias.
- `theorem_4_1_vi_combinatorial_core` (`:1230`): there exists a countable class over `ℕ` with infinite VC dimension and no uniform generator.

#### Combined six-part package

`theorem_4_1_combinatorial_core` (`:1245`) is the conjunction of the six existential regions above, in the order (i), (ii), (iii), (iv), (v), (vi). The universes are allowed to differ among conjuncts. The theorem contains no quantification over a common universe and no assertion that the six witnesses are subclasses of one master class.

### 2.8 Eventually Unbounded Closure: consequences, counterexamples, and covers

#### Monotonicity and implications

**Source:** `P02/EventuallyUnboundedClosure.lean`

- `commonCore_mono_sample` (`:28`): if `S⊆T`, then `core_H(S)⊆core_H(T)`. More positive observations shrink the version space and can only enlarge its intersection.
- `commonCore_infinite_mono_sample` (`:36`): if the core at `S` is infinite and `S⊆T`, then the core at `T` is infinite.
- `finite_closure_dimension_implies_eventuallyUnboundedClosure` (`:44`): UUS plus finite closure dimension implies EUC. No countability or nonemptiness typeclass is in this theorem statement.
- `uniform_implies_eventuallyUnboundedClosure` (`:60`): on a nonempty countable example type, UUS plus uniform generatability implies EUC.

#### A nonuniform class without EUC

For any type `α`, `cofiniteLanguageClass α` is the class of sets `Set.univ \ A` with finite `A`.

- `cofiniteLanguageClass_countable` (`:75`): if `α` is countable, this class is countable.
- `cofiniteLanguageClass_uus` (`:84`): if `α` is infinite, every member is infinite.
- `commonCore_cofiniteLanguageClass_eq` (`:90`): the common core at every finite sample `S` is exactly `S`.
- `cofiniteLanguageClass_not_eventuallyUnboundedClosure` (`:111`): over `ℕ`, this class does not have EUC.
- `exists_nonuniformly_generatable_not_eventuallyUnboundedClosure` (`:127`): there exists a countable UUS class over `ℕ` that is nonuniformly generatable but does not have EUC.

Thus EUC is not necessary for nonuniform generation in the formal theory.

#### A monotone countable EUC cover

`eventuallyUnboundedCoverGenerator` (`:169`) is a noncomputable generator for a sequence `(H_n)`. On a length-`t` history with distinct sample `S`, it forms the finite set of indices `n≤t` for which both `V_{H_n}(S)` is nonempty and `core_{H_n}(S)` is infinite. If this set is nonempty, it chooses the largest eligible index and outputs a fresh point of that component core; otherwise it outputs an arbitrary point.

`nondecreasing_euc_cover_implies_generatable_in_limit` (`:205`) states:

- assume only `[Nonempty α]`;
- assume `H=⋃_n H_n` with `H_n` monotone nondecreasing;
- assume every `H_n` has EUC;
- then `H` is generatable in the limit.

No `[Countable α]` or UUS assumption occurs in this core theorem.

`theorem_C4_eventually_unbounded_closure` (`:275`) is a wrapper whose type additionally assumes `[Countable α]` and `UUS H`, and existentially quantifies the nondecreasing EUC cover before concluding limit generation.

#### EUC itself implies limit generation

**Source:** `P02/EventuallyUnboundedClosureDiagnostics.lean`

`eventuallyUnboundedClosure_implies_generatable_in_limit` (`:51`) states that on any nonempty example type, EUC of the whole class implies generation in the limit. No UUS or countability hypothesis is required in this theorem type.

The same module defines a private generator that chooses a fresh point from the current common core once the version space is nonempty and that core is infinite, and otherwise uses an arbitrary fallback. At public statement level, the theorem exposes only the existence conclusion.

#### The formal EUC-versus-streamwise diagnostic

On

\[
\mathrm{SpineTailUniverse}=\mathbb N\sqcup(\mathbb N\times\mathbb N),
\]

define

\[
L_n=\{\operatorname{inl}(i):i<n\}
\cup
\{\operatorname{inr}(n,k):k\in\mathbb N\},
\]

and let `spineTailClass={L_n:n∈ℕ}`. Also define the arbitrary stream `spineStream(n)=inl(n)`.

The public statements are:

- `spineTailLanguage_infinite` (`:100`): every `L_n` is infinite.
- `spineTailClass_uus` (`:113`): the class satisfies UUS.
- `spineTailClass_eventuallyUnboundedClosure` (`:127`): the class has EUC.
- `spine_versionSpace_nonempty` (`:174`): along `spineStream`, the version space is nonempty at every time.
- `spine_commonCore_subset_sample` (`:180`) and `spine_commonCore_finite` (`:206`): along that stream, the common core is contained in the finite current sample and hence is finite at every time.
- `spineTailClass_not_streamwise_euc` (`:212`): the class fails `StreamwiseEventuallyUnboundedClosure`.
- `eventuallyUnboundedClosure_not_equivalent_to_streamwise` (`:221`): one concrete class satisfies EUC and fails the streamwise predicate.
- `printed_EUC_equivalence_is_false` (`:229`): it is false that every class on `SpineTailUniverse` satisfies
  \[
  \mathrm{EUC}(H)\iff\mathrm{StreamwiseEUC}(H).
  \]

The last proposition is a universal non-equivalence statement internal to the Lean development. This Stage 1 report does not attribute it to or compare it with any external prose source.

#### Finite unions of EUC classes

**Source:** `P02/FiniteEUCUnion.lean`

`finiteEUCUnionGenerator` (`:254`) is a noncomputable generator for a finite list of classes. Its public body unfolds through private helper definitions as follows:

1. A component is active on the current finite history if some prefix of that history has an infinite common core for the component.
2. For an active component, the earliest such prefix is selected and its common core is frozen.
3. Each infinite frozen core receives a fixed repetition-free enumeration by `ℕ`, using countability of `α`.
4. The component progress is the least enumeration index whose point is absent from the current sample.
5. Among active components, one of maximal progress is selected.
6. The output is that component's first currently missing enumerated point; if no component is active, an arbitrary point is returned.

`finite_euc_cover_implies_generatable_in_limit` (`:445`) states that on a nonempty countable example type, if a finite family `(H_i)_{i∈Fin(n)}` exactly covers `H` and every `H_i` has EUC, then `H` is generatable in the limit. The core theorem does not assume UUS.

`theorem_C2_finite_eventually_unbounded_closure_cover` (`:637`) is the existential-cover wrapper with additional syntactic assumptions `[Countable α]` and `UUS H`.

### 2.9 Prompted closure characterization and prompted hierarchy

#### Prompted closure witnesses and their complementarity

**Source:** `P02/PromptedClosure.lean`

- `prompted_closure_witness_mono` (`:46`): for a fixed prompt `y`, if `S⊆T` and `(T,y)` is a prompted closure witness, then `(S,y)` is also a witness.
- `exists_prompted_closure_witness_card_eq` (`:57`): infinite prompted closure dimension yields, for every `d`, a prompt `y` and a witness sample of exact size `d`.
- `finite_prompted_closure_dimension_iff_not_infinite` (`:68`): for every prompted class,
  \[
  \mathrm{HasFinitePromptedClosureDimension}(H)
  \iff
  \neg\mathrm{HasInfinitePromptedClosureDimension}(H).
  \]

As in the ordinary setting, this validates the finite/unbounded relational encodings without constructing a separate dimension-valued object.

#### History-derived samples

`promptedSequenceSample` (`:120`) takes an arbitrary revealed history and a label `y`, keeps precisely the indices whose revealed middle coordinate equals `y`, and returns the distinct first-coordinate examples. `promptedObservedSample` (`:128`) returns all distinct first coordinates.

- `promptedSequenceSample_history` (`:132`): on an actual history generated by `h,xs,ys`, the history-derived label-`y` sample equals `promptedSample h xs y t`.
- `promptedObservedSample_history` (`:149`): on an actual history, the observed sample equals the ordinary distinct prefix sample of `xs`.

These identities are the bridge between the generator's raw triple history and the semantic samples used in the prompted predicates. They do not impose coherence on arbitrary histories passed to the generator; coherence is available only when the history is of the form `promptedHistory h xs ys t`.

#### Named prompted closure generator

`promptedClosureGenerator` (`:168`) is noncomputable and parameterized by `H`, `d`, and `PromptedClosureDimensionAtMost H d`. On a positive-length history:

1. it reads the prompt in the last triple;
2. it forms the distinct examples in the history whose revealed true label equals that prompt;
3. it forms the set of all observed examples;
4. if the label-specific sample has size greater than `d` and the prompted version space is nonempty, it chooses a point in the prompted common core outside **all** observed examples;
5. otherwise it returns an arbitrary point.

At history length zero it also returns an arbitrary point.

`promptedClosureGenerator_spec` (`:187`) states the branch guarantee exactly: under positive length, strict sample-size inequality, and nonempty prompted version space, the output lies in the prompted common core minus the full observed set.

#### Sufficiency, necessity, and characterization

- `prompted_closure_dimension_sufficiency` (`:214`): assume `[Nonempty α]`, `[Countable α]`, `[Countable ι]`, `PUUS H`, and `HasPromptedClosureDimension H d`. Then there exists a prompted generator that works uniformly at threshold `d+1`.
- `finite_prompted_closure_dimension_implies_uniform` (`:277`): under the same typeclass and PUUS assumptions, finite prompted closure dimension implies prompted uniform generatability.
- `exists_earlier_promptedSample_card_eq` (`:309`): if a prompted label-specific sample has cardinality at least `k` at time `t`, then some earlier time `r≤t` has cardinality exactly `k`.
- `prompted_uniform_threshold_mono` (`:338`): if a fixed prompted generator works at threshold `d` and `d≤n`, then it works at threshold `n`.
- `prompted_closure_dimension_necessity` (`:353`): under `[Countable α]`, `[Countable ι]`, and PUUS, infinite prompted closure dimension implies failure of prompted uniform generatability.
- `prompted_uniform_generatability_iff_finite_prompted_closure_dimension` (`:486`): under `[Nonempty α]`, `[Countable α]`, `[Countable ι]`, and PUUS,
  \[
  \mathrm{PromptedUniformlyGeneratable}(H)
  \iff
  \mathrm{HasFinitePromptedClosureDimension}(H).
  \]

There is no prompted analogue of `uniformGenerationSampleComplexity` in the bundle. The only quantitative threshold stated for the closure construction is `d+1`, together with threshold monotonicity.

### 2.10 Prompted nonuniform characterization and finite-prompt consequences

**Source:** `P02/PromptedNonuniform.lean`

#### Monotone prompted covers

`IsPromptedNondecreasingCover H classes` (`:19`) means that the hypothesis subclasses are monotone and their union equals `H` exactly.

#### Characterization directions

- `prompted_nonuniform_characterization_necessity` (`:25`): under `[Countable α]`, `[Countable ι]`, PUUS, and prompted nonuniform generatability, there exists a nondecreasing countable cover by prompted-uniformly generatable subclasses.
- `prompted_nonuniform_characterization_sufficiency` (`:99`): under `[Nonempty α]`, `[Countable α]`, `[Countable ι]`, PUUS, an exact nondecreasing cover by prompted-uniformly generatable subclasses implies prompted nonuniform generatability of the union.
- `prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover` (`:183`): under `[Nonempty α]`, `[Countable α]`, `[Countable ι]`, and PUUS,
  \[
  \mathrm{PromptedNonuniformlyGeneratable}(H)
  \iff
  \exists(H_n)_{n\in\mathbb N},
  \begin{cases}
  H_m\subseteq H_n& m\le n,\\
  H=\bigcup_nH_n,\\
  \mathrm{HasFinitePromptedClosureDimension}(H_n)&\forall n.
  \end{cases}
  \]

The generator in the conclusion is one prompted generator for the entire class. The target-dependent threshold is independent of both streams and of the prompt.

#### Prompted hierarchy

- `prompted_uniform_implies_nonuniform` (`:253`): prompted uniform generation implies prompted nonuniform generation, with no PUUS or typeclass assumptions.
- `prompted_nonuniform_implies_limit` (`:260`): under PUUS, prompted nonuniform generation implies prompted generation in the limit.
- `prompted_uniform_implies_limit` (`:275`): under PUUS, prompted uniform generation implies prompted generation in the limit.

The limit implication uses the condition that the entire support of the distinguished prompt appears somewhere in the example stream, which guarantees that every finite target threshold for that prompt is reached.

#### Finite and countable classes when the prompt type is finite

- `finite_prompt_class_has_finite_prompted_closure_dimension` (`:286`): if the prompt type `ι` has a `Finite` instance and `H` is a finite set of hypotheses, then `H` has finite prompted closure dimension. This combinatorial theorem has no PUUS, countability of `α`, or nonemptiness assumption.
- `finite_prompt_classes_are_uniformly_generatable` (`:322`): under `[Nonempty α]`, `[Countable α]`, `[Countable ι]`, `[Finite ι]`, PUUS, and finiteness of `H`, the class is prompted-uniformly generatable.
- `countable_prompt_classes_are_nonuniformly_generatable` (`:332`): under the same typeclass and PUUS assumptions, every countable hypothesis class is prompted-nonuniformly generatable.
- `countable_prompt_classes_are_generatable_in_limit` (`:376`): under the same assumptions, every countable hypothesis class is prompted-generatable in the limit.

The last two statements include finite classes because `H.Countable` does not mean countably infinite. The prompt-space finiteness assumption is essential to the theorem types.

### 2.11 Infinite-prompt separation

**Source:** `P02/PromptedInfinitePromptExample.lean`

The prompt type is

\[
\mathrm{PositivePrompt}=\{n\in\mathbb N:0<n\},
\]

with distinguished prompt `1`. The example universe is

\[
\mathrm{PositivePrompt}\times\mathrm{Option}(\mathrm{Bool})\times\mathbb N.
\]

Two hypotheses are defined. For a point `(q,mode,k)`:

- if `mode=none`, both hypotheses output `q` when `k<q` and output the distinguished prompt otherwise;
- if `mode=some false`, the left hypothesis outputs `q` and the right hypothesis outputs the distinguished prompt;
- if `mode=some true`, the right hypothesis outputs `q` and the left hypothesis outputs the distinguished prompt.

The class consists exactly of these two hypotheses.

For a positive prompt `p`, the finite block is

\[
A_p=\{(p,\mathrm{none},k):k<p\}.
\]

The public statements establish:

- `promptBlock_card` (`:55`): `|A_p|=p`.
- `promptSeparationLeft_block` (`:63`) and `promptSeparationRight_block` (`:72`): both hypotheses label every point of `A_p` by `p`.
- `promptSeparationClass_finite` (`:81`): the class is finite; in fact its defining set has at most the two displayed hypotheses.
- `promptSeparationClass_puus` (`:85`): for each of the two hypotheses and every positive prompt, the corresponding support is infinite.
- `promptBlock_versionSpace_nonempty` (`:120`): for each `p`, the prompted version space at `(A_p,p)` is nonempty.
- `promptedCommonCore_promptBlock_subset` (`:126`): if `p` is not the distinguished prompt, then the prompted common core at `(A_p,p)` is contained in `A_p`. Combined with the general inclusion `A_p⊆pcore`, this entails equality, although no separate public equality theorem is declared.
- `promptSeparationClass_infinite_prompted_closure_dimension` (`:161`): the two-hypothesis class has infinite prompted closure dimension.
- `exists_finite_prompt_class_not_uniformly_generatable` (`:180`): there exists a finite PUUS hypothesis class over the infinite prompt type that is not prompted-uniformly generatable.
- `promptSeparationClass_not_nonuniformly_generatable` (`:191`): the explicit two-hypothesis class is not prompted-nonuniformly generatable.
- `exists_finite_prompt_class_not_nonuniformly_generatable` (`:230`): there exists a finite PUUS hypothesis class over the infinite prompt type that is not prompted-nonuniformly generatable.

The final existential is stronger than the uniform negative because prompted uniform generation always implies prompted nonuniform generation. The code does not state whether this class is prompted-generatable in the limit.

## 3. Assumptions, quantifier order, and access model

### 3.1 Ordinary generation quantifier table

| Predicate | Exact outer order | Stream precondition | Threshold dependence | Required eventual correctness |
|---|---|---|---|---|
| `IsLimitGenerator G H` | `∀ L, L∈H → ∀ stream, Presents stream L → ∃ T, ∀ s, T≤s → ...` | Exact range equality `range(stream)=L` | No sample-size threshold; `T` may depend on `L` and `stream` | At every `s≥T`, output is in `L` and absent from the distinct input sample before `s` |
| `GeneratableInLimit H` | `∃ G, IsLimitGenerator G H` | As above | One generator for all targets and presentations | As above |
| `IsUniformGeneratorAt G H d` | `∀ L, L∈H → ∀ stream, StreamIn stream L → ∀ t, |sample_t|=d → ∀ s, t≤s → ...` | Only `range(stream)⊆L` | Fixed supplied `d`; independent of target and stream | Every exact-size-`d` trigger time forces correctness forever after |
| `UniformlyGeneratable H` | `∃ G, ∃ d, IsUniformGeneratorAt G H d` | As above | One class-wide `d` | As above |
| `IsNonuniformGenerator G H` | `∀ L, L∈H → ∃ d, ∀ stream, StreamIn stream L → ∀ t, |sample_t|=d → ∀ s≥t, ...` | Only `range(stream)⊆L` | `d` may depend on `L`; it cannot depend on `stream` | Same threshold-triggered correctness |
| `NonuniformlyGeneratable H` | `∃ G, IsNonuniformGenerator G H` | As above | One common generator; target-dependent thresholds | As above |
| `EventuallyUnboundedClosure H` | `∀ L, L∈H → ∀ stream, Presents stream L → ∃ t, core_H(sample_t) infinite` | Exact presentation | Witness time may depend on `L` and `stream` | No generator in the predicate; one infinite-core time is enough |
| `StreamwiseEventuallyUnboundedClosure H` | `∀ stream, ∃ t, versionSpace empty ∨ core infinite` | No target or presentation condition | Witness time depends on arbitrary stream | Structural disjunction only |

### 3.2 Prompted generation quantifier table

| Predicate | Exact order after fixing a generator | Threshold dependence | Stream/presentation condition | Rounds on which correctness is required |
|---|---|---|---|---|
| `IsPromptedUniformGeneratorAt G H d` | `∀ h∈H, ∀ xs, ∀ ys, ∀ y*, ∀ t, |promptedSample(h,xs,y*,t)|=d → ∀ s≥t, ∀ hs:0<s, ys(s-1)=y* → PromptedCorrectAt ... s` | One supplied `d` for the whole class, every hypothesis, and every prompt | None; `xs` and `ys` are arbitrary streams | Positive later rounds whose current prompt is `y*` |
| `PromptedUniformlyGeneratable H` | `∃ G, ∃ d, ...` | Class-wide threshold | None | As above |
| `IsPromptedNonuniformGenerator G H` | `∀ h∈H, ∃ d, ∀ xs, ∀ ys, ∀ y*, ...` | May depend on `h`; cannot depend on `xs`, `ys`, or `y*` | None | Same conditional rounds |
| `PromptedNonuniformlyGeneratable H` | `∃ G, ...` | One generator for all hypotheses | None | As above |
| `IsPromptedLimitGenerator G H` | `∀ h∈H, ∀ xs, ∀ ys, ∀ y*, PromptSupportPresented h xs y* → ∃ t, ∀ s≥t, ...` | No sample-size threshold; stabilization time may depend on all preceding data | `support(h,y*)⊆range(xs)`; extra examples are allowed | Positive later rounds whose current prompt is `y*` |
| `PromptedGeneratableInLimit H` | `∃ G, ...` | One generator for all hypotheses | As above | As above |

`PromptedCorrectAt` itself contains a universal proof argument `0<s`. The uniform, nonuniform, and limit predicates also quantify an outer proof of `0<s` before concluding `PromptedCorrectAt`. Logically this duplicated positivity bookkeeping does not add a second mathematical condition; for `s>0` it reduces to the single membership-and-freshness assertion, and for `s=0` the outer implication is vacuous.

### 3.3 Runtime information available to generators

| Feature | Ordinary generator | Prompted generator |
|---|---|---|
| Ordered input prefix | Yes: `Fin t → α` | Yes: `Fin t → (α × ι × ι)` |
| Repetitions visible | Yes | Yes |
| Distinct sample used internally by correctness | Yes, but computed from input prefix | Yes, all examples for freshness; label-filtered sample for thresholds |
| Target language/hypothesis supplied as runtime argument | No | No; however true labels in the history reveal values of the target hypothesis on observed examples |
| Current prompt supplied | Not applicable | Yes, as the third coordinate of the last observed triple at positive rounds |
| Class `H` supplied at runtime | No. An existential generator may be defined using `H` as a parameter before runtime | Same |
| Membership oracle supplied | No | No |
| Enumeration of `α` or `H` supplied | No explicit input; countability typeclasses and classical choice are used by named constructions | Same |
| Earlier generator outputs included in later histories | No | No |
| Randomness | None; generators are deterministic functions | None |
| Computability/effectivity restriction | None | None |
| Runtime or query complexity | None | None |

### 3.4 Main theorem-assumption table

| Formal result | Type assumptions | Class assumptions | Structural input | Conclusion |
|---|---|---|---|---|
| `uniform_generatability_iff_finite_closure_dimension` | `[Nonempty α] [Countable α]` | `UUS H` | None | Uniform generation iff finite closure dimension |
| `optimal_uniform_generation_sample_complexity_bounds` | `[Nonempty α] [Countable α]` | `UUS H`, `HasClosureDimension H d` | None | `d ≤ d*(H) ≤ d+1` |
| `nonuniform_generatability_iff_nondecreasing_finite_closure_cover` | `[Nonempty α] [Countable α]` | `UUS H` | Existential monotone countable cover on right side | Nonuniform generation iff every cover component has finite closure dimension |
| `countable_classes_are_nonuniformly_generatable` | `[Nonempty α] [Countable α]` | `UUS H`, `H.Countable` | None | Nonuniform generation |
| `finite_closure_dimension_cover_implies_generatable_in_limit` | `[Nonempty α] [Countable α]` | `UUS H` | Exact finite cover by finite-closure classes | Limit generation |
| `nondecreasing_euc_cover_implies_generatable_in_limit` | `[Nonempty α]` | None | Exact monotone countable cover by EUC classes | Limit generation |
| `finite_euc_cover_implies_generatable_in_limit` | `[Nonempty α] [Countable α]` | None | Exact finite cover by EUC classes | Limit generation |
| `eventuallyUnboundedClosure_implies_generatable_in_limit` | `[Nonempty α]` | EUC | None | Limit generation |
| `prompted_uniform_generatability_iff_finite_prompted_closure_dimension` | `[Nonempty α] [Countable α] [Countable ι]` | `PUUS H` | None | Prompted uniform generation iff finite prompted closure dimension |
| `prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover` | `[Nonempty α] [Countable α] [Countable ι]` | `PUUS H` | Monotone countable cover | Prompted nonuniform generation iff each component has finite prompted closure dimension |
| `finite_prompt_classes_are_uniformly_generatable` | `[Nonempty α] [Countable α] [Countable ι] [Finite ι]` | `PUUS H`, `H.Finite` | None | Prompted uniform generation |
| `countable_prompt_classes_are_nonuniformly_generatable` | Same | `PUUS H`, `H.Countable` | None | Prompted nonuniform generation |
| `countable_prompt_classes_are_generatable_in_limit` | Same | `PUUS H`, `H.Countable` | None | Prompted limit generation |

A Lean `[Countable α]` instance permits finite as well as countably infinite types. The UUS or PUUS assumptions may force nontrivial classes to be empty on an insufficiently large universe; the theorem types do not separately assume `[Infinite α]`.

## 4. Dependency, helper, bridge, and encoding audit

### 4.1 Target-versus-dependency scope

The target umbrella imports all 18 modules in the same-named subtree. The two `Core` files are dependency scope. The Paper 02 statements use the generic `Core.Countable` objects `Language`, `LanguageClass`, `Stream`, `Generator`, `Presents`, `StreamIn`, `sample`, `output`, and `CorrectAt`, together with elementary sample-cardinality lemmas.

The fixed-universe indexed-family machinery in `Core.Basic`—including `LanguageFamily`, `Consistent`, and `MembershipOracle`—does not occur in the target subtree. Consequently, no target theorem is an oracle-algorithm theorem, and no theorem assumes decidable membership in class languages.

### 4.2 Closure and prompted closure are not circular definitions

Neither `ClosureDimensionAtMost` nor its prompted analogue mentions a generator or any generation conclusion. Their content is solely about finite samples, nonempty positive version spaces, and finite versus infinite common cores. The characterization theorems are therefore not circular at the level of definitions.

The option-valued `closure` and `promptedClosure` are representational wrappers. The dimension notions use the underlying version space and common core directly. This matters in the empty-version-space case: the raw common core is `Set.univ`, but a witness is impossible because witness predicates demand nonemptiness.

### 4.3 The zero-dimension convention is asymmetric by design

For positive `d`, `HasClosureDimension H d` and `HasPromptedClosureDimension H d` require an exact-size finite-core witness. For `d=0`, they require no witness of size zero. They require only the “at most zero” condition: every nonempty consistent sample of positive cardinality has infinite core.

Consequences:

- The empty class has closure dimension zero at the level of the relational definition, because every positive-sample nonempty-version-space premise is false.
- A class may have a finite common core at the empty sample and still satisfy the zero convention, provided every positive consistent sample has infinite core.
- The public complementarity theorems show that this convention still yields the stated finite-versus-unbounded dichotomy.

### 4.4 Exact-size thresholds are made monotone by sample crossing

Uniform and prompted-uniform correctness is triggered only at a prefix with sample cardinality **equal** to `d`. The code separately proves that distinct sample size rises by at most one per round and therefore crosses every intermediate integer. This supports the public monotonicity theorems:

- `uniform_threshold_mono`;
- `prompted_uniform_threshold_mono`.

Accordingly, “works at `d`” implies “works at every larger threshold,” but this is a theorem, not definitionally built into `IsUniformGeneratorAt`.

### 4.5 Cover predicates encode exact union, not merely coverage

Both `IsNondecreasingCover` and `IsPromptedNondecreasingCover` include exact equality `H=⋃_nH_n`, not only `H⊆⋃_nH_n`. Thus each component is automatically a subclass of `H`, because equality implies `⋃_nH_n⊆H`.

`IsFiniteCover` similarly uses exact equality. None of the cover predicates requires disjointness. Only the countable nonuniform covers require monotonicity; finite covers used for limit generation do not.

### 4.6 No hidden generator link is present in EUC

`EventuallyUnboundedClosure` does not quantify a generator and does not directly state the generation conclusion. It says that along each exact target presentation, one common core becomes infinite. The theorem `eventuallyUnboundedClosure_implies_generatable_in_limit` supplies the nontrivial link to a fresh output.

`StreamwiseEventuallyUnboundedClosure` is strictly stronger in quantifier scope: it ranges over arbitrary streams. The target code does not use it as the hypothesis of the finite-EUC theorem. Instead, it gives an explicit counterexample to universal equivalence with EUC. This avoids silently replacing EUC by a stronger condition in the final formal theorem statement.

### 4.7 The prediction “learnability” predicates directly encode dimension finiteness

The most significant bridge audit finding is definitional:

```lean
PACLearnableViaVC H := HasFiniteVCDimension H
OnlineLearnableViaLittlestone H := HasFiniteLittlestoneDimension H
```

No theorem has the form

```text
literal PAC learnability ↔ finite VC dimension
```

or

```text
literal online learnability ↔ finite Littlestone dimension.
```

There are no literal learning predicates to bridge. Thus the separation packages involving these names establish only dimension-finiteness combinations. This is not internally circular—the conclusions are valid consequences of the definitions—but it is a direct encoding of the characterization boundary and is substantially weaker than formalizing the corresponding learning models.

The code proves only the implications

- infinite VC dimension ⇒ not `PACLearnableViaVC`;
- infinite Littlestone dimension ⇒ not `OnlineLearnableViaLittlestone`.

It does not declare public finite-versus-infinite complement theorems for either dimension encoding.

### 4.8 Prompted histories contain privileged information

A prompted generator receives the true label `h(x_i)` as the middle coordinate of every observed triple. This is stronger information than receiving examples and prompts alone. The threshold sample `promptedSample h xs y t` is defined using the target hypothesis directly, but on actual histories the generator can reconstruct the same labeled subset from the revealed middle coordinates; the public history-sample identities make this explicit.

The generator is not required to behave coherently on arbitrary malformed histories. Correctness is tested only on histories exactly of the form `(x_i,h(x_i),y_i)`.

### 4.9 Named generators are noncomputable set-theoretic witnesses

The public named generators—`closureGenerator`, `partitionLimitGenerator`, `eventuallyUnboundedCoverGenerator`, `finiteEUCUnionGenerator`, and `promptedClosureGenerator`—use classical choice or private helpers that use classical choice. They are valid Lean functions but are not accompanied by computability, decidability, oracle, or complexity guarantees.

Countability typeclasses permit fixed enumerations of infinite subsets to be chosen noncomputably in the finite-cover constructions. No such enumeration is supplied as part of the theorem input.

### 4.10 Wrappers, restatements, and packaged examples

Several public declarations repeat already established content in a different quantifier shape:

- `finite_closure_dimension_implies_uniform` removes a chosen numerical dimension from the sufficiency statement.
- `finite_union_of_paper_cone_classes_generatable_in_limit` rewrites upward cones in a union form on `ℕ`.
- `theorem_C4_eventually_unbounded_closure` and `theorem_C2_finite_eventually_unbounded_closure_cover` add countability/UUS hypotheses to stronger core theorems.
- `theorem_4_1_i_combinatorial_core` through `theorem_4_1_vi_combinatorial_core` package previously proved properties of explicit witness classes into existential statements.
- `theorem_4_1_combinatorial_core` is a conjunction of those six packages.
- The various `exists_...` declarations package explicit constructions into bare existential separations.

These wrappers are public propositions and are included in the substantive inventory, but they do not add stronger mathematical content than the cited component statements.

## 5. Edge cases, vacuity, and potential statement-level risks

### 5.1 Empty or finite example universes

A generator `G : ∀t,(Fin t→α)→α` cannot exist when `α` is empty, because at `t=0` it would have to return an element of `α` from the unique empty history. This is why constructive existence theorems generally assume `[Nonempty α]`.

`[Countable α]` does not imply `[Nonempty α]` or `[Infinite α]`. If `α` is finite, `UUS H` forces `H` to have no members, because no subset of a finite type is infinite. The main ordinary characterization still has a meaningful but potentially vacuous empty-class instance when `[Nonempty α]` holds.

Similarly, under PUUS, a nonempty prompted class requires every quantified prompt support to be infinite. In the main theorems, `[Nonempty α]` and nonemptiness of the hypothesis class imply that the prompt type is nonempty; under those conditions a finite example type forces the class to be empty. The theorem statements do not replace PUUS by an explicit `[Infinite α]` hypothesis.

### 5.2 Empty target languages and exact presentations

For nonempty `α`, no stream `ℕ→α` has empty range. Hence the limit-generation obligation for an empty target language is vacuous: there is no exact presentation of that language. UUS excludes this edge case in the main ordinary characterization and hierarchy implications.

For uniform and nonuniform generation, there is likewise no `StreamIn` stream for an empty target when `α` is nonempty. Thus those target-specific universal clauses are vacuous unless other class assumptions exclude the empty language.

### 5.3 Streams that do not reach the threshold

Uniform and nonuniform definitions use `StreamIn`, not exact presentation. Even if `L` is infinite, a stream contained in `L` may repeat one point forever. If `d>1`, such a stream never has a prefix with exactly `d` distinct observations, and the implication defining threshold correctness is vacuous on that stream.

This is not a hidden flaw in the implication to limit generation: exact presentations of infinite languages do reach every finite distinct-sample size. It is, however, a material limitation of what the uniform/nonuniform predicates demand on arbitrary contained streams.

The same issue occurs in prompted uniform and nonuniform generation: if the example stream never accumulates `d` distinct examples labeled by `y*`, no correctness obligation is triggered for that `(h,xs,y*)` branch.

### 5.4 The threshold `d=0`

At ordinary time `t=0`, the distinct sample is empty and has cardinality zero. Therefore, if a generator works uniformly at threshold zero, the trigger applies at `t=0` for every admissible target and stream, forcing correctness at every `s≥0`.

For prompted generation, a zero threshold also triggers at `t=0`, but correctness at `s=0` is vacuous because `PromptedCorrectAt` quantifies a proof of `0<s`. It becomes substantive at every later positive round satisfying the prompt condition.

### 5.5 Empty version spaces and vacuous common cores

When `V_H(S)=∅`, `commonCore H S` is `Set.univ`. Therefore statements about the raw core can be trivially true in inconsistent cases. The substantive dimension and generator branch conditions guard against this by requiring nonempty version space. The option-valued closures also record the inconsistent case as `none`.

The prompted definitions have the identical issue and identical guard.

### 5.6 Output freshness is not output novelty

At time `t`, correctness excludes membership in the input sample `S_t`. It does not exclude equality with `G`'s output at an earlier time. Thus a generator may repeat an output as long as that point has not appeared in the input stream. On an exact presentation the point will eventually be observed if it belongs to the target, but no immediate pairwise-distinct-output condition is formalized.

The prompted model has the same feature: freshness is against observed examples, not against previous prompted outputs.

### 5.7 Exogenous streams do not react to outputs

The stream is universally quantified independently of the generator. Generator outputs are not appended to the stream and need not influence future observations. Consequently, the formal interaction is repeated prediction from prefixes of a fixed exogenous stream, not an autonomous process that grows its own generated dataset.

### 5.8 Prompted current-round timing

At positive length `s`, the prompted history includes indices `0,...,s-1`, and the required prompt is `ys(s-1)`. The generator therefore sees the current example, its true label, and the current prompt before outputting. Freshness excludes the current example `xs(s-1)` because it belongs to `sample xs s`.

This timing is materially different from a protocol in which a prompt is given before the current example or in which generation occurs before the current labeled observation.

### 5.9 Prompted limit clauses can be prompt-vacuous

After the stabilization time for `y*`, correctness is required only on rounds whose current prompt equals `y*`. If the prompt stream uses `y*` only finitely often, one may choose a later stabilization time and the obligation becomes vacuous. The definition does not require each prompt to recur infinitely often.

### 5.10 Support-presentation inclusion can itself be impossible

`PromptSupportPresented h xs y` requires an entire support to lie in the range of a countable stream. For uncountable supports this is impossible, so the corresponding prompted-limit implication is vacuous. The principal prompted theorems assume `[Countable α]`, avoiding this issue for subsets of `α`, but the bare prompted-limit definition and hierarchy theorem are more general.

### 5.11 Finite-cover zero-index case

`IsFiniteCover H classes` permits `n=0`. Then `Fin 0` has no indices and the union is empty, forcing `H=∅`. The finite-cover sufficiency theorems include this vacuous empty-class case.

### 5.12 Countability of a class versus countability of the universe

`H.Countable` means the set of languages or hypotheses is countable. `[Countable α]` means the example type is countable. These are independent assumptions and both appear in the countable-class corollaries. A countable universe has an uncountable powerset, so classes of languages can be uncountable; the explicit upward-cone theorem demonstrates this.

### 5.13 Finite and infinite VC/Littlestone predicates are not publicly proved complementary

The code defines both finite and infinite dimension predicates and proves that infinite dimension negates the corresponding finite-dimension proxy. It does not expose a public theorem asserting the converse negation-to-infinite implication. Therefore this reconstruction does not silently replace either pair by a proved dichotomy.

### 5.14 The stronger EUC predicate is explicitly rejected as an equivalent reformulation

The development does not leave the relationship between EUC and the arbitrary-stream predicate ambiguous. It proves a concrete EUC class failing the streamwise predicate and then negates the universal equivalence. Any downstream interpretation that treats the two predicates as interchangeable would contradict a public target theorem.

### 5.15 No direct circularity found in closure-cover conditions

The ordinary and prompted finite-closure predicates do not contain generation conclusions. EUC does not contain a generator. The finite and monotone cover predicates contain only class inclusion/equality conditions. The principal characterization and sufficiency assumptions therefore do not directly encode their desired conclusions.

The prediction aliases are the exception in a different sense: they do not circularly assume a separation conclusion, but they define the named learnability notions to be exactly the combinatorial dimensions used to prove those conclusions. This creates a semantic gap to literal learning, not an internal logical circularity.

## 6. What the Lean statements do not establish

The target source does **not** establish any of the following.

1. **No comparison with an author paper.** This Stage 1 reconstruction does not determine whether any external theorem, definition, example, or proof is faithfully represented.

2. **No literal PAC-learning theorem.** There is no distribution space, iid sampling, confidence/accuracy parameter, risk, empirical risk, learner output, sample-complexity bound, or randomized algorithm. `PACLearnableViaVC` is exactly finite VC dimension by definition.

3. **No literal online-learning theorem.** There is no adversarial sequence protocol, learner predictions, losses, mistakes, horizon, regret, comparator, or sublinear-regret statement. `OnlineLearnableViaLittlestone` is exactly finite Littlestone dimension by definition.

4. **No bridge from dimension to learning.** No public theorem connects a separately defined PAC or online predicate to VC or Littlestone dimension, because no separate predicate exists.

5. **No computable-generation result.** All generators may be arbitrary set-theoretic functions; named constructions are noncomputable. There are no decidability, recursion, Turing-machine, oracle-complexity, or runtime claims.

6. **No membership-oracle result.** The dependency bundle contains a membership-oracle structure for a different indexed-family interface, but no Paper 02 declaration uses it.

7. **No randomized generator.** All generation notions are deterministic and point-valued.

8. **No guarantee of pairwise-distinct outputs.** Freshness is relative only to observed inputs.

9. **No feedback of outputs into the data stream.** The stream is exogenous.

10. **No exact uniform sample-complexity equality.** The strongest class-optimal statement is `d≤d*(H)≤d+1` when `HasClosureDimension H d`.

11. **No prompted sample-complexity object or optimality theorem.** The prompted closure generator works at `d+1`, but no least-threshold extended natural is defined for prompted generation.

12. **No characterization of ordinary generation in the limit.** Finite closure-dimension covers, monotone EUC covers, finite EUC covers, and EUC itself are sufficient. No iff theorem characterizes all limit-generatable classes.

13. **No necessity of EUC for limit or nonuniform generation.** Indeed, a nonuniformly generatable class failing EUC is explicitly constructed.

14. **No closure under finite unions for uniform or nonuniform generation.** The code proves a union of two closure-dimension-zero classes can fail nonuniform generation.

15. **No closure under countable unions for limit generation.** The code proves the opposite through an explicit counterexample.

16. **No generic theorem that every finite prompted class is uniformly generatable for infinite prompt spaces.** The positive finite-class theorem requires `[Finite ι]`, and an infinite-prompt counterexample is formalized.

17. **No conclusion about prompted limit generation for the infinite-prompt two-hypothesis counterexample.** Only failures of prompted uniform and prompted nonuniform generation are stated.

18. **No transport theorem identifying the explicit example universes with other encodings.** The statements are on the concrete sum and product types appearing in their definitions.

19. **No exact dimensions for most examples.** Upper bounds such as `d=1` or `d=2`, and infinitude claims, are proved as needed; exact finite VC or Littlestone values are generally not stated.

20. **No theorem that finite and infinite VC/Littlestone dimension are exact logical complements.** Only the directions used by the proxy negations are public.

## 7. Provisional statement-level difficulty assessment

This assessment uses only the complexity of the formal statements and definition dependencies, not theorem proof bodies.

| Statement family | Provisional difficulty | Statement-level reason |
|---|---|---|
| Basic sample/version-space identities | Low | Finite-set membership, monotonicity, and direct unfolding |
| Uniform ⇒ nonuniform and analogous prompted implication | Low | The premise has a class-wide threshold, while the conclusion permits weaker target-dependent thresholds |
| Nonuniform ⇒ limit under UUS/PUUS | Medium | Requires exact presentations to cross target-dependent distinct-sample thresholds while preserving quantifier dependence |
| Closure witness monotonicity and finite/infinite complementarity | Medium | Cardinality restriction plus well-ordering/dichotomy over witness sizes |
| Closure witness defeats a threshold | High | Generator-wise adversarial statement with arbitrary histories, finite core, and target selection after observing a proposed output |
| Uniform iff finite closure dimension | High | Combines a universal lower bound against every generator with a noncomputable fresh-core construction and exact threshold control |
| Sharp interval `d≤d*(H)≤d+1` | Medium after characterization; high standalone | Least-threshold extended-natural API plus generator-wise lower bound and constructive upper bound |
| Nonuniform iff monotone finite-closure cover | High | One global generator must merge countably many component generators while keeping target-dependent but stream-independent thresholds |
| Finite closure cover ⇒ limit generation | High | Finite competing components, no monotonicity, target-dependent stabilization, and fresh valid output from an eventually selected component |
| Limit-not-nonuniform diagonal separation | High | Negates a nested `∃G ∀L ∃d ∀stream` property while preserving a positive limit generator |
| Countable union of zero-closure classes not limit-generatable | Very high | Negates every limit generator by a staged diagonal while the final stream must present a member of the union |
| VC example statements | Medium | Explicit shattering/nonshattering constructions; no probability theory is formalized |
| Littlestone example statements | Medium to high | Recursive complete-tree shattering and finite-depth exclusions |
| Six-way prediction package | Medium | A conjunction of previously separated combinatorial witness properties; easier than literal learning theorems would be |
| EUC ⇒ limit generation | Medium | The structural hypothesis supplies an infinite common core along each target presentation, closely matching the validity-and-freshness conclusion |
| Monotone EUC cover ⇒ limit generation | High | Dynamically selecting among countably many classes while preserving target containment |
| Finite EUC union theorem | Very high | Activation times, frozen infinite cores, finite competition, and maximal progress, all without the stronger arbitrary-stream hypothesis |
| EUC/streamwise inequivalence diagnostic | Medium | Explicit class and arbitrary stream with nonempty version spaces but permanently finite cores |
| Prompted uniform iff finite prompted closure dimension | Very high | All ordinary adversarial and constructive issues plus true-label filtering, prompt quantifiers, current-round timing, and global freshness |
| Prompted nonuniform characterization | Very high | Countable cover merging with thresholds independent of both streams and all prompts |
| Finite-prompt countable-class corollaries | Medium after characterization | Finite combinatorics over hypotheses and prompt labels, then reuse of the characterization |
| Infinite-prompt two-hypothesis separation | High | A finite class must have arbitrarily large prompt-specific finite cores and defeat even target-dependent thresholds |

The formally hardest statement families, judged from quantifier shape alone, are the generator-wise closure necessity, the two diagonal non-generation separations, the finite-EUC union theorem, and the prompted uniform/nonuniform characterizations.

## 8. Consolidated reconstruction

The Lean development presents a coherent deterministic positive-data generation theory with three ordinary levels and three prompted levels. Its strongest exact ordinary characterization is uniform generation iff finite closure dimension under nonempty countable universe and UUS assumptions. Its strongest exact prompted characterization is the analogous prompted theorem under countability and PUUS. Nonuniform generation is characterized by monotone countable covers in both settings. Limit generation receives several sufficient conditions but no full characterization. The code proves strict separations showing that the hierarchy does not collapse and that finite/countable union behavior is delicate.

The main statement-faithfulness risk for a later Stage 2 comparison is not an internal inconsistency in the closure theory. It is the prediction interface: the two predicates whose names refer to PAC and online learnability are direct aliases for dimension finiteness, so the formal six-region theorem is explicitly only combinatorial. A second major audit point is the EUC diagnostic: the code itself rejects the stronger arbitrary-stream condition as universally equivalent to exact-presentation EUC, while separately proving the finite-union theorem using EUC proper. A third is the prompted access/timing model: the generator sees the current labeled example and prompt before outputting, and the threshold counts observed examples having a true label, not occurrences of a prompt.

Subject to those semantic boundaries, the target statements are nonvacuous on their intended infinite-support classes, preserve the important threshold dependencies, and expose their nonemptiness/countability/finite-prompt assumptions in theorem types.

## Appendix A. Complete substantive target-declaration inventory

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean`

- **`IsClosureWitness`** — line 22; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def IsClosureWitness (H : GenLimit.Generic.LanguageClass α) (S : Finset α) : Prop := (versionSpace H S).Nonempty ∧ (commonCore H S).Finite`

- **`ClosureDimensionAtMost`** — line 30; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def ClosureDimensionAtMost (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop := ∀ S : Finset α, d < S.card → (versionSpace H S).Nonempty → (commonCore H S).Infinite`

- **`HasClosureDimension`** — line 39; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasClosureDimension (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop := ClosureDimensionAtMost H d ∧ (d = 0 ∨ ∃ S : Finset α, S.card = d ∧ IsClosureWitness H S)`

- **`HasFiniteClosureDimension`** — line 45; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasFiniteClosureDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ d : ℕ, HasClosureDimension H d`

- **`HasInfiniteClosureDimension`** — line 51; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasInfiniteClosureDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ d : ℕ, ∃ S : Finset α, d ≤ S.card ∧ IsClosureWitness H S`

- **`closure_witness_defeats_uniform_threshold`** — line 82; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem closure_witness_defeats_uniform_threshold [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {S : Finset α} {d : ℕ} (hSd : S.card = d) (hS : IsClosureWitness H S) (gen : GenLimit.Generic.Generator α) : ¬ IsUniformGeneratorAt gen H d`

- **`closure_dimension_necessity`** — line 178; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem closure_dimension_necessity [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hC : HasInfiniteClosureDimension H) : ¬ UniformlyGeneratable H`

- **`finite_closure_dimension_iff_not_infinite`** — line 190; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem finite_closure_dimension_iff_not_infinite {H : GenLimit.Generic.LanguageClass α} : HasFiniteClosureDimension H ↔ ¬ HasInfiniteClosureDimension H`

- **`closureGenerator`** — line 251; `def`; **public noncomputable generator construction**.  
  Exact stripped declaration statement/body: `noncomputable def closureGenerator [Nonempty α] (H : GenLimit.Generic.LanguageClass α) (d : ℕ) (hC : ClosureDimensionAtMost H d) : GenLimit.Generic.Generator α := by classical exact fun _ xs => let S := GenLimit.Generic.sequenceSample xs if hd : d < S.card then if hVS : (versionSpace H S).Nonempty then Classical.choose (core_diff_sample_infinite hC S hd hVS).nonempty else Classical.choice inferInstance else Classical.choice inferInstance`

- **`closureGenerator_isUniformGeneratorAt`** — line 281; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem closureGenerator_isUniformGeneratorAt [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : IsUniformGeneratorAt (closureGenerator H d hC.1) H (d + 1)`

- **`closure_dimension_sufficiency`** — line 308; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem closure_dimension_sufficiency [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : ∃ gen : GenLimit.Generic.Generator α, IsUniformGeneratorAt gen H (d + 1)`

- **`finite_closure_dimension_implies_uniform`** — line 317; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem finite_closure_dimension_implies_uniform [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hfinite : HasFiniteClosureDimension H) : UniformlyGeneratable H`

- **`uniform_generatability_iff_finite_closure_dimension`** — line 329; `theorem`; **main characterization theorem**.  
  Exact stripped declaration statement/body: `theorem uniform_generatability_iff_finite_closure_dimension [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) : UniformlyGeneratable H ↔ HasFiniteClosureDimension H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean`

- **`CountableUnionUniverse`** — line 29; `abbrev`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `abbrev CountableUnionUniverse := ℕ ⊕ (ℕ × ℕ)`

- **`countableUnionAnchor`** — line 31; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def countableUnionAnchor (n : ℕ) : CountableUnionUniverse := Sum.inl n`

- **`countableUnionTail`** — line 34; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def countableUnionTail (n : ℕ) : Set CountableUnionUniverse := {x | ∃ k, x = Sum.inr (n, k)}`

- **`countableUnionCore`** — line 39; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def countableUnionCore : ℕ → Set CountableUnionUniverse | 0 => {x | ∃ n, x = countableUnionAnchor n} | n + 1 => {countableUnionAnchor n} ∪ countableUnionTail n`

- **`countableUnionClasses`** — line 43; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def countableUnionClasses : ℕ → GenLimit.Generic.LanguageClass CountableUnionUniverse := fun n ↦ upwardCone (countableUnionCore n)`

- **`countableUnionHardClass`** — line 47; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def countableUnionHardClass : GenLimit.Generic.LanguageClass CountableUnionUniverse := ⋃ n, countableUnionClasses n`

- **`countableUnionCore_infinite`** — line 81; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem countableUnionCore_infinite (n : ℕ) : (countableUnionCore n).Infinite`

- **`countableUnionClasses_uus`** — line 101; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem countableUnionClasses_uus (n : ℕ) : UUS (countableUnionClasses n)`

- **`countableUnionClasses_closure_dimension_zero`** — line 106; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem countableUnionClasses_closure_dimension_zero (n : ℕ) : HasClosureDimension (countableUnionClasses n) 0`

- **`countableUnionHardClass_not_generatable_in_limit`** — line 578; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem countableUnionHardClass_not_generatable_in_limit : ¬GeneratableInLimit countableUnionHardClass`

- **`exists_countable_sequence_zero_closure_union_not_limit`** — line 607; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem exists_countable_sequence_zero_closure_union_not_limit : ∃ classes : ℕ → GenLimit.Generic.LanguageClass CountableUnionUniverse, (∀ n, UUS (classes n)) ∧ (∀ n, HasClosureDimension (classes n) 0) ∧ ¬GeneratableInLimit (⋃ n, classes n)`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean`

- **`UUS`** — line 19; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def UUS (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ L, L ∈ H → L.Infinite`

- **`versionSpace`** — line 23; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def versionSpace (H : GenLimit.Generic.LanguageClass α) (S : Finset α) : Set (GenLimit.Generic.Language α) := {L | L ∈ H ∧ (↑S : Set α) ⊆ L}`

- **`commonCore`** — line 28; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def commonCore (H : GenLimit.Generic.LanguageClass α) (S : Finset α) : GenLimit.Generic.Language α := {x | ∀ L, L ∈ versionSpace H S → x ∈ L}`

- **`closure`** — line 32; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `noncomputable def closure (H : GenLimit.Generic.LanguageClass α) (S : Finset α) : Option (GenLimit.Generic.Language α) := by classical exact if (versionSpace H S).Nonempty then some (commonCore H S) else none`

- **`IsLimitGenerator`** — line 98; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def IsLimitGenerator (gen : GenLimit.Generic.Generator α) (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α, GenLimit.Generic.Presents stream L → ∃ T, ∀ s, T ≤ s → GenLimit.Generic.CorrectAt gen L stream s`

- **`GeneratableInLimit`** — line 103; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def GeneratableInLimit (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ gen : GenLimit.Generic.Generator α, IsLimitGenerator gen H`

- **`IsUniformGeneratorAt`** — line 111; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def IsUniformGeneratorAt (gen : GenLimit.Generic.Generator α) (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop := ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α, GenLimit.Generic.StreamIn stream L → ∀ t, (GenLimit.Generic.sample stream t).card = d → ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s`

- **`UniformlyGeneratable`** — line 118; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def UniformlyGeneratable (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ gen : GenLimit.Generic.Generator α, ∃ d : ℕ, IsUniformGeneratorAt gen H d`

- **`IsNonuniformGenerator`** — line 123; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def IsNonuniformGenerator (gen : GenLimit.Generic.Generator α) (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ L, L ∈ H → ∃ d : ℕ, ∀ stream : GenLimit.Generic.Stream α, GenLimit.Generic.StreamIn stream L → ∀ t, (GenLimit.Generic.sample stream t).card = d → ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s`

- **`NonuniformlyGeneratable`** — line 130; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def NonuniformlyGeneratable (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ gen : GenLimit.Generic.Generator α, IsNonuniformGenerator gen H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean`

- **`upwardCone_not_countable`** — line 63; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem upwardCone_not_countable [Countable α] {P N : Set α} (hP : P.Infinite) (hDisjoint : Disjoint P N) : ¬(upwardCone N).Countable`

- **`exists_uncountable_uniformly_generatable_class`** — line 93; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem exists_uncountable_uniformly_generatable_class : ∃ H : GenLimit.Generic.LanguageClass ℤ, ¬H.Countable ∧ UUS H ∧ UniformlyGeneratable H`

- **`BlockUniverse`** — line 112; `abbrev`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `abbrev BlockUniverse := (ℕ × ℕ) ⊕ (Bool × ℕ)`

- **`blockFinset`** — line 114; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def blockFinset (d : ℕ) : Finset BlockUniverse := (Finset.range d).image (fun j ↦ Sum.inl (d, j))`

- **`blockSet`** — line 117; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def blockSet (d : ℕ) : Set BlockUniverse := ↑(blockFinset d)`

- **`blockTail`** — line 119; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def blockTail (b : Bool) : Set BlockUniverse := Set.range (fun n : ℕ ↦ Sum.inr (b, n))`

- **`blockLanguage`** — line 122; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def blockLanguage (b : Bool) (d : ℕ) : Set BlockUniverse := blockSet d ∪ blockTail b`

- **`blockSeparationClass`** — line 125; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def blockSeparationClass : GenLimit.Generic.LanguageClass BlockUniverse := Set.range (fun p : Bool × ℕ ↦ blockLanguage p.1 p.2)`

- **`blockSeparationClass_countable`** — line 141; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem blockSeparationClass_countable : blockSeparationClass.Countable`

- **`blockSeparationClass_uus`** — line 144; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem blockSeparationClass_uus : UUS blockSeparationClass`

- **`blockSeparationClass_infinite_closure_dimension`** — line 172; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem blockSeparationClass_infinite_closure_dimension : HasInfiniteClosureDimension blockSeparationClass`

- **`exists_countable_nonuniform_not_uniform_class`** — line 183; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem exists_countable_nonuniform_not_uniform_class : ∃ H : GenLimit.Generic.LanguageClass BlockUniverse, H.Countable ∧ UUS H ∧ NonuniformlyGeneratable H ∧ ¬UniformlyGeneratable H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean`

- **`EventuallyUnboundedClosure`** — line 22; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def EventuallyUnboundedClosure (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α, GenLimit.Generic.Presents stream L → ∃ t, (commonCore H (GenLimit.Generic.sample stream t)).Infinite`

- **`finite_closure_dimension_implies_eventuallyUnboundedClosure`** — line 44; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem finite_closure_dimension_implies_eventuallyUnboundedClosure {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hFinite : HasFiniteClosureDimension H) : EventuallyUnboundedClosure H`

- **`uniform_implies_eventuallyUnboundedClosure`** — line 60; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem uniform_implies_eventuallyUnboundedClosure [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hUniform : UniformlyGeneratable H) : EventuallyUnboundedClosure H`

- **`cofiniteLanguageClass`** — line 72; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def cofiniteLanguageClass (α : Type*) : GenLimit.Generic.LanguageClass α := {L | ∃ A : Set α, A.Finite ∧ L = Set.univ \ A}`

- **`cofiniteLanguageClass_countable`** — line 75; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem cofiniteLanguageClass_countable [Countable α] : (cofiniteLanguageClass α).Countable`

- **`cofiniteLanguageClass_uus`** — line 84; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem cofiniteLanguageClass_uus [Infinite α] : UUS (cofiniteLanguageClass α)`

- **`cofiniteLanguageClass_not_eventuallyUnboundedClosure`** — line 111; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem cofiniteLanguageClass_not_eventuallyUnboundedClosure : ¬EventuallyUnboundedClosure (cofiniteLanguageClass ℕ)`

- **`exists_nonuniformly_generatable_not_eventuallyUnboundedClosure`** — line 127; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem exists_nonuniformly_generatable_not_eventuallyUnboundedClosure : ∃ H : GenLimit.Generic.LanguageClass ℕ, H.Countable ∧ UUS H ∧ NonuniformlyGeneratable H ∧ ¬EventuallyUnboundedClosure H`

- **`eventuallyUnboundedCoverGenerator`** — line 169; `def`; **public noncomputable generator construction**.  
  Exact stripped declaration statement/body: `noncomputable def eventuallyUnboundedCoverGenerator [Nonempty α] (classes : ℕ → GenLimit.Generic.LanguageClass α) : GenLimit.Generic.Generator α := by classical exact fun t xs ↦ let S := GenLimit.Generic.sequenceSample xs let active := eucActiveIndices classes S t if h : active.Nonempty then let selected := active.max' h freshFromCore (commonCore (classes selected) S) ((mem_eucActiveIndices_iff.mp (active.max'_mem h)).2.2) S else Classical.choice inferInstance`

- **`nondecreasing_euc_cover_implies_generatable_in_limit`** — line 205; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem nondecreasing_euc_cover_implies_generatable_in_limit [Nonempty α] {H : GenLimit.Generic.LanguageClass α} {classes : ℕ → GenLimit.Generic.LanguageClass α} (hcover : IsNondecreasingCover H classes) (hEUC : ∀ n, EventuallyUnboundedClosure (classes n)) : GeneratableInLimit H`

- **`theorem_C4_eventually_unbounded_closure`** — line 275; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem theorem_C4_eventually_unbounded_closure [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) (hcover : ∃ classes : ℕ → GenLimit.Generic.LanguageClass α, IsNondecreasingCover H classes ∧ ∀ n, EventuallyUnboundedClosure (classes n)) : GeneratableInLimit H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean`

- **`StreamwiseEventuallyUnboundedClosure`** — line 16; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def StreamwiseEventuallyUnboundedClosure (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ stream : GenLimit.Generic.Stream α, ∃ t, ¬(versionSpace H (GenLimit.Generic.sample stream t)).Nonempty ∨ (commonCore H (GenLimit.Generic.sample stream t)).Infinite`

- **`eventuallyUnboundedClosure_implies_generatable_in_limit`** — line 51; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem eventuallyUnboundedClosure_implies_generatable_in_limit [Nonempty α] {H : GenLimit.Generic.LanguageClass α} (hEUC : EventuallyUnboundedClosure H) : GeneratableInLimit H`

- **`SpineTailUniverse`** — line 89; `abbrev`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `abbrev SpineTailUniverse := ℕ ⊕ (ℕ × ℕ)`

- **`spineTailLanguage`** — line 92; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def spineTailLanguage (n : ℕ) : GenLimit.Generic.Language SpineTailUniverse := {x | match x with | Sum.inl i => i < n | Sum.inr p => p.1 = n}`

- **`spineTailClass`** — line 97; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def spineTailClass : GenLimit.Generic.LanguageClass SpineTailUniverse := Set.range spineTailLanguage`

- **`spineTailLanguage_infinite`** — line 100; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem spineTailLanguage_infinite (n : ℕ) : (spineTailLanguage n).Infinite`

- **`spineTailClass_uus`** — line 113; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem spineTailClass_uus : UUS spineTailClass`

- **`spineTailClass_eventuallyUnboundedClosure`** — line 127; `theorem`; **diagnostic/counterexample theorem**.  
  Exact stripped declaration statement/body: `theorem spineTailClass_eventuallyUnboundedClosure : EventuallyUnboundedClosure spineTailClass`

- **`spineStream`** — line 163; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def spineStream : GenLimit.Generic.Stream SpineTailUniverse := fun n ↦ Sum.inl n`

- **`spineTailClass_not_streamwise_euc`** — line 212; `theorem`; **diagnostic/counterexample theorem**.  
  Exact stripped declaration statement/body: `theorem spineTailClass_not_streamwise_euc : ¬StreamwiseEventuallyUnboundedClosure spineTailClass`

- **`eventuallyUnboundedClosure_not_equivalent_to_streamwise`** — line 221; `theorem`; **diagnostic/counterexample theorem**.  
  Exact stripped declaration statement/body: `theorem eventuallyUnboundedClosure_not_equivalent_to_streamwise : EventuallyUnboundedClosure spineTailClass ∧ ¬StreamwiseEventuallyUnboundedClosure spineTailClass`

- **`printed_EUC_equivalence_is_false`** — line 229; `theorem`; **diagnostic/counterexample theorem**.  
  Exact stripped declaration statement/body: `theorem printed_EUC_equivalence_is_false : ¬(∀ (H : GenLimit.Generic.LanguageClass SpineTailUniverse), EventuallyUnboundedClosure H ↔ StreamwiseEventuallyUnboundedClosure H)`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteConeCover.lean`

- **`upwardCone`** — line 22; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def upwardCone (S : Set α) : GenLimit.Generic.LanguageClass α := {L | S ⊆ L}`

- **`upwardCone_has_closure_dimension_zero`** — line 41; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem upwardCone_has_closure_dimension_zero {S : Set α} (hS : S.Infinite) : HasClosureDimension (upwardCone S) 0`

- **`upwardCone_has_finite_closure_dimension`** — line 50; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem upwardCone_has_finite_closure_dimension {S : Set α} (hS : S.Infinite) : HasFiniteClosureDimension (upwardCone S)`

- **`finite_union_of_infinite_upwardCones_generatable_in_limit`** — line 67; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem finite_union_of_infinite_upwardCones_generatable_in_limit [Nonempty α] [Countable α] {n : ℕ} (bases : Fin n → Set α) (hInfinite : ∀ i, (bases i).Infinite) : GeneratableInLimit (⋃ i, upwardCone (bases i))`

- **`finite_union_of_paper_cone_classes_generatable_in_limit`** — line 82; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem finite_union_of_paper_cone_classes_generatable_in_limit {n : ℕ} (bases : Fin n → Set ℕ) (hInfinite : ∀ i, (bases i).Infinite) : GeneratableInLimit (⋃ i, {L : Set ℕ | ∃ A : Set ℕ, L = bases i ∪ A})`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteEUCUnion.lean`

- **`finiteEUCUnionGenerator`** — line 254; `def`; **public noncomputable generator construction**.  
  Exact stripped declaration statement/body: `noncomputable def finiteEUCUnionGenerator [Nonempty α] [Countable α] {n : ℕ} (classes : Fin n → GenLimit.Generic.LanguageClass α) : GenLimit.Generic.Generator α := by classical exact fun _ xs ↦ let current := GenLimit.Generic.sequenceSample xs match c2WinningIndex classes xs with | none => Classical.choice inferInstance | some i => c2ComponentOutput (c2FrozenCore (classes i) xs) current`

- **`finite_euc_cover_implies_generatable_in_limit`** — line 445; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem finite_euc_cover_implies_generatable_in_limit [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} {n : ℕ} (classes : Fin n → GenLimit.Generic.LanguageClass α) (hcover : IsFiniteCover H classes) (hEUC : ∀ i, EventuallyUnboundedClosure (classes i)) : GeneratableInLimit H`

- **`theorem_C2_finite_eventually_unbounded_closure_cover`** — line 637; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem theorem_C2_finite_eventually_unbounded_closure_cover [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) (hcover : ∃ n : ℕ, ∃ classes : Fin n → GenLimit.Generic.LanguageClass α, IsFiniteCover H classes ∧ ∀ i, EventuallyUnboundedClosure (classes i)) : GeneratableInLimit H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/GenerationInLimitCharacterization.lean`

- **`IsFiniteCover`** — line 24; `def`; **cover predicate definition**.  
  Exact stripped declaration statement/body: `def IsFiniteCover (H : GenLimit.Generic.LanguageClass α) {n : ℕ} (classes : Fin n → GenLimit.Generic.LanguageClass α) : Prop := H = ⋃ i, classes i`

- **`finite_closure_dimension_cover_implies_generatable_in_limit`** — line 524; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem finite_closure_dimension_cover_implies_generatable_in_limit [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hcover : ∃ n : ℕ, ∃ classes : Fin n → GenLimit.Generic.LanguageClass α, IsFiniteCover H classes ∧ ∀ i, HasFiniteClosureDimension (classes i)) : GeneratableInLimit H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Hierarchy.lean`

- **`uniform_implies_nonuniform`** — line 14; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem uniform_implies_nonuniform {H : GenLimit.Generic.LanguageClass α} (h : UniformlyGeneratable H) : NonuniformlyGeneratable H`

- **`nonuniform_implies_limit`** — line 22; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem nonuniform_implies_limit {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (h : NonuniformlyGeneratable H) : GeneratableInLimit H`

- **`uniform_implies_limit`** — line 36; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem uniform_implies_limit {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (h : UniformlyGeneratable H) : GeneratableInLimit H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean`

- **`subsetConeClass`** — line 26; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def subsetConeClass (P N : Set α) : GenLimit.Generic.LanguageClass α := {L | ∃ A : Set α, A ⊆ P ∧ L = N ∪ A}`

- **`limitNonuniformSeparationClass`** — line 31; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def limitNonuniformSeparationClass (P N : Set α) : GenLimit.Generic.LanguageClass α := subsetConeClass P N ∪ ({P} : Set (Set α))`

- **`partitionLimitGenerator`** — line 64; `def`; **public noncomputable generator construction**.  
  Exact stripped declaration statement/body: `noncomputable def partitionLimitGenerator (P N : Set α) (hP : P.Infinite) (hN : N.Infinite) : GenLimit.Generic.Generator α := by classical exact fun _ xs ↦ let seen := GenLimit.Generic.sequenceSample xs if h : (↑seen : Set α) ⊆ P then freshFrom P hP seen else freshFrom N hN seen`

- **`separation_class_uus`** — line 109; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem separation_class_uus {P N : Set α} (hP : P.Infinite) (hN : N.Infinite) : UUS (limitNonuniformSeparationClass P N)`

- **`separation_class_generatable_in_limit`** — line 120; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem separation_class_generatable_in_limit {P N : Set α} (hP : P.Infinite) (hN : N.Infinite) (hDisjoint : Disjoint P N) : GeneratableInLimit (limitNonuniformSeparationClass P N)`

- **`separation_class_not_nonuniformly_generatable`** — line 332; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem separation_class_not_nonuniformly_generatable {P N : Set α} (hP : P.Infinite) (_hN : N.Infinite) (hDisjoint : Disjoint P N) : ¬NonuniformlyGeneratable (limitNonuniformSeparationClass P N)`

- **`subsetConeClass_has_closure_dimension_zero`** — line 373; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem subsetConeClass_has_closure_dimension_zero {P N : Set α} (hN : N.Infinite) : HasClosureDimension (subsetConeClass P N) 0`

- **`singleton_infinite_language_has_closure_dimension_zero`** — line 385; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem singleton_infinite_language_has_closure_dimension_zero {P : Set α} (hP : P.Infinite) : HasClosureDimension ({P} : GenLimit.Generic.LanguageClass α) 0`

- **`two_zero_closure_classes_union_not_nonuniform`** — line 397; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem two_zero_closure_classes_union_not_nonuniform {P N : Set α} (hP : P.Infinite) (hN : N.Infinite) (hDisjoint : Disjoint P N) : HasClosureDimension (subsetConeClass P N) 0 ∧ HasClosureDimension ({P} : GenLimit.Generic.LanguageClass α) 0 ∧ ¬NonuniformlyGeneratable (subsetConeClass P N ∪ ({P} : Set (Set α)))`

- **`paperPositiveIntegers`** — line 411; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def paperPositiveIntegers : Set ℤ := {z | 0 < z}`

- **`paperNonpositiveIntegers`** — line 414; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def paperNonpositiveIntegers : Set ℤ := {z | z ≤ 0}`

- **`exists_generatable_in_limit_not_nonuniformly_generatable`** — line 452; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem exists_generatable_in_limit_not_nonuniformly_generatable : ∃ H : GenLimit.Generic.LanguageClass ℤ, UUS H ∧ GeneratableInLimit H ∧ ¬NonuniformlyGeneratable H`

- **`exists_two_zero_closure_classes_union_not_nonuniform`** — line 469; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem exists_two_zero_closure_classes_union_not_nonuniform : ∃ H₁ H₂ : GenLimit.Generic.LanguageClass ℤ, HasClosureDimension H₁ 0 ∧ HasClosureDimension H₂ 0 ∧ ¬NonuniformlyGeneratable (H₁ ∪ H₂)`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/NonuniformCharacterization.lean`

- **`IsNondecreasingCover`** — line 30; `def`; **cover predicate definition**.  
  Exact stripped declaration statement/body: `def IsNondecreasingCover (H : GenLimit.Generic.LanguageClass α) (classes : ℕ → GenLimit.Generic.LanguageClass α) : Prop := Monotone classes ∧ H = ⋃ n, classes n`

- **`nonuniform_characterization_necessity`** — line 36; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem nonuniform_characterization_necessity [Countable α] {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) (hNonuniform : NonuniformlyGeneratable H) : ∃ classes : ℕ → GenLimit.Generic.LanguageClass α, IsNondecreasingCover H classes ∧ ∀ n, UniformlyGeneratable (classes n)`

- **`nonuniform_characterization_sufficiency`** — line 103; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem nonuniform_characterization_sufficiency [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) {classes : ℕ → GenLimit.Generic.LanguageClass α} (hcover : IsNondecreasingCover H classes) (hUniform : ∀ n, UniformlyGeneratable (classes n)) : NonuniformlyGeneratable H`

- **`nonuniform_generatability_iff_nondecreasing_finite_closure_cover`** — line 167; `theorem`; **main characterization theorem**.  
  Exact stripped declaration statement/body: `theorem nonuniform_generatability_iff_nondecreasing_finite_closure_cover [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) : NonuniformlyGeneratable H ↔ ∃ classes : ℕ → GenLimit.Generic.LanguageClass α, IsNondecreasingCover H classes ∧ ∀ n, HasFiniteClosureDimension (classes n)`

- **`finite_language_class_has_finite_closure_dimension`** — line 191; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem finite_language_class_has_finite_closure_dimension {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite) : HasFiniteClosureDimension H`

- **`countable_classes_are_nonuniformly_generatable`** — line 220; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem countable_classes_are_nonuniformly_generatable [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hCountable : H.Countable) : NonuniformlyGeneratable H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean`

- **`VCShatters`** — line 34; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def VCShatters (H : GenLimit.Generic.LanguageClass α) {d : ℕ} (xs : Fin d → α) : Prop := ∀ labels : Fin d → Bool, ∃ L, L ∈ H ∧ ∀ i, (xs i ∈ L ↔ labels i = true)`

- **`HasFiniteVCDimension`** — line 41; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasFiniteVCDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ d : ℕ, ∀ xs : Fin (d + 1) → α, ¬VCShatters H xs`

- **`HasInfiniteVCDimension`** — line 46; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasInfiniteVCDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ d : ℕ, ∃ xs : Fin d → α, VCShatters H xs`

- **`PACLearnableViaVC`** — line 52; `def`; **direct proxy alias (dimension finiteness)**.  
  Exact stripped declaration statement/body: `def PACLearnableViaVC (H : GenLimit.Generic.LanguageClass α) : Prop := HasFiniteVCDimension H`

- **`PairShattered`** — line 65; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def PairShattered (H : GenLimit.Generic.LanguageClass α) (x y : α) : Prop := ∀ bx byLabel : Bool, ∃ L, L ∈ H ∧ (x ∈ L ↔ bx = true) ∧ (y ∈ L ↔ byLabel = true)`

- **`LittlestoneTree`** — line 110; `inductive`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `inductive LittlestoneTree (α : Type*) : ℕ → Type _ | leaf : LittlestoneTree α 0 | node {d : ℕ} (x : α) (left right : LittlestoneTree α d) : LittlestoneTree α (d + 1)`

- **`labelClass`** — line 117; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def labelClass (H : GenLimit.Generic.LanguageClass α) (x : α) (b : Bool) : GenLimit.Generic.LanguageClass α := {L | L ∈ H ∧ (x ∈ L ↔ b = true)}`

- **`LittlestoneShattered`** — line 124; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def LittlestoneShattered : {d : ℕ} → LittlestoneTree α d → GenLimit.Generic.LanguageClass α → Prop | 0, .leaf, H => H.Nonempty | _ + 1, .node x left right, H => LittlestoneShattered left (labelClass H x false) ∧ LittlestoneShattered right (labelClass H x true)`

- **`HasShatteredLittlestoneTree`** — line 133; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasShatteredLittlestoneTree (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop := ∃ T : LittlestoneTree α d, LittlestoneShattered T H`

- **`HasFiniteLittlestoneDimension`** — line 138; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasFiniteLittlestoneDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ d : ℕ, ¬HasShatteredLittlestoneTree H (d + 1)`

- **`HasInfiniteLittlestoneDimension`** — line 143; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasInfiniteLittlestoneDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ d : ℕ, HasShatteredLittlestoneTree H d`

- **`OnlineLearnableViaLittlestone`** — line 150; `def`; **direct proxy alias (dimension finiteness)**.  
  Exact stripped declaration statement/body: `def OnlineLearnableViaLittlestone (H : GenLimit.Generic.LanguageClass α) : Prop := HasFiniteLittlestoneDimension H`

- **`finiteAugmentationClass`** — line 230; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def finiteAugmentationClass : GenLimit.Generic.LanguageClass ℤ := {L | ∃ A : Set ℤ, A ⊆ paperPositiveIntegers ∧ A.Finite ∧ L = paperNonpositiveIntegers ∪ A}`

- **`finiteAugmentationClass_countable`** — line 234; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem finiteAugmentationClass_countable : finiteAugmentationClass.Countable`

- **`finiteAugmentationClass_uus_and_uniform`** — line 246; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem finiteAugmentationClass_uus_and_uniform : UUS finiteAugmentationClass ∧ UniformlyGeneratable finiteAugmentationClass`

- **`finiteAugmentationClass_infiniteVC`** — line 270; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem finiteAugmentationClass_infiniteVC : HasInfiniteVCDimension finiteAugmentationClass`

- **`theorem_4_1_i_combinatorial_core`** — line 306; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem theorem_4_1_i_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass ℤ, H.Countable ∧ UniformlyGeneratable H ∧ ¬PACLearnableViaVC H`

- **`blockSeparationClass_onlineViaLittlestone`** — line 366; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem blockSeparationClass_onlineViaLittlestone : OnlineLearnableViaLittlestone blockSeparationClass`

- **`blockSeparationClass_not_uniform`** — line 450; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem blockSeparationClass_not_uniform : ¬UniformlyGeneratable blockSeparationClass`

- **`theorem_4_1_ii_combinatorial_core`** — line 457; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem theorem_4_1_ii_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass BlockUniverse, H.Countable ∧ OnlineLearnableViaLittlestone H ∧ ¬UniformlyGeneratable H`

- **`singletonSpikeLanguage`** — line 467; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def singletonSpikeLanguage (a : ℕ) : Set ℤ := paperNonpositiveIntegers ∪ {positiveIntegerPoint a}`

- **`singletonSpikeClass`** — line 472; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def singletonSpikeClass : GenLimit.Generic.LanguageClass ℤ := Set.range singletonSpikeLanguage`

- **`singletonSpikeClass_countable`** — line 475; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem singletonSpikeClass_countable : singletonSpikeClass.Countable`

- **`singletonSpikeClass_uus_and_uniform`** — line 479; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem singletonSpikeClass_uus_and_uniform : UUS singletonSpikeClass ∧ UniformlyGeneratable singletonSpikeClass`

- **`singletonSpikeClass_onlineViaLittlestone`** — line 507; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem singletonSpikeClass_onlineViaLittlestone : OnlineLearnableViaLittlestone singletonSpikeClass`

- **`theorem_4_1_iii_combinatorial_core`** — line 530; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem theorem_4_1_iii_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass ℤ, H.Countable ∧ OnlineLearnableViaLittlestone H ∧ UniformlyGeneratable H`

- **`thresholdLanguage`** — line 541; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def thresholdLanguage (a : ℕ) : Set ℕ := {x | a ≤ x}`

- **`thresholdClass`** — line 543; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def thresholdClass : GenLimit.Generic.LanguageClass ℕ := Set.range thresholdLanguage`

- **`thresholdClass_countable`** — line 550; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdClass_countable : thresholdClass.Countable`

- **`thresholdLanguage_infinite`** — line 553; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdLanguage_infinite (a : ℕ) : (thresholdLanguage a).Infinite`

- **`thresholdClass_uus`** — line 561; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdClass_uus : UUS thresholdClass`

- **`thresholdClass_uniform`** — line 566; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdClass_uniform : UniformlyGeneratable thresholdClass`

- **`thresholdClass_pacViaVC`** — line 604; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdClass_pacViaVC : PACLearnableViaVC thresholdClass`

- **`thresholdClass_infiniteLittlestone`** — line 677; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdClass_infiniteLittlestone : HasInfiniteLittlestoneDimension thresholdClass`

- **`thresholdClass_not_onlineViaLittlestone`** — line 689; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdClass_not_onlineViaLittlestone : ¬OnlineLearnableViaLittlestone thresholdClass`

- **`theorem_4_1_v_combinatorial_core`** — line 696; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem theorem_4_1_v_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass ℕ, H.Countable ∧ PACLearnableViaVC H ∧ UniformlyGeneratable H ∧ ¬OnlineLearnableViaLittlestone H`

- **`liftLeftLanguage`** — line 708; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def liftLeftLanguage (L : Set α) : Set (α ⊕ β) := {z | match z with | Sum.inl x => x ∈ L | Sum.inr _ => False}`

- **`liftRightLanguage`** — line 714; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def liftRightLanguage (L : Set β) : Set (α ⊕ β) := {z | match z with | Sum.inl _ => False | Sum.inr y => y ∈ L}`

- **`liftLeftClass`** — line 719; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def liftLeftClass (H : GenLimit.Generic.LanguageClass α) : GenLimit.Generic.LanguageClass (α ⊕ β) := liftLeftLanguage '' H`

- **`liftRightClass`** — line 723; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def liftRightClass (H : GenLimit.Generic.LanguageClass β) : GenLimit.Generic.LanguageClass (α ⊕ β) := liftRightLanguage '' H`

- **`ThresholdBlockUniverse`** — line 727; `abbrev`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `abbrev ThresholdBlockUniverse := ℕ ⊕ BlockUniverse`

- **`thresholdBlockClass`** — line 733; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def thresholdBlockClass : GenLimit.Generic.LanguageClass ThresholdBlockUniverse := liftLeftClass thresholdClass ∪ liftRightClass blockSeparationClass`

- **`thresholdBlockClass_countable`** — line 738; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdBlockClass_countable : thresholdBlockClass.Countable`

- **`thresholdBlockClass_uus`** — line 743; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdBlockClass_uus : UUS thresholdBlockClass`

- **`thresholdBlockClass_infiniteClosure`** — line 831; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdBlockClass_infiniteClosure : HasInfiniteClosureDimension thresholdBlockClass`

- **`thresholdBlockClass_not_uniform`** — line 857; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdBlockClass_not_uniform : ¬UniformlyGeneratable thresholdBlockClass`

- **`thresholdBlockClass_pacViaVC`** — line 1003; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdBlockClass_pacViaVC : PACLearnableViaVC thresholdBlockClass`

- **`thresholdBlockClass_infiniteLittlestone`** — line 1109; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdBlockClass_infiniteLittlestone : HasInfiniteLittlestoneDimension thresholdBlockClass`

- **`thresholdBlockClass_not_online`** — line 1120; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem thresholdBlockClass_not_online : ¬OnlineLearnableViaLittlestone thresholdBlockClass`

- **`theorem_4_1_iv_combinatorial_core`** — line 1127; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem theorem_4_1_iv_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass ThresholdBlockUniverse, H.Countable ∧ PACLearnableViaVC H ∧ ¬OnlineLearnableViaLittlestone H ∧ ¬UniformlyGeneratable H`

- **`cofiniteClass`** — line 1140; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def cofiniteClass : GenLimit.Generic.LanguageClass ℕ := {L | ∃ A : Set ℕ, A.Finite ∧ L = Aᶜ}`

- **`cofiniteClass_countable`** — line 1143; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem cofiniteClass_countable : cofiniteClass.Countable`

- **`cofiniteClass_uus`** — line 1153; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem cofiniteClass_uus : UUS cofiniteClass`

- **`cofiniteClass_infiniteVC`** — line 1159; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem cofiniteClass_infiniteVC : HasInfiniteVCDimension cofiniteClass`

- **`commonCore_cofiniteClass_eq`** — line 1191; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem commonCore_cofiniteClass_eq (S : Finset ℕ) : commonCore cofiniteClass S = (↑S : Set ℕ)`

- **`cofiniteClass_infiniteClosure`** — line 1208; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem cofiniteClass_infiniteClosure : HasInfiniteClosureDimension cofiniteClass`

- **`cofiniteClass_not_uniform`** — line 1219; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem cofiniteClass_not_uniform : ¬UniformlyGeneratable cofiniteClass`

- **`cofiniteClass_not_pacViaVC`** — line 1224; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem cofiniteClass_not_pacViaVC : ¬PACLearnableViaVC cofiniteClass`

- **`theorem_4_1_vi_combinatorial_core`** — line 1230; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem theorem_4_1_vi_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass ℕ, H.Countable ∧ ¬PACLearnableViaVC H ∧ ¬UniformlyGeneratable H`

- **`theorem_4_1_combinatorial_core`** — line 1245; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem theorem_4_1_combinatorial_core : (∃ H : GenLimit.Generic.LanguageClass ℤ, H.Countable ∧ UniformlyGeneratable H ∧ ¬PACLearnableViaVC H) ∧ (∃ H : GenLimit.Generic.LanguageClass BlockUniverse, H.Countable ∧ OnlineLearnableViaLittlestone H ∧ ¬UniformlyGeneratable H) ∧ (∃ H : GenLimit.Generic.LanguageClass ℤ, H.Countable ∧ OnlineLearnableViaLittlestone H ∧ UniformlyGeneratable H) ∧ (∃ H : GenLimit.Generic.LanguageClass ThresholdBlockUniverse, H.Countable ∧ PACLearnableViaVC H ∧ ¬OnlineLearnableViaLittlestone H ∧ ¬UniformlyGeneratable H) ∧ (∃ H : GenLimit.Generic.LanguageClass ℕ, H.Countable ∧ PACLearnableViaVC H ∧ UniformlyGeneratable H ∧ ¬OnlineLearnableViaLittlestone H) ∧ (∃ H : GenLimit.Generic.LanguageClass ℕ, H.Countable ∧ ¬PACLearnableViaVC H ∧ ¬UniformlyGeneratable H)`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean`

- **`IsPromptedClosureWitness`** — line 15; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def IsPromptedClosureWitness (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Prop := (promptedVersionSpace H S y).Nonempty ∧ (promptedCommonCore H S y).Finite`

- **`PromptedClosureDimensionAtMost`** — line 21; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def PromptedClosureDimensionAtMost (H : MulticlassHypothesisClass α ι) (d : ℕ) : Prop := ∀ y : ι, ∀ S : Finset α, d < S.card → (promptedVersionSpace H S y).Nonempty → (promptedCommonCore H S y).Infinite`

- **`HasPromptedClosureDimension`** — line 28; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasPromptedClosureDimension (H : MulticlassHypothesisClass α ι) (d : ℕ) : Prop := PromptedClosureDimensionAtMost H d ∧ (d = 0 ∨ ∃ y : ι, ∃ S : Finset α, S.card = d ∧ IsPromptedClosureWitness H S y)`

- **`HasFinitePromptedClosureDimension`** — line 36; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasFinitePromptedClosureDimension (H : MulticlassHypothesisClass α ι) : Prop := ∃ d : ℕ, HasPromptedClosureDimension H d`

- **`HasInfinitePromptedClosureDimension`** — line 41; `def`; **dimension/shattering/EUC definition**.  
  Exact stripped declaration statement/body: `def HasInfinitePromptedClosureDimension (H : MulticlassHypothesisClass α ι) : Prop := ∀ d : ℕ, ∃ y : ι, ∃ S : Finset α, d ≤ S.card ∧ IsPromptedClosureWitness H S y`

- **`finite_prompted_closure_dimension_iff_not_infinite`** — line 68; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem finite_prompted_closure_dimension_iff_not_infinite {H : MulticlassHypothesisClass α ι} : HasFinitePromptedClosureDimension H ↔ ¬ HasInfinitePromptedClosureDimension H`

- **`promptedSequenceSample`** — line 120; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `noncomputable def promptedSequenceSample {t : ℕ} (history : Fin t → PromptedObservation α ι) (y : ι) : Finset α := by classical exact (Finset.univ.filter (fun i ↦ (history i).2.1 = y)).image (fun i ↦ (history i).1)`

- **`promptedObservedSample`** — line 128; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `noncomputable def promptedObservedSample {t : ℕ} (history : Fin t → PromptedObservation α ι) : Finset α := GenLimit.Generic.sequenceSample (fun i ↦ (history i).1)`

- **`promptedClosureGenerator`** — line 168; `def`; **public noncomputable generator construction**.  
  Exact stripped declaration statement/body: `noncomputable def promptedClosureGenerator [Nonempty α] (H : MulticlassHypothesisClass α ι) (d : ℕ) (hPC : PromptedClosureDimensionAtMost H d) : PromptedGenerator α ι := by classical exact fun t history ↦ if ht : 0 < t then let last : Fin t := ⟨t - 1, Nat.sub_lt (by omega) (by omega)⟩ let y := (history last).2.2 let S := promptedSequenceSample history y let observed := promptedObservedSample history if hd : d < S.card then if hVS : (promptedVersionSpace H S y).Nonempty then Classical.choose (prompted_core_diff_observed_infinite hPC S observed y hd hVS).nonempty else Classical.choice inferInstance else Classical.choice inferInstance else Classical.choice inferInstance`

- **`prompted_closure_dimension_sufficiency`** — line 214; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_closure_dimension_sufficiency [Nonempty α] [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (_hPUUS : PUUS H) {d : ℕ} (hPC : HasPromptedClosureDimension H d) : ∃ gen : PromptedGenerator α ι, IsPromptedUniformGeneratorAt gen H (d + 1)`

- **`finite_prompted_closure_dimension_implies_uniform`** — line 277; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem finite_prompted_closure_dimension_implies_uniform [Nonempty α] [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) (hfinite : HasFinitePromptedClosureDimension H) : PromptedUniformlyGeneratable H`

- **`prompted_uniform_threshold_mono`** — line 338; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_uniform_threshold_mono {gen : PromptedGenerator α ι} {H : MulticlassHypothesisClass α ι} {d n : ℕ} (hdn : d ≤ n) (hgen : IsPromptedUniformGeneratorAt gen H d) : IsPromptedUniformGeneratorAt gen H n`

- **`prompted_closure_dimension_necessity`** — line 353; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_closure_dimension_necessity [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) (hPC : HasInfinitePromptedClosureDimension H) : ¬ PromptedUniformlyGeneratable H`

- **`prompted_uniform_generatability_iff_finite_prompted_closure_dimension`** — line 486; `theorem`; **main characterization theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_uniform_generatability_iff_finite_prompted_closure_dimension [Nonempty α] [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) : PromptedUniformlyGeneratable H ↔ HasFinitePromptedClosureDimension H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean`

- **`MulticlassHypothesis`** — line 19; `abbrev`; **core semantic definition**.  
  Exact stripped declaration statement/body: `abbrev MulticlassHypothesis (α ι : Type*) := α → ι`

- **`MulticlassHypothesisClass`** — line 21; `abbrev`; **core semantic definition**.  
  Exact stripped declaration statement/body: `abbrev MulticlassHypothesisClass (α ι : Type*) := Set (MulticlassHypothesis α ι)`

- **`promptSupport`** — line 25; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def promptSupport (h : MulticlassHypothesis α ι) (y : ι) : Set α := {x | h x = y}`

- **`PUUS`** — line 29; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def PUUS (H : MulticlassHypothesisClass α ι) : Prop := ∀ h, h ∈ H → ∀ y, (promptSupport h y).Infinite`

- **`PromptedObservation`** — line 34; `abbrev`; **core semantic definition**.  
  Exact stripped declaration statement/body: `abbrev PromptedObservation (α ι : Type*) := α × ι × ι`

- **`PromptedGenerator`** — line 39; `abbrev`; **core semantic definition**.  
  Exact stripped declaration statement/body: `abbrev PromptedGenerator (α ι : Type*) := ∀ t : ℕ, (Fin t → PromptedObservation α ι) → α`

- **`promptedHistory`** — line 43; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def promptedHistory (h : MulticlassHypothesis α ι) (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι) (t : ℕ) : Fin t → PromptedObservation α ι := fun i ↦ (xs i, h (xs i), ys i)`

- **`promptedSample`** — line 52; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `noncomputable def promptedSample (h : MulticlassHypothesis α ι) (xs : GenLimit.Generic.Stream α) (y : ι) (t : ℕ) : Finset α := by classical exact (GenLimit.Generic.sample xs t).filter (fun x ↦ h x = y)`

- **`PromptedCorrectAt`** — line 79; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def PromptedCorrectAt (gen : PromptedGenerator α ι) (h : MulticlassHypothesis α ι) (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι) (s : ℕ) : Prop := ∀ _hs : 0 < s, gen s (promptedHistory h xs ys s) ∈ promptSupport h (ys (s - 1)) \ (↑(GenLimit.Generic.sample xs s) : Set α)`

- **`IsPromptedUniformGeneratorAt`** — line 94; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def IsPromptedUniformGeneratorAt (gen : PromptedGenerator α ι) (H : MulticlassHypothesisClass α ι) (d : ℕ) : Prop := ∀ h, h ∈ H → ∀ xs : GenLimit.Generic.Stream α, ∀ ys : GenLimit.Generic.Stream ι, ∀ yStar : ι, ∀ t, (promptedSample h xs yStar t).card = d → ∀ s, t ≤ s → ∀ _hs : 0 < s, ys (s - 1) = yStar → PromptedCorrectAt gen h xs ys s`

- **`PromptedUniformlyGeneratable`** — line 106; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def PromptedUniformlyGeneratable (H : MulticlassHypothesisClass α ι) : Prop := ∃ gen : PromptedGenerator α ι, ∃ d : ℕ, IsPromptedUniformGeneratorAt gen H d`

- **`IsPromptedNonuniformGenerator`** — line 113; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def IsPromptedNonuniformGenerator (gen : PromptedGenerator α ι) (H : MulticlassHypothesisClass α ι) : Prop := ∀ h, h ∈ H → ∃ d : ℕ, ∀ xs : GenLimit.Generic.Stream α, ∀ ys : GenLimit.Generic.Stream ι, ∀ yStar : ι, ∀ t, (promptedSample h xs yStar t).card = d → ∀ s, t ≤ s → ∀ _hs : 0 < s, ys (s - 1) = yStar → PromptedCorrectAt gen h xs ys s`

- **`PromptedNonuniformlyGeneratable`** — line 125; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def PromptedNonuniformlyGeneratable (H : MulticlassHypothesisClass α ι) : Prop := ∃ gen : PromptedGenerator α ι, IsPromptedNonuniformGenerator gen H`

- **`PromptSupportPresented`** — line 131; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def PromptSupportPresented (h : MulticlassHypothesis α ι) (xs : GenLimit.Generic.Stream α) (y : ι) : Prop := promptSupport h y ⊆ Set.range xs`

- **`IsPromptedLimitGenerator`** — line 137; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def IsPromptedLimitGenerator (gen : PromptedGenerator α ι) (H : MulticlassHypothesisClass α ι) : Prop := ∀ h, h ∈ H → ∀ xs : GenLimit.Generic.Stream α, ∀ ys : GenLimit.Generic.Stream ι, ∀ yStar : ι, PromptSupportPresented h xs yStar → ∃ t, ∀ s, t ≤ s → ∀ _hs : 0 < s, ys (s - 1) = yStar → PromptedCorrectAt gen h xs ys s`

- **`PromptedGeneratableInLimit`** — line 149; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def PromptedGeneratableInLimit (H : MulticlassHypothesisClass α ι) : Prop := ∃ gen : PromptedGenerator α ι, IsPromptedLimitGenerator gen H`

- **`promptedVersionSpace`** — line 154; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def promptedVersionSpace (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Set (MulticlassHypothesis α ι) := {h | h ∈ H ∧ ∀ x ∈ S, h x = y}`

- **`promptedCommonCore`** — line 160; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `def promptedCommonCore (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Set α := {x | ∀ h, h ∈ promptedVersionSpace H S y → h x = y}`

- **`promptedClosure`** — line 165; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `noncomputable def promptedClosure (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Option (Set α) := by classical exact if (promptedVersionSpace H S y).Nonempty then some (promptedCommonCore H S y) else none`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean`

- **`PositivePrompt`** — line 18; `abbrev`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `abbrev PositivePrompt := {n : ℕ // 0 < n}`

- **`firstPositivePrompt`** — line 20; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def firstPositivePrompt : PositivePrompt := ⟨1, by omega⟩`

- **`PromptSeparationUniverse`** — line 24; `abbrev`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `abbrev PromptSeparationUniverse := PositivePrompt × Option Bool × ℕ`

- **`promptSeparationLeft`** — line 27; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def promptSeparationLeft : MulticlassHypothesis PromptSeparationUniverse PositivePrompt := fun x ↦ match x.2.1 with | none => if x.2.2 < x.1.1 then x.1 else firstPositivePrompt | some false => x.1 | some true => firstPositivePrompt`

- **`promptSeparationRight`** — line 36; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def promptSeparationRight : MulticlassHypothesis PromptSeparationUniverse PositivePrompt := fun x ↦ match x.2.1 with | none => if x.2.2 < x.1.1 then x.1 else firstPositivePrompt | some false => firstPositivePrompt | some true => x.1`

- **`promptSeparationClass`** — line 45; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `def promptSeparationClass : MulticlassHypothesisClass PromptSeparationUniverse PositivePrompt := {promptSeparationLeft, promptSeparationRight}`

- **`promptBlock`** — line 50; `def`; **explicit construction or helper definition**.  
  Exact stripped declaration statement/body: `noncomputable def promptBlock (p : PositivePrompt) : Finset PromptSeparationUniverse := by classical exact (Finset.range p.1).image (fun k ↦ (p, none, k))`

- **`promptSeparationClass_finite`** — line 81; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem promptSeparationClass_finite : promptSeparationClass.Finite`

- **`promptSeparationClass_puus`** — line 85; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem promptSeparationClass_puus : PUUS promptSeparationClass`

- **`promptSeparationClass_infinite_prompted_closure_dimension`** — line 161; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem promptSeparationClass_infinite_prompted_closure_dimension : HasInfinitePromptedClosureDimension promptSeparationClass`

- **`exists_finite_prompt_class_not_uniformly_generatable`** — line 180; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem exists_finite_prompt_class_not_uniformly_generatable : ∃ H : MulticlassHypothesisClass PromptSeparationUniverse PositivePrompt, H.Finite ∧ PUUS H ∧ ¬PromptedUniformlyGeneratable H`

- **`promptSeparationClass_not_nonuniformly_generatable`** — line 191; `theorem`; **example or separation theorem**.  
  Exact stripped declaration statement/body: `theorem promptSeparationClass_not_nonuniformly_generatable : ¬PromptedNonuniformlyGeneratable promptSeparationClass`

- **`exists_finite_prompt_class_not_nonuniformly_generatable`** — line 230; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem exists_finite_prompt_class_not_nonuniformly_generatable : ∃ H : MulticlassHypothesisClass PromptSeparationUniverse PositivePrompt, H.Finite ∧ PUUS H ∧ ¬PromptedNonuniformlyGeneratable H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean`

- **`IsPromptedNondecreasingCover`** — line 19; `def`; **cover predicate definition**.  
  Exact stripped declaration statement/body: `def IsPromptedNondecreasingCover (H : MulticlassHypothesisClass α ι) (classes : ℕ → MulticlassHypothesisClass α ι) : Prop := Monotone classes ∧ H = ⋃ n, classes n`

- **`prompted_nonuniform_characterization_necessity`** — line 25; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_nonuniform_characterization_necessity [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (_hPUUS : PUUS H) (hNonuniform : PromptedNonuniformlyGeneratable H) : ∃ classes : ℕ → MulticlassHypothesisClass α ι, IsPromptedNondecreasingCover H classes ∧ ∀ n, PromptedUniformlyGeneratable (classes n)`

- **`prompted_nonuniform_characterization_sufficiency`** — line 99; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_nonuniform_characterization_sufficiency [Nonempty α] [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (_hPUUS : PUUS H) {classes : ℕ → MulticlassHypothesisClass α ι} (hcover : IsPromptedNondecreasingCover H classes) (hUniform : ∀ n, PromptedUniformlyGeneratable (classes n)) : PromptedNonuniformlyGeneratable H`

- **`prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover`** — line 183; `theorem`; **main characterization theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover [Nonempty α] [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) : PromptedNonuniformlyGeneratable H ↔ ∃ classes : ℕ → MulticlassHypothesisClass α ι, IsPromptedNondecreasingCover H classes ∧ ∀ n, HasFinitePromptedClosureDimension (classes n)`

- **`prompted_uniform_implies_nonuniform`** — line 253; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_uniform_implies_nonuniform {H : MulticlassHypothesisClass α ι} : PromptedUniformlyGeneratable H → PromptedNonuniformlyGeneratable H`

- **`prompted_nonuniform_implies_limit`** — line 260; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_nonuniform_implies_limit {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) : PromptedNonuniformlyGeneratable H → PromptedGeneratableInLimit H`

- **`prompted_uniform_implies_limit`** — line 275; `theorem`; **substantive implication/characterization theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_uniform_implies_limit {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) : PromptedUniformlyGeneratable H → PromptedGeneratableInLimit H`

- **`finite_prompt_class_has_finite_prompted_closure_dimension`** — line 286; `theorem`; **substantive construction/property theorem**.  
  Exact stripped declaration statement/body: `theorem finite_prompt_class_has_finite_prompted_closure_dimension [Finite ι] {H : MulticlassHypothesisClass α ι} (hH : H.Finite) : HasFinitePromptedClosureDimension H`

- **`finite_prompt_classes_are_uniformly_generatable`** — line 322; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem finite_prompt_classes_are_uniformly_generatable [Nonempty α] [Countable α] [Countable ι] [Finite ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) (hFinite : H.Finite) : PromptedUniformlyGeneratable H`

- **`countable_prompt_classes_are_nonuniformly_generatable`** — line 332; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem countable_prompt_classes_are_nonuniformly_generatable [Nonempty α] [Countable α] [Countable ι] [Finite ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) (hCountable : H.Countable) : PromptedNonuniformlyGeneratable H`

- **`countable_prompt_classes_are_generatable_in_limit`** — line 376; `theorem`; **wrapper or existential package**.  
  Exact stripped declaration statement/body: `theorem countable_prompt_classes_are_generatable_in_limit [Nonempty α] [Countable α] [Countable ι] [Finite ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) (hCountable : H.Countable) : PromptedGeneratableInLimit H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean`

- **`uniform_threshold_mono`** — line 29; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem uniform_threshold_mono {gen : GenLimit.Generic.Generator α} {H : GenLimit.Generic.LanguageClass α} {d n : ℕ} (hdn : d ≤ n) (hgen : IsUniformGeneratorAt gen H d) : IsUniformGeneratorAt gen H n`

- **`uniformGenerationSampleComplexity`** — line 42; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `noncomputable def uniformGenerationSampleComplexity (gen : GenLimit.Generic.Generator α) (H : GenLimit.Generic.LanguageClass α) : WithTop ℕ := by classical exact if h : ∃ d : ℕ, IsUniformGeneratorAt gen H d then (Nat.find h : WithTop ℕ) else ⊤`

- **`uniformGenerationSampleComplexity_eq_top_iff`** — line 52; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem uniformGenerationSampleComplexity_eq_top_iff {gen : GenLimit.Generic.Generator α} {H : GenLimit.Generic.LanguageClass α} : uniformGenerationSampleComplexity gen H = ⊤ ↔ ¬ ∃ d : ℕ, IsUniformGeneratorAt gen H d`

- **`uniformGenerationSampleComplexity_lt_top_iff`** — line 62; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem uniformGenerationSampleComplexity_lt_top_iff {gen : GenLimit.Generic.Generator α} {H : GenLimit.Generic.LanguageClass α} : uniformGenerationSampleComplexity gen H < ⊤ ↔ ∃ d : ℕ, IsUniformGeneratorAt gen H d`

- **`uniformGenerationSampleComplexity_le_coe_iff`** — line 72; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem uniformGenerationSampleComplexity_le_coe_iff {gen : GenLimit.Generic.Generator α} {H : GenLimit.Generic.LanguageClass α} {d : ℕ} : uniformGenerationSampleComplexity gen H ≤ (d : WithTop ℕ) ↔ IsUniformGeneratorAt gen H d`

- **`uniformGenerationSampleComplexity_eq_coe_iff`** — line 94; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem uniformGenerationSampleComplexity_eq_coe_iff {gen : GenLimit.Generic.Generator α} {H : GenLimit.Generic.LanguageClass α} {d : ℕ} : uniformGenerationSampleComplexity gen H = (d : WithTop ℕ) ↔ IsUniformGeneratorAt gen H d ∧ ∀ e : ℕ, e < d → ¬ IsUniformGeneratorAt gen H e`

- **`uniformlyGeneratable_iff_exists_sampleComplexity_lt_top`** — line 122; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem uniformlyGeneratable_iff_exists_sampleComplexity_lt_top {H : GenLimit.Generic.LanguageClass α} : UniformlyGeneratable H ↔ ∃ gen : GenLimit.Generic.Generator α, uniformGenerationSampleComplexity gen H < ⊤`

- **`optimalUniformGenerationSampleComplexity`** — line 139; `def`; **core semantic definition**.  
  Exact stripped declaration statement/body: `noncomputable def optimalUniformGenerationSampleComplexity (H : GenLimit.Generic.LanguageClass α) : WithTop ℕ := by classical exact if h : ∃ d : ℕ, ∃ gen : GenLimit.Generic.Generator α, IsUniformGeneratorAt gen H d then (Nat.find h : WithTop ℕ) else ⊤`

- **`optimalUniformGenerationSampleComplexity_eq_top_iff`** — line 150; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem optimalUniformGenerationSampleComplexity_eq_top_iff {H : GenLimit.Generic.LanguageClass α} : optimalUniformGenerationSampleComplexity H = ⊤ ↔ ¬ UniformlyGeneratable H`

- **`optimalUniformGenerationSampleComplexity_le_coe_iff`** — line 174; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem optimalUniformGenerationSampleComplexity_le_coe_iff {H : GenLimit.Generic.LanguageClass α} {d : ℕ} : optimalUniformGenerationSampleComplexity H ≤ (d : WithTop ℕ) ↔ ∃ gen : GenLimit.Generic.Generator α, IsUniformGeneratorAt gen H d`

- **`closure_dimension_le_uniform_threshold`** — line 203; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem closure_dimension_le_uniform_threshold [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) {gen : GenLimit.Generic.Generator α} {e : ℕ} (hgen : IsUniformGeneratorAt gen H e) : d ≤ e`

- **`closure_dimension_le_uniformGenerationSampleComplexity`** — line 219; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem closure_dimension_le_uniformGenerationSampleComplexity [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) (gen : GenLimit.Generic.Generator α) : (d : WithTop ℕ) ≤ uniformGenerationSampleComplexity gen H`

- **`closureGenerator_uniformGenerationSampleComplexity_le`** — line 235; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem closureGenerator_uniformGenerationSampleComplexity_le [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : uniformGenerationSampleComplexity (closureGenerator H d hC.1) H ≤ ((d + 1 : ℕ) : WithTop ℕ)`

- **`closure_dimension_le_optimalUniformGenerationSampleComplexity`** — line 246; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem closure_dimension_le_optimalUniformGenerationSampleComplexity [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : (d : WithTop ℕ) ≤ optimalUniformGenerationSampleComplexity H`

- **`optimalUniformGenerationSampleComplexity_le_closureDimension_succ`** — line 264; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem optimalUniformGenerationSampleComplexity_le_closureDimension_succ [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : optimalUniformGenerationSampleComplexity H ≤ ((d + 1 : ℕ) : WithTop ℕ)`

- **`optimal_uniform_generation_sample_complexity_bounds`** — line 281; `theorem`; **quantitative theorem**.  
  Exact stripped declaration statement/body: `theorem optimal_uniform_generation_sample_complexity_bounds [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : (d : WithTop ℕ) ≤ optimalUniformGenerationSampleComplexity H ∧ optimalUniformGenerationSampleComplexity H ≤ ((d + 1 : ℕ) : WithTop ℕ)`

## Appendix B. Public supporting-declaration ledger

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean`

- **`closure_witness_mono`** — line 55; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem closure_witness_mono {H : GenLimit.Generic.LanguageClass α} {S T : Finset α} (hST : S ⊆ T) (hT : IsClosureWitness H T) : IsClosureWitness H S`

- **`exists_closure_witness_card_eq`** — line 69; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem exists_closure_witness_card_eq {H : GenLimit.Generic.LanguageClass α} (hC : HasInfiniteClosureDimension H) (d : ℕ) : ∃ S : Finset α, S.card = d ∧ IsClosureWitness H S`

- **`core_diff_sample_infinite`** — line 240; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem core_diff_sample_infinite {H : GenLimit.Generic.LanguageClass α} {d : ℕ} (hC : ClosureDimensionAtMost H d) (S : Finset α) (hd : d < S.card) (hVS : (versionSpace H S).Nonempty) : (commonCore H S \ (↑S : Set α)).Infinite`

- **`closureGenerator_spec`** — line 264; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem closureGenerator_spec [Nonempty α] {H : GenLimit.Generic.LanguageClass α} {d t : ℕ} (hC : ClosureDimensionAtMost H d) (xs : Fin t → α) (hd : d < (GenLimit.Generic.sequenceSample xs).card) (hVS : (versionSpace H (GenLimit.Generic.sequenceSample xs)).Nonempty) : closureGenerator H d hC t xs ∈ commonCore H (GenLimit.Generic.sequenceSample xs) \ (↑(GenLimit.Generic.sequenceSample xs) : Set α)`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean`

- **`countableUnionTail_mem`** — line 51; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem countableUnionTail_mem (n k : ℕ) : (Sum.inr (n, k) : CountableUnionUniverse) ∈ countableUnionTail n`

- **`countableUnionAnchor_mem_zero`** — line 56; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem countableUnionAnchor_mem_zero (n : ℕ) : countableUnionAnchor n ∈ countableUnionCore 0`

- **`countableUnionAnchor_mem_succ`** — line 60; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem countableUnionAnchor_mem_succ (n : ℕ) : countableUnionAnchor n ∈ countableUnionCore (n + 1)`

- **`countableUnionTail_mem_succ`** — line 64; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem countableUnionTail_mem_succ (n k : ℕ) : (Sum.inr (n, k) : CountableUnionUniverse) ∈ countableUnionCore (n + 1)`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean`

- **`mem_versionSpace_iff`** — line 37; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem mem_versionSpace_iff {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {L : GenLimit.Generic.Language α} : L ∈ versionSpace H S ↔ L ∈ H ∧ (↑S : Set α) ⊆ L`

- **`closure_eq_none_iff`** — line 42; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem closure_eq_none_iff {H : GenLimit.Generic.LanguageClass α} {S : Finset α} : closure H S = none ↔ ¬(versionSpace H S).Nonempty`

- **`closure_eq_some_iff`** — line 55; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem closure_eq_some_iff {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {C : GenLimit.Generic.Language α} : closure H S = some C ↔ (versionSpace H S).Nonempty ∧ C = commonCore H S`

- **`sample_subset_of_streamIn`** — line 71; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem sample_subset_of_streamIn {stream : GenLimit.Generic.Stream α} {L : GenLimit.Generic.Language α} (hstream : GenLimit.Generic.StreamIn stream L) (t : ℕ) : (↑(GenLimit.Generic.sample stream t) : Set α) ⊆ L`

- **`target_mem_versionSpace`** — line 78; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem target_mem_versionSpace {H : GenLimit.Generic.LanguageClass α} {L : GenLimit.Generic.Language α} (hLH : L ∈ H) {stream : GenLimit.Generic.Stream α} (hstream : GenLimit.Generic.StreamIn stream L) (t : ℕ) : L ∈ versionSpace H (GenLimit.Generic.sample stream t)`

- **`sample_subset_commonCore`** — line 84; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem sample_subset_commonCore {H : GenLimit.Generic.LanguageClass α} {S : Finset α} : (↑S : Set α) ⊆ commonCore H S`

- **`commonCore_subset_of_mem_versionSpace`** — line 90; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem commonCore_subset_of_mem_versionSpace {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {L : GenLimit.Generic.Language α} (hL : L ∈ versionSpace H S) : commonCore H S ⊆ L`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean`

- **`blockFinset_card`** — line 128; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem blockFinset_card (d : ℕ) : (blockFinset d).card = d`

- **`blockTail_infinite`** — line 136; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem blockTail_infinite (b : Bool) : (blockTail b).Infinite`

- **`commonCore_blockSeparationClass_eq`** — line 157; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem commonCore_blockSeparationClass_eq (d : ℕ) : commonCore blockSeparationClass (blockFinset d) = blockSet d`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean`

- **`commonCore_mono_sample`** — line 28; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem commonCore_mono_sample {H : GenLimit.Generic.LanguageClass α} {S T : Finset α} (hST : S ⊆ T) : commonCore H S ⊆ commonCore H T`

- **`commonCore_infinite_mono_sample`** — line 36; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem commonCore_infinite_mono_sample {H : GenLimit.Generic.LanguageClass α} {S T : Finset α} (hST : S ⊆ T) (hInfinite : (commonCore H S).Infinite) : (commonCore H T).Infinite`

- **`commonCore_cofiniteLanguageClass_eq`** — line 90; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem commonCore_cofiniteLanguageClass_eq (S : Finset α) : commonCore (cofiniteLanguageClass α) S = (↑S : Set α)`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean`

- **`spine_versionSpace_nonempty`** — line 174; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem spine_versionSpace_nonempty (t : ℕ) : (versionSpace spineTailClass (GenLimit.Generic.sample spineStream t)).Nonempty`

- **`spine_commonCore_subset_sample`** — line 180; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem spine_commonCore_subset_sample (t : ℕ) : commonCore spineTailClass (GenLimit.Generic.sample spineStream t) ⊆ (↑(GenLimit.Generic.sample spineStream t) : Set SpineTailUniverse)`

- **`spine_commonCore_finite`** — line 206; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem spine_commonCore_finite (t : ℕ) : (commonCore spineTailClass (GenLimit.Generic.sample spineStream t)).Finite`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteConeCover.lean`

- **`mem_upwardCone_iff`** — line 25; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem mem_upwardCone_iff {S L : Set α} : L ∈ upwardCone S ↔ S ⊆ L`

- **`upwardCone_eq_union_class`** — line 31; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem upwardCone_eq_union_class (S : Set α) : upwardCone S = {L : Set α | ∃ A : Set α, L = S ∪ A}`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean`

- **`mem_limitNonuniformSeparationClass_iff`** — line 35; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem mem_limitNonuniformSeparationClass_iff {P N L : Set α} : L ∈ limitNonuniformSeparationClass P N ↔ (∃ A : Set α, A ⊆ P ∧ L = N ∪ A) ∨ L = P`

- **`paperPositiveIntegers_infinite`** — line 416; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem paperPositiveIntegers_infinite : paperPositiveIntegers.Infinite`

- **`paperNonpositiveIntegers_infinite`** — line 429; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem paperNonpositiveIntegers_infinite : paperNonpositiveIntegers.Infinite`

- **`paper_integer_partition_disjoint`** — line 442; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem paper_integer_partition_disjoint : Disjoint paperPositiveIntegers paperNonpositiveIntegers`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean`

- **`vcShatters_mono`** — line 56; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem vcShatters_mono {H K : GenLimit.Generic.LanguageClass α} (hHK : H ⊆ K) {d : ℕ} {xs : Fin d → α} (h : VCShatters H xs) : VCShatters K xs`

- **`pairShattered_of_vcShatters`** — line 70; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem pairShattered_of_vcShatters {H : GenLimit.Generic.LanguageClass α} {d : ℕ} {xs : Fin d → α} (h : VCShatters H xs) {i j : Fin d} (hij : i ≠ j) : PairShattered H (xs i) (xs j)`

- **`vcShatters_injective`** — line 83; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem vcShatters_injective {H : GenLimit.Generic.LanguageClass α} {d : ℕ} {xs : Fin d → α} (h : VCShatters H xs) : Function.Injective xs`

- **`not_pacViaVC_of_infinite`** — line 98; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem not_pacViaVC_of_infinite {H : GenLimit.Generic.LanguageClass α} (h : HasInfiniteVCDimension H) : ¬PACLearnableViaVC H`

- **`littlestoneShattered_mono`** — line 154; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem littlestoneShattered_mono {H K : GenLimit.Generic.LanguageClass α} (hHK : H ⊆ K) {d : ℕ} {T : LittlestoneTree α d} (hT : LittlestoneShattered T H) : LittlestoneShattered T K`

- **`littlestoneShattered_nonempty`** — line 174; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem littlestoneShattered_nonempty {H : GenLimit.Generic.LanguageClass α} {d : ℕ} {T : LittlestoneTree α d} (hT : LittlestoneShattered T H) : H.Nonempty`

- **`no_depth_one_of_subsingleton`** — line 185; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem no_depth_one_of_subsingleton {H : GenLimit.Generic.LanguageClass α} (hH : H.Subsingleton) (T : LittlestoneTree α 1) : ¬LittlestoneShattered T H`

- **`not_onlineViaLittlestone_of_infinite`** — line 202; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem not_onlineViaLittlestone_of_infinite {H : GenLimit.Generic.LanguageClass α} (h : HasInfiniteLittlestoneDimension H) : ¬OnlineLearnableViaLittlestone H`

- **`uniformlyGeneratable_of_common_infinite_base`** — line 211; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem uniformlyGeneratable_of_common_infinite_base [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} {B : Set α} (hB : B.Infinite) (hbase : ∀ L, L ∈ H → B ⊆ L) : UUS H ∧ UniformlyGeneratable H`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean`

- **`prompted_closure_witness_mono`** — line 46; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem prompted_closure_witness_mono {H : MulticlassHypothesisClass α ι} {S T : Finset α} {y : ι} (hST : S ⊆ T) (hT : IsPromptedClosureWitness H T y) : IsPromptedClosureWitness H S y`

- **`exists_prompted_closure_witness_card_eq`** — line 57; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem exists_prompted_closure_witness_card_eq {H : MulticlassHypothesisClass α ι} (hPC : HasInfinitePromptedClosureDimension H) (d : ℕ) : ∃ y : ι, ∃ S : Finset α, S.card = d ∧ IsPromptedClosureWitness H S y`

- **`promptedSequenceSample_history`** — line 132; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptedSequenceSample_history (h : MulticlassHypothesis α ι) (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι) (t : ℕ) (y : ι) : promptedSequenceSample (promptedHistory h xs ys t) y = promptedSample h xs y t`

- **`promptedObservedSample_history`** — line 149; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptedObservedSample_history (h : MulticlassHypothesis α ι) (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι) (t : ℕ) : promptedObservedSample (promptedHistory h xs ys t) = GenLimit.Generic.sample xs t`

- **`promptedClosureGenerator_spec`** — line 187; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptedClosureGenerator_spec [Nonempty α] {H : MulticlassHypothesisClass α ι} {d t : ℕ} (hPC : PromptedClosureDimensionAtMost H d) (history : Fin t → PromptedObservation α ι) (ht : 0 < t) : let last : Fin t := ⟨t - 1, Nat.sub_lt (by omega) (by omega)⟩; let y := (history last).2.2; let S := promptedSequenceSample history y; let observed := promptedObservedSample history; d < S.card → (promptedVersionSpace H S y).Nonempty → promptedClosureGenerator H d hPC t history ∈ promptedCommonCore H S y \ (↑observed : Set α)`

- **`exists_earlier_promptedSample_card_eq`** — line 309; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem exists_earlier_promptedSample_card_eq {h : MulticlassHypothesis α ι} {xs : GenLimit.Generic.Stream α} {y : ι} {t k : ℕ} (hk : k ≤ (promptedSample h xs y t).card) : ∃ r ≤ t, (promptedSample h xs y r).card = k`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean`

- **`mem_promptedSample_iff`** — line 58; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem mem_promptedSample_iff {h : MulticlassHypothesis α ι} {xs : GenLimit.Generic.Stream α} {y : ι} {t : ℕ} {x : α} : x ∈ promptedSample h xs y t ↔ x ∈ GenLimit.Generic.sample xs t ∧ h x = y`

- **`promptedSample_mono`** — line 66; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptedSample_mono {h : MulticlassHypothesis α ι} {xs : GenLimit.Generic.Stream α} {y : ι} {s t : ℕ} (hst : s ≤ t) : promptedSample h xs y s ⊆ promptedSample h xs y t`

- **`mem_promptedVersionSpace_iff`** — line 173; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem mem_promptedVersionSpace_iff {H : MulticlassHypothesisClass α ι} {S : Finset α} {y : ι} {h : MulticlassHypothesis α ι} : h ∈ promptedVersionSpace H S y ↔ h ∈ H ∧ ∀ x ∈ S, h x = y`

- **`promptedClosure_eq_none_iff`** — line 180; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptedClosure_eq_none_iff {H : MulticlassHypothesisClass α ι} {S : Finset α} {y : ι} : promptedClosure H S y = none ↔ ¬(promptedVersionSpace H S y).Nonempty`

- **`promptedClosure_eq_some_iff`** — line 187; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptedClosure_eq_some_iff {H : MulticlassHypothesisClass α ι} {S : Finset α} {y : ι} {C : Set α} : promptedClosure H S y = some C ↔ (promptedVersionSpace H S y).Nonempty ∧ C = promptedCommonCore H S y`

- **`promptedSample_subset_commonCore`** — line 204; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptedSample_subset_commonCore {H : MulticlassHypothesisClass α ι} {S : Finset α} {y : ι} : (↑S : Set α) ⊆ promptedCommonCore H S y`

- **`promptedCommonCore_subset_support`** — line 210; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptedCommonCore_subset_support {H : MulticlassHypothesisClass α ι} {S : Finset α} {y : ι} {h : MulticlassHypothesis α ι} (hh : h ∈ promptedVersionSpace H S y) : promptedCommonCore H S y ⊆ promptSupport h y`

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean`

- **`promptBlock_card`** — line 55; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptBlock_card (p : PositivePrompt) : (promptBlock p).card = p.1`

- **`promptSeparationLeft_block`** — line 63; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptSeparationLeft_block (p : PositivePrompt) {x : PromptSeparationUniverse} (hx : x ∈ promptBlock p) : promptSeparationLeft x = p`

- **`promptSeparationRight_block`** — line 72; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptSeparationRight_block (p : PositivePrompt) {x : PromptSeparationUniverse} (hx : x ∈ promptBlock p) : promptSeparationRight x = p`

- **`promptBlock_versionSpace_nonempty`** — line 120; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptBlock_versionSpace_nonempty (p : PositivePrompt) : (promptedVersionSpace promptSeparationClass (promptBlock p) p).Nonempty`

- **`promptedCommonCore_promptBlock_subset`** — line 126; `theorem`; **supporting structural/API theorem**.  
  Exact stripped declaration statement/body: `theorem promptedCommonCore_promptBlock_subset (p : PositivePrompt) (hp : p ≠ firstPositivePrompt) : promptedCommonCore promptSeparationClass (promptBlock p) p ⊆ (↑(promptBlock p) : Set PromptSeparationUniverse)`
