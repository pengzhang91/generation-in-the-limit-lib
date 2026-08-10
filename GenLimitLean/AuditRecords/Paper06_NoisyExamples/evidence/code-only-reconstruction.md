# 06 — Paper06_GenerationFromNoisyExamples — Generation from Noisy Examples — Lean Faithfulness Audit

## Stage 1: Lean-statement reconstruction only

This document reconstructs the mathematical content of the attached deterministic Lean source bundle at repository commit `dfcd13534f9d51642a9f88904268e95454c88f7f`. The audited bundle has byte size `225002` and SHA-256

```text
430635a4daf50622b55ca7e711735e48cb2e600d35f8b93025ad68233db794a3
```

The source manifest contains 18 files and no unresolved local imports. The primary target scope is the umbrella module

```text
GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples.lean
```

and the ten modules under

```text
GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/
```

The remaining seven local modules are dependencies. Their definitions are unfolded below only insofar as they are needed to interpret the primary declarations; their standalone theorems are not presented as Paper 06 claims.

### Evidence discipline

The reconstruction uses declaration types, proposition expressions, and bodies of definitions needed to determine those proposition expressions or the data computed by a declared construction. It does not use comments, docstrings, theorem proof bodies, filenames, module names, namespace names, declaration names, or paper labels as evidence for mathematical meaning. Paths and exact Lean identifiers are reported only for provenance and inventory. Accordingly, statements such as “the numbered wrapper” below identify declarations; their translations come from the types, not from the identifier.

---

## Abstract

The primary Lean modules formalize deterministic generation of fresh valid examples from finite histories over an example type `α`. A language is a set `L ⊆ α`; a language class is a set `H` of such languages. A generator sees the complete ordered finite history, including repetitions, and returns one example. Its correctness at a time means that the output belongs to the target language and is not among the distinct examples observed before that time.

Several adversarial noise models and threshold conventions are formalized.

1. **Uniform noise-independent generation:** one generator and one distinct-observation threshold must work for every target and every stream having finitely many off-target occurrences, independently of how many such occurrences there are.
2. **Uniform noise-dependent generation:** one generator works at every finite noise budget, while the threshold may depend on that budget.
3. **Non-uniform noise-dependent generation:** the threshold may depend on both the noise budget and the target language.
4. **Noisy generation in the limit:** on a stream that contains every target element and only finitely many off-target occurrences, outputs are eventually always valid and fresh.
5. Two additional variants count distinct **positive** observations at the trigger: a uniform noise-independent notion and a target-dependent non-uniform noise-independent notion.

The principal formal results are:

- under an infinite countable example type and an every-language-infinite assumption, uniform noise-independent generatability is equivalent to infinitude of the intersection of all languages in the class;
- under a nonempty countable example type and the same language-infinitude assumption, uniform noise-dependent generatability is equivalent to eventual absence of finite noisy-core witnesses at every fixed noise level;
- every finite class of infinite languages is uniformly noise-dependent generatable;
- every countable class of infinite languages is non-uniformly noise-dependent generatable and noisily generatable in the limit;
- any ordinary non-uniform generator can be noncomputably robustified into a generator that succeeds in the limit on noisy presentations;
- a finite union of uniformly noise-independent generatable components is noisily generatable in the limit, under a countably infinite example type;
- an explicit countable class has ordinary closure dimension zero but exact noisy witnesses of every finite size at noise level one, and hence is not uniformly noise-dependent generatable;
- the positive-count uniform variant is characterized by a uniform bound on witness size minus noise level;
- an explicit two-language parity class is finite and consists of infinite languages, yet is not non-uniformly noise-independent generatable in the positive-count sense.

All noise is deterministic. There are no probability distributions, confidence levels, expected risks, stochastic convergence statements, or random-noise assumptions.

---

## 1. Formal universe, histories, and correctness

### 1.1 Objects

Fix a type `α` when a theorem does not specialize it further.

- A **language** is a set `L : Set α`.
- A **language class** is a set `H : Set (Set α)`.
- A **stream** is a function `x : ℕ → α`.
- A **finite history of length `t`** is a function `h : Fin t → α`.
- A **generator** is a total function
  
  \[
  G : \prod_{t\in\mathbb N}(\operatorname{Fin}(t)\to\alpha)\to\alpha.
  \]

For a stream `x`, the generator output at time `t` is

\[
G_t(x_{<t}) := G\,t\,(i\mapsto x_i),\qquad i\in\operatorname{Fin}(t).
\]

The distinct observed sample before time `t` is

\[
S_t(x):=\{x_s: s<t\},
\]

represented by a finite set. Order and multiplicity are discarded by `S_t`, but they remain visible to `G`, because `G` receives the entire function `Fin t → α`.

### 1.2 Correct output

The dependency definition `GenLimit.Generic.CorrectAt` unfolds to

\[
\operatorname{CorrectAt}(G,L,x,t)
\iff
G_t(x_{<t})\in L
\quad\text{and}\quad
G_t(x_{<t})\notin S_t(x).
\]

Thus “fresh” means fresh relative to the **input stream history** only. Nothing requires outputs at different times to be mutually distinct. In particular, a generator may repeatedly output the same target point if the stream never presents that point.

### 1.3 Every-language-infinite premise

The dependency predicate `GenLimit.LiRamanTewari.UUS H` is

\[
\forall L\;(L\in H\Rightarrow L\text{ is infinite}).
\]

It imposes no nonemptiness requirement on `H`; for `H = ∅` it holds vacuously.

### 1.4 Positive streams, exact presentations, and ordinary baseline notions

The dependency predicate `StreamIn x L` says

\[
\operatorname{range}(x)\subseteq L.
\]

It does **not** require `x` to enumerate every element of `L`.

The dependency predicate `Presents x L` says

\[
\operatorname{range}(x)=L.
\]

The ordinary non-uniform generation premise used later expands as follows. A generator `Q` witnesses `NonuniformlyGeneratable H` exactly when

\[
\forall L\in H\;\exists d_L\;\forall x
\Bigl[
\operatorname{range}(x)\subseteq L
\Rightarrow
\forall t\bigl(|S_t(x)|=d_L\Rightarrow
\forall s\ge t\;\operatorname{CorrectAt}(Q,L,x,s)\bigr)
\Bigr].
\]

The threshold depends on `L`, but not on the positive stream.

---

## 2. Noise predicates and presentation models

### 2.1 Finite noise

For a stream `x` and target `L`,

\[
\operatorname{HasFiniteNoise}(x,L)
\iff
\{t\in\mathbb N:x_t\notin L\}\text{ is finite}.
\]

This counts **time indices**, hence noisy occurrences. Repeating one off-target value at infinitely many times is not finite noise. Conversely, finitely many noisy positions may contain arbitrarily many distinct off-target values, up to their finite number of occurrences.

This condition does not require the stream to enumerate `L`, or even to show infinitely many distinct target points.

### 2.2 Bounded noise

For `n ∈ ℕ`,

\[
\operatorname{HasNoiseAtMost}(x,L,n)
\]

means that there is a finite set `F ⊆ ℕ` such that

\[
|F|\le n
\quad\text{and}\quad
(t\in F\iff x_t\notin L)
\quad\text{for every }t.
\]

Thus the exact set of noisy time indices has cardinality at most `n`. Duplicated noisy values count repeatedly if they occur at different times.

The primary declarations establish both directions relating the two occurrence-based notions:

- bounded noise at some specified level implies finite noise;
- finite noise implies bounded noise for some finite level, namely the cardinality of the finite bad-index set.

### 2.3 Noisy presentation

A stream is a `NoisyPresentation` of `L` exactly when

\[
L\subseteq\operatorname{range}(x)
\quad\text{and}\quad
\operatorname{HasFiniteNoise}(x,L).
\]

Every target element must occur at least once, while off-target occurrences are allowed at only finitely many positions. This does not require `range(x)=L`; the range may contain finitely many negative values.

### 2.4 Distinct noisy values versus noisy occurrences

For a finite set `S`, define

\[
S^+_L=S\cap L,
\qquad
S^-_L=S\setminus L.
\]

The source definitions are filters, so these are finite sets of **distinct values**. The noisy version-space condition below is equivalent to `|S^-_L| ≤ n`, whereas `HasNoiseAtMost` bounds noisy **positions**. The declared bridge proves

\[
\operatorname{HasNoiseAtMost}(x,L,n)
\Longrightarrow
|S_t(x)^-_L|\le n,
\]

and therefore places the target in each corresponding noisy version space. No converse from distinct bad values to bounded bad occurrences is declared or generally valid.

---

## 3. Generation notions and exact quantifier order

All thresholds are natural numbers, including zero. Every trigger uses equality to an exact cardinality, not an inequality.

### 3.1 Uniform noise-independent generation

A fixed `G` works at threshold `d` for `H` when

\[
\forall L\in H\;\forall x\;
\Bigl[
\operatorname{HasFiniteNoise}(x,L)
\Rightarrow
\forall t\bigl(|S_t(x)|=d\Rightarrow
\forall s\ge t\;\operatorname{CorrectAt}(G,L,x,s)\bigr)
\Bigr].
\]

The class is uniformly noise-independent generatable when

\[
\exists G\;\exists d\;[\text{the preceding property}].
\]

The threshold is independent of the target, the stream, the number of noisy occurrences, their values, and their locations.

### 3.2 Uniform noise-dependent generation

A fixed `G` is a uniform noise-dependent generator for `H` when

\[
\forall n\;\exists d_n\;\forall L\in H\;\forall x\;
\Bigl[
\operatorname{HasNoiseAtMost}(x,L,n)
\Rightarrow
\forall t\bigl(|S_t(x)|=d_n\Rightarrow
\forall s\ge t\;\operatorname{CorrectAt}(G,L,x,s)\bigr)
\Bigr].
\]

The class has the property when one such `G` exists. The generator is chosen before `n`; it is not passed `n` as an explicit input. Only the threshold may depend on `n`.

### 3.3 Non-uniform noise-dependent generation

A fixed `G` satisfies the non-uniform notion when

\[
\forall n\;\forall L\in H\;\exists d_{n,L}\;\forall x\;
\Bigl[
\operatorname{HasNoiseAtMost}(x,L,n)
\Rightarrow
\forall t\bigl(|S_t(x)|=d_{n,L}\Rightarrow
\forall s\ge t\;\operatorname{CorrectAt}(G,L,x,s)\bigr)
\Bigr].
\]

The class has the property when one `G` satisfies this for all `n` and `L`.

### 3.4 Noisy generation in the limit

A fixed `G` succeeds in the noisy limit on `H` when

\[
\forall L\in H\;\forall x\;
\Bigl[
\operatorname{NoisyPresentation}(x,L)
\Rightarrow
\exists T\;\forall s\ge T\;\operatorname{CorrectAt}(G,L,x,s)
\Bigr].
\]

The convergence time may depend on both the target and the full stream.

### 3.5 Alternate uniform noise-independent generation

This variant changes only the trigger. A fixed `G,d` must satisfy

\[
\forall L\in H\;\forall x\;
\Bigl[
\operatorname{HasFiniteNoise}(x,L)
\Rightarrow
\forall t\bigl(|S_t(x)\cap L|=d\Rightarrow
\forall s\ge t\;\operatorname{CorrectAt}(G,L,x,s)\bigr)
\Bigr].
\]

The threshold counts distinct positive observations, not all distinct observations.

### 3.6 Non-uniform noise-independent generation

The target-dependent positive-count variant is

\[
\exists G\;\forall L\in H\;\exists d_L\;\forall x\;
\Bigl[
\operatorname{HasFiniteNoise}(x,L)
\Rightarrow
\forall t\bigl(|S_t(x)\cap L|=d_L\Rightarrow
\forall s\ge t\;\operatorname{CorrectAt}(G,L,x,s)\bigr)
\Bigr].
\]

The threshold may depend on `L`, but not on the amount or placement of finite noise.

---

## 4. Noisy version spaces, cores, and dimension predicates

For a class `H`, finite set `S`, and noise level `n`, the noisy version space is

\[
V_n(H,S)
=
\{L\in H: |S|\le |S\cap L|+n\}.
\]

Because `S` is finite and partitions as `(S∩L) ⊔ (S\setminus L)`, this condition is equivalent to

\[
|S\setminus L|\le n.
\]

The noisy common core is the intersection of all languages in this version space:

\[
C_n(H,S)=\{x:\forall L\in V_n(H,S),\;x\in L\}.
\]

As a bare set-theoretic definition, `C_n(H,S)=α` when `V_n(H,S)` is empty. To distinguish that case, `noisyClosure H S n` is option-valued:

- it is `none` exactly when `V_n(H,S)` is empty;
- it is `some C_n(H,S)` exactly when the version space is nonempty.

A noisy-closure witness of level `n` and size `d` is a finite set `S` satisfying

\[
|S|=d,
\qquad
V_n(H,S)\ne\varnothing,
\qquad
C_n(H,S)\text{ is finite}.
\]

The predicate `FiniteNoisyClosureDimensionAt H n` does **not** assign a numeric dimension. It says only

\[
\exists D\;\forall d>D\;\text{there is no level-}n\text{ witness of size }d.
\]

A declared equivalent form is

\[
\exists D\;\forall S\text{ finite},
\quad D<|S|\ \wedge\ V_n(H,S)\ne\varnothing
\Longrightarrow C_n(H,S)\text{ is infinite}.
\]

This eventual-bound formulation allows gaps among witness cardinalities and does not require a largest witness size.

A separate predicate used for the explicit separation is

\[
\operatorname{InfiniteNoisyClosureDimensionAt}(H,n)
\iff
\forall d\;\text{there is a level-}n\text{ witness of exactly size }d.
\]

This is stronger on its face than merely negating the eventual-bound predicate: it requires every exact finite cardinality, not only arbitrarily large cardinalities.

The positive-count variant uses

\[
\operatorname{BoundedNoisyClosureExcess}(H)
\iff
\exists B\;\forall n,k,
\quad
[\text{a level-}n\text{ witness of size }k]
\Longrightarrow k\le n+B.
\]

No supremum object or subtraction in an extended natural-number type is defined.

---

## 5. Reconstructed principal results

### 5.1 Infinite common intersection exactly characterizes uniform noise-independent generation

**Declaration:** `GenLimit.NoisyExamples.theorem_3_1`  
**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/UniformIndependent.lean`

Assume `[Countable α]`, `[Infinite α]`, and every language in `H` is infinite. Then

\[
H\text{ is uniformly noise-independent generatable}
\iff
\bigcap_{L\in H}L\text{ is infinite}.
\]

Expanded, the left side is the existence of one `G` and one `d` such that, for every target `L∈H` and every stream with finitely many off-target time indices, every occurrence of exactly `d` distinct observed values forces all later outputs to lie in `L` and outside the current distinct sample.

The sufficiency direction is also declared separately as

```text
GenLimit.NoisyExamples.infinite_commonIntersection_implies_uniform_noiseIndependent
```

and has no countability, infinitude-of-`α`, or UUS premise in its type. That implication type asserts existence but does not expose a particular threshold. Separately, `commonIntersectionGenerator` and `commonIntersectionGenerator_spec` define and specify a candidate that, on every finite history, chooses a point in the common intersection outside the finite history sample. Combining those declarations yields a threshold-zero witness; the value zero is a derived witness from the construction interfaces, not an argument displayed in the implication theorem’s type.

The necessity direction is declared separately as

```text
GenLimit.NoisyExamples.uniform_noiseIndependent_implies_infinite_commonIntersection
```

under `[Infinite α]` and UUS. Its lower-bound interface is

```text
GenLimit.NoisyExamples.finite_commonIntersection_defeats_threshold
```

which states that if the common intersection is finite, then every proposed generator and every proposed threshold admit a target, a finite-noise stream, an exact trigger time, and a later failure of correctness.

**Statement-level observations.**

- The final equivalence assumes a countably infinite example type. The direction declarations reveal an asymmetry: infinitude of the common intersection alone suffices without countability, whereas the necessity declaration asks only for `[Infinite α]` plus UUS.
- For an empty class, the common intersection is the universal set. Under `[Infinite α]`, both sides hold: the generation property is vacuous after a total generator is chosen, and the universal set is infinite.
- The theorem does not cover a finite example type. In particular, an empty class over a nonempty finite type is vacuously generatable, but its common intersection is finite.
- The generator is noncomputable and obtains no membership oracle for `H` or its members.

### 5.2 Finite noisy closure dimensions exactly characterize uniform noise-dependent generation

**Declaration:** `GenLimit.NoisyExamples.theorem_3_3`  
**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

Assume `[Countable α]`, `[Nonempty α]`, and UUS for `H`. Then

\[
H\text{ is uniformly noise-dependent generatable}
\iff
\forall n\in\mathbb N,
\operatorname{FiniteNoisyClosureDimensionAt}(H,n).
\]

Equivalently, the right side says that for every occurrence-noise budget `n`, there is a bound `D_n` such that every finite distinct sample `S` with more than `D_n` elements and a nonempty `n`-noisy version space has an infinite noisy common core.

The constructive direction is separately declared as

```text
GenLimit.NoisyExamples.finite_noisyClosureDimensions_imply_uniform_noiseDependent
```

under `[Nonempty α]`. Its type asserts existence and does not expose the threshold function. Separately, the module defines one candidate generator independent of `n`. At history set `S` and time `t`, that candidate forms the finite set of levels `m≤t` satisfying

\[
D_m<|S|
\quad\text{and}\quad
V_m(H,S)\ne\varnothing,
\]

selects the largest eligible level, and chooses a fresh point from its infinite noisy core. Combining the candidate’s specifications with the generic bound `|S_t|≤t` gives the sufficient choice

\[
d_n=\max(D_n+1,n).
\]

This formula is not exposed by the implication theorem’s result type; it is a witness derivable from the separately declared construction/specification interfaces. Including `n` ensures that an exact trigger of cardinality `d_n` cannot occur before time `n`.

The converse is separately declared as

```text
GenLimit.NoisyExamples.uniform_noiseDependent_implies_finite_noisyClosureDimensions
```

and factors through

```text
GenLimit.NoisyExamples.nonfinite_noisyClosureDimension_defeats_threshold.
```

For any fixed level `n`, failure of finite noisy closure dimension defeats every proposed generator and every proposed exact threshold by producing a target, a stream with at most `n` noisy occurrences, an exact trigger, and a later incorrect output.

**Statement-level observations.**

- The same generator must serve all noise levels; only `d_n` changes.
- The generator is not given the true noise level. The history-level construction searches among finitely many candidate levels.
- `[Nonempty α]` is required because a generator is total on all finite histories, including histories on which no core is eligible. The theorem does not assert necessity of countability or nonemptiness as mathematical hypotheses beyond the stated implication.
- The dimension predicate is only an eventual finiteness assertion; no minimal or exact numeric `NC_n(H)` is produced.
- If a bounded-noise stream never reaches exactly `d_n` distinct values, the defining obligation on that stream is vacuous.

### 5.3 Finite classes

**Declarations:**

```text
GenLimit.NoisyExamples.noisy_witness_card_le_for_finite_class
GenLimit.NoisyExamples.finite_class_has_finite_noisyClosureDimensionAt
GenLimit.NoisyExamples.corollary_3_4
```

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteClasses.lean`

For a finite class `H`, there is a finite bound `B` on the cardinalities of all finite intersections arising from subclasses of `H`. With such a `B`, every finite set `S` whose level-`n` noisy common core is finite satisfies

\[
|S|\le B+|H|\,n.
\]

Consequently, for every `n`, `H` has finite noisy closure dimension at level `n`; one valid eventual bound is `B+|H|n`.

Under `[Countable α]`, `[Nonempty α]`, and UUS, every finite language class is therefore uniformly noise-dependent generatable.

This is an existence result. The declarations provide no effective procedure for calculating a valid `B` from a presentation of `H`.

### 5.4 Non-uniform noise-dependent generation from increasing covers

#### Sufficient cover condition

**Declaration:** `GenLimit.NoisyExamples.lemma_3_6`  
**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

Assume `[Countable α]`, `[Nonempty α]`, UUS for `H`, and classes `(H_i)_{i∈ℕ}` satisfying

\[
H_i\subseteq H_j\quad(i\le j),
\qquad
H=\bigcup_i H_i.
\]

If

\[
\forall i,
\operatorname{FiniteNoisyClosureDimensionAt}(H_i,i),
\]

then `H` is non-uniformly noise-dependent generatable.

The same module separately defines `diagonalNoisyStrategy`: at a finite history it selects the largest index `i≤t` for which a chosen bound on the level-`i` noisy closure dimension of `H_i` has been passed and the corresponding noisy version space is nonempty, then chooses a fresh point from that core. The theorem’s result type asserts existence of a non-uniform generator and does not identify this named strategy as its witness. By the unfolded conclusion, the resulting exact threshold is allowed to depend on both `n` and `L`, but not on the particular stream.

#### Necessary per-noise cover condition

**Declaration:** `GenLimit.NoisyExamples.lemma_3_8`  
**Path:** the same module.

Assume `[Countable α]`, UUS for `H`, and non-uniform noise-dependent generatability. Then for every fixed noise level `n` there exists a nondecreasing cover `(H_i^{(n)})_i` of `H` such that

\[
\forall i,
\operatorname{FiniteNoisyClosureDimensionAt}(H_i^{(n)},n).
\]

The cover may depend on `n`. The dimension level on the right is the fixed `n`, not the diagonal index `i`.

#### Quantifier mismatch

The sufficient and necessary statements do not form a literal equivalence:

- sufficiency assumes one cover, independent of the unknown true noise level, with diagonal conditions `level i on class H_i`;
- necessity produces, separately for each `n`, a potentially different cover with a fixed-level condition `level n on every class in that cover`.

No primary declaration closes this gap or gives a full characterization of non-uniform noise-dependent generatability by a single cover condition.

### 5.5 Countable classes

**Declaration:** `GenLimit.NoisyExamples.corollary_3_7`  
**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

Assume `[Countable α]`, `[Nonempty α]`, UUS for `H`, and that `H` is a countable set of languages. Then both

\[
H\text{ is non-uniformly noise-dependent generatable}
\]

and

\[
H\text{ is noisily generatable in the limit}
\]

hold.

The corollary’s type does not expose a particular cover or generator. The surrounding primary declarations separately provide a finite-class dimension theorem, an increasing-cover sufficient condition, and the implication

\[
\text{non-uniform noise-dependent generation} + \text{UUS}
\Longrightarrow
\text{noisy generation in the limit}.
\]

No necessity of countability is asserted.

### 5.6 Robustification of an ordinary non-uniform generator

**Declaration:** `GenLimit.NoisyExamples.theorem_3_9`  
**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

Assume `[Countable α]`, UUS for `H`, and ordinary non-uniform generatability of `H` on positive streams. Then `H` is noisily generatable in the limit.

The premise unfolds to the existence of a single generator `Q` such that for each `L∈H` there is a target-specific threshold `d_L` working on every stream whose range is contained in `L`. The conclusion provides one generator that is eventually correct on every noisy presentation of every target.

#### Declared robustified generator

For a finite history `h`:

1. Let `D` be the number of distinct observed values.
2. Choose the largest number `r` of initial positions to discard such that the suffix has exactly `⌊D/2⌋` distinct values.
3. Starting from that suffix as a list, invoke `Q` repeatedly `r+1` times, appending each generated value to the list before the next invocation.
4. Form the finite set of generated values not already in the suffix, then retain those absent from the full original history.
5. If this final set is nonempty, output a chosen member; otherwise output an arbitrary fallback value.

The supporting declarations state that once the suffix consists only of target points and contains at least `d_L` distinct values, the iterative calls add exactly `r+1` distinct target points outside the suffix. Since the discarded prefix has only `r` positions, at least one candidate is absent from the full history.

For a noisy presentation, a finite cutoff is defined after the last off-target occurrence. The declared eventual invariant says that, after sufficiently many distinct values have appeared, the exact-half suffix starts after this cutoff and contains at least `d_L` distinct values. The theorem then applies the local correctness declaration at every later time.

**Statement-level observations.**

- The conclusion permits the convergence time to depend on the entire target and stream. No declaration bounds it using only the number of noisy occurrences, the last noisy time, or a distinct-value growth rate.
- There is no quantitative time bound.
- The construction is noncomputable and uses classical equality and choice.
- No converse is declared.
- The premise itself supplies a total generator, so the theorem can derive an inhabitant of `α`; no separate `[Nonempty α]` appears in the final signature.

### 5.7 Finite unions of uniform noise-independent components

**Declaration:** `GenLimit.NoisyExamples.theorem_3_10`  
**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteUnionLimit.lean`

Assume `[Countable α]`, `[Infinite α]`, UUS for `H`, and a finite family of classes `(H_i)_{i∈Fin(k)}` such that

\[
H=\bigcup_{i\in\operatorname{Fin}(k)} H_i
\]

and every `H_i` is uniformly noise-independent generatable. Then `H` is noisily generatable in the limit.

The component classes may overlap, repeat, or be empty; no monotonicity or disjointness is required. The index set may also be empty, in which case the cover equality forces `H=∅`.

The same module separately defines `finiteUniformUnionNoisyGenerator`. Given an infinite common intersection for each component, this candidate fixes a repetition-free enumeration of each intersection. At a current distinct sample, its progress score is the first enumeration index whose value is absent; it selects a component of maximal progress and outputs that component’s first unseen enumerated point. Supporting declarations state the enumeration and argmax properties and provide a permanently missing enumerated obstruction for any component whose common intersection is not contained in the stream range.

The final theorem’s type asserts existence of a noisy-limit generator but does not name `finiteUniformUnionNoisyGenerator` as its witness, and there is no standalone primary declaration saying that this named generator satisfies `IsNoisyLimitGenerator`. Accordingly, the argmax generator is recorded here as candidate infrastructure supplied by the module, while the theorem-level claim remains the existential implication displayed above.

The result is one-way. No converse or necessity condition for finite-union representability is declared.

### 5.8 Explicit separation at noise level one

**Declarations:**

```text
GenLimit.NoisyExamples.separationClass_properties
GenLimit.NoisyExamples.lemma_3_5
GenLimit.NoisyExamples.separation_not_uniform_noiseDependent
```

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Separation.lean`

The concrete example type is

\[
\alpha=\mathbb N\times\operatorname{Option}(\mathbb N).
\]

For each `p∈ℕ`, define

\[
L_p=\{(q,z):q\ne p\},
\qquad
H=\{L_p:p\in\mathbb N\}.
\]

The declarations establish:

1. `H` is countable.
2. Every `L_p` is infinite.
3. `H` has ordinary closure dimension zero in the imported formal sense: every nonempty finite positive sample with nonempty version space has infinite ordinary common core, and the special zero-dimension disjunct is used.
4. For every `d`, the finite set
   
   \[
   S_d=\{(i,\operatorname{none}):i<d\}
   \]
   
   is a level-one noisy-closure witness of exact cardinality `d`. Indeed, every `L_p` omits at most one point of `S_d`, so the level-one noisy version space is all of `H`, while its common core is empty.

Thus `InfiniteNoisyClosureDimensionAt H 1` holds in the exact-every-cardinality sense. A separate declaration concludes

\[
\neg\operatorname{UniformNoiseDependentGeneratable}(H).
\]

The existential declaration `lemma_3_5` packages only the countability, UUS, ordinary dimension-zero, and exact noisy-witness properties. The generation-level negative conclusion is a separate declaration.

The primary module does not itself state a combined theorem asserting ordinary uniform generatability and noisy non-generatability. Such an ordinary positive consequence may be derivable using imported dependency theorems, but it is not a standalone primary declaration and is not counted here as an explicit Paper 06 result.

### 5.9 Positive-observation threshold characterization

**Declaration:** `GenLimit.NoisyExamples.theorem_C_3`  
**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/AlternatePositive.lean`

Assume `[Countable α]`, `[Nonempty α]`, and UUS for `H`. Then

\[
H\text{ is alternate uniformly noise-independent generatable}
\iff
\operatorname{BoundedNoisyClosureExcess}(H).
\]

Expanded, the right side is

\[
\exists B\;\forall n,k,
\quad
[\exists S,\quad |S|=k,\ V_n(H,S)\ne\varnothing,\ C_n(H,S)\text{ finite}]
\Rightarrow k\le n+B.
\]

The implication theorem’s type does not expose a threshold. Separately, the module’s candidate strategy uses the parameter `B` and, at a current sample `S`, the level

\[
n_S=|S|-(B+1)
\]

and, when its noisy core is infinite, chooses a fresh point from that core. Combining the strategy specifications with the version-space definitions gives the sufficient positive-count threshold `B+1`; this value is a derived witness rather than a parameter in the implication theorem’s type. The target belongs to the relevant version space whenever the current sample contains at least `B+1` distinct target points. The definition of the generation notion still restricts the quantified streams to finite-noise streams; no stronger theorem dropping that premise is declared.

For necessity, the separately declared adversarial theorem says that any level-`n` witness of size `k>n+d` defeats a proposed positive threshold `d`. Consequently the direction declarations support the witness bound `B=d`, although the existential `B` is not displayed in the characterization wrapper’s result type.

### 5.10 Deleting one language can obstruct the positive-count uniform notion

**Declaration:** `GenLimit.NoisyExamples.lemma_C_2`  
**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/AlternatePositive.lean`

Assume `[Countable α]`, UUS for `H`, a subclass `F⊆H`, and a language `f∈F`. If

\[
\bigcap_{L\in F}L\text{ is finite}
\]

but

\[
\bigcap_{L\in F\setminus\{f\}}L\text{ is infinite},
\]

then `H` is **not** alternate uniformly noise-independent generatable.

The premises are structural intersection conditions; they do not mention a generator or the desired negative conclusion. The declaration therefore is not conclusion-encoding. It is, however, a sufficient obstruction only; no converse is stated.

### 5.11 A finite parity class fails target-dependent noise-independent generation

**Declarations:**

```text
GenLimit.NoisyExamples.parityClass_not_nonuniform_noiseIndependent
GenLimit.NoisyExamples.lemma_D_2
```

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformIndependent.lean`

Let

\[
E=\{m\in\mathbb N:m\text{ is even}\},
\qquad
O=\{m\in\mathbb N:m\text{ is odd}\},
\qquad
H=\{E,O\}.
\]

The declarations establish that `H` is finite, both member languages are infinite, and

\[
\neg\operatorname{NonuniformNoiseIndependentGeneratable}(H)
\]

for the positive-observation trigger. The existential wrapper states that some finite UUS class over `ℕ` has this failure.

This negative result does not contradict the finite-class positive theorem for noise-dependent generation: the two notions have different threshold dependencies and different trigger statistics. No formal implication or incomparability theorem between them is declared.

---

## 6. Assumptions, quantifiers, and access model

### 6.1 Main-result assumption table

| Declaration | Type assumptions on `α` | Class assumptions | Stream/noise model | Threshold dependence | Trigger | Conclusion |
|---|---|---|---|---|---|---|
| `theorem_3_1` | `Countable`, `Infinite` | UUS | finite bad time-index set; no coverage requirement | one `d` for all targets and all finite noise | `card(S_t)=d` | uniform noise-independent iff common intersection infinite |
| `theorem_3_3` | `Countable`, `Nonempty` | UUS | at most `n` bad time indices | `d=d(n)`; one generator for all `n` | `card(S_t)=d(n)` | uniform noise-dependent iff finite noisy closure dimension for every `n` |
| `corollary_3_4` | `Countable`, `Nonempty` | UUS, finite `H` | as above | as above | all distinct | uniform noise-dependent generation |
| `lemma_3_6` | `Countable`, `Nonempty` | UUS; nondecreasing cover; diagonal finite dimensions | at most `n` bad occurrences | `d=d(n,L)` | all distinct | non-uniform noise-dependent generation |
| `lemma_3_8` | `Countable` | UUS; non-uniform noise-dependent generation | at most fixed `n` bad occurrences | inherited target thresholds | all distinct | for each `n`, a possibly `n`-dependent increasing cover with finite level-`n` dimensions |
| `corollary_3_7` | `Countable`, `Nonempty` | UUS, countable `H` | bounded occurrence noise and noisy presentations | target/noise dependent; eventual time for limit | all distinct / eventual | non-uniform noise-dependent and noisy-limit generation |
| `theorem_3_9` | `Countable` | UUS; ordinary non-uniform generation | noisy presentation: target covered, finitely many bad occurrences | ordinary `d_L`; noisy conclusion has stream-dependent time | eventual | noisy-limit generation |
| `theorem_3_10` | `Countable`, `Infinite` | UUS; finite cover by uniform noise-independent classes | noisy presentation | eventual time depends on target/stream | eventual | noisy-limit generation |
| `lemma_3_5` | concrete `ℕ×Option ℕ` | existential explicit class | combinatorial noisy closure at level one | none | exact witness sizes | countable UUS class, ordinary dimension zero, witness at every size |
| `separation_not_uniform_noiseDependent` | concrete `ℕ×Option ℕ` | explicit class | at most `n` bad occurrences | uniform noise-dependent | all distinct | negation of uniform noise-dependent generation |
| `theorem_C_3` | `Countable`, `Nonempty` | UUS | finite bad occurrences | one positive-count threshold | `card(S_t ∩ L)=d` | equivalence with bounded noisy-closure excess |
| `lemma_C_2` | `Countable` | UUS; `F⊆H`, `f∈F`; intersection hypotheses | finite bad occurrences in negated notion | one positive-count threshold | positive distinct | non-generatability |
| `lemma_D_2` | concrete `ℕ` | existential finite UUS class | finite bad occurrences | target-dependent, noise-independent | positive distinct | failure of non-uniform noise-independent generation |

### 6.2 What the generator sees

A generator receives:

- the history length `t`;
- the complete ordered prefix `Fin t → α`, including all repetitions and noisy values.

It does **not** receive:

- the target language `L`;
- an index of `L` in `H`;
- the true noise budget `n`;
- the set of noisy positions;
- a membership oracle for `L` or `H`;
- a computable enumeration of `H`;
- a promise that the current history is one of the quantified admissible histories.

The noncomputable generator definitions are parameterized meta-mathematically by `H` and by classical witnesses such as dimension bounds or infinite-core proofs. This is extensional classical access, not an executable oracle model.

### 6.3 Computability and effectivity

No primary result asserts that a generator is computable. The declared generators use combinations of:

- `Classical.choose`;
- noncomputable finite-set filters and maxima;
- noncomputable choices of dimension bounds;
- noncomputable equivalences between `ℕ` and infinite subsets of countable types;
- classical decidable equality.

`[Countable α]` is a logical typeclass assumption; no effective coding, runtime, query complexity, or membership decision procedure is part of the generator interface. The separate `MembershipOracle` structure in a dependency over the fixed universe `ℕ` is not used by the primary Paper 06 declarations.

---

## 7. Dependency, helper, and link audit

### 7.1 Dependency declarations used for interpretation

The primary modules rely on the following dependency-level interfaces.

1. `GenLimit.Core.Countable` supplies generic languages, classes, streams, generators, finite distinct samples, output, exact presentation, positive-stream inclusion, and `CorrectAt`.
2. `Paper02...Definitions` supplies UUS and ordinary uniform, non-uniform, and limit generation notions.
3. `Paper02...Closure` supplies ordinary version spaces, common cores, and ordinary closure-dimension predicates used by the explicit separation.
4. `Paper02...NonuniformCharacterization` supplies nondecreasing-cover notation and a finite-class ordinary closure fact; its standalone characterization is not a Paper 06 claim.
5. `Paper02...Hierarchy` supplies ordinary implication interfaces used in robustification context.
6. `Paper02...GenerationInLimitCharacterization` supplies finite-cover notation used by the finite-union theorem.

No result from these dependency modules is inventoried below as a primary declaration.

### 7.2 Logical links explicitly declared in primary scope

The primary source declares the following implication chain and characterization links:

\[
\begin{aligned}
&\text{infinite common intersection}
\Longleftrightarrow
\text{uniform noise-independent generation},\\
&[\forall n,\text{ finite noisy closure dimension at }n]
\Longleftrightarrow
\text{uniform noise-dependent generation},\\
&\text{uniform noise-dependent}
\Longrightarrow
\text{non-uniform noise-dependent},\\
&\text{non-uniform noise-dependent}+\text{UUS}
\Longrightarrow
\text{noisy generation in the limit},\\
&\text{ordinary non-uniform generation}+\text{UUS}
\Longrightarrow
\text{noisy generation in the limit},\\
&\text{finite cover by uniform noise-independent components}+\text{UUS}
\Longrightarrow
\text{noisy generation in the limit},\\
&\text{bounded noisy-closure excess}
\Longleftrightarrow
\text{alternate uniform noise-independent generation}.
\end{aligned}
\]

### 7.3 No evident circular main premise

After recursively unfolding the main predicates, none of the principal equivalences assumes the desired generation conclusion, a generator already satisfying the same noisy notion, or a dimension predicate defined in terms of generator success.

Several construction lemmas have deliberately strong local premises:

- `nonuniform_generator_correct_on_finite_history` assumes the full target-specific ordinary threshold guarantee for `Q` on every positive stream and converts it to correctness on an arbitrary finite positive history;
- `paperRobustifiedNoiselessGenerator_correct` assumes that the selected suffix is positive and already has enough distinct values;
- the eventual suffix theorem separately establishes those assumptions on every sufficiently late noisy-presentation prefix;
- core-selection specifications assume infinitude of the selected core, which is separately supplied by the corresponding dimension hypothesis.

These are bridge interfaces, not circular restatements: the local assumptions are produced by independent declarations before the final theorem is applied.

### 7.4 Conclusion-proximal construction specifications

Declarations such as `freshFromNoisyCore_spec`, `commonIntersectionGenerator_spec`, and the strategy-output specifications say that a specifically defined choice lies in a desired set difference. They are close to the local correctness goal because the associated definitions choose from exactly that set difference. They should be classified as construction specifications, not substantive characterization claims.

### 7.5 Strong or possibly nonminimal side assumptions

The final signatures include several assumptions whose necessity is not established:

- countability appears in `theorem_3_3`, `lemma_3_6`, `lemma_3_8`, `theorem_C_3`, and `lemma_C_2`, even though the corresponding conclusions do not themselves state an enumeration;
- UUS is an explicit side premise of `lemma_3_6` even though it does not occur inside the cover or noisy-dimension predicates in the antecedent;
- `[Infinite α]` is used in `theorem_3_1` and `theorem_3_10`, excluding all finite universes;
- `[Nonempty α]` is explicit where a total fallback output is needed, except when a premise already provides a generator and hence an inhabitant.

The declarations prove the stated theorems only with these premises. They do not prove that the premises are minimal, and this audit does not remove them.

---

## 8. Edge cases, vacuity, and degeneracy risks

### 8.1 Exact-cardinality trigger vacuity

Every threshold notion has the form

\[
\forall t,\quad |S_t|=d\Rightarrow\cdots
\]

or its positive-count analogue. If an admissible stream never reaches exactly `d`, that stream imposes no correctness obligation. This is material because:

- finite-noise and bounded-noise streams need not enumerate the target;
- they may have finite range;
- UUS makes the target infinite but does not force the stream to reveal infinitely many target values.

Thus these threshold notions are not “eventually correct on every admissible stream” unless one separately knows that the trigger cardinality is reached. Noisy presentations do supply unbounded distinct range under UUS, which is why the link to noisy-limit generation can choose an exact trigger time.

### 8.2 Zero thresholds and zero noise

- `d=0` is allowed. Since `S_0=∅`, a threshold-zero generator must be correct from time zero on every covered stream.
- `n=0` is allowed. `HasNoiseAtMost(x,L,0)` forces every stream value to lie in `L`, but still does not require coverage of `L`.
- At noisy level zero, `V_0(H,S)` is the ordinary positive version space `{L∈H:S⊆L}`. No primary declaration identifies `FiniteNoisyClosureDimensionAt H 0` with the imported ordinary finite closure-dimension predicate, whose encoding has a separate special convention at dimension zero.
- A witness of size zero is possible when `H` is nonempty and its common intersection is finite.

### 8.3 Empty classes

For `H=∅`:

- UUS is vacuous;
- `commonIntersection H=α` by universal quantification;
- all noisy version spaces are empty, so there are no noisy-closure witnesses and every `FiniteNoisyClosureDimensionAt H n` holds;
- generation predicates still require existence of a total generator. They are therefore true when `α` is inhabited and false when no generator can exist over an empty type.

This explains the explicit nonemptiness or infinitude assumptions in several wrappers.

### 8.4 Empty or finite target languages outside UUS theorems

The generation definitions themselves do not require targets to be infinite. For an empty target, there are no bounded-noise streams at any finite budget, because every time index is bad. The universal stream condition may therefore be vacuous. Main characterizations avoid this by assuming UUS, but standalone definitions and some direction lemmas must be read with this degeneracy in mind.

### 8.5 Empty version spaces and universal cores

`noisyCommonCore H S n` is the universal set when `V_n(H,S)` is empty. The option-valued `noisyClosure` and the witness predicate explicitly record nonemptiness, preventing empty-version-space universal cores from becoming witnesses. Strategy eligibility also requires a nonempty noisy version space.

### 8.6 Freshness is stream-relative only

Correctness excludes the current observed sample, not previous generator outputs. No theorem establishes that the generated output sequence itself is injective or that it enumerates infinitely many distinct target points. Internal iteration in the robustification module explicitly appends generated points only for the purpose of forcing fresh successive candidates from the baseline generator.

### 8.7 Time and distinct-cardinality are different quantities

The robustification cutoff is a time index, while its threshold arguments concern distinct sample cardinality. The declared eventual invariant is existential and exposes no formula for its time `T`. Separate suffix-location and suffix-cardinality declarations relate sufficiently large distinct counts to later start positions and larger suffixes, but no quantitative convergence bound is part of the final statement.

### 8.8 Finite noisy dimension may be vacuous

`FiniteNoisyClosureDimensionAt H n` is true whenever sufficiently large finite samples have empty noisy version space, even without any infinite-core phenomenon. The equivalent large-sample theorem retains the premise that the version space is nonempty.

### 8.9 Bounded excess may be vacuous

`BoundedNoisyClosureExcess H` places conditions only on existing witnesses. If there are none, any `B` works. It does not assert existence or attainment of a noisy closure dimension.

### 8.10 Exact-every-size “infinite dimension”

`InfiniteNoisyClosureDimensionAt H n` requires a witness of every exact size. It is not defined as the negation of `FiniteNoisyClosureDimensionAt H n`. The explicit separation proves the stronger exact-every-size property, so no equivalence between these two encodings is needed there.

### 8.11 Finite covers may have zero components

The finite-cover predicate allows `k=0`. Then the union is empty and the cover equality forces `H=∅`. The finite-union generator has a fallback branch for this case.

---

## 9. What the primary Lean statements do not establish

1. **No author-paper comparison.** This is intentionally deferred to Stage 2.
2. **No probabilistic noise model.** There are no random variables, distributions, independence assumptions, rates, or high-probability events.
3. **No effective algorithms.** Existence is classical and noncomputable; no oracle, runtime, sample-query, or representation complexity is supplied.
4. **No time/sample-complexity guarantees in stream time.** Thresholds concern exact numbers of distinct values; noisy-limit convergence times are existential and stream-dependent.
5. **No minimal thresholds or exact dimension values.** Chosen bounds need not be least, and the noisy dimension predicate is eventual rather than numeric.
6. **No full characterization of non-uniform noise-dependent generation.** The cover sufficiency and necessity statements have different quantifier patterns.
7. **No converse to ordinary robustification.** Noisy-limit generation is not shown to imply ordinary non-uniform generation.
8. **No converse to the finite-union theorem.** Noisy-limit generation is not shown to imply any finite cover by uniform noise-independent classes.
9. **No robustness to infinitely many sparse errors.** The noisy-presentation model allows only finitely many off-target occurrences.
10. **No mutual-freshness guarantee across outputs.** Freshness is only against the observed input history.
11. **No declared hierarchy among all noisy variants.** In particular, no implication is proved between the all-distinct and positive-distinct noise-independent notions, or between the positive-count non-uniform notion and noise-dependent non-uniform generation.
12. **No positive ordinary-generation theorem packaged with the separation.** The explicit class has ordinary closure dimension zero and fails uniform noise-dependent generation, but the primary module does not state the combined ordinary-generation separation as one theorem.
13. **No necessity of countability or class finiteness assumptions.** The corollaries are sufficient statements only.
14. **No arbitrary finite-universe analogue of the infinite-universe characterizations.** The two wrappers requiring `[Infinite α]` do not cover finite `α`.
15. **No transport theorem from other universe representations.** Primary statements are generic over `α`, but concrete examples use fixed tagged or natural-number universes.

---

## 10. Provisional statement-level difficulty

This ranking concerns the logical and definitional complexity of the declarations, not the unseen proof bodies.

| Result cluster | Provisional difficulty | Reason from statements and definitions |
|---|---:|---|
| Basic noise predicates and bridges | 1–2 / 5 | finite-set and quantifier bookkeeping; occurrence-to-distinct bridge |
| `theorem_3_1` | 3 / 5 | global adversarial quantifiers and exact-threshold lower bound, but a simple intersection invariant |
| `theorem_3_3` | 4.5 / 5 | one generator must work across all unknown noise levels; nested maxima, nonempty version spaces, and converse adversaries |
| Finite-class corollary | 3.5 / 5 | uniform counting across all subclasses and all noise levels |
| `lemma_3_6` / `lemma_3_8` | 4 / 5 | cover monotonicity, target/noise-dependent thresholds, and nonmatching quantifier directions |
| `theorem_3_9` | 5 / 5 | conversion from global stream guarantees to arbitrary finite histories, exact-half suffix selection, repeated internal calls, and eventual noisy-presentation invariants |
| `theorem_3_10` | 5 / 5 | finite-component argmax, infinite enumerations, bounded bad-component progress, and eventual validity under finite-noise presentations |
| Explicit separation | 3 / 5 | concrete countable construction with exact witness sizes and two closure notions |
| `theorem_C_3` / `lemma_C_2` | 4 / 5 | two-parameter witness bounds and positive-count triggers |
| Parity counterexample | 3.5 / 5 | two target-dependent thresholds confronted through common finite-prefix stream interfaces |

---

## 11. Complete primary declaration inventory

The inventory below includes every source-level declaration in the ten primary modules: 206 declarations total. Private source identifiers are marked `private`; Lean may elaborate them to internal names, so the displayed identifier is the exact source-level name rather than a stable exported constant. The umbrella module contains imports only and adds no declaration.

### 11.1 `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/UniformIndependent.lean`
| Exact source-level Lean declaration | Declaration kind / role | Faithful statement-level content |
|---|---|---|
| `GenLimit.NoisyExamples.commonIntersection` | def; definition | The set of points contained in every member language of `H`. |
| `GenLimit.NoisyExamples.HasFiniteNoise` | def; definition | The set of time indices at which the stream value is outside `L` is finite. |
| `GenLimit.NoisyExamples.IsUniformNoiseIndependentGeneratorAt` | def; core definition | For every `L∈H` and every finite-noise stream, any time with exactly `d` distinct observations triggers correctness at every later time. |
| `GenLimit.NoisyExamples.UniformNoiseIndependentGeneratable` | def; core definition | There exist one generator and one global threshold satisfying `IsUniformNoiseIndependentGeneratorAt`. |
| `GenLimit.NoisyExamples.commonIntersection_subset_of_mem` | theorem; set-theoretic bridge | Membership of `L` in `H` implies `commonIntersection H ⊆ L`. |
| `GenLimit.NoisyExamples.commonIntersectionGenerator` | def; noncomputable construction | Given an infinite common intersection, maps each finite history to a chosen common point outside its distinct sample. |
| `GenLimit.NoisyExamples.commonIntersectionGenerator_spec` | theorem; construction specification | The constructed output lies in the common intersection and outside the finite history sample. |
| `GenLimit.NoisyExamples.infinite_commonIntersection_implies_uniform_noiseIndependent` | theorem; substantive direction | An infinite common intersection implies uniform noise-independent generatability; the adjacent construction/specification declarations yield a threshold-zero witness. |
| `GenLimit.NoisyExamples.prefixThen` | def; stream construction | Uses a given finite prefix and then repeats one tail value forever. |
| `GenLimit.NoisyExamples.prefixThen_apply_lt` | theorem; construction restatement | Before the prefix length, `prefixThen` equals the supplied prefix. |
| `GenLimit.NoisyExamples.sample_prefixThen_full` | theorem; sample bridge | At the end of the prefix, the stream sample is exactly the prefix’s distinct-value set. |
| `GenLimit.NoisyExamples.sequenceSample_card_of_injective` | theorem; finite-set helper | An injective length-`n` finite sequence has exactly `n` distinct values. |
| `GenLimit.NoisyExamples.sample_prefixThen_card_of_le` | theorem; finite-prefix helper | For an injective prefix of length `n`, every initial time `d≤n` has exactly `d` distinct observations. |
| `GenLimit.NoisyExamples.sequenceSample_equivFin_symm` | theorem; finite enumeration bridge | Enumerating a finite set through its canonical equivalence with `Fin S.card` recovers that set. |
| `GenLimit.NoisyExamples.equivFin_symm_value_injective` | theorem; finite enumeration bridge | The value map from the inverse canonical finite-set equivalence is injective. |
| `GenLimit.NoisyExamples.sequenceSample_equivFinOfCardEq_symm` | theorem; finite enumeration bridge | A cardinality-adjusted canonical enumeration of `S` has distinct-value set exactly `S`. |
| `GenLimit.NoisyExamples.finiteNoise_prefixThen` | theorem; noise bridge | A finite prefix followed by a tail value in `L` has finite noise relative to `L`. |
| `GenLimit.NoisyExamples.finite_commonIntersection_defeats_threshold` | theorem; substantive adversarial lemma | Under an infinite universe and UUS, a finite common intersection defeats any proposed generator and exact uniform threshold on some finite-noise stream. |
| `GenLimit.NoisyExamples.uniform_noiseIndependent_implies_infinite_commonIntersection` | theorem; substantive direction | Under an infinite universe and UUS, uniform noise-independent generatability forces the common intersection to be infinite. |
| `GenLimit.NoisyExamples.theorem_3_1` | theorem; numbered characterization wrapper | Under countability, infinitude of `α`, and UUS, uniform noise-independent generatability is equivalent to infinitude of the common intersection. |

### 11.2 `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`
| Exact source-level Lean declaration | Declaration kind / role | Faithful statement-level content |
|---|---|---|
| `GenLimit.NoisyExamples.positivePart` | def; definition | The finite subset of `S` lying in `L`. |
| `GenLimit.NoisyExamples.negativePart` | def; definition | The finite subset of `S` lying outside `L`. |
| `GenLimit.NoisyExamples.noisyVersionSpace` | def; core definition | The languages `L∈H` satisfying `S.card ≤ positivePart(S,L).card + n`, equivalently at most `n` distinct disagreements with `S`. |
| `GenLimit.NoisyExamples.noisyCommonCore` | def; core definition | The intersection of all languages in the noisy version space. |
| `GenLimit.NoisyExamples.noisyClosure` | def; option-valued definition | Returns the noisy common core when the noisy version space is nonempty and `none` otherwise. |
| `GenLimit.NoisyExamples.noisyClosure_eq_none_iff` | theorem; restatement | `noisyClosure H S n = none` exactly when the noisy version space is empty. |
| `GenLimit.NoisyExamples.noisyClosure_eq_some_iff` | theorem; restatement | `noisyClosure H S n = some C` exactly when the version space is nonempty and `C` is the noisy common core. |
| `GenLimit.NoisyExamples.noisyCommonCore_subset_of_mem_versionSpace` | theorem; set-theoretic bridge | The noisy common core is contained in each language belonging to the noisy version space. |
| `GenLimit.NoisyExamples.NoisyClosureWitnessAt` | def; core definition | There is a finite set of exact size `d` with nonempty level-`n` noisy version space and finite noisy common core. |
| `GenLimit.NoisyExamples.FiniteNoisyClosureDimensionAt` | def; core definition | There is a bound beyond which no exact-size level-`n` noisy-closure witness exists. |
| `GenLimit.NoisyExamples.noisyClosureWitnessAt_iff_injective_sequence` | theorem; encoding equivalence | The finite-set witness predicate is equivalent to an injective `Fin d → α` presentation with the same nonempty-space and finite-core conditions. |
| `GenLimit.NoisyExamples.finiteNoisyClosureDimensionAt_iff_eventually_infinite` | theorem; substantive reformulation | Finite level-`n` dimension is equivalent to all sufficiently large finite samples with nonempty noisy version space having infinite noisy core. |
| `GenLimit.NoisyExamples.HasNoiseAtMost` | def; core definition | The exact set of off-target time indices is a finite set of cardinality at most `n`. |
| `GenLimit.NoisyExamples.hasNoiseAtMost_mono` | theorem; noise monotonicity | A stream with noise at most `m` also has noise at most any `n≥m`. |
| `GenLimit.NoisyExamples.bad_sample_card_le_noise` | theorem; occurrence-to-distinct bridge | At most `n` noisy occurrences imply at most `n` distinct off-target values in every finite sample. |
| `GenLimit.NoisyExamples.target_mem_noisyVersionSpace` | theorem; version-space bridge | A target in `H` under at most `n` noisy occurrences belongs to every level-`n` noisy version space of the observed sample. |
| `GenLimit.NoisyExamples.negativePart_card_le_of_mem_noisyVersionSpace` | theorem; restatement | Membership in a level-`n` noisy version space implies at most `n` distinct negative sample values. |
| `GenLimit.NoisyExamples.hasNoiseAtMost_prefixThen` | theorem; adversarial-stream bridge | An injective finite prefix followed by a positive constant tail has bounded occurrence noise when the prefix has at most `n` distinct negatives. |
| `GenLimit.NoisyExamples.IsUniformNoiseDependentGenerator` | def; core definition | One generator satisfies: for every `n` there is a target-independent threshold working for all targets and streams with at most `n` noisy occurrences. |
| `GenLimit.NoisyExamples.UniformNoiseDependentGeneratable` | def; core definition | There exists a generator satisfying `IsUniformNoiseDependentGenerator`. |
| `GenLimit.NoisyExamples.noisyClosureBound` | def; noncomputable witness selection | Chooses one eventual large-sample bound from each finite noisy-closure-dimension proof. |
| `GenLimit.NoisyExamples.noisyClosureBound_spec` | theorem; choice specification | Above the chosen bound, every nonempty noisy version space has infinite noisy core. |
| `GenLimit.NoisyExamples.eligibleNoiseLevels` | def; strategy definition | At history set `S` and time `t`, retains levels `n≤t` whose chosen bound is below `card(S)` and whose noisy version space is nonempty. |
| `GenLimit.NoisyExamples.mem_eligibleNoiseLevels_iff` | theorem; definition restatement | Characterizes membership in the finite eligible-level set by the three displayed inequalities/nonemptiness conditions. |
| `GenLimit.NoisyExamples.selectedNoiseLevel` | def; strategy definition | Chooses the maximum eligible noise level, assuming eligibility is nonempty. |
| `GenLimit.NoisyExamples.selectedNoiseLevel_mem` | theorem; selection specification | The selected maximum is eligible. |
| `GenLimit.NoisyExamples.le_selectedNoiseLevel` | theorem; selection specification | Every eligible level is at most the selected maximum. |
| `GenLimit.NoisyExamples.freshFromNoisyCore` | def; noncomputable construction | Chooses a point in an infinite noisy common core outside the finite sample. |
| `GenLimit.NoisyExamples.freshFromNoisyCore_spec` | theorem; construction specification | The chosen point lies in the noisy core minus the sample. |
| `GenLimit.NoisyExamples.noisyClosureStrategyOutput` | def; strategy construction | Outputs a fresh point from the core at the largest eligible level, or an arbitrary fallback if no level is eligible. |
| `GenLimit.NoisyExamples.noisyClosureStrategyOutput_spec` | theorem; strategy specification | When eligibility is nonempty, the history-level output lies in the selected noisy core outside the sample. |
| `GenLimit.NoisyExamples.noisyClosureStrategy` | def; generator construction | Applies the history-level noisy-closure strategy to the finite sequence’s distinct-value set. |
| `GenLimit.NoisyExamples.noisyClosureStrategy_output` | theorem; execution bridge | Running the generator on a stream equals the strategy output evaluated on the current distinct sample. |
| `GenLimit.NoisyExamples.finite_noisyClosureDimensions_imply_uniform_noiseDependent` | theorem; substantive direction | Finite noisy closure dimension at every level yields one uniform noise-dependent generator. |
| `GenLimit.NoisyExamples.arbitrarily_large_witness_of_not_finiteNoisyClosureDimensionAt` | theorem; logical reformulation | Negating finite level-`n` dimension yields a witness of some size larger than every proposed bound. |
| `GenLimit.NoisyExamples.nonfinite_noisyClosureDimension_defeats_threshold` | theorem; substantive adversarial lemma | Under UUS, nonfinite level-`n` dimension defeats any proposed generator and exact threshold on a stream with at most `n` noisy occurrences. |
| `GenLimit.NoisyExamples.uniform_noiseDependent_implies_finite_noisyClosureDimensions` | theorem; substantive direction | Under UUS, uniform noise-dependent generatability forces finite noisy closure dimension at every level. |
| `GenLimit.NoisyExamples.theorem_3_3` | theorem; numbered characterization wrapper | Under countability, nonemptiness, and UUS, uniform noise-dependent generation is equivalent to finite noisy closure dimension at every noise level. |

### 11.3 `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformDefinitions.lean`
| Exact source-level Lean declaration | Declaration kind / role | Faithful statement-level content |
|---|---|---|
| `GenLimit.NoisyExamples.IsNonuniformNoiseDependentGenerator` | def; core definition | For every noise budget and every target, a target- and budget-dependent threshold works uniformly over all streams within that budget. |
| `GenLimit.NoisyExamples.NonuniformNoiseDependentGeneratable` | def; core definition | There exists one generator satisfying the non-uniform noise-dependent quantifier order. |
| `GenLimit.NoisyExamples.NoisyPresentation` | def; core definition | Every target element appears in the stream, and the set of off-target time indices is finite. |
| `GenLimit.NoisyExamples.IsNoisyLimitGenerator` | def; core definition | On every noisy presentation of every target in `H`, the generator is correct at all sufficiently late times. |
| `GenLimit.NoisyExamples.NoisilyGeneratableInLimit` | def; core definition | There exists an `IsNoisyLimitGenerator`. |
| `GenLimit.NoisyExamples.noisyPresentation_range_infinite` | theorem; presentation bridge | A noisy presentation of an infinite target has infinite stream range. |
| `GenLimit.NoisyExamples.exists_sample_card_eq_of_range_infinite` | theorem; crossing lemma | A stream with infinite range reaches every exact finite distinct-sample cardinality. |
| `GenLimit.NoisyExamples.hasFiniteNoise_of_hasNoiseAtMost` | theorem; noise bridge | A bounded-noise stream has finite noise. |
| `GenLimit.NoisyExamples.exists_hasNoiseAtMost_of_hasFiniteNoise` | theorem; noise bridge | Every finite-noise stream has some finite occurrence-noise bound. |
| `GenLimit.NoisyExamples.uniform_noiseDependent_implies_nonuniform_noiseDependent` | theorem; hierarchy implication | Uniform noise-dependent generation implies its target-dependent non-uniform version. |
| `GenLimit.NoisyExamples.nonuniform_noiseDependent_implies_noisy_limit` | theorem; hierarchy implication | Under UUS, non-uniform noise-dependent generation implies noisy generation in the limit. |

### 11.4 `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteClasses.lean`
| Exact source-level Lean declaration | Declaration kind / role | Faithful statement-level content |
|---|---|---|
| private `classCore` | def; private definition | The intersection of all languages in an arbitrary subclass `V`. |
| private `noisyCommonCore_eq_classCore` | theorem; private definitional bridge | Identifies the noisy common core with `classCore` of the noisy version space. |
| private `finite_class_has_core_bound` | theorem; private combinatorial lemma | A finite class admits one cardinality bound for every finite core arising from any subclass. |
| `GenLimit.NoisyExamples.noisy_witness_card_le_for_finite_class` | theorem; substantive quantitative lemma | Given such a core bound `B`, a finite noisy core forces `card(S) ≤ B + card(H)·n`. |
| `GenLimit.NoisyExamples.finite_class_has_finite_noisyClosureDimensionAt` | theorem; substantive combinatorial result | Every finite language class has finite noisy closure dimension at each fixed noise level. |
| `GenLimit.NoisyExamples.corollary_3_4` | theorem; numbered corollary wrapper | Under countability, nonemptiness, and UUS, every finite class is uniformly noise-dependent generatable. |

### 11.5 `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`
| Exact source-level Lean declaration | Declaration kind / role | Faithful statement-level content |
|---|---|---|
| `GenLimit.NoisyExamples.diagonalNoisyClosureBound` | def; noncomputable witness selection | For each index `i`, chooses an eventual bound for the level-`i` noisy closure dimension of class `classes i`. |
| `GenLimit.NoisyExamples.diagonalNoisyClosureBound_spec` | theorem; choice specification | Above the selected diagonal bound, a nonempty level-`i` version space has infinite core. |
| `GenLimit.NoisyExamples.diagonalEligibleIndices` | def; strategy definition | At history `S,t`, retains indices `i≤t` that are beyond their diagonal bound and have nonempty level-`i` noisy version space. |
| `GenLimit.NoisyExamples.mem_diagonalEligibleIndices_iff` | theorem; definition restatement | Characterizes diagonal eligibility by time, bound, and nonemptiness conditions. |
| `GenLimit.NoisyExamples.selectedDiagonalIndex` | def; strategy definition | Chooses the maximum diagonal-eligible index. |
| `GenLimit.NoisyExamples.selectedDiagonalIndex_mem` | theorem; selection specification | The selected diagonal index is eligible. |
| `GenLimit.NoisyExamples.le_selectedDiagonalIndex` | theorem; selection specification | Every eligible diagonal index is at most the selected maximum. |
| `GenLimit.NoisyExamples.diagonalNoisyStrategyOutput` | def; strategy construction | Outputs a fresh point from the selected component’s selected-level noisy core, or a fallback if no index is eligible. |
| `GenLimit.NoisyExamples.diagonalNoisyStrategyOutput_spec` | theorem; strategy specification | With a nonempty eligible set, the output lies in the selected noisy core outside the sample. |
| `GenLimit.NoisyExamples.diagonalNoisyStrategy` | def; generator construction | Applies the diagonal history-level strategy to each finite history’s distinct-value set. |
| `GenLimit.NoisyExamples.diagonalNoisyStrategy_output` | theorem; execution bridge | Running the diagonal generator on a stream equals the strategy output on the current sample. |
| `GenLimit.NoisyExamples.lemma_3_6` | theorem; numbered sufficient condition | A nondecreasing cover with finite level-`i` noisy closure dimension for component `i` yields non-uniform noise-dependent generation. |
| private `fixed_noise_generator_implies_finite_dimension` | theorem; private converse interface | A fixed generator and exact threshold that work at noise level `n` on a UUS class force finite level-`n` noisy closure dimension. |
| `GenLimit.NoisyExamples.lemma_3_8` | theorem; numbered necessary condition | Non-uniform noise-dependent generation yields, for each fixed `n`, a possibly `n`-dependent nondecreasing cover whose every component has finite level-`n` dimension. |
| `GenLimit.NoisyExamples.corollary_3_7` | theorem; numbered corollary wrapper | A countable UUS class over a countable nonempty type is both non-uniformly noise-dependent generatable and noisily generatable in the limit. |

### 11.6 `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`
| Exact source-level Lean declaration | Declaration kind / role | Faithful statement-level content |
|---|---|---|
| `GenLimit.NoisyExamples.nonuniform_generator_correct_on_finite_history` | theorem; substantive bridge | A target-specific ordinary threshold guarantee on all positive streams implies correctness of `Q` on any finite positive history containing at least that many distinct values. |
| `GenLimit.NoisyExamples.iteratedGeneratorHistory` | def; construction | Starting from a base list, repeatedly appends the output of `Q` on the entire list accumulated so far. |
| `GenLimit.NoisyExamples.iteratedGeneratorHistory_zero` | theorem; definitional restatement | Zero iterations return the base list. |
| `GenLimit.NoisyExamples.iteratedGeneratorHistory_succ` | theorem; definitional restatement | One more iteration appends one new call to `Q` after the previous iterations. |
| `GenLimit.NoisyExamples.iteratedGeneratorHistory_length` | theorem; construction invariant | After `j` iterations, list length is base length plus `j`. |
| `GenLimit.NoisyExamples.iteratedGeneratorHistory_properties` | theorem; substantive invariant | Past the ordinary threshold on a positive base, every iterated history remains positive, contains the base, and gains exactly one distinct point per iteration. |
| `GenLimit.NoisyExamples.balancedSuffixIndices` | def; auxiliary suffix definition | Indices whose suffix retains enough distinct values that total distinct count is at most twice the suffix distinct count. |
| `GenLimit.NoisyExamples.mem_balancedSuffixIndices_iff` | theorem; definition restatement | Characterizes membership in the balanced-suffix index set. |
| `GenLimit.NoisyExamples.balancedSuffixIndices_nonempty` | theorem; existence helper | The balanced-suffix index set is nonempty. |
| `GenLimit.NoisyExamples.balancedSuffixStart` | def; auxiliary suffix construction | The largest balanced-suffix start index. |
| `GenLimit.NoisyExamples.balancedSuffixStart_mem` | theorem; selection specification | The selected balanced start is balanced. |
| `GenLimit.NoisyExamples.balancedSuffixStart_le_length` | theorem; boundary helper | The balanced start does not exceed history length. |
| `GenLimit.NoisyExamples.balancedSuffixStart_balance` | theorem; balance invariant | The selected suffix has at least half the total distinct count in the multiplicative inequality sense. |
| `GenLimit.NoisyExamples.le_balancedSuffixStart` | theorem; maximality helper | Every balanced index is at most the selected start. |
| private `history_toFinset_eq_take_union_drop` | theorem; private list/set bridge | The history’s distinct-value set is the union of the prefix and suffix distinct-value sets. |
| `GenLimit.NoisyExamples.history_card_le_start_add_suffix` | theorem; cardinality helper | Total distinct count is at most the discarded-position count plus the suffix distinct count. |
| `GenLimit.NoisyExamples.start_le_balancedSuffixStart_of_large` | theorem; suffix-location lemma | If total distinct count is at least `2r`, the selected balanced suffix starts no earlier than `r`. |
| private `exists_drop_toFinset_card_eq` | theorem; private crossing lemma | For every `k` up to the history’s distinct count, some suffix has exactly `k` distinct values. |
| `GenLimit.NoisyExamples.paperBalancedSuffixIndices` | def; core suffix definition | Indices whose suffix has exactly floor one-half of the full distinct count. |
| `GenLimit.NoisyExamples.mem_paperBalancedSuffixIndices_iff` | theorem; definition restatement | Characterizes exact-floor suffix indices. |
| `GenLimit.NoisyExamples.paperBalancedSuffixIndices_nonempty` | theorem; existence helper | An exact-floor suffix index always exists. |
| `GenLimit.NoisyExamples.paperBalancedSuffixStart` | def; core suffix construction | The largest start index whose suffix has exactly floor one-half of the full distinct count. |
| `GenLimit.NoisyExamples.paperBalancedSuffixStart_mem` | theorem; selection specification | The selected exact-floor start belongs to the candidate set. |
| `GenLimit.NoisyExamples.paperBalancedSuffixStart_le_length` | theorem; boundary helper | The exact-floor start does not exceed history length. |
| `GenLimit.NoisyExamples.paperBalancedSuffixStart_card` | theorem; cardinality specification | The selected suffix has exactly floor one-half of the full distinct count. |
| `GenLimit.NoisyExamples.le_paperBalancedSuffixStart` | theorem; maximality helper | Every exact-floor candidate start is at most the selected start. |
| `GenLimit.NoisyExamples.start_le_paperBalancedSuffixStart_of_large` | theorem; suffix-location lemma | If total distinct count is at least `2r`, the exact-floor suffix starts no earlier than `r`. |
| `GenLimit.NoisyExamples.finiteNoiseCutoff` | def; noncomputable definition | One plus the supremum of the finite set of noisy time indices. |
| `GenLimit.NoisyExamples.mem_target_after_finiteNoiseCutoff` | theorem; cutoff specification | Every stream value at or after the cutoff lies in the target. |
| `GenLimit.NoisyExamples.balanced_suffix_positive_after_cutoff` | theorem; suffix positivity bridge | Any suffix starting at or after the finite-noise cutoff contains only target values. |
| `GenLimit.NoisyExamples.generatedCandidateSet` | def; construction | The distinct values added by iterating `Q`, with the base distinct values removed. |
| `GenLimit.NoisyExamples.generatedCandidateSet_card` | theorem; candidate invariant | Under a positive base past threshold, `count` iterations produce exactly `count` candidate values. |
| `GenLimit.NoisyExamples.generatedCandidateSet_positive` | theorem; candidate invariant | Under the same conditions, every candidate lies in the target. |
| `GenLimit.NoisyExamples.generatedCandidateSet_disjoint_base` | theorem; set-difference restatement | The generated candidate set is disjoint from the base distinct-value set. |
| `GenLimit.NoisyExamples.generatedCandidate_not_in_history` | theorem; pigeonhole interface | With `r+1` candidates and a suffix formed by dropping `r` positions, at least one candidate is absent from the full history. |
| `GenLimit.NoisyExamples.robustifiedNoiselessGenerator` | def; alternate construction | Uses the inequality-balanced suffix and chooses a generated candidate absent from the full observed history, with fallback otherwise. |
| `GenLimit.NoisyExamples.robustifiedNoiselessGenerator_correct` | theorem; local correctness specification | If that balanced suffix is positive and past threshold, the alternate robustified output is a fresh target point. |
| `GenLimit.NoisyExamples.paperRobustifiedNoiselessGenerator` | def; core construction | Uses the exact-floor suffix and chooses a generated candidate absent from the full observed history, with fallback otherwise. |
| `GenLimit.NoisyExamples.paperRobustifiedNoiselessGenerator_correct` | theorem; local correctness specification | If the exact-floor suffix is positive and past threshold, the robustified output is a fresh target point. |
| `GenLimit.NoisyExamples.eventually_balanced_suffix_positive_and_large` | theorem; eventual invariant | On a noisy presentation of an infinite target, the inequality-balanced suffix is eventually positive and has at least any prescribed distinct size. |
| `GenLimit.NoisyExamples.eventually_paperBalanced_suffix_positive_and_large` | theorem; eventual invariant | The same eventual positivity and size property holds for the exact-floor suffix. |
| `GenLimit.NoisyExamples.theorem_3_9` | theorem; numbered robustification theorem | Under countability and UUS, ordinary non-uniform generatability implies noisy generation in the limit. |

### 11.7 `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteUnionLimit.lean`
| Exact source-level Lean declaration | Declaration kind / role | Faithful statement-level content |
|---|---|---|
| `GenLimit.NoisyExamples.noisyInfiniteSetEquiv` | def; noncomputable enumeration construction | Chooses an equivalence between `ℕ` and an infinite subset of a countable example type. |
| `GenLimit.NoisyExamples.noisyInfiniteEnumeration` | def; noncomputable enumeration | The corresponding repetition-free enumeration of an infinite subset. |
| `GenLimit.NoisyExamples.noisyInfiniteEnumeration_mem` | theorem; enumeration specification | Every enumerated value lies in the subset. |
| `GenLimit.NoisyExamples.noisyInfiniteEnumeration_injective` | theorem; enumeration specification | The enumeration is injective. |
| `GenLimit.NoisyExamples.noisyInfiniteEnumeration_surjective` | theorem; enumeration specification | Every member of the subset appears in the enumeration. |
| `GenLimit.NoisyExamples.noisyEnumeration_misses_finset` | theorem; infinite-set helper | Every finite set misses some value of the infinite enumeration. |
| `GenLimit.NoisyExamples.noisyEnumerationProgress` | def; progress definition | The least enumeration index whose value is absent from the current finite sample. |
| `GenLimit.NoisyExamples.noisyEnumerationProgress_spec` | theorem; progress specification | The value at the progress index is absent from the sample. |
| `GenLimit.NoisyExamples.noisy_mem_of_lt_progress` | theorem; progress specification | Every earlier enumerated value is present in the sample. |
| `GenLimit.NoisyExamples.noisy_progress_le_of_not_mem` | theorem; progress upper bound | Any known missing enumeration value bounds progress from above. |
| `GenLimit.NoisyExamples.noisyWinningIndex` | def; finite argmax construction | Chooses a component maximizing enumeration progress, or `none` when there is no component. |
| `GenLimit.NoisyExamples.noisyWinningIndex_spec` | theorem; argmax specification | For a nonempty finite component set, returns a selected component whose progress dominates every component’s progress. |
| `GenLimit.NoisyExamples.finiteUniformUnionNoisyGenerator` | def; generator construction | At each history, selects a maximal-progress component and emits its first unseen common-intersection point, with fallback for no component. |
| private `rangeGoodIndices` | def; private definition | Components whose common intersection is contained in the full stream range. |
| private `mem_rangeGoodIndices_iff` | theorem; private restatement | Characterizes membership in `rangeGoodIndices` by common-intersection containment in the stream range. |
| private `range_bad_obstruction_exists` | theorem; private obstruction lemma | A component not range-good has an enumerated common-intersection point absent from the entire stream range. |
| private `rangeBadObstruction` | def; private noncomputable definition | Chooses the first such permanently absent obstruction index for a bad component, and zero otherwise. |
| private `rangeBadObstruction_spec` | theorem; private obstruction specification | For a bad component, its selected obstruction value is absent from the stream range. |
| private `component_uus_of_finite_cover` | theorem; private inheritance bridge | A component in a finite cover of a UUS class is itself UUS. |
| `GenLimit.NoisyExamples.theorem_3_10` | theorem; numbered finite-union theorem | Under countability, infinitude, and UUS, a finite cover by uniformly noise-independent generatable classes is noisily generatable in the limit. |

### 11.8 `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Separation.lean`
| Exact source-level Lean declaration | Declaration kind / role | Faithful statement-level content |
|---|---|---|
| `GenLimit.NoisyExamples.SeparationPoint` | abbrev; example universe abbreviation | The concrete type `ℕ × Option ℕ`. |
| `GenLimit.NoisyExamples.primePoint` | def; example encoding | The point `(p, none)`. |
| `GenLimit.NoisyExamples.powerPoint` | def; example encoding | The point `(p, some n)`. |
| `GenLimit.NoisyExamples.separationLanguage` | def; example language | The set of points whose first coordinate differs from `p`. |
| `GenLimit.NoisyExamples.separationClass` | def; example class | The range of the family `p ↦ separationLanguage p`. |
| `GenLimit.NoisyExamples.separationClass_countable` | theorem; example property | The explicit class is countable. |
| `GenLimit.NoisyExamples.separationLanguage_infinite` | theorem; example property | Every explicit member language is infinite. |
| `GenLimit.NoisyExamples.separationClass_uus` | theorem; example property | The explicit class satisfies UUS. |
| `GenLimit.NoisyExamples.separation_commonCore_infinite` | theorem; ordinary-core property | Every nonempty finite positive sample has infinite ordinary common core for the explicit class. |
| `GenLimit.NoisyExamples.separation_hasClosureDimension_zero` | theorem; ordinary-dimension property | The explicit class has imported ordinary closure dimension zero. |
| `GenLimit.NoisyExamples.separationPrimeSample` | def; example finite sample | The distinct set obtained from the first `d` prime-tag points `(i,none)`. |
| `GenLimit.NoisyExamples.separationPrimeSample_card` | theorem; example sample property | The prime-tag sample has cardinality exactly `d`. |
| private `separationPrimeSample_negativePart_card_le_one` | theorem; private example helper | Each explicit language omits at most one point of the prime-tag sample. |
| `GenLimit.NoisyExamples.separationLanguage_mem_oneNoisyVersionSpace` | theorem; example version-space property | Every explicit language lies in the level-one noisy version space of every prime-tag sample. |
| `GenLimit.NoisyExamples.separation_oneNoisyVersionSpace_eq` | theorem; example identity | That level-one noisy version space is the entire explicit class. |
| `GenLimit.NoisyExamples.separation_oneNoisyCommonCore_eq_empty` | theorem; example core identity | The corresponding level-one noisy common core is empty. |
| `GenLimit.NoisyExamples.separation_oneNoisyWitness_every_card` | theorem; substantive example property | For every `d`, the explicit class has a level-one noisy-closure witness of exact size `d`. |
| `GenLimit.NoisyExamples.InfiniteNoisyClosureDimensionAt` | def; definition | Every finite cardinality is realized by an exact noisy-closure witness at the specified level. |
| `GenLimit.NoisyExamples.separationClass_properties` | theorem; packaged example theorem | Packages countability, UUS, ordinary dimension zero, and exact-every-size level-one noisy witnesses. |
| `GenLimit.NoisyExamples.lemma_3_5` | theorem; numbered existential wrapper | There exists a class over the concrete tagged universe with those four properties. |
| `GenLimit.NoisyExamples.separation_not_uniform_noiseDependent` | theorem; generation-level separation | The explicit class is not uniformly noise-dependent generatable. |

### 11.9 `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/AlternatePositive.lean`
| Exact source-level Lean declaration | Declaration kind / role | Faithful statement-level content |
|---|---|---|
| `GenLimit.NoisyExamples.IsAlternateUniformNoiseIndependentGeneratorAt` | def; core definition | Uses finite noise but triggers when exactly `d` distinct observed values lie in the target. |
| `GenLimit.NoisyExamples.AlternateUniformNoiseIndependentGeneratable` | def; core definition | There exist one generator and one global positive-observation threshold. |
| `GenLimit.NoisyExamples.BoundedNoisyClosureExcess` | def; core combinatorial definition | One constant `B` bounds every level-`n` witness size `k` by `k≤n+B`. |
| `GenLimit.NoisyExamples.positivePart_mono` | theorem; finite-set monotonicity | Positive parts are monotone under inclusion of finite samples. |
| private `positive_sample_card_step` | theorem; private crossing helper | Adding one stream observation increases the distinct-positive count by at most one. |
| `GenLimit.NoisyExamples.exists_earlier_positive_sample_card_eq` | theorem; crossing lemma | If a prefix has at least `d` distinct positive values, an earlier prefix has exactly `d`. |
| `GenLimit.NoisyExamples.excessNoisyClosureStrategyOutput` | def; strategy construction | At sample `S`, uses level `card(S)-(B+1)` and chooses a fresh point from its infinite noisy core, with fallback otherwise. |
| `GenLimit.NoisyExamples.excessNoisyClosureStrategyOutput_spec` | theorem; strategy specification | When that core is infinite, the output lies in it outside `S`. |
| `GenLimit.NoisyExamples.excessNoisyClosureStrategy` | def; generator construction | Applies the excess-based history-level output to the finite history’s distinct sample. |
| `GenLimit.NoisyExamples.excessNoisyClosureStrategy_output` | theorem; execution bridge | Running the excess strategy on a stream equals its output on the current sample. |
| `GenLimit.NoisyExamples.boundedNoisyClosureExcess_implies_alternateUniform` | theorem; substantive direction | Bounded witness excess yields alternate uniform noise-independent generation. |
| `GenLimit.NoisyExamples.noisyExcessWitness_defeats_alternate_threshold` | theorem; substantive adversarial lemma | A witness of size `k>n+d` defeats any proposed positive-observation threshold `d`. |
| `GenLimit.NoisyExamples.alternateUniform_implies_boundedNoisyClosureExcess` | theorem; substantive direction | Alternate uniform noise-independent generation forces bounded witness excess. |
| `GenLimit.NoisyExamples.theorem_C_3` | theorem; numbered characterization wrapper | Under countability, nonemptiness, and UUS, alternate uniform noise-independent generation is equivalent to bounded noisy-closure excess. |
| `GenLimit.NoisyExamples.lemma_C_2` | theorem; numbered obstruction theorem | If removing one language changes a finite common intersection into an infinite one, the ambient UUS class is not alternate uniformly noise-independent generatable. |

### 11.10 `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformIndependent.lean`
| Exact source-level Lean declaration | Declaration kind / role | Faithful statement-level content |
|---|---|---|
| `GenLimit.NoisyExamples.IsNonuniformNoiseIndependentGenerator` | def; core definition | For each target there is a positive-observation threshold independent of the amount and placement of finite noise. |
| `GenLimit.NoisyExamples.NonuniformNoiseIndependentGeneratable` | def; core definition | There exists one generator satisfying that target-dependent quantifier order. |
| `GenLimit.NoisyExamples.evenLanguage` | def; example language | The set of even natural numbers. |
| `GenLimit.NoisyExamples.oddLanguage` | def; example language | The set of odd natural numbers. |
| `GenLimit.NoisyExamples.parityClass` | def; example class | The two-language class containing the even and odd languages. |
| `GenLimit.NoisyExamples.evenLanguage_infinite` | theorem; example property | The even language is infinite. |
| `GenLimit.NoisyExamples.oddLanguage_infinite` | theorem; example property | The odd language is infinite. |
| `GenLimit.NoisyExamples.parityClass_finite` | theorem; example property | The parity class is finite. |
| `GenLimit.NoisyExamples.parityClass_uus` | theorem; example property | The parity class satisfies UUS. |
| `GenLimit.NoisyExamples.identityPrefixStream` | def; adversarial stream construction | Agrees with the identity enumeration before time `p` and uses a supplied tail thereafter. |
| `GenLimit.NoisyExamples.sample_identityPrefixStream_of_le` | theorem; sample specification | Before or at the boundary `p`, its sample at time `q≤p` is `Finset.range q`. |
| `GenLimit.NoisyExamples.output_identityPrefixStream_boundary` | theorem; execution bridge | At time `p`, generator output depends on the common identity prefix and equals the finite-history call on `i↦i`. |
| `GenLimit.NoisyExamples.finiteNoise_identityPrefixStream` | theorem; noise specification | If every tail value lies in `L`, the identity-prefix stream has finite noise relative to `L`. |
| `GenLimit.NoisyExamples.positivePart_range_even_card` | theorem; counting helper | Among `0,…,2d-1`, exactly `d` distinct values are even. |
| `GenLimit.NoisyExamples.positivePart_range_odd_card` | theorem; counting helper | Among `0,…,2d-1`, exactly `d` distinct values are odd. |
| private `naturalPrefixOutput` | def; private abbreviation | The generator output on the length-`p` identity history. |
| `GenLimit.NoisyExamples.parityClass_not_nonuniform_noiseIndependent` | theorem; substantive counterexample theorem | Packages finiteness, UUS, and failure of non-uniform noise-independent generatability for the parity class. |
| `GenLimit.NoisyExamples.lemma_D_2` | theorem; numbered existential wrapper | There exists a finite UUS class over `ℕ` that is not non-uniformly noise-independent generatable. |

### 11.11 Umbrella module

`GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples.lean` contains imports only. It introduces no definition, theorem, lemma, structure, abbreviation, or axiom.

### 11.12 Inventory classification summary

- The principal numbered or packaged results are wrappers around separately declared directions, corollaries, sufficient/necessary cover statements, robustification theorems, and explicit counterexamples.
- Construction definitions and their `_spec`, `_output`, membership, maximality, and cardinality lemmas are infrastructure supporting those results; they are not independent paper-level characterizations.
- The separation and parity declarations are concrete examples/counterexamples, not generic characterizations.
- There are no axioms and no primary theorem that is merely an alias of another theorem. Several numbered declarations are wrappers combining previously declared directions.

---

## Executive summary

The Lean statements formalize adversarial deterministic generation from noisy histories. Their strongest generic characterizations are: (i) uniform noise-independent generation exactly when the class-wide intersection is infinite, on a countably infinite universe under UUS; (ii) uniform noise-dependent generation exactly when every fixed noise level has only bounded-size finite-core noisy witnesses, on a countable nonempty universe under UUS; and (iii) the positive-count uniform variant exactly when witness size exceeds noise level by a uniformly bounded amount. Finite classes satisfy the noise-dependent criterion, countable classes satisfy a non-uniform and noisy-limit conclusion, and two explicit constructions separate stronger noise-independent notions.

The key formal cautions are equally important. Noise is counted by bad time occurrences in stream assumptions but by distinct bad values in closure conditions. Threshold obligations trigger only at exact distinct-cardinality equalities and can be vacuous on admissible streams with too small a range. Generators have no target, noise-budget, class-index, membership-oracle, or computability input; the main positive results do not establish effective witnesses, and many key generator constructions are explicitly noncomputable. The non-uniform cover lemmas do not give a matching iff, and no converse is proved for either robustification theorem.

**Confirmed output filename:** `06-generation-from-noisy-examples-lean-statement-reconstruction.md`
