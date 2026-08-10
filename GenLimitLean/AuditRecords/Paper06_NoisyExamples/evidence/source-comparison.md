
# 06 — Paper06_GenerationFromNoisyExamples — Generation from Noisy Examples — Stage 2 Faithfulness Audit

## 0. Audited evidence and readability verification

This Stage 2 audit compares only the following supplied evidence:

1. **Author source:** `06-2501.04179v2.pdf`, exact arXiv version `2501.04179v2`, 374168 bytes, SHA-256  
   `95c02ce2bd069b4fdf9a6b70d81763d9f9a49d65063f5141017b4474a71ad059`.
2. **Lean source bundle:** `06__Paper06_GenerationFromNoisyExamples__lean-source-bundle.txt`, 18 files, 225002 bytes, SHA-256  
   `430635a4daf50622b55ca7e711735e48cb2e600d35f8b93025ad68233db794a3`.
3. **Stage-1 intermediary:** `06-generation-from-noisy-examples-lean-statement-reconstruction.md`.

The PDF hash and byte size match the supplied provenance. It is an unencrypted 15-page PDF with title *Generation from Noisy Examples* and authors Ananth Raman and Vinod Raman. All 15 pages rendered successfully, the title page and the theorem/appendix pages are visually legible, and text extraction produced coherent mathematical text. The PDF is therefore readable and suitable for audit. No web source or substitute version was used.

For Lean, the semantic evidence is declaration signatures and statement-relevant definition bodies in the attached bundle. The audit does **not** use Lean comments/docstrings, declaration names, filenames, or proof bodies as evidence for the mathematical truth of a claim. Paths and names are reported only to identify source declarations. This is a statement-faithfulness audit; it does not certify compilation or proof correctness.

## 1. Overall verdict

**Overall paper-level verdict: substantially faithful at the qualitative theorem level, but not a literal transcription.**

Every numbered new theorem, lemma, and corollary in the paper has a clear Lean counterpart at the level of its main qualitative conclusion. The strongest matches are Definitions 2.4–2.7, Lemma 3.8, Theorem 3.9, Lemma C.2, and the displayed Definition D.1. Several other results are formalized as **faithful specializations** that add `Nonempty α` or `Infinite α`, or fix a concrete countably infinite universe. Those added assumptions repair genuine degenerate cases in the printed statements: empty classes over empty or finite example spaces can otherwise make the paper's equivalences or existential claims false.

The main limitations are:

- Lean does not define a numerical extended-natural quantity `NC_n(H)`. It formalizes witness predicates and boundedness instead. Thus the qualitative finiteness characterizations are captured, but the paper's exact or asymptotic sample-complexity claims around Theorem 3.3 and the bound `NC_n(H_i) < i` in the proof of Lemma 3.8 are not stated.
- The paper's preliminary noisy version-space notation is duplicate-sensitive if read literally, whereas Lean uses the set of distinct observations. This is a mathematically sensible repair consistent with the paper's stated distinct-example sample complexity.
- The literal Algorithm 1 is not reproduced extensionally: Lean totalizes the exact-half suffix choice when the required suffix is empty and chooses an arbitrary fresh generated candidate rather than the first one. Theorem 3.9 itself is faithful.
- The paper is internally inconsistent about Definition D.1: page 11 says it counts all distinct examples, while the displayed definition and the proof of Lemma D.2 on page 13 count distinct positive examples. Lean follows the displayed definition and proof.
- No main result is circular, conclusion-encoding, or collapsed to a tautology. Exact-cardinality triggers can nevertheless make the generation predicates vacuous on admissible streams that never reach the threshold; this feature is present in both paper and Lean.

## 2. Paper result inventory

The paper's new formal objects and main mathematical results are:

| Paper item | Content | PDF location |
|---|---|---|
| Assumption 2.1 | Every target support is infinite (UUS). | p. 4, §2 |
| Definition 2.3 | A generator maps a finite history to one example. | p. 4, §2.1 |
| Definition 2.4 | Uniform noise-independent generatability. | p. 4, §2.1.2 |
| Definition 2.5 | Uniform noise-dependent generatability. | pp. 4–5, §2.1.2 |
| Definition 2.6 | Non-uniform noise-dependent generatability. | p. 5, §2.1.2 |
| Definition 2.7 | Noisy generatability in the limit on noisy enumerations. | p. 5, §2.1.2 |
| Theorem 3.1 | Uniform noise-independent generation iff the class-wide support intersection is infinite. | p. 5, §3.1 |
| Definition 3.2 | Numerical `n`-Noisy Closure dimension `NC_n(H)`. | p. 6, §3.2 |
| Theorem 3.3 | Uniform noise-dependent generation iff `NC_n(H) < ∞` for every noise level. | p. 6, §3.2 |
| Quantitative claim attached to Theorem 3.3 | Lower and upper distinct-sample bounds and sample complexity `Θ(NC_n(H))`. | p. 6, text after Theorem 3.3; Appendix E |
| Corollary 3.4 | Every finite UUS class is uniformly noise-dependent generatable. | p. 6, §3.2 |
| Lemma 3.5 | A countable UUS class has ordinary closure dimension zero but `NC_1(H)=∞`. | pp. 6–7, §3.2 |
| Lemma 3.6 | A single increasing cover with diagonal finite noisy dimensions suffices for non-uniform noise-dependent generation. | p. 7, §3.3; Appendix F |
| Corollary 3.7 | Every countable UUS class is non-uniformly noise-dependent generatable and hence noisily generatable in the limit. | p. 7, §3.3 |
| Lemma 3.8 | For each fixed noise level, non-uniform noise-dependent generation yields a level-dependent increasing cover with finite `NC_n`. | p. 7, §3.3 |
| Quantitative claim in Lemma 3.8's proof | The constructed subclass `H_i` satisfies `NC_n(H_i) < i`. | p. 7, proof of Lemma 3.8 |
| Theorem 3.9 | Noiseless non-uniform generatability implies noisy generatability in the limit. | p. 8, §3.4; Algorithm 1 |
| Theorem 3.10 | A finite union of uniformly noise-independent generatable classes is noisily generatable in the limit. | p. 8, §3.4; Appendix G |
| Definition C.1 | Alternate uniform noise-independent generation, thresholded by distinct positive examples. | p. 11, Appendix C |
| Lemma C.2 | A finite-to-infinite intersection jump after removing one hypothesis obstructs Definition C.1. | p. 12, Appendix C |
| Theorem C.3 | Definition C.1 iff `sup_n (NC_n(H)-n) < ∞`. | p. 12, Appendix C |
| Definition D.1 | Non-uniform noise-independent generation with a target-dependent distinct-positive threshold. | p. 13, Appendix D |
| Lemma D.2 | A finite UUS class need not satisfy Definition D.1. | p. 13, Appendix D |

Definitions A.1–A.3 and results B.2–B.4 on page 11 are recalled prior work. They are used to interpret Theorem 3.9 and Lemma 3.5 but are not counted as new Paper 06 results.

## 3. Formal setting and recursively unfolded Lean definitions

### 3.1 Histories, samples, outputs, and correctness

The dependency interface is:

```lean
abbrev GenLimit.Generic.Generator (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → α

noncomputable def GenLimit.Generic.sample
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Finset α := by
  classical
  exact (Finset.range t).image stream

def GenLimit.Generic.output
    (G : GenLimit.Generic.Generator α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : α :=
  G t (fun i => stream i)

def GenLimit.Generic.CorrectAt
    (G : GenLimit.Generic.Generator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  output G stream t ∈ L ∧ output G stream t ∉ sample stream t
```

Thus the generator sees the **entire ordered finite prefix**, with repetitions and noise locations. The sample used for thresholding and freshness is the finite set of distinct values in that prefix. Correctness means target membership and freshness relative to the observed input prefix only; it does not require outputs at different times to be mutually distinct.

The Lean time `t` is a zero-based prefix length. It corresponds to the paper's output after observing `t` examples, so this is only an indexing shift.

The UUS condition is:

```lean
def GenLimit.LiRamanTewari.UUS
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → L.Infinite
```

It is vacuous for `H = ∅`.

### 3.2 Noise and presentation predicates

```lean
def GenLimit.NoisyExamples.HasFiniteNoise
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  {t | stream t ∉ L}.Finite

def GenLimit.NoisyExamples.HasNoiseAtMost
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) : Prop :=
  ∃ F : Finset ℕ, F.card ≤ n ∧
    ∀ t, t ∈ F ↔ stream t ∉ L

def GenLimit.NoisyExamples.NoisyPresentation
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  L ⊆ Set.range stream ∧ HasFiniteNoise stream L
```

`HasFiniteNoise` and `HasNoiseAtMost` count **bad time occurrences**, not distinct bad values. `NoisyPresentation` additionally requires every target element to occur at least once. It permits repetitions, arbitrary order, and finitely many off-target values/occurrences. Definitions 2.4–2.6 do not require target coverage; Definition 2.7 does.

The bridge declarations [S17] and [S18] establish:

- a bounded bad-position set is finite;
- every finite bad-position set has some finite cardinal bound.

The bridge [S07] is one-way from occurrence noise to distinct-value noise:
\[
\#\bigl(S_t\setminus L\bigr)\le n
\]
whenever the stream has at most `n` off-target occurrences.

### 3.3 Generation notions and exact quantifier dependence

The signatures unfold to the following quantifier orders.

| Notion | Exact Lean quantifiers | Threshold dependence | Stream requirement | Trigger |
|---|---|---|---|---|
| Uniform noise-independent | `∃ G ∃ d ∀ L∈H ∀x, finiteNoise(x,L) → ∀t, |S_t|=d → ∀s≥t, CorrectAt` | class only | finite bad occurrences; no coverage | all distinct observations |
| Uniform noise-dependent | `∃ G ∀n ∃d ∀L∈H ∀x, noise≤n → ∀t, |S_t|=d → ∀s≥t, CorrectAt` | noise level only | at most `n` bad occurrences; no coverage | all distinct observations |
| Non-uniform noise-dependent | `∃ G ∀n ∀L∈H ∃d ∀x, noise≤n → ∀t, |S_t|=d → ∀s≥t, CorrectAt` | noise level and target | at most `n` bad occurrences; no coverage | all distinct observations |
| Noisy limit | `∃ G ∀L∈H ∀x, NoisyPresentation(x,L) → ∃T ∀s≥T, CorrectAt` | convergence time may depend on target and stream | target coverage plus finite bad occurrences | eventual time, not a cardinality trigger |
| Alternate uniform noise-independent | `∃ G ∃d ∀L∈H ∀x, finiteNoise → ∀t, |S_t∩L|=d → ∀s≥t, CorrectAt` | class only | finite bad occurrences | distinct positive observations |
| Non-uniform noise-independent | `∃ G ∀L∈H ∃d ∀x, finiteNoise → ∀t, |S_t∩L|=d → ∀s≥t, CorrectAt` | target only | finite bad occurrences | distinct positive observations |

The exact source definitions are reproduced in Appendix A. In all six notions:

- the generator is chosen before the target and stream;
- it receives neither the target, the true noise budget, nor a bad-position set;
- a target-dependent positive count is a **semantic trigger**, not an oracle available to the generator;
- the condition quantifies over every time at which the exact equality holds;
- if an admissible stream never reaches the exact threshold, its obligation is vacuous.

The paper's wording “if there exists `t*`” is grammatically ambiguous, but its lower-bound proofs negate the condition by quantifying over **every** exact-trigger time (Theorem 3.1, p. 5; Appendix E, p. 14; Lemma C.2, p. 12; Lemma D.2, p. 13). Lean's universal-trigger reading is therefore faithful to what the authors actually prove.

### 3.4 Noisy version spaces, closure, and witness predicates

```lean
def GenLimit.NoisyExamples.noisyVersionSpace
    (H : GenLimit.Generic.LanguageClass α)
    (S : Finset α) (n : ℕ) :
    Set (GenLimit.Generic.Language α) :=
  {L | L ∈ H ∧ S.card ≤ (positivePart S L).card + n}

def GenLimit.NoisyExamples.noisyCommonCore
    (H : GenLimit.Generic.LanguageClass α)
    (S : Finset α) (n : ℕ) :
    GenLimit.Generic.Language α :=
  {x | ∀ L, L ∈ noisyVersionSpace H S n → x ∈ L}

noncomputable def GenLimit.NoisyExamples.noisyClosure
    (H : GenLimit.Generic.LanguageClass α)
    (S : Finset α) (n : ℕ) :
    Option (GenLimit.Generic.Language α) := by
  classical
  exact if (noisyVersionSpace H S n).Nonempty then
    some (noisyCommonCore H S n)
  else none

def GenLimit.NoisyExamples.NoisyClosureWitnessAt
    (H : GenLimit.Generic.LanguageClass α)
    (n d : ℕ) : Prop :=
  ∃ S : Finset α, S.card = d ∧
    (noisyVersionSpace H S n).Nonempty ∧
    (noisyCommonCore H S n).Finite

def GenLimit.NoisyExamples.FiniteNoisyClosureDimensionAt
    (H : GenLimit.Generic.LanguageClass α) (n : ℕ) : Prop :=
  ∃ D : ℕ, ∀ d : ℕ, D < d →
    ¬NoisyClosureWitnessAt H n d
```

Because `S` is a set,
\[
S.card \le |S\cap L|+n
\quad\Longleftrightarrow\quad
|S\setminus L|\le n.
\]
This is distinct-value disagreement. The paper's Definition 3.2 restricts its witnesses to distinct examples, so [S05] is an exact encoding of that witness notion.

The option-valued `noisyClosure` records the paper's bottom case. The bare `noisyCommonCore` is the universal set when the version space is empty, but emptiness cannot create a witness because `NoisyClosureWitnessAt` separately requires a nonempty version space.

The finite-dimension predicate is a boundedness predicate, not a numerical dimension. [S06] states the equivalent large-sample form:
\[
\exists D\ \forall S,\quad
D<|S|\ \land\ V_n(H,S)\ne\varnothing
\ \Longrightarrow\ C_n(H,S)\text{ is infinite}.
\]

A later, separate definition is:

```lean
def GenLimit.NoisyExamples.InfiniteNoisyClosureDimensionAt
    (H : GenLimit.Generic.LanguageClass α) (n : ℕ) : Prop :=
  ∀ d : ℕ, NoisyClosureWitnessAt H n d
```

This requires a witness at **every exact cardinality**, including zero. It is not defined as the negation of `FiniteNoisyClosureDimensionAt`, and no declaration states that the two predicates are complements.

### 3.5 Excess and cover conditions

```lean
def GenLimit.NoisyExamples.BoundedNoisyClosureExcess
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ B : ℕ, ∀ n k : ℕ,
    NoisyClosureWitnessAt H n k → k ≤ n + B

def GenLimit.LiRamanTewari.IsNondecreasingCover
    (H : GenLimit.Generic.LanguageClass α)
    (classes : ℕ → GenLimit.Generic.LanguageClass α) : Prop :=
  Monotone classes ∧ H = ⋃ n, classes n

def GenLimit.LiRamanTewari.IsFiniteCover
    (H : GenLimit.Generic.LanguageClass α) {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α) : Prop :=
  H = ⋃ i, classes i
```

`BoundedNoisyClosureExcess` is the proposition-level form of a uniform upper bound on `NC_n(H)-n`; it neither defines a supremum nor asserts that a largest witness exists. The cover predicates contain no generation conclusion and are independent structural assumptions.

## 4. Bidirectional correspondence: paper to Lean

Each row uses exactly one required correspondence verdict and one required difficulty verdict.

| ID | Paper claim | Paper citation | Lean counterpart | Audit finding | Correspondence verdict | Difficulty verdict |
|---|---|---|---|---|---|---|
| P01 | Generator access model | Definition 2.3, p. 4; notation on p. 3 | `GenLimit.Generic.Generator` | The paper defines `X^*` as finite subsets but immediately calls the input a finite sequence and later uses ordered suffixes and appended generated values. Lean chooses ordered histories with repetitions. | Indeterminate from the supplied evidence | Indeterminate |
| P02 | Uniform noise-independent generation | Definition 2.4, p. 4 | `IsUniformNoiseIndependentGeneratorAt`; `UniformNoiseIndependentGeneratable` | Same one-generator/one-threshold quantifier order, finite bad occurrences, exact distinct-count trigger, and freshness conclusion. Lean's universal trigger matches the paper's lower-bound proofs. | Exact / formally equivalent | Preserved |
| P03 | Uniform noise-dependent generation | Definition 2.5, pp. 4–5 | `IsUniformNoiseDependentGenerator`; `UniformNoiseDependentGeneratable` | One generator is chosen before the noise level; only the threshold depends on `n`; target and stream do not affect it. | Exact / formally equivalent | Preserved |
| P04 | Non-uniform noise-dependent generation | Definition 2.6, p. 5 | `IsNonuniformNoiseDependentGenerator`; `NonuniformNoiseDependentGeneratable` | Threshold depends on `(n,L)` but not on the stream; generator does not receive `n` or `L`. | Exact / formally equivalent | Preserved |
| P05 | Noisy generation in the limit | Definition 2.7, p. 5 | `NoisyPresentation`; `IsNoisyLimitGenerator`; `NoisilyGeneratableInLimit` | Same coverage requirement, finite off-target occurrences, stream-dependent convergence time, and stream-relative freshness. | Exact / formally equivalent | Preserved |
| P06 | Uniform noise-independent characterization | Theorem 3.1, p. 5 | `GenLimit.NoisyExamples.theorem_3_1` [S04] | Lean adds `[Infinite α]`. This is redundant for a nonempty UUS class but repairs the empty-class finite-universe counterexample to the printed statement. | Faithful specialization | Weakened / easier |
| P07 | Distinct noisy-closure witness semantics | Definition 3.2, p. 6 | `NoisyClosureWitnessAt`; [S05] | For distinct examples, Lean's finset condition is exactly nonbottom finite noisy closure. | Exact / formally equivalent | Preserved |
| P08 | Numerical extended-natural `NC_n(H)` | Definition 3.2, p. 6 | `FiniteNoisyClosureDimensionAt`; `InfiniteNoisyClosureDimensionAt` | Lean does not define a numerical value, largest witness, or extended natural. The finite and infinite sides are separate propositions. | Related but materially different | Weakened / easier |
| P09 | Noisy version space on repeated histories | Preliminaries, pp. 3–4; proof of Theorem 3.3, Appendix E | `noisyVersionSpace H (sample stream t) n` | The printed `H(x_{1:d};n)` uses sequence length `d` while also taking a set of values, which is duplicate-sensitive. Lean replaces it by the distinct sample cardinality. This is a source repair consistent with the paper's distinct-example objective. | Related but materially different | Preserved |
| P10 | Uniform noise-dependent characterization, qualitative | Theorem 3.3, p. 6 | `GenLimit.NoisyExamples.theorem_3_3` [S13] | Same qualitative iff, but Lean adds `[Nonempty α]` to repair `α=∅, H=∅`. | Faithful specialization | Weakened / easier |
| P11 | Exact/Theta sample complexity at noise level `n` | Text after Theorem 3.3, p. 6; Appendix E, p. 14 | No numerical Lean theorem | Lean has only bounded-witness predicates and arbitrary chosen bounds; it does not state a minimal threshold, the lower bound from a finite witness of size `d`, the upper threshold `NC_n+1`, or `Θ(NC_n)`. | Not represented in Lean | Indeterminate |
| P12 | Finite classes | Corollary 3.4, p. 6 | `corollary_3_4` [S16], [S14], [S15] | Qualitative conclusion is specialized by `[Nonempty α]`; the counting bound is represented propositionally as `\|S\| ≤ B + \|H\| n`. | Faithful specialization | Weakened / easier |
| P13 | Separation `C(H)=0`, `NC_1(H)=∞` | Lemma 3.5, pp. 6–7 | `lemma_3_5` [S35], [S32]–[S34] | Lean fixes the concrete countably infinite tagged universe matching the incidence structure of the paper's prime/power construction. This repairs the printed arbitrary-countable-`X` wording. | Faithful specialization | Weakened / easier |
| P14 | Strict separation from noiseless uniform generation | Consequence of Lemma 3.5 and Theorem B.2, p. 7 | [S32], imported `uniform_generatability_iff_finite_closure_dimension`, and [S36] | Not packaged as one Paper 06 theorem, but directly derivable from supplied signatures. | Exact / formally equivalent | Preserved |
| P15 | Increasing-cover sufficiency | Lemma 3.6, p. 7; Appendix F | `lemma_3_6` [S21] | Same single cover and diagonal condition; Lean adds `[Nonempty α]` and indexes from zero. | Faithful specialization | Weakened / easier |
| P16 | All countable classes | Corollary 3.7, p. 7 | `corollary_3_7` [S23] | Same conjunction of non-uniform noise-dependent and noisy-limit generation; Lean adds `[Nonempty α]`. | Faithful specialization | Weakened / easier |
| P17 | Strict uniform-vs-nonuniform noisy separation | Consequence of Lemma 3.5 and Corollary 3.7, p. 7 | [S23], [S34]–[S36] | The explicit class is countable/UUS, hence non-uniformly noise-dependent by [S23], but not uniformly noise-dependent by [S36]. | Exact / formally equivalent | Preserved |
| P18 | Per-noise cover necessity | Lemma 3.8, p. 7 | `lemma_3_8` [S22] | The cover is inside `∀n`; it may depend on `n`, and every component has finite dimension at the fixed level `n`. Quantifier order is preserved. | Exact / formally equivalent | Preserved |
| P19 | Quantitative `NC_n(H_i)<i` | Proof of Lemma 3.8, p. 7 | No matching bound declaration | Lean proves only `FiniteNoisyClosureDimensionAt (classes i) n`, not the explicit bound by `i`. | Not represented in Lean | Indeterminate |
| P20 | Robustification theorem | Theorem 3.9, p. 8 | `theorem_3_9` [S29] | Same noiseless non-uniform premise, same noisy-presentation conclusion, same qualitative one-way guarantee, and no computational/rate claim. | Exact / formally equivalent | Preserved |
| P21 | Literal Algorithm 1 | Algorithm 1, p. 8 | `paperRobustifiedNoiselessGenerator` plus [S24]–[S28] | Lean uses the exact-half suffix but totalizes the zero-half case by allowing the empty suffix, and chooses any fresh generated candidate rather than the first one. The access model and correctness invariant are unchanged. | Related but materially different | Preserved |
| P22 | Finite-union noisy-limit sufficiency | Theorem 3.10, p. 8; Appendix G, p. 15 | `theorem_3_10` [S31] | Lean adds `[Infinite α]`, excluding only degenerate empty-class finite-universe cases under UUS; it also makes the finite-noise-value cutoff explicit. | Faithful specialization | Weakened / easier |
| P23 | Alternate positive-count uniform notion | Definition C.1, p. 11 | `IsAlternateUniformNoiseIndependentGeneratorAt`; `AlternateUniformNoiseIndependentGeneratable` | Exact positive-distinct trigger and finite-occurrence noise model. | Exact / formally equivalent | Preserved |
| P24 | Intersection obstruction | Lemma C.2, p. 12 | `lemma_C_2` [S41] | Same subclass, distinguished member, finite full intersection, infinite deleted intersection, and negative conclusion. | Exact / formally equivalent | Preserved |
| P25 | Bounded noisy-closure excess characterization | Theorem C.3, p. 12 | `theorem_C_3` [S40]; `BoundedNoisyClosureExcess` | The witness inequality `k≤n+B` is the exact proposition-level reading of finite `sup_n(NC_n-n)`; Lean adds `[Nonempty α]`. | Faithful specialization | Weakened / easier |
| P26 | Non-uniform noise-independent notion as displayed | Definition D.1, p. 13 | `IsNonuniformNoiseIndependentGenerator`; `NonuniformNoiseIndependentGeneratable` | Lean follows the displayed formula and Lemma D.2 proof: target-dependent threshold counts distinct positive examples. | Exact / formally equivalent | Preserved |
| P27 | Sentence claiming D.1 counts all distinct examples | Last paragraph of p. 11 | No Lean counterpart; Lean follows displayed D.1 | The PDF contradicts itself: page 11 says total distinct examples, while page 13 and its proof use positive distinct examples. | Indeterminate from the supplied evidence | Indeterminate |
| P28 | Finite counterexample to Definition D.1 | Lemma D.2, p. 13 | `lemma_D_2` [S43], [S42] | Lean fixes `X=ℕ`, exactly as the paper's proof does, instead of the literally arbitrary countable `X` in the statement. | Faithful specialization | Weakened / easier |


## 5. Detailed theorem-by-theorem audit

### 5.1 Theorem 3.1: uniform noise-independent generation

**Paper.** Theorem 3.1 states that for countable `X` and UUS `H`,
\[
H\text{ is uniformly noise-independent generatable}
\iff
\left|\bigcap_{h\in H}\operatorname{supp}(h)\right|=\infty
\]
(p. 5, §3.1).

**Lean.** [S04] states:

```lean
theorem GenLimit.NoisyExamples.theorem_3_1 [Countable α] [Infinite α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H) :
    UniformNoiseIndependentGeneratable H ↔
      (commonIntersection H).Infinite
```

After unfolding `UniformNoiseIndependentGeneratable`, the left side is
\[
\exists G\,\exists d\,
\forall L\in H\,\forall x,\;
\operatorname{HasFiniteNoise}(x,L)\Rightarrow
\forall t,\ |S_t(x)|=d\Rightarrow
\forall s\ge t,\ \operatorname{CorrectAt}(G,L,x,s).
\]

The only theorem-level mismatch is `[Infinite α]`. It is a genuine repair, not a cosmetic assumption. If `H=∅` and `α` is finite and nonempty, UUS is vacuous and a total generator exists, so the left side is true, while `commonIntersection ∅ = univ` is finite, so the right side is false. If `H` is nonempty, UUS already forces `α` infinite.

The direction declarations are stronger than the wrapper:

- [S01] needs only an infinite common intersection; it drops countability, universe infinitude, and UUS.
- [S03] drops countability but keeps `[Infinite α]` and UUS.
- [S02] exposes the adversarial quantifiers: for every proposed generator and threshold, a target, finite-noise stream, exact trigger, and later failure exist.

No target, noise budget, or membership oracle is available to the generator. `commonIntersectionGenerator` is a classical noncomputable choice from the infinite intersection outside the finite sample. The paper is explicitly information-theoretic (p. 3, §1.1), so noncomputability is faithful.

**Correspondence verdict:** Faithful specialization.  
**Difficulty verdict:** Weakened / easier.

### 5.2 Definition 3.2 and Theorem 3.3: noisy closure

#### Witness semantics

For a finite set `S`, Lean's noisy version space is
\[
V_n(H,S)=\{L\in H:\ |S\setminus L|\le n\}.
\]
A witness at `(n,d)` is a set `S` of exact cardinality `d` with nonempty `V_n(H,S)` and finite intersection of its members. [S05] proves equivalence with an injective sequence `Fin d → α`. This matches the distinct-sequence clause of Definition 3.2 (p. 6).

The paper's preliminary notation `H(x_{1:d};n)` is less stable on repeated sequences: it uses the number `d` of positions but intersects a set of distinct values. Lean always deduplicates first. This changes the literal semantics on a repeated history, but it is the coherent reading for the paper's distinct-example sample complexity and for the intended proof of Theorem 3.3.

#### Qualitative characterization

[S13] states:

```lean
theorem GenLimit.NoisyExamples.theorem_3_3 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H) :
    UniformNoiseDependentGeneratable H ↔
      ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n
```

This faithfully captures the displayed iff in Theorem 3.3 (p. 6). `[Nonempty α]` repairs the case `α=∅, H=∅`: every finite-dimension predicate is then true, but no total generator exists.

The sufficient direction [S09] is a formal generalization: it requires only `[Nonempty α]` and the finite-dimension predicates, not countability or UUS. At a history set `S` and time `t`, it considers
\[
E(S,t)=\{m\le t:\ D_m<|S|\text{ and }V_m(H,S)\ne\varnothing\},
\]
selects `max E(S,t)`, and outputs a fresh point from that noisy core. The true noise level is not an input. On a stream with at most `n` bad occurrences, the target witnesses nonemptiness at level `n`, and once the exact threshold
\[
d_n=\max(D_n+1,n)
\]
is reached, level `n` is eligible. The nonemptiness filter is a totalization/repair of the paper's displayed maximum: it prevents choosing a bottom closure on arbitrary histories but does not alter admissible post-threshold behavior.

The necessary direction [S12] and adversarial lemma [S11] preserve the order
\[
\forall G\;\forall d\;\exists L\;\exists x\;\exists t\;\exists s\ge t
\]
at a fixed bad noise level.

#### Missing quantitative content

The paper additionally says that if `NC_n(H)=d`, then any generator needs at least `d` distinct examples, a generator succeeds after roughly `NC_n(H)+1`, and the sample complexity is `Θ(NC_n(H))` (p. 6; Appendix E, p. 14). Lean does not define `NC_n(H)` numerically and has no theorem stating:

- a finite witness of exact size `d` defeats threshold `d`;
- the least valid threshold is bounded above by `NC_n(H)+1`;
- any lower/upper asymptotic relation.

The formalization proves only qualitative boundedness and uses a classically chosen, not necessarily least, bound `D_n`.

**Correspondence verdict:** Faithful specialization.  
**Difficulty verdict:** Weakened / easier. The qualitative proof structure is preserved, but the quantitative theorem is absent.

### 5.3 Corollary 3.4: finite classes

The paper's proof defines a finite bound on all finite intersections of subclasses and concludes
\[
NC_n(H)<n|H|+B+1
\]
(p. 6).

Lean exposes the counting statement [S14]:
\[
|S|\le B+|H|\,n
\]
whenever the noisy common core of `S` is finite and `B` bounds finite subclass cores. [S15] converts this to `FiniteNoisyClosureDimensionAt H n`, and [S16] concludes uniform noise-dependent generation under countability, nonemptiness, and UUS.

The bound is propositionally faithful, including its linear dependence on occurrence-noise budget `n` and class size. It is not computational: no finite representation of `H` or algorithm for finding `B` appears.

The wrapper's extra `[Nonempty α]` repairs the empty example type.

**Correspondence verdict:** Faithful specialization.  
**Difficulty verdict:** Weakened / easier.

### 5.4 Lemma 3.5: separation

The paper states “Let `X` be countable. There exists ...” and then sets `X=P∪S` in its proof (pp. 6–7). Read literally as a theorem for every countable `X`, the statement is false on finite `X`, because no nonempty UUS class exists and the empty class cannot have `NC_1=∞`.

Lean repairs the quantification by fixing
\[
\alpha=\mathbb N\times\operatorname{Option}(\mathbb N),
\qquad
L_p=\{(q,z):q\ne p\}.
\]
This is incidence-isomorphic to the paper's prime/negative-prime-power construction: the point `(p,none)` represents prime `p`, and `(p,some n)` represents a member of the `p`-row.

The target declarations establish:

- [S32]: ordinary closure dimension zero;
- [S33]: a level-one witness at every exact `d`, including `d=0`;
- [S34]: countability, UUS, dimension zero, and exact-every-size one-noisy witnesses;
- [S35]: the existential packaged lemma;
- [S36]: failure of uniform noise-dependent generation.

The paper's claimed ordinary-vs-noisy separation is also formally derivable by combining [S32] with the imported ordinary closure characterization and [S36]. The generation-level positive and negative conclusions are not packaged in one target-scope theorem, but they are not missing logically.

**Correspondence verdict:** Faithful specialization. The fixed universe is a source repair, not a second verdict.  
**Difficulty verdict:** Weakened / easier.

### 5.5 Lemmas 3.6 and 3.8: non-uniform covers

The sufficient condition [S21] has the exact diagonal structure:
\[
\exists (H_i)_i\quad
\bigl[H_i\subseteq H_j\ (i\le j),\ H=\bigcup_i H_i,\ 
\forall i\ \operatorname{FiniteDim}(H_i,i)\bigr]
\Rightarrow
\operatorname{NonuniformNoiseDependent}(H).
\]
The cover is selected once, before the unknown target and true noise level. For a target `L` lying in some `H_i` and actual budget `n`, the construction may move to `j=\max(i,n)`, so the threshold depends on `(L,n)` but not the stream. Lean adds `[Nonempty α]`, repairing the empty-type case.

The necessary condition [S22] preserves the different order:
\[
\operatorname{NonuniformNoiseDependent}(H)
\Rightarrow
\forall n\,\exists(H_i^{(n)})_i\quad
\bigl[H=\bigcup_iH_i^{(n)},\ \forall i\ \operatorname{FiniteDim}(H_i^{(n)},n)\bigr].
\]
The cover may depend on `n`, and the dimension level remains the fixed `n`, not the index `i`.

Therefore the Lean sufficiency and necessity do **not** form an iff, exactly as the paper emphasizes after Lemma 3.8 (p. 7). No helper condition secretly closes the quantifier gap.

The paper's proof says the constructed `H_i` satisfies the numerical bound `NC_n(H_i)<i`. Lean's private bridge proves only finiteness, and [S22] exposes no bound. That quantitative part is missing.

**Lemma 3.6 correspondence verdict:** Faithful specialization.  
**Lemma 3.6 difficulty verdict:** Weakened / easier.  
**Lemma 3.8 correspondence verdict:** Exact / formally equivalent.  
**Lemma 3.8 difficulty verdict:** Preserved.

### 5.6 Corollary 3.7: countable classes

[S23] states the conjunction:
\[
\operatorname{NonuniformNoiseDependentGeneratable}(H)
\ \land\
\operatorname{NoisilyGeneratableInLimit}(H)
\]
for countable UUS `H` over a countable nonempty example type.

The construction uses finite prefixes of an enumeration, but unlike the prose `h_1,h_2,\ldots`, it also handles finite and empty classes by intersecting finite ranges back with `H`. The noisy-limit implication is separately stated in [S20]. It uses:

1. finite noise implies some finite occurrence bound [S18];
2. UUS plus noisy presentation gives infinite stream range;
3. an infinite range crosses every exact finite distinct-cardinality threshold.

The extra `[Nonempty α]` is necessary for the printed claim when `H=∅`.

**Correspondence verdict:** Faithful specialization.  
**Difficulty verdict:** Weakened / easier.

### 5.7 Theorem 3.9: noiseless-to-noisy robustification

[S29] exactly matches the theorem-level implication:
\[
\operatorname{NonuniformlyGeneratable}(H)
\Rightarrow
\operatorname{NoisilyGeneratableInLimit}(H)
\]
under countability and UUS.

The noiseless premise uses streams whose range is contained in `L`; it does not require enumeration of `L`. The noisy conclusion uses `NoisyPresentation`, so every target point appears and only finitely many off-target occurrences occur. This is the same stream class as Definition 2.7.

The formal chain is genuine and noncircular:

- [S24] converts the baseline stream guarantee into correctness on any finite positive history with at least the target threshold.
- [S25] shows repeated calls to the baseline generator append distinct positive candidates.
- [S26] uses `r+1` candidates against at most `r` discarded prefix positions to obtain a candidate absent from the whole observed history.
- [S27] gives local correctness of the robustified output once the chosen suffix is positive and large.
- [S28] proves that every sufficiently late exact-half suffix starts after the last noise occurrence and contains enough distinct positives.

The final conclusion is purely qualitative:
\[
\exists T(L,x)\ \forall s\ge T(L,x),\ \operatorname{CorrectAt}.
\]
There is no bound on `T`, no rate in terms of the number or last time of errors, and no computability claim. This exactly matches Theorem 3.9.

The named generator is not extensionally identical to Algorithm 1:

- it treats `r` as the number of discarded zero-based positions and allows `r=t`, giving an empty suffix when `\lfloor d_t/2\rfloor=0`; the paper's one-based `r_t\le t` has no such suffix;
- it selects an arbitrary member of the set of fresh generated candidates rather than the first candidate that is unseen.

These are valid totalization/selection repairs and do not change the theorem.

**Correspondence verdict:** Exact / formally equivalent.  
**Difficulty verdict:** Preserved.

### 5.8 Theorem 3.10: finite unions

[S31] states that if `H` is a finite union of uniformly noise-independent generatable components, then `H` is noisily generatable in the limit, under countability, infinitude of `α`, and UUS.

For each component, [S03] turns uniform noise-independent generation into an infinite common intersection. A fixed repetition-free enumeration of that intersection is used. The progress score is the first enumerated point absent from the current sample; [S30] chooses a component with maximal progress. Components whose entire enumerated core lies in the stream range have unbounded progress, while every other component has a permanently missing obstruction.

The paper's Appendix G asserts that once a selected component is range-good, every unseen point of that component core is in the target. That requires waiting until all finitely many off-target values in the stream have already appeared. Lean makes this missing cutoff explicit. This is a proof repair, not a stronger theorem premise.

`[Infinite α]` is stronger than the paper's countability assumption. Under nonempty `H` and UUS it is automatic; it excludes degenerate empty-class cases. The finite cover may have `k=0`, in which case `H=∅`.

**Correspondence verdict:** Faithful specialization.  
**Difficulty verdict:** Weakened / easier.

### 5.9 Appendix C: positive-count uniform generation

Definition C.1 is represented exactly by the alternate generation predicate. The generator is not told the target; target membership appears only in the semantic trigger. The sentence immediately before Theorem C.3 calls this “Definition D.1,” but the appendix heading, theorem title, formula, and proof are about Definition C.1; Lean follows that coherent reading.

Theorem C.3 is represented by [S40]:
\[
\operatorname{AlternateUniformNoiseIndependentGeneratable}(H)
\iff
\exists B\ \forall n,k,\ 
\operatorname{Witness}(H,n,k)\Rightarrow k\le n+B.
\]
For the paper's numerical dimension, the right side is equivalent to finite
\[
\sup_n(NC_n(H)-n).
\]
Lean avoids extended naturals and subtraction but preserves the logical content. `[Nonempty α]` repairs the empty-type case.

The direction [S37] is a formal generalization: bounded excess implies the alternate generation property without countability or UUS. Its constructed strategy at sample `S` uses level
\[
n_S=|S|-(B+1).
\]
Notably, the sufficient proof does not use the finite-noise premise at all once the positive threshold is met; the resulting generator guarantee is stronger on that aspect. The stated theorem remains the paper's property.

[S38] gives the quantitative lower-bound interface: a witness with `k>n+d` defeats positive threshold `d`. [S39] converts any alternate generator threshold into a global excess bound.

Lemma C.2 is exactly [S41]. Its assumptions are independent intersection properties; they do not encode the negative conclusion.

**Theorem C.3 correspondence verdict:** Faithful specialization.  
**Theorem C.3 difficulty verdict:** Weakened / easier.  
**Lemma C.2 correspondence verdict:** Exact / formally equivalent.  
**Lemma C.2 difficulty verdict:** Preserved.

### 5.10 Appendix D: non-uniform noise-independent generation

The displayed Definition D.1 and the proof of Lemma D.2 count
\[
|S_t\cap L|,
\]
the number of distinct positive observations. Lean follows this formula exactly.

The last paragraph of page 11 instead says Definition D.1 counts all distinct examples. That sentence is incompatible with page 13 and with the even/odd proof. The supplied paper alone does not resolve the editorial inconsistency beyond the stronger evidence of the displayed formula and proof; Lean's choice is therefore justified but not a literal reconciliation of all prose.

[S42] packages the concrete even/odd class:
\[
H=\{\text{even naturals},\text{odd naturals}\},
\]
which is finite, UUS, and fails the non-uniform noise-independent property. [S43] gives the existential theorem over `ℕ`. The paper's statement says arbitrary countable `X` but immediately fixes `X=ℕ` in the proof; Lean repairs this quantification.

**Correspondence verdict:** Faithful specialization.  
**Difficulty verdict:** Weakened / easier.


## 6. Helper, bridge, link, encoding, and circularity audit

The table below expands every statement-relevant condition used by a main result and records whether a separate Lean signature establishes the needed link.

| Condition or construction | Fully expanded logical role and dependencies | Establishing declaration(s) | Audit classification |
|---|---|---|---|
| `commonIntersection H` | `{x : α | ∀ L, L∈H → x∈L}`. Depends only on `H`; for `H=∅` it is `univ`. | Definition; `commonIntersection_subset_of_mem`; [S01]–[S04] | Genuine structural invariant. It contains no generation conclusion. |
| `HasFiniteNoise x L` | The bad index set `{t | x_t∉L}` is finite. No target coverage. | Definition; [S17], [S18] | Exact occurrence-noise model. Independent, noncircular. |
| `HasNoiseAtMost x L n` | There is a finset `F` equal to the bad index set and `|F|≤n`. | Definition; [S17], [S18] | Exact bounded occurrence count. Independent. |
| Occurrence-to-distinct bridge | `HasNoiseAtMost x L n → |sample(x,t)\L|≤n`. Multiple bad occurrences of one value can only decrease the distinct count. | [S07] | Genuine one-way fact. No converse is claimed or valid in general. |
| Target noisy-version membership | If `L∈H` and the stream has at most `n` bad occurrences, then `L∈V_n(H,S_t)` for every `t`. | [S08] | Genuine bridge from the stream model to the combinatorial model. It assumes no oracle access. |
| `NoisyPresentation x L` | `L⊆range(x)` and finite bad occurrences. | Definition; noisy range/infinite-range helpers; [S20], [S28], [S29], [S31] | Exact noisy-enumeration condition. It does not contain eventual correctness. |
| `noisyVersionSpace H S n` | `L∈H` and `|S\L|≤n`. The set `S` consists of distinct values. | Definition; negative-part restatement; [S05], [S07], [S08] | Independent combinatorial condition. On repeated paper sequences it is a repaired, deduplicated semantics. |
| `noisyCommonCore H S n` | Intersection of every member of the noisy version space. If the version space is empty, the bare core is `univ`. | Definition; `noisyCommonCore_subset_of_mem_versionSpace` | Independent. Empty-space universality is neutralized wherever correctness is inferred by an explicit membership/nonemptiness premise. |
| `noisyClosure H S n` | `none` iff the version space is empty; otherwise `some` of the common core. | `noisyClosure_eq_none_iff`, `noisyClosure_eq_some_iff` | Faithful bottom encoding. Not used to smuggle in an infinite core. |
| `NoisyClosureWitnessAt H n d` | `∃S`, exact `|S|=d`, nonempty noisy version space, finite common core. | Definition; [S05] | Genuine witness predicate. Desired generation conclusions do not occur in it. |
| `FiniteNoisyClosureDimensionAt H n` | `∃D ∀d>D`, no exact witness of size `d`. | Definition; [S06], [S10] | Genuine boundedness predicate. It can hold vacuously when all large version spaces are empty. |
| Large-sample infinite-core form | Above some `D`, nonempty noisy version space implies infinite core. | [S06] | Exact reformulation of the finite predicate. The nonemptiness premise is essential. |
| Negation of finite dimension | For every `D`, some witness has size `d>D`. | [S10] | Exact logical negation of boundedness. It gives arbitrarily large witnesses, not every exact size. |
| `InfiniteNoisyClosureDimensionAt H n` | Every exact `d∈ℕ` has a witness. | Definition; [S33] for the example | Separate exact-witness predicate. No generic complement theorem links it to finite dimension. |
| `BoundedNoisyClosureExcess H` | `∃B ∀n,k`, every witness satisfies `k≤n+B`. | Definition; [S37]–[S40] | Genuine two-parameter combinatorial condition. It can be vacuous if no witnesses exist. |
| `IsNondecreasingCover H classes` | `classes` is monotone and `H=⋃i classes i`; equality implies each component is a subclass of `H`. | Definition; [S21], [S22], [S23] | Independent cover structure. It neither assumes nor contains generation. |
| `IsFiniteCover H classes` | `H=⋃i classes i` for `i:Fin k`. Components may overlap or be empty; `k=0` forces `H=∅`. | Definition; [S31] | Independent finite cover. |
| Chosen noisy-closure bounds | `noisyClosureBound H hdim n` classically selects a `D_n` satisfying [S06]. | `noisyClosureBound_spec` | Genuine witness extraction from the dimension premise. It need not select the least bound. |
| Eligible noise levels | `m≤t`, selected bound `D_m<|S|`, and `V_m(H,S)` nonempty. The maximum eligible level is used. | `mem_eligibleNoiseLevels_iff`, `selectedNoiseLevel_mem`, `le_selectedNoiseLevel` | Totalized version of the paper strategy. No true noise level or target is passed to the generator. |
| Fresh point from noisy core | From an infinite core and finite `S`, choose a point in the core outside `S`. | `freshFromNoisyCore_spec` | Classical choice interface. It assumes the local infinite-core fact, not the desired global generation theorem. |
| Uniform noisy-closure strategy | Uses only `H`, chosen bounds, time, and the distinct history sample. | `noisyClosureStrategy_output`, [S09] | Genuine construction; noncomputable extensional class access, no target/noise oracle. |
| Diagonal cover bounds/eligibility | At index `i`, use a bound for level `i` on `H_i`; require `i≤t`, bound passed, and nonempty version space. | `diagonalNoisyClosureBound_spec`, `mem_diagonalEligibleIndices_iff`, strategy specs, [S21] | Genuine implementation of Lemma 3.6. It assumes the stronger diagonal cover exactly as the paper does. |
| Fixed-noise necessity subclasses | `H_i={L∈H : threshold_n(L)≤i}`; the generator works uniformly at level `n` on each subclass. | private `fixed_noise_generator_implies_finite_dimension`; [S22] | Independent construction. It proves finiteness but not the paper proof's explicit numerical bound `<i`. |
| Finite-noise/bounded-noise link | Finite bad set has its cardinality as a bound; bounded noise is finite. | [S17], [S18] | Exact and noncircular. Used to pass from Definition 2.6 to Definition 2.7. |
| Exact-cardinality crossing | An infinite-range stream reaches every finite distinct-sample cardinality because the count starts at zero and rises by at most one per time. | `exists_sample_card_eq_of_range_infinite` and dependencies | Genuine fact ensuring the noisy-limit implication is nonvacuous under UUS presentations. |
| Baseline finite-history correctness | A noiseless non-uniform stream guarantee implies correctness of `Q` on any finite positive history with at least the threshold, by appending a positive fallback. | [S24] | Genuine bridge omitted from the paper's prose. It does not assume robustified correctness. |
| Iterated baseline candidates | Repeatedly append `Q`'s output; after the threshold, every appended point is positive, new relative to the accumulated list, and distinct. | [S25] | Genuine induction invariant. |
| Candidate pigeonhole step | `r+1` generated candidates are disjoint from the suffix; at most `r` positions precede the suffix, so one candidate is absent from the full history. | [S26] | Independent finite counting fact. |
| Exact-half suffix | Choose the largest discarded-prefix length `r≤t` such that the remaining suffix has `floor(totalDistinct/2)` distinct values. | `paperBalancedSuffixIndices`, `paperBalancedSuffixStart`, cardinality/maximality lemmas | Faithful repaired implementation. Allowing `r=t` supplies an empty suffix when the target cardinality is zero. |
| Robustified local correctness | If the exact-half suffix is positive and has at least baseline threshold `d`, the robustified output is positive and unseen in the full history. | [S27] | Genuine local theorem. Its premises do not contain eventual correctness. |
| Eventual suffix invariant | On a noisy presentation of an infinite target, eventually every exact-half suffix starts after the finite-noise cutoff and has at least `d` distinct positives. | [S28] | Genuine global convergence statement. No explicit time/rate is exposed. |
| Finite-union common cores | Uniform noise-independent generation of a component plus its inherited UUS gives an infinite common intersection. | [S03], component-UUS helper | Genuine use of a stronger component property; not circular with noisy-limit generation. |
| Finite-union progress | Fixed injective enumeration of each infinite core; progress is first unseen index; choose an argmax. | [S30] and enumeration specs | Genuine finite-selection mechanism. |
| Range-good component | A component core is contained in the full stream range. Bad components have a permanently absent enumerated obstruction. | `rangeGoodIndices`, obstruction specs | Independent range condition. It is weaker than core containment in the target, so the noise-value cutoff is separately needed. |
| Finite-noise-value cutoff in Theorem 3.10 | Wait until all values occurring at bad positions are in the current sample. Then any unseen range point is positive. | Finite-set eventual-subset helper inside [S31]'s statement-level construction interfaces | Valid repair of an omitted Appendix G step; no stronger stream premise. |
| Excess strategy | At sample `S`, use level `|S|-(B+1)` and choose from its infinite core if available. | strategy specs, [S37] | Genuine construction. It does not receive `L`; positive target count is used only to prove target version-space membership. |
| Excess lower bound | A witness of size `k>n+d` defeats proposed positive threshold `d`. | [S38] | Genuine adversarial fact, not conclusion-encoding. |
| Parity counterexample trigger | The trigger counts positives in the target; the identity prefix provides exactly `d` even and `d` odd values in the Lean indexing convention. | parity counting helpers; [S42], [S43] | Genuine counterexample to displayed Definition D.1. |

### Circularity and conclusion-encoding determination

No main combinatorial premise directly contains its desired generation conclusion:

- finite noisy dimension, bounded excess, UUS, and cover conditions are independent set/cardinality predicates;
- Theorem 3.9 assumes a **noiseless** non-uniform generator, not the noisy-limit conclusion;
- Theorem 3.10 assumes stronger componentwise uniform noise-independent generation, not noisy-limit generation of the union;
- strategy specifications assume local infinite-core or local suffix conditions that are separately established from the main premises.

Some declarations are intentionally conclusion-proximal construction specifications—for example, a chosen point from an infinite core lies in that core—but these are standard witness interfaces, not circular assumptions.

## 7. Focused required checks

### 7.1 Finite and infinite noisy closure dimension

They are **not** formalized as a single numerical dimension and its two complementary cases.

- `FiniteNoisyClosureDimensionAt H n` means witness sizes are bounded.
- Its negation is formally expanded by [S10] as existence of arbitrarily large witness sizes.
- `InfiniteNoisyClosureDimensionAt H n` means a witness exists at every exact size.
- No theorem proves witness downward closure, equivalence of “arbitrarily large” and “every exact size,” or complementarity of the finite and infinite predicates.
- The explicit separation proves the stronger exact-every-size property directly and then uses a witness at `D+1` to refute finite dimension.

The paper's numerical Definition 3.2 intends a genuine extended-natural dimension. Lean faithfully captures the finite side used by Theorem 3.3 but does not formalize the numerical object or its general complement law.

Empty version spaces cannot become witnesses: `NoisyClosureWitnessAt` explicitly requires nonemptiness. The bare common core is universal on an empty version space, but `noisyClosure` returns `none`, the large-sample reformulation has a nonemptiness antecedent, and strategy eligibility also requires nonemptiness.

### 7.2 Non-uniform cover quantifiers

The two cover conditions do **not** match:

\[
\underbrace{\exists(H_i)_i\ \forall i\ \operatorname{FiniteDim}(H_i,i)}_{\text{sufficiency}}
\qquad\text{versus}\qquad
\underbrace{\forall n\ \exists(H_i^{(n)})_i\ \forall i\ \operatorname{FiniteDim}(H_i^{(n)},n)}_{\text{necessity}}.
\]

Lean preserves this mismatch exactly. The necessary cover may change with `n`; the sufficient cover must be fixed before the true noise level is known. No hidden bridge converts one into the other.

### 7.3 Robustification stream class, rate, and effectivity

Theorem 3.9 uses exactly the paper's noisy-enumeration stream class:
\[
L\subseteq range(x),\qquad \#\{t:x_t\notin L\}<\infty.
\]
It does **not** prove robustness on every finite-noise stream that may omit target elements. It proves only qualitative eventual correctness, with `T` depending on the full stream and target.

No rate, sample complexity in time, computable cutoff, runtime, oracle complexity, or effective representation is stated. The generator is noncomputable and uses classical equality/choice. This matches the paper's information-theoretic framing and its open question about computable noisy generation with a membership oracle (pp. 8–9, §4).

Theorem 3.10 has the same qualitative stream class and no rate/effectivity guarantee.

### 7.4 Ordered-history and oracle access

The Lean generator sees:

- history length;
- ordered values at every prior position;
- repetitions and the locations of noise.

It does not see:

- the target language;
- target membership;
- the true noise level;
- the set of bad positions;
- an index of the target;
- a membership oracle.

The closure-based generators are defined relative to `H` and classically chosen bounds. This is extensional information-theoretic dependence on the class, not a runtime oracle interface.

The paper is internally inconsistent about whether `X^*` denotes finite sets or finite sequences. Algorithm 1 requires ordered-history access. Lean resolves the inconsistency in favor of the operational sequence model.

### 7.5 Exact-cardinality triggers and avoidability

Definitions 2.4–2.6, C.1, and D.1 are all exact-trigger properties. An admissible finite-noise stream can repeat one positive example forever and never reach a threshold `d>1`; then the guarantee is vacuous on that stream. This is not a Lean-only defect.

For a noisy presentation of a UUS target, the range is infinite, so every finite distinct-cardinality threshold is eventually crossed. This is why [S20] can convert non-uniform noise-dependent generation into noisy-limit generation.

Lean natural numbers include zero. The paper appears to use positive naturals in places and explicitly writes `N∪{0}` elsewhere. Allowing zero does not materially change the existential generation notions—an always-correct threshold-zero generator also works at threshold one—but it does make exact witness predicates include size zero.

### 7.6 Degenerate classes and universes

- **Empty class, inhabited `α`:** generation notions are vacuous once a total generator is chosen; common intersection is `univ`; noisy version spaces are empty; all finite-dimension predicates hold.
- **Empty class, empty `α`:** no total generator exists, while finite-dimension/bounded-excess predicates remain true.
- **Empty class, finite nonempty `α`:** Theorem 3.1 as printed fails because uniform noise-independent generation is vacuous but the universal common intersection is finite.
- **Nonempty UUS class:** automatically forces `α` infinite.
- **Finite target outside UUS:** exact thresholds above the target's distinct size can be avoided, making positive conclusions vacuous.

These cases explain the Lean additions `[Nonempty α]` and `[Infinite α]`.

### 7.7 Probability, asymptotics, and freshness

There is no probabilistic noise, random stream, confidence level, expectation, convergence probability, or distributional rate in either the relevant paper results or Lean. Noise is adversarial and finite.

Freshness is relative to the observed sample only. Neither paper nor Lean requires outputs to be fresh relative to previous generator outputs. The robustification proof internally appends generated candidates to force distinctness among candidates, but the final generation notion remains stream-relative.

## 8. Bidirectional correspondence: substantive Lean results to paper

The scope below includes every target-scope theorem judged substantive for the paper-level mathematics or a necessary semantic bridge. Pure definitional rewrites, execution equations, finite-set arithmetic, and private implementation lemmas are audited in §6 rather than duplicated here. Exact signatures are in Appendix A.

| Signature ID | Lean declaration | Paper counterpart | Finding | Correspondence verdict | Difficulty verdict |
|---|---|---|---|---|---|
| S01 | `infinite_commonIntersection_implies_uniform_noiseIndependent` | Theorem 3.1 sufficiency | Drops countability, UUS, and universe-infinitude assumptions. | Faithful generalization | Strengthened / harder |
| S02 | `finite_commonIntersection_defeats_threshold` | Theorem 3.1 necessity proof | Exposes the adversary for every generator and exact threshold; drops countability. | Faithful generalization | Strengthened / harder |
| S03 | `uniform_noiseIndependent_implies_infinite_commonIntersection` | Theorem 3.1 necessity | Drops countability while retaining the nondegenerate universe/UUS conditions. | Faithful generalization | Strengthened / harder |
| S04 | `theorem_3_1` | Theorem 3.1 | Adds `[Infinite α]` to repair degenerate empty-class finite-universe cases. | Faithful specialization | Weakened / easier |
| S05 | `noisyClosureWitnessAt_iff_injective_sequence` | Definition 3.2 encoding | Exact finset/injective-sequence equivalence not separately stated in the paper. | Extra Lean result not claimed by the paper | Indeterminate |
| S06 | `finiteNoisyClosureDimensionAt_iff_eventually_infinite` | Definition 3.2 finiteness | Useful reformulation with nonempty version-space antecedent; not separately stated. | Extra Lean result not claimed by the paper | Indeterminate |
| S07 | `bad_sample_card_le_noise` | Noise model to closure bridge | Occurrence bound implies a distinct-negative bound; implicit but unnumbered. | Extra Lean result not claimed by the paper | Indeterminate |
| S08 | `target_mem_noisyVersionSpace` | Theorem 3.3 proof bridge | Target membership at every prefix under bounded occurrence noise; implicit but unnumbered. | Extra Lean result not claimed by the paper | Indeterminate |
| S09 | `finite_noisyClosureDimensions_imply_uniform_noiseDependent` | Theorem 3.3 sufficiency | Drops countability and UUS; only inhabitation and finite-dimension premises remain. | Faithful generalization | Strengthened / harder |
| S10 | `arbitrarily_large_witness_of_not_finiteNoisyClosureDimensionAt` | Negation of finite dimension | Logical expansion not separately claimed. | Extra Lean result not claimed by the paper | Indeterminate |
| S11 | `nonfinite_noisyClosureDimension_defeats_threshold` | Theorem 3.3 necessity proof | Drops countability and gives explicit adversarial quantifiers. | Faithful generalization | Strengthened / harder |
| S12 | `uniform_noiseDependent_implies_finite_noisyClosureDimensions` | Theorem 3.3 necessity | Drops countability and explicit nonemptiness. | Faithful generalization | Strengthened / harder |
| S13 | `theorem_3_3` | Theorem 3.3 | Adds `[Nonempty α]`; qualitative iff otherwise matches. | Faithful specialization | Weakened / easier |
| S14 | `noisy_witness_card_le_for_finite_class` | Corollary 3.4 proof bound | States the paper's counting inequality under weaker ambient assumptions. | Faithful generalization | Strengthened / harder |
| S15 | `finite_class_has_finite_noisyClosureDimensionAt` | Corollary 3.4 combinatorial step | No UUS, countability, or inhabitation needed for the bounded-witness conclusion. | Faithful generalization | Strengthened / harder |
| S16 | `corollary_3_4` | Corollary 3.4 | Adds `[Nonempty α]`. | Faithful specialization | Weakened / easier |
| S17 | `hasFiniteNoise_of_hasNoiseAtMost` | Definitions 2.5–2.7 bridge | Explicit bounded-to-finite occurrence-noise lemma. | Extra Lean result not claimed by the paper | Indeterminate |
| S18 | `exists_hasNoiseAtMost_of_hasFiniteNoise` | Definitions 2.5–2.7 bridge | Explicit finite-to-some-bound occurrence-noise lemma. | Extra Lean result not claimed by the paper | Indeterminate |
| S19 | `uniform_noiseDependent_implies_nonuniform_noiseDependent` | Noisy hierarchy implicit in §2.1.2 | Same generator and threshold specialization. | Exact / formally equivalent | Preserved |
| S20 | `nonuniform_noiseDependent_implies_noisy_limit` | Implication used in Corollary 3.7 | Same UUS/noisy-presentation crossing argument. | Exact / formally equivalent | Preserved |
| S21 | `lemma_3_6` | Lemma 3.6 | Adds `[Nonempty α]`; diagonal cover and dependence order match. | Faithful specialization | Weakened / easier |
| S22 | `lemma_3_8` | Lemma 3.8 | Preserves `∀n∃cover_n` and fixed-level dimensions. | Exact / formally equivalent | Preserved |
| S23 | `corollary_3_7` | Corollary 3.7 | Adds `[Nonempty α]`; conclusion is even packaged as a conjunction. | Faithful specialization | Weakened / easier |
| S24 | `nonuniform_generator_correct_on_finite_history` | Theorem 3.9 proof infrastructure | Bridges stream guarantees to arbitrary positive finite histories. | Extra Lean result not claimed by the paper | Indeterminate |
| S25 | `iteratedGeneratorHistory_properties` | Algorithm 1 invariant | Formal positivity/freshness/cardinality invariant not separately stated. | Extra Lean result not claimed by the paper | Indeterminate |
| S26 | `generatedCandidate_not_in_history` | Algorithm 1 pigeonhole step | Formal candidate-existence lemma not separately stated. | Extra Lean result not claimed by the paper | Indeterminate |
| S27 | `paperRobustifiedNoiselessGenerator_correct` | Algorithm 1 local correctness | Conditional local theorem not separately stated. | Extra Lean result not claimed by the paper | Indeterminate |
| S28 | `eventually_paperBalanced_suffix_positive_and_large` | Theorem 3.9 convergence step | Makes the omitted monotonicity/cutoff invariant explicit. | Extra Lean result not claimed by the paper | Indeterminate |
| S29 | `theorem_3_9` | Theorem 3.9 | Same premise, stream class, conclusion, and qualitative strength. | Exact / formally equivalent | Preserved |
| S30 | `noisyWinningIndex_spec` | Appendix G argmax infrastructure | Formal max-progress specification not separately stated. | Extra Lean result not claimed by the paper | Indeterminate |
| S31 | `theorem_3_10` | Theorem 3.10 | Adds `[Infinite α]` and handles finite-noise values explicitly. | Faithful specialization | Weakened / easier |
| S32 | `separation_hasClosureDimension_zero` | Lemma 3.5 first property | Exact property of the chosen incidence-equivalent construction. | Exact / formally equivalent | Preserved |
| S33 | `separation_oneNoisyWitness_every_card` | Lemma 3.5 second property | Proves every Lean natural size, including zero, rather than merely arbitrary positive sizes. | Faithful generalization | Strengthened / harder |
| S34 | `separationClass_properties` | Lemma 3.5 constructed example | Packages exactly the four properties of the concrete construction. | Exact / formally equivalent | Preserved |
| S35 | `lemma_3_5` | Lemma 3.5 | Fixes a concrete countably infinite universe instead of arbitrary countable `X`. | Faithful specialization | Weakened / easier |
| S36 | `separation_not_uniform_noiseDependent` | Generation-level consequence of Lemma 3.5 + Theorem 3.3 | Explicitly states the negative generation conclusion. | Exact / formally equivalent | Preserved |
| S37 | `boundedNoisyClosureExcess_implies_alternateUniform` | Theorem C.3 sufficiency | Drops countability/UUS; keeps only inhabitation and bounded excess. | Faithful generalization | Strengthened / harder |
| S38 | `noisyExcessWitness_defeats_alternate_threshold` | Theorem C.3 necessity proof | Exposes the exact inequality `n+d<k` and adversarial failure. | Exact / formally equivalent | Preserved |
| S39 | `alternateUniform_implies_boundedNoisyClosureExcess` | Theorem C.3 necessity | Drops countability. | Faithful generalization | Strengthened / harder |
| S40 | `theorem_C_3` | Theorem C.3 | Adds `[Nonempty α]`; proposition-level excess condition matches. | Faithful specialization | Weakened / easier |
| S41 | `lemma_C_2` | Lemma C.2 | Same assumptions and negative conclusion. | Exact / formally equivalent | Preserved |
| S42 | `parityClass_not_nonuniform_noiseIndependent` | Lemma D.2 concrete construction | Same even/odd class and target-dependent positive-count obstruction. | Exact / formally equivalent | Preserved |
| S43 | `lemma_D_2` | Lemma D.2 | Fixes `X=ℕ`, as the paper proof does. | Faithful specialization | Weakened / easier |


## 9. Missing paper results or strength not present in Lean

The following paper claims are not stated by any target-scope Lean declaration:

1. **Numerical noisy closure dimension.** Definition 3.2's extended-natural value `NC_n(H)`, its largest-witness value, and its special `0`/`∞` cases are not defined as an object.
2. **Quantitative Theorem 3.3.** The paper's claims that a finite witness of size `d` enforces a lower bound, that a generator succeeds after `NC_n(H)+1` (with the Appendix E `max` correction), and that sample complexity is `Θ(NC_n(H))` are not formal statements.
3. **Quantitative Lemma 3.8.** The proof's asserted bound `NC_n(H_i)<i` is weakened to qualitative finiteness.
4. **A generic complement theorem.** No signature identifies `InfiniteNoisyClosureDimensionAt H n` with `¬FiniteNoisyClosureDimensionAt H n`.
5. **Literal Algorithm 1 behavior.** The exact first-unseen-candidate selection and the paper's one-based suffix rule are not reproduced extensionally; Lean proves a valid repaired variant.
6. **The printed arbitrary-universe versions of Lemmas 3.5 and D.2.** Lean formalizes the concrete universes used in the proofs, not the literally universal “let `X` be countable” statements.
7. **Theorem 3.10 without an infinite-universe assumption.** The qualitative theorem is formalized only under `[Infinite α]`.
8. **Theorem 3.1 without an infinite-universe assumption and Theorem 3.3/Corollaries without inhabitation.** These omissions are deliberate source repairs, not accidental gaps.

No computability, efficiency, probabilistic rate, or oracle theorem is listed as missing, because the paper does not claim one; it explicitly leaves computable noisy generation as an open question.

## 10. Extra Lean results not separately claimed in the paper

The primary modules add useful statement-level infrastructure:

- direction theorems that drop countability and sometimes UUS;
- explicit finite-noise/bounded-noise equivalences;
- occurrence-to-distinct disagreement bridges;
- exact finset/injective-sequence witness equivalence;
- a large-sample infinite-core reformulation of finite dimension;
- an explicit finite-class cardinal inequality;
- explicit hierarchy implications;
- finite-history and candidate-count invariants for robustification;
- a total exact-half suffix construction and a separate rounding-stable balanced-suffix variant;
- an explicit generation-level negative theorem for the separation class;
- exact-every-cardinality witnesses, including size zero;
- proposition-level witness-excess lower bounds.

These additions do not change the advertised qualitative conclusions. Several are formal generalizations; outside UUS some may be satisfied for vacuous exact-trigger reasons.

## 11. Indeterminate comparisons and exact missing evidence

Three points cannot be resolved to a single literal-paper semantics from the attached PDF alone:

1. **Finite set versus ordered sequence access.** Page 3 defines `X^*` as finite subsets, while Definition 2.3 calls the input a finite sequence and Algorithm 1 uses suffixes and appended outputs. Lean chooses the ordered model. There is no internally consistent single literal reading in the PDF.
2. **Definition D.1 trigger statistic.** Page 11 says D.1 counts all distinct examples, but the displayed Definition D.1 and Lemma D.2 proof on page 13 count distinct positive examples. Lean chooses the latter. No corrected sentence or erratum is supplied.
3. **Positive versus zero-based naturals.** The paper uses `N∪{0}` in one preliminary definition, suggesting `N` may be positive, while Lean's `ℕ` includes zero throughout. The main existential generation properties are not materially changed, but exact size-zero witness statements are stronger.

There is also no supplied compilation log or kernel-check certificate. Accordingly, this audit makes no claim that the source compiled or that theorem bodies establish their signatures.

## 12. Check of the Stage-1 reconstruction

The Stage-1 artifact is reliable as a reconstruction of the Lean statements. Its main cautions—occurrence noise versus distinct-value closure noise, exact-trigger vacuity, nonmatching non-uniform covers, noncomputability, empty-version-space handling, and separate finite/infinite dimension predicates—are confirmed by direct signature inspection.

Stage 2 adds three material refinements that could not be seen code-only:

- the printed paper's finite-set/ordered-sequence inconsistency;
- the duplicate-sensitive preliminary noisy-version notation and Lean's deduplicating repair;
- the Appendix D contradiction and the missing quantitative claims attached to Theorem 3.3 and Lemma 3.8.

The Stage-1 description of the final robustification as “literal Algorithm 1” should be read with the totalization and arbitrary-candidate qualifications in §5.7.

## 13. Compact verdict table

| Paper item | Correspondence verdict | Difficulty verdict | Compact reason |
|---|---|---|---|
| Definitions 2.4–2.7 | Exact / formally equivalent | Preserved | Quantifier order, noise, trigger, and coverage match. |
| Theorem 3.1 | Faithful specialization | Weakened / easier | Adds infinite universe to repair empty-class finite-universe failure. |
| Definition 3.2 witness semantics | Exact / formally equivalent | Preserved | Finset witnesses equal injective distinct sequences. |
| Definition 3.2 numerical dimension | Related but materially different | Weakened / easier | No numerical extended-natural object or complement theorem. |
| Theorem 3.3 qualitative iff | Faithful specialization | Weakened / easier | Adds nonempty universe; qualitative boundedness matches. |
| Theorem 3.3 quantitative claims | Not represented in Lean | Indeterminate | No exact `NC_n`, minimal threshold, or `Θ` theorem. |
| Corollary 3.4 | Faithful specialization | Weakened / easier | Qualitative result plus linear witness bound; adds inhabitation. |
| Lemma 3.5 | Faithful specialization | Weakened / easier | Concrete countably infinite universe repairs printed quantification. |
| Lemma 3.6 | Faithful specialization | Weakened / easier | Same diagonal cover; adds inhabitation. |
| Corollary 3.7 | Faithful specialization | Weakened / easier | Same two conclusions; adds inhabitation. |
| Lemma 3.8 qualitative | Exact / formally equivalent | Preserved | `∀n∃cover_n` order is exact. |
| Lemma 3.8 bound `<i` | Not represented in Lean | Indeterminate | Only finiteness is stated. |
| Theorem 3.9 | Exact / formally equivalent | Preserved | Same one-way qualitative robustification and stream class. |
| Algorithm 1 | Related but materially different | Preserved | Totalized suffix and arbitrary fresh-candidate choice. |
| Theorem 3.10 | Faithful specialization | Weakened / easier | Adds infinite universe and repairs finite-noise cutoff. |
| Definition C.1 | Exact / formally equivalent | Preserved | Positive-count trigger matches. |
| Lemma C.2 | Exact / formally equivalent | Preserved | Structural obstruction matches. |
| Theorem C.3 | Faithful specialization | Weakened / easier | Exact witness-bound reading; adds inhabitation. |
| Displayed Definition D.1 | Exact / formally equivalent | Preserved | Lean follows positive-count formula and proof. |
| Page-11 prose about D.1 | Indeterminate from the supplied evidence | Indeterminate | Direct contradiction inside the PDF. |
| Lemma D.2 | Faithful specialization | Weakened / easier | Concrete `ℕ` universe matches proof. |

## 14. Overall paper-level conclusion

The formalization captures the paper's central qualitative mathematics:

- the uniform noise-independent intersection characterization;
- the uniform noise-dependent finite-dimension characterization;
- finite and countable class corollaries;
- non-uniform cover sufficiency and necessity with their intended mismatch;
- noiseless-to-noisy robustification;
- finite-union sufficiency;
- the two appendix characterizations/counterexamples.

It is best classified as a **substantially faithful repaired formalization**. The repairs mostly address false or undefined degenerate cases and proof gaps without altering the intended nondegenerate theorems. The major loss is quantitative: Lean formalizes boundedness rather than the numerical noisy closure dimension and therefore does not capture the paper's strongest sample-complexity statements. No main theorem is vacuously obtained from a conclusion-encoding premise, although the underlying exact-trigger definitions remain vulnerable to stream-level vacuity exactly as in the paper.

## Executive summary for the consolidated 36-paper audit

Paper 06 is **qualitatively faithful with explicit repairs**. All numbered principal results have Lean counterparts. Definitions 2.4–2.7, Lemma 3.8, Theorem 3.9, Lemma C.2, and displayed Definition D.1 are exact at statement level. Theorem 3.1, Theorem 3.3, Corollaries 3.4/3.7, Lemmas 3.5/3.6/D.2, Theorem 3.10, and Theorem C.3 are faithful specializations adding nonempty/infinite or concrete-universe assumptions that repair genuine degenerate counterexamples in the printed paper. The formalization preserves occurrence-count noise, target coverage for noisy presentations, quantifier dependence, ordered-history access, and the nonmatching cover quantifiers. It does not formalize the numerical `NC_n`, the `Θ(NC_n)` sample complexity, or the bound `NC_n(H_i)<i`. Algorithm 1 and Appendix G are implemented by valid repaired variants. The PDF itself is inconsistent about finite-set versus sequence access and about whether Definition D.1 counts all distinct or positive distinct examples; Lean follows the operationally coherent sequence/positive-count readings.

## Appendix A. Exact/whitespace-normalized signatures for substantive target-scope claims

All declarations below are in namespace `GenLimit.NoisyExamples`. The displayed paths are the exact primary source paths in the supplied bundle. Proof bodies are omitted after the declaration type.

### S01. `infinite_commonIntersection_implies_uniform_noiseIndependent`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/UniformIndependent.lean`

```lean
theorem GenLimit.NoisyExamples.infinite_commonIntersection_implies_uniform_noiseIndependent
    {H : GenLimit.Generic.LanguageClass α}
    (hcommon : (commonIntersection H).Infinite) :
    UniformNoiseIndependentGeneratable H
```

### S02. `finite_commonIntersection_defeats_threshold`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/UniformIndependent.lean`

```lean
theorem GenLimit.NoisyExamples.finite_commonIntersection_defeats_threshold [Infinite α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (hfinite : (commonIntersection H).Finite)
    (gen : GenLimit.Generic.Generator α) (d : ℕ) :
    ∃ L, L ∈ H ∧ ∃ stream : GenLimit.Generic.Stream α,
      HasFiniteNoise stream L ∧
      ∃ t, (GenLimit.Generic.sample stream t).card = d ∧
        ∃ s, t ≤ s ∧ ¬GenLimit.Generic.CorrectAt gen L stream s
```

### S03. `uniform_noiseIndependent_implies_infinite_commonIntersection`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/UniformIndependent.lean`

```lean
theorem GenLimit.NoisyExamples.uniform_noiseIndependent_implies_infinite_commonIntersection
    [Infinite α] {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (hgen : UniformNoiseIndependentGeneratable H) :
    (commonIntersection H).Infinite
```

### S04. `theorem_3_1`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/UniformIndependent.lean`

```lean
theorem GenLimit.NoisyExamples.theorem_3_1 [Countable α] [Infinite α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H) :
    UniformNoiseIndependentGeneratable H ↔
      (commonIntersection H).Infinite
```

### S05. `noisyClosureWitnessAt_iff_injective_sequence`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.noisyClosureWitnessAt_iff_injective_sequence
    {H : GenLimit.Generic.LanguageClass α} {n d : ℕ} :
    NoisyClosureWitnessAt H n d ↔
      ∃ xs : Fin d → α, Function.Injective xs ∧
        (noisyVersionSpace H (GenLimit.Generic.sequenceSample xs) n).Nonempty ∧
        (noisyCommonCore H (GenLimit.Generic.sequenceSample xs) n).Finite
```

### S06. `finiteNoisyClosureDimensionAt_iff_eventually_infinite`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.finiteNoisyClosureDimensionAt_iff_eventually_infinite
    {H : GenLimit.Generic.LanguageClass α} {n : ℕ} :
    FiniteNoisyClosureDimensionAt H n ↔
      ∃ D : ℕ, ∀ S : Finset α, D < S.card →
        (noisyVersionSpace H S n).Nonempty →
        (noisyCommonCore H S n).Infinite
```

### S07. `bad_sample_card_le_noise`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.bad_sample_card_le_noise
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {n t : ℕ}
    (hnoise : HasNoiseAtMost stream L n) :
    (negativePart (GenLimit.Generic.sample stream t) L).card ≤ n
```

### S08. `target_mem_noisyVersionSpace`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.target_mem_noisyVersionSpace
    {H : GenLimit.Generic.LanguageClass α}
    {L : GenLimit.Generic.Language α} (hLH : L ∈ H)
    {stream : GenLimit.Generic.Stream α} {n t : ℕ}
    (hnoise : HasNoiseAtMost stream L n) :
    L ∈ noisyVersionSpace H (GenLimit.Generic.sample stream t) n
```

### S09. `finite_noisyClosureDimensions_imply_uniform_noiseDependent`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.finite_noisyClosureDimensions_imply_uniform_noiseDependent
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n) :
    UniformNoiseDependentGeneratable H
```

### S10. `arbitrarily_large_witness_of_not_finiteNoisyClosureDimensionAt`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.arbitrarily_large_witness_of_not_finiteNoisyClosureDimensionAt
    {H : GenLimit.Generic.LanguageClass α} {n : ℕ}
    (hnot : ¬FiniteNoisyClosureDimensionAt H n) :
    ∀ D : ℕ, ∃ d : ℕ, D < d ∧ NoisyClosureWitnessAt H n d
```

### S11. `nonfinite_noisyClosureDimension_defeats_threshold`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.nonfinite_noisyClosureDimension_defeats_threshold
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    {n : ℕ} (hnot : ¬FiniteNoisyClosureDimensionAt H n)
    (gen : GenLimit.Generic.Generator α) (d : ℕ) :
    ∃ L, L ∈ H ∧ ∃ stream : GenLimit.Generic.Stream α,
      HasNoiseAtMost stream L n ∧
      ∃ t, (GenLimit.Generic.sample stream t).card = d ∧
        ∃ s, t ≤ s ∧ ¬GenLimit.Generic.CorrectAt gen L stream s
```

### S12. `uniform_noiseDependent_implies_finite_noisyClosureDimensions`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.uniform_noiseDependent_implies_finite_noisyClosureDimensions
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (hgen : UniformNoiseDependentGeneratable H) :
    ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n
```

### S13. `theorem_3_3`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.theorem_3_3 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H) :
    UniformNoiseDependentGeneratable H ↔
      ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n
```

### S14. `noisy_witness_card_le_for_finite_class`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteClasses.lean`

```lean
theorem GenLimit.NoisyExamples.noisy_witness_card_le_for_finite_class
    {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite)
    (B : ℕ)
    (hB : ∀ V : Set (GenLimit.Generic.Language α),
      V ⊆ H → (classCore V).Finite → (classCore V).ncard ≤ B)
    {S : Finset α} {n : ℕ}
    (hcore : (noisyCommonCore H S n).Finite) :
    S.card ≤ B + H.ncard * n
```

### S15. `finite_class_has_finite_noisyClosureDimensionAt`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteClasses.lean`

```lean
theorem GenLimit.NoisyExamples.finite_class_has_finite_noisyClosureDimensionAt
    {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite)
    (n : ℕ) : FiniteNoisyClosureDimensionAt H n
```

### S16. `corollary_3_4`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteClasses.lean`

```lean
theorem GenLimit.NoisyExamples.corollary_3_4 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (hH : H.Finite) :
    UniformNoiseDependentGeneratable H
```

### S17. `hasFiniteNoise_of_hasNoiseAtMost`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformDefinitions.lean`

```lean
theorem GenLimit.NoisyExamples.hasFiniteNoise_of_hasNoiseAtMost
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {n : ℕ}
    (hnoise : HasNoiseAtMost stream L n) :
    HasFiniteNoise stream L
```

### S18. `exists_hasNoiseAtMost_of_hasFiniteNoise`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformDefinitions.lean`

```lean
theorem GenLimit.NoisyExamples.exists_hasNoiseAtMost_of_hasFiniteNoise
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hnoise : HasFiniteNoise stream L) :
    ∃ n, HasNoiseAtMost stream L n
```

### S19. `uniform_noiseDependent_implies_nonuniform_noiseDependent`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformDefinitions.lean`

```lean
theorem GenLimit.NoisyExamples.uniform_noiseDependent_implies_nonuniform_noiseDependent
    {H : GenLimit.Generic.LanguageClass α}
    (h : UniformNoiseDependentGeneratable H) :
    NonuniformNoiseDependentGeneratable H
```

### S20. `nonuniform_noiseDependent_implies_noisy_limit`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformDefinitions.lean`

```lean
theorem GenLimit.NoisyExamples.nonuniform_noiseDependent_implies_noisy_limit
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (h : NonuniformNoiseDependentGeneratable H) :
    NoisilyGeneratableInLimit H
```

### S21. `lemma_3_6`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

```lean
theorem GenLimit.NoisyExamples.lemma_3_6 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (_hUUS : GenLimit.LiRamanTewari.UUS H)
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hcover : GenLimit.LiRamanTewari.IsNondecreasingCover H classes)
    (hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i) :
    NonuniformNoiseDependentGeneratable H
```

### S22. `lemma_3_8`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

```lean
theorem GenLimit.NoisyExamples.lemma_3_8 [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (hgen : NonuniformNoiseDependentGeneratable H) :
    ∀ n : ℕ, ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
      GenLimit.LiRamanTewari.IsNondecreasingCover H classes ∧
      ∀ i, FiniteNoisyClosureDimensionAt (classes i) n
```

### S23. `corollary_3_7`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

```lean
theorem GenLimit.NoisyExamples.corollary_3_7 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (hCountable : H.Countable) :
    NonuniformNoiseDependentGeneratable H ∧ NoisilyGeneratableInLimit H
```

### S24. `nonuniform_generator_correct_on_finite_history`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.nonuniform_generator_correct_on_finite_history
    [DecidableEq α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (history : List α)
    (hhistory : (↑history.toFinset : Set α) ⊆ L)
    (hcard : d ≤ history.toFinset.card) :
    Q history.length history.get ∈ L \ (history.toFinset : Set α)
```

### S25. `iteratedGeneratorHistory_properties`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.iteratedGeneratorHistory_properties
    [DecidableEq α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (base : List α) (hbase : (↑base.toFinset : Set α) ⊆ L)
    (hbaseCard : d ≤ base.toFinset.card) :
    ∀ j : ℕ,
      (↑(iteratedGeneratorHistory Q base j).toFinset : Set α) ⊆ L ∧
      base.toFinset ⊆ (iteratedGeneratorHistory Q base j).toFinset ∧
      (iteratedGeneratorHistory Q base j).toFinset.card =
        base.toFinset.card + j
```

### S26. `generatedCandidate_not_in_history`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.generatedCandidate_not_in_history
    [DecidableEq α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (history : List α) (r : ℕ)
    (hbase : (↑(history.drop r).toFinset : Set α) ⊆ L)
    (hbaseCard : d ≤ (history.drop r).toFinset.card) :
    (generatedCandidateSet Q (history.drop r) (r + 1) \
      history.toFinset).Nonempty
```

### S27. `paperRobustifiedNoiselessGenerator_correct`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.paperRobustifiedNoiselessGenerator_correct
    [DecidableEq α] [Nonempty α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d t : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ q, (GenLimit.Generic.sample stream q).card = d →
        ∀ s, q ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (history : Fin t → α)
    (hbase :
      (↑((List.ofFn history).drop
        (paperBalancedSuffixStart history)).toFinset : Set α) ⊆ L)
    (hbaseCard : d ≤
      ((List.ofFn history).drop
        (paperBalancedSuffixStart history)).toFinset.card) :
    paperRobustifiedNoiselessGenerator Q t history ∈ L \
      ((List.ofFn history).toFinset : Set α)
```

### S28. `eventually_paperBalanced_suffix_positive_and_large`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.eventually_paperBalanced_suffix_positive_and_large
    [DecidableEq α]
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hLInfinite : L.Infinite)
    (hP : NoisyPresentation stream L)
    (d : ℕ) :
    ∃ T : ℕ, ∀ s, T ≤ s →
      let history : Fin s → α
```

### S29. `theorem_3_9`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.theorem_3_9 [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (hNonuniform : GenLimit.LiRamanTewari.NonuniformlyGeneratable H) :
    NoisilyGeneratableInLimit H
```

### S30. `noisyWinningIndex_spec`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteUnionLimit.lean`

```lean
theorem GenLimit.NoisyExamples.noisyWinningIndex_spec [Countable α] {k : ℕ}
    (classes : Fin k → GenLimit.Generic.LanguageClass α)
    (hcores : ∀ i, (commonIntersection (classes i)).Infinite)
    (current : Finset α)
    (hindices : (Finset.univ : Finset (Fin k)).Nonempty) :
    ∃ selected,
      noisyWinningIndex classes hcores current = some selected ∧
      ∀ i, noisyEnumerationProgress (commonIntersection (classes i))
          (hcores i) current ≤
        noisyEnumerationProgress (commonIntersection (classes selected))
          (hcores selected) current
```

### S31. `theorem_3_10`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteUnionLimit.lean`

```lean
theorem GenLimit.NoisyExamples.theorem_3_10 [Countable α] [Infinite α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (hcover : ∃ k : ℕ,
      ∃ classes : Fin k → GenLimit.Generic.LanguageClass α,
        GenLimit.LiRamanTewari.IsFiniteCover H classes ∧
        ∀ i, UniformNoiseIndependentGeneratable (classes i)) :
    NoisilyGeneratableInLimit H
```

### S32. `separation_hasClosureDimension_zero`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Separation.lean`

```lean
theorem GenLimit.NoisyExamples.separation_hasClosureDimension_zero :
    GenLimit.LiRamanTewari.HasClosureDimension separationClass 0
```

### S33. `separation_oneNoisyWitness_every_card`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Separation.lean`

```lean
theorem GenLimit.NoisyExamples.separation_oneNoisyWitness_every_card (d : ℕ) :
    NoisyClosureWitnessAt separationClass 1 d
```

### S34. `separationClass_properties`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Separation.lean`

```lean
theorem GenLimit.NoisyExamples.separationClass_properties :
    separationClass.Countable ∧
      GenLimit.LiRamanTewari.UUS separationClass ∧
      GenLimit.LiRamanTewari.HasClosureDimension separationClass 0 ∧
      InfiniteNoisyClosureDimensionAt separationClass 1
```

### S35. `lemma_3_5`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Separation.lean`

```lean
theorem GenLimit.NoisyExamples.lemma_3_5 :
    ∃ H : GenLimit.Generic.LanguageClass SeparationPoint,
      H.Countable ∧
      GenLimit.LiRamanTewari.UUS H ∧
      GenLimit.LiRamanTewari.HasClosureDimension H 0 ∧
      InfiniteNoisyClosureDimensionAt H 1
```

### S36. `separation_not_uniform_noiseDependent`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Separation.lean`

```lean
theorem GenLimit.NoisyExamples.separation_not_uniform_noiseDependent :
    ¬UniformNoiseDependentGeneratable separationClass
```

### S37. `boundedNoisyClosureExcess_implies_alternateUniform`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/AlternatePositive.lean`

```lean
theorem GenLimit.NoisyExamples.boundedNoisyClosureExcess_implies_alternateUniform
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hbound : BoundedNoisyClosureExcess H) :
    AlternateUniformNoiseIndependentGeneratable H
```

### S38. `noisyExcessWitness_defeats_alternate_threshold`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/AlternatePositive.lean`

```lean
theorem GenLimit.NoisyExamples.noisyExcessWitness_defeats_alternate_threshold
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    {n k : ℕ} (hwit : NoisyClosureWitnessAt H n k)
    {d : ℕ} (hlarge : n + d < k)
    (gen : GenLimit.Generic.Generator α) :
    ∃ L, L ∈ H ∧ ∃ stream : GenLimit.Generic.Stream α,
      HasFiniteNoise stream L ∧
      ∃ t,
        (positivePart (GenLimit.Generic.sample stream t) L).card = d ∧
        ∃ s, t ≤ s ∧ ¬GenLimit.Generic.CorrectAt gen L stream s
```

### S39. `alternateUniform_implies_boundedNoisyClosureExcess`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/AlternatePositive.lean`

```lean
theorem GenLimit.NoisyExamples.alternateUniform_implies_boundedNoisyClosureExcess
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (hgen : AlternateUniformNoiseIndependentGeneratable H) :
    BoundedNoisyClosureExcess H
```

### S40. `theorem_C_3`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/AlternatePositive.lean`

```lean
theorem GenLimit.NoisyExamples.theorem_C_3 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H) :
    AlternateUniformNoiseIndependentGeneratable H ↔
      BoundedNoisyClosureExcess H
```

### S41. `lemma_C_2`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/AlternatePositive.lean`

```lean
theorem GenLimit.NoisyExamples.lemma_C_2 [Countable α]
    {H F : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.LiRamanTewari.UUS H)
    (hFH : F ⊆ H)
    {f : GenLimit.Generic.Language α} (hfF : f ∈ F)
    (hcommonFinite : (commonIntersection F).Finite)
    (hwithoutInfinite : (commonIntersection (F \ {f})).Infinite) :
    ¬AlternateUniformNoiseIndependentGeneratable H
```

### S42. `parityClass_not_nonuniform_noiseIndependent`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformIndependent.lean`

```lean
theorem GenLimit.NoisyExamples.parityClass_not_nonuniform_noiseIndependent :
    parityClass.Finite ∧
      GenLimit.LiRamanTewari.UUS parityClass ∧
      ¬NonuniformNoiseIndependentGeneratable parityClass
```

### S43. `lemma_D_2`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformIndependent.lean`

```lean
theorem GenLimit.NoisyExamples.lemma_D_2 :
    ∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Finite ∧
      GenLimit.LiRamanTewari.UUS H ∧
      ¬NonuniformNoiseIndependentGeneratable H
```


## Appendix B. Exact/whitespace-normalized signatures for principal helper links

These are the separately stated public helper signatures cited in §6. Private source-level helpers are described there but are not assigned potentially unstable elaborated names.

### H01. `commonIntersection_subset_of_mem`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/UniformIndependent.lean`

```lean
theorem GenLimit.NoisyExamples.commonIntersection_subset_of_mem
    {H : GenLimit.Generic.LanguageClass α}
    {L : GenLimit.Generic.Language α} (hL : L ∈ H) :
    commonIntersection H ⊆ L
```

### H02. `commonIntersectionGenerator_spec`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/UniformIndependent.lean`

```lean
theorem GenLimit.NoisyExamples.commonIntersectionGenerator_spec
    {H : GenLimit.Generic.LanguageClass α}
    (hcommon : (commonIntersection H).Infinite)
    {t : ℕ} (xs : Fin t → α) :
    commonIntersectionGenerator H hcommon t xs ∈
      commonIntersection H \
        (↑(GenLimit.Generic.sequenceSample xs) : Set α)
```

### H03. `noisyClosure_eq_none_iff`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.noisyClosure_eq_none_iff
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {n : ℕ} :
    noisyClosure H S n = none ↔ ¬(noisyVersionSpace H S n).Nonempty
```

### H04. `noisyClosure_eq_some_iff`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.noisyClosure_eq_some_iff
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {n : ℕ}
    {C : GenLimit.Generic.Language α} :
    noisyClosure H S n = some C ↔
      (noisyVersionSpace H S n).Nonempty ∧ C = noisyCommonCore H S n
```

### H05. `noisyCommonCore_subset_of_mem_versionSpace`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.noisyCommonCore_subset_of_mem_versionSpace
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {n : ℕ}
    {L : GenLimit.Generic.Language α}
    (hL : L ∈ noisyVersionSpace H S n) :
    noisyCommonCore H S n ⊆ L
```

### H06. `negativePart_card_le_of_mem_noisyVersionSpace`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.negativePart_card_le_of_mem_noisyVersionSpace
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {n : ℕ}
    {L : GenLimit.Generic.Language α}
    (hL : L ∈ noisyVersionSpace H S n) :
    (negativePart S L).card ≤ n
```

### H07. `noisyClosureBound_spec`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.noisyClosureBound_spec
    {H : GenLimit.Generic.LanguageClass α}
    (hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n)
    (n : ℕ) (S : Finset α)
    (hlarge : noisyClosureBound H hdim n < S.card)
    (hVS : (noisyVersionSpace H S n).Nonempty) :
    (noisyCommonCore H S n).Infinite
```

### H08. `mem_eligibleNoiseLevels_iff`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.mem_eligibleNoiseLevels_iff
    {H : GenLimit.Generic.LanguageClass α}
    {hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n}
    {S : Finset α} {t n : ℕ} :
    n ∈ eligibleNoiseLevels H hdim S t ↔
      n ≤ t ∧ noisyClosureBound H hdim n < S.card ∧
        (noisyVersionSpace H S n).Nonempty
```

### H09. `selectedNoiseLevel_mem`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.selectedNoiseLevel_mem
    {H : GenLimit.Generic.LanguageClass α}
    {hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n}
    {S : Finset α} {t : ℕ}
    (hE : (eligibleNoiseLevels H hdim S t).Nonempty) :
    selectedNoiseLevel H hdim S t hE ∈
      eligibleNoiseLevels H hdim S t
```

### H10. `le_selectedNoiseLevel`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.le_selectedNoiseLevel
    {H : GenLimit.Generic.LanguageClass α}
    {hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n}
    {S : Finset α} {t n : ℕ}
    (hn : n ∈ eligibleNoiseLevels H hdim S t)
    (hE : (eligibleNoiseLevels H hdim S t).Nonempty) :
    n ≤ selectedNoiseLevel H hdim S t hE
```

### H11. `freshFromNoisyCore_spec`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.freshFromNoisyCore_spec
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α} {n : ℕ}
    (hcore : (noisyCommonCore H S n).Infinite) :
    freshFromNoisyCore H S n hcore ∈
      noisyCommonCore H S n \ (S : Set α)
```

### H12. `noisyClosureStrategyOutput_spec`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.noisyClosureStrategyOutput_spec [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    {hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n}
    {S : Finset α} {t : ℕ}
    (hE : (eligibleNoiseLevels H hdim S t).Nonempty) :
    let n
```

### H13. `noisyClosureStrategy_output`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoisyClosure.lean`

```lean
theorem GenLimit.NoisyExamples.noisyClosureStrategy_output
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    {hdim : ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n}
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    GenLimit.Generic.output (noisyClosureStrategy H hdim) stream t =
      noisyClosureStrategyOutput H hdim
        (GenLimit.Generic.sample stream t) t
```

### H14. `noisyPresentation_range_infinite`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformDefinitions.lean`

```lean
theorem GenLimit.NoisyExamples.noisyPresentation_range_infinite
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hL : L.Infinite) (hP : NoisyPresentation stream L) :
    (Set.range stream).Infinite
```

### H15. `exists_sample_card_eq_of_range_infinite`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NonuniformDefinitions.lean`

```lean
theorem GenLimit.NoisyExamples.exists_sample_card_eq_of_range_infinite
    {stream : GenLimit.Generic.Stream α}
    (hrange : (Set.range stream).Infinite) (d : ℕ) :
    ∃ t, (GenLimit.Generic.sample stream t).card = d
```

### H16. `diagonalNoisyClosureBound_spec`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

```lean
theorem GenLimit.NoisyExamples.diagonalNoisyClosureBound_spec
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i)
    (i : ℕ) (S : Finset α)
    (hlarge : diagonalNoisyClosureBound classes hdim i < S.card)
    (hVS : (noisyVersionSpace (classes i) S i).Nonempty) :
    (noisyCommonCore (classes i) S i).Infinite
```

### H17. `mem_diagonalEligibleIndices_iff`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

```lean
theorem GenLimit.NoisyExamples.mem_diagonalEligibleIndices_iff
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i}
    {S : Finset α} {t i : ℕ} :
    i ∈ diagonalEligibleIndices classes hdim S t ↔
      i ≤ t ∧ diagonalNoisyClosureBound classes hdim i < S.card ∧
        (noisyVersionSpace (classes i) S i).Nonempty
```

### H18. `selectedDiagonalIndex_mem`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

```lean
theorem GenLimit.NoisyExamples.selectedDiagonalIndex_mem
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i}
    {S : Finset α} {t : ℕ}
    (hE : (diagonalEligibleIndices classes hdim S t).Nonempty) :
    selectedDiagonalIndex classes hdim S t hE ∈
      diagonalEligibleIndices classes hdim S t
```

### H19. `le_selectedDiagonalIndex`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

```lean
theorem GenLimit.NoisyExamples.le_selectedDiagonalIndex
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i}
    {S : Finset α} {t i : ℕ}
    (hi : i ∈ diagonalEligibleIndices classes hdim S t)
    (hE : (diagonalEligibleIndices classes hdim S t).Nonempty) :
    i ≤ selectedDiagonalIndex classes hdim S t hE
```

### H20. `diagonalNoisyStrategyOutput_spec`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

```lean
theorem GenLimit.NoisyExamples.diagonalNoisyStrategyOutput_spec [Nonempty α]
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i}
    {S : Finset α} {t : ℕ}
    (hE : (diagonalEligibleIndices classes hdim S t).Nonempty) :
    let i
```

### H21. `diagonalNoisyStrategy_output`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/Nonuniform.lean`

```lean
theorem GenLimit.NoisyExamples.diagonalNoisyStrategy_output [Nonempty α]
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    {hdim : ∀ i, FiniteNoisyClosureDimensionAt (classes i) i}
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    GenLimit.Generic.output (diagonalNoisyStrategy classes hdim) stream t =
      diagonalNoisyStrategyOutput classes hdim
        (GenLimit.Generic.sample stream t) t
```

### H22. `paperBalancedSuffixStart_card`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.paperBalancedSuffixStart_card [DecidableEq α]
    {t : ℕ} (history : Fin t → α) :
    ((List.ofFn history).drop
      (paperBalancedSuffixStart history)).toFinset.card =
        (List.ofFn history).toFinset.card / 2
```

### H23. `start_le_paperBalancedSuffixStart_of_large`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.start_le_paperBalancedSuffixStart_of_large [DecidableEq α]
    {t : ℕ} {history : Fin t → α} {r : ℕ}
    (hlarge : 2 * r ≤ (List.ofFn history).toFinset.card) :
    r ≤ paperBalancedSuffixStart history
```

### H24. `mem_target_after_finiteNoiseCutoff`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.mem_target_after_finiteNoiseCutoff
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hnoise : HasFiniteNoise stream L) {t : ℕ}
    (ht : finiteNoiseCutoff hnoise ≤ t) :
    stream t ∈ L
```

### H25. `generatedCandidateSet_card`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.generatedCandidateSet_card
    [DecidableEq α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (base : List α) (hbase : (↑base.toFinset : Set α) ⊆ L)
    (hbaseCard : d ≤ base.toFinset.card) (count : ℕ) :
    (generatedCandidateSet Q base count).card = count
```

### H26. `generatedCandidateSet_positive`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/NoiselessRobustification.lean`

```lean
theorem GenLimit.NoisyExamples.generatedCandidateSet_positive
    [DecidableEq α]
    {Q : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α} {d : ℕ}
    (hLInfinite : L.Infinite)
    (hd : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt Q L stream s)
    (base : List α) (hbase : (↑base.toFinset : Set α) ⊆ L)
    (hbaseCard : d ≤ base.toFinset.card) (count : ℕ) :
    (↑(generatedCandidateSet Q base count) : Set α) ⊆ L
```

### H27. `noisyEnumerationProgress_spec`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteUnionLimit.lean`

```lean
theorem GenLimit.NoisyExamples.noisyEnumerationProgress_spec [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    noisyInfiniteEnumeration C hC (noisyEnumerationProgress C hC S) ∉ S
```

### H28. `noisy_progress_le_of_not_mem`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/FiniteUnionLimit.lean`

```lean
theorem GenLimit.NoisyExamples.noisy_progress_le_of_not_mem [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) {k : ℕ}
    (hk : noisyInfiniteEnumeration C hC k ∉ S) :
    noisyEnumerationProgress C hC S ≤ k
```

### H29. `excessNoisyClosureStrategyOutput_spec`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/AlternatePositive.lean`

```lean
theorem GenLimit.NoisyExamples.excessNoisyClosureStrategyOutput_spec [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α} {B : ℕ}
    {S : Finset α}
    (hcore :
      (noisyCommonCore H S (S.card - (B + 1))).Infinite) :
    excessNoisyClosureStrategyOutput H B S ∈
      noisyCommonCore H S (S.card - (B + 1)) \ (S : Set α)
```

### H30. `excessNoisyClosureStrategy_output`

**Path:** `GenLimitLean/GenLimit/Paper06_GenerationFromNoisyExamples/AlternatePositive.lean`

```lean
theorem GenLimit.NoisyExamples.excessNoisyClosureStrategy_output [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α) (B : ℕ)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    GenLimit.Generic.output (excessNoisyClosureStrategy H B) stream t =
      excessNoisyClosureStrategyOutput H B
        (GenLimit.Generic.sample stream t)
```



## Final compact verdict

| Main paper result | Correspondence verdict | Difficulty verdict |
|---|---|---|
| Theorem 3.1 | Faithful specialization | Weakened / easier |
| Theorem 3.3, qualitative iff | Faithful specialization | Weakened / easier |
| Theorem 3.3, quantitative sample complexity | Not represented in Lean | Indeterminate |
| Corollary 3.4 | Faithful specialization | Weakened / easier |
| Lemma 3.5 | Faithful specialization | Weakened / easier |
| Lemma 3.6 | Faithful specialization | Weakened / easier |
| Corollary 3.7 | Faithful specialization | Weakened / easier |
| Lemma 3.8, qualitative cover | Exact / formally equivalent | Preserved |
| Lemma 3.8, bound `NC_n(H_i)<i` | Not represented in Lean | Indeterminate |
| Theorem 3.9 | Exact / formally equivalent | Preserved |
| Theorem 3.10 | Faithful specialization | Weakened / easier |
| Lemma C.2 | Exact / formally equivalent | Preserved |
| Theorem C.3 | Faithful specialization | Weakened / easier |
| Lemma D.2 | Faithful specialization | Weakened / easier |

**Overall paper-level verdict:** **Substantially faithful repaired formalization.** The qualitative mathematical map is preserved, the added universe assumptions and concrete examples repair real source-level degeneracies, and no main theorem is circular or trivialized. The principal loss is the paper's numerical and asymptotic noisy-closure sample-complexity content.

**Executive summary for the consolidated 36-paper audit:** Paper 06 formalizes all principal qualitative results with high fidelity. Exact matches include the noisy generation notions, Lemma 3.8's quantifier order, Theorem 3.9, Lemma C.2, and displayed Definition D.1. Most remaining numbered results are faithful specializations that add nonempty/infinite or concrete-universe assumptions to repair false degenerate cases in the PDF. Lean correctly preserves occurrence-count noise, distinct-value closure witnesses, target coverage for noisy presentations, target/noise/stream dependence, and the nonmatching cover conditions. It does not formalize a numerical `NC_n`, the `Θ(NC_n)` sample complexity, or the proof-level bound `NC_n(H_i)<i`. Algorithm 1 and Appendix G are represented by valid repaired variants. The paper itself is internally inconsistent about finite-set versus ordered-sequence access and about Definition D.1's trigger statistic; Lean chooses the operationally coherent readings.
