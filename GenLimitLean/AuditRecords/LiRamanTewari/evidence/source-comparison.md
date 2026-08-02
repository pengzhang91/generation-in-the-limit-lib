# 02 — Paper02_GenerationThroughTheLensOfLearningTheory — Generation through the Lens of Learning Theory — Lean Faithfulness Audit

## Audit status, evidence, and source verification

This is the Stage 2 statement-faithfulness audit requested for Paper 02. It compares only the following three conversation-local sources:

1. `02-2410.13714v5.pdf`, the supplied author source;
2. `02__Paper02_GenerationThroughTheLensOfLearningTheory__lean-source-bundle.txt`, the supplied deterministic Lean bundle at repository commit `dfcd13534f9d51642a9f88904268e95454c88f7f`;
3. `02-generation-through-the-lens-of-learning-theory-lean-statement-reconstruction.md`, the Stage 1 reconstruction, treated here only as a fallible index.

No web source or substituted paper version was used.

The new PDF was verified before comparison:

- byte length: `706525`;
- SHA-256: `acaf59abdb4542173cb20dd05e874f7fa5b505bf7b2c5c561529d5e387502482`;
- readable PDF metadata: 35 pages, unencrypted;
- text extraction succeeded and produced nonempty text covering all 35 pages, including the numbered statements and appendices.

The Lean bundle was independently verified at `295728` bytes with SHA-256 `46a46f86c03e8fa7300b7efa3d223141942bee91d95476c7afa818bf889c7146`; all 21 embedded source files were extracted byte-for-byte for inspection. Every one of the 234 exact/normalized declarations quoted in Appendices A–B was independently checked to occur in the corresponding extracted Lean source, rather than copied on trust from the Stage 1 prose. The Stage 1 artifact was left unchanged.

This is a **source-statement audit**, not a build audit. The presence of declarations and proof text in the bundle is not taken as evidence that the snapshot compiles or that Lean has accepted the proofs. The semantic evidence on the Lean side is limited to declaration types and statement-relevant definition bodies, with proof bodies ignored.

### Verdict vocabulary

Every comparison below uses exactly one correspondence verdict from the requested list:

- **Exact / formally equivalent**
- **Faithful specialization**
- **Faithful generalization**
- **Related but materially different**
- **Not represented in Lean**
- **Extra Lean result not claimed by the paper**
- **Indeterminate from the supplied evidence**

Every comparison also uses exactly one difficulty verdict:

- **Preserved**
- **Strengthened / harder**
- **Weakened / easier**
- **Collapsed / trivialized**
- **Indeterminate**

## Executive finding

The ordinary generation theory and the prompted generation theory are, at the level of their principal definitions, quantifier order, closure dimensions, characterizations, hierarchy separations, and finite/countable-cover results, **substantially faithful**. The Lean source usually states the same theorem over a generic countable type and adds an explicit `Nonempty α` assumption where the paper silently needs an output value. Several witness constructions use isomorphic tagged universes rather than the paper's arithmetic examples; because the author statements are existential, these are faithful specializations or generalizations rather than changes to the advertised mathematical content.

There are, however, two material paper-level exceptions.

First, the Lean development does **not** formalize the paper's PAC or online learning models. It defines

```lean
def PACLearnableViaVC (H : GenLimit.Generic.LanguageClass α) : Prop :=
  HasFiniteVCDimension H

def OnlineLearnableViaLittlestone
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  HasFiniteLittlestoneDimension H
```

and then states the six regions of Theorem 4.1 using those abbreviations. Thus, no probability space, iid sample, learning algorithm, risk, confidence parameter, prediction protocol, mistake count, or sublinear regret bound occurs in the formal theorem. The six-way Lean result is a nontrivial **dimension-and-generation** theorem, but it is only related to, and materially weaker as a formalization than, the authors' literal PAC/online theorem.

Second, the paper states in prose after Definition C.1 that exact-presentation EUC is equivalent to a stronger arbitrary-stream condition. The Lean source defines that stronger condition separately and contains declarations asserting a counterexample and the negation of the universal equivalence. The Lean source therefore **corrects rather than formalizes** that prose claim. Importantly, the Lean statement of Theorem C.2 itself assumes only the paper's Definition C.1 EUC, not the stronger condition, so the advertised finite-EUC-union theorem is preserved at statement level.

The Gold–Angluin identification results, Theorems 2.2 and 2.3, are not represented. The paper's computational/oracle remarks are also not formalized. Subject to those omissions and the prediction gap, the core generation results preserve their mathematical difficulty: no main closure, cover, EUC, or prompted theorem has a public hypothesis that directly contains its generation conclusion.

**Overall paper-level verdict: mixed but strongly positive for the generation content.** The formalization is faithful for the paper's main ordinary and prompted generation mathematics, materially incomplete for the identification portion, and materially different for the PAC/online-learning portion.

## 1. Definition-level correspondence and access model

### 1.1 Binary hypotheses are represented extensionally by supports

The paper works with binary functions `h : X → {0,1}` and writes `supp(h)`. Lean works with languages `L : Set α`. This is an exact extensional representation for every statement in which a binary hypothesis is used only through membership in its support. For prediction, membership in the set is also the binary label, so no information is lost at the combinatorial VC/Littlestone level.

The dependency-layer declarations are:

```lean
-- GenLimit.Generic
abbrev Language (α : Type*) := Set α
abbrev LanguageClass (α : Type*) := Set (Language α)
abbrev Stream (α : Type*) := ℕ → α
abbrev Generator (α : Type*) := ∀ t : ℕ, (Fin t → α) → α

def Presents (stream : Stream α) (L : Language α) : Prop :=
  Set.range stream = L

def StreamIn (stream : Stream α) (L : Language α) : Prop :=
  Set.range stream ⊆ L

def CorrectAt
    (G : Generator α) (L : Language α) (stream : Stream α) (t : ℕ) : Prop :=
  output G stream t ∈ L ∧ output G stream t ∉ sample stream t
```

`sample stream t` is the finite set of distinct values `stream s` with `s < t`; `output G stream t` applies `G` to the ordered prefix of length `t`. Lean time `t` therefore corresponds to the paper's one-based round after `t` examples have been seen.

There is one source-level access-model ambiguity. Section 2.1 on p. 4 says that `X^⋆` is the set of finite **subsets**, while Definition 2.1 on p. 5 says that a generator takes a finite **sequence**, and every game formula uses `G(x_{1:s})`. Lean chooses the sequential reading and lets the generator depend on order and repetitions. If the earlier “finite subsets” sentence were taken literally, Lean would give the generator strictly more runtime information. The supplied paper is internally inconsistent on this point, so the discrepancy cannot be resolved from the supplied evidence alone. All later theorem comparisons use the sequential game prose as the intended reading, while retaining this caveat.

**Support/presentation/correctness correspondence verdict:** Exact / formally equivalent  
**Support/presentation/correctness difficulty verdict:** Preserved  
**Generator-input representation correspondence verdict:** Indeterminate from the supplied evidence  
**Generator-input representation difficulty verdict:** Indeterminate

### 1.2 Ordinary generation definitions

The paper's Definition 2.2 on p. 5, Definition 2.3 on p. 6, and Definition 2.5 on p. 6 are represented by the following fully qualified declarations in `Definitions.lean`:

```lean
def GenLimit.LiRamanTewari.IsLimitGenerator
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream L →
      ∃ T, ∀ s, T ≤ s → GenLimit.Generic.CorrectAt gen L stream s

def GenLimit.LiRamanTewari.GeneratableInLimit
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α, IsLimitGenerator gen H

def GenLimit.LiRamanTewari.IsUniformGeneratorAt
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.StreamIn stream L →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s

def GenLimit.LiRamanTewari.UniformlyGeneratable
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α, ∃ d : ℕ,
    IsUniformGeneratorAt gen H d

def GenLimit.LiRamanTewari.IsNonuniformGenerator
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∃ d : ℕ,
    ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
        ∀ t, (GenLimit.Generic.sample stream t).card = d →
          ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s

def GenLimit.LiRamanTewari.NonuniformlyGeneratable
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α, IsNonuniformGenerator gen H
```

These signatures preserve the decisive dependencies:

- limit: `G` is class-wide; `T` may depend on the target and exact presentation;
- uniform: `G` and `d` are class-wide and precede target and stream;
- nonuniform: `G` is class-wide, while `d` may depend on the target but precedes the stream;
- uniform and nonuniform streams need only lie inside the target and need not enumerate it;
- limit streams must have range exactly equal to the target.

The Lean uniform predicate universally quantifies every trigger time `t` at which exactly `d` distinct examples have appeared. This is the reading used by the paper's negation on p. 10 and by its discussion of generating after observing `d` unique examples. Because sample cardinality is monotone and changes by at most one, it also gives the intended threshold behavior. There is no material quantifier change.

**Correspondence verdict:** Exact / formally equivalent  
**Difficulty verdict:** Preserved

### 1.3 Freshness, feedback, target access, and runtime information

Both sources require the output to avoid only the observed examples. Neither source requires outputs at different rounds to be distinct unless earlier outputs are later inserted into the exogenous stream. The generator's own outputs are not automatically fed back. The paper's autoregressive discussion on p. 7 explains that one *may choose* the next adversarial input to be the previous output after the threshold; this is not part of the game definition. Lean matches that distinction.

The generator receives no target index, target set, membership answer, loss, or correctness feedback. A generator witness may be chosen as a function of the class in the surrounding existence proof, but its runtime type contains only the finite history. The target subtree does not use `GenLimit.MembershipOracle` in any public Paper 02 theorem.

**Correspondence verdict:** Exact / formally equivalent  
**Difficulty verdict:** Preserved

### 1.4 UUS, version space, closure, and closure dimension

Paper Assumption 1 on p. 5 and Definition 3.1 on p. 10 are represented by:

```lean
def GenLimit.LiRamanTewari.UUS
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → L.Infinite

def GenLimit.LiRamanTewari.versionSpace
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    Set (GenLimit.Generic.Language α) :=
  {L | L ∈ H ∧ (↑S : Set α) ⊆ L}

def GenLimit.LiRamanTewari.commonCore
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    GenLimit.Generic.Language α :=
  {x | ∀ L, L ∈ versionSpace H S → x ∈ L}

def GenLimit.LiRamanTewari.IsClosureWitness
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) : Prop :=
  (versionSpace H S).Nonempty ∧ (commonCore H S).Finite

def GenLimit.LiRamanTewari.ClosureDimensionAtMost
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∀ S : Finset α, d < S.card → (versionSpace H S).Nonempty →
    (commonCore H S).Infinite

def GenLimit.LiRamanTewari.HasClosureDimension
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop :=
  ClosureDimensionAtMost H d ∧
    (d = 0 ∨ ∃ S : Finset α, S.card = d ∧ IsClosureWitness H S)

def GenLimit.LiRamanTewari.HasFiniteClosureDimension
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ d : ℕ, HasClosureDimension H d

def GenLimit.LiRamanTewari.HasInfiniteClosureDimension
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ d : ℕ, ∃ S : Finset α, d ≤ S.card ∧ IsClosureWitness H S
```

A `Finset` is exactly a finite set of distinct examples, so it captures the paper's distinct sequence after forgetting order. `HasClosureDimension H 0` uses the paper's special zero convention. `HasInfiniteClosureDimension` uses arbitrarily large witnesses; downward closure of witnesses makes this equivalent to exact-size witnesses. The main dimension predicates always require a nonempty version space, so the vacuous value of `commonCore` when the version space is empty does not create a false witness.

**Correspondence verdict:** Exact / formally equivalent  
**Difficulty verdict:** Preserved

### 1.5 Uniform generation sample complexity

Paper Definition 2.4 on p. 6 defines the least valid threshold for a fixed generator, or infinity. Lean uses `WithTop ℕ`:

```lean
noncomputable def GenLimit.LiRamanTewari.uniformGenerationSampleComplexity
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : WithTop ℕ :=
  if h : ∃ d : ℕ, IsUniformGeneratorAt gen H d then
    (Nat.find h : WithTop ℕ)
  else ⊤

noncomputable def GenLimit.LiRamanTewari.optimalUniformGenerationSampleComplexity
    (H : GenLimit.Generic.LanguageClass α) : WithTop ℕ :=
  if h : ∃ d : ℕ, ∃ gen : GenLimit.Generic.Generator α,
      IsUniformGeneratorAt gen H d then
    (Nat.find h : WithTop ℕ)
  else ⊤
```

The fixed-generator definition is exact. The class-optimal definition and its API are a precise formal extension of the paper's phrase “optimal uniform generation sample complexity.” The paper does not separately define this infimum/minimum object.

At the zero edge, Lean's natural numbers include `0`. The paper explicitly allows closure dimension `0` but does not unambiguously state whether generation thresholds are positive naturals. Since valid thresholds are upward closed, this convention does not change uniform or nonuniform *generatability*, but it can change whether a fixed generator's least numerical threshold is `0` or `1`.

**Correspondence verdict:** Faithful generalization  
**Difficulty verdict:** Strengthened / harder

### 1.6 Literal PAC and online definitions are absent

The paper's Definition 2.8 on p. 8 quantifies a sample-complexity function, a learner, `ε,δ`, every distribution and target, an iid sample, high-probability risk, and a future error expectation. Definition 2.10 on p. 8 quantifies an online algorithm and a sublinear bound on cumulative mistakes over every horizon and adversarial sequence.

Lean instead has the following direct aliases in `Prediction.lean`:

```lean
def GenLimit.LiRamanTewari.PACLearnableViaVC
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  HasFiniteVCDimension H

def GenLimit.LiRamanTewari.OnlineLearnableViaLittlestone
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  HasFiniteLittlestoneDimension H
```

No declaration states or proves a bridge from these predicates to a literal PAC or online-learning structure. Consequently, negating `PACLearnableViaVC` means only negating the finite-VC predicate, and negating `OnlineLearnableViaLittlestone` means only negating the finite-Littlestone predicate.

**Correspondence verdict:** Related but materially different  
**Difficulty verdict:** Collapsed / trivialized

The VC-shattering and Littlestone-tree definitions themselves are faithful combinatorial definitions of Definitions 2.9, 2.11, and 2.12 (pp. 8–9).

### 1.7 Prompted definitions and information access

Paper Assumption 2 and Definitions 5.1–5.4 on pp. 22–23 are represented by:

```lean
def GenLimit.LiRamanTewari.PUUS
    (H : MulticlassHypothesisClass α ι) : Prop :=
  ∀ h, h ∈ H → ∀ y, (promptSupport h y).Infinite

abbrev GenLimit.LiRamanTewari.PromptedGenerator (α ι : Type*) :=
  ∀ t : ℕ, (Fin t → PromptedObservation α ι) → α

def GenLimit.LiRamanTewari.promptedHistory
    (h : MulticlassHypothesis α ι)
    (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι)
    (t : ℕ) : Fin t → PromptedObservation α ι :=
  fun i ↦ (xs i, h (xs i), ys i)

def GenLimit.LiRamanTewari.PromptedCorrectAt
    (gen : PromptedGenerator α ι) (h : MulticlassHypothesis α ι)
    (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι)
    (s : ℕ) : Prop :=
  ∀ _hs : 0 < s,
    gen s (promptedHistory h xs ys s) ∈
      promptSupport h (ys (s - 1)) \
        (↑(GenLimit.Generic.sample xs s) : Set α)
```

The uniform, nonuniform, and limit predicates preserve the paper's quantifier order. The threshold counts distinct examples whose **true label** under `h` equals the distinguished prompt, not the number of times that prompt occurred in the prompt stream. The threshold in prompted nonuniform generation may depend on `h` but not on the prompt or either stream. Prompted limit generation assumes only that the full support for `yStar` is contained in the example stream's range; additional examples are permitted.

The displayed tuple in paper Definition 5.1 contains `h(x₁)` in its second tuple, an apparent typographical error. The game description and all later formulas use the current true label. Lean's `promptedHistory` uses `h (xs i)` at every index. This is a source correction, not an extra information channel beyond the paper's intended prompted game.

**Correspondence verdict:** Exact / formally equivalent  
**Difficulty verdict:** Preserved

### 1.8 Prompted closure dimension

The prompted version space, prompted common core, and dimension predicates exactly mirror paper Definition 5.5 on p. 24:

```lean
def GenLimit.LiRamanTewari.IsPromptedClosureWitness
    (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Prop :=
  (promptedVersionSpace H S y).Nonempty ∧
    (promptedCommonCore H S y).Finite

def GenLimit.LiRamanTewari.HasFinitePromptedClosureDimension
    (H : MulticlassHypothesisClass α ι) : Prop :=
  ∃ d : ℕ, HasPromptedClosureDimension H d

def GenLimit.LiRamanTewari.HasInfinitePromptedClosureDimension
    (H : MulticlassHypothesisClass α ι) : Prop :=
  ∀ d : ℕ, ∃ y : ι, ∃ S : Finset α,
    d ≤ S.card ∧ IsPromptedClosureWitness H S y
```

**Correspondence verdict:** Exact / formally equivalent  
**Difficulty verdict:** Preserved

### 1.9 EUC and the stronger arbitrary-stream predicate

Paper Definition C.1 on p. 33 is represented exactly by:

```lean
def GenLimit.LiRamanTewari.EventuallyUnboundedClosure
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream L →
      ∃ t, (commonCore H (GenLimit.Generic.sample stream t)).Infinite
```

The stronger property suggested as an equivalent reformulation in the prose immediately following Definition C.1 is separately encoded as:

```lean
def GenLimit.LiRamanTewari.StreamwiseEventuallyUnboundedClosure
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ stream : GenLimit.Generic.Stream α,
    ∃ t,
      ¬(versionSpace H (GenLimit.Generic.sample stream t)).Nonempty ∨
        (commonCore H (GenLimit.Generic.sample stream t)).Infinite
```

The former quantifies only exact presentations of class members; the latter quantifies every arbitrary stream. The latter is genuinely stronger and is not used as a hidden hypothesis in the public Theorem C.2 declaration.

**Correspondence verdict for Definition C.1:** Exact / formally equivalent  
**Difficulty verdict:** Preserved

**Correspondence verdict for the paper's claimed equivalence:** Related but materially different  
**Difficulty verdict:** Indeterminate

## 2. Bidirectional correspondence: every main author result

Exact Lean signatures for every declaration named in this table appear in Appendix A. The table is paper-to-Lean complete for all numbered mathematical results in the supplied PDF, together with the unnumbered hierarchy, quantitative, and EUC claims that the paper presents as substantive conclusions.

| Paper result and locus | Author-paper assertion | Lean representation | Correspondence verdict | Difficulty verdict | Audit finding |
|---|---|---|---|---|---|
| Hierarchy display, p. 7 | uniform ⇒ nonuniform ⇒ limit | `uniform_implies_nonuniform`; `nonuniform_implies_limit`; `uniform_implies_limit` | Exact / formally equivalent | Preserved | Same generator is reused; UUS is needed only to force an exact presentation to reach the target-dependent distinct-sample threshold. |
| Proposition 2.1(i), p. 7 | some UUS class is nonuniform but not uniform | `exists_countable_nonuniform_not_uniform_class` | Faithful specialization | Preserved | Lean supplies an explicit countably infinite tagged universe rather than quantifying an arbitrary countable `X`. |
| Proposition 2.1(ii), p. 7 | some UUS class is limit-generatable but not nonuniform | `exists_generatable_in_limit_not_nonuniformly_generatable` | Faithful specialization | Preserved | The final wrapper uses the paper's positive/nonpositive integer partition. |
| Theorem 2.2, p. 9 | a countable class is not identifiable in the limit | none | Not represented in Lean | Indeterminate | No identifier or identification-in-the-limit predicate occurs in target scope. |
| Theorem 2.3, pp. 9–10 | Angluin tell-tale characterization of identification | none | Not represented in Lean | Indeterminate | Neither implication is stated. |
| Theorem 2.4, p. 10 | every countable UUS class is limit-generatable | `countable_classes_are_nonuniformly_generatable` plus `nonuniform_implies_limit` | Faithful generalization | Strengthened / harder | Lean states the stronger nonuniform conclusion before deriving limit generation. There is no single public wrapper with exactly Theorem 2.4's signature. |
| Theorem 2.5, p. 10 | every finite UUS class is uniformly generatable | `finite_language_class_has_finite_closure_dimension` plus `uniform_generatability_iff_finite_closure_dimension` | Faithful specialization | Preserved | Composite representation; Lean explicitly requires a nonempty example type in the characterization. |
| Lemma 3.1, p. 11 | infinite closure dimension obstructs uniform generation | `closure_witness_defeats_uniform_threshold`; `closure_dimension_necessity` | Exact / formally equivalent | Preserved | Quantifier order is generator first, then arbitrary threshold witness; no generator conclusion is built into the closure witness. |
| Lemma 3.2, pp. 11–12 | finite closure dimension `d` yields a generator at `d+1` | `closureGenerator_isUniformGeneratorAt`; `closure_dimension_sufficiency` | Faithful specialization | Preserved | Adds explicit `Nonempty α` for fallback output; otherwise the threshold and access model match. |
| Theorem 3.3, p. 12 | uniform generation iff finite closure dimension | `uniform_generatability_iff_finite_closure_dimension` | Faithful specialization | Preserved | Same UUS/countability assumptions, plus explicit nonemptiness. |
| Quantitative claims after Lemmas 3.1–3.2 and Theorem 3.3, pp. 11–12 | `C(H) ≤ d_G`, closure generator at `C(H)+1`, optimal complexity `Θ(C(H))` | lower/upper declarations culminating in `optimal_uniform_generation_sample_complexity_bounds` | Faithful generalization | Strengthened / harder | Lean sharpens the asymptotic sentence to the exact interval `[d,d+1]` and handles the zero edge without claiming equality. |
| Lemma 3.4, pp. 12–13 | an uncountable UUS class is uniformly generatable | `exists_uncountable_uniformly_generatable_class` | Faithful specialization | Preserved | Uses the exact integer upward cone from the paper's proof. |
| Theorem 3.5, p. 13 | nonuniform generation iff a nondecreasing countable finite-closure cover exists | `nonuniform_generatability_iff_nondecreasing_finite_closure_cover` | Faithful specialization | Preserved | Indexing begins at `0` rather than `1`; this is a harmless reindexing. |
| Corollary 3.6, p. 13 | every countable UUS class is nonuniformly generatable | `countable_classes_are_nonuniformly_generatable` | Faithful specialization | Preserved | Includes finite and empty countable classes; the paper says countable without excluding them in the theorem statement. |
| Lemma 3.7, p. 13 | nonuniform generation yields a monotone cover by uniformly generatable subclasses | `nonuniform_characterization_necessity` | Exact / formally equivalent | Preserved | Threshold subclass construction has the same dependencies. |
| Lemma 3.8, pp. 14–15 | a monotone cover by uniform subclasses yields nonuniform generation | `nonuniform_characterization_sufficiency` | Faithful specialization | Preserved | Lean pads each component threshold by its index, repairing the paper's potentially undefined maximum without strengthening the theorem hypothesis. |
| Lemma 3.9, p. 15 | nonuniform generation is strictly weaker than uniform generation | `exists_countable_nonuniform_not_uniform_class` | Faithful specialization | Preserved | Tagged block construction is incidence-isomorphic to the paper's triangular blocks and even/odd tails. |
| Theorem 3.10, p. 16 | a finite cover by finite-closure classes is sufficient for limit generation | `finite_closure_dimension_cover_implies_generatable_in_limit` | Faithful generalization | Preserved | Lean also permits the degenerate empty finite cover, yielding the empty class. |
| Corollary 3.11, p. 17 | finite union of the displayed cone classes is limit-generatable | `finite_union_of_paper_cone_classes_generatable_in_limit` | Exact / formally equivalent | Preserved | The union-with-arbitrary-set class is explicitly shown to be the upward cone. |
| Lemma 3.12, pp. 17–18 | a UUS class is limit-generatable but not nonuniform | `exists_generatable_in_limit_not_nonuniformly_generatable` | Faithful specialization | Preserved | The public existential has exactly the advertised three properties. |
| Theorem 4.1(i), p. 19 | countable, uniformly generatable, not PAC learnable | `theorem_4_1_i_combinatorial_core` | Related but materially different | Weakened / easier | “Not PAC learnable” is only `¬HasFiniteVCDimension`; no PAC learner or probability model is present. |
| Theorem 4.1(ii), p. 19 | countable, online learnable, not uniform | `theorem_4_1_ii_combinatorial_core` | Related but materially different | Weakened / easier | “Online learnable” is only finite Littlestone dimension. The paper's stronger proof detail `L(H)=2` is not stated as an exact equality. |
| Theorem 4.1(iii), p. 19 | countable, online learnable and uniform | `theorem_4_1_iii_combinatorial_core` | Related but materially different | Weakened / easier | Same proxy gap. |
| Theorem 4.1(iv), p. 19 | PAC but neither online nor uniform | `theorem_4_1_iv_combinatorial_core` | Related but materially different | Weakened / easier | Finite VC and infinite Littlestone replace literal learning statements; witness lives on an explicit sum type. |
| Theorem 4.1(v), p. 19 | PAC and uniform but not online | `theorem_4_1_v_combinatorial_core` | Related but materially different | Weakened / easier | Same proxy gap; threshold witness is over `ℕ`. |
| Theorem 4.1(vi), p. 19 | neither PAC nor uniform | `theorem_4_1_vi_combinatorial_core` | Related but materially different | Weakened / easier | “Not PAC” is infinite VC by definition of the proxy. |
| Lemma 4.2, p. 20 | two closure-dimension-zero classes have a union not nonuniformly generatable | `exists_two_zero_closure_classes_union_not_nonuniform` | Faithful specialization | Preserved | Exact integer witness is supplied; no PAC/online proxy is involved. |
| Lemma 4.3, pp. 20–21 | a countable sequence of UUS, closure-zero classes has a union not limit-generatable | `exists_countable_sequence_zero_closure_union_not_limit` | Faithful specialization | Preserved | Tagged anchors/private tails replace prime ratios while preserving the existential incidence structure. |
| Theorem 5.1, p. 24 | prompted uniform generation iff finite prompted closure dimension | `prompted_uniform_generatability_iff_finite_prompted_closure_dimension` | Faithful specialization | Preserved | Same countability and PUUS assumptions, plus explicit nonempty example type. |
| Theorem 5.2, p. 24 | prompted nonuniform generation iff a monotone finite-PC cover exists | `prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover` | Faithful specialization | Preserved | Same threshold dependency: target-dependent but prompt- and stream-independent. |
| Corollary 5.3(i), pp. 24–25 | finite class and finite prompt space imply prompted uniform generation | `finite_prompt_classes_are_uniformly_generatable` | Faithful specialization | Preserved | Lean supplies the finite-PC intermediate as a separate declaration and avoids the paper proof's unjustified equality with arbitrary per-prompt thresholds. |
| Corollary 5.3(ii), pp. 24–25 | countably infinite class and finite prompt space imply prompted nonuniform generation | `countable_prompt_classes_are_nonuniformly_generatable` | Faithful generalization | Strengthened / harder | Lean covers every countable class, including finite and empty classes. |
| Corollary 5.3(iii), pp. 24–25 | countably infinite class and finite prompt space imply prompted limit generation | `countable_prompt_classes_are_generatable_in_limit` | Faithful generalization | Strengthened / harder | Same extension to all countable classes. |
| Lemma 5.4, pp. 25–26 | with countably infinite prompts, a finite PUUS class need not be prompted-uniform | `exists_finite_prompt_class_not_uniformly_generatable` | Faithful specialization | Preserved | Uses a tagged version of the paper's two-hypothesis finite-block/two-tail construction. |
| Corollary 5.5, p. 26 | such a finite class can also fail prompted nonuniform generation | `exists_finite_prompt_class_not_nonuniformly_generatable` | Faithful specialization | Preserved | Public conclusion matches exactly at the existential-property level. |
| Appendix C comparison claim, p. 34 | uniform generatability implies EUC | `uniform_implies_eventuallyUnboundedClosure` | Faithful specialization | Preserved | Obtained at the same paper-facing countability/UUS boundary, with explicit nonempty example type. |
| Appendix C strictness claim, p. 34 | EUC does not imply uniform generatability | none directly | Not represented in Lean | Indeterminate | The bundle has a candidate diagnostic class with EUC, but no public signature states that this class is not uniformly generatable or packages the strict separation. |
| Unnumbered EUC sufficiency, p. 33 | EUC of a class implies limit generation | `eventuallyUnboundedClosure_implies_generatable_in_limit` | Faithful generalization | Indeterminate | Lean drops the paper's ambient countability/UUS assumptions; outside countable spaces both EUC and limit clauses may become vacuous for unpresentable targets. |
| Lemma C.1, p. 33 | some UUS nonuniform class fails EUC | `exists_nonuniformly_generatable_not_eventuallyUnboundedClosure` | Faithful generalization | Preserved | Lean additionally states the witness class is countable, a fact also established in the paper's proof, but uses a different cofinite witness. |
| Theorem C.2, pp. 33–34 | a finite union of EUC classes is limit-generatable | `theorem_C2_finite_eventually_unbounded_closure_cover` | Faithful specialization | Preserved | Exact paper-facing hypotheses plus `Nonempty α`; no streamwise-EUC assumption appears. |
| Theorem C.4, pp. 34–35 | a nondecreasing countable EUC cover is sufficient for limit generation | `theorem_C4_eventually_unbounded_closure` | Faithful specialization | Preserved | Exact paper-facing wrapper; a second core declaration drops countability and UUS. |
| Prose equivalence after Definition C.1, p. 33 | EUC iff every arbitrary stream eventually has bottom or infinite closure | `eventuallyUnboundedClosure_not_equivalent_to_streamwise`; `printed_EUC_equivalence_is_false` | Related but materially different | Indeterminate | Lean asserts the opposite and supplies a class satisfying exact-presentation EUC but failing the streamwise property. This is a source correction, not a faithful rendering of the prose sentence. |

## 3. Detailed audit of the principal Lean theorem signatures

### 3.1 Ordinary hierarchy

```lean
theorem GenLimit.LiRamanTewari.uniform_implies_nonuniform
    {H : GenLimit.Generic.LanguageClass α} (h : UniformlyGeneratable H) :
    NonuniformlyGeneratable H

theorem GenLimit.LiRamanTewari.nonuniform_implies_limit
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (h : NonuniformlyGeneratable H) :
    GeneratableInLimit H

theorem GenLimit.LiRamanTewari.uniform_implies_limit
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (h : UniformlyGeneratable H) :
    GeneratableInLimit H
```

The first implication is pure quantifier weakening. The second uses UUS because an exact presentation of an infinite target must pass through every finite number of distinct examples. No computability or oracle condition is added.

**Verdict:** Exact / formally equivalent  
**Difficulty:** Preserved

### 3.2 Uniform characterization and quantitative bounds

The characterization is:

```lean
theorem GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) :
    UniformlyGeneratable H ↔ HasFiniteClosureDimension H
```

The necessity and sufficiency signatures are independently exposed:

```lean
theorem GenLimit.LiRamanTewari.closure_dimension_necessity [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hC : HasInfiniteClosureDimension H) :
    ¬ UniformlyGeneratable H

theorem GenLimit.LiRamanTewari.closure_dimension_sufficiency
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ}
    (hC : HasClosureDimension H d) :
    ∃ gen : GenLimit.Generic.Generator α,
      IsUniformGeneratorAt gen H (d + 1)
```

The lower bound is generator-wise and threshold-wise:

```lean
theorem GenLimit.LiRamanTewari.closure_dimension_le_uniform_threshold
    [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {d : ℕ} (hC : HasClosureDimension H d)
    {gen : GenLimit.Generic.Generator α} {e : ℕ}
    (hgen : IsUniformGeneratorAt gen H e) :
    d ≤ e
```

The class-optimal statement is:

```lean
theorem GenLimit.LiRamanTewari.optimal_uniform_generation_sample_complexity_bounds
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {d : ℕ} (hC : HasClosureDimension H d) :
    (d : WithTop ℕ) ≤ optimalUniformGenerationSampleComplexity H ∧
      optimalUniformGenerationSampleComplexity H ≤
        ((d + 1 : ℕ) : WithTop ℕ)
```

No helper premise mentions a generator that already succeeds. `HasClosureDimension` is entirely about version spaces and finite/infinite intersections. The construction is noncomputable but is not circular.

**Characterization correspondence verdict:** Faithful specialization  
**Characterization difficulty verdict:** Preserved  
**Quantitative-package correspondence verdict:** Faithful generalization  
**Quantitative-package difficulty verdict:** Strengthened / harder

### 3.3 Nonuniform characterization

```lean
def GenLimit.LiRamanTewari.IsNondecreasingCover
    (H : GenLimit.Generic.LanguageClass α)
    (classes : ℕ → GenLimit.Generic.LanguageClass α) : Prop :=
  Monotone classes ∧ H = ⋃ n, classes n

theorem GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) :
    NonuniformlyGeneratable H ↔
      ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
        IsNondecreasingCover H classes ∧
        ∀ n, HasFiniteClosureDimension (classes n)
```

The cover equality means both that every target lies in some component and that every component lies inside `H`. The monotonicity witness is independent of the eventual generator.

The sufficiency construction does not assume that the displayed component thresholds are monotone or that an unbounded threshold sequence has finite sublevel sets. Its statement-relevant helper definitions replace a threshold `d_n` by `max n d_n`; eligible indices are then restricted to `Finset.range (k+1)`. This is a genuine reduction repair. It supplies only a still-valid larger component threshold and does not encode nonuniform success of the union.

**Correspondence:** Faithful specialization  
**Difficulty:** Preserved

### 3.4 Finite-cover limit theorem and union separations

```lean
def GenLimit.LiRamanTewari.IsFiniteCover
    (H : GenLimit.Generic.LanguageClass α) {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α) : Prop :=
  H = ⋃ i, classes i

theorem GenLimit.LiRamanTewari.finite_closure_dimension_cover_implies_generatable_in_limit
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hcover : ∃ n : ℕ,
      ∃ classes : Fin n → GenLimit.Generic.LanguageClass α,
        IsFiniteCover H classes ∧
          ∀ i, HasFiniteClosureDimension (classes i)) :
    GeneratableInLimit H
```

The cover hypothesis does not mention any generator or correctness event. It is neither circular nor stronger than the desired conclusion. The theorem is one-way, exactly as in the paper.

The separation wrappers are:

```lean
theorem GenLimit.LiRamanTewari.exists_generatable_in_limit_not_nonuniformly_generatable :
    ∃ H : GenLimit.Generic.LanguageClass ℤ,
      UUS H ∧ GeneratableInLimit H ∧ ¬NonuniformlyGeneratable H

theorem GenLimit.LiRamanTewari.exists_two_zero_closure_classes_union_not_nonuniform :
    ∃ H₁ H₂ : GenLimit.Generic.LanguageClass ℤ,
      HasClosureDimension H₁ 0 ∧ HasClosureDimension H₂ 0 ∧
        ¬NonuniformlyGeneratable (H₁ ∪ H₂)

theorem GenLimit.LiRamanTewari.exists_countable_sequence_zero_closure_union_not_limit :
    ∃ classes : ℕ →
        GenLimit.Generic.LanguageClass CountableUnionUniverse,
      (∀ n, UUS (classes n)) ∧
      (∀ n, HasClosureDimension (classes n) 0) ∧
      ¬GeneratableInLimit (⋃ n, classes n)
```

These are genuine negative results. The class definitions are explicit and contain no generator-failure clause.

**Correspondence:** Faithful specialization  
**Difficulty:** Preserved

### 3.5 Theorem 4.1: the exact point of failure

The combined Lean theorem is:

```lean
theorem GenLimit.LiRamanTewari.theorem_4_1_combinatorial_core :
    (∃ H : GenLimit.Generic.LanguageClass ℤ,
      H.Countable ∧ UniformlyGeneratable H ∧
        ¬PACLearnableViaVC H) ∧
    (∃ H : GenLimit.Generic.LanguageClass BlockUniverse,
      H.Countable ∧ OnlineLearnableViaLittlestone H ∧
        ¬UniformlyGeneratable H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ℤ,
      H.Countable ∧ OnlineLearnableViaLittlestone H ∧
        UniformlyGeneratable H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ThresholdBlockUniverse,
      H.Countable ∧ PACLearnableViaVC H ∧
        ¬OnlineLearnableViaLittlestone H ∧
        ¬UniformlyGeneratable H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ PACLearnableViaVC H ∧
        UniformlyGeneratable H ∧
        ¬OnlineLearnableViaLittlestone H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ ¬PACLearnableViaVC H ∧
        ¬UniformlyGeneratable H)
```

The six witnesses are allowed to live on different explicit universes. The paper's displayed “Let `X` be countable” is itself too broad if read as every finite countable `X`, because its generation definitions require infinite supports; the Appendix immediately chooses infinite universes. Lean sensibly instantiates explicit countably infinite universes, but it does not state a transport theorem for every countably infinite `X`.

More importantly, the learning predicates are direct dimension aliases. The formal theorem establishes the same six regions **after replacing** PAC learnability by finite VC dimension and online learnability by finite Littlestone dimension. It does not establish the classical characterization theorems inside Lean or instantiate literal learners from them.

**Correspondence:** Related but materially different  
**Difficulty:** Weakened / easier

The construction-specific VC and Littlestone facts are still substantive. For example, the source declares infinite VC for the finite-augmentation and cofinite classes, finite Littlestone for the block and singleton-spike classes, and infinite Littlestone for the threshold constructions. Those facts preserve the combinatorial work of Appendix A; what is missing is the formal learning-theory bridge.

### 3.6 EUC theorems and the repaired C.2 path

```lean
theorem GenLimit.LiRamanTewari.eventuallyUnboundedClosure_implies_generatable_in_limit
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hEUC : EventuallyUnboundedClosure H) :
    GeneratableInLimit H

theorem GenLimit.LiRamanTewari.finite_euc_cover_implies_generatable_in_limit
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    {n : ℕ} (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (hcover : IsFiniteCover H classes)
    (hEUC : ∀ i, EventuallyUnboundedClosure (classes i)) :
    GeneratableInLimit H

theorem GenLimit.LiRamanTewari.theorem_C2_finite_eventually_unbounded_closure_cover
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H)
    (hcover : ∃ n : ℕ,
      ∃ classes : Fin n → GenLimit.Generic.LanguageClass α,
        IsFiniteCover H classes ∧
          ∀ i, EventuallyUnboundedClosure (classes i)) :
    GeneratableInLimit H
```

The core finite-cover theorem drops UUS; the paper-facing wrapper retains it. No `StreamwiseEventuallyUnboundedClosure` premise occurs. The statement-relevant C.2 helper definitions say only that a component has activated if some prefix has an infinite core, choose the earliest such prefix, freeze that core, compare finite enumeration progress, and output a fresh point. None contains the target conclusion or assumes that arbitrary streams satisfy EUC.

The source also declares:

```lean
theorem GenLimit.LiRamanTewari.eventuallyUnboundedClosure_not_equivalent_to_streamwise :
    EventuallyUnboundedClosure spineTailClass ∧
      ¬StreamwiseEventuallyUnboundedClosure spineTailClass

theorem GenLimit.LiRamanTewari.printed_EUC_equivalence_is_false :
    ¬(∀ (H : GenLimit.Generic.LanguageClass SpineTailUniverse),
      EventuallyUnboundedClosure H ↔
        StreamwiseEventuallyUnboundedClosure H)
```

Those signatures directly conflict with the paper's prose equivalence but not with Theorem C.2's stated hypothesis.

**Theorem C.2 correspondence:** Faithful specialization  
**Theorem C.2 difficulty:** Preserved

**Prose-equivalence correspondence:** Related but materially different  
**Prose-equivalence difficulty:** Indeterminate

The C.4 declarations are:

```lean
theorem GenLimit.LiRamanTewari.nondecreasing_euc_cover_implies_generatable_in_limit
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    {classes : ℕ → GenLimit.Generic.LanguageClass α}
    (hcover : IsNondecreasingCover H classes)
    (hEUC : ∀ n, EventuallyUnboundedClosure (classes n)) :
    GeneratableInLimit H

theorem GenLimit.LiRamanTewari.theorem_C4_eventually_unbounded_closure
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H)
    (hcover : ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
      IsNondecreasingCover H classes ∧
        ∀ n, EventuallyUnboundedClosure (classes n)) :
    GeneratableInLimit H
```

The first is a faithful generalization that drops countability and UUS; the second is the paper-facing specialization.

### 3.7 Prompted characterizations and finite/infinite prompt consequences

The main signatures are:

```lean
theorem GenLimit.LiRamanTewari.prompted_uniform_generatability_iff_finite_prompted_closure_dimension
    [Nonempty α] [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) :
    PromptedUniformlyGeneratable H ↔
      HasFinitePromptedClosureDimension H

theorem GenLimit.LiRamanTewari.prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover
    [Nonempty α] [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) :
    PromptedNonuniformlyGeneratable H ↔
      ∃ classes : ℕ → MulticlassHypothesisClass α ι,
        IsPromptedNondecreasingCover H classes ∧
        ∀ n, HasFinitePromptedClosureDimension (classes n)
```

The finite-prompt consequences are:

```lean
theorem GenLimit.LiRamanTewari.finite_prompt_classes_are_uniformly_generatable
    [Nonempty α] [Countable α] [Countable ι] [Finite ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H)
    (hFinite : H.Finite) :
    PromptedUniformlyGeneratable H

theorem GenLimit.LiRamanTewari.countable_prompt_classes_are_nonuniformly_generatable
    [Nonempty α] [Countable α] [Countable ι] [Finite ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H)
    (hCountable : H.Countable) :
    PromptedNonuniformlyGeneratable H

theorem GenLimit.LiRamanTewari.countable_prompt_classes_are_generatable_in_limit
    [Nonempty α] [Countable α] [Countable ι] [Finite ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H)
    (hCountable : H.Countable) :
    PromptedGeneratableInLimit H
```

The infinite-prompt separation wrappers are:

```lean
theorem GenLimit.LiRamanTewari.exists_finite_prompt_class_not_uniformly_generatable :
    ∃ H : MulticlassHypothesisClass
        PromptSeparationUniverse PositivePrompt,
      H.Finite ∧ PUUS H ∧ ¬PromptedUniformlyGeneratable H

theorem GenLimit.LiRamanTewari.exists_finite_prompt_class_not_nonuniformly_generatable :
    ∃ H : MulticlassHypothesisClass
        PromptSeparationUniverse PositivePrompt,
      H.Finite ∧ PUUS H ∧ ¬PromptedNonuniformlyGeneratable H
```

The prompt type is the positive naturals, consistent with the paper's indexing convention in the example. The construction is tagged rather than prime-power based, but the two hypotheses, finite blocks of unbounded size, and disjoint infinite prompt-specific tails have the same incidence content.

**Theorems 5.1, 5.2, Corollary 5.3(i), Lemma 5.4, and Corollary 5.5 correspondence verdict:** Faithful specialization  
**Their difficulty verdict:** Preserved  
**Corollary 5.3(ii)–(iii) correspondence verdict:** Faithful generalization  
**Their difficulty verdict:** Strengthened / harder

## 4. Quantifier, assumption, and access-model matrix

| Property | Fully expanded witness order | Input stream condition | Threshold/eventual dependence | Runtime information | Freshness |
|---|---|---|---|---|---|
| Limit generation | `∃G ∀L∈H ∀x [range(x)=L → ∃T(L,x) ∀s≥T ...]` | exact presentation | `T` depends on target and stream | ordered positive history only | excludes observed inputs only |
| Uniform generation | `∃G ∃d ∀L∈H ∀x [range(x)⊆L] ∀t [|S_t|=d → ∀s≥t ...]` | any target-contained stream | one class-wide `d`; every exact-size trigger | ordered history only | excludes observed inputs only |
| Nonuniform generation | `∃G ∀L∈H ∃d(L) ∀x [range(x)⊆L] ∀t [|S_t|=d(L) → ∀s≥t ...]` | any target-contained stream | target-dependent, stream-independent threshold | ordered history only | excludes observed inputs only |
| Prompted uniform | `∃G ∃d ∀h∈H ∀xs ∀ys ∀y* ∀t [|S_t(h,y*)|=d → ...]` | arbitrary example and prompt streams | class-wide and prompt-independent | each observed example, its true label, and current prompt | excludes every observed example, regardless of label |
| Prompted nonuniform | `∃G ∀h∈H ∃d(h) ∀xs ∀ys ∀y* ∀t [...]` | arbitrary streams | target-dependent, prompt- and stream-independent | labeled prompted history | excludes all observed examples |
| Prompted limit | `∃G ∀h∈H ∀xs ∀ys ∀y* [supp(h,y*)⊆range(xs) → ∃T ...]` | stream need only contain full `y*`-support; extras allowed | `T` may depend on target, both streams, and prompt | labeled prompted history | excludes all observed examples |
| `PACLearnableViaVC` | `∃d ∀xs:Fin(d+1)→α, ¬VCShatters H xs` | none | none | no learner or sample | not applicable |
| `OnlineLearnableViaLittlestone` | `∃d, ¬∃T depth d+1, LittlestoneShattered T H` | none | none | no prediction algorithm | not applicable |

### Assumption effects

| Assumption | Paper role | Lean role | Audit |
|---|---|---|---|
| `Countable X` | permits enumeration/ordering constructions | `[Countable α]` on most paper-facing theorems | faithful; some core EUC theorems valid without it |
| UUS | every target support is infinite | `∀L∈H, L.Infinite` | exact |
| PUUS | every prompt support of every hypothesis is infinite | exact universal infinitude | exact |
| `Nonempty α` | implicit because a generator must output even before a threshold | explicit typeclass on constructive existence theorems | source repair / faithful specialization |
| finite prompt space | needed for Corollary 5.3 | `[Finite ι]` plus `[Countable ι]` | exact, with empty finite prompt type also allowed |
| class countability | countable set of hypotheses/languages | `H.Countable` | exact; includes finite/empty classes |

## 5. Helper, bridge, link, encoding, and circularity audit

### 5.1 Genuine independent combinatorial conditions

`HasFiniteClosureDimension`, `HasInfiniteClosureDimension`, their prompted analogues, `EventuallyUnboundedClosure`, `IsFiniteCover`, and `IsNondecreasingCover` are independent predicates about sets, intersections, streams, and covers. None mentions `GeneratableInLimit`, `UniformlyGeneratable`, or `NonuniformlyGeneratable` in its body. They do not directly encode the desired conclusion.

The closure condition unfolds to:

\[
\exists d\;\Bigl[
  \forall S,\ |S|>d\land V_H(S)\neq\varnothing
      \Rightarrow \bigcap_{L\in V_H(S)}L\text{ is infinite}
\Bigr]
\]

together with either the zero convention or an exact-size finite-core witness. This is a genuine combinatorial restriction.

The nondecreasing cover condition unfolds to:

\[
(\forall m\le n,\ H_m\subseteq H_n)
\quad\land\quad H=\bigcup_n H_n.
\]

It contains no generator witness.

### 5.2 The only conclusion-encoding bridges: the prediction aliases

`PACLearnableViaVC H` is definitionally `HasFiniteVCDimension H`; `OnlineLearnableViaLittlestone H` is definitionally `HasFiniteLittlestoneDimension H`. These are not independent compatibility conditions linking dimensions to the paper's learner definitions. They replace the learning notions. The classical characterization theorems are therefore assumed by naming, not established as formal claims.

This is the only main area where an advertised concept is collapsed into a proxy that omits a substantial part of the paper's formal structure.

### 5.3 Nonuniform cover reduction repair

The paper's Lemma 3.8 writes a maximum over indices satisfying a sample-complexity inequality. An unbounded sequence of thresholds can still have an infinite sublevel set, so the displayed maximum need not exist. Lean's statement-relevant definitions use

```lean
paddedThreshold threshold n = max n (threshold n)
eligibleIndices threshold k =
  (Finset.range (k + 1)).filter
    (fun n ↦ paddedThreshold threshold n ≤ k)
```

and the prompted version uses the analogous `promptedPaddedThreshold`. The padding makes every eligible index at most `k`, while preserving validity because a generator working at `d_n` also works at any larger exact threshold. This is a genuine repair, not a stronger oracle and not a hypothesis containing the desired conclusion.

### 5.4 Theorem C.2 repair and the false streamwise reformulation

The paper's proof sketch of Theorem C.2 relies on the preceding false arbitrary-stream equivalence. Lean's public C.2 statement does not. The private activation/frozen-core machinery, when recursively unfolded, requires only:

1. a component has some prefix with infinite common core along the current finite history;
2. choose the earliest such prefix and freeze that core;
3. enumerate each infinite frozen core using countability;
4. compare how much of each enumeration has appeared in the exact target presentation;
5. output the first missing point from a maximal-progress core.

The component containing the target is guaranteed to activate by its own EUC assumption because the global stream is an exact presentation of that target. Components not containing the target need not activate at all; if they do, their first point outside the target bounds their progress. No arbitrary-stream EUC assumption is smuggled in.

### 5.5 Corollary 5.3 intermediate repair

The paper's proof of Corollary 5.3(i) chooses per-prompt uniform thresholds and then asserts an equality between `PC(H)` and their maximum. Arbitrary valid thresholds need not be minimal and need not equal closure dimensions. Lean does not state that equality. Instead it has the independent signature

```lean
theorem GenLimit.LiRamanTewari.finite_prompt_class_has_finite_prompted_closure_dimension
    [Finite ι]
    {H : MulticlassHypothesisClass α ι} (hH : H.Finite) :
    HasFinitePromptedClosureDimension H
```

This is the correct combinatorial intermediate needed for Corollary 5.3(i). It does not contain prompted uniform generatability in its hypothesis or conclusion.

### 5.6 Explicit example encodings

The tagged universes used for Lemmas 3.9, 4.3, 5.4, and parts of Theorem 4.1 are direct incidence structures: finite blocks, shared anchors, and disjoint infinite tails. Their definitions do not refer to generators, dimensions, or failure predicates. Separate declarations assert countability, UUS/PUUS, closure dimension, and generation failure. No example is made true by defining the class in terms of the theorem conclusion.

### 5.7 Computability and oracle access

All named generators are unrestricted set-theoretic functions, frequently `noncomputable` and using classical choice. No public main theorem requires:

- a membership oracle;
- an ERM oracle;
- a max-min oracle;
- decidable membership in the class or closure;
- computable enumeration of the class;
- polynomial time or any complexity bound.

This matches the information-theoretic theorem statements, but it does not formalize the implementation remarks on pp. 4–6, 12, 14–16.

## 6. Edge cases, vacuity, and source-level repairs

### 6.1 Empty example space and empty class

The paper says only that `X` is countable. If `X` and `H` are both empty, UUS holds vacuously and closure dimension is zero, but no generator `X*→X` exists because it must output on the empty history. Main Lean equivalences therefore add `[Nonempty α]`. This is a necessary source repair and a faithful specialization, not a mathematical weakening on nonempty spaces.

### 6.2 Finite countable universes in existential separation statements

Several displayed paper theorems begin “Let `X` be countable” and then assert a UUS example. Such a statement cannot hold for an arbitrary finite `X`. The paper proofs immediately set `X` to `ℤ`, `ℕ`, `ℚ_+`, or another infinite set. Lean states explicit countably infinite universes instead of the overbroad universal phrasing. A transport theorem to every countably infinite type is not present.

### 6.3 Threshold zero

Lean thresholds range over `ℕ`, including zero. At threshold `0`, the empty prefix triggers correctness from the beginning. The paper explicitly defines closure dimension zero but is not fully explicit about whether its threshold naturals begin at zero or one. Generatability properties are unaffected because thresholds are monotone upward; fixed numerical sample complexity at the zero edge is convention-sensitive.

### 6.4 Streams that never reach the threshold

Uniform and nonuniform obligations are implications from “the current distinct-sample cardinality equals `d`.” A stream with fewer than `d` distinct values forever imposes no post-threshold correctness requirement. This is deliberate and matches the paper's discussion of repeated examples.

### 6.5 Empty version spaces

`commonCore H S` is the whole universe when the version space is empty, by vacuous universal quantification. Every closure-witness and closure-dimension clause separately requires a nonempty version space. EUC along an exact presentation also has a nonempty version space because the target itself is consistent. The stronger streamwise predicate explicitly allows the bottom/empty-version-space branch.

### 6.6 Finite cover with zero components

Lean's `Fin n` permits `n=0`. Then exact cover equality forces `H=∅`, and on a nonempty example type the conclusion is vacuous. The paper's phrase “finite sequence `H_1,…,H_n`” likely assumes positive `n`. This is a harmless degenerate generalization.

### 6.7 Prompt-vacuous eventuality

In prompted uniform, nonuniform, and limit generation, correctness after a reference time is required only at later rounds whose current prompt equals `yStar`. If `yStar` never occurs again, that clause is vacuous. This is present in the paper's “for all `s ≥ t*` where `y_s=y*`” wording and in Lean.

### 6.8 Prompt support presentation

Prompted limit generation requires `supp(h,y*) ⊆ range(xs)`, not equality and not that those examples appeared on rounds whose prompt was `y*`. This is faithful because the generator observes the true label `h(x_s)` independently of the current prompt.

### 6.9 Presentation vacuity outside the paper's countable setting

The ordinary and prompted limit predicates are defined over arbitrary Lean types, but a stream `ℕ → α` can present only a countable range. For an uncountable target language, `Presents stream L` is impossible; for an uncountable prompted support, `PromptSupportPresented` can be impossible. Consequently, the countability-free EUC and limit-generation core theorems include extra cases in which both premise and conclusion are partly vacuous. This is why their domain extension is a faithful formal generalization but does not receive an unqualified “harder” assessment.

### 6.10 Output novelty is not output-to-output novelty

`CorrectAt` and `PromptedCorrectAt` exclude the observed sample only. Repeating the same generated output on multiple rounds can remain formally correct if that output never enters the input stream. Neither source states a stronger breadth or exhaustion requirement.

## 7. What the Lean source does not establish

1. **Gold–Angluin identification.** There is no formal `Identifier`, identification-in-the-limit predicate, impossibility theorem, or tell-tale characterization corresponding to Definitions 2.6–2.7 and Theorems 2.2–2.3 (pp. 7, 9–10).

2. **Literal PAC learnability.** No learning algorithm, sample complexity `m(ε,δ)`, probability space, iid sample, confidence event, expected risk, or VC-to-PAC bridge theorem is present. The formal predicate is finite VC dimension by definition.

3. **Literal online learnability.** No sequential prediction algorithm, revealed-label protocol, cumulative mistake count, sublinear regret function, or Littlestone-to-online bridge theorem is present. The formal predicate is finite Littlestone dimension by definition.

4. **The exact Appendix A claim `L(H)=2`.** The block example has a declaration sufficient to show no shattered tree of depth three, but no public theorem states both lower and upper bounds giving exact equality two.

5. **Computability or efficiency.** The ERM, max-min, closure-dimension, and membership-oracle implementation remarks are not formalized as assumptions or algorithms. The generators are semantic existence witnesses.

6. **A transport theorem for arbitrary countably infinite example spaces.** The existential examples use explicit universes. No theorem transports them along a type equivalence to every countably infinite `X`.

7. **The paper's streamwise EUC equivalence.** Lean states its negation rather than the claimed equivalence.

8. **The paper proof's equality `PC(H)=max_y d_y` for arbitrary chosen per-prompt thresholds.** Lean deliberately does not assert it; it states only the finite-PC consequence needed for Corollary 5.3.

9. **Prompted sample-complexity bounds.** There is no prompted analogue of `uniformGenerationSampleComplexity` or the ordinary `[PC,PC+1]` quantitative package.

10. **The claimed equivalence with the Kleinberg–Mullainathan prompted model and the binary prompted/unprompted comparison.** Section 5.1 and Remark 5.3 (p. 23) are not represented by transport, encoding, or restriction theorems.

11. **A public strict separation EUC `\not\Rightarrow` uniform generation.** The paper asserts the non-converse on p. 34; the bundle does not state it directly.

12. **A resolution of the paper's `X^⋆` inconsistency.** The paper calls `X^⋆` finite subsets on p. 4 but calls generator inputs finite sequences on p. 5. Lean implements sequences; no supplied source disambiguates the notation conclusively.

13. **Compilation or proof acceptance.** No compilation log or kernel output was supplied or produced in this audit.

## 8. Extra Lean results and faithful strengthenings

The main extras are mathematically meaningful rather than aliases of desired conclusions:

- a complete `WithTop ℕ` API for fixed-generator and class-optimal uniform sample complexity;
- the exact optimal interval `[C(H),C(H)+1]`;
- complementarity theorems between finite and infinite relational encodings of closure dimension and prompted closure dimension;
- generic versions of several existential examples on arbitrary disjoint infinite sets or tagged countable universes;
- a C.4 core theorem requiring only `Nonempty α`, not countability or UUS;
- an EUC-implies-limit theorem requiring only `Nonempty α`;
- explicit counterexamples showing exact-presentation EUC is not equivalent to arbitrary-stream EUC;
- prompted hierarchy implications and the finite-class finite-PC intermediate;
- countable prompted corollaries strengthened from “countably infinite” to all countable classes.

Every substantive public theorem declaration is classified individually in Appendix A.

## 9. Difficulty-preservation assessment

### Preserved

The mathematical difficulty is preserved for:

- closure-dimension necessity and sufficiency;
- uniform and nonuniform characterizations;
- finite closure-cover sufficiency for limit generation;
- all hierarchy separations and union counterexamples;
- prompted closure and prompted nonuniform characterizations;
- finite/infinite prompt-space separations;
- Theorems C.2 and C.4 at statement level.

These statements use independent combinatorial hypotheses and retain the paper's adversarial stream, threshold, and freshness quantifiers.

### Strengthened / harder

The formal statement is stronger where Lean:

- proves countable classes are nonuniformly generatable before obtaining Theorem 2.4;
- sharpens `Θ(C(H))` to the exact one-step interval;
- drops UUS from the finite-EUC core theorem;
- extends prompted countably-infinite corollaries to all countable classes;
- gives generic structural forms of paper-specific existential examples.

### Weakened / easier

Theorem 4.1 is weakened as a formal learning-theory result because PAC and online learning are replaced by dimension-finiteness aliases. The remaining dimension calculations can still be nontrivial, but the probabilistic/algorithmic bridge is absent.

### Collapsed / trivialized

At the definition/bridge level, `PACLearnableViaVC` and `OnlineLearnableViaLittlestone` collapse the two learning notions to their characterizing dimensions. No other main generation result is collapsed by a conclusion-encoding helper.

## 10. Compact verdict table

| Domain | Correspondence | Difficulty | Compact reason |
|---|---|---|---|
| Ordinary generation definitions and hierarchy | Exact / formally equivalent | Preserved | Quantifier order, exact presentations, target-contained streams, and freshness match. |
| Uniform closure characterization | Faithful specialization | Preserved | Explicit nonempty universe repair; same combinatorial equivalence. |
| Uniform quantitative sample complexity | Faithful generalization | Strengthened / harder | Exact `[C,C+1]` interval replaces an informal `Θ(C)` sentence. |
| Nonuniform characterization | Faithful specialization | Preserved | Same monotone cover; padded-threshold repair does not alter hypotheses. |
| Limit-generation finite-cover theorem | Faithful generalization | Preserved | Same theorem plus harmless empty-cover case. |
| Ordinary separations and union failures | Faithful specialization | Preserved | Explicit/isomorphic countably infinite witnesses. |
| Gold–Angluin identification | Not represented in Lean | Indeterminate | No identification interface. |
| Generation-versus-PAC/online landscape | Related but materially different | Weakened / easier | Dimension proxies replace literal learning models. |
| Prompted definitions and closure characterizations | Faithful specialization | Preserved | Same labeled-history access, prompt-specific support, and threshold dependencies. |
| Finite-prompt countable corollaries | Faithful generalization | Strengthened / harder | Covers all countable classes, not only countably infinite ones. |
| Infinite-prompt separations | Faithful specialization | Preserved | Tagged two-hypothesis witness has the same incidence structure. |
| EUC definition and EUC cover theorems | Faithful specialization | Preserved | Paper-facing statements match; some core declarations drop assumptions. |
| Paper's arbitrary-stream EUC equivalence | Related but materially different | Indeterminate | Lean explicitly refutes it and proves C.2 without it. |
| Computability/oracle remarks | Not represented in Lean | Indeterminate | All generators are unrestricted semantic functions. |

## 11. Overall paper-level verdict

**Overall verdict: partially faithful, with a faithful generation core and a material prediction gap.**

The Lean source accurately captures the central new mathematics of the paper: ordinary uniform and nonuniform generation, closure dimension, quantitative uniform thresholds, finite-cover sufficiency, strict hierarchy/union separations, prompted generation, prompted closure dimension, finite versus infinite prompt behavior, and EUC cover results. The main quantifier dependencies and adversarial access model are preserved. Several source-level issues are repaired transparently by theorem signatures or statement-relevant definitions rather than hidden assumptions.

It is not a complete formalization of the paper. The identification section is absent, and Theorem 4.1 is only a VC/Littlestone combinatorial core because PAC and online learnability are not formalized literally. For a consolidated 36-paper report, Paper 02 should therefore be recorded as **core-generation faithful; paper-wide mixed**.

## 12. Executive summary for the consolidated 36-paper report

Paper 02's Lean development is highly faithful to the paper's ordinary and prompted generation results. It preserves the exact presentation versus target-contained-stream distinction, threshold dependencies, no-feedback model, observed-input freshness, closure-dimension characterizations, nondecreasing-cover characterizations, finite-cover sufficiency, hierarchy separations, union counterexamples, finite/infinite prompt phenomena, and EUC theorems. It also gives a sharper `[C(H),C(H)+1]` uniform sample-complexity bound and repairs several source proof issues without assuming the conclusion.

The principal defect is Theorem 4.1: the Lean predicates called `PACLearnableViaVC` and `OnlineLearnableViaLittlestone` are direct abbreviations for finite VC and finite Littlestone dimension, so the formal theorem does not contain the paper's probabilistic PAC model or online prediction/mistake model. Gold–Angluin identification is also missing. The Lean source additionally and correctly records that the paper's prose equivalence between exact-presentation EUC and arbitrary-stream EUC is false, while retaining the stated C.2 theorem under EUC proper.


## Appendix A. Exhaustive Lean-to-paper ledger for all 128 substantive public theorem declarations

This appendix is the reverse, Lean-to-paper half of the required bidirectional audit. It includes every public theorem that the Stage 1 declaration census classified as substantive rather than purely structural/supporting. Definitions and private helpers are audited in the main text and Appendix B. Each entry gives the fully qualified declaration, exact or whitespace-normalized signature, source path and line, paper locus, one correspondence verdict, and one difficulty verdict.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean`

#### `GenLimit.LiRamanTewari.closure_witness_defeats_uniform_threshold`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:82`
- **Exact/normalized signature:** `theorem closure_witness_defeats_uniform_threshold [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {S : Finset α} {d : ℕ} (hSd : S.card = d) (hS : IsClosureWitness H S) (gen : GenLimit.Generic.Generator α) : ¬ IsUniformGeneratorAt gen H d`
- **Paper locus:** Lemma 3.1 and quantitative lower-bound discussion, p. 11
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact finite-witness obstruction at a fixed proposed threshold.

#### `GenLimit.LiRamanTewari.closure_dimension_necessity`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:178`
- **Exact/normalized signature:** `theorem closure_dimension_necessity [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hC : HasInfiniteClosureDimension H) : ¬ UniformlyGeneratable H`
- **Paper locus:** Lemma 3.1, p. 11
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Infinite closure dimension defeats uniform generation.

#### `GenLimit.LiRamanTewari.finite_closure_dimension_iff_not_infinite`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:190`
- **Exact/normalized signature:** `theorem finite_closure_dimension_iff_not_infinite {H : GenLimit.Generic.LanguageClass α} : HasFiniteClosureDimension H ↔ ¬ HasInfiniteClosureDimension H`
- **Paper locus:** No separately stated paper theorem; consequence of Definition 3.1
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Validates the two relational encodings as complements.

#### `GenLimit.LiRamanTewari.closureGenerator_isUniformGeneratorAt`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:281`
- **Exact/normalized signature:** `theorem closureGenerator_isUniformGeneratorAt [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : IsUniformGeneratorAt (closureGenerator H d hC.1) H (d + 1)`
- **Paper locus:** Lemma 3.2, pp. 11–12
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Named closure generator at threshold d+1; explicit nonempty output type.

#### `GenLimit.LiRamanTewari.closure_dimension_sufficiency`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:308`
- **Exact/normalized signature:** `theorem closure_dimension_sufficiency [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : ∃ gen : GenLimit.Generic.Generator α, IsUniformGeneratorAt gen H (d + 1)`
- **Paper locus:** Lemma 3.2, pp. 11–12
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Existential generator at threshold d+1.

#### `GenLimit.LiRamanTewari.finite_closure_dimension_implies_uniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:317`
- **Exact/normalized signature:** `theorem finite_closure_dimension_implies_uniform [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hfinite : HasFiniteClosureDimension H) : UniformlyGeneratable H`
- **Paper locus:** Theorem 3.3, p. 12, sufficiency direction
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Wrapper from finite dimension to uniform generation.

#### `GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:329`
- **Exact/normalized signature:** `theorem uniform_generatability_iff_finite_closure_dimension [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) : UniformlyGeneratable H ↔ HasFiniteClosureDimension H`
- **Paper locus:** Theorem 3.3, p. 12
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Main characterization with explicit Nonempty α.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean`

#### `GenLimit.LiRamanTewari.countableUnionCore_infinite`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:81`
- **Exact/normalized signature:** `theorem countableUnionCore_infinite (n : ℕ) : (countableUnionCore n).Infinite`
- **Paper locus:** Lemma 4.3, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged anchor/private-tail realization of the existential countable-union counterexample.

#### `GenLimit.LiRamanTewari.countableUnionClasses_uus`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:101`
- **Exact/normalized signature:** `theorem countableUnionClasses_uus (n : ℕ) : UUS (countableUnionClasses n)`
- **Paper locus:** Lemma 4.3, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged anchor/private-tail realization of the existential countable-union counterexample.

#### `GenLimit.LiRamanTewari.countableUnionClasses_closure_dimension_zero`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:106`
- **Exact/normalized signature:** `theorem countableUnionClasses_closure_dimension_zero (n : ℕ) : HasClosureDimension (countableUnionClasses n) 0`
- **Paper locus:** Lemma 4.3, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged anchor/private-tail realization of the existential countable-union counterexample.

#### `GenLimit.LiRamanTewari.countableUnionHardClass_not_generatable_in_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:578`
- **Exact/normalized signature:** `theorem countableUnionHardClass_not_generatable_in_limit : ¬GeneratableInLimit countableUnionHardClass`
- **Paper locus:** Lemma 4.3, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged anchor/private-tail realization of the existential countable-union counterexample.

#### `GenLimit.LiRamanTewari.exists_countable_sequence_zero_closure_union_not_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:607`
- **Exact/normalized signature:** `theorem exists_countable_sequence_zero_closure_union_not_limit : ∃ classes : ℕ → GenLimit.Generic.LanguageClass CountableUnionUniverse, (∀ n, UUS (classes n)) ∧ (∀ n, HasClosureDimension (classes n) 0) ∧ ¬GeneratableInLimit (⋃ n, classes n)`
- **Paper locus:** Lemma 4.3, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged anchor/private-tail realization of the existential countable-union counterexample.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean`

#### `GenLimit.LiRamanTewari.upwardCone_not_countable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:63`
- **Exact/normalized signature:** `theorem upwardCone_not_countable [Countable α] {P N : Set α} (hP : P.Infinite) (hDisjoint : Disjoint P N) : ¬(upwardCone N).Countable`
- **Paper locus:** Lemma 3.4 proof pattern, pp. 12–13
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Generic uncountability lemma for upward cones over an infinite disjoint complement.

#### `GenLimit.LiRamanTewari.exists_uncountable_uniformly_generatable_class`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:93`
- **Exact/normalized signature:** `theorem exists_uncountable_uniformly_generatable_class : ∃ H : GenLimit.Generic.LanguageClass ℤ, ¬H.Countable ∧ UUS H ∧ UniformlyGeneratable H`
- **Paper locus:** Lemma 3.4, pp. 12–13
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Exact integer upward-cone witness.

#### `GenLimit.LiRamanTewari.blockSeparationClass_countable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:141`
- **Exact/normalized signature:** `theorem blockSeparationClass_countable : blockSeparationClass.Countable`
- **Paper locus:** Lemma 3.9, p. 15; Proposition 2.1(i), p. 7
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged finite-block/two-tail witness in place of triangular arithmetic.

#### `GenLimit.LiRamanTewari.blockSeparationClass_uus`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:144`
- **Exact/normalized signature:** `theorem blockSeparationClass_uus : UUS blockSeparationClass`
- **Paper locus:** Lemma 3.9, p. 15; Proposition 2.1(i), p. 7
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged finite-block/two-tail witness in place of triangular arithmetic.

#### `GenLimit.LiRamanTewari.blockSeparationClass_infinite_closure_dimension`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:172`
- **Exact/normalized signature:** `theorem blockSeparationClass_infinite_closure_dimension : HasInfiniteClosureDimension blockSeparationClass`
- **Paper locus:** Lemma 3.9, p. 15; Proposition 2.1(i), p. 7
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged finite-block/two-tail witness in place of triangular arithmetic.

#### `GenLimit.LiRamanTewari.exists_countable_nonuniform_not_uniform_class`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:183`
- **Exact/normalized signature:** `theorem exists_countable_nonuniform_not_uniform_class : ∃ H : GenLimit.Generic.LanguageClass BlockUniverse, H.Countable ∧ UUS H ∧ NonuniformlyGeneratable H ∧ ¬UniformlyGeneratable H`
- **Paper locus:** Lemma 3.9, p. 15; Proposition 2.1(i), p. 7
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged finite-block/two-tail witness in place of triangular arithmetic.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean`

#### `GenLimit.LiRamanTewari.finite_closure_dimension_implies_eventuallyUnboundedClosure`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:44`
- **Exact/normalized signature:** `theorem finite_closure_dimension_implies_eventuallyUnboundedClosure {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hFinite : HasFiniteClosureDimension H) : EventuallyUnboundedClosure H`
- **Paper locus:** Appendix C discussion after Definition C.1, pp. 33–34
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Indeterminate
- **Audit note:** Finite closure dimension forces an infinite core along exact presentations.

#### `GenLimit.LiRamanTewari.uniform_implies_eventuallyUnboundedClosure`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:60`
- **Exact/normalized signature:** `theorem uniform_implies_eventuallyUnboundedClosure [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hUniform : UniformlyGeneratable H) : EventuallyUnboundedClosure H`
- **Paper locus:** Appendix C discussion, p. 34
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Uses Theorem 3.3; explicit nonempty/countable universe.

#### `GenLimit.LiRamanTewari.cofiniteLanguageClass_countable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:75`
- **Exact/normalized signature:** `theorem cofiniteLanguageClass_countable [Countable α] : (cofiniteLanguageClass α).Countable`
- **Paper locus:** Alternative witness supporting Lemma C.1, p. 33
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Properties of a cofinite-class witness not used in the paper.

#### `GenLimit.LiRamanTewari.cofiniteLanguageClass_uus`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:84`
- **Exact/normalized signature:** `theorem cofiniteLanguageClass_uus [Infinite α] : UUS (cofiniteLanguageClass α)`
- **Paper locus:** Alternative witness supporting Lemma C.1, p. 33
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Properties of a cofinite-class witness not used in the paper.

#### `GenLimit.LiRamanTewari.cofiniteLanguageClass_not_eventuallyUnboundedClosure`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:111`
- **Exact/normalized signature:** `theorem cofiniteLanguageClass_not_eventuallyUnboundedClosure : ¬EventuallyUnboundedClosure (cofiniteLanguageClass ℕ)`
- **Paper locus:** Alternative witness supporting Lemma C.1, p. 33
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Properties of a cofinite-class witness not used in the paper.

#### `GenLimit.LiRamanTewari.exists_nonuniformly_generatable_not_eventuallyUnboundedClosure`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:127`
- **Exact/normalized signature:** `theorem exists_nonuniformly_generatable_not_eventuallyUnboundedClosure : ∃ H : GenLimit.Generic.LanguageClass ℕ, H.Countable ∧ UUS H ∧ NonuniformlyGeneratable H ∧ ¬EventuallyUnboundedClosure H`
- **Paper locus:** Lemma C.1, p. 33
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Preserved
- **Audit note:** Adds countability explicitly and uses a different countable witness.

#### `GenLimit.LiRamanTewari.nondecreasing_euc_cover_implies_generatable_in_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:205`
- **Exact/normalized signature:** `theorem nondecreasing_euc_cover_implies_generatable_in_limit [Nonempty α] {H : GenLimit.Generic.LanguageClass α} {classes : ℕ → GenLimit.Generic.LanguageClass α} (hcover : IsNondecreasingCover H classes) (hEUC : ∀ n, EventuallyUnboundedClosure (classes n)) : GeneratableInLimit H`
- **Paper locus:** Theorem C.4, pp. 34–35
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Indeterminate
- **Audit note:** Drops the paper-facing countability and UUS assumptions.

#### `GenLimit.LiRamanTewari.theorem_C4_eventually_unbounded_closure`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:275`
- **Exact/normalized signature:** `theorem theorem_C4_eventually_unbounded_closure [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) (hcover : ∃ classes : ℕ → GenLimit.Generic.LanguageClass α, IsNondecreasingCover H classes ∧ ∀ n, EventuallyUnboundedClosure (classes n)) : GeneratableInLimit H`
- **Paper locus:** Theorem C.4, pp. 34–35
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Paper-facing wrapper plus explicit Nonempty α.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean`

#### `GenLimit.LiRamanTewari.eventuallyUnboundedClosure_implies_generatable_in_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:51`
- **Exact/normalized signature:** `theorem eventuallyUnboundedClosure_implies_generatable_in_limit [Nonempty α] {H : GenLimit.Generic.LanguageClass α} (hEUC : EventuallyUnboundedClosure H) : GeneratableInLimit H`
- **Paper locus:** Unnumbered assertion after Definition C.1, p. 33
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Indeterminate
- **Audit note:** Drops countability and UUS; retains EUC proper.

#### `GenLimit.LiRamanTewari.spineTailLanguage_infinite`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:100`
- **Exact/normalized signature:** `theorem spineTailLanguage_infinite (n : ℕ) : (spineTailLanguage n).Infinite`
- **Paper locus:** No paper claim; support for the EUC prose correction
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Construction facts for a counterexample to the printed equivalence.

#### `GenLimit.LiRamanTewari.spineTailClass_uus`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:113`
- **Exact/normalized signature:** `theorem spineTailClass_uus : UUS spineTailClass`
- **Paper locus:** No paper claim; support for the EUC prose correction
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Construction facts for a counterexample to the printed equivalence.

#### `GenLimit.LiRamanTewari.spineTailClass_eventuallyUnboundedClosure`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:127`
- **Exact/normalized signature:** `theorem spineTailClass_eventuallyUnboundedClosure : EventuallyUnboundedClosure spineTailClass`
- **Paper locus:** Printed EUC equivalence discussion after Definition C.1, p. 33
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Indeterminate
- **Audit note:** One half of a counterexample to the paper prose equivalence.

#### `GenLimit.LiRamanTewari.spineTailClass_not_streamwise_euc`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:212`
- **Exact/normalized signature:** `theorem spineTailClass_not_streamwise_euc : ¬StreamwiseEventuallyUnboundedClosure spineTailClass`
- **Paper locus:** Printed EUC equivalence discussion after Definition C.1, p. 33
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Indeterminate
- **Audit note:** Declares the opposite of the paper prose claim; source correction.

#### `GenLimit.LiRamanTewari.eventuallyUnboundedClosure_not_equivalent_to_streamwise`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:221`
- **Exact/normalized signature:** `theorem eventuallyUnboundedClosure_not_equivalent_to_streamwise : EventuallyUnboundedClosure spineTailClass ∧ ¬StreamwiseEventuallyUnboundedClosure spineTailClass`
- **Paper locus:** Printed EUC equivalence discussion after Definition C.1, p. 33
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Indeterminate
- **Audit note:** Declares the opposite of the paper prose claim; source correction.

#### `GenLimit.LiRamanTewari.printed_EUC_equivalence_is_false`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:229`
- **Exact/normalized signature:** `theorem printed_EUC_equivalence_is_false : ¬(∀ (H : GenLimit.Generic.LanguageClass SpineTailUniverse), EventuallyUnboundedClosure H ↔ StreamwiseEventuallyUnboundedClosure H)`
- **Paper locus:** Printed EUC equivalence discussion after Definition C.1, p. 33
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Indeterminate
- **Audit note:** Declares the opposite of the paper prose claim; source correction.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteConeCover.lean`

#### `GenLimit.LiRamanTewari.upwardCone_has_closure_dimension_zero`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteConeCover.lean:41`
- **Exact/normalized signature:** `theorem upwardCone_has_closure_dimension_zero {S : Set α} (hS : S.Infinite) : HasClosureDimension (upwardCone S) 0`
- **Paper locus:** Corollary 3.11, p. 17
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Type-generic strengthening of the paper cone example.

#### `GenLimit.LiRamanTewari.upwardCone_has_finite_closure_dimension`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteConeCover.lean:50`
- **Exact/normalized signature:** `theorem upwardCone_has_finite_closure_dimension {S : Set α} (hS : S.Infinite) : HasFiniteClosureDimension (upwardCone S)`
- **Paper locus:** Corollary 3.11, p. 17
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Type-generic strengthening of the paper cone example.

#### `GenLimit.LiRamanTewari.finite_union_of_infinite_upwardCones_generatable_in_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteConeCover.lean:67`
- **Exact/normalized signature:** `theorem finite_union_of_infinite_upwardCones_generatable_in_limit [Nonempty α] [Countable α] {n : ℕ} (bases : Fin n → Set α) (hInfinite : ∀ i, (bases i).Infinite) : GeneratableInLimit (⋃ i, upwardCone (bases i))`
- **Paper locus:** Corollary 3.11, p. 17
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Type-generic strengthening of the paper cone example.

#### `GenLimit.LiRamanTewari.finite_union_of_paper_cone_classes_generatable_in_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteConeCover.lean:82`
- **Exact/normalized signature:** `theorem finite_union_of_paper_cone_classes_generatable_in_limit {n : ℕ} (bases : Fin n → Set ℕ) (hInfinite : ∀ i, (bases i).Infinite) : GeneratableInLimit (⋃ i, {L : Set ℕ | ∃ A : Set ℕ, L = bases i ∪ A})`
- **Paper locus:** Corollary 3.11, p. 17
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact ℕ-valued displayed cone classes.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteEUCUnion.lean`

#### `GenLimit.LiRamanTewari.finite_euc_cover_implies_generatable_in_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteEUCUnion.lean:445`
- **Exact/normalized signature:** `theorem finite_euc_cover_implies_generatable_in_limit [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} {n : ℕ} (classes : Fin n → GenLimit.Generic.LanguageClass α) (hcover : IsFiniteCover H classes) (hEUC : ∀ i, EventuallyUnboundedClosure (classes i)) : GeneratableInLimit H`
- **Paper locus:** Theorem C.2, pp. 33–34
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Drops UUS while retaining nonempty/countable example type.

#### `GenLimit.LiRamanTewari.theorem_C2_finite_eventually_unbounded_closure_cover`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteEUCUnion.lean:637`
- **Exact/normalized signature:** `theorem theorem_C2_finite_eventually_unbounded_closure_cover [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) (hcover : ∃ n : ℕ, ∃ classes : Fin n → GenLimit.Generic.LanguageClass α, IsFiniteCover H classes ∧ ∀ i, EventuallyUnboundedClosure (classes i)) : GeneratableInLimit H`
- **Paper locus:** Theorem C.2, pp. 33–34
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Paper-facing signature plus explicit Nonempty α.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/GenerationInLimitCharacterization.lean`

#### `GenLimit.LiRamanTewari.finite_closure_dimension_cover_implies_generatable_in_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/GenerationInLimitCharacterization.lean:524`
- **Exact/normalized signature:** `theorem finite_closure_dimension_cover_implies_generatable_in_limit [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hcover : ∃ n : ℕ, ∃ classes : Fin n → GenLimit.Generic.LanguageClass α, IsFiniteCover H classes ∧ ∀ i, HasFiniteClosureDimension (classes i)) : GeneratableInLimit H`
- **Paper locus:** Theorem 3.10, p. 16
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Preserved
- **Audit note:** Allows the degenerate n=0 cover; otherwise literal finite-cover theorem.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Hierarchy.lean`

#### `GenLimit.LiRamanTewari.uniform_implies_nonuniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Hierarchy.lean:14`
- **Exact/normalized signature:** `theorem uniform_implies_nonuniform {H : GenLimit.Generic.LanguageClass α} (h : UniformlyGeneratable H) : NonuniformlyGeneratable H`
- **Paper locus:** Hierarchy display before Proposition 2.1, p. 7
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact implication chain; UUS appears on implications to limit generation.

#### `GenLimit.LiRamanTewari.nonuniform_implies_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Hierarchy.lean:22`
- **Exact/normalized signature:** `theorem nonuniform_implies_limit {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (h : NonuniformlyGeneratable H) : GeneratableInLimit H`
- **Paper locus:** Hierarchy display before Proposition 2.1, p. 7
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact implication chain; UUS appears on implications to limit generation.

#### `GenLimit.LiRamanTewari.uniform_implies_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Hierarchy.lean:36`
- **Exact/normalized signature:** `theorem uniform_implies_limit {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (h : UniformlyGeneratable H) : GeneratableInLimit H`
- **Paper locus:** Hierarchy display before Proposition 2.1, p. 7
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact implication chain; UUS appears on implications to limit generation.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean`

#### `GenLimit.LiRamanTewari.separation_class_uus`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:109`
- **Exact/normalized signature:** `theorem separation_class_uus {P N : Set α} (hP : P.Infinite) (hN : N.Infinite) : UUS (limitNonuniformSeparationClass P N)`
- **Paper locus:** Lemma 3.12, pp. 17–18
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** General disjoint-infinite-partition form of the paper integer witness.

#### `GenLimit.LiRamanTewari.separation_class_generatable_in_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:120`
- **Exact/normalized signature:** `theorem separation_class_generatable_in_limit {P N : Set α} (hP : P.Infinite) (hN : N.Infinite) (hDisjoint : Disjoint P N) : GeneratableInLimit (limitNonuniformSeparationClass P N)`
- **Paper locus:** Lemma 3.12, pp. 17–18
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** General disjoint-infinite-partition form of the paper integer witness.

#### `GenLimit.LiRamanTewari.separation_class_not_nonuniformly_generatable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:332`
- **Exact/normalized signature:** `theorem separation_class_not_nonuniformly_generatable {P N : Set α} (hP : P.Infinite) (_hN : N.Infinite) (hDisjoint : Disjoint P N) : ¬NonuniformlyGeneratable (limitNonuniformSeparationClass P N)`
- **Paper locus:** Lemma 3.12, pp. 17–18
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** General disjoint-infinite-partition form of the paper integer witness.

#### `GenLimit.LiRamanTewari.subsetConeClass_has_closure_dimension_zero`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:373`
- **Exact/normalized signature:** `theorem subsetConeClass_has_closure_dimension_zero {P N : Set α} (hN : N.Infinite) : HasClosureDimension (subsetConeClass P N) 0`
- **Paper locus:** Lemma 4.2, p. 20
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** General disjoint-infinite-partition form of the two-class union obstruction.

#### `GenLimit.LiRamanTewari.singleton_infinite_language_has_closure_dimension_zero`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:385`
- **Exact/normalized signature:** `theorem singleton_infinite_language_has_closure_dimension_zero {P : Set α} (hP : P.Infinite) : HasClosureDimension ({P} : GenLimit.Generic.LanguageClass α) 0`
- **Paper locus:** Lemma 4.2, p. 20
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** General disjoint-infinite-partition form of the two-class union obstruction.

#### `GenLimit.LiRamanTewari.two_zero_closure_classes_union_not_nonuniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:397`
- **Exact/normalized signature:** `theorem two_zero_closure_classes_union_not_nonuniform {P N : Set α} (hP : P.Infinite) (hN : N.Infinite) (hDisjoint : Disjoint P N) : HasClosureDimension (subsetConeClass P N) 0 ∧ HasClosureDimension ({P} : GenLimit.Generic.LanguageClass α) 0 ∧ ¬NonuniformlyGeneratable (subsetConeClass P N ∪ ({P} : Set (Set α)))`
- **Paper locus:** Lemma 4.2, p. 20
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** General disjoint-infinite-partition form of the two-class union obstruction.

#### `GenLimit.LiRamanTewari.exists_generatable_in_limit_not_nonuniformly_generatable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:452`
- **Exact/normalized signature:** `theorem exists_generatable_in_limit_not_nonuniformly_generatable : ∃ H : GenLimit.Generic.LanguageClass ℤ, UUS H ∧ GeneratableInLimit H ∧ ¬NonuniformlyGeneratable H`
- **Paper locus:** Lemma 3.12, pp. 17–18; Proposition 2.1(ii), p. 7
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Exact integer existential wrapper.

#### `GenLimit.LiRamanTewari.exists_two_zero_closure_classes_union_not_nonuniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:469`
- **Exact/normalized signature:** `theorem exists_two_zero_closure_classes_union_not_nonuniform : ∃ H₁ H₂ : GenLimit.Generic.LanguageClass ℤ, HasClosureDimension H₁ 0 ∧ HasClosureDimension H₂ 0 ∧ ¬NonuniformlyGeneratable (H₁ ∪ H₂)`
- **Paper locus:** Lemma 4.2, p. 20
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Exact integer existential wrapper.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/NonuniformCharacterization.lean`

#### `GenLimit.LiRamanTewari.nonuniform_characterization_necessity`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/NonuniformCharacterization.lean:36`
- **Exact/normalized signature:** `theorem nonuniform_characterization_necessity [Countable α] {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) (hNonuniform : NonuniformlyGeneratable H) : ∃ classes : ℕ → GenLimit.Generic.LanguageClass α, IsNondecreasingCover H classes ∧ ∀ n, UniformlyGeneratable (classes n)`
- **Paper locus:** Lemma 3.7, p. 13
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Target-threshold subclasses give a monotone uniform cover.

#### `GenLimit.LiRamanTewari.nonuniform_characterization_sufficiency`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/NonuniformCharacterization.lean:103`
- **Exact/normalized signature:** `theorem nonuniform_characterization_sufficiency [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H) {classes : ℕ → GenLimit.Generic.LanguageClass α} (hcover : IsNondecreasingCover H classes) (hUniform : ∀ n, UniformlyGeneratable (classes n)) : NonuniformlyGeneratable H`
- **Paper locus:** Lemma 3.8, pp. 14–15
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Padded-threshold construction repairs the maximum while preserving hypotheses.

#### `GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/NonuniformCharacterization.lean:167`
- **Exact/normalized signature:** `theorem nonuniform_generatability_iff_nondecreasing_finite_closure_cover [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) : NonuniformlyGeneratable H ↔ ∃ classes : ℕ → GenLimit.Generic.LanguageClass α, IsNondecreasingCover H classes ∧ ∀ n, HasFiniteClosureDimension (classes n)`
- **Paper locus:** Theorem 3.5, p. 13
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Main characterization with explicit Nonempty α.

#### `GenLimit.LiRamanTewari.finite_language_class_has_finite_closure_dimension`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/NonuniformCharacterization.lean:191`
- **Exact/normalized signature:** `theorem finite_language_class_has_finite_closure_dimension {H : GenLimit.Generic.LanguageClass α} (hH : H.Finite) : HasFiniteClosureDimension H`
- **Paper locus:** No separately stated paper theorem; intermediate behind Theorem 2.5/Corollary 3.6
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Pure combinatorial fact stronger in assumptions than needed by the paper proof.

#### `GenLimit.LiRamanTewari.countable_classes_are_nonuniformly_generatable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/NonuniformCharacterization.lean:220`
- **Exact/normalized signature:** `theorem countable_classes_are_nonuniformly_generatable [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) (hCountable : H.Countable) : NonuniformlyGeneratable H`
- **Paper locus:** Corollary 3.6, p. 13
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** All countable classes, including finite/empty, under UUS.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean`

#### `GenLimit.LiRamanTewari.finiteAugmentationClass_countable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:234`
- **Exact/normalized signature:** `theorem finiteAugmentationClass_countable : finiteAugmentationClass.Countable`
- **Paper locus:** Appendix A.1 / Theorem 4.1(i), pp. 29–30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact finite-augmentation construction properties.

#### `GenLimit.LiRamanTewari.finiteAugmentationClass_uus_and_uniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:246`
- **Exact/normalized signature:** `theorem finiteAugmentationClass_uus_and_uniform : UUS finiteAugmentationClass ∧ UniformlyGeneratable finiteAugmentationClass`
- **Paper locus:** Appendix A.1 / Theorem 4.1(i), pp. 29–30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact finite-augmentation construction properties.

#### `GenLimit.LiRamanTewari.finiteAugmentationClass_infiniteVC`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:270`
- **Exact/normalized signature:** `theorem finiteAugmentationClass_infiniteVC : HasInfiniteVCDimension finiteAugmentationClass`
- **Paper locus:** Appendix A.1 / Theorem 4.1(i), pp. 29–30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact finite-augmentation construction properties.

#### `GenLimit.LiRamanTewari.theorem_4_1_i_combinatorial_core`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:306`
- **Exact/normalized signature:** `theorem theorem_4_1_i_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass ℤ, H.Countable ∧ UniformlyGeneratable H ∧ ¬PACLearnableViaVC H`
- **Paper locus:** Theorem 4.1(i), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** PAC learnability is replaced by the finite-VC proxy.

#### `GenLimit.LiRamanTewari.blockSeparationClass_onlineViaLittlestone`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:366`
- **Exact/normalized signature:** `theorem blockSeparationClass_onlineViaLittlestone : OnlineLearnableViaLittlestone blockSeparationClass`
- **Paper locus:** Appendix A.2 / Theorem 4.1(ii), p. 30 and p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** Only finite Littlestone dimension is stated; no online learner.

#### `GenLimit.LiRamanTewari.blockSeparationClass_not_uniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:450`
- **Exact/normalized signature:** `theorem blockSeparationClass_not_uniform : ¬UniformlyGeneratable blockSeparationClass`
- **Paper locus:** Theorem 4.1(ii), p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Generation half of the typed block witness.

#### `GenLimit.LiRamanTewari.theorem_4_1_ii_combinatorial_core`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:457`
- **Exact/normalized signature:** `theorem theorem_4_1_ii_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass BlockUniverse, H.Countable ∧ OnlineLearnableViaLittlestone H ∧ ¬UniformlyGeneratable H`
- **Paper locus:** Theorem 4.1(ii), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** Online learnability is replaced by the finite-Littlestone proxy.

#### `GenLimit.LiRamanTewari.singletonSpikeClass_countable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:475`
- **Exact/normalized signature:** `theorem singletonSpikeClass_countable : singletonSpikeClass.Countable`
- **Paper locus:** Appendix A.3(iii) / Theorem 4.1(iii), p. 30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact singleton-spike construction properties.

#### `GenLimit.LiRamanTewari.singletonSpikeClass_uus_and_uniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:479`
- **Exact/normalized signature:** `theorem singletonSpikeClass_uus_and_uniform : UUS singletonSpikeClass ∧ UniformlyGeneratable singletonSpikeClass`
- **Paper locus:** Appendix A.3(iii) / Theorem 4.1(iii), p. 30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact singleton-spike construction properties.

#### `GenLimit.LiRamanTewari.singletonSpikeClass_onlineViaLittlestone`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:507`
- **Exact/normalized signature:** `theorem singletonSpikeClass_onlineViaLittlestone : OnlineLearnableViaLittlestone singletonSpikeClass`
- **Paper locus:** Theorem 4.1(iii), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** Finite Littlestone proxy in place of literal online learnability.

#### `GenLimit.LiRamanTewari.theorem_4_1_iii_combinatorial_core`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:530`
- **Exact/normalized signature:** `theorem theorem_4_1_iii_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass ℤ, H.Countable ∧ OnlineLearnableViaLittlestone H ∧ UniformlyGeneratable H`
- **Paper locus:** Theorem 4.1(iii), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** Proxy-based online region.

#### `GenLimit.LiRamanTewari.thresholdClass_countable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:550`
- **Exact/normalized signature:** `theorem thresholdClass_countable : thresholdClass.Countable`
- **Paper locus:** Appendix A.3(v) / Theorem 4.1(v), p. 30 and p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Threshold construction on ℕ rather than the paper ambient integer presentation.

#### `GenLimit.LiRamanTewari.thresholdLanguage_infinite`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:553`
- **Exact/normalized signature:** `theorem thresholdLanguage_infinite (a : ℕ) : (thresholdLanguage a).Infinite`
- **Paper locus:** Appendix A.3(v) / Theorem 4.1(v), p. 30 and p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Threshold construction on ℕ rather than the paper ambient integer presentation.

#### `GenLimit.LiRamanTewari.thresholdClass_uus`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:561`
- **Exact/normalized signature:** `theorem thresholdClass_uus : UUS thresholdClass`
- **Paper locus:** Appendix A.3(v) / Theorem 4.1(v), p. 30 and p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Threshold construction on ℕ rather than the paper ambient integer presentation.

#### `GenLimit.LiRamanTewari.thresholdClass_uniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:566`
- **Exact/normalized signature:** `theorem thresholdClass_uniform : UniformlyGeneratable thresholdClass`
- **Paper locus:** Appendix A.3(v) / Theorem 4.1(v), p. 30 and p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Threshold construction on ℕ rather than the paper ambient integer presentation.

#### `GenLimit.LiRamanTewari.thresholdClass_pacViaVC`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:604`
- **Exact/normalized signature:** `theorem thresholdClass_pacViaVC : PACLearnableViaVC thresholdClass`
- **Paper locus:** Theorem 4.1(v), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** PAC/online assertions are finite/infinite dimension proxies.

#### `GenLimit.LiRamanTewari.thresholdClass_infiniteLittlestone`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:677`
- **Exact/normalized signature:** `theorem thresholdClass_infiniteLittlestone : HasInfiniteLittlestoneDimension thresholdClass`
- **Paper locus:** Appendix A.3(v) / Theorem 4.1(v), p. 30 and p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Threshold construction on ℕ rather than the paper ambient integer presentation.

#### `GenLimit.LiRamanTewari.thresholdClass_not_onlineViaLittlestone`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:689`
- **Exact/normalized signature:** `theorem thresholdClass_not_onlineViaLittlestone : ¬OnlineLearnableViaLittlestone thresholdClass`
- **Paper locus:** Theorem 4.1(v), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** PAC/online assertions are finite/infinite dimension proxies.

#### `GenLimit.LiRamanTewari.theorem_4_1_v_combinatorial_core`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:696`
- **Exact/normalized signature:** `theorem theorem_4_1_v_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass ℕ, H.Countable ∧ PACLearnableViaVC H ∧ UniformlyGeneratable H ∧ ¬OnlineLearnableViaLittlestone H`
- **Paper locus:** Theorem 4.1(v), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** PAC/online assertions are finite/infinite dimension proxies.

#### `GenLimit.LiRamanTewari.thresholdBlockClass_countable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:738`
- **Exact/normalized signature:** `theorem thresholdBlockClass_countable : thresholdBlockClass.Countable`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30 and p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum witness preserves the combinatorial and generation properties.

#### `GenLimit.LiRamanTewari.thresholdBlockClass_uus`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:743`
- **Exact/normalized signature:** `theorem thresholdBlockClass_uus : UUS thresholdBlockClass`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30 and p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum witness preserves the combinatorial and generation properties.

#### `GenLimit.LiRamanTewari.thresholdBlockClass_infiniteClosure`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:831`
- **Exact/normalized signature:** `theorem thresholdBlockClass_infiniteClosure : HasInfiniteClosureDimension thresholdBlockClass`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30 and p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum witness preserves the combinatorial and generation properties.

#### `GenLimit.LiRamanTewari.thresholdBlockClass_not_uniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:857`
- **Exact/normalized signature:** `theorem thresholdBlockClass_not_uniform : ¬UniformlyGeneratable thresholdBlockClass`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30 and p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum witness preserves the combinatorial and generation properties.

#### `GenLimit.LiRamanTewari.thresholdBlockClass_pacViaVC`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1003`
- **Exact/normalized signature:** `theorem thresholdBlockClass_pacViaVC : PACLearnableViaVC thresholdBlockClass`
- **Paper locus:** Theorem 4.1(iv), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** PAC/online assertions are dimension proxies.

#### `GenLimit.LiRamanTewari.thresholdBlockClass_infiniteLittlestone`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1109`
- **Exact/normalized signature:** `theorem thresholdBlockClass_infiniteLittlestone : HasInfiniteLittlestoneDimension thresholdBlockClass`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30 and p. 19
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum witness preserves the combinatorial and generation properties.

#### `GenLimit.LiRamanTewari.thresholdBlockClass_not_online`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1120`
- **Exact/normalized signature:** `theorem thresholdBlockClass_not_online : ¬OnlineLearnableViaLittlestone thresholdBlockClass`
- **Paper locus:** Theorem 4.1(iv), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** PAC/online assertions are dimension proxies.

#### `GenLimit.LiRamanTewari.theorem_4_1_iv_combinatorial_core`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1127`
- **Exact/normalized signature:** `theorem theorem_4_1_iv_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass ThresholdBlockUniverse, H.Countable ∧ PACLearnableViaVC H ∧ ¬OnlineLearnableViaLittlestone H ∧ ¬UniformlyGeneratable H`
- **Paper locus:** Theorem 4.1(iv), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** PAC/online assertions are dimension proxies.

#### `GenLimit.LiRamanTewari.cofiniteClass_countable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1143`
- **Exact/normalized signature:** `theorem cofiniteClass_countable : cofiniteClass.Countable`
- **Paper locus:** Appendix A.3(vi) / Theorem 4.1(vi), p. 30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact cofinite construction and generation obstruction.

#### `GenLimit.LiRamanTewari.cofiniteClass_uus`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1153`
- **Exact/normalized signature:** `theorem cofiniteClass_uus : UUS cofiniteClass`
- **Paper locus:** Appendix A.3(vi) / Theorem 4.1(vi), p. 30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact cofinite construction and generation obstruction.

#### `GenLimit.LiRamanTewari.cofiniteClass_infiniteVC`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1159`
- **Exact/normalized signature:** `theorem cofiniteClass_infiniteVC : HasInfiniteVCDimension cofiniteClass`
- **Paper locus:** Appendix A.3(vi) / Theorem 4.1(vi), p. 30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact cofinite construction and generation obstruction.

#### `GenLimit.LiRamanTewari.commonCore_cofiniteClass_eq`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1191`
- **Exact/normalized signature:** `theorem commonCore_cofiniteClass_eq (S : Finset ℕ) : commonCore cofiniteClass S = (↑S : Set ℕ)`
- **Paper locus:** Appendix A.3(vi) / Theorem 4.1(vi), p. 30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact cofinite construction and generation obstruction.

#### `GenLimit.LiRamanTewari.cofiniteClass_infiniteClosure`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1208`
- **Exact/normalized signature:** `theorem cofiniteClass_infiniteClosure : HasInfiniteClosureDimension cofiniteClass`
- **Paper locus:** Appendix A.3(vi) / Theorem 4.1(vi), p. 30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact cofinite construction and generation obstruction.

#### `GenLimit.LiRamanTewari.cofiniteClass_not_uniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1219`
- **Exact/normalized signature:** `theorem cofiniteClass_not_uniform : ¬UniformlyGeneratable cofiniteClass`
- **Paper locus:** Appendix A.3(vi) / Theorem 4.1(vi), p. 30 and p. 19
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact cofinite construction and generation obstruction.

#### `GenLimit.LiRamanTewari.cofiniteClass_not_pacViaVC`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1224`
- **Exact/normalized signature:** `theorem cofiniteClass_not_pacViaVC : ¬PACLearnableViaVC cofiniteClass`
- **Paper locus:** Theorem 4.1(vi), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** Not-PAC is represented only as failure of finite VC dimension.

#### `GenLimit.LiRamanTewari.theorem_4_1_vi_combinatorial_core`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1230`
- **Exact/normalized signature:** `theorem theorem_4_1_vi_combinatorial_core : ∃ H : GenLimit.Generic.LanguageClass ℕ, H.Countable ∧ ¬PACLearnableViaVC H ∧ ¬UniformlyGeneratable H`
- **Paper locus:** Theorem 4.1(vi), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** Not-PAC is represented only as failure of finite VC dimension.

#### `GenLimit.LiRamanTewari.theorem_4_1_combinatorial_core`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1245`
- **Exact/normalized signature:** `theorem theorem_4_1_combinatorial_core : (∃ H : GenLimit.Generic.LanguageClass ℤ, H.Countable ∧ UniformlyGeneratable H ∧ ¬PACLearnableViaVC H) ∧ (∃ H : GenLimit.Generic.LanguageClass BlockUniverse, H.Countable ∧ OnlineLearnableViaLittlestone H ∧ ¬UniformlyGeneratable H) ∧ (∃ H : GenLimit.Generic.LanguageClass ℤ, H.Countable ∧ OnlineLearnableViaLittlestone H ∧ UniformlyGeneratable H) ∧ (∃ H : GenLimit.Generic.LanguageClass ThresholdBlockUniverse, H.Countable ∧ PACLearnableViaVC H ∧ ¬OnlineLearnableViaLittlestone H ∧ ¬UniformlyGeneratable H) ∧ (∃ H : GenLimit.Generic.LanguageClass ℕ, H.Countable ∧ PACLearnableViaVC H ∧ UniformlyGeneratable H ∧ ¬OnlineLearnableViaLittlestone H) ∧ (∃ H : GenLimit.Generic.LanguageClass ℕ, H.Countable ∧ ¬PACLearnableViaVC H ∧ ¬UniformlyGeneratable H)`
- **Paper locus:** Theorem 4.1(i)–(vi), p. 19
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Weakened / easier
- **Audit note:** Combined six-region dimension/generation package on explicit universes.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean`

#### `GenLimit.LiRamanTewari.finite_prompted_closure_dimension_iff_not_infinite`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:68`
- **Exact/normalized signature:** `theorem finite_prompted_closure_dimension_iff_not_infinite {H : MulticlassHypothesisClass α ι} : HasFinitePromptedClosureDimension H ↔ ¬ HasInfinitePromptedClosureDimension H`
- **Paper locus:** No separately stated paper theorem; consequence of Definition 5.5
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Complements the relational finite/infinite encodings.

#### `GenLimit.LiRamanTewari.prompted_closure_dimension_sufficiency`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:214`
- **Exact/normalized signature:** `theorem prompted_closure_dimension_sufficiency [Nonempty α] [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (_hPUUS : PUUS H) {d : ℕ} (hPC : HasPromptedClosureDimension H d) : ∃ gen : PromptedGenerator α ι, IsPromptedUniformGeneratorAt gen H (d + 1)`
- **Paper locus:** Theorem 5.1, p. 24; Appendix B.1, p. 31
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Prompted closure characterization with explicit Nonempty α.

#### `GenLimit.LiRamanTewari.finite_prompted_closure_dimension_implies_uniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:277`
- **Exact/normalized signature:** `theorem finite_prompted_closure_dimension_implies_uniform [Nonempty α] [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) (hfinite : HasFinitePromptedClosureDimension H) : PromptedUniformlyGeneratable H`
- **Paper locus:** Theorem 5.1, p. 24; Appendix B.1, p. 31
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Prompted closure characterization with explicit Nonempty α.

#### `GenLimit.LiRamanTewari.prompted_uniform_threshold_mono`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:338`
- **Exact/normalized signature:** `theorem prompted_uniform_threshold_mono {gen : PromptedGenerator α ι} {H : MulticlassHypothesisClass α ι} {d n : ℕ} (hdn : d ≤ n) (hgen : IsPromptedUniformGeneratorAt gen H d) : IsPromptedUniformGeneratorAt gen H n`
- **Paper locus:** No separately stated paper theorem; threshold consequence of Definition 5.2
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Prompted exact-threshold monotonicity.

#### `GenLimit.LiRamanTewari.prompted_closure_dimension_necessity`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:353`
- **Exact/normalized signature:** `theorem prompted_closure_dimension_necessity [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) (hPC : HasInfinitePromptedClosureDimension H) : ¬ PromptedUniformlyGeneratable H`
- **Paper locus:** Theorem 5.1, p. 24; Appendix B.1, p. 31
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Prompted closure characterization with explicit Nonempty α.

#### `GenLimit.LiRamanTewari.prompted_uniform_generatability_iff_finite_prompted_closure_dimension`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:486`
- **Exact/normalized signature:** `theorem prompted_uniform_generatability_iff_finite_prompted_closure_dimension [Nonempty α] [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) : PromptedUniformlyGeneratable H ↔ HasFinitePromptedClosureDimension H`
- **Paper locus:** Theorem 5.1, p. 24; Appendix B.1, p. 31
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Prompted closure characterization with explicit Nonempty α.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean`

#### `GenLimit.LiRamanTewari.promptSeparationClass_finite`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:81`
- **Exact/normalized signature:** `theorem promptSeparationClass_finite : promptSeparationClass.Finite`
- **Paper locus:** Lemma 5.4, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged two-hypothesis finite-block/two-tail witness.

#### `GenLimit.LiRamanTewari.promptSeparationClass_puus`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:85`
- **Exact/normalized signature:** `theorem promptSeparationClass_puus : PUUS promptSeparationClass`
- **Paper locus:** Lemma 5.4, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged two-hypothesis finite-block/two-tail witness.

#### `GenLimit.LiRamanTewari.promptSeparationClass_infinite_prompted_closure_dimension`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:161`
- **Exact/normalized signature:** `theorem promptSeparationClass_infinite_prompted_closure_dimension : HasInfinitePromptedClosureDimension promptSeparationClass`
- **Paper locus:** Lemma 5.4, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged two-hypothesis finite-block/two-tail witness.

#### `GenLimit.LiRamanTewari.exists_finite_prompt_class_not_uniformly_generatable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:180`
- **Exact/normalized signature:** `theorem exists_finite_prompt_class_not_uniformly_generatable : ∃ H : MulticlassHypothesisClass PromptSeparationUniverse PositivePrompt, H.Finite ∧ PUUS H ∧ ¬PromptedUniformlyGeneratable H`
- **Paper locus:** Lemma 5.4, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged two-hypothesis finite-block/two-tail witness.

#### `GenLimit.LiRamanTewari.promptSeparationClass_not_nonuniformly_generatable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:191`
- **Exact/normalized signature:** `theorem promptSeparationClass_not_nonuniformly_generatable : ¬PromptedNonuniformlyGeneratable promptSeparationClass`
- **Paper locus:** Corollary 5.5, p. 26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Same explicit finite class fails prompted nonuniform generation.

#### `GenLimit.LiRamanTewari.exists_finite_prompt_class_not_nonuniformly_generatable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:230`
- **Exact/normalized signature:** `theorem exists_finite_prompt_class_not_nonuniformly_generatable : ∃ H : MulticlassHypothesisClass PromptSeparationUniverse PositivePrompt, H.Finite ∧ PUUS H ∧ ¬PromptedNonuniformlyGeneratable H`
- **Paper locus:** Corollary 5.5, p. 26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Same explicit finite class fails prompted nonuniform generation.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean`

#### `GenLimit.LiRamanTewari.prompted_nonuniform_characterization_necessity`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:25`
- **Exact/normalized signature:** `theorem prompted_nonuniform_characterization_necessity [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (_hPUUS : PUUS H) (hNonuniform : PromptedNonuniformlyGeneratable H) : ∃ classes : ℕ → MulticlassHypothesisClass α ι, IsPromptedNondecreasingCover H classes ∧ ∀ n, PromptedUniformlyGeneratable (classes n)`
- **Paper locus:** Theorem 5.2 necessity, p. 24; Appendix B.2, p. 32
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Monotone cover by prompted-uniform subclasses.

#### `GenLimit.LiRamanTewari.prompted_nonuniform_characterization_sufficiency`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:99`
- **Exact/normalized signature:** `theorem prompted_nonuniform_characterization_sufficiency [Nonempty α] [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (_hPUUS : PUUS H) {classes : ℕ → MulticlassHypothesisClass α ι} (hcover : IsPromptedNondecreasingCover H classes) (hUniform : ∀ n, PromptedUniformlyGeneratable (classes n)) : PromptedNonuniformlyGeneratable H`
- **Paper locus:** Theorem 5.2 sufficiency, p. 24; Appendix B.2, pp. 32–33
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Padded-threshold reduction preserves the source hypothesis.

#### `GenLimit.LiRamanTewari.prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:183`
- **Exact/normalized signature:** `theorem prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover [Nonempty α] [Countable α] [Countable ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) : PromptedNonuniformlyGeneratable H ↔ ∃ classes : ℕ → MulticlassHypothesisClass α ι, IsPromptedNondecreasingCover H classes ∧ ∀ n, HasFinitePromptedClosureDimension (classes n)`
- **Paper locus:** Theorem 5.2, p. 24
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Main prompted nonuniform characterization.

#### `GenLimit.LiRamanTewari.prompted_uniform_implies_nonuniform`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:253`
- **Exact/normalized signature:** `theorem prompted_uniform_implies_nonuniform {H : MulticlassHypothesisClass α ι} : PromptedUniformlyGeneratable H → PromptedNonuniformlyGeneratable H`
- **Paper locus:** Definitions 5.2–5.4 and hierarchy discussion, pp. 22–23
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted hierarchy with PUUS on implications to limit generation.

#### `GenLimit.LiRamanTewari.prompted_nonuniform_implies_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:260`
- **Exact/normalized signature:** `theorem prompted_nonuniform_implies_limit {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) : PromptedNonuniformlyGeneratable H → PromptedGeneratableInLimit H`
- **Paper locus:** Definitions 5.2–5.4 and hierarchy discussion, pp. 22–23
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted hierarchy with PUUS on implications to limit generation.

#### `GenLimit.LiRamanTewari.prompted_uniform_implies_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:275`
- **Exact/normalized signature:** `theorem prompted_uniform_implies_limit {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) : PromptedUniformlyGeneratable H → PromptedGeneratableInLimit H`
- **Paper locus:** Definitions 5.2–5.4 and hierarchy discussion, pp. 22–23
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted hierarchy with PUUS on implications to limit generation.

#### `GenLimit.LiRamanTewari.finite_prompt_class_has_finite_prompted_closure_dimension`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:286`
- **Exact/normalized signature:** `theorem finite_prompt_class_has_finite_prompted_closure_dimension [Finite ι] {H : MulticlassHypothesisClass α ι} (hH : H.Finite) : HasFinitePromptedClosureDimension H`
- **Paper locus:** Combinatorial intermediate for Corollary 5.3(i), pp. 24–25
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Supplies a corrected finite-PC lemma without the source proof’s threshold equality.

#### `GenLimit.LiRamanTewari.finite_prompt_classes_are_uniformly_generatable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:322`
- **Exact/normalized signature:** `theorem finite_prompt_classes_are_uniformly_generatable [Nonempty α] [Countable α] [Countable ι] [Finite ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) (hFinite : H.Finite) : PromptedUniformlyGeneratable H`
- **Paper locus:** Corollary 5.3(i), pp. 24–25
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Finite class and finite prompt type.

#### `GenLimit.LiRamanTewari.countable_prompt_classes_are_nonuniformly_generatable`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:332`
- **Exact/normalized signature:** `theorem countable_prompt_classes_are_nonuniformly_generatable [Nonempty α] [Countable α] [Countable ι] [Finite ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) (hCountable : H.Countable) : PromptedNonuniformlyGeneratable H`
- **Paper locus:** Corollary 5.3(ii), pp. 24–25
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Extends countably infinite to all countable classes.

#### `GenLimit.LiRamanTewari.countable_prompt_classes_are_generatable_in_limit`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:376`
- **Exact/normalized signature:** `theorem countable_prompt_classes_are_generatable_in_limit [Nonempty α] [Countable α] [Countable ι] [Finite ι] {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) (hCountable : H.Countable) : PromptedGeneratableInLimit H`
- **Paper locus:** Corollary 5.3(iii), pp. 24–25
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Extends countably infinite to all countable classes.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean`

#### `GenLimit.LiRamanTewari.uniform_threshold_mono`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:29`
- **Exact/normalized signature:** `theorem uniform_threshold_mono {gen : GenLimit.Generic.Generator α} {H : GenLimit.Generic.LanguageClass α} {d n : ℕ} (hdn : d ≤ n) (hgen : IsUniformGeneratorAt gen H d) : IsUniformGeneratorAt gen H n`
- **Paper locus:** Consequence of Definitions 2.3–2.4, p. 6
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Exact-threshold monotonicity API.

#### `GenLimit.LiRamanTewari.uniformGenerationSampleComplexity_eq_top_iff`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:52`
- **Exact/normalized signature:** `theorem uniformGenerationSampleComplexity_eq_top_iff {gen : GenLimit.Generic.Generator α} {H : GenLimit.Generic.LanguageClass α} : uniformGenerationSampleComplexity gen H = ⊤ ↔ ¬ ∃ d : ℕ, IsUniformGeneratorAt gen H d`
- **Paper locus:** Definition 2.4, p. 6
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Formal least-threshold API not separately claimed in the paper.

#### `GenLimit.LiRamanTewari.uniformGenerationSampleComplexity_lt_top_iff`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:62`
- **Exact/normalized signature:** `theorem uniformGenerationSampleComplexity_lt_top_iff {gen : GenLimit.Generic.Generator α} {H : GenLimit.Generic.LanguageClass α} : uniformGenerationSampleComplexity gen H < ⊤ ↔ ∃ d : ℕ, IsUniformGeneratorAt gen H d`
- **Paper locus:** Definition 2.4, p. 6
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Formal least-threshold API not separately claimed in the paper.

#### `GenLimit.LiRamanTewari.uniformGenerationSampleComplexity_le_coe_iff`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:72`
- **Exact/normalized signature:** `theorem uniformGenerationSampleComplexity_le_coe_iff {gen : GenLimit.Generic.Generator α} {H : GenLimit.Generic.LanguageClass α} {d : ℕ} : uniformGenerationSampleComplexity gen H ≤ (d : WithTop ℕ) ↔ IsUniformGeneratorAt gen H d`
- **Paper locus:** Definition 2.4, p. 6
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Formal least-threshold API not separately claimed in the paper.

#### `GenLimit.LiRamanTewari.uniformGenerationSampleComplexity_eq_coe_iff`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:94`
- **Exact/normalized signature:** `theorem uniformGenerationSampleComplexity_eq_coe_iff {gen : GenLimit.Generic.Generator α} {H : GenLimit.Generic.LanguageClass α} {d : ℕ} : uniformGenerationSampleComplexity gen H = (d : WithTop ℕ) ↔ IsUniformGeneratorAt gen H d ∧ ∀ e : ℕ, e < d → ¬ IsUniformGeneratorAt gen H e`
- **Paper locus:** Definition 2.4, p. 6
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Formal least-threshold API not separately claimed in the paper.

#### `GenLimit.LiRamanTewari.uniformlyGeneratable_iff_exists_sampleComplexity_lt_top`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:122`
- **Exact/normalized signature:** `theorem uniformlyGeneratable_iff_exists_sampleComplexity_lt_top {H : GenLimit.Generic.LanguageClass α} : UniformlyGeneratable H ↔ ∃ gen : GenLimit.Generic.Generator α, uniformGenerationSampleComplexity gen H < ⊤`
- **Paper locus:** Definition 2.4, p. 6
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Formal least-threshold API not separately claimed in the paper.

#### `GenLimit.LiRamanTewari.optimalUniformGenerationSampleComplexity_eq_top_iff`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:150`
- **Exact/normalized signature:** `theorem optimalUniformGenerationSampleComplexity_eq_top_iff {H : GenLimit.Generic.LanguageClass α} : optimalUniformGenerationSampleComplexity H = ⊤ ↔ ¬ UniformlyGeneratable H`
- **Paper locus:** Unnumbered “optimal sample complexity” discussion after Theorem 3.3, p. 12
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Formal API for a newly explicit class-optimal value.

#### `GenLimit.LiRamanTewari.optimalUniformGenerationSampleComplexity_le_coe_iff`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:174`
- **Exact/normalized signature:** `theorem optimalUniformGenerationSampleComplexity_le_coe_iff {H : GenLimit.Generic.LanguageClass α} {d : ℕ} : optimalUniformGenerationSampleComplexity H ≤ (d : WithTop ℕ) ↔ ∃ gen : GenLimit.Generic.Generator α, IsUniformGeneratorAt gen H d`
- **Paper locus:** Unnumbered “optimal sample complexity” discussion after Theorem 3.3, p. 12
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Formal API for a newly explicit class-optimal value.

#### `GenLimit.LiRamanTewari.closure_dimension_le_uniform_threshold`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:203`
- **Exact/normalized signature:** `theorem closure_dimension_le_uniform_threshold [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) {gen : GenLimit.Generic.Generator α} {e : ℕ} (hgen : IsUniformGeneratorAt gen H e) : d ≤ e`
- **Paper locus:** Quantitative lower bound after Lemma 3.1, p. 11
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Every valid threshold is at least the closure dimension.

#### `GenLimit.LiRamanTewari.closure_dimension_le_uniformGenerationSampleComplexity`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:219`
- **Exact/normalized signature:** `theorem closure_dimension_le_uniformGenerationSampleComplexity [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) (gen : GenLimit.Generic.Generator α) : (d : WithTop ℕ) ≤ uniformGenerationSampleComplexity gen H`
- **Paper locus:** Quantitative lower bound after Lemma 3.1, p. 11
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Extended-natural fixed-generator formulation.

#### `GenLimit.LiRamanTewari.closureGenerator_uniformGenerationSampleComplexity_le`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:235`
- **Exact/normalized signature:** `theorem closureGenerator_uniformGenerationSampleComplexity_le [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : uniformGenerationSampleComplexity (closureGenerator H d hC.1) H ≤ ((d + 1 : ℕ) : WithTop ℕ)`
- **Paper locus:** Lemma 3.2 and quantitative discussion, pp. 11–12
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Closure generator has threshold at most d+1.

#### `GenLimit.LiRamanTewari.closure_dimension_le_optimalUniformGenerationSampleComplexity`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:246`
- **Exact/normalized signature:** `theorem closure_dimension_le_optimalUniformGenerationSampleComplexity [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : (d : WithTop ℕ) ≤ optimalUniformGenerationSampleComplexity H`
- **Paper locus:** Quantitative sentence after Theorem 3.3, p. 12
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Sharp optimal interval refines the paper’s Θ statement.

#### `GenLimit.LiRamanTewari.optimalUniformGenerationSampleComplexity_le_closureDimension_succ`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:264`
- **Exact/normalized signature:** `theorem optimalUniformGenerationSampleComplexity_le_closureDimension_succ [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : optimalUniformGenerationSampleComplexity H ≤ ((d + 1 : ℕ) : WithTop ℕ)`
- **Paper locus:** Quantitative sentence after Theorem 3.3, p. 12
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Sharp optimal interval refines the paper’s Θ statement.

#### `GenLimit.LiRamanTewari.optimal_uniform_generation_sample_complexity_bounds`

- **Source:** `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:281`
- **Exact/normalized signature:** `theorem optimal_uniform_generation_sample_complexity_bounds [Nonempty α] [Countable α] {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) {d : ℕ} (hC : HasClosureDimension H d) : (d : WithTop ℕ) ≤ optimalUniformGenerationSampleComplexity H ∧ optimalUniformGenerationSampleComplexity H ≤ ((d + 1 : ℕ) : WithTop ℕ)`
- **Paper locus:** Quantitative sentence after Theorem 3.3, p. 12
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Sharp optimal interval refines the paper’s Θ statement.

## Appendix B. Exhaustive ledger of all 106 substantive public definitions, abbreviations, and the one inductive type

These declarations are not independent theorems, but they determine the meanings of every theorem in Appendix A. Bodies are quoted exactly or with whitespace normalized. Each is classified against the paper because a helper definition can strengthen, weaken, circularize, or directly encode a result.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean`

#### `GenLimit.LiRamanTewari.IsClosureWitness`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:22`
- **Exact/normalized declaration:** `def IsClosureWitness (H : GenLimit.Generic.LanguageClass α) (S : Finset α) : Prop := (versionSpace H S).Nonempty ∧ (commonCore H S).Finite`
- **Paper locus:** Definition 3.1, p. 10
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Relational encoding of finite and infinite closure dimension, including the zero convention.

#### `GenLimit.LiRamanTewari.ClosureDimensionAtMost`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:30`
- **Exact/normalized declaration:** `def ClosureDimensionAtMost (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop := ∀ S : Finset α, d < S.card → (versionSpace H S).Nonempty → (commonCore H S).Infinite`
- **Paper locus:** Definition 3.1, p. 10
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Relational encoding of finite and infinite closure dimension, including the zero convention.

#### `GenLimit.LiRamanTewari.HasClosureDimension`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:39`
- **Exact/normalized declaration:** `def HasClosureDimension (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop := ClosureDimensionAtMost H d ∧ (d = 0 ∨ ∃ S : Finset α, S.card = d ∧ IsClosureWitness H S)`
- **Paper locus:** Definition 3.1, p. 10
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Relational encoding of finite and infinite closure dimension, including the zero convention.

#### `GenLimit.LiRamanTewari.HasFiniteClosureDimension`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:45`
- **Exact/normalized declaration:** `def HasFiniteClosureDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ d : ℕ, HasClosureDimension H d`
- **Paper locus:** Definition 3.1, p. 10
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Relational encoding of finite and infinite closure dimension, including the zero convention.

#### `GenLimit.LiRamanTewari.HasInfiniteClosureDimension`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:51`
- **Exact/normalized declaration:** `def HasInfiniteClosureDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ d : ℕ, ∃ S : Finset α, d ≤ S.card ∧ IsClosureWitness H S`
- **Paper locus:** Definition 3.1, p. 10
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Relational encoding of finite and infinite closure dimension, including the zero convention.

#### `GenLimit.LiRamanTewari.closureGenerator`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Closure.lean:251`
- **Exact/normalized declaration:** `noncomputable def closureGenerator [Nonempty α] (H : GenLimit.Generic.LanguageClass α) (d : ℕ) (hC : ClosureDimensionAtMost H d) : GenLimit.Generic.Generator α := by classical exact fun _ xs => let S := GenLimit.Generic.sequenceSample xs if hd : d < S.card then if hVS : (versionSpace H S).Nonempty then Classical.choose (core_diff_sample_infinite hC S hd hVS).nonempty else Classical.choice inferInstance else Classical.choice inferInstance`
- **Paper locus:** Lemma 3.2 construction, pp. 11–12
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Noncomputable closure-core generator; runtime input remains only the finite history.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean`

#### `GenLimit.LiRamanTewari.CountableUnionUniverse`

- **Kind / source:** `abbrev`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:29`
- **Exact/normalized declaration:** `abbrev CountableUnionUniverse := ℕ ⊕ (ℕ × ℕ)`
- **Paper locus:** Lemma 4.3 construction, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged incidence-isomorphic replacement for prime-ratio components.

#### `GenLimit.LiRamanTewari.countableUnionAnchor`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:31`
- **Exact/normalized declaration:** `def countableUnionAnchor (n : ℕ) : CountableUnionUniverse := Sum.inl n`
- **Paper locus:** Lemma 4.3 construction, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged incidence-isomorphic replacement for prime-ratio components.

#### `GenLimit.LiRamanTewari.countableUnionTail`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:34`
- **Exact/normalized declaration:** `def countableUnionTail (n : ℕ) : Set CountableUnionUniverse := {x | ∃ k, x = Sum.inr (n, k)}`
- **Paper locus:** Lemma 4.3 construction, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged incidence-isomorphic replacement for prime-ratio components.

#### `GenLimit.LiRamanTewari.countableUnionCore`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:39`
- **Exact/normalized declaration:** `def countableUnionCore : ℕ → Set CountableUnionUniverse | 0 => {x | ∃ n, x = countableUnionAnchor n} | n + 1 => {countableUnionAnchor n} ∪ countableUnionTail n`
- **Paper locus:** Lemma 4.3 construction, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged incidence-isomorphic replacement for prime-ratio components.

#### `GenLimit.LiRamanTewari.countableUnionClasses`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:43`
- **Exact/normalized declaration:** `def countableUnionClasses : ℕ → GenLimit.Generic.LanguageClass CountableUnionUniverse := fun n ↦ upwardCone (countableUnionCore n)`
- **Paper locus:** Lemma 4.3 construction, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged incidence-isomorphic replacement for prime-ratio components.

#### `GenLimit.LiRamanTewari.countableUnionHardClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/CountableUnionSeparation.lean:47`
- **Exact/normalized declaration:** `def countableUnionHardClass : GenLimit.Generic.LanguageClass CountableUnionUniverse := ⋃ n, countableUnionClasses n`
- **Paper locus:** Lemma 4.3 construction, pp. 20–21
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged incidence-isomorphic replacement for prime-ratio components.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean`

#### `GenLimit.LiRamanTewari.UUS`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:19`
- **Exact/normalized declaration:** `def UUS (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ L, L ∈ H → L.Infinite`
- **Paper locus:** Assumption 1 and closure notation, pp. 4–5 and Definition 3.1, p. 10
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact support infinitude, positive version space, common core, and bottom-aware closure.

#### `GenLimit.LiRamanTewari.versionSpace`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:23`
- **Exact/normalized declaration:** `def versionSpace (H : GenLimit.Generic.LanguageClass α) (S : Finset α) : Set (GenLimit.Generic.Language α) := {L | L ∈ H ∧ (↑S : Set α) ⊆ L}`
- **Paper locus:** Assumption 1 and closure notation, pp. 4–5 and Definition 3.1, p. 10
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact support infinitude, positive version space, common core, and bottom-aware closure.

#### `GenLimit.LiRamanTewari.commonCore`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:28`
- **Exact/normalized declaration:** `def commonCore (H : GenLimit.Generic.LanguageClass α) (S : Finset α) : GenLimit.Generic.Language α := {x | ∀ L, L ∈ versionSpace H S → x ∈ L}`
- **Paper locus:** Assumption 1 and closure notation, pp. 4–5 and Definition 3.1, p. 10
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact support infinitude, positive version space, common core, and bottom-aware closure.

#### `GenLimit.LiRamanTewari.closure`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:32`
- **Exact/normalized declaration:** `noncomputable def closure (H : GenLimit.Generic.LanguageClass α) (S : Finset α) : Option (GenLimit.Generic.Language α) := by classical exact if (versionSpace H S).Nonempty then some (commonCore H S) else none`
- **Paper locus:** Assumption 1 and closure notation, pp. 4–5 and Definition 3.1, p. 10
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact support infinitude, positive version space, common core, and bottom-aware closure.

#### `GenLimit.LiRamanTewari.IsLimitGenerator`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:98`
- **Exact/normalized declaration:** `def IsLimitGenerator (gen : GenLimit.Generic.Generator α) (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α, GenLimit.Generic.Presents stream L → ∃ T, ∀ s, T ≤ s → GenLimit.Generic.CorrectAt gen L stream s`
- **Paper locus:** Definition 2.2, p. 5
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact-presentation limit generation.

#### `GenLimit.LiRamanTewari.GeneratableInLimit`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:103`
- **Exact/normalized declaration:** `def GeneratableInLimit (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ gen : GenLimit.Generic.Generator α, IsLimitGenerator gen H`
- **Paper locus:** Definition 2.2, p. 5
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact-presentation limit generation.

#### `GenLimit.LiRamanTewari.IsUniformGeneratorAt`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:111`
- **Exact/normalized declaration:** `def IsUniformGeneratorAt (gen : GenLimit.Generic.Generator α) (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop := ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α, GenLimit.Generic.StreamIn stream L → ∀ t, (GenLimit.Generic.sample stream t).card = d → ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s`
- **Paper locus:** Definition 2.3, p. 6
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Class-wide threshold over target-contained streams.

#### `GenLimit.LiRamanTewari.UniformlyGeneratable`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:118`
- **Exact/normalized declaration:** `def UniformlyGeneratable (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ gen : GenLimit.Generic.Generator α, ∃ d : ℕ, IsUniformGeneratorAt gen H d`
- **Paper locus:** Definition 2.3, p. 6
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Class-wide threshold over target-contained streams.

#### `GenLimit.LiRamanTewari.IsNonuniformGenerator`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:123`
- **Exact/normalized declaration:** `def IsNonuniformGenerator (gen : GenLimit.Generic.Generator α) (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ L, L ∈ H → ∃ d : ℕ, ∀ stream : GenLimit.Generic.Stream α, GenLimit.Generic.StreamIn stream L → ∀ t, (GenLimit.Generic.sample stream t).card = d → ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s`
- **Paper locus:** Definition 2.5, pp. 6–7
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Target-dependent, stream-independent threshold.

#### `GenLimit.LiRamanTewari.NonuniformlyGeneratable`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:130`
- **Exact/normalized declaration:** `def NonuniformlyGeneratable (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ gen : GenLimit.Generic.Generator α, IsNonuniformGenerator gen H`
- **Paper locus:** Definition 2.5, pp. 6–7
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Target-dependent, stream-independent threshold.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean`

#### `GenLimit.LiRamanTewari.BlockUniverse`

- **Kind / source:** `abbrev`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:112`
- **Exact/normalized declaration:** `abbrev BlockUniverse := (ℕ × ℕ) ⊕ (Bool × ℕ)`
- **Paper locus:** Lemma 3.9 construction, p. 15
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged finite blocks and two disjoint infinite tails.

#### `GenLimit.LiRamanTewari.blockFinset`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:114`
- **Exact/normalized declaration:** `def blockFinset (d : ℕ) : Finset BlockUniverse := (Finset.range d).image (fun j ↦ Sum.inl (d, j))`
- **Paper locus:** Lemma 3.9 construction, p. 15
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged finite blocks and two disjoint infinite tails.

#### `GenLimit.LiRamanTewari.blockSet`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:117`
- **Exact/normalized declaration:** `def blockSet (d : ℕ) : Set BlockUniverse := ↑(blockFinset d)`
- **Paper locus:** Lemma 3.9 construction, p. 15
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged finite blocks and two disjoint infinite tails.

#### `GenLimit.LiRamanTewari.blockTail`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:119`
- **Exact/normalized declaration:** `def blockTail (b : Bool) : Set BlockUniverse := Set.range (fun n : ℕ ↦ Sum.inr (b, n))`
- **Paper locus:** Lemma 3.9 construction, p. 15
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged finite blocks and two disjoint infinite tails.

#### `GenLimit.LiRamanTewari.blockLanguage`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:122`
- **Exact/normalized declaration:** `def blockLanguage (b : Bool) (d : ℕ) : Set BlockUniverse := blockSet d ∪ blockTail b`
- **Paper locus:** Lemma 3.9 construction, p. 15
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged finite blocks and two disjoint infinite tails.

#### `GenLimit.LiRamanTewari.blockSeparationClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EarlierSectionThreeExamples.lean:125`
- **Exact/normalized declaration:** `def blockSeparationClass : GenLimit.Generic.LanguageClass BlockUniverse := Set.range (fun p : Bool × ℕ ↦ blockLanguage p.1 p.2)`
- **Paper locus:** Lemma 3.9 construction, p. 15
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged finite blocks and two disjoint infinite tails.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean`

#### `GenLimit.LiRamanTewari.EventuallyUnboundedClosure`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:22`
- **Exact/normalized declaration:** `def EventuallyUnboundedClosure (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α, GenLimit.Generic.Presents stream L → ∃ t, (commonCore H (GenLimit.Generic.sample stream t)).Infinite`
- **Paper locus:** Definition C.1, p. 33
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact presentations only.

#### `GenLimit.LiRamanTewari.cofiniteLanguageClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:72`
- **Exact/normalized declaration:** `def cofiniteLanguageClass (α : Type*) : GenLimit.Generic.LanguageClass α := {L | ∃ A : Set α, A.Finite ∧ L = Set.univ \ A}`
- **Paper locus:** Alternative Lean witness for Lemma C.1
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Cofinite class is not the prime-power class displayed in the paper.

#### `GenLimit.LiRamanTewari.eventuallyUnboundedCoverGenerator`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosure.lean:169`
- **Exact/normalized declaration:** `noncomputable def eventuallyUnboundedCoverGenerator [Nonempty α] (classes : ℕ → GenLimit.Generic.LanguageClass α) : GenLimit.Generic.Generator α := by classical exact fun t xs ↦ let S := GenLimit.Generic.sequenceSample xs let active := eucActiveIndices classes S t if h : active.Nonempty then let selected := active.max' h freshFromCore (commonCore (classes selected) S) ((mem_eucActiveIndices_iff.mp (active.max'_mem h)).2.2) S else Classical.choice inferInstance`
- **Paper locus:** Algorithm 1 / Theorem C.4, pp. 34–35
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Indeterminate
- **Audit note:** Core generator works without paper-facing countability/UUS assumptions.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean`

#### `GenLimit.LiRamanTewari.StreamwiseEventuallyUnboundedClosure`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:16`
- **Exact/normalized declaration:** `def StreamwiseEventuallyUnboundedClosure (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ stream : GenLimit.Generic.Stream α, ∃ t, ¬(versionSpace H (GenLimit.Generic.sample stream t)).Nonempty ∨ (commonCore H (GenLimit.Generic.sample stream t)).Infinite`
- **Paper locus:** Prose equivalence following Definition C.1, p. 33
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Indeterminate
- **Audit note:** Faithful encoding of the stronger arbitrary-stream property, which Lean later refutes as equivalent to EUC.

#### `GenLimit.LiRamanTewari.SpineTailUniverse`

- **Kind / source:** `abbrev`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:89`
- **Exact/normalized declaration:** `abbrev SpineTailUniverse := ℕ ⊕ (ℕ × ℕ)`
- **Paper locus:** No paper construction; counterexample to the printed EUC equivalence
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Explicit diagnostic witness.

#### `GenLimit.LiRamanTewari.spineTailLanguage`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:92`
- **Exact/normalized declaration:** `def spineTailLanguage (n : ℕ) : GenLimit.Generic.Language SpineTailUniverse := {x | match x with | Sum.inl i => i < n | Sum.inr p => p.1 = n}`
- **Paper locus:** No paper construction; counterexample to the printed EUC equivalence
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Explicit diagnostic witness.

#### `GenLimit.LiRamanTewari.spineTailClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:97`
- **Exact/normalized declaration:** `def spineTailClass : GenLimit.Generic.LanguageClass SpineTailUniverse := Set.range spineTailLanguage`
- **Paper locus:** No paper construction; counterexample to the printed EUC equivalence
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Explicit diagnostic witness.

#### `GenLimit.LiRamanTewari.spineStream`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/EventuallyUnboundedClosureDiagnostics.lean:163`
- **Exact/normalized declaration:** `def spineStream : GenLimit.Generic.Stream SpineTailUniverse := fun n ↦ Sum.inl n`
- **Paper locus:** No paper construction; counterexample to the printed EUC equivalence
- **Correspondence verdict:** Extra Lean result not claimed by the paper
- **Difficulty verdict:** Indeterminate
- **Audit note:** Explicit diagnostic witness.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteConeCover.lean`

#### `GenLimit.LiRamanTewari.upwardCone`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteConeCover.lean:22`
- **Exact/normalized declaration:** `def upwardCone (S : Set α) : GenLimit.Generic.LanguageClass α := {L | S ⊆ L}`
- **Paper locus:** Corollary 3.11 displayed class, p. 17
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Generic form of all sets containing a fixed base.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteEUCUnion.lean`

#### `GenLimit.LiRamanTewari.finiteEUCUnionGenerator`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/FiniteEUCUnion.lean:254`
- **Exact/normalized declaration:** `noncomputable def finiteEUCUnionGenerator [Nonempty α] [Countable α] {n : ℕ} (classes : Fin n → GenLimit.Generic.LanguageClass α) : GenLimit.Generic.Generator α := by classical exact fun _ xs ↦ let current := GenLimit.Generic.sequenceSample xs match c2WinningIndex classes xs with | none => Classical.choice inferInstance | some i => c2ComponentOutput (c2FrozenCore (classes i) xs) current`
- **Paper locus:** Theorem C.2, pp. 33–34
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Repaired finite-EUC-union generator using activation and frozen cores.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/GenerationInLimitCharacterization.lean`

#### `GenLimit.LiRamanTewari.IsFiniteCover`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/GenerationInLimitCharacterization.lean:24`
- **Exact/normalized declaration:** `def IsFiniteCover (H : GenLimit.Generic.LanguageClass α) {n : ℕ} (classes : Fin n → GenLimit.Generic.LanguageClass α) : Prop := H = ⋃ i, classes i`
- **Paper locus:** Theorem 3.10 and Theorem C.2 hypotheses, pp. 16, 33
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact union equality for a finite indexed family.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean`

#### `GenLimit.LiRamanTewari.subsetConeClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:26`
- **Exact/normalized declaration:** `def subsetConeClass (P N : Set α) : GenLimit.Generic.LanguageClass α := {L | ∃ A : Set α, A ⊆ P ∧ L = N ∪ A}`
- **Paper locus:** Lemma 3.12 construction, pp. 17–18
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Generic disjoint-infinite-partition form of the paper integer example.

#### `GenLimit.LiRamanTewari.limitNonuniformSeparationClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:31`
- **Exact/normalized declaration:** `def limitNonuniformSeparationClass (P N : Set α) : GenLimit.Generic.LanguageClass α := subsetConeClass P N ∪ ({P} : Set (Set α))`
- **Paper locus:** Lemma 3.12 construction, pp. 17–18
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Generic disjoint-infinite-partition form of the paper integer example.

#### `GenLimit.LiRamanTewari.partitionLimitGenerator`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:64`
- **Exact/normalized declaration:** `noncomputable def partitionLimitGenerator (P N : Set α) (hP : P.Infinite) (hN : N.Infinite) : GenLimit.Generic.Generator α := by classical exact fun _ xs ↦ let seen := GenLimit.Generic.sequenceSample xs if h : (↑seen : Set α) ⊆ P then freshFrom P hP seen else freshFrom N hN seen`
- **Paper locus:** Lemma 3.12 construction, pp. 17–18
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Generic disjoint-infinite-partition form of the paper integer example.

#### `GenLimit.LiRamanTewari.paperPositiveIntegers`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:411`
- **Exact/normalized declaration:** `def paperPositiveIntegers : Set ℤ := {z | 0 < z}`
- **Paper locus:** Lemma 3.12 and Lemma 4.2 constructions, pp. 17–20
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact positive/nonpositive integer partition.

#### `GenLimit.LiRamanTewari.paperNonpositiveIntegers`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/LimitVsNonuniformSeparation.lean:414`
- **Exact/normalized declaration:** `def paperNonpositiveIntegers : Set ℤ := {z | z ≤ 0}`
- **Paper locus:** Lemma 3.12 and Lemma 4.2 constructions, pp. 17–20
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact positive/nonpositive integer partition.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/NonuniformCharacterization.lean`

#### `GenLimit.LiRamanTewari.IsNondecreasingCover`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/NonuniformCharacterization.lean:30`
- **Exact/normalized declaration:** `def IsNondecreasingCover (H : GenLimit.Generic.LanguageClass α) (classes : ℕ → GenLimit.Generic.LanguageClass α) : Prop := Monotone classes ∧ H = ⋃ n, classes n`
- **Paper locus:** Theorem 3.5 and Theorem C.4 hypotheses, pp. 13, 34
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Monotone subclasses with exact union equality.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean`

#### `GenLimit.LiRamanTewari.VCShatters`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:34`
- **Exact/normalized declaration:** `def VCShatters (H : GenLimit.Generic.LanguageClass α) {d : ℕ} (xs : Fin d → α) : Prop := ∀ labels : Fin d → Bool, ∃ L, L ∈ H ∧ ∀ i, (xs i ∈ L ↔ labels i = true)`
- **Paper locus:** Definitions 2.9 and Appendix A, pp. 8, 29–30
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Faithful combinatorial VC notions; no probabilistic learner.

#### `GenLimit.LiRamanTewari.HasFiniteVCDimension`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:41`
- **Exact/normalized declaration:** `def HasFiniteVCDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ d : ℕ, ∀ xs : Fin (d + 1) → α, ¬VCShatters H xs`
- **Paper locus:** Definitions 2.9 and Appendix A, pp. 8, 29–30
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Faithful combinatorial VC notions; no probabilistic learner.

#### `GenLimit.LiRamanTewari.HasInfiniteVCDimension`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:46`
- **Exact/normalized declaration:** `def HasInfiniteVCDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ d : ℕ, ∃ xs : Fin d → α, VCShatters H xs`
- **Paper locus:** Definitions 2.9 and Appendix A, pp. 8, 29–30
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Faithful combinatorial VC notions; no probabilistic learner.

#### `GenLimit.LiRamanTewari.PACLearnableViaVC`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:52`
- **Exact/normalized declaration:** `def PACLearnableViaVC (H : GenLimit.Generic.LanguageClass α) : Prop := HasFiniteVCDimension H`
- **Paper locus:** Definition 2.8 and VC characterization discussion, p. 8
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Collapsed / trivialized
- **Audit note:** Directly aliases finite VC dimension and omits the PAC model.

#### `GenLimit.LiRamanTewari.PairShattered`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:65`
- **Exact/normalized declaration:** `def PairShattered (H : GenLimit.Generic.LanguageClass α) (x y : α) : Prop := ∀ bx byLabel : Bool, ∃ L, L ∈ H ∧ (x ∈ L ↔ bx = true) ∧ (y ∈ L ↔ byLabel = true)`
- **Paper locus:** Definitions 2.9 and Appendix A, pp. 8, 29–30
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Faithful combinatorial VC notions; no probabilistic learner.

#### `GenLimit.LiRamanTewari.LittlestoneTree`

- **Kind / source:** `inductive`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:110`
- **Exact/normalized declaration:** `inductive LittlestoneTree (α : Type*) : ℕ → Type _ | leaf : LittlestoneTree α 0 | node {d : ℕ} (x : α) (left right : LittlestoneTree α d) : LittlestoneTree α (d + 1)`
- **Paper locus:** Definitions 2.11–2.12, pp. 8–9
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Faithful combinatorial Littlestone notions.

#### `GenLimit.LiRamanTewari.labelClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:117`
- **Exact/normalized declaration:** `def labelClass (H : GenLimit.Generic.LanguageClass α) (x : α) (b : Bool) : GenLimit.Generic.LanguageClass α := {L | L ∈ H ∧ (x ∈ L ↔ b = true)}`
- **Paper locus:** Definitions 2.11–2.12, pp. 8–9
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Faithful combinatorial Littlestone notions.

#### `GenLimit.LiRamanTewari.LittlestoneShattered`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:124`
- **Exact/normalized declaration:** `def LittlestoneShattered : {d : ℕ} → LittlestoneTree α d → GenLimit.Generic.LanguageClass α → Prop | 0, .leaf, H => H.Nonempty | _ + 1, .node x left right, H => LittlestoneShattered left (labelClass H x false) ∧ LittlestoneShattered right (labelClass H x true)`
- **Paper locus:** Definitions 2.11–2.12, pp. 8–9
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Faithful combinatorial Littlestone notions.

#### `GenLimit.LiRamanTewari.HasShatteredLittlestoneTree`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:133`
- **Exact/normalized declaration:** `def HasShatteredLittlestoneTree (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop := ∃ T : LittlestoneTree α d, LittlestoneShattered T H`
- **Paper locus:** Definitions 2.11–2.12, pp. 8–9
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Faithful combinatorial Littlestone notions.

#### `GenLimit.LiRamanTewari.HasFiniteLittlestoneDimension`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:138`
- **Exact/normalized declaration:** `def HasFiniteLittlestoneDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∃ d : ℕ, ¬HasShatteredLittlestoneTree H (d + 1)`
- **Paper locus:** Definitions 2.11–2.12, pp. 8–9
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Faithful combinatorial Littlestone notions.

#### `GenLimit.LiRamanTewari.HasInfiniteLittlestoneDimension`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:143`
- **Exact/normalized declaration:** `def HasInfiniteLittlestoneDimension (H : GenLimit.Generic.LanguageClass α) : Prop := ∀ d : ℕ, HasShatteredLittlestoneTree H d`
- **Paper locus:** Definitions 2.11–2.12, pp. 8–9
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Faithful combinatorial Littlestone notions.

#### `GenLimit.LiRamanTewari.OnlineLearnableViaLittlestone`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:150`
- **Exact/normalized declaration:** `def OnlineLearnableViaLittlestone (H : GenLimit.Generic.LanguageClass α) : Prop := HasFiniteLittlestoneDimension H`
- **Paper locus:** Definition 2.10 and Littlestone characterization discussion, pp. 8–9
- **Correspondence verdict:** Related but materially different
- **Difficulty verdict:** Collapsed / trivialized
- **Audit note:** Directly aliases finite Littlestone dimension and omits online prediction/mistakes.

#### `GenLimit.LiRamanTewari.finiteAugmentationClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:230`
- **Exact/normalized declaration:** `def finiteAugmentationClass : GenLimit.Generic.LanguageClass ℤ := {L | ∃ A : Set ℤ, A ⊆ paperPositiveIntegers ∧ A.Finite ∧ L = paperNonpositiveIntegers ∪ A}`
- **Paper locus:** Appendix A.1 / Theorem 4.1(i), p. 29
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact finite positive augmentation of the nonpositive tail.

#### `GenLimit.LiRamanTewari.singletonSpikeLanguage`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:467`
- **Exact/normalized declaration:** `def singletonSpikeLanguage (a : ℕ) : Set ℤ := paperNonpositiveIntegers ∪ {positiveIntegerPoint a}`
- **Paper locus:** Appendix A.3(iii) / Theorem 4.1(iii), p. 30
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact singleton-spike class.

#### `GenLimit.LiRamanTewari.singletonSpikeClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:472`
- **Exact/normalized declaration:** `def singletonSpikeClass : GenLimit.Generic.LanguageClass ℤ := Set.range singletonSpikeLanguage`
- **Paper locus:** Appendix A.3(iii) / Theorem 4.1(iii), p. 30
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact singleton-spike class.

#### `GenLimit.LiRamanTewari.thresholdLanguage`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:541`
- **Exact/normalized declaration:** `def thresholdLanguage (a : ℕ) : Set ℕ := {x | a ≤ x}`
- **Paper locus:** Appendix A.3(v) / Theorem 4.1(v), p. 30
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Threshold class realized on ℕ; existential properties are preserved.

#### `GenLimit.LiRamanTewari.thresholdClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:543`
- **Exact/normalized declaration:** `def thresholdClass : GenLimit.Generic.LanguageClass ℕ := Set.range thresholdLanguage`
- **Paper locus:** Appendix A.3(v) / Theorem 4.1(v), p. 30
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Threshold class realized on ℕ; existential properties are preserved.

#### `GenLimit.LiRamanTewari.liftLeftLanguage`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:708`
- **Exact/normalized declaration:** `def liftLeftLanguage (L : Set α) : Set (α ⊕ β) := {z | match z with | Sum.inl x => x ∈ L | Sum.inr _ => False}`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum replacement for the displayed union on one arithmetic universe.

#### `GenLimit.LiRamanTewari.liftRightLanguage`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:714`
- **Exact/normalized declaration:** `def liftRightLanguage (L : Set β) : Set (α ⊕ β) := {z | match z with | Sum.inl _ => False | Sum.inr y => y ∈ L}`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum replacement for the displayed union on one arithmetic universe.

#### `GenLimit.LiRamanTewari.liftLeftClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:719`
- **Exact/normalized declaration:** `def liftLeftClass (H : GenLimit.Generic.LanguageClass α) : GenLimit.Generic.LanguageClass (α ⊕ β) := liftLeftLanguage '' H`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum replacement for the displayed union on one arithmetic universe.

#### `GenLimit.LiRamanTewari.liftRightClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:723`
- **Exact/normalized declaration:** `def liftRightClass (H : GenLimit.Generic.LanguageClass β) : GenLimit.Generic.LanguageClass (α ⊕ β) := liftRightLanguage '' H`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum replacement for the displayed union on one arithmetic universe.

#### `GenLimit.LiRamanTewari.ThresholdBlockUniverse`

- **Kind / source:** `abbrev`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:727`
- **Exact/normalized declaration:** `abbrev ThresholdBlockUniverse := ℕ ⊕ BlockUniverse`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum replacement for the displayed union on one arithmetic universe.

#### `GenLimit.LiRamanTewari.thresholdBlockClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:733`
- **Exact/normalized declaration:** `def thresholdBlockClass : GenLimit.Generic.LanguageClass ThresholdBlockUniverse := liftLeftClass thresholdClass ∪ liftRightClass blockSeparationClass`
- **Paper locus:** Appendix A.3(iv) / Theorem 4.1(iv), p. 30
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Typed disjoint-sum replacement for the displayed union on one arithmetic universe.

#### `GenLimit.LiRamanTewari.cofiniteClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/Prediction.lean:1140`
- **Exact/normalized declaration:** `def cofiniteClass : GenLimit.Generic.LanguageClass ℕ := {L | ∃ A : Set ℕ, A.Finite ∧ L = Aᶜ}`
- **Paper locus:** Appendix A.3(vi) / Theorem 4.1(vi), p. 30
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact cofinite class on ℕ.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean`

#### `GenLimit.LiRamanTewari.IsPromptedClosureWitness`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:15`
- **Exact/normalized declaration:** `def IsPromptedClosureWitness (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Prop := (promptedVersionSpace H S y).Nonempty ∧ (promptedCommonCore H S y).Finite`
- **Paper locus:** Definition 5.5, p. 24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted closure-dimension encodings.

#### `GenLimit.LiRamanTewari.PromptedClosureDimensionAtMost`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:21`
- **Exact/normalized declaration:** `def PromptedClosureDimensionAtMost (H : MulticlassHypothesisClass α ι) (d : ℕ) : Prop := ∀ y : ι, ∀ S : Finset α, d < S.card → (promptedVersionSpace H S y).Nonempty → (promptedCommonCore H S y).Infinite`
- **Paper locus:** Definition 5.5, p. 24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted closure-dimension encodings.

#### `GenLimit.LiRamanTewari.HasPromptedClosureDimension`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:28`
- **Exact/normalized declaration:** `def HasPromptedClosureDimension (H : MulticlassHypothesisClass α ι) (d : ℕ) : Prop := PromptedClosureDimensionAtMost H d ∧ (d = 0 ∨ ∃ y : ι, ∃ S : Finset α, S.card = d ∧ IsPromptedClosureWitness H S y)`
- **Paper locus:** Definition 5.5, p. 24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted closure-dimension encodings.

#### `GenLimit.LiRamanTewari.HasFinitePromptedClosureDimension`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:36`
- **Exact/normalized declaration:** `def HasFinitePromptedClosureDimension (H : MulticlassHypothesisClass α ι) : Prop := ∃ d : ℕ, HasPromptedClosureDimension H d`
- **Paper locus:** Definition 5.5, p. 24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted closure-dimension encodings.

#### `GenLimit.LiRamanTewari.HasInfinitePromptedClosureDimension`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:41`
- **Exact/normalized declaration:** `def HasInfinitePromptedClosureDimension (H : MulticlassHypothesisClass α ι) : Prop := ∀ d : ℕ, ∃ y : ι, ∃ S : Finset α, d ≤ S.card ∧ IsPromptedClosureWitness H S y`
- **Paper locus:** Definition 5.5, p. 24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted closure-dimension encodings.

#### `GenLimit.LiRamanTewari.promptedSequenceSample`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:120`
- **Exact/normalized declaration:** `noncomputable def promptedSequenceSample {t : ℕ} (history : Fin t → PromptedObservation α ι) (y : ι) : Finset α := by classical exact (Finset.univ.filter (fun i ↦ (history i).2.1 = y)).image (fun i ↦ (history i).1)`
- **Paper locus:** Definitions 5.2–5.3 and prompted-history semantics, pp. 22–23
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Extracts label-specific and global observed samples from the revealed triples.

#### `GenLimit.LiRamanTewari.promptedObservedSample`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:128`
- **Exact/normalized declaration:** `noncomputable def promptedObservedSample {t : ℕ} (history : Fin t → PromptedObservation α ι) : Finset α := GenLimit.Generic.sequenceSample (fun i ↦ (history i).1)`
- **Paper locus:** Definitions 5.2–5.3 and prompted-history semantics, pp. 22–23
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Extracts label-specific and global observed samples from the revealed triples.

#### `GenLimit.LiRamanTewari.promptedClosureGenerator`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedClosure.lean:168`
- **Exact/normalized declaration:** `noncomputable def promptedClosureGenerator [Nonempty α] (H : MulticlassHypothesisClass α ι) (d : ℕ) (hPC : PromptedClosureDimensionAtMost H d) : PromptedGenerator α ι := by classical exact fun t history ↦ if ht : 0 < t then let last : Fin t := ⟨t - 1, Nat.sub_lt (by omega) (by omega)⟩ let y := (history last).2.2 let S := promptedSequenceSample history y let observed := promptedObservedSample history if hd : d < S.card then if hVS : (promptedVersionSpace H S y).Nonempty then Classical.choose (prompted_core_diff_observed_infinite hPC S observed y hd hVS).nonempty else Classical.choice inferInstance else Classical.choice inferInstance else Classical.choice inferInstance`
- **Paper locus:** Theorem 5.1 sufficiency construction, Appendix B.1, p. 31
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Noncomputable prompted common-core generator at threshold d+1.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean`

#### `GenLimit.LiRamanTewari.MulticlassHypothesis`

- **Kind / source:** `abbrev`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:19`
- **Exact/normalized declaration:** `abbrev MulticlassHypothesis (α ι : Type*) := α → ι`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.MulticlassHypothesisClass`

- **Kind / source:** `abbrev`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:21`
- **Exact/normalized declaration:** `abbrev MulticlassHypothesisClass (α ι : Type*) := Set (MulticlassHypothesis α ι)`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.promptSupport`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:25`
- **Exact/normalized declaration:** `def promptSupport (h : MulticlassHypothesis α ι) (y : ι) : Set α := {x | h x = y}`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.PUUS`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:29`
- **Exact/normalized declaration:** `def PUUS (H : MulticlassHypothesisClass α ι) : Prop := ∀ h, h ∈ H → ∀ y, (promptSupport h y).Infinite`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.PromptedObservation`

- **Kind / source:** `abbrev`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:34`
- **Exact/normalized declaration:** `abbrev PromptedObservation (α ι : Type*) := α × ι × ι`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.PromptedGenerator`

- **Kind / source:** `abbrev`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:39`
- **Exact/normalized declaration:** `abbrev PromptedGenerator (α ι : Type*) := ∀ t : ℕ, (Fin t → PromptedObservation α ι) → α`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.promptedHistory`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:43`
- **Exact/normalized declaration:** `def promptedHistory (h : MulticlassHypothesis α ι) (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι) (t : ℕ) : Fin t → PromptedObservation α ι := fun i ↦ (xs i, h (xs i), ys i)`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.promptedSample`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:52`
- **Exact/normalized declaration:** `noncomputable def promptedSample (h : MulticlassHypothesis α ι) (xs : GenLimit.Generic.Stream α) (y : ι) (t : ℕ) : Finset α := by classical exact (GenLimit.Generic.sample xs t).filter (fun x ↦ h x = y)`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.PromptedCorrectAt`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:79`
- **Exact/normalized declaration:** `def PromptedCorrectAt (gen : PromptedGenerator α ι) (h : MulticlassHypothesis α ι) (xs : GenLimit.Generic.Stream α) (ys : GenLimit.Generic.Stream ι) (s : ℕ) : Prop := ∀ _hs : 0 < s, gen s (promptedHistory h xs ys s) ∈ promptSupport h (ys (s - 1)) \ (↑(GenLimit.Generic.sample xs s) : Set α)`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.IsPromptedUniformGeneratorAt`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:94`
- **Exact/normalized declaration:** `def IsPromptedUniformGeneratorAt (gen : PromptedGenerator α ι) (H : MulticlassHypothesisClass α ι) (d : ℕ) : Prop := ∀ h, h ∈ H → ∀ xs : GenLimit.Generic.Stream α, ∀ ys : GenLimit.Generic.Stream ι, ∀ yStar : ι, ∀ t, (promptedSample h xs yStar t).card = d → ∀ s, t ≤ s → ∀ _hs : 0 < s, ys (s - 1) = yStar → PromptedCorrectAt gen h xs ys s`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.PromptedUniformlyGeneratable`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:106`
- **Exact/normalized declaration:** `def PromptedUniformlyGeneratable (H : MulticlassHypothesisClass α ι) : Prop := ∃ gen : PromptedGenerator α ι, ∃ d : ℕ, IsPromptedUniformGeneratorAt gen H d`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.IsPromptedNonuniformGenerator`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:113`
- **Exact/normalized declaration:** `def IsPromptedNonuniformGenerator (gen : PromptedGenerator α ι) (H : MulticlassHypothesisClass α ι) : Prop := ∀ h, h ∈ H → ∃ d : ℕ, ∀ xs : GenLimit.Generic.Stream α, ∀ ys : GenLimit.Generic.Stream ι, ∀ yStar : ι, ∀ t, (promptedSample h xs yStar t).card = d → ∀ s, t ≤ s → ∀ _hs : 0 < s, ys (s - 1) = yStar → PromptedCorrectAt gen h xs ys s`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.PromptedNonuniformlyGeneratable`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:125`
- **Exact/normalized declaration:** `def PromptedNonuniformlyGeneratable (H : MulticlassHypothesisClass α ι) : Prop := ∃ gen : PromptedGenerator α ι, IsPromptedNonuniformGenerator gen H`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.PromptSupportPresented`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:131`
- **Exact/normalized declaration:** `def PromptSupportPresented (h : MulticlassHypothesis α ι) (xs : GenLimit.Generic.Stream α) (y : ι) : Prop := promptSupport h y ⊆ Set.range xs`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.IsPromptedLimitGenerator`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:137`
- **Exact/normalized declaration:** `def IsPromptedLimitGenerator (gen : PromptedGenerator α ι) (H : MulticlassHypothesisClass α ι) : Prop := ∀ h, h ∈ H → ∀ xs : GenLimit.Generic.Stream α, ∀ ys : GenLimit.Generic.Stream ι, ∀ yStar : ι, PromptSupportPresented h xs yStar → ∃ t, ∀ s, t ≤ s → ∀ _hs : 0 < s, ys (s - 1) = yStar → PromptedCorrectAt gen h xs ys s`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.PromptedGeneratableInLimit`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:149`
- **Exact/normalized declaration:** `def PromptedGeneratableInLimit (H : MulticlassHypothesisClass α ι) : Prop := ∃ gen : PromptedGenerator α ι, IsPromptedLimitGenerator gen H`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.promptedVersionSpace`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:154`
- **Exact/normalized declaration:** `def promptedVersionSpace (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Set (MulticlassHypothesis α ι) := {h | h ∈ H ∧ ∀ x ∈ S, h x = y}`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.promptedCommonCore`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:160`
- **Exact/normalized declaration:** `def promptedCommonCore (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Set α := {x | ∀ h, h ∈ promptedVersionSpace H S y → h x = y}`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

#### `GenLimit.LiRamanTewari.promptedClosure`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedDefinitions.lean:165`
- **Exact/normalized declaration:** `noncomputable def promptedClosure (H : MulticlassHypothesisClass α ι) (S : Finset α) (y : ι) : Option (Set α) := by classical exact if (promptedVersionSpace H S y).Nonempty then some (promptedCommonCore H S y) else none`
- **Paper locus:** Assumption 2 and Definitions 5.1–5.5, pp. 22–24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Exact prompted game after correcting the displayed h(x₁) typo to the current true label.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean`

#### `GenLimit.LiRamanTewari.PositivePrompt`

- **Kind / source:** `abbrev`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:18`
- **Exact/normalized declaration:** `abbrev PositivePrompt := {n : ℕ // 0 < n}`
- **Paper locus:** Lemma 5.4 and Corollary 5.5 constructions, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged positive-prompt version of the two-hypothesis prime-power construction.

#### `GenLimit.LiRamanTewari.firstPositivePrompt`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:20`
- **Exact/normalized declaration:** `def firstPositivePrompt : PositivePrompt := ⟨1, by omega⟩`
- **Paper locus:** Lemma 5.4 and Corollary 5.5 constructions, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged positive-prompt version of the two-hypothesis prime-power construction.

#### `GenLimit.LiRamanTewari.PromptSeparationUniverse`

- **Kind / source:** `abbrev`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:24`
- **Exact/normalized declaration:** `abbrev PromptSeparationUniverse := PositivePrompt × Option Bool × ℕ`
- **Paper locus:** Lemma 5.4 and Corollary 5.5 constructions, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged positive-prompt version of the two-hypothesis prime-power construction.

#### `GenLimit.LiRamanTewari.promptSeparationLeft`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:27`
- **Exact/normalized declaration:** `def promptSeparationLeft : MulticlassHypothesis PromptSeparationUniverse PositivePrompt := fun x ↦ match x.2.1 with | none => if x.2.2 < x.1.1 then x.1 else firstPositivePrompt | some false => x.1 | some true => firstPositivePrompt`
- **Paper locus:** Lemma 5.4 and Corollary 5.5 constructions, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged positive-prompt version of the two-hypothesis prime-power construction.

#### `GenLimit.LiRamanTewari.promptSeparationRight`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:36`
- **Exact/normalized declaration:** `def promptSeparationRight : MulticlassHypothesis PromptSeparationUniverse PositivePrompt := fun x ↦ match x.2.1 with | none => if x.2.2 < x.1.1 then x.1 else firstPositivePrompt | some false => firstPositivePrompt | some true => x.1`
- **Paper locus:** Lemma 5.4 and Corollary 5.5 constructions, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged positive-prompt version of the two-hypothesis prime-power construction.

#### `GenLimit.LiRamanTewari.promptSeparationClass`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:45`
- **Exact/normalized declaration:** `def promptSeparationClass : MulticlassHypothesisClass PromptSeparationUniverse PositivePrompt := {promptSeparationLeft, promptSeparationRight}`
- **Paper locus:** Lemma 5.4 and Corollary 5.5 constructions, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged positive-prompt version of the two-hypothesis prime-power construction.

#### `GenLimit.LiRamanTewari.promptBlock`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedInfinitePromptExample.lean:50`
- **Exact/normalized declaration:** `noncomputable def promptBlock (p : PositivePrompt) : Finset PromptSeparationUniverse := by classical exact (Finset.range p.1).image (fun k ↦ (p, none, k))`
- **Paper locus:** Lemma 5.4 and Corollary 5.5 constructions, pp. 25–26
- **Correspondence verdict:** Faithful specialization
- **Difficulty verdict:** Preserved
- **Audit note:** Tagged positive-prompt version of the two-hypothesis prime-power construction.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean`

#### `GenLimit.LiRamanTewari.IsPromptedNondecreasingCover`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/PromptedNonuniform.lean:19`
- **Exact/normalized declaration:** `def IsPromptedNondecreasingCover (H : MulticlassHypothesisClass α ι) (classes : ℕ → MulticlassHypothesisClass α ι) : Prop := Monotone classes ∧ H = ⋃ n, classes n`
- **Paper locus:** Theorem 5.2, p. 24
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Monotone multiclass subclasses with exact union equality.

### `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean`

#### `GenLimit.LiRamanTewari.uniformGenerationSampleComplexity`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:42`
- **Exact/normalized declaration:** `noncomputable def uniformGenerationSampleComplexity (gen : GenLimit.Generic.Generator α) (H : GenLimit.Generic.LanguageClass α) : WithTop ℕ := by classical exact if h : ∃ d : ℕ, IsUniformGeneratorAt gen H d then (Nat.find h : WithTop ℕ) else ⊤`
- **Paper locus:** Definition 2.4, p. 6
- **Correspondence verdict:** Exact / formally equivalent
- **Difficulty verdict:** Preserved
- **Audit note:** Least valid fixed-generator threshold or top.

#### `GenLimit.LiRamanTewari.optimalUniformGenerationSampleComplexity`

- **Kind / source:** `def`, `GenLimitLean/GenLimit/Paper02_GenerationThroughTheLensOfLearningTheory/UniformSampleComplexity.lean:139`
- **Exact/normalized declaration:** `noncomputable def optimalUniformGenerationSampleComplexity (H : GenLimit.Generic.LanguageClass α) : WithTop ℕ := by classical exact if h : ∃ d : ℕ, ∃ gen : GenLimit.Generic.Generator α, IsUniformGeneratorAt gen H d then (Nat.find h : WithTop ℕ) else ⊤`
- **Paper locus:** Unnumbered optimal-complexity discussion after Theorem 3.3, p. 12
- **Correspondence verdict:** Faithful generalization
- **Difficulty verdict:** Strengthened / harder
- **Audit note:** Makes the class-optimal least threshold explicit.
