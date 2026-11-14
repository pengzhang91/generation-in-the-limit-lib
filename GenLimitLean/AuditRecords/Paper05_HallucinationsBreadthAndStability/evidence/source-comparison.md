# P05 Stage 2: independent source and Lean statement comparison

## Identity, scope, and evidence boundary

The six facade declarations represent a substantial semantic core of the paper, but they do not represent its complete mathematical or algorithmic contribution. Exact breadth and stable approximate breadth have close semantic counterparts. Two other targets instead assert universal impossibility under a literal freshness convention; these are materially different from the positive stable-generation statements associated with their source numbers. A whole-target counterpart matches an alternative convention explicitly discussed in the paper. These findings concern statements, not proof correctness or the eventual Stage 3 adjudication.

The pinned source is Alkis Kalavasis, Anay Mehrotra, and Grigoris Velegkas, *On Characterizations for Language Generation: Interplay of Hallucinations, Breadth, and Stability*, arXiv:2412.18530v2, version dated 3 July 2025. The supplied official PDF has 46 pages, 1,476,994 bytes, and SHA-256 `ba5c0de2215a156ea45791e2399487aed75e08715176d57c24e6238ce4fdd7dd`. Throughout this report, a citation such as p. 17 means both printed page 17 and one-based PDF page 17; inspected footers agree. No other edition or outside mathematical source was used.

The complete source claim inventory below was established from pages 1-46 before either frozen Stage 1 file was opened. The representation assessments were added afterward. Decisive formulas and conventions were visually checked on rendered PDF pages 7, 9, 12, 17, 20, 22, 38, 39, 40, 41, and 46, using Ghostscript because Poppler was unavailable. The PNG filenames and full hashes are recorded in `stage2-run.json`.

The frozen Stage 1 hashes matched the supplied values: reconstruction `8eed8dcb9c22ca48c5c355759acecd288120ad889db3d3e63b5762510f0f579f`; run record `8b2f026804e72c8ccf46de1ffc54e116ffcd076be192ea9803f34ccce09e9eec`. The Lean snapshot records working-tree capture at 2026-11-10T05:05:20.850589Z, HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`, dirty tree, Lean v4.24.0, and Mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. These are snapshot provenance, not a fresh Git or compilation observation.

Exactly six targets receive dossiers. Coverage checks additionally inspect the complete 34-module native-paper closure in `stage2/coverage-context/source-index.json`, including its two supplemental files. All 55 Stage 2 checksum entries and all 34 indexed source hashes matched. The project imports within that closure resolve to indexed files. Comments and theorem proof bodies supplied no mathematical evidence. Defining values, including values written using `by`, were inspected as definitions; theorem statements were extracted separately. No build, proof audit, library edit, Git operation, developer explanation, or human certification occurred.

## Independent full-paper inventory

There are 57 distinct numbered items, including definitions, remarks, examples, and informal theorems. A textual mention of Theorem 4.5 on p. 19 is not an additional theorem. The following inventory includes all 57; four figures and substantive unnumbered claims follow it. “Native” means a statement within the supplied umbrella closure, including imported modules, not necessarily a P05 facade declaration. A semantic counterpart does not automatically include the source's effective implementation claims.

| Source items and exact pages | Independently inventoried content | Representation after checking the full closure |
|---|---|---|
| Informal Theorem 1.1, p. 4; 1.2, p. 5; 1.3, p. 6 | Exact breadth versus identification; approximate breadth versus weak Angluin condition; stable exact/approximate breadth versus identification. | Detailed counterparts and qualifications appear in T1-T5; the approximate converse is not supplied by T2. |
| Definition 2.1, pp. 7-8 | On every complete target enumeration, eventually the output is contained in the unseen target remainder. | `GeneratesInLimitCorrectAt` and `IsLimitGenerator`, Definitions.lean:39,50, match the literal subset specification. Nonemptiness is absent on both sides. |
| Definition 2.2, p. 8; Remark 2.3, pp. 8-9 | Finite tell-tales prohibit proper sublanguages containing them; upper constructions have succinct, effective sampling/enumeration/membership representations, whereas lower bounds allow noncomputable functions. | `Angluin.IsTellTale`/`ConditionTwo` match the set condition. Effective representations are not part of the six targets. |
| Definitions 3.1, 3.2; Theorem 3.3, p. 9 | Exact support is K minus the observed set; approximate support is a subset of K with finite omissions; exact breadth iff Angluin condition. | Definitions.lean:57,74 and T1 provide semantic counterparts. |
| Definition 3.4; Theorem 3.5; Remark 3.6, p. 10 | Abstract uniqueness criterion, its general Angluin lower bound, and strict metric-separation consequences. | No native abstract property/uniqueness lower-bound statement or metric instantiation. Exact-specific necessity exists, but does not formalize the general theorem. |
| Definition 3.7, pp. 10-11 | Weak finite tell-tales allow proper sublanguages only with finite missing difference; an oracle enumerates each tell-tale. | The set condition is represented by `IsWeakTellTale`/`WeakAngluinCondition`; its enumerating-oracle contract is absent. |
| Theorem 3.8; Definition 3.9, p. 11 | Approximate breadth iff weak condition; abstract finite non-uniqueness means simultaneous success only for finitely differing languages. | T2 gives the sufficiency implication, weak condition to approximate generation. Neither the general finite-non-uniqueness predicate nor a native approximate-breadth converse is stated. |
| Theorem 3.10; Remarks 3.11, 3.12, 3.13, p. 12 | General weak-condition lower bound; metric consequences; stochastic extension; N and its co-singletons separate strong from weak conditions. | General theorem and statistical extension absent. Imported P04 has a co-singleton example over integers, weak-condition satisfaction, and failure of a tell-tale for the whole domain: a semantic counterpart of the example after domain reindexing. |
| Definition 3.14; Theorem 3.15, p. 12 | Eventually equal supports on each presentation; stable approximate and stable exact characterization by strong condition. | Stability and approximate arm are represented; exact arm requires the convention analysis in T4-T5. |
| Definitions 4.1, 4.2, p. 15 | Unambiguous generation strictly minimizes cardinal symmetric difference; exhaustive generation has finite current hallucinations and covers K by observations, earlier first outputs, and current enumeration. | Imported P03 defines unambiguous generation using `encard`; imported P04 defines the full history-sensitive exhaustive predicate, not just finite symmetric difference. |
| Theorem 4.3, p. 16 | Exact/unambiguous iff strong condition; approximate/exhaustive iff weak condition. | Exact equivalence and approximate sufficiency are present. Full exhaustive semantic equivalence is imported. Unstable unambiguous characterization and approximate necessity are not native theorem statements. |
| Remark 4.4; Theorem 4.5, p. 17 | Stability discussion and five-way characterization covering all four breadth notions and strong condition. Footnote 3 permits seen strings for exact breadth. | Stable approximate and stable whole-target core are present. Imported stable-unambiguous necessity is partial coverage. No stable-exhaustive equivalence is supplied. |
| Definition 5.1, pp. 20-21; Theorem 5.2, p. 21; Theorem 5.3, p. 22 | Universal expected-error rates; exponential upper/lower rates; no-rate alternatives for exact and approximate breadth, with a wording issue in 5.3. | No native probability, expected breadth-loss, universal-rate, or no-rate formalization in the closure. |
| Corollary 6.1, p. 26 | An approximate generator on a nonidentifiable family admits a presentation with infinitely many success times for distinct proper sublanguages. | No native statement of this adversarial trace; T3's end characterization is not that intermediate claim. |
| Lemma 7.1, p. 28; Corollary 7.2, pp. 29-30 | Membership/subset-oracle approximate generator; the particular KM-derived function achieves exact, approximate, or infinite coverage according to the family's condition. | A named semantic critical-focus generator achieves approximate breadth. No bundled oracle contract or named three-regime theorem, especially its exact/infinite arms, is stated. |
| Lemma 7.3, pp. 30-32; Remark 7.4, p. 32 | Membership-plus-tell-tale implementation, decidable MOP, and instability of that construction. | No tell-tale-oracle algorithm or computational MOP statement for this construction. Semantic existence does not cover this refinement. |
| Lemma 7.5; Remark 7.6, p. 32 | Exhaustive function with membership, subset, and finite-difference access, additionally eventually consistent. | Imported P04 has exhaustive semantic sufficiency with finite hallucinations; the stronger eventual absence of hallucinations and this access contract are not asserted there. |
| Lemma 7.7, pp. 34-35 | Exhaustive generator with membership and tell-tale oracle access. | Semantic exhaustive existence is present; this implementation refinement is absent. |
| Remarks 8.1, 8.2, p. 35 | Cross-references to existing stable-breadth results and hallucination variants. | No additional mathematical claim beyond those mapped. |
| Definition 8.3; Proposition 8.4; Remark 8.5, p. 36 | Infinite fresh coverage; universal possibility for countable families; functions versus membership/tell-tale algorithms. | Literal coverage predicate exists. There is no positive `IsInfiniteCoverageGenerator` existence theorem in the closure; critical-focus ingredients exist, but the three-conjunct positive result remains unpackaged. Access distinction is not modeled computationally. |
| Example 8.6; Theorem 8.7, pp. 37-38 | Co-singleton family satisfies weak condition but admits no stable infinite-coverage generator. | Imported co-singleton structural example is present over integers. T6 supplies a broader literal-freshness obstruction, not the intended nontrivial separation under seen-support conventions. |
| Definition 8.8, p. 38; Definition 8.9, p. 39 | Closure dimension from finite intersections of consistent families; VSI membership oracle. | Neither closure-dimension nor VSI interface is defined in the closure. |
| Proposition 8.10, pp. 39-40 | Finite closure dimension yields stable infinite coverage with VSI access after d+1 distinct examples. | T6 is an obstruction to its literal specification, not a positive formalization. No relaxed positive counterpart or distinct-example bound is present. |
| Corollary 8.11, p. 39 | Finite collections: stable exact breadth with membership access, and stable infinite coverage after d+1 distinct examples. | General strong-condition/whole-target results supply relevant semantic ingredients; no finite-collection oracle instantiation or bounded coverage result is stated. |
| Example 8.12, p. 40 | Integer upper tails plus Z fail weak condition yet purportedly have a stable infinite-coverage generator after one observation. | No native upper-tail family or such positive generator. The displayed source witness itself raises a question below. |
| Definition 8.13, pp. 40-41; Proposition 8.14, p. 41 | Eventual support inclusion and eventual strict growth unless already equal to K; an infinite-coverage example outside weak condition. | Increasing coverage, its witness, and its separation are absent from the native closure. Footnote 17 changes the freshness convention. |
| Observation A.1, p. 44; Observation A.2; Remark A.3, p. 45 | Unambiguous uniqueness; exhaustive finite non-uniqueness; exhaustive failure of uniqueness. | Concrete predicates and co-singleton constructions exist; these abstract criterion statements are not supplied. |
| Definition A.4, p. 45 | MOP asks support membership from a generator description and a string. | P03 has Boolean membership fields; the supplied values impose no recursive program or generator-description model. |
| Definition B.1, pp. 45-46; Theorem B.2, p. 46 | Identification stabilizes to one correct index despite duplicate languages; effective characterization requires tell-tale enumeration access and a converse implementability claim. | Semantic identification has the correct stable-index form. Imported Angluin equivalence is semantic; oracle access/implementability aspects are not represented. |

Figure 1, p. 11, illustrates the strong and weak conditions. Figure 2, p. 18, summarizes strict separations. Figure 3, p. 19, claims a nine-cell breadth/hallucination classification: strong condition only for exact/no hallucination, weak condition for the other three upper-left cells, and universal possibility in the remaining cells. Figure 4, p. 20, gives the stable version, with strong condition in both first-column breadth cells, weak condition in both finite-hallucination breadth cells, universal right column, and two expressly unresolved infinite-coverage cells. The supplied Lean closure has neither a general hallucination grid nor all its cell characterizations. Exhaustive sufficiency partly overlaps finite-hallucination coverage, but is a different predicate; it is not blanket grid coverage.

Unnumbered claims also matter: arbitrary finite prescribed coverage sizes on p. 35; closure dimension finiteness for finite collections on p. 38; approximate plus increasing coverage forcing eventual exact support on p. 41; a proposed finite-output postprocessing argument on p. 41; and extension to prompted generation on p. 42. These are not native theorem statements. Pages 13-14, 22-35, 37-41, and 44-45 provide proof/construction context; it was used only to interpret source terminology and conventions, not to certify the arguments. Pages 43 and 46 contain references and a comparison to other work; no external paper was imported as evidence.

## Common dictionary and dependencies

Write B for `GenLimit.BreadthCharacterizations`, A for `GenLimit.Angluin`, and Q for `GenLimit.Generic`. Native paths below are relative to `stage2/source-snapshot/GenLimitLean/GenLimit/` unless stated otherwise. `Results/Overview.lean` lies in the P05 directory. Full target identifiers are given in each dossier.

The decisive defining values were independently rechecked. A language is `Set α`; a family is `Nat → Set α`; a presentation satisfies `range s = K`. `textPrefix s t` contains observations at indices below t, and `sample s t` is their finite set. This is the source's first-n-observations convention after harmless zero-based indexing. Repetitions and duplicate family indices are allowed. The paper's finite alphabet Σ gives a countable domain Σ*, while Lean's α denotes the observation/string domain, not necessarily the alphabet itself.

`SupportAlgorithm α = List α → Set α` sees only ordered finite history. One existential G is chosen for the family before target index and presentation; convergence thresholds follow the presentation. Set-valued functions are not stochastic models or algorithms merely because they are named generators. The source also allows arbitrary functions in lower bounds, so semantic lower statements can be faithful without effectivity. Source upper representation claims require a separate assessment.

Define S(t)=G(textPrefix s t), D(t)=sample s t. Exact correctness is S(t)=K\D(t); approximate correctness is S(t)⊆K and Finite(K\S(t)); whole-target correctness is S(t)=K; infinite coverage is S(t)⊆K, Disjoint(S(t),D(t)), and Infinite(S(t)). Each generator predicate has `∀ z s, Presents s (F z) → ∃ T, ∀ t≥T, ...`. Stability separately has `∀ z s, Presents ... → ∃ T, ∀ n,n'≥T, S(n)=S(n')`. Conjuncts use the same G but can have different thresholds.

A strong tell-tale W is a finite subset of F i such that `W⊆F j → F j⊆F i → F i⊆F j`. This is equivalent to forbidding proper sublanguages containing W. A weak tell-tale changes the competitor requirement to `F j ⊂ F i → Finite(F i\F j)`. Both have `∀ i ∃ W ∀ j`, without a finite-size bound or effective selector. `chosenTellTale` explicitly uses `Classical.choose`; its constant approximation and semantic learner do not implement the source's tell-tale oracle.

## T1: exact breadth characterization

**Target:** `GenLimit.BreadthCharacterizations.Results.theorem_3_3_semantic`, Overview.lean:27. Direct native counterpart: ExactBreadth.lean:250.

```lean
[Nonempty α] [Countable α] (F : Q.LanguageFamily α)
(hInfinite : ∀ i, (F i).Infinite) :
B.ExactBreadthGeneratable F ↔ A.ConditionTwo F
```

**Source:** Theorem 3.3, p. 9; Definitions 2.2 and 3.1, pp. 8-9; Informal Theorem 1.1, p. 4. The shared skeleton is `(∃ G ∀ z s, Presents → ∃ T ∀ t≥T, S(t)=F z\D(t)) ↔ (∀ i ∃ W, strong-telltale(F,i,W))`. Witness placement, finite history, complete adversarial presentations, exact equality, and absence of time bounds agree. The source defines languages as infinite; Lean retains that assumption explicitly. Nonempty/countable instances do not supply executable enumerations.

**Correspondence:** exact/equivalent for the semantic set-and-history characterization; faithful domain generalization from strings to arbitrary nonempty countable α. The ordinary/oracle computational implementation component is not represented. This qualification is material because Remark 2.3 and Appendix B distinguish effective access from mere existence. The actual native `exactBreadthFromConditionTwo` value uses the semantic learner and chosen tell-tales, then removes `historySet`; no theorem type specifies a membership-oracle program.

**Strength and boundaries:** neither direction loses set-theoretic content. The source's informal identification wording must be read with its access qualifications, not substituted for semantic inferrability without comment. Output is infinite eventually because an infinite target loses only a finite sample. It remains changing as new elements arrive; stability is not a conclusion. Empty/finite targets lie outside the hypothesis; repetitions only delay convergence. Duplicate language indices do not require discovering their original index. No distribution, expected loss, universal rate, or named T appears. The facade existential itself does not designate the separately defined native construction.

## T2: approximate breadth sufficiency

**Target:** `GenLimit.BreadthCharacterizations.Results.theorem_3_8_sufficiency_semantic`, Overview.lean:37. Native counterpart: ApproximateBreadth.lean:94.

```lean
[Countable α] (F : Q.LanguageFamily α)
(hInfinite : ∀ i, (F i).Infinite) :
B.WeakAngluinCondition F → B.ApproximateBreadthGeneratable F
```

**Source:** sufficiency direction of Theorem 3.8, p. 11; Definition 3.2, p. 9; Definition 3.7, pp. 10-11. Lemmas 7.1 and 7.3, pp. 28 and 30, separately refine existence by access model. Lean has `∀ F, infinite-members → (∀ i ∃ W, weak-telltale) → ∃ G ∀ z s, Presents → ∃ T ∀ t≥T, S(t)⊆F z ∧ Finite(F z\S(t))`. Quantifier dependencies and both correctness conjuncts match the semantic sufficiency claim.

**Correspondence:** faithful specialization to the sufficiency component, with a faithful domain generalization; not an equivalent formalization of the entire source theorem. The missing converse is not recovered by the six targets or by a native approximate-necessity theorem. Imported exhaustive necessity concerns a different output representation and needs a bridge; mathematical derivability is not a supplied declaration.

The rechecked named native `approximateFocusAlgorithm` returns the family member selected by `exhaustiveFocus`. The latter filters a finite index range using global subset comparisons and chooses a greatest critical index. This explains a semantic relationship to the source's subset-oracle construction, but does not certify that construction or an implementation. **Source-construction interpretation:** Lemma 7.1's displayed output removes observations, while the Lean definition returns the whole focus language. Definition 3.2 permits observed strings, so this difference does not invalidate the compared approximate predicate. It does prevent attributing the source construction's freshness to the native value.

**Strength and boundaries:** no stabilization, common finite exception set, omitted-cardinality bound, decidable MOP program, tell-tale enumeration, or membership-only access is asserted. Finite omissions may vary with time. The result has no explicit Nonempty instance, but infinite members force a nonempty domain. An infinite approximate subset is productive semantically; no sampler law follows. The facade's unspecified existential witness is not itself a named algorithmic guarantee for Lemma 7.3 or Corollary 7.2.

## T3: stable approximate breadth

**Target:** `GenLimit.BreadthCharacterizations.Results.theorem_3_15_approximate_semantic`, Overview.lean:46. Native counterpart: StableApproximate.lean:55.

```lean
(F : Q.LanguageFamily Nat) (hInfinite : ∀ i, (F i).Infinite) :
(∃ G, B.IsStableGenerator G F ∧ B.IsApproximateBreadthGenerator G F)
  ↔ A.ConditionTwo F
```

**Source:** approximate arm of Theorem 3.15, p. 12, and Theorem 4.5, p. 17; Definitions 3.2 and 3.14, pp. 9 and 12. Both require a single G, eventual pairwise equality of supports on every target presentation, and eventual target containment with finite omission. Stabilization and correctness thresholds can be combined by a maximum; neither specification makes them uniform across presentations.

**Correspondence:** faithful specialization of the semantic approximate arm to Nat. Encoding a countable string domain into Nat is mathematically plausible but no transport statement is included in this target, so its actual domain restriction is retained. The target does not express the exact or other-breadth arms of the source characterization, nor its computational refinements.

The native `asP03SupportGenerator` at Relationships.lean:25 fills a Boolean query field using classical `decide (x ∈ G history)`. Its type and value supply a semantic Boolean function; they do not establish a recursive procedure, uniform program taking generator descriptions, or effective MOP implementation. No inference from pointwise classical decidability to computational uniformity is made. The imported stable-approximate reduction's conclusion is semantic inferrability.

**Strength and boundaries:** for Nat, the strong-condition equivalence matches the source support content. The conclusion allows the eventual support to include training examples and to omit finitely many target elements; it need not equal K or be the same across different presentations. This matches literal Definition 3.2, which has no freshness clause. Infinite targets prevent empty eventual support. There is no particular co-singleton counterexample, counterpresentation, detection of the stabilization time, or quantitative error bound. Arbitrary semantic functions are covered in the negative implication, while effective positive production remains outside the formal statement.

## T4: literal stable exact breadth obstruction

**Target:** `GenLimit.BreadthCharacterizations.Results.theorem_3_15_literal_exact_inconsistent`, Overview.lean:57. Native counterpart: StabilityGap.lean:72.

```lean
[Countable α] (F : Q.LanguageFamily α)
(hInfinite : ∀ i, (F i).Infinite) :
¬ ∃ G, B.IsStableGenerator G F ∧ B.IsExactBreadthGenerator G F
```

**Source comparison:** Theorem 3.15, p. 12, lists a positive stable-exact equivalence with the strong condition. Literal Definition 3.1, p. 9, says K\S. Definition 3.14, p. 12, says eventually constant supports. Combining precisely those definitions creates the conflict identified by this target: a fixed nonempty subset of K eventually contains an element subsequently observed, while exact freshness then excludes it. This is a statement-level compatibility analysis, not verification of the Lean proof.

**Correspondence:** materially different from the positive exact arm of Theorem 3.15. Lean quantifies over every family of infinite languages and concludes nonexistence without any failure of the strong condition. For a constant family with value Nat, the strong condition holds with empty tell-tales, so this cannot be the same assertion as the source's positive arm under the same literal predicates. It is stronger negative information, not a weakened positive theorem.

However, p. 17 footnote 3 expressly switches to a version allowing training examples in exact support. That source convention must not be omitted when evaluating the discrepancy. Under it, the relevant exact predicate is whole-target support, examined in T5; T4 is then a diagnostic about a different literal convention. Stage 2 does not adjudicate whether a source correction, formalization correction, or scope explanation is the final appropriate resolution.

**Strength and boundaries:** all semantic functions are excluded, not only computable generators. The argument requires fair complete presentations; arbitrary pauses from repetitions do not avoid eventual observation of a fixed target member. No finite tell-tale hypothesis, named difficult family, rate, or executable adversary is supplied. Countability supports the intended presentation setting; impossible infinitude premises are vacuous. The result says the joint eventual properties are impossible, not that stability alone or exact generation alone is impossible. Whole-target/exact existential equivalence after restoring/removing observations does not preserve stability of the original G.

## T5: stable whole-target characterization

**Target:** `GenLimit.BreadthCharacterizations.Results.theorem_3_15_corrected_wholeTarget_semantic`, Overview.lean:68. Native counterpart: CorrectedStability.lean:68.

```lean
[Nonempty α] [Countable α] (F : Q.LanguageFamily α)
(hInfinite : ∀ i, (F i).Infinite) :
(∃ G, B.IsWholeTargetGenerator G F ∧ B.IsStableGenerator G F)
  ↔ A.ConditionTwo F
```

**Source:** stable exact arm interpreted under Remark 4.4 and footnote 3, p. 17; Theorem 3.15, p. 12; Theorem 4.5, p. 17. Lean explicitly requires S(t)=K at every sufficiently late t, including observations. The same G also satisfies a separately quantified stability predicate. Whole-target correctness entails stability, but the conjunction remains part of the actual type.

**Correspondence:** exact/equivalent for the source's explicitly discussed seen-support semantic convention, with a faithful generalization of the domain. Materially different from literal Definition 3.1 if detached from that convention. The source itself provides evidence for the alternative; the target's identifier is not evidence that the developer independently repaired the paper. No unconditional ordinary algorithmic equivalence follows.

The native `restoreObserved G` has value `G history ∪ historySet history`; `removeObserved G` subtracts that history set. ExactBreadth.lean:109,117,125 states whole-target/literal-exact conversions and existential equivalence. CorrectedStability.lean:27 defines stability after restoring observations; line 47 states exact generators have that property. These supplied statements carefully concern transformed generators. They do not say subtracting observations preserves stability, which would conflict with T4.

**Strength and boundaries:** as an existence characterization the strong condition agrees with the source's intended stable-exact family classification; as a per-generator predicate whole-target correctness differs from unseen correctness. It is not a substitute for identifying a computable tell-tale oracle, a sampler, or an effective learner. One family-dependent G must work across all complete presentations; it is not chosen after seeing the target. Empty or finite languages are excluded by the facade premise, even though some native supporting theorems have broader hypotheses. No named witness is designated by this existential, and there are no bounded convergence times or statistical rates.

## T6: literal stable infinite-coverage obstruction

**Target:** `GenLimit.BreadthCharacterizations.Results.proposition_8_10_literal_specification_inconsistent`, Overview.lean:80. Native counterpart: StabilityGap.lean:134.

```lean
[Countable α] (F : Q.LanguageFamily α)
(hInfinite : ∀ i, (F i).Infinite) :
¬ ∃ G, B.IsStableGenerator G F ∧ B.IsInfiniteCoverageGenerator G F
```

**Source:** Proposition 8.10, pp. 39-40, assumes finite closure dimension, access to its value and a VSI membership oracle, and promises stable infinite coverage after d+1 distinct observations. Definition 8.3, p. 36, requires target containment, disjointness from observations, and infinite output. Definition 8.8, p. 38, counts distinct finite witnesses with nonempty version space and finite intersection. Definition 8.9, p. 39, specifies membership in that intersection.

**Correspondence:** materially different. Lean supplies none of closure dimension, a dimension parameter, a VSI interface, a distinct-observation trigger, or a positive generator. It instead excludes stable infinite fresh coverage on every infinite family. Adding a finite-dimension premise to this negative statement would still not give the source positive conclusion. Its disjointness conjunct is decisive: a fixed infinite target subset is eventually observed member by member and cannot remain disjoint from all later samples.

The source's proof discussion on p. 40 says to freeze support to the VSI intersection. **Interpretation, not proof certification:** that explains a positive *seen-support* coverage idea, but does not reconcile it with literal Definition 8.3. Footnote 17 on p. 41 later permits seen strings for subsequent increasing-coverage discussion; it does not explicitly redefine Proposition 8.10. This remains a source-convention question for Stage 3. No relaxed stable-infinite-coverage positive counterpart appears in the native closure.

**Strength and boundaries:** T6 is a universal semantic obstruction, stronger than the particular negative example in Theorem 8.7 under literal freshness, but it does not establish the intended nontrivial stable/unstable separation using a relaxed coverage notion. The current output must be infinite; otherwise an empty fixed output would evade the conflict. Coverage need not be cofinite or exhaustive. The two thresholds may depend on presentation, but use the same G. No computation model, numerical rate, failure frequency, counterpresentation, or sample-complexity upper bound is encoded. Finite collections are not exempt from the literal negative statement merely because the source promises a positive result for them.

## Bidirectional component matrix and strength assessment

| Component | Source to Lean | Lean to source and classification |
|---|---|---|
| Target languages and data | Infinite languages on countable strings; complete enumerations with repetitions. | Arbitrary countable α in T1,T2,T4,T5,T6; Nat only in T3. Faithful generalization/specialization as stated, without claiming executable encodings. |
| Input and quantifiers | One family-level generator, all targets/texts, presentation-dependent eventual threshold. | Exact in all six. Ordered histories retain the paper's sequence information even when it writes sample-set notation. |
| Exact breadth | Equality with unseen remainder. | Exact in T1 and the predicate in T4; whole-target variant in T5 corresponds to p. 17's alternative. Stability cannot be transferred silently. |
| Approximate breadth | Target containment plus finite omissions; Definition 3.2 itself allows seen strings. | Exact predicate in T2,T3. T2 lacks necessity; T3 restricts the domain. |
| Infinite coverage | Three conjuncts including freshness; later discussion allows seen strings. | Exact literal predicate in T6, opposite conclusion to the positive proposition. Relaxed positive theory not represented. |
| Structural witnesses | `∀ i ∃ finite W ∀ competitor`, strong or weak difference condition. | Equivalent set predicates. Effective enumeration/selection is not represented. Empty witnesses and duplicate indices are permitted. |
| Output representation | Sets, enumerations, and distributions with specified supports; effective sampler/enumerator/membership assertions. | Facade only has sets. Imported exhaustive model genuinely has enumerations and past first outputs. No stochastic sampler or computational representation theorem. |
| Unambiguous/exhaustive breadth | Cardinal-distance minimizer; history-sensitive exhaustive condition. | Imported concrete definitions exist; exhaustive iff weak condition is fully stated semantically. Unstable unambiguous iff and stable exhaustive iff are absent. |
| Abstract lower bounds and metrics | Uniqueness/finite non-uniqueness for arbitrary properties; metric consequences. | No native abstract counterpart. Concrete exact necessity is narrower, not a general-property theorem. |
| Statistical setting | IID samples from “valid” P supported on K; indicator loss. Achievability has `∃G ∀P ∃C,c>0 ∀n`; lower bounds have `∀G ∃P ∃C,c>0` infinitely often; no-rate uses positive limsup expected loss. | No distributions, IID laws, loss expectations, rescaling constants, exponential rates, or limsup theorem in the closure. The edition defers the precise `Val`/nontriviality contract to prior work; exact full-support requirements remain indeterminate here. |
| Stable finite-dimension results | Known d, VSI access, d+1 distinct observations, stable positive output. | Entire parameter/access/bound component absent from T6 and native model. This is more than a missing facade wrapper. |
| Hallucination grids and increasing coverage | Figures 3-4, Definition 8.13, Proposition 8.14. | No general grid or increasing-coverage model; literal negatives do not fill relaxed positive cells. |

There is no single total strength ordering between the whole paper and the targets. Lean generalizes some domains and includes unrestricted semantic nonexistence. It omits effective positive refinements, multipart converse directions, and quantitative models. Calling every difference a weakening or every semantic theorem an algorithm would conceal these opposing changes.

## Native coverage versus facade omissions

The complete closure was inspected at declaration level: 425 declarations across 34 modules, including 81 in the ten P05 modules (umbrella included). Counts are a reproducibility aid, not mathematical coverage scores. The supplemental umbrella imports Overview and SemanticBoundary. Imported P00/P00A supplies semantic identification/tell-tales; P03 supplies support predicates and stable reductions; P04 supplies exhaustive generation and its characterization; support modules provide histories, presentations, enumeration, candidates, and stabilization.

The clearest **missing facade wrapper with native coverage** is `GenLimit.CharikarPabbaraju.theorem4_exhaustive_generation_characterization`, P04/ExhaustiveCharacterization.lean:712. Its type, under Countable α and infinite family members, is `ExhaustivelyGeneratable (Set.range F) ↔ WeakAngluinExistence (Set.range F)`. The defining exhaustive predicate includes finite current hallucinations and coverage by sample, finitely many prior first outputs, and current output range, matching Definition 4.2. `WeakAngluinExistence` uses finite tell-tales and finite proper-subset differences, so range-indexing is equivalent to the family formulation. This is a semantic counterpart of Theorem 4.3's exhaustive arm, not an absent native formalization. The algorithm value is noncomputable and does not supply Lemmas 7.5/7.7's access refinements.

Other native coverage outside the facade includes exact/whole-target conversions, named semantic generators, stable-unambiguous necessity over Nat with a distinct-language premise, and the integer co-singleton separation. These are partial or convention-qualified coverage, not six new facade targets. The imported unambiguous predicate's universal pairwise inequality agrees with strict minimization when competitors exist; the source's minimum over an empty competitor set needs a convention for a single distinct language.

**Genuine native model gaps within this closure** include abstract property criteria/metric consequences; statistical laws/losses/rates; computational oracle-program contracts; closure dimension/VSI and d+1 bounds; increasing coverage; and the full hallucination grids. **Missing result/bridge gaps** include approximate necessity, positive literal infinite-coverage packaging, unstable unambiguous characterization, stable exhaustive characterization, and named best-of-three guarantees. Some ingredients could support future derivations; absence of a supplied declaration does not claim logical nonderivability. Finite-language learning modules concern finite *targets*, not the finite *collections of infinite targets* of Corollary 8.11.

The supplemental `emptySupportAlgorithm` and its theorem `emptySupportAlgorithm_isLimitGenerator` explicitly expose a semantic boundary: the literal subset-only generation definition allows empty output. Companion statements exclude it from exact, approximate on infinite targets, and infinite coverage. This agrees with the literal source Definition 2.1 but does not formalize productive single-string generation. It must not be counted as a positive coverage theorem.

## Source issues and unresolved Stage 3 questions

1. **Stable fresh support versus positive stability claims.** Pages 9 and 12 together create a literal conflict for exact support; p. 17 footnote 3 supplies an explicit seen-support convention. T4 diagnoses the literal reading and T5 represents the alternative. For infinite coverage, pp. 36 and 39-40 have the analogous conflict, with a later p. 41 footnote rather than an explicit local change. Stage 3 should determine and document which source convention the intended claims use.
2. **Example 8.12's displayed witness.** Visual p. 40 says the support is N minus the first sample, independent of the observed value. For target an upper tail starting sufficiently above the bottom of N, this includes natural numbers outside that target. It also keeps later observed natural strings. This is evidence of a source witness/convention problem, not license to substitute a first-observation-dependent tail. The named source witness is not formalized.
3. **Theorem 5.3's final clause.** Visual p. 22 says no rate for *exact* breadth when the weak condition fails, despite the approximate-breadth title and preceding clauses. Literal and intended approximate conclusions must be distinguished. Neither statistical version is supplied in Lean.
4. **Hallucination-grid wording.** Figures 3-4 label the right column infinitely many hallucinations, and claim all countable collections there using whole-domain support. If K is the whole domain, that support has no hallucinations. Interpreting the column as unrestricted allowance resolves a different statement; the literal equality-to-infinity label does not. Clarification is needed before claiming grid fidelity.
5. **Metric and definitional boundaries.** Remark 3.11's finite set of optimizing languages need not, from its wording alone, consist of pairwise finitely differing languages, as required by Definition 3.9. The exact “valid distribution” and nontriviality conditions in Section 5 are not self-contained. Definition 2.1 permits empty support, unlike the productive motivation. These are source scope questions, not proof verdicts.
6. **Additional informal deductions.** On p. 37 the text says exhaustive generation implies approximate breadth “by definition,” although Definition 4.2 allows finite hallucinations while Definition 3.2 forbids them. This does not hold for the same generator without an additional transformation. On p. 41 a size-at-most-t postprocessing rule alone does not imply nested supports. These statements warrant source clarification, but their proofs are outside this audit.

## Stage 1 corrections and completion checklist

No dropped binder, conjunction, quantifier dependency, or decisive definition error was found in Stage 1's six reconstructions. Its core mathematical expansions are retained. Three contextual corrections are necessary after opening the source and full closure: α is the observation domain rather than necessarily the source's alphabet; “corrected whole-target” matches a convention the paper itself explicitly discusses; and facade completeness does not imply full-paper coverage, especially because exhaustive characterization already exists natively. Conversely, Stage 1's accurate identification of missing oracle/computability/rate content must remain in force; names and classical Boolean fields do not fill those gaps.

All six targets have independent source locations, direct Lean type/definition checks, quantifier/witness dependencies, hypotheses/conclusions, representation/access assessments, temporal guarantees, strength assessments, and boundary cases. All 57 numbered items, four figures, and substantive unnumbered headline consequences were inventoried. Missing wrappers, partial native results, missing semantic bridges, and missing models are distinguished. PDF page labels and decisive formulas were checked visually; all input checksums and source-index hashes matched. The report and run record are frozen after validation. Developer-explanation adjudication, theorem-proof correctness, fresh compilation, and human certification remain expressly outside Stage 2.
