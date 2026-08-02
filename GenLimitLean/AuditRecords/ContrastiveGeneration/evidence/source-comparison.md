# 28 — Paper28_ContrastiveIdentificationAndGeneration — Contrastive Identification and Generation in the Limit — Lean Faithfulness Audit

## 0. Executive verdict

**Overall verdict: the Lean development is substantially faithful to the paper's central *semantic* mathematics, but it is not a complete formal counterpart of the paper.** The exact contrastive-identification characterization, the qualitative and quantitative closure-dimension characterization, the non-uniform chain characterization, the defect-infimum identity, the co-singleton separation, and the corrupted incomparability witnesses all have strong statement-level counterparts. The main losses are coverage and access-model fidelity rather than obvious logical circularity.

The highest-risk conclusions are:

1. **The clean diamond theorem is only componentwise represented.** The Lean bundle proves several inclusions and two separating examples, but no target-scope theorem states the full strict diamond of Theorems 5.13–5.14. In particular, the general inclusion `CtrGen ⊆ TxtGen` and the strictness `TxtId ⊊ TxtGen` are not target-scope Lean results.
2. **The observation carrier is ordered in Lean.** The paper gives the learner unordered two-element sets. Lean identifiers and generators consume `Edge α` with visible `left` and `right` fields. Crossing and incidence are swap-invariant, and the uniform dimension counts unordered images, so the semantic existence results are transportable by a classical orientation choice; nevertheless, no theorem in the supplied bundle states that transport or enforces swap-invariance of learners.
3. **The general results are information-theoretic, and the paper's constructive contrast is not preserved.** All principal Lean learners/generators are arbitrary semantic functions; many are declared `noncomputable`. Most importantly, the paper calls the co-singleton absence-count method fully constructive and oracle-free (Appendix E.3, PDF p. 22), whereas Lean's `absenceCountIdentifier` chooses an arbitrary finite minimizer by classical choice and has no `Computable` theorem.
4. **The robustness headline is only partly represented.** `theorem_6_6` asserts the existence of one identifier working for every budget, but no theorem signature states that the named absence-count identifier is the witness; connecting them would require using the proof body, which this audit does not use. The broader overview claim that pairwise infinite defect gaps imply finite-corruption identification also has no numbered source theorem and no Lean counterpart.
5. **Finite-family geometry is incomplete.** The paper's family shared-presentation criterion (Proposition B.1), membership-pattern criterion (Proposition D.1), higher-order example (Example D.2), and confusability-complex interface are absent. Lean's Proposition 5.12 instead takes a shared stream and an exact finite intersection as supplied certificates.
6. **The punctured example is only partially represented.** Lean proves the punctured family is contrastively generatable and not text-identifiable, but does not state the paper's `CΔ(H)=∞` conclusion or formalize the displayed hollow witnesses of Example 5.7.
7. **The paper's Example 5.9 is under-specified as printed.** Merely assuming an infinite proper `A ⊊ X` does not ensure that the augmented supports have a common-negative point; the appendix proof adds disjoint infinite `A,B` and `X \ (A∪B) ≠ ∅` (PDF p. 18). Lean does not formalize the printed example and uses the punctured class as a different valid strictness witness.
8. **The sharp threshold has a boundary repair.** The paper says the sample complexity is `CΔ(H)+1`; Lean proves leastness only among *positive* thresholds. This avoids a real `d=0` interface ambiguity caused by Lean histories including the empty prefix.

No primary theorem literally assumes its own conclusion. The most important delegation risks are finite tell-tales, infinite safe closures, an eventual core, an increasing finite-dimension cover, a shared presentation, and an exact finite intersection: these are strong semantic certificates, but they are not tautological restatements of the requested conclusion.

## 1. Source and version identity

Only the following three local inputs were inspected:

- **Author paper:** `28-2605.06211v1.pdf`, title *Contrastive Identification and Generation in the Limit*, Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao, arXiv:2605.06211v1, dated 7 May 2026, 23 PDF pages. Verified SHA-256: `40af9564b2066c0c47840aaf66b28caf12e5848b1673153cfcd4c92d0de5bf2a`.
- **Lean bundle:** `28__Paper28_ContrastiveIdentificationAndGeneration__lean-source-bundle.txt`, repository snapshot commit `dfcd13534f9d51642a9f88904268e95454c88f7f`, 291603 bytes. Verified SHA-256: `875fbf9e86e337e82b8e09783d8e39672bb993564af10a4f4981f2cac80ba79d`.
- **Stage 1 reconstruction:** `28-contrastive-identification-and-generation-lean-statement-reconstruction.md`. Local SHA-256: `fa6f1310ba03200168d65a0927aa0c8ef12c50ee733a7ddd5f05fe32b08a1900`.

The PDF was rendered page by page and visually checked. Paper claims below are cited by theorem/definition/example number and PDF page. Lean evidence is restricted to declaration types and definition bodies needed to unfold those types. Comments, docstrings, declaration names, source paths, proof bodies, tactic scripts, and proof-local facts are not used to infer mathematical content. Source labels and bundle line numbers are provenance only.

## 2. Model and interface alignment before comparing theorems

### 2.1 Domain and class representation

The paper fixes a countably infinite example space `X={u₀,u₁,…}` and a countable extensional class `H ⊆ {0,1}^X` (Setting, PDF p. 5). Lean uses two interfaces:

- indexed families `F : ℕ → Set α` for identification;
- extensional classes `𝓗 : Set (Set α)` for generation and geometric closure.

For the identification theorems, `[Countable α] [Infinite α]` replaces the paper's fixed enumeration. A natural-indexed family can represent every **nonempty** countable extensional class up to repetitions, but it cannot represent the empty class. Repeated indices may denote the same support.

Lean convergence is syntactic at the index level:

```lean
def ContrastivelyIdentifiesFrom
    (I : ContrastiveIdentifier α)
    (F : GenLimit.Generic.LanguageFamily α)
    (z : ℕ) (stream : ℕ → Edge α) : Prop :=
  ∃ j, F j = F z ∧
    ∃ T, ∀ t, T ≤ t →
      contrastiveIdentifierOutput I stream t = j
```

Thus the limiting representative `j` may depend on the presentation, but its support must equal the target support. With duplicate indices this is slightly stronger than merely requiring every late guessed support to be correct, because Lean requires stabilization to one index. At the semantic level a canonical representative can be chosen classically, but no target-scope transport theorem states this quotient equivalence.

### 2.2 Unordered paper observations versus oriented Lean observations

The paper's contrastive datum is an unordered two-element subset `{x,y}` (Definitions 3.3 and 4.1, PDF pp. 5–6). Lean uses:

```lean
structure Edge (α : Type*) where
  left : α
  right : α
  ne : left ≠ right
```

and

```lean
def Crosses (h : Set α) (e : Edge α) : Prop :=
  (e.left ∈ h ∧ e.right ∉ h) ∨
    (e.right ∈ h ∧ e.left ∉ h)
```

`Crosses`, `CommonCrossing`, and `Incident` are invariant under swapping, and the closure-dimension development explicitly forgets orientation through `UnorderedEdge`. Nevertheless, `ContrastiveIdentifier` and `ContrastiveGenerator` receive the ordered fields. No declaration requires their output to be invariant under swapping each edge.

For *existence* results this is plausibly semantically equivalent: an unordered learner can forget orientation, and an oriented learner that succeeds for every orientation can be converted to an unordered learner by fixing one classical orientation per pair. That conversion is not stated in the supplied Lean interface, so orientation remains a representation assumption and a modest evidence gap rather than a demonstrated counterexample to correspondence.

### 2.3 Valid contrastive presentations

Paper Definition 3.3 requires every pair to satisfy XOR and every positive point to occur as an endpoint; negatives need not be covered and pairs may repeat (PDF p. 5). Lean states:

```lean
def IsContrastivePresentation
    (stream : ℕ → Edge α) (h : Set α) : Prop :=
  (∀ n, Crosses h (stream n)) ∧
    h ⊆ {x | ∃ n, Incident x (stream n)}
```

This preserves the one-sided positive coverage exactly. It does not require every crossing edge, every negative point, any frequency condition, or any stochastic sampling law.

### 2.4 Three different generation quantifier orders

The paper distinguishes ordinary generation in the limit from uniform and non-uniform distinct-edge thresholds. Lean faithfully keeps three separate interfaces:

1. **Ordinary stream-wise generation**

   `∃G, ∀h∈𝓗, ∀P, Valid(P,h) → ∃T(h,P), ∀t≥T, G(P≤t)∈h\Seen_t(P)`.

2. **Uniform distinct-edge threshold**

   `∃d ∃G, ∀h∈𝓗, ∀ finite crossing histories E, d≤|E_distinct| → correct and unseen`.

3. **Target-dependent distinct-edge threshold**

   `∃G, ∀h∈𝓗, ∃d_h, ∀ finite crossing histories E of h, d_h≤|E_distinct| → correct and unseen`.

The ordinary threshold may depend on both target and presentation. The non-uniform distinct-edge threshold depends on the target but is uniform over all crossing histories of that target. These notions are not interchangeable.

Both paper and Lean define novelty only relative to **observed input points**. Neither principal conclusion requires outputs to be distinct from earlier generated outputs.

### 2.5 Corruption quantifiers

Lean's corrupted text and contrastive presentations count bad **occurrences** and preserve exact positive-side coverage:

```lean
def IsKCorruptedTextPresentation
    (k : ℕ) (stream : Generic.Stream α) (h : Set α) : Prop :=
  {n : ℕ | stream n ∉ h}.Finite ∧
    {n : ℕ | stream n ∉ h}.ncard ≤ k ∧
    h ⊆ Set.range stream
```

```lean
def IsKCorruptedContrastivePresentation
    (k : ℕ) (stream : ℕ → Edge α) (h : Set α) : Prop :=
  {n : ℕ | ¬Crosses h (stream n)}.Finite ∧
    {n : ℕ | ¬Crosses h (stream n)}.ncard ≤ k ∧
    h ⊆ {x | ∃ n, Incident x (stream n)}
```

`KContrastivelyIdentifiable k F` has `∃I` after fixing `k`, so the learner may depend on a known budget. `FinitelyCorruptionContrastivelyIdentifiable F` has `∃I ∀k`, so one identifier must work for every finite budget. This matches Definition 6.1 (PDF p. 10).

### 2.6 Access and effectivity baseline

The paper explicitly describes Theorems 4.7 and 5.5 as information-theoretic (Remarks 4.8 and 5.6, PDF pp. 7–8), and Appendix E.3 discusses consistency, closure-membership, ERM, tell-tale, and dimension oracles (PDF p. 22). Lean's top-level interfaces are even more semantic:

- no membership oracle is passed to general identifiers or generators;
- no class encoding, consistency decider, closure-membership decider, ERM oracle, runtime, sample-processing complexity, or Turing-computability predicate appears in Paper28 theorem conclusions;
- many constructions are explicitly `noncomputable` and use classical choice;
- countability typeclasses provide set-theoretic enumerations, not computable enumerators.

The co-singleton paper algorithm is the notable exception on the paper side: Appendix E.3 calls it fully constructive and oracle-free. That stronger claim is not certified in Lean.

## 3. Theorem correspondence matrix

The verdict vocabulary is exactly the one requested. `Difficulty` compares the statement/interface burden, not the length of the Lean proof.

### 3.1 Preliminaries and imported background

| Paper result | Lean counterpart | Correspondence verdict | Difficulty verdict | Main delta |
|---|---|---:|---:|---|
| Definition 3.1, UUS (PDF p. 5) | Imported dependency `GenLimit.LiRamanTewari.UUS`; Paper28 uses explicit infinitude hypotheses in hierarchy declarations | Exact / formally equivalent | Preserved | Dependency/background only, not a Paper28 declaration. |
| Definition 3.2, positive version space and closure (PDF p. 5) | Imported `versionSpace`, `commonCore`, `closure` | Faithful specialization | Preserved | Dependency uses finite sets and `Option` for `⊥`; Paper28's contrastive closure uses `∅` plus a nonempty-version guard. |
| Definition 3.3, text presentation (PDF p. 5) | Imported `Generic.Presents`, `sample` | Faithful specialization | Preserved | Exact range presentation and finite-prefix sample; dependency/background only. |
| Definition 3.3, informant presentation (PDF p. 5) | No labeled full-domain presentation in the Paper28 target scope | Not represented in Lean | Indeterminate | A labeled-enumeration interface exists only in unrelated imported Paper08 background and is not the paper's `InfId` interface. |
| Definition 3.3, contrastive presentation (PDF p. 5) | `IsContrastivePresentation`, `Edge`, `Crosses`, `Incident` (`Geometry.lean`, bundle lines 558–689) | Faithful specialization | Indeterminate | Ordered carrier instead of unordered set; predicates are swap-invariant, learner invariance is not stated. |
| Definition 3.4, text/contrastive identification and generation (PDF p. 5) | `TextIdentifiable`, `ContrastivelyIdentifiesFrom`, `ContrastivelyIdentifiable`, `GeneratesFrom`, `ContrastivelyGeneratable` | Faithful specialization | Preserved | Indexed outputs may use duplicate representations; stable representative may depend on the stream; functions are total on invalid histories. |
| Definition 3.4, informant identification branch (PDF p. 5) | No Paper28 identifier or convergence predicate for informants | Not represented in Lean | Indeterminate | This is why Theorem 3.5 is also absent. |
| Theorem 3.5, all countable classes are informant-identifiable (PDF p. 5) | No target-scope or imported theorem in the supplied bundle states this result | Not represented in Lean | Indeterminate | Informant identification is not part of the Paper28 formal interface. |
| Theorem 3.6, Angluin tell-tale characterization (PDF p. 5) | Imported `ConditionTwo`, `identifiable_of_conditionTwo`, and `conditionTwo_of_identifiable` | Faithful specialization | Preserved | Semantic indexed formulation with possible repeated indices; dependency/background only. |
| Theorem 3.7, universal text generation for countable UUS classes (PDF p. 5) | No target-scope theorem states ordinary text-generation universality; imported Paper02 has a stronger target-dependent-threshold result but no Paper28 bridge to `TxtGen` | Not represented in Lean | Indeterminate | The literal paper theorem is not exposed at the relevant interface, preventing a complete target-scope Theorem 5.13. |

### 3.2 Identification geometry and characterization

| Paper result | Lean counterpart | Correspondence verdict | Difficulty verdict | Main delta |
|---|---|---:|---:|---|
| Definition 4.1, non-eliminability (PDF p. 6) | `NotEliminableFrom` (`Geometry.lean:L689`) | Faithful generalization | Preserved | Lean drops distinct/proper hypotheses and defines only the existential non-eliminable direction. |
| Proposition 4.2 (PDF p. 6) | `proposition_4_2` (`Geometry.lean:L746`) | Faithful generalization | Preserved | Lean receives a positive point and an enumeration covering `h`; paper obtains them from standing properness/countability. |
| Theorem 4.3, region equivalence (PDF p. 6) | `theorem_4_3` (`Geometry.lean:L625`) | Faithful generalization | Strengthened / harder | Lean proves the displayed equivalence for arbitrary sets, without distinctness, properness, or countability. |
| Theorem 4.3, explicit N1/N2/N3 regime classification (PDF p. 6) | No declaration states the three named regimes | Not represented in Lean | Indeterminate | The core region iff is present, but the case classification is not a theorem type. |
| Lemma 4.4, shared-presentation iff union coverage (PDF p. 6) | `lemma_4_4` (`Geometry.lean:L825`) | Faithful generalization | Preserved | Explicit union point and enumeration are supplied. |
| Lemma 4.4, “mutual non-eliminability implies confusability” (PDF p. 6) | No single theorem states this clause; related types are `proposition_4_2`, `lemma_4_4`, and `commonPresentation_for_noncontained` | Related but materially different | Preserved | The clause is only reconstructible by composing bridges under standing assumptions. |
| Definition 4.5, overlapping cover (PDF p. 7) | `OverlappingCover` (`IdentificationGeometry.lean:L880`) | Exact / formally equivalent | Preserved | None beyond set/hypothesis representation. |
| Lemma 4.6 inclusion (PDF p. 7) | `lemma_4_6_inclusion` (`IdentifierCharacterization.lean:L3355`) | Faithful specialization | Preserved | Indexed family, countable/infinite typeclasses, semantic noncomputable simulation. |
| Lemma 4.6 strictness on UUS classes (PDF p. 7) | Disjoint witness gives `TextIdentifiable` and `¬ContrastivelyGeneratable`; a separate theorem gives `CtrId→CtrGen` | Related but materially different | Weakened / easier | No declaration directly states `TextIdentifiable ∧ ¬ContrastivelyIdentifiable`; strictness follows only by composition. |
| Theorem 4.7, conditions (i)↔(ii) (PDF p. 7) | `theorem_4_7_identifier_equivalence` (`IdentifierCharacterization.lean:L3755`) | Faithful specialization | Preserved | Geometric coverage is used instead of literal `NotEliminableFrom`, but Proposition 4.2 restores equivalence under the theorem hypotheses. |
| Theorem 4.7, conditions (ii)↔(iii) (PDF p. 7) | `theorem_4_7_geometric_equivalence` (`IdentificationGeometry.lean:L974`) | Faithful generalization | Strengthened / harder | Lean proves the pure class geometry for arbitrary extensional classes. |
| Theorem 4.7, conditions (i)↔(iii) (PDF p. 7) | `theorem_4_7` (`IdentifierCharacterization.lean:L3776`) | Faithful specialization | Preserved | Nonempty indexed countable class; ordered edge representation; otherwise same quantifiers and conditions. |
| Remark 4.8, information-theoretic/non-effective construction (PDF p. 7) | `chosenTellTale`, `contrastiveTellTaleLearner`, and top-level semantic existence theorems | Faithful specialization | Preserved | Lean makes noncomputability explicit and proves no effective/oracle implementation theorem. |

### 3.3 Generation, closure, cores, and hierarchy

| Paper result | Lean counterpart | Correspondence verdict | Difficulty verdict | Main delta |
|---|---|---:|---:|---|
| Definition 5.1, edge version space/closure (PDF p. 8) | `unorderedVersionSpace`, `unorderedClosure`, plus history-based `edgeVersionSpace`, `edgeClosure` | Related but materially different | Preserved | Paper's empty-version value is `⊥`; Lean uses `∅` and separately records nonemptiness. Relevant theorems guard the case. |
| Definition 5.2, uniform threshold (PDF p. 8) | `UniformlyContrastivelyGeneratesAt`, `...GeneratableAt` (`ClosureDimension.lean:L3986–3999`) | Faithful generalization | Preserved | Finite crossing histories replace stream prefixes; equivalent for positive thresholds, with an empty-prefix boundary at threshold zero. |
| Definition 5.2, target-dependent threshold (PDF p. 8) | `NonuniformlyContrastivelyGenerates`, `...Generatable` (`NonuniformClosure.lean:L5036–5048`) | Faithful generalization | Preserved | Same `∃G ∀h ∃d_h ∀history` order; finite histories replace stream prefixes and Lean admits broader, sometimes vacuous, target classes. |
| Definition 5.3, hollow sets and `CΔ` (PDF p. 8) | `IsContrastivelyHollow`, `ContrastiveClosureDimensionAtMost`, `...Equals` | Faithful generalization | Preserved | Extended supremum is represented by upper-bound and least-bound predicates. |
| Theorem 5.4 qualitative iff (PDF p. 8) | `theorem_5_4` (`ClosureDimension.lean:L4228`) | Faithful generalization | Strengthened / harder | Lean allows arbitrary extensional classes, not only countable classes in the paper's setting. |
| Theorem 5.4 exact `d+1` equivalence (PDF pp. 8,17) | `theorem_5_4_quantitative` (`ClosureDimension.lean:L4215`) | Faithful generalization | Strengthened / harder | Exact finite-bound biconditional for every `d`; no countability/properness premise. |
| Theorem 5.4 sharp least sample complexity (PDF pp. 8,17) | `theorem_5_4_sharp_sample_complexity` (`ClosureDimension.lean:L4245`) | Faithful specialization | Preserved | Leastness is restricted to positive thresholds, repairing the `d=0` convention. |
| Theorem 5.5 chain characterization (PDF pp. 8,17) | `theorem_5_5`, plus separate necessity/sufficiency directions (`NonuniformClosure.lean:L5098–5274`) | Faithful generalization | Strengthened / harder | Arbitrary extensional class; bounds are selected noncomputably from existence proofs; exact chain quantifiers retained. |
| Remark 5.6, chain and dimensions as information-theoretic inputs (PDF p. 8) | `theorem_5_5_sufficiency`, `selectedClosureBound`, `nonuniformClosureGenerator` | Related but materially different | Weakened / easier | Lean takes a cover and proofs that bounds exist, then chooses numerical bounds classically; it does not expose the paper's bounds-as-runtime-input interface. |
| Example 5.7, punctured class is in `CtrGen` (PDF p. 8) | `punctured_contrastivelyGeneratable` and `theorem_5_13_5_14_punctured_witness` | Faithful specialization | Preserved | `A` is instantiated as the even numbers. |
| Example 5.7, `CΔ(H)=∞` via hollow `E_n` (PDF p. 8) | No declaration states infinite contrastive closure dimension for the punctured class | Not represented in Lean | Indeterminate | The stated reason ordinary generation exceeds the dimension theory is absent. |
| Proposition 5.8, safe-core sufficiency (PDF pp. 9,17) | `proposition_5_8` (`GenerationCores.lean:L1126`) | Faithful generalization | Preserved | The proposition has the same eventual conclusion in broader semantic scope; separate helper interfaces certify an all-time named safe output. |
| Example 5.9, augmented-support class (PDF p. 9) | No corresponding target-scope class or theorem | Not represented in Lean | Indeterminate | Printed source assumptions are insufficient; appendix uses stronger sets. |
| Definition 5.10, eventual core (PDF p. 9) | `IsEventualCore` (`GenerationCores.lean:L1141`) | Exact / formally equivalent | Preserved | None. |
| Proposition 5.11, eventual-core sufficiency (PDF pp. 9,17) | `proposition_5_11` (`GenerationCores.lean:L1201`) | Faithful generalization | Weakened / easier | Lean drops countability/properness; targets without valid presentations can make the conclusion vacuous. |
| Proposition B.1, finite-family shared-presentation criterion (PDF p. 18) | No finite-family coverage criterion | Not represented in Lean | Indeterminate | Only the two-hypothesis criterion is formalized. |
| Proposition 5.12, finite-family obstruction (PDF pp. 9,18) | `proposition_5_12` (`Hierarchy.lean:L5551`) | Faithful generalization | Weakened / easier | Lean receives the shared stream and exact finite intersection as explicit certificates and allows singleton finite-support families. |
| Theorem 5.13, full strict hierarchy chain (PDF pp. 9,18) | Several inclusion and witness declarations, but no full theorem | Related but materially different | Weakened / easier | `CtrGen⊆TxtGen` and `TxtId⊊TxtGen` are missing; strictness claims are not assembled. |
| Theorem 5.14, `CtrGen` and `TxtId` incomparable (PDF pp. 10,18) | Punctured and disjoint witness theorems | Faithful specialization | Preserved | Concrete arithmetic instances replace arbitrary named sets. |
| Proposition D.1 and Example D.2, higher-order membership patterns (PDF pp. 20–21) | No corresponding declarations | Not represented in Lean | Indeterminate | Pairwise-insufficiency example and criterion are absent. |

### 3.4 Corruption and robustness

| Paper result | Lean counterpart | Correspondence verdict | Difficulty verdict | Main delta |
|---|---|---:|---:|---|
| Definition 6.1, corrupted presentations and `k`/`Fin` identification (PDF p. 10) | `IsKCorruptedTextPresentation`, `IsKCorruptedContrastivePresentation`, `KTextIdentifiable`, `KContrastivelyIdentifiable`, `FinitelyCorruptionContrastivelyIdentifiable` | Faithful specialization | Preserved | Occurrence counting and budget order are exact; contrastive observations use the oriented Lean carrier and classes are indexed. |
| Definition 6.2, defect set/number (PDF p. 10) | `positiveDefectSet`, `defectNumber` (`DefectInfimum.lean:L7145–7149`) | Exact / formally equivalent | Preserved | Lean uses extended naturals `ℕ∞`. |
| Proposition 6.3, exact infimum (PDF pp. 10,18–19) | `proposition_6_3_defect_eq_forced_wrong_cut_infimum` (`DefectInfimum.lean:L7573`) | Faithful generalization | Strengthened / harder | Lean drops the paper's infinite-domain restriction and states a literal `sInf` equality in `ℕ∞`. |
| Proposition 6.3, zero-defect/non-eliminability clause (PDF pp. 10,18) | `proposition_6_3_notEliminable_iff_defectNumber_zero` (`DefectInfimum.lean:L7606`) | Faithful generalization | Preserved | Distinctness and properness of `g` are retained as parameters although not needed by the displayed conclusion. |
| Headline claim: pairwise infinite defects imply finite-corruption identification (PDF p. 3) | No general target-scope theorem | Not represented in Lean | Indeterminate | Lean proves the defect identity and the co-singleton instance, not the advertised general sufficient criterion. |
| Definition 6.4, co-singleton class (PDF p. 10) | `coSingletonSupport`, `coSingletonFamily` | Faithful specialization | Preserved | Domain specialized to `ℕ`. |
| Theorem 6.5, text fragility (PDF pp. 10–11) | `theorem_6_5` (`CorruptedPresentations.lean:L6049`) | Faithful specialization | Preserved | Same identity stream argument at the statement level; semantic identifier. |
| Algorithm 1, fixed-enumeration absence minimizer (PDF p. 11) | `absenceCount`, `seenEndpoints`, `absenceCountIdentifier` | Related but materially different | Weakened / easier | Lean chooses an arbitrary minimizer by classical choice; no fixed-enumeration tie-break or computability theorem. |
| Theorem 6.6, `Hco∈Fin-CtrId` (PDF pp. 11,19) | `theorem_6_6` (`AbsenceCount.lean:L6482`) | Faithful specialization | Preserved | Exact `∃I∀k` semantic membership; theorem type does not name the absence-count identifier. |
| Example 6.7, six-prefix counts and minimizer (PDF p. 11) | `example_6_7_absence_counts`, `example_6_7_unique_minimizer` | Faithful specialization | Strengthened / harder | Lean also states uniqueness among all seen endpoints. |
| Example 6.7, divergence along every extension (PDF p. 11) | No theorem states the displayed extension-asymptotic claim | Not represented in Lean | Indeterminate | General helper lemmas imply related behavior under valid corrupted presentations, but no example-specific theorem states it. |
| Theorem 6.8, corrupted incomparability (PDF pp. 11,19–20) | `theorem_6_8` and block/co-singleton component theorems | Faithful specialization | Preserved | Reverse witness depends on `k`, as in the paper; arithmetic coding over `ℕ`. |
| Definition E.1 and Remark E.2, corrupted generation and identify-then-generate (PDF p. 21) | No target-scope definitions or theorem | Not represented in Lean | Indeterminate | `k-CtrGen`, `Fin-CtrGen`, and the co-singleton lift are absent. |
| Definition E.3, random contrastive presentations (PDF p. 22) | No probability/randomness declarations | Not represented in Lean | Indeterminate | No i.i.d. model, almost-sure coverage, phase transition, spectral method, or rate theorem. |
| Appendix E.3, absence-count is fully constructive and oracle-free (PDF p. 22) | Noncomputable `absenceCountIdentifier`; no `Computable` result | Related but materially different | Weakened / easier | The semantic theorem does not preserve the paper's constructive classification. |


### 3.5 Foundational numbered statements in quantified form

The Section 3 results are imported background rather than new Paper 28 claims, but they are numbered in the supplied paper and are used in the hierarchy. Their exact coverage is therefore recorded here.

**Definition 3.1 (UUS).** The paper requires

`∀h∈H, |supp(h)|=∞`

(Definition 3.1, PDF p. 5). The imported Lean predicate is

```lean
def UUS (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → L.Infinite
```

(`Paper02_GenerationThroughTheLensOfLearningTheory/Definitions.lean:L4294`, dependency/background). This is the same extensional infinitude condition.

**Correspondence verdict:** **Exact / formally equivalent**.  
**Difficulty verdict:** **Preserved**.

**Definition 3.2 (positive version space and closure).** The paper takes a finite positive sample, retains all class members containing it, and intersects their supports, returning `⊥` if the version space is empty (Definition 3.2, PDF p. 5). Imported Lean uses a `Finset`, the same containment version space, and `Option (Set α)` to distinguish `none` from a nonempty-version closure. This is a faithful finite-set encoding and is background only.

**Correspondence verdict:** **Faithful specialization**.  
**Difficulty verdict:** **Preserved**.

**Definitions 3.3–3.4 (presentations and learning).** For text data, Lean's `Presents stream L := range stream = L` and finite-prefix sample match the paper. For contrastive data, `IsContrastivePresentation` preserves XOR and positive-side coverage but exposes an orientation. Paper28's text and contrastive learners consume only finite prefixes and have the same eventual quantifier order. The informant branch is absent from the target scope.

**Text/contrastive correspondence verdict:** **Faithful specialization**.  
**Text/contrastive difficulty verdict:** **Preserved**.

**Informant correspondence verdict:** **Not represented in Lean**.  
**Informant difficulty verdict:** **Indeterminate**.

**Theorem 3.5 (Gold informant identification).** The paper quantifies over every countable class on the countably infinite domain and concludes existence of an identifier succeeding on every full labeled presentation (Theorem 3.5, PDF p. 5). No Paper28 declaration defines this informant learner or states the theorem.

**Correspondence verdict:** **Not represented in Lean**.  
**Difficulty verdict:** **Indeterminate**.

**Theorem 3.6 (semantic tell-tale characterization).** In the paper's extensional notation,

`H∈TxtId ↔ ∀g∈H, ∃ finite T_g⊆supp(g), ∀f∈H, T_g⊆supp(f) ∧ supp(f)⊊supp(g) is impossible`

(Theorem 3.6, PDF p. 5). For an indexed family, imported Lean uses

```lean
def ConditionTwo (C : Generic.LanguageFamily α) : Prop :=
  ∀ i, ∃ T : Finset α,
    (↑T : Set α) ⊆ C i ∧
      ∀ j, (↑T : Set α) ⊆ C j → C j ⊆ C i → C i ⊆ C j
```

and Paper28's

```lean
def TextIdentifiable (F : Generic.LanguageFamily α) : Prop :=
  ∃ M : GenLimit.Angluin.SemanticIdentifier α,
    GenLimit.Angluin.SemanticallyIdentifies M F
```

The imported directions are `ConditionTwo C → IdentifiableInLimit C` and, under `[Nonempty α] [Countable α]`, `IdentifiableInLimit C → ConditionTwo C`. The latter handles empty indexed languages explicitly. Repeated indices are allowed, so equality is support equality rather than index equality. No recursive/effective conclusion is asserted.

**Correspondence verdict:** **Faithful specialization**.  
**Difficulty verdict:** **Preserved**.

**Theorem 3.7 (universal text generation).** The paper states

`∀ countable H, UUS(H) → H∈TxtGen`

(Theorem 3.7, PDF p. 5). The supplied dependencies contain

```lean
theorem countable_classes_are_nonuniformly_generatable
    [Nonempty α] [Countable α]
    {H : LanguageClass α} (hUUS : UUS H)
    (hCountable : H.Countable) :
    NonuniformlyGeneratable H
```

(`Paper02_GenerationThroughTheLensOfLearningTheory/NonuniformCharacterization.lean:L4974`). This is a stronger target-dependent distinct-sample-threshold property, but no Paper28 declaration converts it to the ordinary `GeneratableInLimit`/`TxtGen` interface or packages it into Theorem 5.13. Under the audit's primary-scope rule, the literal Paper 28 background theorem is therefore not represented as a target-scope result.

**Correspondence verdict:** **Not represented in Lean**.  
**Difficulty verdict:** **Indeterminate**.

## 4. Detailed identification comparison

### 4.1 Definition 4.1 and Proposition 4.2: pairwise eliminability

**Paper claim.** For distinct proper nontrivial `h,g`, `g` is not eliminable from `h` exactly when there exists a valid contrastive presentation of `h` using only edges crossing `g`; Proposition 4.2 says this is equivalent to `supp(h) ⊆ V(Γ(h,g))` (Definition 4.1 and Proposition 4.2, PDF p. 6). The paper's standing setting supplies a countably infinite `X`, so the reverse direction may enumerate `supp(h)`.

**Lean content.** The existential notion unfolds to

```lean
def NotEliminableFrom (g h : Set α) : Prop :=
  ∃ stream : ℕ → Edge α,
    IsContrastivePresentation stream h ∧
      ∀ n, Crosses g (stream n)
```

and the theorem type is

```lean
theorem proposition_4_2
    {h g : Set α} (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α) (henum : h ⊆ Set.range enumeration) :
    NotEliminableFrom g h ↔ h ⊆ commonVertices h g
```

(`Geometry.lean`, bundle lines 689 and 746).

The reverse direction's local representation assumptions are explicit: a positive fallback point and a sequence covering `h` are arguments. No membership oracle, decidability, or computability is supplied. Pointwise incident edges are available only through the geometric coverage proposition and classical existence.

The paper's distinctness and properness of `g` are absent, so Lean is more general. Nonemptiness of `h` is not absent: it is encoded by `x₀∈h`. Under the paper's setting, `x₀` and `enumeration` are derivable and do not alter the mathematical equivalence.

**Correspondence verdict:** **Faithful generalization**.  
**Difficulty verdict:** **Preserved**.

### 4.2 Theorem 4.3: four-region geometry

**Paper claim.** For distinct proper nontrivial `h,g`, with

`A=h∩g`, `B=h\g`, `C=g\h`, `D=X\(h∪g)`, the paper states

`g` not eliminable from `h` iff `(A≠∅⇒D≠∅) ∧ (B≠∅⇒C≠∅)`, and then classifies non-eliminability into exactly three support regimes: proper superset, disjoint incomparable, and intersecting non-covering incomparable (Theorem 4.3, PDF p. 6; proof repeated on PDF p. 15).

**Lean content.** The displayed theorem is

```lean
theorem theorem_4_3
    (h g : Set α) :
    h ⊆ commonVertices h g ↔
      ((bothPositive h g).Nonempty → (bothNegative h g).Nonempty) ∧
      ((hOnly h g).Nonempty → (gOnly h g).Nonempty)
```

(`Geometry.lean:L625`). The region definitions are exactly `h∩g`, `h\g`, `g\h`, and `(h∪g)ᶜ`.

The theorem does not mention `NotEliminableFrom`; Proposition 4.2 is the bridge. It also does not state the N1/N2/N3 case disjunction. Consequently:

- the **core region equivalence** is stronger in scope than the paper because it applies to arbitrary sets, including empty and universal supports;
- the **named three-regime classification** is not a Lean declaration.

The implications on the right can be vacuous when `A` or `B` is empty. This mirrors the correct set-theoretic boundary behavior; it is not circular.

**Core-equivalence correspondence verdict:** **Faithful generalization**.  
**Core-equivalence difficulty verdict:** **Strengthened / harder**.

**Three-regime correspondence verdict:** **Not represented in Lean**.  
**Three-regime difficulty verdict:** **Indeterminate**.

### 4.3 Lemma 4.4: shared presentations

**Paper claim.** Two targets admit one common contrastive presentation iff their union is covered by the common crossing graph; mutual non-eliminability then implies confusability (Lemma 4.4, PDF p. 6; proof on PDF p. 15).

**Lean content.** A common presentation is

```lean
def AdmitCommonPresentation (h g : Set α) : Prop :=
  ∃ stream : ℕ → Edge α,
    IsContrastivePresentation stream h ∧
      IsContrastivePresentation stream g
```

and Lean states

```lean
theorem lemma_4_4
    {h g : Set α} (x₀ : α) (hx₀ : x₀ ∈ h ∪ g)
    (enumeration : ℕ → α)
    (henum : h ∪ g ⊆ Set.range enumeration) :
    AdmitCommonPresentation h g ↔
      h ∪ g ⊆ commonVertices h g
```

(`Geometry.lean:L768,L825`). The point and enumeration of the union are supplied. The final “mutual non-eliminability” sentence is not itself a theorem type; obtaining it requires two Proposition 4.2 bridges plus Lemma 4.4, or the more specialized helper `commonPresentation_for_noncontained` used in the characterization necessity direction.

**Iff correspondence verdict:** **Faithful generalization**.  
**Iff difficulty verdict:** **Preserved**.

**Final-clause correspondence verdict:** **Related but materially different**.  
**Final-clause difficulty verdict:** **Preserved**.

### 4.4 Lemma 4.6: `CtrId ⊆ TxtId`

**Paper quantifiers.** On a class of proper nontrivial hypotheses, every contrastive identifier yields a text identifier; moreover the inclusion is strict even when every support is infinite (Lemma 4.6, PDF p. 7).

**Lean inclusion.** The exact type is

```lean
theorem lemma_4_6_inclusion
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F → TextIdentifiable F
```

(`IdentifierCharacterization.lean:L3355`), where

```lean
def AllProperNontrivial (F : ℕ → Set α) : Prop :=
  ∀ i, (F i).Nonempty ∧ (F i)ᶜ.Nonempty
```

and, after unfolding, the implication is

`(∃I, ∀z∀P, ValidCtr(P,F z) → ∃j, F j=F z ∧ ∃T∀t≥T, I(P≤t)=j)`

`→`

`(∃M, ∀z∀text, range(text)=F z → ∃j, F j=F z ∧ ∃T∀t≥T, M(text≤t)=j)`.

The paper's fixed least-element enumeration is replaced by a set-theoretically selected surjection from countability. No effective enumeration is present. The Lean learner is total on invalid finite histories, so early synthetic histories may be invalid without making the function ill-typed.

**Inclusion correspondence verdict:** **Faithful specialization**.  
**Inclusion difficulty verdict:** **Preserved**.

**Strictness.** Lean's disjoint family theorem gives

```lean
TextIdentifiable disjointFamily ∧
  GeneratableInLimit (Set.range disjointFamily) ∧
  ¬ContrastivelyGeneratable (Set.range disjointFamily)
```

and a separate theorem gives `ContrastivelyIdentifiable F → ContrastivelyGeneratable (Set.range F)` under infinite supports. Those types jointly imply the disjoint family is not contrastively identifiable, but no declaration states the strict inclusion or even the direct conjunction `TextIdentifiable disjointFamily ∧ ¬ContrastivelyIdentifiable disjointFamily`.

**Strictness correspondence verdict:** **Related but materially different**.  
**Strictness difficulty verdict:** **Weakened / easier**.

### 4.5 Theorem 4.7: exact characterization

**Paper statement.** For a countable class `H` of proper nontrivial hypotheses, the following are equivalent (Theorem 4.7, PDF p. 7):

1. `H∈CtrId`;
2. `H∈TxtId` and contrastive non-eliminability is contained in the positive-data proper-superset relation;
3. `H∈TxtId` and every incomparable pair has nonempty intersection and union `X`.

The learner is information-theoretic and consumes finite tell-tales; no effective construction is claimed (Remark 4.8, PDF p. 7).

**Lean condition definitions.** Lean writes

```lean
def NonEliminabilityContained (𝓗 : Set (Set α)) : Prop :=
  ∀ h ∈ 𝓗, ∀ g ∈ 𝓗,
    h ⊆ commonVertices h g → h ⊆ g
```

and

```lean
def IncomparablePairsOverlap (𝓗 : Set (Set α)) : Prop :=
  ∀ h ∈ 𝓗, ∀ g ∈ 𝓗,
    (¬h ⊆ g ∧ ¬g ⊆ h) →
      (h ∩ g).Nonempty ∧ h ∪ g = Set.univ
```

(`IdentificationGeometry.lean:L886,L891`). Non-strict `h⊆g` replaces the paper's proper superset relation because Lean permits duplicate indices with equal supports; on distinct extensional supports the two formulations coincide.

**Lean theorem types.** The three directions are exposed as:

```lean
theorem theorem_4_7_identifier_equivalence
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F ↔
      TextIdentifiable F ∧
        NonEliminabilityContained (Set.range F)
```

```lean
theorem theorem_4_7_geometric_equivalence
    (𝓗 : Set (Set α)) :
    NonEliminabilityContained 𝓗 ↔
      IncomparablePairsOverlap 𝓗
```

```lean
theorem theorem_4_7
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F ↔
      TextIdentifiable F ∧
        IncomparablePairsOverlap (Set.range F)
```

(`IdentifierCharacterization.lean:L3755,L3776`; `IdentificationGeometry.lean:L974`).

**Quantifier and representation audit.**

- Countability of the class is encoded by a natural-number index, not a `Countable` predicate on an extensional set.
- The class cannot be empty; finite classes are represented with repetitions.
- The stable output is a single index denoting the target support.
- The paper's literal non-eliminability relation is replaced in condition (ii) by common-vertex coverage. Under `[Countable α]` and properness, Proposition 4.2 supplies the equivalence for each pair.
- `theorem_4_7_geometric_equivalence` itself has no nonempty/proper/countability assumptions, so it is a genuine generalization of the set geometry.
- No membership, consistency, closure, or tell-tale oracle is in the theorem type.

**Access recursively unfolded.** The sufficiency helper is

```lean
theorem contrastiveTellTaleLearner_identifies
    {F : ℕ → Set α}
    (hTell : GenLimit.Angluin.ConditionTwo F)
    (hrel : NonEliminabilityContained (Set.range F)) :
    ContrastivelyIdentifies
      (contrastiveTellTaleLearner F (chosenTellTale hTell)) F
```

Its eligibility certificate for index `i` at time `t` is exactly:

1. `i≤t`;
2. the selected finite tell-tale `T_i` is contained in the set of observed endpoints;
3. every observed edge crosses `F i`.

`ConditionTwo` supplies the finite distinguishing sets; `hrel` forces a candidate failing to contain the target eventually to violate an observed edge. For a strict superset candidate, the tell-tale condition plus the XOR consistency test excludes it. These are substantive link conditions, but neither directly asserts contrastive identification.

**Characterization correspondence verdict:** **Faithful specialization**.  
**Characterization difficulty verdict:** **Preserved**.

**Pure geometric subequivalence correspondence verdict:** **Faithful generalization**.  
**Pure geometric subequivalence difficulty verdict:** **Strengthened / harder**.

## 5. Detailed generation and closure comparison

### 5.1 Definitions 5.1–5.3: closure, hollow sets, and thresholds

**Paper definitions.** For finite unordered `E⊆[X]^2`,

- `HΔ(E)={g∈H:E⊆Δ(g)}`;
- `⟨E⟩^Δ_H=⋂_{g∈HΔ(E)} supp(g)` when the version space is nonempty, and `⊥` otherwise;
- `E` is hollow when `HΔ(E)≠∅` and `⟨E⟩^Δ_H\V(E)=∅`;
- `CΔ(H)` is the supremum of hollow-edge cardinalities, with empty supremum `0`;
- a uniform generator has one distinct-edge threshold for the whole class;
- a non-uniform generator has one fixed generator and a target-dependent threshold (Definitions 5.1–5.3, PDF p. 8).

**Lean unordered interface.** The principal finite-edge definitions are:

```lean
def unorderedVersionSpace
    (𝓗 : Set (Set α)) (E : Finset (UnorderedEdge α)) :
    Set (Set α) :=
  {h | h ∈ 𝓗 ∧ ∀ p, p ∈ E → UnorderedCrosses h p}
```

```lean
noncomputable def unorderedClosure
    (𝓗 : Set (Set α)) (E : Finset (UnorderedEdge α)) : Set α :=
  if (unorderedVersionSpace 𝓗 E).Nonempty then
    {x | ∀ h, h ∈ unorderedVersionSpace 𝓗 E → x ∈ h}
  else ∅
```

```lean
def IsContrastivelyHollow
    (𝓗 : Set (Set α)) (E : Finset (UnorderedEdge α)) : Prop :=
  (unorderedVersionSpace 𝓗 E).Nonempty ∧
    unorderedClosure 𝓗 E ⊆ unorderedVertices E
```

```lean
def ContrastiveClosureDimensionAtMost
    (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  ∀ E, IsContrastivelyHollow 𝓗 E → E.card ≤ d
```

```lean
def ContrastiveClosureDimensionEquals
    (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  ContrastiveClosureDimensionAtMost 𝓗 d ∧
    ∀ b, ContrastiveClosureDimensionAtMost 𝓗 b → d ≤ b
```

(`ClosureDimension.lean`, bundle lines 3824–3986).

`unorderedClosure=∅` on an empty version space is not literally the paper's `⊥`. The distinction is retained by explicitly conjoining version-space nonemptiness in `IsContrastivelyHollow`; valid target histories also carry a member of the version space. Therefore the conflation does not trivialize Theorem 5.4, but the definition is not a literal encoding of the paper's partial closure value.

**Uniform threshold.** Lean states

```lean
def UniformlyContrastivelyGeneratesAt
    (G : ContrastiveGenerator α) (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  ∀ h, h ∈ 𝓗 → ∀ t, ∀ history : Fin t → Edge α,
    (∀ i, Crosses h (history i)) →
    d ≤ (distinctUnorderedEdges history).card →
      G t history ∈ h ∧ G t history ∉ seenPrefix history
```

The paper quantifies over prefixes of crossing-edge streams; Lean quantifies directly over every finite crossing history. At positive thresholds every such nonempty history can be continued by repeating a crossing edge, so this is the natural finite-prefix form. At threshold `0`, however, Lean also tests the empty history.

**Non-uniform threshold.** Lean states

```lean
def NonuniformlyContrastivelyGenerates
    (G : ContrastiveGenerator α) (𝓗 : Set (Set α)) : Prop :=
  ∀ h, h ∈ 𝓗 →
    ∃ d, ∀ t, ∀ history : Fin t → Edge α,
      (∀ i, Crosses h (history i)) →
      d ≤ (distinctUnorderedEdges history).card →
        G t history ∈ h ∧ G t history ∉ seenPrefix history
```

This preserves the paper's `∃G ∀h ∃d_h ∀P` order exactly. The threshold does not depend on the stream/history.

**Closure-definition correspondence verdict:** **Related but materially different**.  
**Closure-definition difficulty verdict:** **Preserved**.

**Uniform-definition correspondence verdict:** **Faithful generalization**.  
**Uniform-definition difficulty verdict:** **Preserved**.

**Non-uniform-definition correspondence verdict:** **Faithful generalization**.  
**Non-uniform-definition difficulty verdict:** **Preserved**.

### 5.2 Theorem 5.4: uniform generation and exact sample complexity

**Paper theorem.** `H` is uniformly contrastively generatable iff `CΔ(H)<∞`; if `CΔ(H)=d`, then distinct-edge sample complexity `d+1` is necessary and sufficient (Theorem 5.4, PDF p. 8; full proof on PDF p. 17).

**Lean qualitative theorem.** 

```lean
theorem theorem_5_4
    [Nonempty α] (𝓗 : Set (Set α)) :
    UniformlyContrastivelyGeneratable 𝓗 ↔
      FiniteContrastiveClosureDimension 𝓗
```

where `UniformlyContrastivelyGeneratable 𝓗 := ∃d, ∃G, UniformlyContrastivelyGeneratesAt G 𝓗 d` and `FiniteContrastiveClosureDimension 𝓗 := ∃d, ContrastiveClosureDimensionAtMost 𝓗 d` (`ClosureDimension.lean:L4002,L3970,L4228`).

**Lean quantitative theorem.**

```lean
theorem theorem_5_4_quantitative
    [Nonempty α] (𝓗 : Set (Set α)) (d : ℕ) :
    UniformlyContrastivelyGeneratableAt 𝓗 (d + 1) ↔
      ContrastiveClosureDimensionAtMost 𝓗 d
```

(`ClosureDimension.lean:L4215`). This is stronger than merely saying that a class of exact dimension `d` has a generator at `d+1`: it identifies the threshold `d+1` exactly with the upper-bound statement for every `d`.

**Sharpness theorem.**

```lean
theorem theorem_5_4_sharp_sample_complexity
    [Nonempty α] {𝓗 : Set (Set α)} {d : ℕ}
    (hdim : ContrastiveClosureDimensionEquals 𝓗 d) :
    IsLeastPositiveUniformThreshold 𝓗 (d + 1)
```

with

```lean
def IsLeastPositiveUniformThreshold (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  0 < d ∧ UniformlyContrastivelyGeneratableAt 𝓗 d ∧
  ∀ k, 0 < k → UniformlyContrastivelyGeneratableAt 𝓗 k → d ≤ k
```

(`ClosureDimension.lean:L4010,L4245`).

**Changed assumptions and scope.**

- The paper's standing classes are countable; Lean allows an arbitrary extensional class `𝓗`, possibly uncountable.
- The paper's example space is countably infinite; Lean needs only `[Nonempty α]` for fallback outputs. The closure theorem itself is purely semantic and does not enumerate the domain.
- No UUS, properness, or presentation-coverage premise appears. Uniform correctness is asked directly on finite crossing histories, and the closure condition itself determines when a fresh forced positive exists.
- Sample complexity counts distinct **unordered edges**, exactly as in the paper, not rounds, distinct vertices, or total occurrences.
- There is no probabilistic confidence, expected sample size, runtime, or oracle-call complexity.

**Boundary repair.** If thresholds range over all naturals and the empty history is a legal finite history, a class of dimension zero can sometimes generate already at threshold zero. The paper's round convention starts with observed pairs and calls `d+1` the sample complexity. Lean avoids asserting false or convention-dependent global leastness by minimizing only among positive thresholds. For `d≥1`, or under the paper's positive-round convention, the formulations agree.

**Qualitative correspondence verdict:** **Faithful generalization**.  
**Qualitative difficulty verdict:** **Strengthened / harder**.

**Quantitative correspondence verdict:** **Faithful generalization**.  
**Quantitative difficulty verdict:** **Strengthened / harder**.

**Sharp-threshold correspondence verdict:** **Faithful specialization**.  
**Sharp-threshold difficulty verdict:** **Preserved**.

### 5.3 Theorem 5.4 helper graph and circularity audit

The relevant statement interfaces unfold as follows.

1. `finite_history_target_in_version` says that if `h∈𝓗` and every history edge crosses `h`, then `h` belongs to the unordered version space of the distinct observed edges.
2. `fresh_closure_point_of_dimension_bound` assumes a dimension upper bound `d`, nonempty version space, and at least `d+1` distinct edges, and concludes that the closure contains a point outside the observed vertex set.
3. `closureDimensionGenerator` classically chooses such a point when one exists; otherwise it returns an arbitrary inhabitant.
4. `dimensionBound_suffices` states that this named generator works at threshold `d+1`.
5. `hollow_obstructs_generator` says a supplied hollow set `E` with `d≤|E|` defeats any proposed generator at threshold `d`.
6. `generator_implies_dimension_bound` derives the dimension bound from a proposed generator at `d+1`.

No helper assumes uniform generation and then concludes the same generator works. The lower bound does receive the hard finite witness `E`, but that witness is exactly what the dimension definition quantifies over. The upper bound uses semantic intersection membership and classical choice rather than any executable closure oracle.

The additional declaration

```lean
theorem hollow_cardinality_lower_bound
    (hollow : IsContrastivelyHollow 𝓗 E) :
    ¬UniformlyContrastivelyGeneratableAt 𝓗 E.card
```

is a useful theorem-level lower-bound form not separately numbered in the paper.

**Correspondence verdict:** **Extra Lean result not claimed by the paper**.  
**Difficulty verdict:** **Indeterminate**.

### 5.4 Theorem 5.5: non-uniform chain characterization

**Paper theorem.** There is one target-dependent-threshold generator for `H` iff `H` is the increasing union of classes `H₁⊆H₂⊆…` with finite contrastive closure dimension at every level (Theorem 5.5, PDF p. 8; proof on PDF p. 17). The generator is information-theoretic and takes the chain and per-level dimensions as inputs (Remark 5.6, PDF p. 8).

**Lean theorem.** 

```lean
theorem theorem_5_5
    [Nonempty α] (𝓗 : Set (Set α)) :
    NonuniformlyContrastivelyGeneratable 𝓗 ↔
      ∃ classes : ℕ → Set (Set α),
        GenLimit.LiRamanTewari.IsNondecreasingCover 𝓗 classes ∧
        ∀ n, FiniteContrastiveClosureDimension (classes n)
```

(`NonuniformClosure.lean:L5274`). The imported cover predicate unfolds to `Monotone classes ∧ 𝓗 = ⋃n, classes n`.

The two directions are also separate declarations:

```lean
theorem theorem_5_5_necessity
    (hNonuniform : NonuniformlyContrastivelyGeneratable 𝓗) :
    ∃ classes, IsNondecreasingCover 𝓗 classes ∧
      ∀ n, FiniteContrastiveClosureDimension (classes n)
```

```lean
theorem theorem_5_5_sufficiency
    [Nonempty α]
    (hcover : IsNondecreasingCover 𝓗 classes)
    (hdim : ∀ n, FiniteContrastiveClosureDimension (classes n)) :
    NonuniformlyContrastivelyGeneratable 𝓗
```

(`NonuniformClosure.lean:L5098,L5212`).

**Quantifier preservation.** The right side is existential in the chain. The left side is `∃G∀h∈𝓗∃d_h∀history`. No stream-specific threshold is introduced. The same `G` must work for every target.

**Access and helper graph.**

- Necessity defines `generatorLevel G 𝓗 n` as the targets on which `G` is correct after `n+1` distinct edges. These levels are monotone and cover `𝓗` if `G` has target-dependent thresholds. Uniform correctness at level `n` yields a closure-dimension bound `n`.
- Sufficiency receives a monotone cover and, for each level, the proposition that some finite dimension bound exists. `selectedClosureBound` chooses one such number by classical choice.
- The padded threshold is `m + bound(m) + 1`. Padding ensures only finitely many levels can be active at a finite edge count.
- The generator selects the largest active level and invokes that level's closure generator. Monotonicity moves a target from its first containing level to the selected larger level.

The paper says the dimensions are inputs. Lean's theorem type supplies only proofs that finite bounds exist and selects the actual values noncomputably, which is easier at an algorithmic interface even though the semantic theorem is more general in class cardinality.

**Correspondence verdict:** **Faithful generalization**.  
**Difficulty verdict:** **Strengthened / harder**. The class theorem covers arbitrary extensional classes. Separately, its effectivity/access interface is weaker because numerical bounds are selected semantically rather than supplied by an effective procedure; that access observation is not a second difficulty verdict.

### 5.5 Proposition 5.8: infinite safe cores

**Paper statement.** If for every target, every valid contrastive presentation, and every time `n`, the safe closure is infinite, then `H∈CtrGen` (Proposition 5.8, PDF p. 9; proof p. 17).

**Lean premise and theorem.**

```lean
def InfiniteSafeCores (𝓗 : Set (Set α)) : Prop :=
  ∀ h, h ∈ 𝓗 → ∀ stream : ℕ → Edge α,
    IsContrastivePresentation stream h →
      ∀ t, (edgeClosure 𝓗 (streamPrefix stream t)).Infinite
```

```lean
theorem proposition_5_8 [Nonempty α]
    (𝓗 : Set (Set α)) (hsafe : InfiniteSafeCores 𝓗) :
    ContrastivelyGeneratable 𝓗
```

(`GenerationCores.lean:L1092,L1126`). Separately, `safeCoreGenerator_spec` together with `edgeClosure_subset_target` states an all-time safe and unseen output under the premise, although the public proposition concludes only eventual correctness.

The safe-core premise already supplies infinitely many points common to all edge-consistent hypotheses at each valid prefix. Since the observed endpoint set is finite, a fresh target point follows immediately by choice. This is a strong but noncircular certificate: it does not assert existence of one global generator or specify its outputs.

For targets admitting no valid presentation, both the premise's presentation implication and the generation obligation are vacuous. The paper avoids this through proper nontrivial targets; the Lean theorem does not.

**Correspondence verdict:** **Faithful generalization**.  
**Difficulty verdict:** **Preserved**. The public proposition has the same eventual conclusion; the all-time guarantee belongs to the separate named helper interface, while degenerate presentationless targets add only vacuous broader cases.

### 5.6 Definition 5.10 and Proposition 5.11: eventual cores

**Paper statement.** An injective sequence `(r_m)` is an eventual core if every target omits only finitely many terms; a countable class of infinite proper nontrivial hypotheses with such a sequence lies in `CtrGen` (Definition 5.10 and Proposition 5.11, PDF p. 9; proof p. 17).

**Lean content.**

```lean
def IsEventualCore (𝓗 : Set (Set α)) (core : ℕ → α) : Prop :=
  Function.Injective core ∧
    ∀ h, h ∈ 𝓗 → {m : ℕ | core m ∉ h}.Finite
```

```lean
theorem proposition_5_11
    (𝓗 : Set (Set α)) (core : ℕ → α)
    (hcore : IsEventualCore 𝓗 core) :
    ContrastivelyGeneratable 𝓗
```

(`GenerationCores.lean:L1141,L1201`). The sequence is a supplied witness. The finite exceptional set may depend on the target. The generator uses a pairing index at least the current time and chooses a core value outside the finitely many observed endpoints; it does not use any target-membership oracle.

Lean drops countability of `𝓗`, explicit support infinitude, and properness. The eventual-core condition itself forces every target to contain infinitely many core points, but it does not force a negative point. For a universal support, no valid contrastive presentation exists, and the conclusion is vacuous. Thus the theorem is a valid logical generalization but easier on degenerate targets than the source result.

**Definition correspondence verdict:** **Exact / formally equivalent**.  
**Definition difficulty verdict:** **Preserved**.

**Proposition correspondence verdict:** **Faithful generalization**.  
**Proposition difficulty verdict:** **Weakened / easier**.

### 5.7 Proposition 5.12: finite-family obstruction

**Paper statement.** If a finite family `F` belongs to the confusability complex, has at least two members, and has finite support intersection, then the ambient class is not contrastively generatable (Proposition 5.12, PDF p. 9; full proof p. 18). Proposition B.1 characterizes existence of a shared presentation by common-family crossing coverage (PDF p. 18).

**Lean certificate interface.**

```lean
def IsSharedPresentation
    (stream : ℕ → Edge α) (family : Finset (Set α)) : Prop :=
  ∀ h, h ∈ family → IsContrastivePresentation stream h
```

```lean
def IsFiniteFamilyIntersection
    (family : Finset (Set α)) (core : Finset α) : Prop :=
  ∀ x, x ∈ core ↔ ∀ h, h ∈ family → x ∈ h
```

```lean
theorem proposition_5_12
    {𝓗 : Set (Set α)} {family : Finset (Set α)}
    {core : Finset α} {stream : ℕ → Edge α}
    (hfamilyNonempty : family.Nonempty)
    (hfamilyClass : ∀ h, h ∈ family → h ∈ 𝓗)
    (hshared : IsSharedPresentation stream family)
    (hcore : IsFiniteFamilyIntersection family core) :
    ¬ContrastivelyGeneratable 𝓗
```

(`Hierarchy.lean:L5539–5551`).

The Lean theorem receives the shared stream and a finite set exactly coding the intersection; it does not construct either from a family-level common crossing graph. This is an explicit-certificate specialization of the paper premise. It permits a singleton family with finite support; the paper excludes this only because UUS makes the singleton case impossible.

The certificate does real work but does not encode the conclusion. A common stream makes the generator's finite history identical under every selected target. Eventual correctness for all targets forces outputs into the finite intersection, and positive-side coverage eventually puts every intersection point into the observed endpoint set, contradicting novelty.

**Correspondence verdict:** **Faithful generalization**.  
**Difficulty verdict:** **Weakened / easier** because the shared presentation and exact finite intersection are supplied.

**Proposition B.1 correspondence verdict:** **Not represented in Lean**.  
**Proposition B.1 difficulty verdict:** **Indeterminate**.

### 5.8 Examples 5.7 and 5.9

#### Punctured support

The paper takes an infinite proper `A={a_m}` and supports `A` and `A\{a_m}`. It claims ordinary contrastive generation via the eventual core and infinite closure dimension through hollow edge sets `{{a_i,b}:1≤i≤n}` (Example 5.7, PDF p. 8).

Lean specializes `A` to the even numbers:

```lean
def puncturedFamily : ℕ → Set ℕ
  | 0 => Set.range (fun m => 2*m)
  | m+1 => Set.range (fun m => 2*m) \ {2*m}
```

and states

```lean
theorem theorem_5_13_5_14_punctured_witness :
  ContrastivelyGeneratable (Set.range puncturedFamily) ∧
    ¬TextIdentifiable puncturedFamily ∧
    ¬ContrastivelyIdentifiable puncturedFamily
```

(`Hierarchy.lean:L5617,L5718`).

The ordinary-generation and non-text-identification conclusions are strong faithful instances. No declaration states `CΔ=∞`, identifies hollow edge sets, or compares this class with `UniformlyContrastivelyGeneratable`.

**Generation/witness correspondence verdict:** **Faithful specialization**.  
**Generation/witness difficulty verdict:** **Preserved**.

**Infinite-dimension correspondence verdict:** **Not represented in Lean**.  
**Infinite-dimension difficulty verdict:** **Indeterminate**.

#### Augmented support and source defect

The printed Example 5.9 assumes only that `A⊊X` is infinite and writes `X\A={b_m}`; it then claims the supports `A` and `A∪{b_m}` yield a non-covering barrier (PDF p. 9). This is not valid from those assumptions alone. If `X\A` has one point, the class has only a chain. If it has exactly two points, the two augmented supports intersect in `A` and together cover `X`, so they satisfy the overlapping-cover condition rather than violate it. The appendix hierarchy proof repairs the witness by choosing disjoint infinite `A,B` with a further nonempty region `X\(A∪B)` (PDF p. 18).

No Lean declaration formalizes either the printed or repaired augmented class. Lean instead uses the punctured family to witness `CtrId⊊CtrGen`.

**Literal Example 5.9 correspondence verdict:** **Not represented in Lean**.  
**Literal Example 5.9 difficulty verdict:** **Indeterminate**.

**Hierarchy repair correspondence verdict:** **Related but materially different**.  
**Hierarchy repair difficulty verdict:** **Preserved**.

## 6. Detailed clean-hierarchy comparison

### 6.1 Theorem 5.13: the strict diamond's chain edges

**Paper statement.** On countable UUS classes,

`CtrId ⊊ CtrGen ⊊ TxtGen` and `CtrId ⊊ TxtId ⊊ TxtGen`

(Theorem 5.13, PDF p. 9; full proof p. 18). This is a theorem about four **families of classes**, not merely about one or two examples.

Lean does not define those four meta-level families as sets and does not state a single strict-containment theorem. Its component declarations are as follows.

#### `CtrId ⊆ CtrGen`

```lean
theorem contrastiveIdentification_implies_generation
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    ContrastivelyIdentifiable F →
      ContrastivelyGeneratable (Set.range F)
```

(`Hierarchy.lean:L5354`). This is a faithful generalization: neither countability of `α` nor properness is needed once the indexed supports are infinite. The generator chooses a point in the currently guessed support outside the finite observed endpoint set. It does not exclude earlier generated outputs.

**Correspondence verdict:** **Faithful generalization**.  
**Difficulty verdict:** **Strengthened / harder**.

#### `CtrId ⊆ TxtId`

This is `lemma_4_6_inclusion`, already audited as a faithful specialization.

**Correspondence verdict:** **Faithful specialization**.  
**Difficulty verdict:** **Preserved**.

#### `TxtId ⊆ TxtGen`

```lean
theorem textIdentification_implies_generation
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    TextIdentifiable F →
      GenLimit.LiRamanTewari.GeneratableInLimit (Set.range F)
```

(`Hierarchy.lean:L5405`). This proves the elementary identification-to-generation inclusion for an indexed UUS family. The paper derives the same inclusion from universal text generation, but the direct implication is sufficient.

**Correspondence verdict:** **Faithful generalization**.  
**Difficulty verdict:** **Strengthened / harder**.

#### `CtrGen ⊆ TxtGen`

No target-scope theorem starts from `ContrastivelyGeneratable 𝓗` and concludes ordinary text generation. Imported Paper02 background has a stronger target-dependent distinct-sample-threshold theorem for countable UUS text classes, but no Paper28 declaration bridges that predicate to ordinary `TxtGen` or applies it here.

**Correspondence verdict:** **Not represented in Lean**.  
**Difficulty verdict:** **Indeterminate**.

### 6.2 Strictness witnesses

#### `CtrId ⊊ CtrGen` and `CtrGen ⊄ TxtId`

Lean's punctured theorem states:

```lean
theorem theorem_5_13_5_14_punctured_witness :
  ContrastivelyGeneratable (Set.range puncturedFamily) ∧
    ¬TextIdentifiable puncturedFamily ∧
    ¬ContrastivelyIdentifiable puncturedFamily
```

This directly supplies a UUS-style class in `CtrGen\CtrId` and in `CtrGen\TxtId`. It differs from the paper's augmented-support witness for the first strictness but agrees with the punctured witness used for incomparability and `TxtId` strictness.

**Correspondence verdict:** **Faithful specialization**.  
**Difficulty verdict:** **Preserved**.

#### `TxtId ⊄ CtrGen` and `CtrGen ⊊ TxtGen` witness

Lean's disjoint theorem states:

```lean
theorem theorem_5_13_5_14_disjoint_witness :
  TextIdentifiable disjointFamily ∧
    GenLimit.LiRamanTewari.GeneratableInLimit
      (Set.range disjointFamily) ∧
    ¬ContrastivelyGeneratable (Set.range disjointFamily)
```

(`DisjointHierarchy.lean:L5923`). The family is the even support and the odd support (with repeated odd indices); both are infinite. The theorem directly gives a class in `TxtId\CtrGen` and `TxtGen\CtrGen`.

**Correspondence verdict:** **Faithful specialization**.  
**Difficulty verdict:** **Preserved**.

#### `CtrId ⊊ TxtId`

The disjoint theorem does not state `¬ContrastivelyIdentifiable`, but that follows from its `¬ContrastivelyGeneratable` component and the separate general inclusion `CtrId→CtrGen`. Because the strictness is not one theorem type, the literal correspondence is componentwise.

**Correspondence verdict:** **Related but materially different**.  
**Difficulty verdict:** **Weakened / easier**.

#### `TxtId ⊊ TxtGen`

Lean has the general inclusion `TxtId→TxtGen`, but it does not state that the punctured class is text-generatable. The imported Paper02 non-uniform text-generation theorem is related and could support an additional bridge, but no target-scope declaration instantiates or converts it. Therefore no Paper28 theorem type provides a class in `TxtGen\TxtId`.

**Correspondence verdict:** **Not represented in Lean**.  
**Difficulty verdict:** **Indeterminate**.

### 6.3 Overall verdict for Theorem 5.13

The component types establish three inclusions, two powerful witnesses, and enough facts to derive some strictness claims externally. They do not state or fully support the entire strict diamond within the supplied declaration graph.

**Correspondence verdict:** **Related but materially different**.  
**Difficulty verdict:** **Weakened / easier**.

### 6.4 Theorem 5.14: mutual incomparability

**Paper statement.** `CtrGen⊄TxtId` and `TxtId⊄CtrGen` (Theorem 5.14, PDF p. 10; proof p. 18).

The punctured witness gives the first direction, and the disjoint witness gives the second. Both are explicit arithmetic specializations of the paper's natural examples. The quantifiers needed for an incomparability theorem are existential over witness classes, and these conjunctions provide exactly those witnesses even though no meta-level family relation is defined.

**Correspondence verdict:** **Faithful specialization**.  
**Difficulty verdict:** **Preserved**.

### 6.5 Family confusability and higher-order geometry

The paper defines the family common crossing graph `Γ(F)=⋂_{h∈F}Δ(h)`, a confusability complex `C(H)`, gives Proposition B.1, and proves that pairwise intersections can all be infinite while a three-way shared presentation has finite intersection (Proposition D.1 and Example D.2, PDF pp. 9,18,20–21).

Lean has only:

- `IsSharedPresentation stream family`, an explicit shared-stream certificate;
- `IsFiniteFamilyIntersection family core`, an exact finite-intersection certificate;
- Proposition 5.12 using those certificates.

There is no `Γ(F)`, no finite-family common-vertex set, no confusability-complex object, no downward-closure theorem, no membership-pattern cells, and no higher-order example.

**Correspondence verdict:** **Not represented in Lean**.  
**Difficulty verdict:** **Indeterminate**.

## 7. Detailed robustness comparison

### 7.1 Definition 6.1: corrupted presentations and known versus unknown budget

The paper distinguishes:

- `k-TxtId` and `k-CtrId`, where `k` is known and the learner may depend on it;
- `Fin-CtrId`, where one learner works for every finite `k` (Definition 6.1, PDF p. 10).

Lean's exact quantifier orders are:

```lean
def KTextIdentifiable (k : ℕ) (F : ℕ → Set α) : Prop :=
  ∃ M, ∀ z stream,
    IsKCorruptedTextPresentation k stream (F z) →
      ∃ j, F j = F z ∧ ConvergesTo M stream j
```

```lean
def KContrastivelyIdentifiable (k : ℕ) (F : ℕ → Set α) : Prop :=
  ∃ I, ∀ z stream,
    IsKCorruptedContrastivePresentation k stream (F z) →
      ContrastivelyIdentifiesFrom I F z stream
```

```lean
def FinitelyCorruptionContrastivelyIdentifiable
    (F : ℕ → Set α) : Prop :=
  ∃ I, ∀ k z stream,
    IsKCorruptedContrastivePresentation k stream (F z) →
      ContrastivelyIdentifiesFrom I F z stream
```

(`CorruptedPresentations.lean`, bundle lines 5986–6008).

In `Fin-CtrId`, the existential identifier precedes `k`, exactly preserving budget independence. Corruption counts stream positions, not distinct bad examples or edges. Positive-side coverage is never corrupted away.

**Correspondence verdict:** **Faithful specialization**.  
**Difficulty verdict:** **Preserved**.

### 7.2 Definition 6.2 and Proposition 6.3: defect as exact forced violations

**Paper claim.** For distinct proper nontrivial `h,g`,

`D⁺_{h→g}=supp(h)\V(Γ(h,g))`, `κ(h→g)=|D⁺_{h→g}|`, and

`inf_{P valid for h} |{t:p_t∉Δ(g)}| = κ(h→g)`;

in particular, `g` is not eliminable from `h` iff `κ(h→g)=0` (Definition 6.2 and Proposition 6.3, PDF p. 10; proof pp. 18–19).

**Lean definitions.**

```lean
def positiveDefectSet (h g : Set α) : Set α :=
  h \ commonVertices h g
```

```lean
noncomputable def defectNumber (h g : Set α) : ℕ∞ :=
  (positiveDefectSet h g).encard
```

```lean
def cleanWrongCutViolationCounts (h g : Set α) : Set ℕ∞ :=
  {c | ∃ stream,
    IsContrastivePresentation stream h ∧
      wrongCutViolationCount g stream = c}
```

```lean
noncomputable def forcedWrongCutViolationInfimum
    (h g : Set α) : ℕ∞ :=
  sInf (cleanWrongCutViolationCounts h g)
```

(`DefectInfimum.lean:L7145–7171`). The count is a literal extended-natural cardinal of bad occurrence indices.

**Lean exact theorem.**

```lean
theorem proposition_6_3_defect_eq_forced_wrong_cut_infimum
    [Countable α] {h g : Set α}
    (_hDistinct : h ≠ g)
    (hh : ProperNontrivialSupport h)
    (hg : ProperNontrivialSupport g) :
    forcedWrongCutViolationInfimum h g = defectNumber h g
```

and

```lean
theorem proposition_6_3_notEliminable_iff_defectNumber_zero
    [Countable α] {h g : Set α}
    (_hDistinct : h ≠ g)
    (hh : ProperNontrivialSupport h)
    (_hg : ProperNontrivialSupport g) :
    NotEliminableFrom g h ↔ defectNumber h g = 0
```

(`DefectInfimum.lean:L7573,L7606`).

Lean does not require `[Infinite α]`; countability plus properness suffices even for finite domains because a clean infinite stream may repeat edges. The exact equality direction is reversed syntactically relative to the paper, but equality is symmetric.

**Helper graph.**

1. `defectToViolationTime` chooses, for each positive defect, one presentation occurrence incident to it.
2. `defectToViolationTime_injective` states that this map is injective, because an `h`-crossing edge has only one positive endpoint.
3. `defectNumber_le_wrongCutViolationCount` gives the lower bound for every clean presentation.
4. `exists_clean_contrastive_presentation` ensures the set over which the infimum is taken is nonempty under countability and properness.
5. If the defect set is finite, `exists_clean_presentation_wrongCutCount_eq_defect` supplies a clean presentation with exactly one wrong-cut occurrence per defect and only common-crossing filler edges thereafter.
6. If the defect set is infinite, both sides are `⊤` once the universal lower bound is used.

The infimum is therefore not made true by an empty-set convention. No premise already states the infimum equality. The paper's distinctness assumption is carried but not needed for the displayed equality, and properness of `g` is not needed for the zero-defect corollary's displayed conclusion; these are assumption slack, not unsoundness.

**Exact-infimum correspondence verdict:** **Faithful generalization**.  
**Exact-infimum difficulty verdict:** **Strengthened / harder**.

**Zero-defect correspondence verdict:** **Faithful generalization**.  
**Zero-defect difficulty verdict:** **Preserved**.

### 7.3 Missing general infinite-defect identification theorem

The main-results overview says that when the defect number is infinite between every pair of hypotheses, finite-corruption identification is possible by violation counting (PDF p. 3). The body text says this “opens a path” and then proves the co-singleton instance (PDF p. 10). No numbered general theorem appears in the PDF, and no Lean declaration states such a class-level sufficient condition.

The Lean defect theorem alone gives a pairwise lower bound on wrong-cut occurrences. Turning those bounds into one identifier for a countable class requires an additional candidate-selection and stabilization theorem. That theorem is absent.

**Correspondence verdict:** **Not represented in Lean**.  
**Difficulty verdict:** **Indeterminate**.

### 7.4 Definition 6.4 and Theorem 6.5: co-singleton text fragility

Lean defines

```lean
def coSingletonSupport (s : α) : Set α := {x | x ≠ s}

def coSingletonFamily : ℕ → Set ℕ := coSingletonSupport
```

and states

```lean
theorem theorem_6_5 :
  ¬KTextIdentifiable 1 coSingletonFamily
```

(`CorruptedPresentations.lean:L6015–6049`). The paper works on an arbitrary countably infinite `X`; Lean fixes `X=ℕ`. The index is the missing point, so different indices denote different supports.

The theorem is fully nonvacuous: the identity enumeration is a one-corrupted text for every co-singleton target, so two different targets receive identical data. The theorem is semantic; it rules out every arbitrary identifier, not only computable ones.

**Correspondence verdict:** **Faithful specialization**.  
**Difficulty verdict:** **Preserved**.

### 7.5 Algorithm 1 and Theorem 6.6

**Paper algorithm and guarantee.** On a finite prefix, compute

`a_n(x)=|{i≤n:x∉p_i}|`

for each observed endpoint, choose a minimizer, break ties by the fixed enumeration of `X`, and output the corresponding co-singleton hypothesis. Theorem 6.6 says one budget-independent algorithm identifies under every finite corruption budget (PDF p. 11; proof p. 19). Appendix E.3 calls the method primitive computable and oracle-free (PDF p. 22).

**Lean finite statistics.**

```lean
def seenEndpoints [DecidableEq α]
    {t : ℕ} (history : Fin t → Edge α) : Finset α :=
  (Finset.univ.image fun i => (history i).left) ∪
    (Finset.univ.image fun i => (history i).right)
```

```lean
def absenceCount [DecidableEq α]
    {t : ℕ} (history : Fin t → Edge α) (x : α) : ℕ :=
  (Finset.univ.filter fun i => ¬Incident x (history i)).card
```

These exactly implement the displayed finite statistic.

**Lean identifier.**

```lean
noncomputable def absenceCountIdentifier : ContrastiveIdentifier ℕ :=
  fun _t history =>
    if hseen : (seenEndpoints history).Nonempty then
      Classical.choose
        (Finset.exists_min_image
          (seenEndpoints history)
          (fun x => absenceCount history x) hseen)
    else 0
```

(`AbsenceCount.lean:L6364`). This selects an arbitrary minimizer. There is no fixed-enumeration tie-break, no executable finite search term, and no `Computable` declaration.

**Lean theorem.**

```lean
theorem theorem_6_6 :
  FinitelyCorruptionContrastivelyIdentifiable coSingletonFamily
```

(`AbsenceCount.lean:L6482`), i.e.

`∃I, ∀k s stream, IsKCorruptedContrastivePresentation k stream (ℕ\{s}) → ∃j, coSingleton(j)=coSingleton(s) ∧ ∃T∀t≥T, I(stream≤t)=j`.

The existential `I` is outside `k`, so budget independence is exact. But the theorem type does **not** mention `absenceCountIdentifier`. Under the evidence rule, the proof body cannot be used to claim that the named minimizer is the witness.

**Named helper statements.** The bundle separately states that:

- the true center's absence count is at most `k` at every time;
- every false center is omitted at infinitely many observation indices;
- every false center's absence count eventually exceeds any fixed `k`;
- the true center is eventually in the seen-endpoint candidate set;
- `absenceCountIdentifier` belongs to that candidate set and has minimal absence count;
- any seen candidate with absence count at most `k` must already occur among endpoints of the first `k+1` observations.

These are the substantive ingredients of the paper's argument, but no final theorem signature combines them with the named identifier.

**Membership-theorem correspondence verdict:** **Faithful specialization**.  
**Membership-theorem difficulty verdict:** **Preserved**.

**Algorithm-specific correspondence verdict:** **Related but materially different**.  
**Algorithm-specific difficulty verdict:** **Weakened / easier**.

**Constructivity correspondence verdict:** **Related but materially different**.  
**Constructivity difficulty verdict:** **Weakened / easier**.

### 7.6 Example 6.7

The paper gives the six pairs

`{3,0},{3,1},{0,4},{3,2},{3,4},{3,5}`

with `{0,4}` corrupted, and records absence counts `(4,5,5,1,4,5)` for endpoints `0,…,5`; it also says that along any valid extension the count of `3` stays bounded while every false count diverges (Example 6.7, PDF p. 11).

Lean has a concrete six-edge history and states:

```lean
theorem example_6_7_absence_counts :
  absenceCount example67History 0 = 4 ∧
  absenceCount example67History 1 = 5 ∧
  absenceCount example67History 2 = 5 ∧
  absenceCount example67History 3 = 1 ∧
  absenceCount example67History 4 = 4 ∧
  absenceCount example67History 5 = 5
```

and the stronger finite-prefix statement

```lean
theorem example_6_7_unique_minimizer :
  3 ∈ seenEndpoints example67History ∧
  ∀ x ∈ seenEndpoints example67History,
    x ≠ 3 → absenceCount example67History 3 <
      absenceCount example67History x
```

(`AbsenceCount.lean:L6563,L6574`). The extension-asymptotic sentence is not an example-specific theorem.

**Finite-trace correspondence verdict:** **Faithful specialization**.  
**Finite-trace difficulty verdict:** **Strengthened / harder**.

**Extension-asymptotic correspondence verdict:** **Not represented in Lean**.  
**Extension-asymptotic difficulty verdict:** **Indeterminate**.

### 7.7 Theorem 6.8: corrupted incomparability

**Paper statement.** For every `k≥1`, `k-CtrId` and `k-TxtId` are incomparable. One direction uses the fixed co-singleton class. The reverse direction uses a class `H_k={A∪B_i}` with pairwise disjoint blocks of size `k+1` and a nonempty common-negative region (Theorem 6.8, PDF p. 11; proof pp. 19–20).

**Lean theorem.**

```lean
theorem theorem_6_8
    (k : ℕ) (hk : 1 ≤ k) :
  (KContrastivelyIdentifiable k coSingletonFamily ∧
    ¬KTextIdentifiable k coSingletonFamily) ∧
  (KTextIdentifiable k (robustBlockFamily k) ∧
    ¬KContrastivelyIdentifiable k (robustBlockFamily k))
```

(`CorruptedIncomparability.lean:L7090`). `robustBlockFamily k` arithmetically codes:

- an infinite common core at residues `0 mod 4`;
- blocks of exactly `k+1` points at residues `2 mod 4`, separated using `Nat.pair`;
- common-negative points at residues `1 mod 4`.

The reverse witness depends on `k`, exactly as the paper's construction does. The co-singleton identifier is uniform across budgets; the block text identifier may depend on the known `k`.

**Access audit.** The block learner is again semantic. `robustBlockTextIdentifier` classically chooses an index of a complete block if one exists. No bounded search, decidable block-index recovery, or computability theorem appears, even though the arithmetic representation suggests one could be developed.

**Correspondence verdict:** **Faithful specialization**.  
**Difficulty verdict:** **Preserved** at the semantic level; the absent computability interface is recorded separately.

### 7.8 Unformalized extensions

The following numbered paper interfaces have no target-scope counterpart:

- `k-CtrGen` and `Fin-CtrGen` (Definition E.1, PDF p. 21);
- the co-singleton identify-then-generate lift (Remark E.2, PDF p. 21);
- `μ`-random i.i.d. contrastive presentations and almost-sure coverage (Definition E.3, PDF p. 22).

There is no probability measure, almost-sure event, random graph, sample-density threshold, spectral algorithm, message passing, or stochastic rate in the bundle.

**Correspondence verdict:** **Not represented in Lean**.  
**Difficulty verdict:** **Indeterminate**.

## 8. Helper and link-condition dependency graph

This section follows only declaration types and definition bodies.

### 8.1 Theorem 4.7

The top-level path is:

`ContrastivelyIdentifiable F`

→ `lemma_4_6_inclusion` → `TextIdentifiable F`

and

`ContrastivelyIdentifiable F`

→ `contrastiveIdentifiable_nonEliminabilityContained` → `NonEliminabilityContained (range F)`

while the reverse path is:

`TextIdentifiable F`

→ imported semantic tell-tale necessity → `ConditionTwo F`

plus

`NonEliminabilityContained (range F)`

→ `contrastiveTellTaleLearner_identifies`

→ `ContrastivelyIdentifiable F`.

The geometric replacement is:

`NonEliminabilityContained 𝓗 ↔ IncomparablePairsOverlap 𝓗`.

The necessity branch's non-eliminability link uses:

1. common-vertex coverage for `h` against `g`;
2. failure of `h⊆g`;
3. a helper deriving common-vertex coverage for `g` against `h`;
4. Lemma 4.4 to obtain one shared stream;
5. convergence of the same deterministic identifier on that stream to force equality of target supports.

The sufficiency branch's hard inputs are finite tell-tales and the geometric containment condition. Neither is the desired contrastive identifier, but together they encode precisely the finite positive-data discrimination and pairwise elimination content. The remaining least-index stabilization is bookkeeping over finitely many lower indices.

**Circularity check:** no cycle occurs at the proposition level. The imported implication `TextIdentifiable→ConditionTwo` does not assume contrastive identification. `hrel` does not assert that the learner converges.  
**Inhabitedness check:** the main theorem's properness and infinite countable domain guarantee legal contrastive presentations and the local enumerations used by the bridges.  
**Difficulty assessment:** the central characterization is preserved; effectivity is not.

### 8.2 Theorem 5.4

The sufficiency path is:

`ContrastiveClosureDimensionAtMost 𝓗 d`

+ target membership in the version space

+ at least `d+1` distinct unordered edges

→ current edge set is not hollow

→ a closure point exists outside the observed vertices

→ classical choice defines the output

→ output lies in every consistent support, hence in the target.

The necessity path is:

proposed uniform generator at `d+1`

+ any hollow edge set of size at least `d+1`

→ run the generator on an orientation of exactly those edges

→ if output is incident to `E`, novelty fails;

→ otherwise hollowness says the output is not in the closure, so some version-space target excludes it and precision fails.

**Circularity check:** the dimension bound does not mention a generator, and uniform generation does not mention dimension.  
**Vacuity check:** on an empty class, uniform obligations are vacuous and there are no hollow sets; both sides are true, as expected. At a positive threshold, histories below threshold create no obligation.  
**Hardness delegation:** membership in the semantic intersection and selection of an element are noncomputable; no closure oracle is formalized.  
**Difficulty assessment:** semantic combinatorial difficulty is preserved and generalized.

### 8.3 Theorem 5.5

Necessity uses the levels on which a given generator already satisfies a fixed threshold. These levels automatically form an increasing cover and each has a uniform generator at its defining threshold; Theorem 5.4 supplies finite dimension.

Sufficiency receives:

- a monotone cover whose union is exactly the target class;
- a proof that each level has some finite dimension bound.

It classically chooses one bound per level, pads it by the level index, and selects the largest active level. The cover premise does not supply the final global generator, and the finite-dimension premises do not state non-uniform generation. The max-active-level construction is substantive but information-theoretic.

**Circularity check:** none.  
**Potential vacuity:** the empty class is covered by empty levels and is trivially generatable.  
**Difficulty assessment:** preserved semantically, weakened as an algorithmic interface.

### 8.4 Theorems 5.13–5.14

The target-scope dependency graph is componentwise:

- `CtrId→CtrGen`: current identified support + infinitude → choose fresh point;
- `CtrId→TxtId`: least-unseen simulation;
- `TxtId→TxtGen`: current identified support + infinitude → choose fresh point;
- finite-family obstruction: supplied shared stream + supplied finite exact intersection → contradiction;
- punctured witness: supplied eventual core → `CtrGen`; absence of tell-tale → `¬TxtId`; then inclusion yields `¬CtrId`;
- disjoint witness: first-positive text identifier + one explicit shared contrastive stream + empty intersection → `TxtId ∧ TxtGen ∧ ¬CtrGen`.

No node supplies `CtrGen→TxtGen`, and no node certifies text generation of the punctured class. These are the exact missing links in the strict diamond.

### 8.5 Proposition 6.3

The exact-infimum graph is:

positive defect point

→ first incident occurrence in any clean presentation

→ wrong-cut occurrence for `g`

→ injection from defects to violation times

→ universal lower bound.

For the matching upper bound:

- finite defects are each paired once with an `h`-negative point;
- nondefects are paired along common-crossing edges;
- a common-crossing nondefect exists for proper nontrivial cuts;
- countability supplies an enumeration;
- infinite defects force extended count `⊤`.

The theorem separately proves the set of clean violation counts is nonempty before taking its infimum. No empty-infimum convention collapses the claim.

### 8.6 Theorem 6.6

The named absence-count helper chain is:

finite corruption

→ true center omitted at most `k` times

and

positive-side coverage + only finitely many corruptions

→ every false center omitted infinitely often

→ false absence count eventually exceeds `k`.

A low-count candidate must have appeared among endpoints of the first `k+1` observations, giving a finite competitor set. Once the true center is seen, every arbitrary minimizer is eventually the true center.

This chain is noncircular and mathematically substantive. The audit limitation is formal-interface linkage: the final theorem type existentially quantifies an unnamed identifier, while the helpers name `absenceCountIdentifier`. The proof body may connect them, but proof bodies are excluded from evidence.

### 8.7 Theorem 6.8

The co-singleton direction composes:

- `theorem_6_6` → `KContrastivelyIdentifiable k` for every `k`;
- budget antitonicity + `theorem_6_5` → `¬KTextIdentifiable k` for `k≥1`.

The block direction composes:

- exact block cardinality `k+1` and disjointness → no false block can be completely seen using at most `k` corrupted text occurrences;
- target coverage → the true block is eventually complete;
- an explicit clean stream is valid for two distinct block supports;
- a clean shared stream is also `k`-corrupted for every `k`, so no contrastive identifier can distinguish those targets.

No hypothesis already asserts either separation.

## 9. Vacuity, circularity, consistency, and inhabitedness audit

| Interface/result | Audit finding |
|---|---|
| `IsContrastivePresentation` | Empty or universal supports have no valid presentation on a nonempty domain because no edge can cross. Main identification theorems exclude them; several general helper theorems do not. |
| `ContrastivelyIdentifies` / `GeneratesFrom` | Both are implications from presentation validity. They are vacuous for targets with no valid presentation. This matters for generalized Proposition 5.11 and some arbitrary-class statements. |
| `proposition_4_2` | Explicit `x₀∈h` rules out empty `h`; the enumeration premise is satisfiable under the paper's countability assumptions. |
| `lemma_4_4` | Explicit `x₀∈h∪g` rules out an empty union. The supplied union enumeration is a genuine representation witness. |
| `theorem_4_3` | Region implications may be vacuous when antecedent regions are empty, but the biconditional correctly captures those cases. |
| `theorem_4_7` | Properness removes presentation vacuity. `TextIdentifiable` plus overlap is not the conclusion in disguise; each condition rules out a distinct failure mode. |
| `InfiniteSafeCores` | Very strong: it already supplies infinitely many universally safe points at every valid prefix. It nearly contains the pointwise output existence but not one global generator. |
| `IsEventualCore` | Supplies an injective tail eventually contained in every target. The existence of this core is the hard content; the generator is a semantic selection wrapper. |
| Uniform threshold definitions | Obligations are vacuous below the threshold. Threshold `0` additionally activates the empty history in Lean, motivating the positive-threshold repair. |
| `FiniteContrastiveClosureDimension` | If no hollow set exists, every natural is an upper bound and the least exact bound is `0`; this matches the paper's empty-supremum convention. |
| `theorem_5_5_sufficiency` | The cover and per-level finite bounds are strong but consistent; neither supplies the global max-active-level generator. |
| `proposition_5_12` | The shared stream and finite exact intersection are explicit obstruction certificates, not the non-generation conclusion itself. |
| Corrupted identification definitions | They are implications and can be vacuous for nonexistent corrupted presentations. Co-singleton and block theorems use classes with explicit valid presentations, so their conclusions are nonvacuous. |
| `theorem_6_5` | Nonvacuous because one concrete stream is a one-corrupted text for multiple distinct targets. |
| `theorem_6_6` | No hypotheses; nonvacuous because co-singleton targets admit infinitely many clean and finitely corrupted presentations. |
| Defect infimum | Clean presentations are proved to exist under theorem assumptions, so `sInf` is not taken over an empty set. |
| `theorem_6_8` | Both witnesses have distinct supports and explicit valid streams; neither separation is vacuous. |

No displayed primary hypothesis is inconsistent under the paper's intended countably infinite domain. No primary theorem is tautological after unfolding. The closest cases to “conclusion supplied as input” are safe cores, eventual cores, and the explicit shared-stream/finite-core obstruction; these are appropriately classified as strong sufficient certificates rather than characterizations.

## 10. Computability, oracle, and information-access audit

| Result/interface | Target/index or correct-answer access | Enumeration and representation | Oracle/certificate access | Future data | Computability/runtime status |
|---|---|---|---|---|---|
| Contrastive identification definition | Learner is not given target index `z`; it sees only finite edge history. It may be selected as a function of the whole indexed family. | Family is an indexed sequence; edge orientation is visible. | None in the runtime type. | No. Only `Fin t` prefix. | Arbitrary total Lean function; no `Computable` predicate. |
| Theorem 4.7 necessity | No target answer supplied. | `[Countable α]` yields a noncomputable surjection; paper's fixed enumeration is not an explicit effective input. | A successful contrastive identifier is supplied as the premise. | No. | Semantic reduction only. |
| Theorem 4.7 sufficiency | No target answer supplied. | Index order is used for least eligible candidate and stable representative. | Finite tell-tales and geometric containment are available semantically; arbitrary set membership and crossing consistency are propositions, not decidable procedures. | No. | `chosenTellTale` and learner are noncomputable; no oracle machine. |
| Proposition 5.8 | No target identity supplied to generator. | Extensional class `𝓗`; arbitrary domain. | The premise certifies an infinite semantic intersection at every valid prefix. Generator classically chooses a point. | No. | Noncomputable; no closure-membership procedure. |
| Proposition 5.11 | No target identity supplied. | Explicit injective core sequence is supplied. | Eventual-core certificate supplied; no membership oracle is used by the generator. | No. | Choice of a fresh pairing-fiber coordinate is noncomputable. |
| Theorem 5.4 | No target identity supplied. | Finite unordered edge set derived from ordered input. | Full semantic access to version-space intersections through an existential test; no explicit ERM or closure-membership oracle. | No. | Noncomputable output choice; no runtime or oracle-call bound. |
| Theorem 5.5 | No target identity supplied. | Countable chain is a witness; level index and selected dimension bounds are semantic data. | Cover and finite-dimension certificates supplied; numerical bounds chosen classically. | No. | Noncomputable largest-active-level/closure construction; no effective theorem. |
| Hierarchy inclusion generators | Current guessed index is available because it is the identifier's output, not the true target. | Indexed family. | Infinitude proof supplies existence of a fresh point. | No. | Fresh point selected by classical choice. |
| Proposition 5.12 | No target answer supplied to generator. | Finite family, explicit stream, explicit finite intersection. | The obstruction witnesses are given in full. | The proof statement quantifies an entire stream as certificate, but the attacked generator still receives prefixes only. | Pure impossibility theorem; no algorithm. |
| `k`-corrupted identification | In `k-CtrId`, the chosen identifier may depend on known `k`; in `Fin-CtrId`, the identifier has no `k` argument and must work for all. | Indexed family and ordered edges. | No corruption locations are supplied. | No. | Semantic functions. |
| Co-singleton absence statistics | No target hole supplied. | Domain `ℕ` and finite seen endpoints; decidable equality is available. | No class oracle needed for counts. | No. | Counts are finitary, but the identifier uses `Classical.choose`; no computability theorem. |
| Robust block text learner | No target block index supplied. | Arithmetic block coding depends on known `k`. | Existence of a complete block is tested propositionally and an index is chosen classically. | No. | Noncomputable; no bounded search theorem. |
| Defect infimum | Not a learner. | Sets, extended cardinality, and literal `sInf`. | Full set-theoretic cardinal/infimum access. | Entire presentation sets are quantified mathematically. | Noncomputable invariant, no estimator. |

### 10.1 Comparison with the paper's oracle discussion

The paper says:

- Theorem 4.7's identifier needs a tell-tale family in addition to consistency access.
- Theorem 5.4's closure generator needs ERM/nonempty-version detection and closure-membership access.
- Theorem 5.5 needs the chain and per-level dimensions.
- Algorithm 1 is fully constructive and needs no class oracle (Appendix E.3, PDF p. 22).

Lean confirms the first three only at the level of semantic dependence: the relevant witnesses appear as propositions, class parameters, or classical choices. It does not formalize the proposed oracle hierarchy or prove an algorithm from those oracles. For the fourth claim, Lean falls short: it formalizes the finite statistic but not a computable tie-broken minimization or a theorem that the named algorithm is the `Fin-CtrId` witness.

### 10.2 No hidden access to target or future samples

No target-scope learner receives the true target index, the correct answer, corruption locations, or future observations as an explicit argument. Supplied streams in impossibility or existence certificates are theorem-level quantified objects; generator/identifier outputs still depend only on finite prefixes. The principal extra access is instead **semantic class access** through arbitrary functions and classical choice.

## 11. Difficulty-preservation assessment

### 11.1 Preserved central mathematical difficulty

The following interfaces contain the hard mathematical content rather than assuming it:

- the four-region common-crossing equivalence;
- the semantic contrastive-identification characterization;
- the exact `d+1`/dimension-bound biconditional;
- the increasing finite-dimension cover characterization;
- the finite-family shared-input contradiction once its witnesses are supplied;
- the exact extended-cardinal defect infimum;
- the one-corruption text impossibility;
- the budget-independent co-singleton existence result;
- both corrupted separation witnesses.

### 11.2 Strengthened or harder statements

- `theorem_4_3` applies to arbitrary sets rather than distinct proper supports.
- `theorem_4_7_geometric_equivalence` applies to arbitrary extensional classes.
- Theorems 5.4 and 5.5 apply to arbitrary extensional classes, not only countable ones.
- The named `safeCoreGenerator_spec` helper certifies a safe unseen output at every prefix under the infinite-closure premise; the public Proposition 5.8 itself retains only the paper's eventual conclusion.
- Proposition 6.3 works on countable finite or infinite domains and uses literal extended-natural infima.
- Example 6.7 has an explicit unique-minimizer theorem, stronger than merely listing counts.

### 11.3 Weakened or easier interfaces

- All general learners and generators may be noncomputable semantic functions.
- Proposition 5.11 drops properness, permitting vacuous targets with no contrastive presentation.
- Proposition 5.12 receives both the shared stream and the exact finite intersection.
- Theorem 5.5 selects dimension bounds by classical choice rather than requiring an effective sequence.
- The absence-count and robust-block identifiers use arbitrary classical witnesses rather than executable tie-breaking/search.
- The full hierarchy theorem is replaced by components, omitting difficult global links.

### 11.4 No collapsed central theorem

No central characterization is reduced to a premise literally identical to the conclusion. The safe-core and eventual-core propositions are reductions from strong certificates, but they remain mathematically meaningful sufficient conditions. The defect theorem explicitly proves nonemptiness and attainment/lower bounds rather than exploiting lattice defaults.

## 12. Source defects, ambiguities, and Lean repairs

### 12.1 Printed Example 5.9 versus appendix repair

**Literal source issue.** Example 5.9 says `supp(h∞)=A` and `supp(h_m)=A∪{b_m}`, but then describes a non-covering barrier “between `h∞` and any `h_m`” and calls those supports incomparable (PDF p. 9). Literally, `A⊊A∪{b_m}`, so that pair is comparable and cannot witness the incomparable-pair obstruction in Theorem 4.7. The intended comparison must be between two distinct augmented supports `h_m,h_r`. Even then, the printed assumptions merely say that `A⊊X` is infinite and that `{b_m}` enumerates `X\A`; without an explicit distinctness/size condition on the complement, two augmented supports can cover `X`, so a common-negative point is not guaranteed.

**Source repair.** The full hierarchy proof compares `h_m` and `h_r` for `m≠r` and instead assumes disjoint infinite `A,B` with `X\(A∪B)≠∅` (PDF p. 18). Those strengthened assumptions make the supports incomparable, intersecting, and non-covering.

**Lean status.** Neither version is formalized. Lean repairs the strictness theorem at the result level by using the punctured class, which is a different valid witness.

**Literal correspondence verdict:** **Not represented in Lean**.  
**Literal difficulty verdict:** **Indeterminate**.  
**Repaired-result correspondence verdict:** **Related but materially different**.  
**Repaired-result difficulty verdict:** **Preserved**.

### 12.2 Theorem 5.4 at dimension zero

**Source ambiguity.** “Sample complexity `d+1` is necessary” is unambiguous when rounds/thresholds are positive. If a formal model includes the empty prefix and allows threshold zero, dimension zero does not universally imply that threshold one is the least natural threshold.

**Lean repair.** `IsLeastPositiveUniformThreshold` minimizes only over `k>0`. The quantitative biconditional at `d+1` remains exact.

**Literal correspondence verdict:** **Related but materially different** at the zero boundary.  
**Repaired theorem status:** mathematically sound and faithful to the paper's positive-round convention.  
**Difficulty verdict:** **Preserved**.

### 12.3 `⊥` versus `∅` for inconsistent closure

The paper uses a sentinel `⊥`; Lean uses the empty set. This could be unsound if an inconsistent version space were treated as an empty common core without remembering inconsistency. Lean repairs the interface by explicitly requiring version-space nonemptiness in hollowness and by using target membership for valid histories. No headline theorem is collapsed by the encoding.

**Correspondence verdict:** **Related but materially different**.  
**Difficulty verdict:** **Preserved**.

### 12.4 Finite histories versus extendible stream prefixes

The paper's uniform lower bound discusses extending a finite edge set to a valid presentation. Lean defines uniform correctness directly on all finite crossing histories, so no extension premise is needed. For positive thresholds and proper targets this is faithful; at threshold zero it contributes to the boundary issue above.

**Correspondence verdict:** **Faithful generalization**.  
**Difficulty verdict:** **Strengthened / harder**.

### 12.5 Proposition 6.3 assumption slack

Lean retains `h≠g` in both defect theorems, although the displayed exact equality does not use distinctness at the proposition level. The zero-defect theorem also carries a properness argument for `g` that is not needed by its displayed conclusion. This is redundant source-aligned assumption, not a faithfulness defect and not a repair.

### 12.6 Constructive co-singleton claim not repaired

The paper's fixed-enumeration minimization is computable on a finite set (PDF p. 22). Lean could in principle formalize that algorithm, but the current bundle does not: the minimizer is selected noncomputably and no theorem links the named identifier to Theorem 6.6 at the type level. This is a genuine remaining gap, not a Lean repair.


### 12.7 The overview's general infinite-defect identification criterion is not stated as a theorem

Section 1.1 says that if `κ(h→g)=∞` between every pair of distinct hypotheses, then finite-corruption identification is possible by violation counting (PDF p. 3). Section 6 proves the exact defect identity and then the co-singleton instance, but the supplied PDF contains no numbered class-level theorem, no exact quantifier statement, and no general candidate-selection/stabilization argument for this implication. Proposition 6.3 by itself is pairwise and does not name a learner.

This audit therefore treats the sentence as an **unsupported overview-level generalization in the supplied version**, not as a numbered theorem that Lean should receive credit for formalizing. It may be true and derivable, but that is indeterminate from the permitted evidence. Lean neither states nor repairs it.

**Literal correspondence verdict:** **Not represented in Lean**.  
**Difficulty verdict:** **Indeterminate**.

## 13. Missing paper results and claims

The following paper content is absent as a target-scope declaration or complete theorem:

1. Theorem 3.5 (informant identification) and Theorem 3.7 (universal text generation).
2. Theorem 4.3's explicit N1/N2/N3 case classification.
3. Lemma 4.4's mutual-non-eliminability corollary as a standalone theorem.
4. Example 5.7's infinite contrastive closure dimension and hollow witnesses.
5. Example 5.9, both printed and appendix-repaired versions.
6. The family common crossing graph, confusability complex, Proposition B.1, Proposition D.1, and Example D.2.
7. The full strict-chain statement of Theorem 5.13, especially `CtrGen⊆TxtGen` and a target-scope witness for `TxtId⊊TxtGen`.
8. The main-results overview's general “infinite pairwise defects imply finite-corruption identification” criterion.
9. The co-singleton mechanism `Γ(h_s,h_t)={{s,t}}` and `κ(h_s→h_t)=∞` as explicit theorem statements.
10. A theorem that the named absence-count identifier, with fixed-enumeration tie-breaking, witnesses Theorem 6.6.
11. A computability/oracle-free theorem for Algorithm 1.
12. Example 6.7's extension-specific asymptotic statement.
13. Definition E.1, Remark E.2, Definition E.3, and all probability/statistical extensions.

## 14. Substantive extra Lean results

The following target-scope declarations strengthen, decompose, or make explicit content not separately claimed as a numbered paper result. Each is classified relative to the paper as requested.

| Lean declaration/content | Why extra | Correspondence verdict | Difficulty verdict |
|---|---|---:|---:|
| `theorem_4_7_geometric_equivalence` for arbitrary classes | Paper includes the equivalence only inside Theorem 4.7 under its standing setting | Extra Lean result not claimed by the paper | Indeterminate |
| `contrastiveIdentifiable_nonEliminabilityContained` as an exposed direction | Paper gives it as part of Theorem 4.7 | Extra Lean result not claimed by the paper | Indeterminate |
| `contrastiveTellTaleLearner_identifies` with explicit `ConditionTwo` and geometric premises | Exposes the exact semantic sufficiency interface | Extra Lean result not claimed by the paper | Indeterminate |
| `theorem_5_4_quantitative` for every upper bound `d` | Stronger formulation than only exact-dimension classes | Extra Lean result not claimed by the paper | Indeterminate |
| `hollow_cardinality_lower_bound` | Direct witness-wise lower-bound theorem | Extra Lean result not claimed by the paper | Indeterminate |
| Separate `theorem_5_5_necessity` and `theorem_5_5_sufficiency` | Directional decomposition of Theorem 5.5 | Extra Lean result not claimed by the paper | Indeterminate |
| Punctured witness explicitly includes `¬CtrId` | Paper uses it primarily for `CtrGen⊄TxtId`; `¬CtrId` follows from the hierarchy | Extra Lean result not claimed by the paper | Indeterminate |
| `isContrastivePresentation_iff_zeroCorrupted` | Explicit bridge between clean and zero-corruption models | Extra Lean result not claimed by the paper | Indeterminate |
| `exists_clean_contrastive_presentation` | Explicit presentation-existence theorem under countability/properness | Extra Lean result not claimed by the paper | Indeterminate |
| `exists_clean_presentation_wrongCutCount_eq_defect` | Exact finite-defect attainment, stronger than only infimum equality | Extra Lean result not claimed by the paper | Indeterminate |
| `example_6_7_unique_minimizer` | Strengthens the displayed count vector to uniqueness over all seen endpoints | Extra Lean result not claimed by the paper | Indeterminate |
| Arithmetic block coding and exact block-cardinality theorems | Concrete support-isomorphic implementation of the paper's abstract blocks | Extra Lean result not claimed by the paper | Indeterminate |

Low-level endpoint, finite-set, monotonicity, and classical-choice specification lemmas are omitted from this “substantive extra” list because they are implementation links rather than independent mathematical claims.


## 15. Headline, overview, and conclusion-level claims

The abstract, Section 1.1, Section 1.2, and the conclusion make several aggregate claims that are broader than any single numbered theorem. This table audits those claims separately so that partial formal coverage is not mistaken for full headline coverage.

| Paper headline or overview claim | Statement-level Lean coverage | Correspondence verdict | Difficulty verdict | Audit conclusion |
|---|---|---:|---:|---|
| The only obstruction added by contrastive data beyond text identification is failure of incomparable supports to overlap and cover `X` (Abstract; Main result (1), PDF pp. 1–3) | `theorem_4_7`, `theorem_4_7_identifier_equivalence`, and `theorem_4_7_geometric_equivalence` | Faithful specialization | Preserved | The semantic characterization is strongly represented for countably indexed families over countably infinite domains. The non-eliminability bridge has explicit enumeration/nonemptiness inputs, and no effective learner is claimed. |
| One common-crossing coverage identity controls pairwise ambiguity (Technical overview, PDF pp. 3–4) | `proposition_4_2`, `theorem_4_3`, and `lemma_4_4` | Faithful generalization | Preserved | The set-theoretic coverage core is represented in broader scope. The named N1/N2/N3 classification and the final mutual-non-eliminability corollary are not separately stated. |
| Contrastive closure dimension exactly characterizes uniform generation, with tight distinct-edge sample complexity `CΔ+1` (Abstract; Main result (2); Technical overview, PDF pp. 1,3–4) | `theorem_5_4`, `theorem_5_4_quantitative`, and `theorem_5_4_sharp_sample_complexity` | Faithful specialization | Preserved | The qualitative and quantitative content is present. The least-threshold theorem is deliberately restricted to positive thresholds at the zero-dimensional boundary. |
| The non-uniform contrastive-generation variant is exactly an increasing union of finite-dimension levels (Main result (2); Technical overview, PDF pp. 3–4) | `theorem_5_5` with separate necessity and sufficiency declarations | Faithful generalization | Strengthened / harder | Quantifier order is retained and the class scope is broader, but the construction remains noncomputable and consumes a supplied cover plus classically selected bounds. |
| The four clean families form a strict diamond, with `CtrGen` and `TxtId` incomparable (Abstract; Main result (3); Figure 1, PDF p. 3) | General inclusions plus punctured and disjoint witnesses | Related but materially different | Weakened / easier | Mutual incomparability is represented by faithful concrete witnesses. The full strict diamond is not stated or derivable from target-scope declarations alone because `CtrGen⊆TxtGen` and a target-scope `TxtId⊊TxtGen` witness/link are absent. |
| Finite-family confusability, not merely pairwise ambiguity, governs negative generation results (Technical overview; Section 5.2; Appendix D, PDF pp. 4,9,20–21) | `proposition_5_12` only, with a shared stream and exact finite intersection supplied | Related but materially different | Weakened / easier | The contradiction theorem is present, but the family common-crossing graph, coverage criterion, confusability complex, membership-pattern criterion, and three-way counterexample are missing. |
| Finite adversarial corruption reverses the clean comparison: the co-singleton class is robustly contrastively identifiable by one budget-independent method but not one-corruption text identifiable (Abstract; Main result (4), PDF pp. 1,3) | `theorem_6_5` and `theorem_6_6` | Faithful specialization | Preserved | The class-membership statements are exact at the semantic level. The theorem type for 6.6 does not name the absence-count identifier, and no computability/tie-breaking theorem preserves the paper's algorithm-specific claim. |
| Infinite pairwise defect gaps yield finite-corruption identification by violation counting (Main result (4); Technical overview, PDF pp. 3–4) | Exact defect identity plus co-singleton instance, but no general identification theorem | Related but materially different | Weakened / easier | Lean formalizes the invariant and a concrete robust class, not the advertised general sufficient principle. |
| The common crossing graph unifies pairwise ambiguity, family-level generation obstructions, and corruption defects (Abstract; Technical overview; Conclusion, PDF pp. 1,3–4,11) | Pairwise geometry and defect geometry are formalized; finite-family geometry is not | Related but materially different | Weakened / easier | Two of the three advertised scales are represented. The family-scale part is delegated to a supplied shared stream rather than derived from a common-family graph. |
| General characterizations are information-theoretic, whereas the co-singleton algorithm is fully constructive and oracle-free (Remarks 4.8, 5.6; Appendix E.3, PDF pp. 7–8,22) | General constructions are noncomputable as advertised; co-singleton minimization is also noncomputable | Related but materially different | Weakened / easier | Lean preserves the nonconstructive status of the general results but loses the paper's constructive separation for Algorithm 1. |
| Statistical/random-presentation and corrupted-generation extensions remain open (Conclusion and Appendix E, PDF pp. 11,21–22) | No corresponding probability or corrupted-generation interfaces | Not represented in Lean | Indeterminate | This is expected for open material, but it is a genuine coverage gap if the target is a complete formal transcription of all definitions in the supplied paper. |

## 16. Coverage gaps and target-scope declaration ledger

### 16.1 Coverage of substantive target-scope Lean declarations

Every substantive declaration in the `GenLimit.Paper28_ContrastiveIdentificationAndGeneration` family falls into one of the audited clusters below. Low-level endpoint rewrites, finite-set bookkeeping, and specification lemmas are treated as links in Section 8 rather than independent paper correspondences.

| Target-scope cluster | Substantive declarations covered | Audit location |
|---|---|---|
| Common-crossing geometry | `Edge`, `Crosses`, `CommonCrossing`, `Incident`, `commonVertices`, four-region definitions, `theorem_4_3`, `IsContrastivePresentation`, `NotEliminableFrom`, `proposition_4_2`, `AdmitCommonPresentation`, `lemma_4_4` | Sections 2.2–2.3, 3.2, 4.1–4.3, 8.1 |
| Identification geometry | `Incomparable`, `OverlappingCover`, `NonEliminabilityContained`, `IncomparablePairsOverlap`, both directional implications, `theorem_4_7_geometric_equivalence` | Sections 3.2, 4.5, 8.2, 14 |
| Contrastive identification | identifier/output/convergence definitions, `AllProperNontrivial`, `lemma_4_6_inclusion`, necessity of relation containment, eligibility/tell-tale learner interfaces, sufficiency theorem, both Theorem 4.7 equivalences | Sections 2.1, 3.2, 4.4–4.5, 8.2, 10.2 |
| Ordinary generation and cores | finite-prefix/seen definitions, `GeneratesFrom`, `ContrastivelyGeneratable`, edge version space/closure, `InfiniteSafeCores`, `proposition_5_8`, `IsEventualCore`, `proposition_5_11` | Sections 2.4, 3.3, 5.5–5.7, 8.5, 9.2–9.3 |
| Uniform closure dimension | unordered-edge carrier, distinct-edge and closure definitions, hollowness, bound/equality predicates, uniform threshold predicates, closure generator, quantitative/qualitative/sharp theorems, hollow lower bound | Sections 2.2, 3.3, 5.1–5.3, 8.3–8.4, 12.2–12.4, 14 |
| Non-uniform closure characterization | target-dependent generation predicate, generator levels, necessity, selected bounds and padded thresholds, sufficiency, `theorem_5_5` | Sections 2.4, 3.3, 5.4, 8.4, 10.3, 14 |
| Clean hierarchy and witnesses | identification-to-generation links, text-identification-to-generation link, semantic tell-tale necessity bridge, shared-presentation/intersection certificates, `proposition_5_12`, punctured class and separation, disjoint class and separation | Sections 3.3, 6.1–6.5, 8.5, 11, 14 |
| Corrupted presentations and text fragility | corrupted-presentation and corrupted-identification definitions, co-singleton support/family, `theorem_6_5` | Sections 2.5, 3.4, 7.1, 7.3, 8.6 |
| Absence-count development | finite/stream absence counts, true-center bound, false-center divergence, finite competitor reduction, `absenceCountIdentifier`, `theorem_6_6`, Example 6.7 declarations | Sections 3.4, 7.4–7.5, 8.6, 10.4, 12.6 |
| Corrupted incomparability | budget monotonicity, co-singleton component, robust block coding/cardinality, corrupted-text identifier, clean shared stream, reverse nonidentifiability, `theorem_6_8` | Sections 3.4, 7.6, 8.6, 10.4, 14 |
| Defect infimum | defect/violation/infimum definitions, lower-bound injection, presentation existence, exact finite-defect attainment, both Proposition 6.3 declarations | Sections 3.4, 7.2, 8.6, 9.4, 12.5, 14 |

No imported `Core`, `Dependency_Angluin1980`, `Paper02`, or `Paper08` result is counted as a Paper 28 primary result. Those declarations are used only to interpret or discharge Paper 28 interfaces, and their effectivity limitations are called out explicitly.

### 16.2 Principal paper-to-Lean coverage gaps

The most consequential absent or incomplete interfaces are, in descending order of impact:

1. **Full clean diamond theorem.** A single theorem should state the two strict chains and the `CtrGen`/`TxtId` incomparability, including `CtrGen⊆TxtGen` and `TxtId⊊TxtGen` at the same semantic interface.
2. **Algorithm-specific Theorem 6.6.** A theorem should name the fixed-enumeration absence-count identifier, state its tie-breaking rule, and prove it witnesses the single `∃I∀k` conclusion; a separate computability theorem is needed to support Appendix E.3's constructive claim.
3. **Finite-family common-crossing theory.** Proposition B.1, the confusability complex, Proposition D.1, and Example D.2 are needed to substantiate the advertised family-scale role of `Γ`.
4. **Punctured class has infinite closure dimension.** The explicit hollow sets and unbounded-cardinality conclusion from Example 5.7 are absent.
5. **Unordered-observation transport.** A quotient or canonical-orientation theorem should show that existence of learners over the oriented carrier is equivalent to existence in the paper's unordered-prefix model.
6. **General infinite-defect robustness criterion.** The overview's general implication from pairwise infinite defects to finite-corruption identification is not stated.
7. **Explicit geometric corollaries.** The N1/N2/N3 classification, mutual-non-eliminability confusability, and the co-singleton formulas for `Γ` and `κ` are not theorem types.
8. **Example 5.9 and source repair.** A corrected statement should explicitly require enough common-negative points, or use the appendix's stronger ambient decomposition.
9. **Open-section definitions.** `k-CtrGen`, `Fin-CtrGen`, identify-then-generate, and random contrastive presentations are absent.

### 16.3 Coverage is strongest where the paper is semantic

The most complete correspondences are Theorems 4.7, 5.4, 5.5, Proposition 6.3, Theorems 6.5–6.6 as semantic class-membership claims, and Theorem 6.8. Coverage is weakest where the paper relies on:

- quotient-level unordered observations;
- executable or oracle-specific algorithms;
- assembling a global hierarchy from imported universal results;
- higher-order finite-family geometry;
- examples whose auxiliary properties are part of the advertised separation;
- probabilistic or rate-sensitive extensions.

## 17. Prioritized conclusions

### Priority 1 — conclusions that materially affect a faithfulness score

1. **Rate the formalization as semantically strong but incomplete, not as an exact full-paper formalization.** The central existence and characterization theorems are present, but the full hierarchy, finite-family geometry, and algorithmic effectivity are not.
2. **Do not credit Algorithm 1's constructivity from Theorem 6.6 alone.** The theorem type is existential, the named identifier is noncomputable, and the tie-breaking/access claim is absent.
3. **Do not credit the full strict diamond from the two witness theorems.** They establish mutual incomparability and some strictness, but the target-scope library lacks the general `CtrGen⊆TxtGen` link and a complete `TxtId⊊TxtGen` package.
4. **Treat the oriented carrier as an unresolved representation gap.** It is likely removable by a semantic transport theorem, but that theorem is not supplied and learners can inspect orientation.
5. **Credit Proposition 6.3 highly.** Lean states the literal extended-natural infimum and proves a stronger-scope theorem without collapsing the empty-infimum case.

### Priority 2 — conclusions that affect local theorem grading

1. Theorem 4.7 is a faithful semantic specialization; its tell-tale access is nonconstructive exactly as the paper acknowledges.
2. Theorem 5.4 is faithful after the positive-threshold boundary repair; the `⊥`/`∅` encoding is guarded and does not trivialize the result.
3. Theorem 5.5 preserves the target-dependent threshold and increasing-cover quantifiers, but its selected bounds are semantic advice rather than computable inputs.
4. Proposition 5.12 is correct but easier at its public interface because the shared stream and finite intersection are supplied.
5. Proposition 5.11 is more general syntactically but easier semantically on targets with no valid presentations, because the conclusion can be vacuous there.
6. Theorem 6.8 is a faithful concrete specialization; the reverse block identifier is semantic/noncomputable rather than an effective implementation.

### Priority 3 — source and editorial conclusions

1. Example 5.9 should be cited with its appendix-strengthened assumptions or explicitly repaired; the printed statement is not sufficient without an infinitude/distinctness condition on the complement.
2. Theorem 5.4's zero-dimensional sample-complexity convention should be stated using positive thresholds or a first-round convention.
3. The paper's phrase “by a single budget-independent algorithm” has two separable components: the quantifier order `∃I∀k`, which Lean preserves, and executability of a named procedure, which Lean does not preserve.

## 18. Compact final verdict table for a consolidated 36-paper report

| Result cluster | Coverage in target-scope Lean | Correspondence verdict | Difficulty verdict | Access/effectivity status | Consolidated assessment |
|---|---|---:|---:|---|---|
| Pairwise common-crossing geometry: Proposition 4.2, Theorem 4.3, Lemma 4.4 | Core equivalences present; named regime/corollary pieces partial | Faithful generalization | Preserved | Classical witnesses and supplied enumerations; no oracle/computability claim | Strong semantic correspondence with minor representation and coverage gaps |
| Exact contrastive-identification characterization: Lemma 4.6, Theorem 4.7 | Main biconditionals present | Faithful specialization | Preserved | Information-theoretic semantic learner; chosen tell-tales; no effective construction | High-faithfulness central theorem |
| Uniform closure dimension: Theorem 5.4 | Qualitative, quantitative, and sharp forms present | Faithful specialization | Preserved | Noncomputable closure choice; no ERM/closure oracle complexity | High-faithfulness theorem with sound zero-boundary repair |
| Non-uniform closure chain: Theorem 5.5 | Both directions and full biconditional present | Faithful generalization | Strengthened / harder | Supplied chain and classically selected finite bounds; no effective procedure | Strong semantic correspondence, weaker algorithmic interface |
| Safe/eventual cores: Propositions 5.8 and 5.11 | Both sufficient conditions present | Related but materially different | Weakened / easier | Strong certificates are supplied; vacuity possible for presentationless targets | Correct reductions, not intrinsic characterizations |
| Finite-family obstruction: Proposition 5.12 and Appendix D | Obstruction present; geometry/complex absent | Related but materially different | Weakened / easier | Shared stream and exact intersection are supplied as certificates | Partial family-scale formalization |
| Clean diamond: Theorems 5.13–5.14 | Incomparability witnesses present; full strict chains incomplete | Related but materially different | Weakened / easier | Semantic/noncomputable witnesses; imported universal link not packaged | Material coverage gap |
| Defect identity: Proposition 6.3 | Literal `ℕ∞` infimum and zero clause present | Faithful generalization | Strengthened / harder | Semantic cardinal/infimum statement; no algorithm required | Very strong correspondence |
| Co-singleton reversal: Theorems 6.5–6.6 and Algorithm 1 | Membership theorems and finite statistics present; named computable algorithm not certified | Related but materially different | Weakened / easier | `∃I∀k` preserved; minimizer noncomputable; no tie-break/computability theorem | Mathematical reversal faithful, constructive claim incomplete |
| Corrupted incomparability: Theorem 6.8 | Both concrete separations present | Faithful specialization | Preserved | Semantic identifiers; arithmetic representation of blocks | High-faithfulness witness theorem |
| Whole-paper headline package | Central semantic results present; hierarchy, family geometry, constructivity, and open definitions incomplete | Related but materially different | Weakened / easier | Predominantly noncomputable semantic abstraction | **Substantially faithful core, incomplete full-paper coverage** |

## 19. Uncertainty and audit limits

Confidence is **high** for the transcription of paper statements, theorem numbering, page references, and Lean quantifier structure: the complete 23-page PDF was rendered and checked, and the relevant Lean declarations were read from the verified deterministic bundle. Confidence is also high that no proof body was needed to establish the correspondence verdicts above.

The following judgments carry narrower uncertainty:

- **Oriented versus unordered transport:** confidence is medium-high that semantic existence is transportable by a fixed classical orientation, but the equivalence is not a supplied theorem and no quotient-level audit was possible from statement types alone.
- **Duplicate indices:** confidence is high that Lean requires stabilization to one correct index; confidence is medium-high that this is harmless for extensional class learnability after a classical canonical-representative construction, which is not stated.
- **Theorem 5.4 at `d=0`:** confidence is medium that the paper intended a positive-round threshold convention. Lean's repair is mathematically sound, but the source does not spell out the boundary convention.
- **Example 5.9:** confidence is high that the printed assumptions do not, literally, guarantee the claimed pairwise non-covering obstruction unless the complement enumeration is understood to contain sufficiently many distinct points. The appendix supplies a stronger valid construction, but authorial intent beyond the printed text is indeterminate.
- **Algorithm-specific Theorem 6.6:** confidence is high that the membership theorem alone does not identify its witness, because doing so would require inspecting the proof term. The named finite minimizer is visibly noncomputable from its definition, but a separate computable implementation could be added without changing the class-membership theorem.

This audit makes no independent claim about proof correctness or successful compilation, because proof bodies and build results were outside the evidence used here. It makes no claim about the uninspected repository outside the supplied bundle and no claim that omitted paper material cannot be derived later. Verdicts concern only the supplied author PDF, target-scope declaration types, and the explicit definition bodies needed to interpret those types.
