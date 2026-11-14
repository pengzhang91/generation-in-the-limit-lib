# P03 Overview: Stage 2 statement-faithfulness comparison

Date: 2026-11-09 America/New_York (completed UTC timestamp is in the run record).

This is a completed comparison of all 13 requested declaration interfaces, with qualifications and unresolved source-model questions. It is not a proof audit, fresh Lean verification, or human review. Several components preserve the paper's mathematical task, but the 13 interfaces are not collectively an exact transcription. The main non-equivalences concern the semantic identification/tell-tale predicates, the effectiveness and quantitative content of the positive breadth certificates, and the opposite event used for the statistical unambiguity loss. The infinite-target scope of generation agrees with the introduction's contextual convention, which the later local theorem headers do not repeat.

## 1. Identity, scope, and evidence boundary

The authoritative source is *On the Limits of Language Generation: Trade-Offs Between Hallucination and Mode Collapse*, Alkis Kalavasis, Anay Mehrotra, Grigoris Velegkas, arXiv:2411.09642v3, 14 October 2025. The supplied `stage2/paper-arxiv-2411.09642v3.pdf` has 98 PDF pages and SHA-256 `097bda3ceeab7ddb244595b2817c8766f540b508abfe24a2ca8eaa0feecf3439`. No other edition or web source was consulted. Citations below give **printed page / one-based PDF page**, written `p. 27 / PDF 30`; the offset was checked on the displayed pages.

The frozen Lean input is the working-tree byte snapshot captured at `2026-11-10T01:29:42.007354+00:00`, recorded HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`, recorded dirty state true. Its scope module is `GenLimit.Paper03_HallucinationAndModeCollapse.Results.Overview`. Lean is pinned to `leanprover/lean4:v4.24.0`; the supplied manifest pins Mathlib to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. All 96 source/configuration files matched `lean-interface/snapshot.json`; all 118 Stage 2 manifest entries and all 16 interface manifest entries matched. These are input identity checks, not mathematical evidence from a successful build.

The completed, separate code-only Stage 1 report was present: `results/code-only-reconstruction.md`, SHA-256 `ac42c709b4ca0a380a9c8279260d4f1bed7e59871c1f14962ee238b00fca5d9a`; its run record has SHA-256 `6dd82b670c993f2610ccfa5a1a90427c910e3bbfd89bede4239f9aeb4ed1457a`. The paper inventory was made before consulting that reconstruction. Decisive comparisons were then rechecked in the original snapshot's declaration signatures and definition bodies, with the machine export as a cross-check. A correction to one Stage 1 prose sentence is recorded in section 7.

Scope is exactly Theorems 3.1-3.9, Propositions 3.10-3.12, and Theorem 3.13, against the 13 entries in `stage2/lean-interface/targets.txt`. Supporting definitions and source passages elsewhere are interpretive inputs, not extra headline targets. No `Results.Additional` coverage is credited. No old audit, PaperMap, owner record, or registry was consulted. The first independent draft was completed before the coordinator reviewed it. After that draft, the parent supplied the previously missed source locator p. 2 / PDF 5 and suggested an all-infinite variant of the illustrative loss-sign example; both were independently checked against the PDF and the relevant definitions before revision. This is disclosed post-draft model-coordinator review, not a human-review claim or an untouched independent first pass. Lean comments/docstrings, names, proof bodies/tactics, and compilation were not used as correspondence evidence. Source proof discussion is used only where identified as interpretation. Local standard-library bodies were not needed; the conventional semantics of PMF, `Set.encard`, filters, and computability are the disclosed library boundary.

All Lean paths below are relative to `stage2/source-snapshot/GenLimitLean/GenLimit/`. `P3/` abbreviates `Paper03_HallucinationAndModeCollapse/`. `H` abbreviates namespace `GenLimit.HallucinationModeCollapse`; all target identifiers have prefix `H.Results.`. Paths/identifiers locate evidence; their spelling does not establish meaning. Only the two requested Stage 2 outputs are retained. Source-page renderings were temporary visual-check intermediates and were removed, including the post-draft p. 2 rendering made inside the package. No library or frozen input was edited; no staging, committing, tracking change, or push occurred.

## 2. Independent source inventory

### Standing objects and conventions

- **Domain and presentations:** section 2, pp. 20-21 / PDF 23-24, fixes an infinite countable domain `X`, permits its replacement by `N` through a bijection, and defines an enumeration as a complete stream of target elements with repetitions allowed. The collection is an indexed countable list. Those section-2 domain conventions alone do not make each language infinite. However, the introduction explicitly says that the target `K` must be infinite for fresh generation to be well-defined (p. 2 / PDF 5). Because generation is required for every target in the collection, the contextual generation regime is an all-infinite family. Finite languages remain explicitly relevant to identification and to separate exhaustion conventions. Empty languages have no such endless element-valued enumeration; the source does not supply a pause symbol for them.
- **Information/computation:** section 2, p. 21 / PDF 24, supplies a family-membership oracle on `(i,x)`. Section 1.1.1, p. 4 / PDF 7, and section 3.1.1, p. 25 / PDF 28, describe learners as computable mappings; generated distributions are represented by sampling Turing machines. The exact distinction between an arbitrary oracle and an ordinary algorithm is not consistently explicit throughout the source. A subset oracle can be noncomputable (p. 9 / PDF 12). Proposition 6.5's discussion, p. 61 / PDF 64, treats membership in the selected language as decidable. This tension matters below.
- **Valid laws:** Definition 1, p. 4 / PDF 7, requires `supp(P)=K`, not containment. Samples in the statistical results are independent draws from that law. Definition 16, p. 36 / PDF 39, requires full marginal support on all `X`, with the deterministic correct positive/negative label for the target.
- **Identification:** Definition 10, p. 21 / PDF 24, requires eventual constancy of an index denoting the target, for every target and every presenting stream. Equation (4), p. 26 / PDF 29, counts a statistical error when the output language differs from `K`; footnote 11, p. 27 / PDF 30, explicitly allows repeated language indices.
- **Angluin condition:** Definition 11, p. 22 / PDF 25, asks for an index-to-tell-tale enumeration oracle, with `T_i⊆L_i` and no proper family sublanguage of `L_i` containing `T_i`. Literally it says a “set of finite strings,” which does not itself assert finite cardinality. Appendix B.1, pp. 91-92 / PDF 94-95, explicitly describes a *finite* tell-tale set; this is strong interpretive evidence for the finite-set reading, not a literal clause that should be silently inserted into Definition 11. The procedure/oracle requirement also must be kept separate from bare existence of one finite set per index.
- **Rates:** Definition 13, p. 26 / PDF 29 (and Definition 3, p. 4 / PDF 7), uses `∀P valid ∃c,C>0 ∀n, E er_n≤C R(cn)`, with constants depending on the law. The lower-bound meaning is `∀algorithm ∃P,c,C>0` and infinitely many `n` with `E er_n≥C R(cn)`. “No rate” is the positive-limsup assertion for some valid law against every algorithm. `R` tends to zero. The expression `R(cn)` is written despite a natural-number rate domain; rounding/extension is not specified. This does not affect a real exponential expression, but needs a convention for arbitrary `g`.
- **Nontriviality:** Definition 14, p. 26 / PDF 29, requires two distinct languages sharing an element. Definition 18, p. 49 / PDF 52, instead requires a finite subcollection with a common point and finite intersection. The infinite domain makes an empty intersection-of-no-languages unsuitable as its witness.
- **Fresh generation:** The introduction, p. 2 / PDF 5, explicitly requires infinite `K` and uses the support-failure event `supp(G_n)⊈K\S_n` in Equation (1). Equation (5), p. 27 / PDF 30, counts `output∉K\S_n` in the deterministic simplification. Remark 1 allows a deterministic output to stand for a point-mass sampler in this section. Definition 12, p. 23 / PDF 26, has an explicit exhausted-target exception for online deterministic generation; Equation (5) has no corresponding exception.
- **Breadth:** section 3.2.2, p. 29 / PDF 32, uses the failure event `supp(G_n(S_n))≠K\S_n`. Remark 2 and footnote 12 on that page discuss adding the training sample to the support, and the reverse rejection-sampling conversion. The reverse conversion presupposes that unseen support remains nonempty. Section 3.3, p. 31 / PDF 34, explicitly permits training repetitions for its relaxations.
- **MOP:** Definitions 5-6, p. 5 / PDF 8, and the restatement of Definition 5, p. 28 / PDF 31, mean decidability of membership in each trained generator's positive-probability support. Definition 6 literally quantifies over each history before asserting decidability. It does not explicitly assert a joint selector of deciders from histories. Surrounding source reductions that compute using MOP suggest a uniform operational reading; that suggestion is not a literal extra hypothesis.
- **Token generation:** Definition 15, p. 30 / PDF 33, uses a randomized next-token machine, auxiliary information, and an EOS stop. It halts on every input. Section 6.1, p. 58 / PDF 61, clarifies all realizations of its random bits and explicitly notes that the overall token process need not halt.
- **Stability and relaxations:** Definitions 7-8, p. 32 / PDF 35, require eventual equality of support sets on each enumeration, and strict symmetric-difference closeness to the target versus every distinct competitor. Cardinalities can be infinite. The displayed statistical “error” on that same page is literally the indicator of this *success* comparison. Definition 9 and Equation (6), p. 33 / PDF 36, require support contained in `K`, with only finitely many omissions; their error is the indicator of failure of that property. No quantitative bound on the finite omitted set is given.

### Numbered claims, inventoried independently

| Source claim and section | Location | Source components and quantifier order |
|---|---|---|
| Theorem 3.1, 3.1.2 | p. 27 / PDF 30 | For every identification-nontrivial countable collection: exactly one of `(∀g=o(n) ∃learner identifying at e^{-g(n)}, with exponential lower bound)` and `no rate`; the positive case iff Angluin's condition. Learner may depend on `g`, before the target law. |
| Theorem 3.2, 3.1.3 | p. 28 / PDF 31 | The local header says every countable collection; in the contextual infinite-target generation regime, one generator has exponential fresh-generation rate for every valid law. For generation-nontrivial collections, no generator beats exponential. Following prose additionally claims infinitely many new strings on the same high-probability training event. |
| Theorem 3.3, 3.2.2 | p. 30 / PDF 33 | For generation-nontrivial nonidentifiable collections: no MOP-decidable algorithm has any breadth rate; an algorithm in that class has exponential generation; arbitrary generators have the exponential lower bound. For identifiable generation-nontrivial collections: for each sublinear `g`, an algorithm in that class has breadth rate `e^{-g(n)}`; even generation without breadth cannot beat exponential. |
| Theorem 3.4, 3.2.3 | p. 30 / PDF 33 | For every token-by-token generator, support membership is decidable. The generator is fixed before the queried word. |
| Theorem 3.5, 3.2.4 | p. 31 / PDF 34 | Nonidentifiability rules out eventual breadth for every MOP-decidable algorithm. Identifiability supplies a MOP-decidable generator with eventual breadth. Remark 2 supports fresh and repetition-allowing formulations, subject to exhaustion. |
| Theorem 3.6, 3.3.1 | p. 32 / PDF 35 | For every nonidentifiable collection, every stable MOP-decidable algorithm is excluded from every statistical unambiguity rate. Literal preceding displayed loss counts success. |
| Theorem 3.7, 3.3.1 | p. 33 / PDF 36 | Same nonidentifiability/stability/MOP premises exclude eventual unambiguity on all target enumerations. Negating that universal success means some bad enumeration, not every enumeration. |
| Theorem 3.8, 3.3.2 | p. 34 / PDF 37 | Same premises exclude every approximate-breadth rate under Equation (6). |
| Theorem 3.9, 3.3.2 | p. 34 / PDF 37 | Same premises exclude eventual approximate breadth for every target enumeration. |
| Proposition 3.10, 3.4.1 | pp. 34-35 / PDF 37-38 | For every collection satisfying Angluin's condition, there is an exponential-rate identifier using a subset oracle; family membership remains standing information. |
| Proposition 3.11, 3.4.2 | p. 35 / PDF 38 | For every finite collection, there exists an exponential-rate identifier; languages themselves may be infinite. |
| Proposition 3.12, 3.4.3 | p. 35 / PDF 38 | For every countable collection of finite languages, there exists an exponential-rate identifier. No uniform size bound is required. |
| Theorem 3.13, 3.4.4 | p. 36 / PDF 39 | For every countable collection, an exponential-rate identifier exists under Definition 16's labeled laws. For identification-nontrivial collections every learner has the exponential lower bound. |

## 3. Formal dictionary and common comparison obligations

The following facts come from statement-relevant definition bodies, not comments or proofs.

| Meaning | Exact Lean evidence |
|---|---|
| Indexed sets and complete positive streams | `Generic.LanguageFamily = Nat → Set α`, `Core/GenericGeneration.lean:28`; `Generic.Presents = (range stream = L)`, same file:50. `Learner = List Info → Name`, `Core/Identification.lean:18`. |
| Eventual fixed name | `IdentifiesInLimit`, `Core/Identification.lean:53`, existentially chooses one correct name and then a stabilization threshold; `StabilizesTo`, same file:47. |
| Purely semantic identifiability | `H.IdentifiableInLimit`, `P3/Definitions.lean:104`, aliases `Angluin.SemanticallyInferrable`, `Paper00A_PositiveDataInference/Semantic/Definitions.lean:30`; its learner has no computability field. `SemanticallyIdentifies`, same file:24, quantifies every target and complete stream. |
| Bare finite tell-tales | `Angluin.ConditionTwo`, semantic definitions:52, is `∀i∃T : Finset Nat, IsTellTale C i T`; `IsTellTale`, same file:39, forbids proper sublanguages containing `T`. This is not `ConditionOne`, effective definitions:49, which requires one computable emission function. |
| Membership and subset oracles | `Core/Basic.lean:38`, `Core/SubsetOracle.lean:13`: correct Boolean queries; no ordinary computability certificate in either bundle. |
| All languages infinite in `OracleFamily` | `Core/OracleFamily.lean:17`, specifically field `infinite'` at:19. No restriction on number of distinct languages. |
| Statistical objects | `StatisticalIdentifier`, `P3/StatisticalModel.lean:33`, and `StatisticalGenerator`, `P3/GenerationModel.lean:17`, are `List Nat → PMF Nat`. No sampler or computability field. `ValidDistribution`, statistical model:29, is exact support equality. |
| IID histories and probability | `Support/DiscreteIID.lean:20` defines the length-`n` product list law; probability at:25 is the real outer measure of a discrete event. Ordered histories are preserved even when success predicates use their set of elements. |
| Identification and fresh output errors | `identificationError`, statistical model:40, averages `C(output index)≠C_i`; `generationError`, generation model:36, averages `y∉C_i ∨ y∈xs`, including output randomness. |
| Exponential rates | `ExponentialIdentifies`, statistical model:46; `ExponentialGenerates`, generation model:41; `ExponentialBreadth`, `P3/BreadthModel.lean:36`; and `ExponentialLabeledIdentifies`, labeled model:69: `∀i,p valid ∃c>0∃D>0∀n, e_n≤D exp(-cn)`. |
| Sublinear rates and no-rate | `AdmissibleSublinearExponent`, `P3/UniversalRates.lean:26`, requires nonnegative `g`, `g=o(n)`, and `g→∞`. `AlmostExponentialIdentifiable`, same file:39, chooses a semantic deterministic learner after `g`. `AchievesIdentificationRate`, same file:34, and `AchievesBreadthRate`, breadth model:27, have `D R(n)` with no argument rescaling. `NoIdentificationRate`, universal rates:45, and `NoBreadthRate`, breadth model:32, use a fixed bad law with positive limsup. |
| Nontriviality | `NontrivialCollection`, statistical model:52, is overlapping unequal languages. `GenerationNontrivial`, generation model:52, is a nonempty finite set of indices with a common element and finite intersection. Duplicate indices do not alter the intersection. |
| Support predicates | `FreshBreadthInLimit`, `P3/Definitions.lean:53`, is eventual `supp=C_z\sample`; `RepeatingBreadthInLimit`, same file:61, is eventual `supp=C_z`. `Stable`, same file:45, is eventual equality of supports along each complete stream. `StatisticalStable`, `P3/UnambiguousModel.lean:39`, applies it to a PMF-valued learner. |
| Unambiguity and approximate breadth | `UnambiguousAt`, definitions:69, uses `encard(S△C_z)<encard(S△C_i)` for all extensionally different `C_i`. `UnambiguousInLimit`, same file:75, eventually requires it. `ApproximateBreadthAt`, same file:82, is `S⊆K ∧ Finite(K\S)`; its limit predicate is at:86. |
| Statistical relaxation errors | `unambiguousError`, unambiguous model:50, uses **not** `UnambiguousAt`; `printedUnambiguousError`, same file:56, uses the success event, but is not the target loss. `NoUnambiguousRate`, same file:79, is positive limsup of failure. `approximateBreadthError`, `P3/ApproximateBreadthModel.lean:20`, and `NoApproximateBreadthRate`, same file:44, use failure and positive limsup. |
| Pointwise and uniform support decision | `DecidableMOP`, breadth model:41, is `∀xs∃query, Computable query ∧ ∀x, query x↔x∈supp(G xs)`. `UniformDecidableMOP`, same file:45, is one jointly computable query on `(xs,x)`. The former does not imply the latter. |
| Oracle support decision and sampling | `OracleMOP`, `P3/SupportMembership.lean:23`, allows a history-dependent finite-query program for each history. `HasComputableSampler`, same file:27, requires one joint computable sample function on `(xs,seed)` with a fixed positive geometric seed law. It is substantially more than a PMF-valued function. |
| Labeled validity and loss | `LabeledDatum`, `P3/LabeledIdentificationModel.lean:17`, is `Nat×Bool`; `CorrectLabel`, same file:20, is `b=true↔x∈C_i`; validity at:23 requires support exactly that graph. Error at:65 is language-inequality averaged over labeled histories and output indices. |

### Consequences used throughout

**Encoding:** The paper itself authorizes an `X↔N` bijection for set-theoretic statements. PMF pushforward, list/stream transport, and language equality preserve the stated semantic events. Effective claims need an *effective* coding and transport of the oracles/algorithms; a bare arbitrary bijection does not preserve computability. No target theorem proves a general transport theorem. A total `Nat`-indexed family is nonempty as a collection; any finite nonempty source collection can be represented by repetitions, but an empty collection needs a separate trivial case. Repeated languages are handled extensionally by the errors and excluded from unambiguity competitors, in agreement with footnote 11.

**Quantifiers:** Learners receive the finite ordered sample, not the target index, target law, or future stream. Rate witnesses follow the valid target/law and are fixed for all `n`, including zero. Lower-bound target/law/constants follow the challenged learner and precede the infinitely-often sample sizes. Limit thresholds can depend on the entire target enumeration; that is a dependency in the correctness predicate, not information supplied at runtime.

**Scope of algorithms:** Arbitrary PMF-valued functions include noncomputable learners and distributions without an executable sampler. Universal lower bounds over them are harder than lower bounds over computable source algorithms, when the nonidentifiability premise is held fixed. Positive existence of such a function is easier than positive existence of a source algorithm. Conversely, `¬semantic-identifiable` is a stronger restriction on families than absence of a computable identifier. These changes can pull in opposite directions; they do not justify a global “harder” label.

**MOP:** The pointwise quantifier order in Lean matches Definition 6's literal wording. It should not be called a missing uniformity hypothesis relative to that literal definition. It nevertheless fails to give a common support-query procedure when an executable source reduction needs one. `OracleMOP` and ordinary `DecidableMOP` are different guarantees when family membership is noncomputable.

**Asymptotics:** Positive limsup means persistent nonvanishing error along a subsequence, not error bounded away from zero at every late time. Infinitely-often exponential lower bounds may coexist with convergence to zero. All exponential constant/rescaling dependencies match Definition 13. For a specific arbitrary `g`, the unscaled Lean upper bound implies the source bound with `c=1`; the reverse needs an argument. Nonnegativity/divergence of `g` implement the rate-domain/rate-to-zero requirements; they are not an unmentioned monotonicity assumption. Neither side requires monotonicity. There is no supplied rounding convention for the source's `g(cn)`.

## 4. Bidirectional component table

Verdicts apply to the full compared component unless a stated restriction is shown. Strength is assessed from the changed assumptions/conclusions, separately from the fidelity label. `Indeterminate` is retained when changes have opposing directions or a source-model ambiguity prevents a total ordering. The detailed quantifiers, precise defining interfaces, and consequences for every row follow in section 5.

| Unit | Source location and section | Target locator | Correspondence verdict | Strength/difficulty | Decisive reason |
|---|---|---|---|---|---|
| 3.1a positive/no-rate exclusive dichotomy | 27/30, 3.1.2 | `theorem_3_1`, Overview:60 | Related but materially different | Indeterminate | Positive learner is semantic; no-rate quantifies arbitrary PMF learners; sublinear scaling differs. |
| 3.1b tell-tale iff | 27/30, 3.1.2; Def. 11 22/25 | same, :63 | Indeterminate | Indeterminate | Bare finite tell-tales versus enumeration oracle/procedure; source finite-cardinality wording needs interpretation. |
| 3.1c exponential lower bound | 27/30, 3.1.2 | same, :64 | Faithful generalization | Strengthened / harder | Same overlap premise; fixed `exp(-2n)` bound against arbitrary randomized semantic identifiers. |
| 3.2a exponential fresh generation | 28/31, 3.1.3; contextual scope 2/5 | `theorem_3_2`, Overview:88 | Faithful specialization | Preserved | Concrete deterministic witness in the source's contextual infinite-target regime; effectiveness is relative/conditional. |
| 3.2b computation certificate | same | same, :90 | Faithful specialization | Preserved | Ordinary computation conditional on joint computability of membership; extra explicit certificate of the witness. |
| 3.2c lower bound | same; Def. 18 49/52 | same, :91 | Faithful generalization | Strengthened / harder | Contextual infinite-target scope matches; challenged randomized PMF class is larger, with the same rate and witness order. |
| 3.3a no breadth rate | 30/33, 3.2.2 | `theorem_3_3`, Overview:104 | Related but materially different | Indeterminate | Contextual infinite-target scope matches; semantic nonidentifiability changes the premise against a larger learner class. |
| 3.3b exponential generator in MOP class | same | same, :107 | Related but materially different | Indeterminate | Pointwise MOP unconditional; sampler only under computable membership; generic PMF existence and source support-loss interpretation need qualifications. |
| 3.3c identifiable positive breadth | same | same, :109; StatisticalBreadth:32 | Related but materially different | Indeterminate | One semantic tell-tale generator has exact exponential breadth for all admissible `g`; ordinary MOP and sampling are conditional. |
| 3.3d both branches' generation lower bounds | same | same, :110 | Faithful generalization | Strengthened / harder | One unconditional-in-identifiability conjunct covers both clauses in the contextual infinite regime, against the larger randomized class. |
| 3.4a token support decision | 30/33, 3.2.3 | `theorem_3_4`, Overview:119 | Faithful generalization | Strengthened / harder | Computable exact stopped-word decider; natural tokens allow a larger alphabet, with coding/EOS conventions. |
| 3.5a fresh impossibility | 31/34, 3.2.4 | `theorem_3_5`, Overview:129-131 | Related but materially different | Indeterminate | Same support-event obstruction, narrower semantic premise, larger learner class; contextual infinite-target regime matches. |
| 3.5b repetition-allowing impossibility | same; Remark 2 29/32 | same, :132 | Related but materially different | Indeterminate | Second support convention is explicit; source conversion has exhaustion boundary. |
| 3.5c positive fresh and repeating witnesses | 31/34, 3.2.4 | same, :133; OnlineBreadthConstruction:90 | Related but materially different | Indeterminate | Correct semantic supports, but computable membership is needed for ordinary MOP; effective emit is additional for sampler. |
| 3.5d two equivalences under computable membership | same | same, :134-138 | Faithful specialization | Indeterminate | Extra conditional equivalences over semantic PMF generators, not an unconditional algorithm-existence equivalence. |
| 3.6a statistical unambiguity impossibility | 32/35, 3.3.1 | `theorem_3_6`, Overview:147 | Related but materially different | Indeterminate | Lean lower-bounds failure, literal displayed source loss is success; semantic/algorithm premise issue also remains. |
| 3.7a online unambiguity impossibility | 33/36, 3.3.1 | `theorem_3_7`, Overview:155 | Indeterminate | Indeterminate | Support/stability comparison matches; computational meaning of nonidentifiability is unresolved. |
| 3.8a statistical approximate-breadth impossibility | 34/37, 3.3.2 | `theorem_3_8`, Overview:165 | Indeterminate | Indeterminate | Equation (6) and positive limsup match; semantic premise versus executable source model is unresolved. |
| 3.9a online approximate-breadth impossibility | 34/37, 3.3.2 | `theorem_3_9`, Overview:173 | Indeterminate | Indeterminate | Correct finite-omission/stability task; same unresolved premise. |
| 3.10a exponential subset-oracle identification | 34-35/37-38, 3.4.1 | `proposition_3_10`, Overview:183-186 | Faithful generalization | Strengthened / harder | Concrete oracle procedure works under bare tell-tales without obtaining an enumeration oracle. |
| 3.10b computation certificate | same | same, :187 | Faithful specialization | Preserved | Relative oracle algorithm becomes ordinary when both Boolean oracles are computable. |
| 3.11a finite-collection upper bound | 35/38, 3.4.2 | `proposition_3_11`, Overview:193-195 | Faithful generalization | Strengthened / harder | Finite range with arbitrary repetitions and unknown size; one explicit learner. |
| 3.11b computation certificate | same | same, :196 | Faithful specialization | Preserved | Correct standing membership oracle is the only information required. |
| 3.12a finite-language upper bound | 35/38, 3.4.3 | `proposition_3_12`, Overview:201-203 | Exact / formally equivalent | Preserved | After erasing the named witness, same existence, full-support sample law, and pointwise language finiteness. |
| 3.12b computation certificate/named witness | same | same, :204 | Faithful specialization | Strengthened / harder | Explicit finite-query learner with conditional ordinary computation refines the existential claim. |
| 3.13a labeled exponential upper bound | 36/39, 3.4.4 | `theorem_3_13`, Overview:211-212 | Exact / formally equivalent | Preserved | After erasing the named witness, graph-supported labeled laws equal Definition 16. |
| 3.13b computation certificate/named witness | same | same, :213 | Faithful specialization | Strengthened / harder | Membership-only finite-query construction realizes the existential upper bound. |
| 3.13c labeled lower bound | same | same, :214-217 | Faithful generalization | Strengthened / harder | Same source nontriviality; fixed exponent 2 against arbitrary randomized semantic learners. |

“Exact” in the two upper-bound rows concerns the mathematical existential conclusion after the specified witness/encoding erasure. It is not a claim that the full named Lean theorem is literally the source sentence. The other conjuncts are listed separately. No row is a build-based pass.

## 5. Thirteen declaration dossiers

### 5.1 Theorem 3.1 — identification dichotomy

**Source:** section 3.1.2, p. 27 / PDF 30, using Definitions 10-11, 13-14 and Equation (4). **Lean:** `H.Results.theorem_3_1`, `P3/Results/Overview.lean:60`; relevant interfaces: semantic definitions:24,30,39,52; universal rates:26,34,39,45; statistical model:29,33,40,52.

Write `P(C)=AlmostExponentialIdentifiable C`, `Q(C)=NoIdentificationRate C`, `TT(C)=ConditionTwo C`. The exact top-level Lean skeleton is

`∀C, NontrivialCollection C → [((P∧¬Q)∨(¬P∧Q)) ∧ (P↔TT) ∧ ∀A∃i,p, Valid(C,i,p) ∧ frequently_n(exp(-2n)≤e_id(C,A,p,i,n))]`.

Inside `P`, the order is `∀g admissible ∃A_g : List Nat→Nat ∀i,p valid ∃D>0 ∀n, e_id(pure∘A_g)≤D exp(-g(n))`. The source has `∀g=o(n) ∃computable learner ∀valid P∃c,C>0∀n, error≤C exp(-g(cn))`; it inherits the rate-to-zero convention. Lean is stronger in the unscaled bound for a specified `g` but removes computational realizability. No theorem conjunct supplies a computable version of `A_g`, a tell-tale enumeration oracle, or a sampling implementation. Thus the positive branch is related, not an algorithmic reconstruction of the source assertion.

Inside `Q`, Lean quantifies **all** PMF-valued identifiers, with a fixed bad valid law and positive limsup. This preserves the source “no rate” asymptotics while strengthening the challenged class. The paired negations encode exclusivity correctly, and the fixed-exponent lower bound is shared across both branches, just as “no faster than exponential” applies wherever relevant. That lower-bound conjunct is a faithful strengthening: `c=2,C=1` are allowed source constants, and arbitrary output randomization is included. The overlapping-unequal-language premise is exactly Definition 14 under indexing.

The iff compares to bare finite tell-tales, not to an effective tell-tale procedure. Under an explicit semantic/oracle reading of Definition 11 with arbitrary tell-tale access and intended finite cardinality, this is the right structural condition. Under the source's stated computable-learner/procedure reading it is not enough. This is an unresolved interpretation, not a silent identification of effective and semantic Angluin conditions. Empty target obligations are vacuous for positive PMF laws and streams on both represented sides. No repeated-index error is introduced.

### 5.2 Theorem 3.2 — generation rate

**Source:** section 3.1.3, p. 28 / PDF 31; Equation (5), p. 27 / PDF 30; Definition 18, p. 49 / PDF 52. **Lean:** `H.Results.theorem_3_2`, Overview:88, using `OracleFamily` at core oracle family:17, generation model:36,41,52, and `certifiedKM`, `P3/OracleGeneration.lean:283`.

The Lean skeleton is `∀O, EG(C,pure∘F_O) ∧ (Computable₂ O.query→Computable F_O) ∧ (GN(C)→∀G∃i,p,c>0,D>0, Valid∧frequently_n(D exp(-cn)≤e_gen))`, where `C=O.language`, `F_O=certifiedKM O`.

`F_O` is an actual oracle-search definition: `generationProgram.run (generationOracle O)` with a termination certificate. The stage definitions at oracle generation:27,51,63,86,120,152 use only membership queries on finitely many candidate languages and finitely many domain points, then unbounded stage search; `Support/OracleSearchProgram.lean:45,53,56,59,68` gives that operational interface. Its only runtime data are the finite sample and the family oracle. It is not handed the target index or law. No correspondence to a named paper implementation is inferred from its name.

The upper-bound loss exactly counts hallucinations and repeats in the current training history; output freshness against earlier *generated* strings is not requested by either numbered statement. Every `C_i` is infinite in Lean. The later local header does not repeat that restriction, but p. 2 / PDF 5 explicitly explains that `K` must be infinite for fresh generation. Thus the formal bundle matches the paper's contextual intended generation regime; this is not a novel repair required by Lean. Read in isolation, the local header is broader than that contextual regime. Infinitude avoids exhaustion and makes the concrete total fresh search possible. With a computable membership query the explicit second conjunct certifies ordinary computation; otherwise the definition is a membership-oracle procedure, matching a relative-information reading of the standing source oracle.

The lower bound covers every randomized semantic generator, without MOP or computation restrictions. Its bad law and positive constants are fixed before the infinitely-often indices, exactly as Definition 13 requires. A nonempty finite index intersection is equivalent to Definition 18's finite subcollection witness in a nonempty indexed family; duplicates cannot manufacture a different intersection. Against the contextual infinite-target source regime, infinitude does not weaken this lower bound. Extending the challenged class to arbitrary randomized semantic learners strengthens it. The local header should not be detached from that contextual regime.

The following source prose claims infinitely many fresh outputs on the same high-probability event. The target conjuncts only establish the error of one output; a general sampler-assembly or infinitely-many-distinct-output guarantee is not present. Supporting imports and a function name do not fill that coverage gap. This prose is adjacent quantitative content, not an additional headline theorem target.

### 5.3 Theorem 3.3 — breadth dichotomy and rates

**Source:** section 3.2.2, p. 30 / PDF 33, with breadth loss/Remark 2 at p. 29 / PDF 32. **Lean:** `H.Results.theorem_3_3`, Overview:104; breadth model:23,32,36,41; `CertifiedBreadthPositiveBranch`, `P3/StatisticalBreadth.lean:32`; support membership:23,27.

For `C=O.language`, `I=IdentifiableInLimit C`, `DM=DecidableMOP`, `OM=OracleMOP`, `CQ=Computable₂ O.query`, the four-conjunct skeleton is:

1. `¬I→∀G, DM(G)→∃i,p valid, limsup breadthError>0`.
2. `∃G, DM(G)∧OM(generationOracle O,G)∧EG(C,G)∧(CQ→HasComputableSampler G)`.
3. `I→CertifiedBreadthPositiveBranch O`.
4. `∀G∃i,p,c>0,D>0, Valid∧frequently_n(D exp(-cn)≤generationError)`.

The whole declaration assumes `GenerationNontrivial C`, and every member is infinite. Conjunct 2 does **not** require `¬I`; it consequently covers the source nonidentifiable branch and a larger identifiability regime. Conjunct 4 likewise covers both source occurrences of the generation lower bound without repeating it. It is a single-outcome generation lower bound, not a breadth-specific lower bound. These are faithful component mappings; no source clause was dropped merely because it was shared in Lean. There is also a loss-model qualification for the generic existential generator in conjunct 2: Equation (1), p. 2 / PDF 5, measures support-inconsistency, whereas `ExponentialGenerates` averages the probability of a wrong output. They agree for the deterministic witness explicitly exposed in 3.2, but need not agree for an arbitrary PMF-valued `G`. A sampler may assign exponentially small positive mass to an invalid output at every history, so averaged error vanishes while the support-failure event persists. The 3.3 existential does not package point-mass output or a support-risk bound. On the Equation (5) deterministic/single-output reading its rate matches; on the introductory support-risk reading, a same-witness determinism/support-risk assembly remains to be stated. No proof-body choice of witness is used to fill that obligation.

The first conjunct matches the breadth failure event and strong no-rate meaning. Its semantic nonidentifiability premise is narrower than the effective reading of the source premise, while its generator class is larger than executable source algorithms. Literal pointwise MOP is preserved. The infinite-family scope agrees with the contextual generation assumption at p. 2 / PDF 5. Thus the complete negative component is related but materially different, with opposing strength changes.

The full positive certificate chooses **one** `emit : Nat→Nat→Option Nat` before every target law and before `g`. It asserts, for that same emit and `B=tellTaleBreadthGenerator O emit`:

- each `enumeratedSet emit i` is a finite tell-tale;
- `OracleMOP (generationOracle O) B`;
- `ExponentialBreadth C B`;
- `∀g admissible, AchievesBreadthRate C B (n↦exp(-g(n)))`;
- `CQ→DecidableMOP B`;
- `CQ→Computable₂ emit→(HasComputableSampler B ∧ UniformDecidableMOP B)`.

These are all its conjuncts. Definition `B`, statistical breadth:23, uses the finite-query identifier `identificationProgram.run (identificationOracle (familyMembership O) emit)` and then the selected language's exact fresh sampler. The former consumes both membership and tell-tale emissions (`P3/OracleIdentification.lean:22,25,57,71,97,105,111`); the latter searches fresh selected-language elements using a positive geometric seed (`P3/ExactSampler.lean:21,33,42,62,88,111`). None receives the true target as an argument. The tell-tale emission function is not asserted computable by the initial existential.

This differs in **both directions** from the source positive clause. Quantitatively and in witness order, Lean is stronger: one semantic `B` achieves exact exponential breadth and hence every admissible sublinear exponent, whereas the source supplies `∀g∃algorithm B_g` at almost exponential rates. Computationally the certificate is weaker: it gives ordinary `DM B` only under `CQ`, and a joint sampler only under `CQ` plus computability of the selected emit. For arbitrary `O`, its unconditional `OM` does not put `B` into the source's ordinary-MOP class. Even under `CQ`, a pointwise support decider does not make the sample-to-generator mapping executable. No target conjunct assembles an effectively available emit from semantic `I`. Adding that hypothesis after the fact would change the statement. This is the principal positive-coverage discrepancy, not an omission remedied by imported machinery.

### 5.4 Theorem 3.4 — token-by-token MOP

**Source:** Definition 15 and Theorem 3.4, section 3.2.3, p. 30 / PDF 33; interpretation in section 6.1, p. 58 / PDF 61. **Lean:** `H.Results.theorem_3_4`, Overview:119; `TokenGenerator`, `P3/TokenGeneration.lean:19`; `Machine`, `Support/RandomBitMachine/Basic.lean:25`; `AlwaysHalts`, same file:49.

Lean asserts `∀G ∀hG : AlwaysHalts G.machine, ∃query : List Nat→Bool, Computable query ∧ ∀word, query word=true ↔ 0<wordProbability G hG word`. The query is chosen for the fixed generator before the word. It is not a computable transformer uniformly accepting arbitrary generator codes and totality proofs; the source numbered statement also only asks for decidability for each fixed generator.

`AlwaysHalts` means `∀input,tape ∃time,output`, not almost-sure halting. This is faithful to the source's clarification about every realization of random bits. The machine bundle includes computable initial/action functions; the decoder is computable. Natural auxiliary state codes finite information. `nextLaw` at token generation:29 maps the machine's output law through that decoder. `wordExperiment`, same file:62, recursively requires every token in order and then a stop; `wordProbability`, same file:92, is its success probability. Empty word means immediate stop. Auxiliary states from each successful branch are carried forward; they are not discarded.

The formal alphabet is `Nat`, a generalization of a fixed finite token alphabet. To instantiate a source generator, encode its tokens and auxiliary strings as naturals and model its randomized machine by the computable bit-machine interface. The representation of an EOS-terminated output in Definition 15 includes an EOS symbol syntactically, whereas Lean uses `none` as control and leaves it out of the content word. Deleting/adding a distinguished terminal marker is a computable support-preserving convention on well-formed outputs, but that convention and a general TM-to-machine encoding theorem are not target conclusions. Thus this is a faithful generalized support-decision task with explicit transport obligations, not byte-for-byte equivalence of string encodings.

No global halting of the token process and no total PMF on finite words is assumed. All finite-word probabilities can be zero for a process that never emits EOS. Section 6.1 explicitly permits this possibility, so it is not an added easy restriction in Lean. The result decides positivity of exact terminated words, not prefix occurrence or exact numerical probability.

### 5.5 Theorem 3.5 — online breadth

**Source:** section 3.2.4, p. 31 / PDF 34; Remark 2, p. 29 / PDF 32. **Lean:** `H.Results.theorem_3_5`, Overview:129; definitions:53,61,104; `CertifiedOnlineBreadthPositiveBranch`, `P3/OnlineBreadthConstruction.lean:90`.

The negative skeleton is `¬I→∀G, DM G→(¬Fresh(G,C) ∧ ¬Repeat(G,C))`. Each positive predicate is `∀z,stream, range stream=C_z→∃T∀t≥T, support(G(prefix_t))=required target set`. The fresh set is `C_z\sample_t`; the repeating set is `C_z`. Negating each universal gives some bad target stream with arbitrarily late failures. The witnesses for the two negations need not coincide. The formal nonidentifiability qualification and contextual infinite-member agreement are exactly those discussed for 3.3; no generation-nontriviality premise is imposed here, matching the source theorem.

The positive certificate existentially chooses one finite-tell-tale emission function and sets `A=identificationProgram.run (identificationOracle (familyMembership O) emit)`, `F=identifiedBreadth O A`, `R=identifiedRepeatingBreadth O A`. It asserts **all** of:

1. eventual fresh breadth for `F`;
2. eventual repeating breadth for `R`;
3. `OracleMOP (generationOracle O) F`;
4. `OracleMOP (generationOracle O) R`;
5. `CQ→(DecidableMOP F ∧ DecidableMOP R)`;
6. `CQ→Computable₂ emit→(HasComputableSampler F ∧ UniformDecidableMOP F ∧ HasComputableSampler R ∧ UniformDecidableMOP R)`.

`F` samples the selected language minus the observed list; `R`, defined at online breadth construction:30, samples with an empty removal list. The support choices match the source's two conventions, and the common identifier is selected before each stream. Computational availability is qualified exactly as in 3.3: semantic `I` alone does not give an executable sampler, and ordinary MOP is conditional on computable membership.

The last top-level conjunct is `CQ→[(I↔∃G, DM G∧Fresh(G,C)) ∧ (I↔∃G, DM G∧Repeat(G,C))]`. These extra equivalences use semantic PMF generators; neither existential includes a sampler or uniform MOP requirement. They accurately express a conditional mathematical characterization but cannot be read as unconditional equivalences about computable source algorithms. Every explicit conjunct is accounted for; there is no statistical rate claim in this target.

### 5.6 Theorem 3.6 — statistical unambiguity

**Source:** section 3.3.1, p. 32 / PDF 35, including the immediately preceding displayed error. **Lean:** `H.Results.theorem_3_6`, Overview:147; definitions:45,69; unambiguous model:39,50,56,79; breadth model:41.

The exact formal skeleton is `∀C, ¬I(C)→∀G, Stable(G,C)→DM(G)→∃i,p, Valid∧0<limsup_n P_{xs~p^n}[¬U(C,i,supp(G xs))]`. The source literally defines its statistical error as `1{U}` and then denies a rate whose expectation is bounded above by a vanishing function. Lean instead denies a rate for `1{¬U}`. These are complementary events, not equivalent formulations of the same loss. The raw source snapshot even contains the success-event definition at unambiguous model:56, but the target's conclusion unfolds through the failure-event body at:50. The existence of the unused success-event definition does not cover the literal target claim.

A plausible repair is to complement the printed indicator. Definition 8's success criterion and the surrounding prose support that repair; the statistical argument discusses eventual zero error (section 7.2, pp. 66-67 / PDF 69-70). This is an interpretation of the intended theorem, clearly distinct from the printed statement. The failure event matches that intended reading. It must not be classified “exact” against the literal PDF.

The size metric is correctly modeled by `Set.encard : ENat`: finite cardinalities retain their values, all infinite differences have value infinity, and strict inequality treats two infinities as a tie. The source's minimum over competitors and Lean's comparisons against every distinct competitor agree when competitors exist, since subsets of `N∪{∞}` have a minimum. Under nonidentifiability there must be more than one distinct family language. Duplicates are excluded extensionally. Stability is per enumeration, with support equality rather than equal weights or a common threshold across targets. These support-level ingredients are preserved; the separate effective-versus-semantic premise and arbitrary-PMF domain remain as in section 3.

### 5.7 Theorem 3.7 — online unambiguity

**Source:** section 3.3.1, p. 33 / PDF 36, using Definitions 7-8 from p. 32 / PDF 35. **Lean:** `H.Results.theorem_3_7`, Overview:155; definitions:45,69,75,104; unambiguous model:26,39; breadth model:41.

Lean is `∀C, ¬I(C)→∀G, Stable(G,C)→DM(G)→¬[∀z,stream, Presents stream C_z→∃T∀t≥T,U(C,z,supp(G(prefix_t)))]`. Hence some fixed target and presenting stream have unambiguity failures arbitrarily late. There is no assertion that every stream fails, no error probability, and no claim about all late times individually.

With semantic identifiability used on both sides, the support predicate, quantifier order, complete-stream requirement, stability, and literal pointwise MOP agree. On that explicit reading this is a faithful generalization to arbitrary PMF learners (harder negative conclusion). With the source's computable identification convention, the premise is narrower in Lean and the source theorem is not fully represented. The primary verdict is therefore Indeterminate for the full algorithmic comparison, not an unexplained pass. Unlike 3.6, there is no loss-sign issue in the online statement. No member-infinitude premise is imposed by this target.

### 5.8 Theorem 3.8 — statistical approximate breadth

**Source:** section 3.3.2, p. 34 / PDF 37; Definition 9 and Equation (6), p. 33 / PDF 36. **Lean:** `H.Results.theorem_3_8`, Overview:165; definitions:45,82,104; approximate breadth model:20,44; unambiguous model:39; breadth model:41.

Lean is `∀C, ¬I(C)→∀G, Stable(G,C)→DM(G)→∃i,p valid, 0<limsup_n P[¬(supp(G xs)⊆C_i ∧ Finite(C_i\supp(G xs)))]`. De Morgan's law makes its error exactly the source event `supp⊈K or |K\supp|=∞` on a countable domain. It permits repetitions and does not require finite omission bounds, an omission mass rate, or a fixed omitted set at all times. A finite target makes the finite-omission clause automatic; support containment is still required. Empty targets have no valid positive PMF and cannot be the bad-law witness.

The no-rate quantifiers choose one target/law for the fixed challenged `G`, before the limsup, matching Definition 13's strong no-rate meaning. Stability covers every presenting stream, not merely almost surely under one law. There is no sign discrepancy. As with 3.7, the support/statistical task is preserved and the full verdict remains Indeterminate because nonidentifiability has the unresolved computational reading. Under the explicitly semantic reading it is a faithful strengthened negative statement over arbitrary PMF learners; under the effective reading it covers fewer families. No source component concerning approximate omissions was silently replaced by exact breadth.

### 5.9 Theorem 3.9 — online approximate breadth

**Source:** section 3.3.2, p. 34 / PDF 37; Definition 9, p. 33 / PDF 36. **Lean:** `H.Results.theorem_3_9`, Overview:173; definitions:45,82,86,104; unambiguous model:39; breadth model:41.

The formal conclusion negates `∀z,stream, Presents stream C_z→∃T∀t≥T, supp(G(prefix_t))⊆C_z ∧ Finite(C_z\supp(G(prefix_t)))`, under `¬I`, stability, and pointwise MOP. Equivalently some target and complete stream have arbitrarily late times with an outside-support element or infinitely many omissions. Which disjunct fails may vary with time. No permanently missed named element, common finite omission set, or distributional rate follows from this statement alone. Stability eventually fixes support along a given stream; it is a separate hypothesis, not built into Definition 9.

The direct source support/stream comparison is faithful, including training repetitions and finite-language cases. The same semantic/effective premise issue determines the Indeterminate full verdict and the opposing difficulty directions. No witness construction or sampler is a conclusion, so their absence is not an extra positive-coverage gap here.

### 5.10 Proposition 3.10 — subset-oracle identification

**Source:** section 3.4.1, pp. 34-35 / PDF 37-38. **Lean:** `H.Results.proposition_3_10`, Overview:183; core basic:38 and subset oracle:13; semantic definitions:39,52; `subsetIdentifier`, `P3/SubsetIdentification.lean:138`; statistical model:46.

Lean is `∀C,O_membership,S_subset, TT(C)→[EI(C,pure∘A_{O,S}) ∧ (Computable₂ O.query→Computable₂ S.query→Computable A_{O,S})]`. Its upper-rate order is `∀i,p valid∃c,D>0∀n`; the learner is fixed before the target/law. Both oracles are correct by their bundles; the subset orientation is `C_i⊆C_j`, matching the source.

The named learner is a finite-query truth-table program. At sample size `n`, its definitions at subset identification:31,59,73,94,102,108 query sample membership for candidates `<n`, inclusion into earlier candidates, and select the largest qualifying candidate, defaulting to zero if none. The query/postprocessing interface at `Support/OracleTruthTable.lean:14,20` stores finite primitive-recursive questions and a computable postprocessor. Thus its body genuinely represents a computation relative to the two stated oracles; no effective tell-tale enumeration is needed as runtime input. A semantic finite tell-tale assumption is weaker than the source's procedural Angluin-condition reading, yet the same concrete relative algorithm and statistical guarantee are supplied. This is a faithful strengthening/generalization of the source result, not the mistaken inference that arbitrary tell-tales are computably obtainable.

The explicit ordinary-computability implication is a correct additional certificate when both oracle functions are computable; it does not restrict the rate theorem to that case. Bare oracles may be noncomputable, as the source permits for subset queries. Neither finite-range nor infinite-language restrictions are imposed. Empty targets are statistically vacuous; duplicate indices are judged by denoted language. There is no source lower-bound clause to find in this declaration.

### 5.11 Proposition 3.11 — finite collections

**Source:** section 3.4.2, p. 35 / PDF 38. **Lean:** `H.Results.proposition_3_11`, Overview:193; `finiteVersionSpaceLearner`, `P3/FiniteIdentification.lean:36`; predicates at same file:24,29; statistical model:46.

The skeleton is `∀C,O, Finite(range C)→[EI(C,pure∘F_O) ∧ (Computable₂ O.query→Computable F_O)]`. The finite-range predicate constrains the number of distinct languages, not language cardinalities, and allows arbitrarily many repeated names. A finite nonempty source list is transported by repeating a representative after its last entry. The empty collection needs a separate vacuous case, not a total-family encoding.

`F_O` considers candidate indices `≤length xs`, tests observed membership and containment of the candidate's finite domain restriction in all consistent candidates' restrictions, and takes the least passing index, defaulting to zero. It is not given the finite cardinality, a completed finite list of representatives, or any target-specific information. This supports a stronger, explicit uniform witness than the source's bare existential for each finite collection, and extends it to arbitrary repeated indexed presentations. The source's allowance of infinite individual languages is preserved. The error/rate constants and quantifiers are the usual full-support exponential ones. Conditional ordinary computation uses exactly the standing membership information, with no subset or tell-tale oracle.

This is a faithful generalization/refinement, with the nonempty-indexing boundary disclosed. It does not assert a computable last-mind-change time or common constants across laws. No extra lower bound is present or demanded by the source proposition.

### 5.12 Proposition 3.12 — finite languages

**Source:** section 3.4.3, p. 35 / PDF 38. **Lean:** `H.Results.proposition_3_12`, Overview:201; the same finite identification definitions:24,29,36; statistical model:29,40,46.

Lean is `∀C,O, (∀i,Finite C_i)→[EI(C,pure∘F_O) ∧ (Computable₂ O.query→Computable F_O)]`. There may be infinitely many distinct languages and no uniform cardinality or maximum-element bound. That is exactly the numbered source setting. The same learner as in 3.11 works without receiving a finite target's cardinality or all its contents at once.

After replacing the explicit witness by its existential consequence, the mathematical upper-rate claim is formally the source one on a nonempty indexed collection: one identifier, before each valid law, with law-dependent positive exponential constants. The named finite-query construction and conditional computation are additional witness certificates, recorded separately. An empty target has no valid positive law, so neither formulation imposes a statistical sampling obligation for it. This is different from excluding every empty language from a family. No subset oracle or tell-tale enumerator was added. The paper's informal algorithm discussion is not evidence that the formal witness equals that algorithm; this audit asserts statement correspondence only.

### 5.13 Theorem 3.13 — positive and negative examples

**Source:** section 3.4.4, p. 36 / PDF 39, including Definition 16. **Lean:** `H.Results.theorem_3_13`, Overview:211; labeled identification model:17,20,23,62,65,69; `labeledEnumerationLearner`, `P3/LabeledEnumeration.lean:34`, with consistency predicate at:19; statistical model:52.

Lean has three conjuncts: `ELI(C,pure∘A_O)`; `Computable₂ O.query→Computable A_O`; and `NontrivialCollection C→∀A_randomized∃i,p valid_labeled, frequently_n(exp(-2n)≤e_labeled)`. The selected target/law in the lower bound can depend on `A`, but neither it nor the fixed exponent depends on `n`.

Definition 16's full-support marginal and deterministic correct conditional label are equivalent, on a countable discrete domain, to the formal graph-support equality. Each `x` has positive marginal mass; its sole correct `(x,b)` therefore has positive joint mass, and its wrong label has zero mass, and conversely. Empty and universal targets are covered: they produce all-negative and all-positive labeled laws, respectively. This obligation is not vacuous for the empty target, unlike positive-only laws.

The learner checks candidates `<length xs`, compares every observed Boolean label to family membership, and chooses the least consistent candidate or zero. It receives the complete labeled history and the standing family oracle, not a target-membership oracle with the true target index. Its explicit finite-query body supplies a relative computation, and the second conjunct supplies ordinary computation under joint computability of membership. After witness erasure, the upper exponential claim is the numbered source statement; the named witness/certificate is an additional faithful refinement.

The lower bound uses exactly the source's overlap-based identification nontriviality, even though other nontriviality notions might also be natural with labels. It must not be silently enlarged. Fixed `exp(-2n)` is stronger quantitative information than existence of source exponential constants, and quantifying arbitrary randomized semantic identifiers enlarges the challenged class. Duplicate language indices remain successful if they denote the right set. No subset or tell-tale oracle, infinitude of targets, or uniform sample-law constants is introduced.

## 6. Discrepancy and uncertainty dossiers

### D1. Semantic identification is not automatically the source's algorithmic identification

**Kind:** formal/source model mismatch under the effective reading; unresolved source interpretation under an oracle reading. Relevant targets: 3.1, 3.3, 3.5-3.9; also the weaker assumption of 3.10 is a deliberate strengthening of that positive result.

The decisive bodies are semantic inferrability and `ConditionTwo`, not their names. `ConditionTwo` is `∀i∃finite T_i`; it provides no index-to-enumerator computation. The original effective definitions expose a different condition with `∃emit, Computable₂ emit ∧ ...` at effective definitions:49. Nothing in the scoped interfaces identifies these two conditions. The source explicitly requires computable learners and discusses an oracle/procedure finding tell-tales; its Definition 11 does not state that this oracle is ordinarily computable, nor consistently specify all algorithms' relative-oracle access.

If “identifiable” means an ordinary or fixed-oracle effective learner, `¬semantic I` can exclude fewer collections from consideration than “not effectively identifiable.” Lean's negative results then do not cover all the source's stated nonidentifiable collections. If arbitrary additional tell-tale access is allowed and the finite-set reading is fixed, semantic structure may be the intended common notion; that must be stated, not inferred from the standard theorem name. Executable positives still require an available oracle/emit, whereas semantic existential witnesses do not provide that availability. This audit does not resolve the source's computational convention by silently replacing one definition with the other. A further uniformity question is whether the source's “sequence of computable mappings” requires one computable program uniform in sample size, or only a separate computable mapping for each fixed size. The latter is weaker: for the finite-query tell-tale construction, a fixed size uses finitely many emission values, which can be hard-coded nonuniformly. Thus absence of a joint `HasComputableSampler` certificate should not be presented as a proof that every per-size computational reading fails. The table retains the full-model qualification rather than deciding that convention implicitly.

### D2. Contextual infinite targets and local headers

**Kind:** contextual source convention successfully represented, with an editorial local-header boundary; not a newly discovered formal scope defect. Relevant targets: 3.2, 3.3, 3.5 and Remark 2.

The first draft missed the introduction's explicit standing explanation on p. 2 / PDF 5: `K` must be infinite for fresh generation to be well-defined, since otherwise the sample eventually exhausts it. After the coordinator supplied that locator, the original PDF page was independently extracted and visually checked. For results promising generation for every target, this contextual regime corresponds to the all-infinite family stored in Lean's `OracleFamily.infinite'`. The later “every countable collection” headers do not repeat it, but they should not be read as erasing the earlier convention. Accordingly, infinitude is **not** counted as an unsupported extra Lean assumption or a novel source repair in the final comparison.

The singleton target `{0}` remains a useful *explanation* of the convention: under Equation (5), every output after a nonempty sample is either outside the target or a repeat, so its error is one. This shows why an unrestricted finite-target extension would require an exhaustion convention; it does not contradict the paper's contextually intended theorem. Definition 12's online exception is a separate stated convention. Infinitude also supports the rejection-sampling conversion in Remark 2 and the adjacent infinitely-many-new-strings discussion.

There remains a distinction between the literal local header considered in isolation and the complete contextual statement. The latter is the appropriate primary scope for assessing the generation interfaces. Finite-language identification in Propositions 3.11-3.12 is unaffected. The repetition-allowing relaxation targets 3.6-3.9 do not explicitly bundle member infinitude in Lean; no unwritten infinite-language premise is inserted into their formal interfaces.

### D3. Positive breadth certificates change information and quantitative difficulty

**Kind:** changed formal conclusion and incomplete unconditional algorithm coverage. Relevant targets: 3.3 and 3.5.

The certificates completely represent fresh/repeating semantic support success, and provide extra relative-support and conditional-computation properties. They do **not** state the unconditional ordinary-MOP and executable-learning witnesses of a literal source-algorithm reading. Specifically, no ordinary `DecidableMOP` conclusion is available without computable family membership, and no joint sampler is available without an effective chosen tell-tale enumeration as well. Pointwise oracle programs depending on histories non-effectively cannot supply that missing assembly.

At the same time, the statistical certificate is stronger in rate and witness dependency: `∃B∀g` with exponential breadth, versus source `∀g∃B_g` with almost exponential breadth. The stronger idealized rate is not evidence that the computationally harder source claim was formalized. A report must retain both observations, rather than call the certificate uniformly weaker or uniformly stronger. No repair to Lean was requested or made.

### D4. The unambiguity indicator is complemented

**Kind:** definite literal mismatch, with a strongly supported suspected source sign problem. Relevant target: 3.6 only; 3.7's online success definition is unaffected.

Literal: displayed source statistical `er=1{strict target-closeness}` on p. 32 / PDF 35. Formal: probability of the complementary event, unambiguous model:50. Proposed reading: the source intended failure as error, consistent with its prose and the roles of zero error in section 7.2. The named theorem itself does not print a replacement formula.

The difference has mathematical consequences. As an **informal illustration, not Lean verified**, let `B={4k:k∈N}`, let `C_m=B∪{4k+2:k<m}`, and include `C_∞={2k:k∈N}`. Every language is infinite, so this example stays within the contextual infinite-target regime. The standard finite-tell-tale obstruction applies to `C_∞`: any finite subset of it lies in some proper `C_m`. Thus the intended finite-tell-tale characterization gives nonidentifiability. A fixed computably sampled generator with support all naturals is stable and has decidable support. Its symmetric-difference distance from every family language is infinite, since the odd naturals are always in the difference; all comparisons tie. The *printed success indicator* is therefore zero for every target, whereas Lean's failure indicator is one. This illustrates why the two no-rate assertions cannot be interchanged. The coordinator suggested using an all-infinite chain after reviewing the draft; the set construction, obstruction, and distance calculation were independently checked here. It supports a source clarification without certifying source proof steps or a global verdict that the paper is wrong. The literal target is not represented by the chosen Lean conclusion; the plausible repaired statement is represented at the support-event level, subject to D1.

### D5. Transport, decidability, and sampling are separate obligations

**Kind:** representation obligations, not automatic mathematical errors. Relevant throughout, especially 3.4 and algorithmic upper bounds.

The semantic `N` domain, extensional duplicate handling, exact-support sample laws, independent finite histories, fixed-index stabilization, and no-target-leakage input shape correspond closely. Effective coding of `X`, strings, labels, auxiliary state, and source machines must still be supplied when claiming executable transport. For token generation, EOS stripping/adding must be fixed and the source machine must inhabit the computable all-tapes-halting bit-machine interface. No scoped theorem states a global code-to-code simulation theorem. Its absence limits representation claims; it does not make the exact-word positivity predicate a different task.

`DecidableMOP` is intentionally pointwise and matches the literal Definition 6 order. It cannot be used as a uniform algorithm selector. Source proof descriptions that train a generator and then call MOP operationally appear to need that extra availability. This is a source model/implementation question, not permission to rewrite Definition 6. The positive target certificates explicitly separate pointwise ordinary MOP, oracle MOP, a uniform decider, and a sampler; none should be collapsed into another.

### D6. Remaining quantitative and component coverage

**Kind:** explicit extra conclusions, scoped omissions, and minor conventions.

All source lower-bound clauses have mapped Lean counterparts within the recorded formal scopes, including both occurrences in 3.3 via its one final conjunct. The stronger fixed-exponent lower bounds in 3.1 and 3.13 and randomized learner domains are additional formal content. Both fresh/repeating negations, both positive support witnesses, and both conditional equivalences in 3.5 have been expanded; none is credited merely through imports. Source upper-rate constants are distribution-dependent on both sides. Lean includes sample size zero, absorbable in a positive prefactor for the exponential comparisons; index base zero versus one is an ordinary renumbering. Rates for arbitrary `g` need the scaling convention described in section 3; the stronger unscaled formal bound implies its scaled source instance but is not asserted literally equivalent in the reverse direction.

The source's adjacent “infinitely many new strings” assertion after 3.2 has no corresponding witness-assembly conclusion in this target. Empty *collections* need separate trivial handling because a total indexed family has nonempty range. Empty *languages* inside a nonempty family are allowed outside `OracleFamily`, with the positive-data and labeled-law distinctions already recorded. These are not silently omitted assumptions.

## 7. Corrections to Stage 1

The independent first draft was subsequently reviewed by the model coordinator. Its two substantive review messages supplied the p. 2 / PDF 5 infinite-target locator and an all-infinite loss-sign illustration; these prompted the independently verified scope/example corrections in D2 and D4. The initial draft's claim that target infinitude lacked source evidence is withdrawn. This review history affects Stage 2 only; neither frozen Stage 1 output was edited.

Stage 1 accurately reconstructed the decisive types, semantic/effective distinctions, pointwise MOP order, certificate dependencies, and error definitions used here. No second decisive type mistranslation was found.

One prose correction is required: in dossier 7 it says the generator “fails eventual unambiguity on all presenting streams.” Read literally, that overstates the conclusion. The theorem negates success **on all streams**, so it supplies **some** target and presenting stream with arbitrarily late failures. The same Stage 1 dossier's displayed quantifier skeleton and following paragraph give the correct existential consequence. This report uses that correct reading.

Stage 1's “Interpretation uncertainties: none beyond the declared boundary” is a code-only assessment and must not be carried into the paper comparison. Its reconstructed `unambiguousError` is correct for the code, but it differs from the literal source display. Likewise its exact-exponential positive breadth certificate, infinite-member bundle, and semantic tell-tales are accurate reconstructions; they are not evidence of exact source faithfulness. These are Stage 2 qualifications, not invented Stage 1 failures.

## 8. Completion checklist and unresolved questions

| Target | All interface components accounted for? | Source coverage disposition |
|---|---|---|
| `theorem_3_1` | Yes: exclusive dichotomy, iff, lower bound | Semantic/effective and tell-tale interpretations unresolved; lower bound faithfully strengthened. |
| `theorem_3_2` | Yes: named upper bound, computation, lower bound | Contextual infinite-target regime matched; adjacent infinitely-many-output content not supplied. |
| `theorem_3_3` | Yes: four top-level conjuncts and six positive-certificate clauses | Negative-model qualification; mixed stronger rate/weaker computational availability in positive branch. |
| `theorem_3_4` | Yes: total per-call premise, computable query, exact positivity | Faithful generalized token task with explicit encoding/EOS obligations. |
| `theorem_3_5` | Yes: two negations, full six-clause certificate, two equivalences | Semantic/conditional-effectiveness qualifications retained; infinitude matches contextual fresh-generation scope. |
| `theorem_3_6` | Yes: nonidentifiability, stability, MOP, positive limsup | Literal loss mismatch; plausible intended failure-loss reading identified separately. |
| `theorem_3_7` | Yes: all premises and negated stream predicate | Support task preserved; algorithmic premise reading unresolved. |
| `theorem_3_8` | Yes: all premises and bad-law failure limsup | Equation (6) preserved; algorithmic premise reading unresolved. |
| `theorem_3_9` | Yes: all premises and negated eventual finite-omission predicate | Support task preserved; algorithmic premise reading unresolved. |
| `proposition_3_10` | Yes: upper bound and computation | Faithful stronger relative-oracle result under bare tell-tales. |
| `proposition_3_11` | Yes: finite-range premise, upper bound, computation | Faithful finite-collection refinement/generalization with repetitions. |
| `proposition_3_12` | Yes: pointwise finite premise, upper bound, computation | Existential statistical task equivalent; explicit witness/computation refined. |
| `theorem_3_13` | Yes: upper bound, computation, lower bound | Labeled validity equivalent; lower bound strengthened to arbitrary randomized learners. |

Unresolved items are substantive limitations, not missing audit execution:

1. Precisely which fixed oracles are source learners allowed to use, and is “identifiable” effective relative to those oracles or merely semantic? Is a tell-tale enumeration required computable relative to membership, independently available, or an arbitrary oracle? The PDF supports multiple readings and does not justify identifying all of them.
2. Should Definition 11 explicitly require a finite **set** of tell-tale strings? Appendix B strongly supports that interpretation, but the displayed definition's wording should be clarified.
3. Is a family-membership oracle meant to be ordinarily computable uniformly in the language index, pointwise decidable per language, or only available as a black box? This affects the unconditional ordinary-MOP and sampler claims in positive breadth.
4. Does Definition 6 intend a uniform history-to-support decider for source operational reductions, beyond its literal pointwise existence wording?
5. The p. 2 contextual infinite-target convention resolves the intended fresh-generation scope. The remaining editorial/model question is whether later local theorem headers should explicitly repeat it, and how any proposed extension to mixed finite/infinite collections would handle exhaustion. Such an extension is not assumed here and is not a missing repair of the contextual theorem.
6. Should the displayed unambiguity “error” on p. 32 be complemented? Lean represents the apparent intended failure event, not the literal event.
7. What is the precise rescaling/rounding convention for general `R(cn)` and `g(cn)` with a natural-number rate domain? No global effective encoding transport theorem or infinitely-many-output assembly theorem is a conclusion of these targets.

No Lean build was run because the task changes audit prose/provenance only and does not alter Lean, imports, module paths, generated inputs, or executable examples. There are no new build warnings or failures to report; neither absence of a build nor input hash agreement certifies proofs. The audit is complete at the requested statement level, with the indeterminate and non-equivalence findings retained.
