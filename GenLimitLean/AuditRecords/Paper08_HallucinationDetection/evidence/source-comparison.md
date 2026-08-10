
# 08 — Paper08_AutomatedHallucinationDetection — Lean Faithfulness Audit

## 1. Executive conclusion

**Overall paper-level verdict: substantially faithful at the paper's stated semantic, oracle-level notion of learning, with one material source correction and several important non-effectivity and vacuity qualifications.**

The central existence equivalence in Theorem 2.1 (p. 7, §2.2) is represented faithfully: the formal detector receives a complete positive presentation in the limit, may make finitely many adaptive membership queries to an arbitrary candidate set in each round, and must eventually decide the predicate `G ⊆ K`; the formal identifier receives only positive prefixes and must stabilize to one index denoting the target. The Lean theorem is a specialization to a **nonempty** countable example type, whereas the paper says only “countable domain.” The reduction declarations preserve target/presentation/candidate dependence, duplicate indices, and exact subsethood. They do not turn the result into a computable or efficient reduction.

The finite-tell-tale characterization in Corollary 2.2 (p. 7, §2.2) and Definition 4/Theorem A.1 (p. 19, §A.1) is faithful only at this same semantic level. The formal predicate `GenLimit.Angluin.ConditionTwo` is merely

\[
\forall i\;\exists T_i\text{ finite},\quad T_i\subseteq C_i
\quad\text{and}\quad
\forall j\;(T_i\subseteq C_j\subseteq C_i\Rightarrow C_i\subseteq C_j).
\]

It gives no computable or uniformly enumerable certificate selector. The Paper 08 module obtains a selector with `Classical.choose` and places the final tell-tale at every “approximation” stage. No target-scope theorem establishes effective discovery, a tell-tale enumeration procedure, a halting/completion signal, or any bound on certificate size. This does not contradict the paper's explicit statement that it imposes no computational restrictions (p. 7, §2.1), but it means the formalization is not an effective version of Angluin's theorem and should not be read as one.

The negative-example theorem, Theorem 2.3 (p. 8, §2.2), matches the paper on every **valid complete labeled enumeration**: every domain point must eventually appear and every label must be exact. The Lean statement is quantified over an arbitrary type `α` without `[Countable α]`; outside countable presentable domains the premise has no witness, so the extra generality is vacuous. The formal theorem therefore faithfully covers the intended countable setting but is globally easier than the paper-looking wording suggests.

The paper's sentence immediately after Example 1 (p. 6, §2.1) is mathematically false. For the family of positive-integer multiples, the singleton `{i}` is a tell-tale for the language of multiples of `i`. Hence the family satisfies the paper's own Angluin condition and, by Corollary 2.2, is hallucination-detectable. The Lean declarations prove exactly this counterdiagnosis. They are a **formal repair of a source error**, not a faithful restatement of that sentence. The two displayed containment calculations, `L_4 ⊆ L_2` and `L_3 ⊄ L_2`, are represented correctly.

No conclusion below asserts that the supplied Lean source compiled or that its proof bodies are correct. This audit compares declaration signatures and statement-relevant definitions only.

## 2. Evidence integrity and readability

The author source inspected is exactly `08-2504.17004v2.pdf`, 339,652 bytes, SHA-256
`b4268bc32c32c7aa3660b8f54c425b8d1a2534f23cfab10774a5d2b592e847c0`.
The hash matches the value supplied in the request. The file reports 20 unencrypted letter-size pages. All 20 pages rendered successfully, and text extraction produced readable content containing the title, authors, Definitions 1–5, Theorems 2.1, 2.3, A.1, A.2, Corollary 2.2, Lemmas 3.1–3.2, Algorithms 1–2, and Example 1. The visually inspected theorem and definition pages were legible.

The Lean evidence is exactly `08__Paper08_AutomatedHallucinationDetection__lean-source-bundle.txt`, 145,824 bytes, SHA-256
`60e5b14e054663034a0d71380a2bf44f2f3578758d35512b9a1dc97999cdfc06`, containing the 18-file transitive local import closure recorded in its manifest for commit `dfcd13534f9d51642a9f88904268e95454c88f7f`. The Stage-1 artifact inspected as a fallible index is `08-automated-hallucination-detection-lean-statement-reconstruction.md`, 98,264 bytes, SHA-256
`fc6cbe5edec38e8e35420ce58cc551a5bc686b26ce1390d36825541bd464b008`.

No web source, connector, other Project file, alternate paper version, or prior-chat mathematical content was used.

## 3. Audit method and verdict vocabulary

Paper claims are cited by their printed number plus PDF page and section. Lean claims are cited by fully qualified declaration name, primary bundle file path, and an exact or whitespace-normalized signature. For definitions, the logical right-hand side is unfolded. Imported definitions are unfolded only when needed to interpret a primary statement and are kept in a separate dependency ledger.

The semantic evidence excludes Lean comments, docstrings, declaration names as indicators of intent, and theorem proof bodies. A theorem declaration is treated only as asserting its displayed type. Where a named construction and an existential theorem occur separately, the audit does **not** infer from a proof body that the named construction is the theorem's witness; it records whether a separate statement-level correctness link exists.

Every comparison uses exactly one correspondence verdict from the requested list and exactly one difficulty verdict from the requested list. “Preserved” concerns the paper's own semantic model, not an external effective reading of the cited Angluin literature.

### 3.1 Stage-1 reconstruction cross-check

The Stage-1 reconstruction was treated only as an index of declarations. Its inventory of 72 public declarations across the six substantive primary modules agrees with a fresh direct pass over the bundle. Stage 2 independently re-read every displayed signature and every statement-relevant defining right-hand side. The main Stage-1 semantic reconstruction is confirmed, subject to five paper-facing qualifications that only become visible in comparison with the PDF:

1. `theorem_2_1` is a nonempty-domain specialization of the paper's countable-domain statement, while its two directional reductions have different, explicitly displayed generality.
2. `ConditionTwo` is nonuniform finite-certificate existence. The primary Paper 08 statements do not establish effective certificate discovery or the operational tell-tale enumeration primitive mentioned in Definition 4.
3. `theorem_2_3` is stated for arbitrary `α`; the extra uncountable and empty-domain cases are vacuous because no complete labeled enumeration exists.
4. The multiples-family declarations are not merely auxiliary examples: they prove that the paper's no-detector sentence after Example 1 is false and repair it.
5. Named constructions such as `detectorFromIdentifier`, `identifierFromDetector`, and `negativeExampleDetector` are not explicitly named as witnesses in the public existential main-theorem signatures. Their intended use cannot be credited from proof bodies under this audit's evidence rules.

No Stage-1 statement was accepted as authority when it conflicted with, or went beyond, the source signatures.

## 4. Paper model and complete main-result inventory

### 4.1 Common model assumptions

The paper fixes a naturally indexed countable collection `𝓛 = {L₁,L₂,…}` of subsets of a countable domain `𝓧`; duplicate indices are allowed, and languages may be finite or infinite. It assumes exact membership access to every family language `L_i` (p. 5, §2.1). A positive enumeration is an infinite sequence lying in the target and covering every target element, with repetition allowed (p. 5, §2.1). The candidate `G` is any subset of the domain, not necessarily a member of the family. A detector may make finitely many membership queries to `G` in every round (p. 5, §2.1). The paper explicitly imposes no computational restriction and asks only for eventual correctness (p. 7, §2.1).

### 4.2 Named definitions, results, and substantive explicit claims

| Paper item | Exact paper content | Location | Lean coverage |
|---|---|---|---|
| Definition 1 | Eventual exact decision of `G ⊆ K` from every complete positive presentation, for every target and candidate set. | p. 5, §2.1 | `DetectorCorrectAt`, `DetectsHallucinations`, `HallucinationDetectable` |
| Example 1 containment 1 | With `K=L₂`, `G₁=L₄` does not hallucinate, i.e. `L₄ ⊆ L₂`. | p. 5, §2.1 | `example_1_L4_subset_L2` |
| Example 1 containment 2 | With `K=L₂`, `G₂=L₃` hallucinates, i.e. `L₃ ⊄ L₂`. | p. 5, §2.1 | `example_1_L3_not_subset_L2` |
| Example 1 impossibility sentence | Theorem 2.1 plus Theorem A.1 supposedly imply that no detector exists for the multiples family. | p. 6, §2.1 | Contradicted and repaired by `singleton_index_isTellTale`, `example_1_angluinCondition`, `example_1_hallucinationDetectable` |
| Informal Result I | Positive-only automated detection is described as inherently difficult and “typically impossible.” | p. 2, §1 | `theorem_2_1` and `corollary_2_2` supply an exact characterization, but no formal notion of “typically” or “most” |
| Informal Result II | Reliable detection is achievable with positive and explicitly labeled negative examples. | p. 3, §1 | Formalized by Definition 2 and `theorem_2_3` under complete perfectly labeled domain presentations |
| Theorem 2.1 | Hallucination detectability in the limit iff identification in the limit. | p. 7, §2.2 | `theorem_2_1` |
| Corollary 2.2 | Hallucination detectability iff Angluin's condition. | p. 7, §2.2 | `corollary_2_2` |
| Definition 2 | Same subsethood decision from a complete correctly labeled enumeration of the whole domain. | pp. 7–8, §2.2 | `IsLabeledEnumeration`, `DetectsWithNegativeExamples`, `DetectableWithNegativeExamples` |
| Theorem 2.3 | Every countable indexed family over a countable domain is detectable from negative examples. | p. 8, §2.2 | `theorem_2_3` |
| Lemma 3.1 | Identification implies detection. | p. 8, §3.1; proof p. 9 | `lemma_3_1_identification_implies_detection` |
| Algorithm 1 | Use the identifier's current language and scan a growing domain prefix for `x∈G\L_i`. | pp. 8–9, §3.1 | `domainPrefix`, `subsetTestTree`, `detectorFromIdentifier`, evaluation lemma |
| Lemma 3.2 | Detection implies identification. | p. 9, §3.1; proof pp. 10–12 | `lemma_3_2_detection_implies_identification` |
| Algorithm 2 | Choose the least bounded index that is positive-data consistent and for which the detector says `L_i ⊆ K`. | pp. 10–11, §3.1 | `DetectorCandidate`, `identifierFromDetector`, least-candidate lemmas |
| Family-oracle query count | Computing the bounded consistent set needs `2t−1` fresh family-membership queries in round `t`. | p. 10, footnote 5 | No target-scope query-count declaration |
| Definition 3 | Identification requires adjacent guesses eventually equal and each late guessed language equal to the target. | p. 19, §A.1 | `ConsecutivelyIdentifiesFrom`, `ConsecutivelyIdentifies`, `ConsecutivelyIdentifiable` |
| Definition 4 | Finite tell-tale condition; the paper additionally declares a tell-tale oracle primitive that outputs an enumeration of `T_i`. | p. 19, §A.1 | Finite-set predicate represented by imported `IsTellTale`/`ConditionTwo`; operational oracle not represented as data or computability |
| Theorem A.1 | Identification iff Angluin's condition. | p. 19, §A.1 | `theorem_A_1` |
| Definition 5 | Eventual fresh valid generation, with unrestricted output once `K\E_t=∅`. | p. 20, §A.2 | `AppendixGenerationCorrectAt`, `AppendixGeneratesInLimit`, `AppendixGeneratableInLimit` |
| Theorem A.2 | Every countable indexed family is generatable in this appendix sense. | p. 20, §A.2 | `theorem_A_2` |
| Probabilistic carry-over assertion | The adversarial results are said to carry over to a probabilistic setting by similar techniques. | p. 6, §2.1 | Not represented in Lean |

The informal statements that detection is impossible “for most” collections and that negative examples are “fundamentally necessary” are not separate quantified theorems. The formal results establish a characterization and a universal sufficiency result, not a measure-theoretic notion of “most” and not necessity of negative labels for every individual family.

## 5. Fully unfolded formal setting

### 5.1 Languages, families, streams, and exact presentation

The imported paper-facing core has the following statement-relevant definitions:

```lean
abbrev GenLimit.Generic.Language (α : Type*) := Set α
abbrev GenLimit.Generic.LanguageClass (α : Type*) := Set (Set α)
abbrev GenLimit.Generic.LanguageFamily (α : Type*) := ℕ → Set α
abbrev GenLimit.Generic.Stream (α : Type*) := ℕ → α
abbrev GenLimit.Generic.Generator (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → α

def GenLimit.Generic.Presents
    (stream : Stream α) (L : Language α) : Prop :=
  Set.range stream = L

def GenLimit.Generic.output
    (G : Generator α) (stream : Stream α) (t : ℕ) : α :=
  G t (fun i => stream i)
```

Thus the family is indexed rather than represented as a set; repeated languages are preserved. Exact presentation is stronger than merely positive-only soundness: every shown point belongs to the target and every target point eventually appears. For a nonempty domain, an empty target has no exact presentation, so all universally quantified positive-presentation obligations for that target are vacuous. This is also the literal consequence of the paper's infinite-sequence definition.

### 5.2 Finite adaptive candidate-set queries

```lean
inductive GenLimit.HallucinationDetection.OracleTree (α : Type*) where
  | answer : Bool → OracleTree α
  | query : α → OracleTree α → OracleTree α → OracleTree α

noncomputable def GenLimit.HallucinationDetection.OracleTree.eval
    (G : Set α) : OracleTree α → Bool
  | .answer b => b
  | .query x yes no =>
      if x ∈ G then eval G yes else eval G no

abbrev GenLimit.HallucinationDetection.Detector (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → OracleTree α
```

Every individual tree is finite inductive syntax, so each round contains finitely many adaptive membership queries to `G`. There is no declaration giving a numerical size/depth/query-count function, no bound uniform in `t` or the history, and no computability condition on the map that constructs the tree. Exact membership in an arbitrary set is evaluated classically and noncomputably.

The detector is memoryless in its type—its visible input is the current positive prefix—but this is not a material restriction in the paper's deterministic, unbounded semantic model: any finite cross-round oracle interaction can be unrolled and replayed inside the current finite tree. Such unrolling may destroy all efficiency, which neither source measures.

### 5.3 Positive-data detection, fully expanded

```lean
def GenLimit.HallucinationDetection.DetectorCorrectAt
    (D : Detector α) (G K : Set α)
    (stream : Stream α) (t : ℕ) : Prop :=
  detectorOutput D G stream t = true ↔ G ⊆ K

def GenLimit.HallucinationDetection.DetectsHallucinations
    (D : Detector α) (C : LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Stream α,
    Presents stream (C z) → ∀ G : Set α,
    ∃ T, ∀ t, T ≤ t → DetectorCorrectAt D G (C z) stream t

def GenLimit.HallucinationDetection.HallucinationDetectable
    (C : LanguageFamily α) : Prop :=
  ∃ D : Detector α, DetectsHallucinations D C
```

After all abbreviations are removed, the collection property is

\[
\exists D\;\forall z\;\forall E\;
(\operatorname{range}E=C_z)\Rightarrow
\forall G\;\exists T\;\forall t\ge T,
\bigl(\operatorname{eval}_G(D(t,E_{<t}))=\mathrm{true}
\iff G\subseteq C_z\bigr).
\]

The stabilization time is after `z`, the complete presentation, and `G`; it may depend on all three. The detector receives neither `z` nor `C_z` at runtime. It tests subsethood of an arbitrary candidate set, not individual-output correctness, exact equality, or support recovery.

### 5.4 Semantic identification, fully expanded

```lean
abbrev GenLimit.Angluin.SemanticIdentifier (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → ℕ

def GenLimit.Angluin.ConvergesTo
    (M : SemanticIdentifier α) (stream : Stream α) (j : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t → identifierOutput M stream t = j

def GenLimit.Angluin.IdentifiesFrom
    (M : SemanticIdentifier α) (C : LanguageFamily α)
    (z : ℕ) (stream : Stream α) : Prop :=
  ∃ j, C j = C z ∧ ConvergesTo M stream j

def GenLimit.Angluin.SemanticallyIdentifies
    (M : SemanticIdentifier α) (C : LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Stream α, Presents stream (C z) →
    IdentifiesFrom M C z stream

def GenLimit.HallucinationDetection.IdentifiableInLimit
    (C : LanguageFamily α) : Prop :=
  ∃ M : SemanticIdentifier α, SemanticallyIdentifies M C
```

The limiting index `j` and time may depend on the target index and presentation. Duplicate indices are permitted; the conclusion requires eventual syntactic constancy at one extensionally correct representative. No `Computable`, machine, runtime, or membership-oracle argument appears in the type.

### 5.5 Tell-tales, fully expanded

```lean
def GenLimit.Angluin.IsTellTale
    (C : LanguageFamily α) (i : ℕ) (T : Finset α) : Prop :=
  (↑T : Set α) ⊆ C i ∧
    ∀ j, (↑T : Set α) ⊆ C j → C j ⊆ C i → C i ⊆ C j

def GenLimit.Angluin.ConditionTwo
    (C : LanguageFamily α) : Prop :=
  ∀ i, ∃ T : Finset α, IsTellTale C i T
```

This is logically equivalent to the finite-set part of Definition 4 (p. 19, §A.1): no family language containing `T_i` is a proper subset of `C_i`. It is **not** an oracle object and contains no selector, enumeration, computability, or size bound.

The effective dependency interface is distinct:

```lean
def GenLimit.Angluin.ConditionOne (F : EffectiveIndexedFamily) : Prop :=
  ∃ emit : ℕ → ℕ → Option ℕ, Computable₂ emit ∧
    ∀ i, IsEnumeratedTellTale F.language i (enumeratedSet emit i)
```

No primary Paper 08 theorem concludes `ConditionOne` or effective inference.

### 5.6 Complete labeled data, fully expanded

```lean
abbrev GenLimit.HallucinationDetection.LabeledStream (α : Type*) :=
  ℕ → α × Bool

def GenLimit.HallucinationDetection.IsLabeledEnumeration
    (stream : LabeledStream α) (K : Set α) : Prop :=
  Set.range (fun n => (stream n).1) = Set.univ ∧
  ∀ n, (stream n).2 = true ↔ (stream n).1 ∈ K
```

This is complete, perfectly labeled data over the whole domain, not a partial sample containing some positives and some negatives. A valid stream itself witnesses a surjection from `ℕ` onto `α`; hence no valid stream exists for an uncountable type or an empty type.

### 5.7 Appendix generation, fully expanded

```lean
def GenLimit.HallucinationDetection.AppendixGenerationCorrectAt
    (G : GenLimit.Generic.Generator α)
    (L : Set α) (stream : Stream α) (t : ℕ) : Prop :=
  GenLimit.Generic.output G stream t ∈
      L \ (↑(GenLimit.Generic.sample stream t) : Set α) ∨
  L \ (↑(GenLimit.Generic.sample stream t) : Set α) = ∅
```

The second disjunct is an explicit finite-target escape clause. Once every target element has appeared, the generated output is unrestricted. Lean follows the displayed formal definition on p. 20, not the preceding prose sentence that says the generator “must output” an unseen string at every step.

### 5.8 Remaining statement-relevant dependency helpers, recursively unfolded

The following imported definitions occur in primary Paper 08 signatures or are needed to expand their conditional bridge statements. They are interfaces, not Paper 08 results.

```lean
noncomputable def GenLimit.Generic.sequenceSample
    {t : ℕ} (xs : Fin t → α) : Finset α :=
  Finset.univ.image xs

noncomputable def GenLimit.Generic.sample
    (stream : Stream α) (t : ℕ) : Finset α :=
  (Finset.range t).image stream

def GenLimit.Angluin.identifierOutput
    (M : SemanticIdentifier α) (stream : Stream α) (t : ℕ) : ℕ :=
  M t (fun i => stream i)

def GenLimit.Angluin.streamPrefix
    (stream : Stream α) (t : ℕ) : List α :=
  List.ofFn (fun i : Fin t => stream i)

def GenLimit.Angluin.IsTellTaleApproximation
    (C : LanguageFamily α) (A : ℕ → ℕ → Finset α) : Prop :=
  (∀ i n m, n ≤ m → A i n ⊆ A i m) ∧
  ∀ i, ∃ T : Finset α, IsTellTale C i T ∧
    ∃ N, ∀ n, N ≤ n → A i n = T

def GenLimit.Angluin.ListWithin
    (xs : List α) (L : Set α) : Prop :=
  ∀ x, x ∈ xs → x ∈ L

def GenLimit.Angluin.IsLockingSequence
    (M : List α → ℕ) (L : Set α)
    (xs : List α) (j : ℕ) : Prop :=
  ListWithin xs L ∧
  ∀ tail, ListWithin tail L → M (xs ++ tail) = j

def GenLimit.Angluin.HasChangeExtension
    (M : List α → ℕ) (L : Set α) (xs : List α) : Prop :=
  ∃ tail, ListWithin tail L ∧ M (xs ++ tail) ≠ M xs

def GenLimit.LiRamanTewari.UUS
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → L.Infinite
```

`sequenceSample` and `sample` discard repetitions and expose only finite histories. `IsTellTaleApproximation` has no uniform stabilization stage: its final certificate `T` and stage `N` may depend on the family index `i`. It assumes eventual *equality* to a complete finite tell-tale, not merely convergence element by element. `IsLockingSequence` is a strong supplied-witness condition: every finite continuation drawn from `L` must force exactly the same syntactic index `j`. It does not assert that a lock exists or that `C_j=L`; those are separate bridge conclusions. `HasChangeExtension` is the explicit finite mind-change witness used by the locking-existence interface. `UUS` says only that all languages in a class are infinite and enters Paper 08 solely through the appendix helper `infiniteMembers_uus`.

## 6. Bidirectional correspondence tables

### 6.1 Paper-to-Lean coverage

| Paper claim | Formal declaration(s) | Correspondence verdict | Difficulty verdict | Audit conclusion |
|---|---|---|---|---|
| Definition 1, p. 5 §2.1 | `DetectorCorrectAt`; `DetectsHallucinations`; `HallucinationDetectable` | Exact / formally equivalent | Preserved | Same arbitrary `G`, exact subset predicate, complete positive presentation, and pointwise eventuality. `t>t*` versus `T≤t` is a threshold shift. |
| Informal Result I, p. 2 §1 | `theorem_2_1`; `corollary_2_2` | Related but materially different | Indeterminate | Lean gives the exact characterization but has no quantified notion of “typically,” “most collections,” or practical inherent difficulty. |
| Informal Result II, p. 3 §1 | negative-example definitions; `theorem_2_3` | Faithful generalization | Weakened / easier | The formal theorem proves the advertised positive conclusion for complete perfect labels; arbitrary-type extra scope is vacuous when no labeled enumeration exists. |
| Lemma 3.1, p. 8 §3.1 | `lemma_3_1_identification_implies_detection` | Faithful specialization | Preserved | Lean asks for an explicit surjection `ℕ→α`; the paper obtains one from countability. Exact family-language and candidate membership access is semantic rather than machine-level. |
| Lemma 3.2, p. 9 §3.1 | `lemma_3_2_detection_implies_identification` | Faithful generalization | Preserved | The declaration drops countability because the direction itself does not need a domain enumeration. On any paper instance it is the same implication. |
| Theorem 2.1, p. 7 §2.2 | `theorem_2_1` | Faithful specialization | Preserved | Same semantic biconditional; Lean additionally assumes `Nonempty α`. No efficiency or reduction-cost preservation is claimed by either statement. |
| Finite tell-tale clause of Definition 4, p. 19 §A.1 | imported `IsTellTale`, `ConditionTwo` | Exact / formally equivalent | Preserved | Same inclusion structure and duplicate-index behavior. |
| Tell-tale oracle sentence in Definition 4, p. 19 §A.1 | no primary oracle input or effective enumeration; `chosenTellTale` is a proof-driven full-set chooser | Not represented in Lean | Weakened / easier | The primitive/access contract itself is absent. The nearest helper is materially different: it assumes `ConditionTwo` and uses noncomputable choice. |
| Corollary 2.2, p. 7 §2.2 | `corollary_2_2` | Faithful specialization | Preserved | Correct at the paper's noncomputational semantic level; not an effective characterization. |
| Definition 2, pp. 7–8 §2.2 | labeled-stream and negative-detection definitions | Exact / formally equivalent | Preserved | Complete domain enumeration and perfect labels are preserved; so is pointwise dependence on `G` and stream. |
| Theorem 2.3, p. 8 §2.2 | `theorem_2_3` | Faithful generalization | Weakened / easier | Exact on every valid labeled enumeration; extra arbitrary-type scope is vacuous when such an enumeration cannot exist. |
| Example 1: `L₄⊆L₂`, p. 5 §2.1 | `example_1_L4_subset_L2` | Exact / formally equivalent | Preserved | Correct zero-based encoding. |
| Example 1: `L₃⊄L₂`, p. 5 §2.1 | `example_1_L3_not_subset_L2` | Exact / formally equivalent | Preserved | Correct zero-based encoding. |
| Example 1: no detector, p. 6 §2.1 | `singleton_index_isTellTale`; `example_1_angluinCondition`; `example_1_hallucinationDetectable` | Related but materially different | Indeterminate | Paper claim is false; Lean supplies the correct opposite result. Formal repair, not restatement. |
| Definition 3, p. 19 §A.1 | consecutive-identification definitions plus `definition_3_equivalence` | Exact / formally equivalent | Preserved | Adjacent tail equality is equivalent to stabilization at one index even with duplicate languages. |
| Theorem A.1, p. 19 §A.1 | `theorem_A_1` | Faithful specialization | Preserved | Same semantic condition; nonempty domain restriction and non-effective tell-tales noted. |
| Definition 5, p. 20 §A.2 | appendix generation definitions | Exact / formally equivalent | Preserved | Includes the same empty-unseen-remainder escape clause. |
| Theorem A.2, p. 20 §A.2 | `theorem_A_2` | Faithful specialization | Preserved | Same universal semantic existence result over a nonempty countable domain. |
| `2t−1` fresh family-membership query statement, p. 10 footnote 5 | none | Not represented in Lean | Weakened / easier | Family membership is extensional and uncosted; no query counter or bound appears. |
| Probabilistic carry-over assertion, p. 6 §2.1 | none | Not represented in Lean | Indeterminate | No distributions, stochastic presentations, almost-sure/eventual probability, or error bounds occur. |

### 6.2 Complete Lean-to-paper reverse correspondence

Every public primary declaration is listed here once; §21 supplies its full signature and detailed audit.

| Ledger | Fully qualified Lean declaration | Paper counterpart | Correspondence verdict | Difficulty verdict |
|---|---|---|---|---|
| D01 | `GenLimit.HallucinationDetection.OracleTree` | Finite membership queries in Definition 1, p. 5 §2.1. | Faithful specialization | Preserved |
| D02 | `GenLimit.HallucinationDetection.OracleTree.eval` | Exact membership-query answers to `G`, p. 5 §2.1. | Faithful specialization | Preserved |
| D03 | `GenLimit.HallucinationDetection.Detector` | Detector sequence `D=(D_t)` in Definition 1, p. 5 §2.1. | Faithful specialization | Preserved |
| D04 | `GenLimit.HallucinationDetection.detectorOutput` | Round output in Definition 1, p. 5 §2.1. | Exact / formally equivalent | Preserved |
| D05 | `GenLimit.HallucinationDetection.DetectorCorrectAt` | Indicator equality `d_t=1{G⊆K}` in Definition 1, p. 5 §2.1. | Exact / formally equivalent | Preserved |
| D06 | `GenLimit.HallucinationDetection.DetectsHallucinations` | Definition 1, p. 5 §2.1. | Exact / formally equivalent | Preserved |
| D07 | `GenLimit.HallucinationDetection.HallucinationDetectable` | Collection-level existential in Definition 1, p. 5 §2.1. | Exact / formally equivalent | Preserved |
| D08 | `GenLimit.HallucinationDetection.IdentifiableInLimit` | Definition 3, p. 19 §A.1, via stable-index equivalence. | Exact / formally equivalent | Preserved |
| D09 | `GenLimit.HallucinationDetection.LabeledStream` | Labeled enumeration in Definition 2, pp. 7–8 §2.2. | Exact / formally equivalent | Preserved |
| D10 | `GenLimit.HallucinationDetection.IsLabeledEnumeration` | Definition 2, pp. 7–8 §2.2. | Exact / formally equivalent | Preserved |
| D11 | `GenLimit.HallucinationDetection.NegativeExampleDetector` | Detector interface in Definition 2, pp. 7–8 §2.2. | Faithful specialization | Preserved |
| D12 | `GenLimit.HallucinationDetection.negativeDetectorOutput` | Round output in Definition 2, pp. 7–8 §2.2. | Exact / formally equivalent | Preserved |
| D13 | `GenLimit.HallucinationDetection.NegativeDetectorCorrectAt` | Indicator equality in Definition 2, pp. 7–8 §2.2. | Exact / formally equivalent | Preserved |
| D14 | `GenLimit.HallucinationDetection.DetectsWithNegativeExamples` | Definition 2, pp. 7–8 §2.2. | Exact / formally equivalent | Preserved |
| D15 | `GenLimit.HallucinationDetection.DetectableWithNegativeExamples` | Collection-level existential in Definition 2, pp. 7–8 §2.2. | Exact / formally equivalent | Preserved |
| D16 | `GenLimit.HallucinationDetection.domainPrefix` | Growing domain prefix in Algorithm 1, pp. 8–9 §3.1. | Exact / formally equivalent | Preserved |
| D17 | `GenLimit.HallucinationDetection.mem_domainPrefix_iff` | Implicit finite-prefix fact used by Algorithm 1, pp. 8–9. | Extra Lean result not claimed by the paper | Preserved |
| D18 | `GenLimit.HallucinationDetection.subsetTestTree` | Finite local subset scan in Algorithm 1, pp. 8–9. | Faithful specialization | Preserved |
| D19 | `GenLimit.HallucinationDetection.eval_subsetTestTree_eq_true_iff` | Correctness of Algorithm 1 finite scan, pp. 8–9. | Extra Lean result not claimed by the paper | Preserved |
| D20 | `GenLimit.HallucinationDetection.detectorFromIdentifier` | Algorithm 1, pp. 8–9 §3.1. | Exact / formally equivalent | Preserved |
| D21 | `GenLimit.HallucinationDetection.lemma_3_1_identification_implies_detection` | Lemma 3.1, p. 8 §3.1. | Faithful specialization | Preserved |
| D22 | `GenLimit.HallucinationDetection.DetectorCandidate` | Two candidate tests and bounded scope in Algorithm 2, pp. 10–11. | Exact / formally equivalent | Preserved |
| D23 | `GenLimit.HallucinationDetection.identifierFromDetector` | Least-index choice in Algorithm 2, pp. 10–11. | Exact / formally equivalent | Preserved |
| D24 | `GenLimit.HallucinationDetection.identifierFromDetector_candidate` | Implicit least-candidate property of Algorithm 2, pp. 10–11 §3.1. | Extra Lean result not claimed by the paper | Preserved |
| D25 | `GenLimit.HallucinationDetection.identifierFromDetector_le_of_candidate` | Implicit minimality property of Algorithm 2, pp. 10–11 §3.1. | Extra Lean result not claimed by the paper | Preserved |
| D26 | `GenLimit.HallucinationDetection.lemma_3_2_detection_implies_identification` | Lemma 3.2, p. 9 §3.1. | Faithful generalization | Preserved |
| D27 | `GenLimit.HallucinationDetection.theorem_2_1` | Theorem 2.1, p. 7 §2.2. | Faithful specialization | Preserved |
| D28 | `GenLimit.HallucinationDetection.chosenTellTale` | Paper tell-tale oracle sentence, Definition 4 p. 19. | Related but materially different | Weakened / easier |
| D29 | `GenLimit.HallucinationDetection.chosenTellTale_spec` | Specification expected of a tell-tale primitive, Definition 4 p. 19. | Related but materially different | Weakened / easier |
| D30 | `GenLimit.HallucinationDetection.constantTellTaleApproximation` | Paper mentions an enumeration of `T_i`, Definition 4 p. 19. | Related but materially different | Weakened / easier |
| D31 | `GenLimit.HallucinationDetection.constantTellTaleApproximation_spec` | Tell-tale enumeration semantics surrounding Definition 4 p. 19. | Related but materially different | Weakened / easier |
| D32 | `GenLimit.HallucinationDetection.identifiable_of_conditionTwo` | Sufficiency direction of Theorem A.1, p. 19 §A.1, and Corollary 2.2, p. 7 §2.2. | Faithful generalization | Preserved |
| D33 | `GenLimit.HallucinationDetection.listIdentifierOf` | No separately stated paper result. | Extra Lean result not claimed by the paper | Preserved |
| D34 | `GenLimit.HallucinationDetection.listIdentifierOf_streamPrefix` | No separately stated paper result. | Extra Lean result not claimed by the paper | Preserved |
| D35 | `GenLimit.HallucinationDetection.ListConvergesTo` | Stable tail underlying Definition 3, p. 19 §A.1. | Faithful specialization | Preserved |
| D36 | `GenLimit.HallucinationDetection.presentationFromDomainEnumeration` | Existence of positive enumerations implicit in the model, p. 5. | Extra Lean result not claimed by the paper | Indeterminate |
| D37 | `GenLimit.HallucinationDetection.presentationFromDomainEnumeration_presents` | Positive enumeration existence implicit in pp. 5, 19. | Extra Lean result not claimed by the paper | Preserved |
| D38 | `GenLimit.HallucinationDetection.exists_lockingSequence_of_identifies_with_presentation` | Locking argument implicit in Angluin characterization, Theorem A.1 p. 19. | Extra Lean result not claimed by the paper | Preserved |
| D39 | `GenLimit.HallucinationDetection.lockingSequence_correct_with_presentation` | Locking correctness implicit in Theorem A.1, p. 19 §A.1. | Extra Lean result not claimed by the paper | Preserved |
| D40 | `GenLimit.HallucinationDetection.lockingSequence_isTellTale_with_presentations` | Necessity logic behind Theorem A.1, p. 19 §A.1. | Extra Lean result not claimed by the paper | Preserved |
| D41 | `GenLimit.HallucinationDetection.lockingSequence_isTellTale_with_nonempty_presentations` | Empty-language-aware necessity logic behind Theorem A.1, p. 19 §A.1. | Extra Lean result not claimed by the paper | Preserved |
| D42 | `GenLimit.HallucinationDetection.append_mem_isLockingSequence` | No separate paper result. | Extra Lean result not claimed by the paper | Preserved |
| D43 | `GenLimit.HallucinationDetection.conditionTwo_of_identifiable` | Necessity direction of Theorem A.1, p. 19 §A.1, and Corollary 2.2, p. 7 §2.2. | Faithful specialization | Preserved |
| D44 | `GenLimit.HallucinationDetection.corollary_2_2` | Corollary 2.2, p. 7 §2.2. | Faithful specialization | Preserved |
| D45 | `GenLimit.HallucinationDetection.ConsecutivelyIdentifiesFrom` | Definition 3, p. 19 §A.1. | Exact / formally equivalent | Preserved |
| D46 | `GenLimit.HallucinationDetection.ConsecutivelyIdentifies` | Collection-level Definition 3, p. 19 §A.1. | Exact / formally equivalent | Preserved |
| D47 | `GenLimit.HallucinationDetection.ConsecutivelyIdentifiable` | Existential in Definition 3, p. 19 §A.1. | Exact / formally equivalent | Preserved |
| D48 | `GenLimit.HallucinationDetection.semanticallyIdentifies_implies_consecutivelyIdentifies` | No separate paper result; validates encoding of Definition 3. | Extra Lean result not claimed by the paper | Preserved |
| D49 | `GenLimit.HallucinationDetection.consecutivelyIdentifies_implies_semanticallyIdentifies` | No separate paper result; validates encoding of Definition 3. | Extra Lean result not claimed by the paper | Preserved |
| D50 | `GenLimit.HallucinationDetection.definition_3_equivalence` | Definition 3, p. 19 §A.1. | Exact / formally equivalent | Preserved |
| D51 | `GenLimit.HallucinationDetection.theorem_A_1` | Theorem A.1, p. 19 §A.1. | Faithful specialization | Preserved |
| D52 | `GenLimit.HallucinationDetection.AppendixGenerationCorrectAt` | Definition 5, p. 20 §A.2. | Exact / formally equivalent | Preserved |
| D53 | `GenLimit.HallucinationDetection.AppendixGeneratesInLimit` | Definition 5, p. 20 §A.2. | Exact / formally equivalent | Preserved |
| D54 | `GenLimit.HallucinationDetection.AppendixGeneratableInLimit` | Collection existential in Definition 5, p. 20 §A.2. | Exact / formally equivalent | Preserved |
| D55 | `GenLimit.HallucinationDetection.infiniteMembers` | No separate paper result. | Extra Lean result not claimed by the paper | Preserved |
| D56 | `GenLimit.HallucinationDetection.infiniteMembers_countable` | No separate paper result. | Extra Lean result not claimed by the paper | Preserved |
| D57 | `GenLimit.HallucinationDetection.infiniteMembers_uus` | No separate paper result. | Extra Lean result not claimed by the paper | Preserved |
| D58 | `GenLimit.HallucinationDetection.theorem_A_2` | Theorem A.2, p. 20 §A.2. | Faithful specialization | Preserved |
| D59 | `GenLimit.HallucinationDetection.multiplesFamily` | Example 1, pp. 5–6 §2.1. | Faithful specialization | Preserved |
| D60 | `GenLimit.HallucinationDetection.mem_multiplesFamily` | Defining membership in Example 1, p. 5 §2.1. | Exact / formally equivalent | Preserved |
| D61 | `GenLimit.HallucinationDetection.multiplesFamily_allNonempty` | Implicit fact about Example 1, p. 5 §2.1. | Extra Lean result not claimed by the paper | Preserved |
| D62 | `GenLimit.HallucinationDetection.singleton_index_isTellTale` | Contradicts the no-detector sentence after Example 1, p. 6. | Related but materially different | Indeterminate |
| D63 | `GenLimit.HallucinationDetection.example_1_angluinCondition` | Contradicts the no-detector sentence after Example 1, p. 6. | Related but materially different | Indeterminate |
| D64 | `GenLimit.HallucinationDetection.example_1_L4_subset_L2` | First containment in Example 1, p. 5. | Exact / formally equivalent | Preserved |
| D65 | `GenLimit.HallucinationDetection.example_1_L3_not_subset_L2` | Second containment in Example 1, p. 5. | Exact / formally equivalent | Preserved |
| D66 | `GenLimit.HallucinationDetection.example_1_hallucinationDetectable` | Opposite of the sentence on p. 6 after Example 1. | Related but materially different | Indeterminate |
| D67 | `GenLimit.HallucinationDetection.labeledPrefix` | Finite labeled history in Definition 2, pp. 7–8 §2.2, and proof of Theorem 2.3, pp. 12–13 §3.2. | Exact / formally equivalent | Preserved |
| D68 | `GenLimit.HallucinationDetection.mem_labeledPrefix_iff` | Implicit finite-prefix fact in the proof of Theorem 2.3, pp. 12–13 §3.2. | Extra Lean result not claimed by the paper | Preserved |
| D69 | `GenLimit.HallucinationDetection.negativeExampleTree` | Explicit strategy in proof of Theorem 2.3, pp. 12–13. | Exact / formally equivalent | Preserved |
| D70 | `GenLimit.HallucinationDetection.eval_negativeExampleTree_eq_true_iff` | Correctness of finite test in proof of Theorem 2.3, pp. 12–13. | Extra Lean result not claimed by the paper | Preserved |
| D71 | `GenLimit.HallucinationDetection.negativeExampleDetector` | Detector strategy in proof of Theorem 2.3, pp. 12–13. | Exact / formally equivalent | Preserved |
| D72 | `GenLimit.HallucinationDetection.theorem_2_3` | Theorem 2.3, p. 8 §2.2. | Faithful generalization | Weakened / easier |

## 7. Detailed audit of the central equivalence

### 7.1 Main theorem signature and complete quantifiers

**Paper:** Theorem 2.1, p. 7, §2.2.

**Lean:** `GenLimit.HallucinationDetection.theorem_2_1`, file
`GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`:

```lean
theorem theorem_2_1
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    HallucinationDetectable C ↔ IdentifiableInLimit C
```

Fully expanded, this is the biconditional between the formulas in §§5.3–5.4. The detector threshold may depend on target index, full presentation, and candidate set. The identifier's limiting representative and threshold may depend on target index and presentation. Neither threshold is uniform. The paper has the same dependencies; its order of the two universal variables `G` and `E` is immaterial because both precede the existential stabilization time.

**Correspondence verdict:** Faithful specialization
**Difficulty verdict:** Preserved

The specialization is `[Nonempty α]`. For the empty domain the paper's games have no infinite presentations, so both sides are vacuous; Lean simply omits that degenerate case from the top-level theorem.

### 7.2 Identification to detection

**Paper:** Lemma 3.1 and Algorithm 1, pp. 8–9, §3.1.

**Lean reduction statement:**

```lean
theorem GenLimit.HallucinationDetection.lemma_3_1_identification_implies_detection
    (C : GenLimit.Generic.LanguageFamily α)
    (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    (hID : IdentifiableInLimit C) :
    HallucinationDetectable C
```

The explicit construction declarations are:

```lean
def domainPrefix (enumerate : ℕ → α) (t : ℕ) : List α :=
  List.ofFn (fun i : Fin t => enumerate i)

noncomputable def subsetTestTree (L : Set α) : List α → OracleTree α
  | [] => .answer true
  | x :: xs =>
      if x ∈ L then subsetTestTree L xs
      else .query x (.answer false) (subsetTestTree L xs)

noncomputable def detectorFromIdentifier
    (C : GenLimit.Generic.LanguageFamily α)
    (enumerate : ℕ → α)
    (M : GenLimit.Angluin.SemanticIdentifier α) : Detector α :=
  fun t xs => subsetTestTree (C (M t xs)) (domainPrefix enumerate t)
```

The separate evaluation theorem states exactly:

```lean
theorem eval_subsetTestTree_eq_true_iff
    (G L : Set α) (xs : List α) :
    OracleTree.eval G (subsetTestTree L xs) = true ↔
      ∀ x, x ∈ xs → x ∈ G → x ∈ L
```

This finite tree checks the paper's local predicate on the growing domain prefix. It does not query `G` at points already known to belong to the current conjectured language, an equivalent optimization. Surjectivity—not injectivity—is sufficient because every counterexample `x∈G\K` must eventually occur.

The formal construction uses exact membership in the current family language while building the tree. This corresponds to the paper's membership oracle for `𝓛` (p. 5 and Algorithm 1), but the access is represented extensionally and noncomputably rather than as an explicit oracle argument. It does not already decide `G⊆K`: it only decides membership pointwise and still needs eventual identification plus unbounded domain scanning.

Each produced tree is finite and, from the recursive definition, contains at most one candidate query per listed point; no theorem signature records the `≤t` bound. There is no bound on family-membership work or tree-construction time.

There is also no public theorem whose conclusion explicitly names `detectorFromIdentifier`, such as `DetectsHallucinations (detectorFromIdentifier …) C`. The existence reduction and named construction are separately stated. Their intended relationship is transparent from definitions, but it is not encoded in the existential theorem's type.

**Correspondence verdict:** Faithful specialization
**Difficulty verdict:** Preserved

### 7.3 Detection to identification

**Paper:** Lemma 3.2 and Algorithm 2, pp. 9–12, §3.1.

**Lean reduction statement:**

```lean
theorem GenLimit.HallucinationDetection.lemma_3_2_detection_implies_identification
    (C : GenLimit.Generic.LanguageFamily α)
    (hHD : HallucinationDetectable C) :
    IdentifiableInLimit C
```

The candidate predicate unfolds to

```lean
def DetectorCandidate
    (C : GenLimit.Generic.LanguageFamily α) (D : Detector α)
    {t : ℕ} (xs : Fin t → α) (i : ℕ) : Prop :=
  i ≤ t ∧
  (↑(GenLimit.Generic.sequenceSample xs) : Set α) ⊆ C i ∧
  OracleTree.eval (C i) (D t xs) = true
```

Thus a candidate index must be bounded, contain all distinct positive examples, and receive a positive detector answer when the detector's candidate-set oracle is exactly the family language `C_i`. This is the paper's two-test construction. The exact membership oracle for `C_i` is permitted by the paper's family-membership-access assumption; it does not directly reveal whether `C_i⊆K`, because the target `K` is unknown and only the detector's eventual behavior supplies that relation.

The selected identifier is

```lean
noncomputable def identifierFromDetector
    (C : GenLimit.Generic.LanguageFamily α) (D : Detector α) :
    GenLimit.Angluin.SemanticIdentifier α := by
  classical
  exact fun t xs =>
    if h : ∃ i, DetectorCandidate C D xs i then Nat.find h else 0
```

`identifierFromDetector_candidate` says the selected index is a candidate whenever one exists, and `identifierFromDetector_le_of_candidate` says it is no larger than any supplied candidate. These are genuine least-witness properties but do not themselves establish eventual existence or convergence.

Duplicate indices are handled correctly: identification may stabilize to any extensionally correct representative, while this construction is designed around the least one. The theorem's final `IdentifiableInLimit` conclusion preserves the paper's requirement of one stable syntactic index.

The bounded index condition makes the *set of indices* finite at each round, but there is no executable finite search theorem. `DetectorCandidate` is a proposition involving arbitrary-set membership and noncomputable oracle evaluation; `identifierFromDetector` uses classical `Nat.find`. The paper likewise imposes no computational restrictions, but its footnoted family-query count is not formalized.

As in the other direction, no public theorem directly states that the named `identifierFromDetector C D` semantically identifies `C` under a displayed detector hypothesis; the reduction theorem asserts only existential identification.

**Correspondence verdict:** Faithful generalization
**Difficulty verdict:** Preserved

The generalization is the absence of countability/nonemptiness assumptions in this direction. It is not a stronger effective result.

## 8. Detailed audit of Angluin's condition and certificate access

### 8.1 Paper claim

Definition 4 (p. 19, §A.1) first states the finite tell-tale property and then adds: “the tell-tale oracle is a primitive that, given an index `i`, outputs an enumeration of the set `T_i`.” Corollary 2.2 (p. 7, §2.2) and Theorem A.1 (p. 19, §A.1) use “Angluin's condition.” The paper also says there are no computational restrictions (p. 7, §2.1).

### 8.2 Formal condition and main signatures

```lean
theorem GenLimit.HallucinationDetection.identifiable_of_conditionTwo
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    IdentifiableInLimit C

theorem GenLimit.HallucinationDetection.conditionTwo_of_identifiable
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α)
    (hID : IdentifiableInLimit C) :
    GenLimit.Angluin.ConditionTwo C

theorem GenLimit.HallucinationDetection.corollary_2_2
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    HallucinationDetectable C ↔ GenLimit.Angluin.ConditionTwo C
```

The finite-set predicate itself is exact. The operational oracle sentence is not represented in these types.

### 8.3 Nonuniform existential tell-tales and answer-encoding helpers

```lean
noncomputable def chosenTellTale
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) (i : ℕ) : Finset α :=
  Classical.choose (h i)

noncomputable def constantTellTaleApproximation
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    ℕ → ℕ → Finset α :=
  fun i _stage => chosenTellTale C h i
```

The `ConditionTwo` proof is an answer-containing hypothesis: for each index it proves that some complete finite certificate exists. `chosenTellTale` uses classical choice to select the certificate; `constantTellTaleApproximation` makes that complete selected certificate available at stage zero and every later stage. Its specification only says the constant sequence is monotone and eventually equals a tell-tale. This is not discovery or enumeration.

No target-scope theorem establishes any of the following:

* a computable function `i ↦ T_i`;
* a computable stage emitter;
* an effective way to recognize that enumeration of `T_i` is complete;
* a uniform bound on `|T_i|`;
* `ConditionTwo → ConditionOne`;
* a computable identifier from `ConditionTwo`.

The imported dependency explicitly distinguishes `ConditionOne`, which includes a `Computable₂ emit`, from `ConditionTwo`. The available dependency theorem

```lean
theorem GenLimit.Angluin.ConditionOne.semantic_sufficiency
    {F : EffectiveIndexedFamily} (h : ConditionOne F) :
    ∃ M : SemanticIdentifier ℕ,
      SemanticallyIdentifies M F.language
```

still concludes only semantic identification. Conversely,

```lean
theorem GenLimit.Angluin.effectiveInferrable_conditionTwo
    {F : EffectiveIndexedFamily} (h : EffectiveInferrable F) :
    ConditionTwo F.language
```

establishes only necessity of nonuniform existence. There is no declaration in the bundle establishing effective discovery from `ConditionTwo`.

### 8.4 Locking helpers and circularity audit

The necessity direction is decomposed into separately stated conditional facts:

* `exists_lockingSequence_of_identifies_with_presentation` assumes one exact base presentation and convergence on every presentation of a fixed language, and concludes existence of a syntactic locking sequence. This is a genuine independent statement; it does not assume a tell-tale or the desired family equality.
* `lockingSequence_correct_with_presentation` assumes semantic identification of the fixed target plus a supplied lock and concludes that the lock's index denotes the target. The hypothesis says some correct limit exists on each presentation; it does not directly assert correctness of the separately supplied locked index.
* `lockingSequence_isTellTale_with_presentations` assumes full identification, presentability of every family member, a supplied lock, and a supplied equality linking its index to the target; it concludes a tell-tale. The equality is an overstrong link input for this helper, but the desired tell-tale conclusion quantifies over every candidate sublanguage and is not merely the equality restated.
* `lockingSequence_isTellTale_with_nonempty_presentations` weakens presentability to nonempty candidates but requires a nonempty locking history. This avoids needing a presentation of an empty candidate.
* `append_mem_isLockingSequence` preserves an existing lock after appending one supplied target member; it does not find either the lock or the member.
* `conditionTwo_of_identifiable` has no locking-sequence or correctness witness in its public assumptions. Thus the main necessity statement is not circular, even though several internal bridge statements are intentionally conditional.

For an empty indexed target, positive identification is vacuous and the empty finset is a tell-tale. The main equivalence therefore remains true but says nothing operational about learning that target.

### 8.5 Verdict

**Correspondence verdict:** Faithful specialization
**Difficulty verdict:** Preserved

This verdict is restricted to the paper's explicitly noncomputational semantic/oracle reading. The finite tell-tale predicate is exact, and the paper itself grants a tell-tale primitive. Under an effective reading, the formal theorem would be materially easier because classical choice and a constant full-certificate approximation replace discovery. The supplied PDF does not specify a machine model for the tell-tale oracle, so that effective interpretation is indeterminate from the supplied evidence.

## 9. Detailed audit of negative examples

### 9.1 Paper definition and theorem

Definition 2 (pp. 7–8, §2.2) replaces the positive presentation by a labeled enumeration of the **entire domain**. Theorem 2.3 (p. 8, §2.2) asserts universal detectability for every countable family over a countable domain.

### 9.2 Formal statement and explicit local test

```lean
theorem GenLimit.HallucinationDetection.theorem_2_3
    (C : GenLimit.Generic.LanguageFamily α) :
    DetectableWithNegativeExamples C
```

Expanded, this asserts existence of one detector `D` such that for every index `z`, every stream whose first coordinates cover `Set.univ` and whose labels are exactly target membership, every candidate `G`, there is a threshold after which

\[
\operatorname{eval}_G(D(t,\text{labeled-prefix}))=\mathrm{true}
\iff G\subseteq C_z.
\]

The named tree is

```lean
def negativeExampleTree : List (α × Bool) → OracleTree α
  | [] => .answer true
  | (_x, true) :: xs => negativeExampleTree xs
  | (x, false) :: xs =>
      .query x (.answer false) (negativeExampleTree xs)
```

and its exact finite-prefix semantics are separately stated as

```lean
theorem eval_negativeExampleTree_eq_true_iff
    (G : Set α) (xs : List (α × Bool)) :
    OracleTree.eval G (negativeExampleTree xs) = true ↔
      ∀ x b, (x, b) ∈ xs → b = false → x ∉ G
```

Thus the local test accepts exactly when no observed negatively labeled point lies in `G`. It queries at most one point per negative-labeled list entry, hence finitely many per round; there is no formal query-count theorem.

The named detector is

```lean
def negativeExampleDetector : NegativeExampleDetector α :=
  fun _t xs => negativeExampleTree (List.ofFn xs)
```

but `theorem_2_3` has an existential conclusion and does not name this detector. No separate public declaration has conclusion `DetectsWithNegativeExamples negativeExampleDetector C`. The intended link is visible from the definitions and evaluation theorem, but not from the existential theorem's type alone.

### 9.3 Scope and vacuity

The paper assumes a countable domain. The Lean theorem has no typeclass assumptions. This is harmless on every valid labeled stream, because validity itself gives a surjection `ℕ→α`. For uncountable or empty `α`, no valid stream exists and `DetectsWithNegativeExamples` is vacuously true. Thus the statement is a faithful generalization on realizable instances but a weakened/easier theorem globally.

The data are much stronger than ordinary supervised samples: they eventually reveal the exact target-membership bit of every domain point. The detector still needs candidate membership queries because it must determine whether any target-negative point belongs to `G`.

**Correspondence verdict:** Faithful generalization
**Difficulty verdict:** Weakened / easier

The qualifier applies only to the vacuous extra scope; on the paper's countable domain with a valid complete labeled enumeration, the mathematical task and explicit test are preserved.

## 10. Direct arithmetic audit of Example 1

### 10.1 Paper statements

Example 1 defines `L_i={i·j:j∈ℕ_{>0}}`, takes `K=L₂`, and correctly states `L₄⊆L₂` and `L₃⊄L₂` (p. 5, §2.1). The next page states that no hallucination detector exists for the entire multiples family (p. 6, §2.1).

### 10.2 Formal encoding and calculations

```lean
def GenLimit.HallucinationDetection.multiplesFamily :
    GenLimit.Generic.LanguageFamily ℕ :=
  fun i => {x | i + 1 ∣ x + 1}
```

Lean index `i` and point `x` encode paper integers `i+1` and `x+1`. The formal containments are

```lean
theorem example_1_L4_subset_L2 :
    multiplesFamily 3 ⊆ multiplesFamily 1

theorem example_1_L3_not_subset_L2 :
    ¬ multiplesFamily 2 ⊆ multiplesFamily 1
```

These are exact.

### 10.3 Direct tell-tale calculation

For paper index `i≥1`, take `T_i={i}`. Then `T_i⊆L_i`. If `T_i⊆L_j`, then `i∈L_j`, so `j` divides `i`. Every multiple of `i` is consequently a multiple of `j`, hence `L_i⊆L_j`. Therefore `L_j` cannot be a proper subset of `L_i`. This is precisely Definition 4.

The corresponding formal statements are

```lean
theorem singleton_index_isTellTale (i : ℕ) :
    GenLimit.Angluin.IsTellTale multiplesFamily i {i}

theorem example_1_angluinCondition :
    GenLimit.Angluin.ConditionTwo multiplesFamily

theorem example_1_hallucinationDetectable :
    HallucinationDetectable multiplesFamily
```

The paper's no-detector sentence is therefore contradicted by its own definitions and Corollary 2.2. This is a **source error**. The formal declarations are a correct repair.

**Correspondence verdict:** Related but materially different
**Difficulty verdict:** Indeterminate

The two sides assert opposite propositions, so a same-direction difficulty comparison is not meaningful under the permitted categories.

## 11. Appendix results

### 11.1 Definition 3 and stable-index equivalence

The paper's Definition 3 (p. 19, §A.1) is encoded literally by

```lean
def ConsecutivelyIdentifiesFrom
    (M : GenLimit.Angluin.SemanticIdentifier α)
    (C : GenLimit.Generic.LanguageFamily α) (z : ℕ)
    (stream : GenLimit.Generic.Stream α) : Prop :=
  ∃ T, ∀ t, T < t →
    identifierOutput M stream t = identifierOutput M stream (t - 1) ∧
    C (identifierOutput M stream t) = C z
```

with collection-level universal and existential wrappers. The two bridge theorems state both implication directions between this adjacent-equality form and the shared stable-index form; `definition_3_equivalence` states the collection-level biconditional. These bridges preserve duplicate indices because eventual adjacent equality forces one syntactic tail value.

**Correspondence verdict:** Exact / formally equivalent
**Difficulty verdict:** Preserved

### 11.2 Theorem A.1

```lean
theorem GenLimit.HallucinationDetection.theorem_A_1
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    ConsecutivelyIdentifiable C ↔ GenLimit.Angluin.ConditionTwo C
```

This matches Theorem A.1 (p. 19, §A.1) at the paper's semantic level, with the same nonempty-domain specialization and the same non-effective certificate caveat.

**Correspondence verdict:** Faithful specialization
**Difficulty verdict:** Preserved

### 11.3 Definition 5 and Theorem A.2

The appendix generation definitions preserve exact presentation, target-dependent stabilization time, freshness relative to all distinct observations, and the explicit `unseen remainder = ∅` escape. The main declaration is

```lean
theorem GenLimit.HallucinationDetection.theorem_A_2
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    AppendixGeneratableInLimit C
```

It represents the paper's stated Theorem A.2 (p. 20, §A.2). The helper declarations `infiniteMembers`, `infiniteMembers_countable`, and `infiniteMembers_uus` are extra formal infrastructure; the theorem signature itself does not expose a named generator or distinguish finite and infinite targets.

For a finite target, the conclusion can become automatic once the presentation has exhausted the target, because the output is then unrestricted. For an empty target, no exact presentation exists and the requirement is vacuous.

**Correspondence verdict:** Faithful specialization
**Difficulty verdict:** Preserved

## 12. Quantifier, dependence, and access ledger

| Formal property | Exact quantifier/dependence | Runtime access | Hidden or absent requirements |
|---|---|---|---|
| `DetectsHallucinations D C` | `∀z ∀stream, Presents stream C_z → ∀G ∃T ∀t≥T` | finite positive prefix; finite adaptive exact membership queries to `G` | `T` may depend on target, entire presentation, and `G`; no uniform bound or computability |
| `HallucinationDetectable C` | `∃D` before all targets/streams/candidates | detector may be noncomputably hardwired to whole `C` | no explicit family-membership oracle argument |
| `SemanticallyIdentifies M C` | `∀z ∀stream, Presents → ∃j, C_j=C_z ∧ ∃T ∀t≥T` | finite positive prefix only | `j,T` may depend on target and presentation; duplicate indices allowed |
| `ConditionTwo C` | `∀i ∃T_i finite` | no online access object at all | no selector, enumeration, size bound, computability, or uniformity |
| `DetectsWithNegativeExamples D C` | `∀z ∀labeledStream, valid → ∀G ∃T ∀t≥T` | finite complete-label prefix; finite adaptive exact queries to `G` | valid stream must cover whole domain and label perfectly; `T` may depend on all fixed data |
| `ConsecutivelyIdentifiesFrom` | `∃T ∀t>T` adjacent equality plus target-language equality | finite positive prefix | equivalent to stable index; uses `t−1` after a strict lower bound |
| `AppendixGeneratesInLimit` | `∀z ∀stream, Presents → ∃T ∀t≥T` | finite positive prefix | no candidate oracle; output unrestricted after finite target exhausted |

The target language/index is never a runtime argument to the detector or identifier. Future presentation values are not exposed. The complete stream appears only in the specification and through its current prefix. Proof-side presentation constructors do receive the target set and exact membership, but they are not learner inputs.

## 13. Finite-query and computational audit

1. **Candidate queries are finite syntax per round.** `OracleTree` is an inductive finite tree. This is genuine finiteness, not an unrestricted set-functional call.
2. **There is no uniform query bound.** No declaration counts nodes, depth, or queries. For the two explicit trees one can read a linear per-prefix bound from the recursive definitions, but that bound is not asserted in a theorem signature.
3. **Family membership is uncosted.** The reductions inspect propositions `x∈C_i` and evaluate detector trees against `C_i` extensionally. The paper's family-membership oracle and its `2t−1` fresh-query observation are not modeled quantitatively.
4. **No actual computability is asserted.** Principal functions may be explicitly `noncomputable`; principal properties contain no `Computable`, partial-recursive, oracle-machine, or code-extraction predicate.
5. **No runtime preservation is asserted by “equivalence.”** Theorem 2.1 is an existence biconditional, not a polynomial-time or query-preserving reduction theorem.
6. **Exact oracles do not directly answer the target relation.** Candidate membership and family-language membership are pointwise. The key subset/equality decisions still arise from limiting behavior and positive-data consistency. The exception is the tell-tale sufficiency side, where a `ConditionTwo` proof plus classical choice supplies complete certificates nonconstructively.

## 14. Vacuity and edge-case audit

* **Empty positive target:** no exact stream has empty range on a nonempty domain. Detection and identification obligations are vacuous. The empty finset satisfies the tell-tale condition for an empty family language.
* **Unpresentable language over arbitrary `α`:** helper theorems without countability can have vacuous identification premises for languages with no `ℕ`-indexed exact presentation.
* **Uncountable or empty domain in Theorem 2.3:** no valid complete labeled enumeration, so the universal implication is vacuous.
* **Finite target in Theorem A.2:** after all target elements are seen, the formal correctness disjunction imposes no constraint on output.
* **Candidate `G=∅`:** subsethood is always true, so a correct detector must eventually accept; this is not problematic but is an easy case.
* **Duplicate family indices:** identification must stabilize syntactically, but the stable index need only denote the target extensionally. The reductions and appendix bridge preserve this distinction.
* **No candidate-family restriction:** `G` is any set, including noncomputable sets; this matches the paper's explicit remark in Example 1.

## 15. Statement-level helper and link audit

| Helper/link | Fully expanded role | Independent, circular, answer-encoding, or vacuous? | Separate establishment in signatures |
|---|---|---|---|
| `OracleTree.eval` | exact finite adaptive membership evaluation against `G` | genuine oracle semantics; noncomputable for arbitrary set | evaluation equations are the definition |
| `subsetTestTree` | local check of `G⊆L` on a finite list | genuine finite local test; uses exact membership in `L` | `eval_subsetTestTree_eq_true_iff` states exact behavior |
| `detectorFromIdentifier` | current identifier index + growing domain prefix | genuine construction; no target/future input; no named correctness theorem | existence reduction is separate and existential |
| `DetectorCandidate` | bounded index + positive consistency + detector says `C_i⊆K` | genuine bridge; exact `C_i` oracle supplied as paper permits | candidate and minimality lemmas only; convergence is in separate reduction theorem |
| `identifierFromDetector` | least candidate or default `0` | noncomputable least witness; default has no correctness content | candidate/minimality theorems; no named full identification theorem |
| `chosenTellTale` | choose `T_i` from `ConditionTwo` proof | answer-encoding/nonconstructive packaging | `chosenTellTale_spec` directly packages `Classical.choose_spec` |
| `constantTellTaleApproximation` | final chosen `T_i` at every stage | stronger than discovery; stage stabilization is tautological | `constantTellTaleApproximation_spec` only certifies the packaging |
| locking-existence helper | convergence on all presentations ⇒ a syntactic lock | genuine independent diagonal statement; nonvacuous only with base presentation | explicit theorem signature |
| locking-correctness helper | supplied lock + semantic identification ⇒ locked index is correct | genuine link, not conclusion restated | explicit theorem signature |
| locking-to-tell-tale helpers | supplied correct lock ⇒ finite certificate | strong link assumptions but stronger all-candidate conclusion | explicit theorem signatures; main necessity theorem removes helper witnesses |
| `IsLabeledEnumeration` | surjective whole-domain stream + exact labels | very strong access; can be unsatisfiable | definition only; theorem 2.3 is conditional on it |
| `negativeExampleTree` | reject if an observed target-negative point lies in `G` | genuine finite local test | exact evaluation theorem; no named full-detector correctness theorem |
| consecutive/stable bridge | adjacent tail equality ↔ fixed tail index | genuine elementary equivalence, no extra access | both directions and collection-level biconditional are explicit |
| finite-target escape | `fresh-valid ∨ no unseen target remains` | can trivialize late finite-target rounds | directly contained in definition, not hidden in proof |

## 16. Dependency/interface ledger

Only the following imported interfaces materially enter Paper 08 statement types:

* `GenLimit.Generic.Language`, `LanguageClass`, `LanguageFamily`, `Stream`, `Generator`, `Presents`, `sequenceSample`, `sample`, and `output` from `Core/Countable.lean`.
* `GenLimit.Angluin.SemanticIdentifier`, `identifierOutput`, `ConvergesTo`, `IdentifiesFrom`, `SemanticallyIdentifies`, `IsTellTale`, `ConditionTwo`, and `IsTellTaleApproximation` from `Dependency_Angluin1980/Definitions.lean`.
* `GenLimit.Angluin.ListWithin` and `IsLockingSequence` from `Dependency_Angluin1980/Locking.lean`.
* `GenLimit.LiRamanTewari.UUS` appears only in the type of the extra helper `infiniteMembers_uus`.
* Mathlib's `[Nonempty α]`, `[Countable α]`, `Function.Surjective`, finite sets, and classical choice/decidability.

Imported effective predicates (`EffectiveIndexedFamily`, `EffectiveInferrable`, `ConditionOne`) are not conclusions or assumptions of the primary Paper 08 main theorems. Imported theorems from the Angluin and Li–Raman–Tewari modules are dependencies, not Paper 08 results. The supplied evidence does not justify attributing their source-paper fidelity to Paper 08.

## 17. Missing paper content, extra Lean content, and indeterminate points

### 17.1 Paper content not represented

1. The operational “tell-tale oracle” of Definition 4 is not a formal input object and has no computability or enumeration contract.
2. The `2t−1` fresh family-membership query bound in footnote 5 is absent.
3. The prose claim that the results carry to probabilistic presentations is absent.
4. No formal statement captures “most” collections or quantifies prevalence of impossibility.
5. No formal statement connects these semantic abstractions to prompts, LLM probability distributions, logits, model architectures, RLHF, or human-feedback sample complexity.
6. No effective or efficient algorithmic theorem is represented, despite the everyday word “automated.” This is consistent with the paper's own disclaimer but important for interpretation.

### 17.2 Extra or corrective Lean content

1. A full finite adaptive query-tree syntax and exact evaluation semantics.
2. Named local-test trees and their exact finite-prefix characterizations.
3. Least-candidate and list/tuple representation lemmas.
4. Generic locking-sequence existence/correctness/tell-tale bridge theorems, including empty-language handling.
5. An explicit equivalence between the paper's adjacent-guess Definition 3 and the stable-index interface.
6. Countability/UUS helpers for the appendix generation statement.
7. The multiples-family tell-tale calculation and positive detectability theorem correcting the paper.
8. Theorem 2.3 stated over arbitrary `α`, with vacuous extra cases.

### 17.3 Indeterminate from supplied evidence

1. Whether the authors intended the tell-tale oracle sentence to impose any effective uniformity beyond an unrestricted semantic primitive. The PDF supplies no machine model and explicitly disclaims computational restrictions.
2. Whether every theorem declaration compiled and every proof term is accepted at the pinned commit. Compilation and proof bodies were outside the permitted evidence.
3. Whether the paper's quoted Theorems A.1 and A.2 are faithful to the original Angluin and Kleinberg–Mullainathan sources. Those sources were not supplied and were not consulted.
4. The intended quantitative cost of replaying prior adaptive query interactions. Neither source gives a formal state/cost model.

## 18. What the Lean statements do not establish

The primary declarations do **not** establish:

* a computable, implementable, or efficient hallucination detector;
* a computable identifier or computable family-membership procedure;
* a uniform stabilization time, sample-complexity rate, query-depth bound, or total runtime bound;
* effective discovery or uniform enumeration of tell-tales from `ConditionTwo`;
* robustness to incomplete, noisy, adversarially mislabeled, or stochastic labels;
* detection of whether a particular generated sentence is true—the tested predicate is global set containment `G⊆K`;
* exact equality of the candidate output set with the target;
* a detector using only sampled LLM outputs rather than exact membership queries to the entire candidate set;
* nonvacuous positive-data learning of empty targets;
* nonvacuous Theorem 2.3 behavior on domains without a complete natural-number enumeration;
* constrained output after a finite target is exhausted in Theorem A.2;
* the paper's erroneous non-detectability conclusion for the multiples family;
* any probabilistic, approximate, or high-confidence guarantee.

## 19. Compact final verdict table

| Component | Correspondence verdict | Difficulty verdict | Bottom line |
|---|---|---|---|
| Positive detection definition | Exact / formally equivalent | Preserved | Correct subsethood-in-the-limit formalization |
| Identification ⇒ detection | Faithful specialization | Preserved | Explicit domain surjection; semantic family/candidate oracles |
| Detection ⇒ identification | Faithful generalization | Preserved | Same bounded consistency-plus-detector logic; no countability needed |
| Theorem 2.1 | Faithful specialization | Preserved | Core advertised semantic equivalence is faithful |
| Finite tell-tale predicate | Exact / formally equivalent | Preserved | Inclusion condition is exact |
| Tell-tale oracle/effective discovery | Not represented in Lean | Weakened / easier | Replaced by nonuniform existence and classical choice |
| Corollary 2.2 / Theorem A.1 | Faithful specialization | Preserved | Faithful semantically; not effective |
| Negative-example definition | Exact / formally equivalent | Preserved | Requires complete perfect labels over all domain points |
| Theorem 2.3 | Faithful generalization | Weakened / easier | Exact on valid streams; vacuous extra type scope |
| Example containment calculations | Exact / formally equivalent | Preserved | Both calculations correct |
| Example no-detector sentence | Related but materially different | Indeterminate | Source error; Lean correctly repairs it |
| Appendix Definition 3 | Exact / formally equivalent | Preserved | Stable-index encoding is genuinely equivalent |
| Appendix Definition 5 / Theorem A.2 | Faithful specialization | Preserved | Finite-target escape clause preserved |
| Query/runtime bounds | Not represented in Lean | Weakened / easier | Finite syntax only; no quantitative cost model |

## 20. Consolidated-audit executive summary

Paper 08's Lean formalization is **substantially faithful to the paper's semantic, noncomputational model**. Theorem 2.1 (p. 7, §2.2) and its two directions preserve exact subsethood, complete positive presentations, pointwise stabilization, duplicate indices, and finite adaptive candidate queries. Corollary 2.2 (p. 7, §2.2) is faithful only as a semantic finite-tell-tale characterization: `ConditionTwo` is nonuniform existence, certificates are selected by classical choice, and no effective tell-tale discovery or computable detector is established. Theorem 2.3 (p. 8, §2.2) is faithful for complete correctly labeled enumerations but is stated over arbitrary types, making non-countable cases vacuous. The formalization also correctly identifies and repairs a genuine paper error after Example 1 (p. 6, §2.1): the multiples family **is** identifiable and hallucination-detectable, because `{i}` is a tell-tale for the language of multiples of `i`. The main residual gaps are machine-level access, query/runtime bounds, probabilistic extensions, and explicit effective oracle interfaces.


## 21. Declaration-by-declaration target-scope audit

This ledger covers all 72 public declarations in the six substantive primary Paper 08 modules. The umbrella module contains no declarations.

### `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

#### D01. `GenLimit.HallucinationDetection.OracleTree`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
inductive OracleTree (α : Type*) where
  | answer : Bool → OracleTree α
  | query : α → OracleTree α → OracleTree α → OracleTree α
```

**Paper counterpart:** Finite membership queries in Definition 1, p. 5 §2.1.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Finite deterministic adaptive syntax. It does not impose a numerical or uniform bound beyond structural finiteness.

#### D02. `GenLimit.HallucinationDetection.OracleTree.eval`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
noncomputable def eval (G : Set α) : OracleTree α → Bool
  | answer b => b
  | query x yes no => if x ∈ G then eval G yes else eval G no
```

**Paper counterpart:** Exact membership-query answers to `G`, p. 5 §2.1.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Uses exact arbitrary-set membership and classical decidability. It is an oracle semantics, not a computable evaluator.

#### D03. `GenLimit.HallucinationDetection.Detector`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
abbrev Detector (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → OracleTree α
```

**Paper counterpart:** Detector sequence `D=(D_t)` in Definition 1, p. 5 §2.1.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Sees exactly the finite positive prefix. A family-specific witness may be hardwired to the whole family; no target index or future data is an argument.

#### D04. `GenLimit.HallucinationDetection.detectorOutput`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
noncomputable def detectorOutput
    (D : Detector α) (G : Set α) (stream : Stream α) (t : ℕ) : Bool :=
  OracleTree.eval G (D t (fun i => stream i))
```

**Paper counterpart:** Round output in Definition 1, p. 5 §2.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Combines the current prefix-generated tree with exact candidate membership. The detector itself does not receive `G` extensionally.

#### D05. `GenLimit.HallucinationDetection.DetectorCorrectAt`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
def DetectorCorrectAt
    (D : Detector α) (G K : Set α)
    (stream : Stream α) (t : ℕ) : Prop :=
  detectorOutput D G stream t = true ↔ G ⊆ K
```

**Paper counterpart:** Indicator equality `d_t=1{G⊆K}` in Definition 1, p. 5 §2.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Tests global candidate subsethood, not exact support or individual-output truth.

#### D06. `GenLimit.HallucinationDetection.DetectsHallucinations`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
def DetectsHallucinations
    (D : Detector α) (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream (C z) → ∀ G : Set α,
    ∃ T, ∀ t, T ≤ t → DetectorCorrectAt D G (C z) stream t
```

**Paper counterpart:** Definition 1, p. 5 §2.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Threshold depends on `z`, the full presentation, and `G`. Exact presentation excludes incomplete positive data and makes empty targets vacuous.

#### D07. `GenLimit.HallucinationDetection.HallucinationDetectable`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
def HallucinationDetectable
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ D : Detector α, DetectsHallucinations D C
```

**Paper counterpart:** Collection-level existential in Definition 1, p. 5 §2.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** One semantic detector must work for the whole indexed family; no computability or concrete witness is exposed.

#### D08. `GenLimit.HallucinationDetection.IdentifiableInLimit`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
def IdentifiableInLimit
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ M : GenLimit.Angluin.SemanticIdentifier α,
    GenLimit.Angluin.SemanticallyIdentifies M C
```

**Paper counterpart:** Definition 3, p. 19 §A.1, via stable-index equivalence.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** After dependency unfolding, guesses stabilize to one index denoting the target. The limiting representative may depend on the presentation.

#### D09. `GenLimit.HallucinationDetection.LabeledStream`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
abbrev LabeledStream (α : Type*) := ℕ → α × Bool
```

**Paper counterpart:** Labeled enumeration in Definition 2, pp. 7–8 §2.2.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** An infinite sequence of domain points and Boolean target labels.

#### D10. `GenLimit.HallucinationDetection.IsLabeledEnumeration`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
def IsLabeledEnumeration
    (stream : LabeledStream α) (K : Set α) : Prop :=
  Set.range (fun n => (stream n).1) = Set.univ ∧
  ∀ n, (stream n).2 = true ↔ (stream n).1 ∈ K
```

**Paper counterpart:** Definition 2, pp. 7–8 §2.2.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Requires complete domain coverage and perfect labels. It can be unsatisfiable, causing vacuity.

#### D11. `GenLimit.HallucinationDetection.NegativeExampleDetector`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
abbrev NegativeExampleDetector (α : Type*) :=
  ∀ t : ℕ, (Fin t → α × Bool) → OracleTree α
```

**Paper counterpart:** Detector interface in Definition 2, pp. 7–8 §2.2.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Sees the finite labeled prefix and returns a finite adaptive candidate-query tree; no cross-round state or computation bound is represented.

#### D12. `GenLimit.HallucinationDetection.negativeDetectorOutput`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
noncomputable def negativeDetectorOutput
    (D : NegativeExampleDetector α) (G : Set α)
    (stream : LabeledStream α) (t : ℕ) : Bool :=
  OracleTree.eval G (D t (fun i => stream i))
```

**Paper counterpart:** Round output in Definition 2, pp. 7–8 §2.2.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Exact candidate-oracle execution on the current labeled prefix.

#### D13. `GenLimit.HallucinationDetection.NegativeDetectorCorrectAt`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
def NegativeDetectorCorrectAt
    (D : NegativeExampleDetector α) (G K : Set α)
    (stream : LabeledStream α) (t : ℕ) : Prop :=
  negativeDetectorOutput D G stream t = true ↔ G ⊆ K
```

**Paper counterpart:** Indicator equality in Definition 2, pp. 7–8 §2.2.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Same exact subset predicate as the positive-only model.

#### D14. `GenLimit.HallucinationDetection.DetectsWithNegativeExamples`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
def DetectsWithNegativeExamples
    (D : NegativeExampleDetector α)
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : LabeledStream α,
    IsLabeledEnumeration stream (C z) →
    ∀ G : Set α, ∃ T, ∀ t, T ≤ t →
      NegativeDetectorCorrectAt D G (C z) stream t
```

**Paper counterpart:** Definition 2, pp. 7–8 §2.2.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Pointwise stabilization time may depend on target, complete labeled stream, and candidate set.

#### D15. `GenLimit.HallucinationDetection.DetectableWithNegativeExamples`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Definitions.lean`

**Whitespace-normalized signature/definition**

```lean
def DetectableWithNegativeExamples
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ D : NegativeExampleDetector α, DetectsWithNegativeExamples D C
```

**Paper counterpart:** Collection-level existential in Definition 2, pp. 7–8 §2.2.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** One semantic detector for the whole family; no executable implementation requirement.

### `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

#### D16. `GenLimit.HallucinationDetection.domainPrefix`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
def domainPrefix (enumerate : ℕ → α) (t : ℕ) : List α :=
  List.ofFn (fun i : Fin t => enumerate i)
```

**Paper counterpart:** Growing domain prefix in Algorithm 1, pp. 8–9 §3.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Concrete representation of the paper step; no surjectivity or computability is built into the definition itself.

#### D17. `GenLimit.HallucinationDetection.mem_domainPrefix_iff`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
theorem mem_domainPrefix_iff
    {enumerate : ℕ → α} {t : ℕ} {x : α} :
    x ∈ domainPrefix enumerate t ↔ ∃ i < t, enumerate i = x
```

**Paper counterpart:** Implicit finite-prefix fact used by Algorithm 1, pp. 8–9.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Exact list-membership characterization; no learning conclusion.

#### D18. `GenLimit.HallucinationDetection.subsetTestTree`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
noncomputable def subsetTestTree (L : Set α) : List α → OracleTree α
  | [] => .answer true
  | x :: xs => if x ∈ L then subsetTestTree L xs
      else .query x (.answer false) (subsetTestTree L xs)
```

**Paper counterpart:** Finite local subset scan in Algorithm 1, pp. 8–9.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Skips candidate queries at points already in `L`. Uses exact noncomputable membership in `L`; at most one `G` query per list entry definitionally.

#### D19. `GenLimit.HallucinationDetection.eval_subsetTestTree_eq_true_iff`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
theorem eval_subsetTestTree_eq_true_iff
    (G L : Set α) (xs : List α) :
    OracleTree.eval G (subsetTestTree L xs) = true ↔
      ∀ x, x ∈ xs → x ∈ G → x ∈ L
```

**Paper counterpart:** Correctness of Algorithm 1 finite scan, pp. 8–9.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Genuine exact local correctness statement; does not assert global `G⊆L` unless the list covers the domain.

#### D20. `GenLimit.HallucinationDetection.detectorFromIdentifier`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
noncomputable def detectorFromIdentifier
    (C : GenLimit.Generic.LanguageFamily α)
    (enumerate : ℕ → α)
    (M : GenLimit.Angluin.SemanticIdentifier α) : Detector α :=
  fun t xs => subsetTestTree (C (M t xs)) (domainPrefix enumerate t)
```

**Paper counterpart:** Algorithm 1, pp. 8–9 §3.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Same current-conjecture plus growing-domain-prefix construction. No public theorem names it as the existential witness in Lemma 3.1.

#### D21. `GenLimit.HallucinationDetection.lemma_3_1_identification_implies_detection`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
theorem lemma_3_1_identification_implies_detection
    (C : GenLimit.Generic.LanguageFamily α)
    (enumerate : ℕ → α) (henumerate : Function.Surjective enumerate)
    (hID : IdentifiableInLimit C) :
    HallucinationDetectable C
```

**Paper counterpart:** Lemma 3.1, p. 8 §3.1.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Explicitly supplies the domain enumeration that the paper derives from countability. Semantic, finite-query, non-effective conclusion.

#### D22. `GenLimit.HallucinationDetection.DetectorCandidate`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
def DetectorCandidate
    (C : GenLimit.Generic.LanguageFamily α) (D : Detector α)
    {t : ℕ} (xs : Fin t → α) (i : ℕ) : Prop :=
  i ≤ t ∧
  (↑(GenLimit.Generic.sequenceSample xs) : Set α) ⊆ C i ∧
  OracleTree.eval (C i) (D t xs) = true
```

**Paper counterpart:** Two candidate tests and bounded scope in Algorithm 2, pp. 10–11.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Positive consistency plus detector test of `C_i⊆K`. Exact membership in `C_i` is available extensionally; no direct equality/subset oracle is supplied.

#### D23. `GenLimit.HallucinationDetection.identifierFromDetector`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
noncomputable def identifierFromDetector
    (C : GenLimit.Generic.LanguageFamily α) (D : Detector α) :
    GenLimit.Angluin.SemanticIdentifier α := by
  classical
  exact fun t xs =>
    if h : ∃ i, DetectorCandidate C D xs i then Nat.find h else 0
```

**Paper counterpart:** Least-index choice in Algorithm 2, pp. 10–11.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Uses noncomputable least-witness selection; default `0` is arbitrary. No named full correctness theorem for this exact object.

#### D24. `GenLimit.HallucinationDetection.identifierFromDetector_candidate`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
theorem identifierFromDetector_candidate
    {C : GenLimit.Generic.LanguageFamily α} {D : Detector α}
    {t : ℕ} {xs : Fin t → α}
    (h : ∃ i, DetectorCandidate C D xs i) :
    DetectorCandidate C D xs (identifierFromDetector C D t xs)
```

**Paper counterpart:** Implicit least-candidate property of Algorithm 2, pp. 10–11 §3.1.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Packages candidate existence and `Nat.find`; it does not establish eventual candidate existence.

#### D25. `GenLimit.HallucinationDetection.identifierFromDetector_le_of_candidate`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
theorem identifierFromDetector_le_of_candidate
    {C : GenLimit.Generic.LanguageFamily α} {D : Detector α}
    {t : ℕ} {xs : Fin t → α} {i : ℕ}
    (hi : DetectorCandidate C D xs i) :
    identifierFromDetector C D t xs ≤ i
```

**Paper counterpart:** Implicit minimality property of Algorithm 2, pp. 10–11 §3.1.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Direct least-witness order fact; no convergence content.

#### D26. `GenLimit.HallucinationDetection.lemma_3_2_detection_implies_identification`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
theorem lemma_3_2_detection_implies_identification
    (C : GenLimit.Generic.LanguageFamily α)
    (hHD : HallucinationDetectable C) :
    IdentifiableInLimit C
```

**Paper counterpart:** Lemma 3.2, p. 9 §3.1.

**Correspondence verdict:** Faithful generalization

**Difficulty verdict:** Preserved

**Audit:** Same implication, with countability omitted because this direction needs no domain enumeration. Still purely semantic.

#### D27. `GenLimit.HallucinationDetection.theorem_2_1`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Reductions.lean`

**Whitespace-normalized signature/definition**

```lean
theorem theorem_2_1
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    HallucinationDetectable C ↔ IdentifiableInLimit C
```

**Paper counterpart:** Theorem 2.1, p. 7 §2.2.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Core result. Nonempty-domain specialization; exact semantic equivalence; no runtime/query-complexity equivalence.

### `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

#### D28. `GenLimit.HallucinationDetection.chosenTellTale`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
noncomputable def chosenTellTale
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) (i : ℕ) : Finset α :=
  Classical.choose (h i)
```

**Paper counterpart:** Paper tell-tale oracle sentence, Definition 4 p. 19.

**Correspondence verdict:** Related but materially different

**Difficulty verdict:** Weakened / easier

**Audit:** Noncomputable answer selection from a proof of existence. It is not an effective oracle or discovery procedure.

#### D29. `GenLimit.HallucinationDetection.chosenTellTale_spec`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem chosenTellTale_spec
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) (i : ℕ) :
    GenLimit.Angluin.IsTellTale C i (chosenTellTale C h i)
```

**Paper counterpart:** Specification expected of a tell-tale primitive, Definition 4 p. 19.

**Correspondence verdict:** Related but materially different

**Difficulty verdict:** Weakened / easier

**Audit:** Direct choice-specification packaging; assumes the full `ConditionTwo` proof and proves no new certificate existence.

#### D30. `GenLimit.HallucinationDetection.constantTellTaleApproximation`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
noncomputable def constantTellTaleApproximation
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    ℕ → ℕ → Finset α :=
  fun i _stage => chosenTellTale C h i
```

**Paper counterpart:** Paper mentions an enumeration of `T_i`, Definition 4 p. 19.

**Correspondence verdict:** Related but materially different

**Difficulty verdict:** Weakened / easier

**Audit:** Makes the complete final certificate available at stage zero. This collapses staged discovery, though the paper imposes no computational restriction.

#### D31. `GenLimit.HallucinationDetection.constantTellTaleApproximation_spec`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem constantTellTaleApproximation_spec
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    GenLimit.Angluin.IsTellTaleApproximation C
      (constantTellTaleApproximation C h)
```

**Paper counterpart:** Tell-tale enumeration semantics surrounding Definition 4 p. 19.

**Correspondence verdict:** Related but materially different

**Difficulty verdict:** Weakened / easier

**Audit:** Monotonicity and eventual equality are tautological for the constant full-certificate function; no effective enumeration is established.

#### D32. `GenLimit.HallucinationDetection.identifiable_of_conditionTwo`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem identifiable_of_conditionTwo
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    IdentifiableInLimit C
```

**Paper counterpart:** Sufficiency direction of Theorem A.1, p. 19 §A.1, and Corollary 2.2, p. 7 §2.2.

**Correspondence verdict:** Faithful generalization

**Difficulty verdict:** Preserved

**Audit:** On the paper scope it is the same semantic sufficiency direction. Outside countable/presentable domains some obligations may be vacuous; certificate selection remains nonconstructive and is audited separately from the paper's operational oracle sentence.

#### D33. `GenLimit.HallucinationDetection.listIdentifierOf`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
def listIdentifierOf
    (M : GenLimit.Angluin.SemanticIdentifier α) : List α → ℕ :=
  fun xs => M xs.length xs.get
```

**Paper counterpart:** No separately stated paper result.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Representation adapter from finite functions to lists; no extra information or oracle access.

#### D34. `GenLimit.HallucinationDetection.listIdentifierOf_streamPrefix`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem listIdentifierOf_streamPrefix
    (M : GenLimit.Angluin.SemanticIdentifier α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    listIdentifierOf M (GenLimit.Angluin.streamPrefix stream t) =
      GenLimit.Angluin.identifierOutput M stream t
```

**Paper counterpart:** No separately stated paper result.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Exact equality between two encodings of the same prefix; no learning content.

#### D35. `GenLimit.HallucinationDetection.ListConvergesTo`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
def ListConvergesTo
    (M : List α → ℕ)
    (stream : GenLimit.Generic.Stream α) (j : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    M (GenLimit.Angluin.streamPrefix stream t) = j
```

**Paper counterpart:** Stable tail underlying Definition 3, p. 19 §A.1.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Same syntactic convergence under a list encoding; threshold depends on the complete stream.

#### D36. `GenLimit.HallucinationDetection.presentationFromDomainEnumeration`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
noncomputable def presentationFromDomainEnumeration
    (enumerate : ℕ → α) (L : Set α) (hL : L.Nonempty) :
    GenLimit.Generic.Stream α :=
  fun n => if enumerate n ∈ L then enumerate n else Classical.choose hL
```

**Paper counterpart:** Existence of positive enumerations implicit in the model, p. 5.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Indeterminate

**Audit:** Proof-side target-dependent presentation constructor with exact target membership and a supplied target point. Not learner access.

#### D37. `GenLimit.HallucinationDetection.presentationFromDomainEnumeration_presents`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem presentationFromDomainEnumeration_presents
    (enumerate : ℕ → α) (henumerate : Function.Surjective enumerate)
    (L : Set α) (hL : L.Nonempty) :
    GenLimit.Generic.Presents
      (presentationFromDomainEnumeration enumerate L hL) L
```

**Paper counterpart:** Positive enumeration existence implicit in pp. 5, 19.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Genuine correctness statement under supplied surjection and nonemptiness; not an algorithm available to the learner.

#### D38. `GenLimit.HallucinationDetection.exists_lockingSequence_of_identifies_with_presentation`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem exists_lockingSequence_of_identifies_with_presentation
    {M : List α → ℕ} {L : Set α}
    {base : GenLimit.Generic.Stream α}
    (hbaseP : GenLimit.Generic.Presents base L)
    (hIdentifies : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream L →
        ∃ j, ListConvergesTo M stream j) :
    ∃ xs : List α, ∃ j,
      GenLimit.Angluin.IsLockingSequence M L xs j
```

**Paper counterpart:** Locking argument implicit in Angluin characterization, Theorem A.1 p. 19.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Genuine semantic diagonal statement. Assumes one base presentation and convergence on every presentation; does not assume correctness of the locked index.

#### D39. `GenLimit.HallucinationDetection.lockingSequence_correct_with_presentation`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem lockingSequence_correct_with_presentation
    {C : GenLimit.Generic.LanguageFamily α} {M : List α → ℕ}
    {z j : ℕ} {xs : List α}
    {base : GenLimit.Generic.Stream α}
    (hbaseP : GenLimit.Generic.Presents base (C z))
    (hIdentifies : ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C z) →
        ∃ ell, C ell = C z ∧ ListConvergesTo M stream ell)
    (hlock : GenLimit.Angluin.IsLockingSequence M (C z) xs j) :
    C j = C z
```

**Paper counterpart:** Locking correctness implicit in Theorem A.1, p. 19 §A.1.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Not circular: the hypothesis supplies some correct limit on each stream, not correctness of the separately supplied lock index `j`.

#### D40. `GenLimit.HallucinationDetection.lockingSequence_isTellTale_with_presentations`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem lockingSequence_isTellTale_with_presentations
    {C : GenLimit.Generic.LanguageFamily α} {M : List α → ℕ}
    (hIdentifies : ∀ z, ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C z) →
        ∃ j, C j = C z ∧ ListConvergesTo M stream j)
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C i))
    {z j : ℕ} {xs : List α}
    (hlock : GenLimit.Angluin.IsLockingSequence M (C z) xs j)
    (hcorrect : C j = C z) :
    GenLimit.Angluin.IsTellTale C z xs.toFinset
```

**Paper counterpart:** Necessity logic behind Theorem A.1, p. 19 §A.1.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Strong supplied lock/correctness/presentability assumptions, but the tell-tale conclusion is not merely an assumed equality. Empty family members make `hPresentable` strong.

#### D41. `GenLimit.HallucinationDetection.lockingSequence_isTellTale_with_nonempty_presentations`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem lockingSequence_isTellTale_with_nonempty_presentations
    {C : GenLimit.Generic.LanguageFamily α} {M : List α → ℕ}
    (hIdentifies : ∀ z, ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (C z) →
        ∃ j, C j = C z ∧ ListConvergesTo M stream j)
    (hPresentable : ∀ i, (C i).Nonempty →
      ∃ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.Presents stream (C i))
    {z j : ℕ} {xs : List α}
    (hxs : xs ≠ [])
    (hlock : GenLimit.Angluin.IsLockingSequence M (C z) xs j)
    (hcorrect : C j = C z) :
    GenLimit.Angluin.IsTellTale C z xs.toFinset
```

**Paper counterpart:** Empty-language-aware necessity logic behind Theorem A.1, p. 19 §A.1.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Nonempty history ensures any candidate containing it is presentable. Conditional but noncircular.

#### D42. `GenLimit.HallucinationDetection.append_mem_isLockingSequence`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem append_mem_isLockingSequence
    {M : List α → ℕ} {L : Set α} {xs : List α} {j : ℕ}
    (hlock : GenLimit.Angluin.IsLockingSequence M L xs j)
    {x : α} (hx : x ∈ L) :
    GenLimit.Angluin.IsLockingSequence M L (xs ++ [x]) j
```

**Paper counterpart:** No separate paper result.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Preserves an already supplied lock; it finds neither a lock nor a target member.

#### D43. `GenLimit.HallucinationDetection.conditionTwo_of_identifiable`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem conditionTwo_of_identifiable
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α)
    (hID : IdentifiableInLimit C) :
    GenLimit.Angluin.ConditionTwo C
```

**Paper counterpart:** Necessity direction of Theorem A.1, p. 19 §A.1, and Corollary 2.2, p. 7 §2.2.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Semantic necessity with empty-language handling. It proves only existence, not a uniformly enumerable or computable certificate family.

#### D44. `GenLimit.HallucinationDetection.corollary_2_2`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/AngluinCondition.lean`

**Whitespace-normalized signature/definition**

```lean
theorem corollary_2_2
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    HallucinationDetectable C ↔ GenLimit.Angluin.ConditionTwo C
```

**Paper counterpart:** Corollary 2.2, p. 7 §2.2.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Faithful semantic certificate characterization. Operational tell-tale oracle/effectivity is absent; target/candidate thresholds remain pointwise.

### `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

#### D45. `GenLimit.HallucinationDetection.ConsecutivelyIdentifiesFrom`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
def ConsecutivelyIdentifiesFrom
    (M : GenLimit.Angluin.SemanticIdentifier α)
    (C : GenLimit.Generic.LanguageFamily α) (z : ℕ)
    (stream : GenLimit.Generic.Stream α) : Prop :=
  ∃ T, ∀ t, T < t →
    GenLimit.Angluin.identifierOutput M stream t =
      GenLimit.Angluin.identifierOutput M stream (t - 1) ∧
    C (GenLimit.Angluin.identifierOutput M stream t) = C z
```

**Paper counterpart:** Definition 3, p. 19 §A.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Literal adjacent-tail equality and extensional target correctness. Strict threshold handles predecessor time.

#### D46. `GenLimit.HallucinationDetection.ConsecutivelyIdentifies`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
def ConsecutivelyIdentifies
    (M : GenLimit.Angluin.SemanticIdentifier α)
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream (C z) →
    ConsecutivelyIdentifiesFrom M C z stream
```

**Paper counterpart:** Collection-level Definition 3, p. 19 §A.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Every target index and exact presentation; empty/unpresentable targets are vacuous.

#### D47. `GenLimit.HallucinationDetection.ConsecutivelyIdentifiable`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
def ConsecutivelyIdentifiable
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ M : GenLimit.Angluin.SemanticIdentifier α,
    ConsecutivelyIdentifies M C
```

**Paper counterpart:** Existential in Definition 3, p. 19 §A.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Semantic identifier existence, with no computability.

#### D48. `GenLimit.HallucinationDetection.semanticallyIdentifies_implies_consecutivelyIdentifies`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
theorem semanticallyIdentifies_implies_consecutivelyIdentifies
    {M : GenLimit.Angluin.SemanticIdentifier α}
    {C : GenLimit.Generic.LanguageFamily α}
    (hM : GenLimit.Angluin.SemanticallyIdentifies M C) :
    ConsecutivelyIdentifies M C
```

**Paper counterpart:** No separate paper result; validates encoding of Definition 3.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Stable fixed index immediately gives adjacent equality and target correctness.

#### D49. `GenLimit.HallucinationDetection.consecutivelyIdentifies_implies_semanticallyIdentifies`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
theorem consecutivelyIdentifies_implies_semanticallyIdentifies
    {M : GenLimit.Angluin.SemanticIdentifier α}
    {C : GenLimit.Generic.LanguageFamily α}
    (hM : ConsecutivelyIdentifies M C) :
    GenLimit.Angluin.SemanticallyIdentifies M C
```

**Paper counterpart:** No separate paper result; validates encoding of Definition 3.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Adjacent equality on a tail forces one fixed syntactic index; no target/equivalence oracle is added.

#### D50. `GenLimit.HallucinationDetection.definition_3_equivalence`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
theorem definition_3_equivalence
    (C : GenLimit.Generic.LanguageFamily α) :
    ConsecutivelyIdentifiable C ↔ IdentifiableInLimit C
```

**Paper counterpart:** Definition 3, p. 19 §A.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Explicit bridge showing the shared stable-index interface is not a weakening, including duplicate-index families.

#### D51. `GenLimit.HallucinationDetection.theorem_A_1`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
theorem theorem_A_1
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    ConsecutivelyIdentifiable C ↔ GenLimit.Angluin.ConditionTwo C
```

**Paper counterpart:** Theorem A.1, p. 19 §A.1.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Semantic characterization with nonempty-domain specialization and non-effective certificates.

#### D52. `GenLimit.HallucinationDetection.AppendixGenerationCorrectAt`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
def AppendixGenerationCorrectAt
    (G : GenLimit.Generic.Generator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  GenLimit.Generic.output G stream t ∈
      L \ (↑(GenLimit.Generic.sample stream t) : Set α) ∨
    L \ (↑(GenLimit.Generic.sample stream t) : Set α) = ∅
```

**Paper counterpart:** Definition 5, p. 20 §A.2.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Faithfully includes the finite-target escape. Once exhausted, output is unrestricted.

#### D53. `GenLimit.HallucinationDetection.AppendixGeneratesInLimit`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
def AppendixGeneratesInLimit
    (G : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream (C z) →
    ∃ T, ∀ t, T ≤ t →
      AppendixGenerationCorrectAt G (C z) stream t
```

**Paper counterpart:** Definition 5, p. 20 §A.2.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Threshold may depend on target and presentation; one generator handles all family members.

#### D54. `GenLimit.HallucinationDetection.AppendixGeneratableInLimit`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
def AppendixGeneratableInLimit
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ G : GenLimit.Generic.Generator α,
    AppendixGeneratesInLimit G C
```

**Paper counterpart:** Collection existential in Definition 5, p. 20 §A.2.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Pure semantic existence; no computability or named generator.

#### D55. `GenLimit.HallucinationDetection.infiniteMembers`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
def infiniteMembers
    (C : GenLimit.Generic.LanguageFamily α) :
    GenLimit.Generic.LanguageClass α :=
  {L | L ∈ Set.range C ∧ L.Infinite}
```

**Paper counterpart:** No separate paper result.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Auxiliary class of extensionally occurring infinite family languages; duplicate indices are forgotten at this helper layer.

#### D56. `GenLimit.HallucinationDetection.infiniteMembers_countable`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
theorem infiniteMembers_countable
    (C : GenLimit.Generic.LanguageFamily α) :
    (infiniteMembers C).Countable
```

**Paper counterpart:** No separate paper result.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Set-theoretic countability of the range-derived class; no computable enumeration.

#### D57. `GenLimit.HallucinationDetection.infiniteMembers_uus`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
theorem infiniteMembers_uus
    (C : GenLimit.Generic.LanguageFamily α) :
    GenLimit.LiRamanTewari.UUS (infiniteMembers C)
```

**Paper counterpart:** No separate paper result.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Unfolds to the tautological fact that every member selected as infinite is infinite. Packaging helper.

#### D58. `GenLimit.HallucinationDetection.theorem_A_2`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/Appendix.lean`

**Whitespace-normalized signature/definition**

```lean
theorem theorem_A_2
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    AppendixGeneratableInLimit C
```

**Paper counterpart:** Theorem A.2, p. 20 §A.2.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Same universal semantic generation result, with nonempty-domain specialization and the finite-target escape inherited from the definition.

### `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`

#### D59. `GenLimit.HallucinationDetection.multiplesFamily`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`

**Whitespace-normalized signature/definition**

```lean
def multiplesFamily : GenLimit.Generic.LanguageFamily ℕ :=
  fun i => {x | i + 1 ∣ x + 1}
```

**Paper counterpart:** Example 1, pp. 5–6 §2.1.

**Correspondence verdict:** Faithful specialization

**Difficulty verdict:** Preserved

**Audit:** Exact predecessor encoding of positive integers and one-based language indices.

#### D60. `GenLimit.HallucinationDetection.mem_multiplesFamily`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`

**Whitespace-normalized signature/definition**

```lean
@[simp] theorem mem_multiplesFamily {i x : ℕ} :
    x ∈ multiplesFamily i ↔ i + 1 ∣ x + 1
```

**Paper counterpart:** Defining membership in Example 1, p. 5 §2.1.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Definitional membership characterization; no additional assumption.

#### D61. `GenLimit.HallucinationDetection.multiplesFamily_allNonempty`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`

**Whitespace-normalized signature/definition**

```lean
theorem multiplesFamily_allNonempty :
    GenLimit.Angluin.AllNonempty multiplesFamily
```

**Paper counterpart:** Implicit fact about Example 1, p. 5 §2.1.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Every multiples language contains its least positive multiple. Auxiliary, not a detection theorem.

#### D62. `GenLimit.HallucinationDetection.singleton_index_isTellTale`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`

**Whitespace-normalized signature/definition**

```lean
theorem singleton_index_isTellTale (i : ℕ) :
    GenLimit.Angluin.IsTellTale multiplesFamily i {i}
```

**Paper counterpart:** Contradicts the no-detector sentence after Example 1, p. 6.

**Correspondence verdict:** Related but materially different

**Difficulty verdict:** Indeterminate

**Audit:** Constructs the decisive singleton certificate. Genuine formal repair; not circular or vacuous.

#### D63. `GenLimit.HallucinationDetection.example_1_angluinCondition`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`

**Whitespace-normalized signature/definition**

```lean
theorem example_1_angluinCondition :
    GenLimit.Angluin.ConditionTwo multiplesFamily
```

**Paper counterpart:** Contradicts the no-detector sentence after Example 1, p. 6.

**Correspondence verdict:** Related but materially different

**Difficulty verdict:** Indeterminate

**Audit:** The family satisfies the paper's characterization. Opposite of the source diagnosis.

#### D64. `GenLimit.HallucinationDetection.example_1_L4_subset_L2`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`

**Whitespace-normalized signature/definition**

```lean
theorem example_1_L4_subset_L2 :
    multiplesFamily 3 ⊆ multiplesFamily 1
```

**Paper counterpart:** First containment in Example 1, p. 5.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Paper `L₄⊆L₂`, correctly translated to zero-based indices.

#### D65. `GenLimit.HallucinationDetection.example_1_L3_not_subset_L2`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`

**Whitespace-normalized signature/definition**

```lean
theorem example_1_L3_not_subset_L2 :
    ¬ multiplesFamily 2 ⊆ multiplesFamily 1
```

**Paper counterpart:** Second containment in Example 1, p. 5.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Paper `L₃⊄L₂`, correctly translated to zero-based indices.

#### D66. `GenLimit.HallucinationDetection.example_1_hallucinationDetectable`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/ExampleOne.lean`

**Whitespace-normalized signature/definition**

```lean
theorem example_1_hallucinationDetectable :
    HallucinationDetectable multiplesFamily
```

**Paper counterpart:** Opposite of the sentence on p. 6 after Example 1.

**Correspondence verdict:** Related but materially different

**Difficulty verdict:** Indeterminate

**Audit:** Correct positive conclusion under the paper's own theorem and tell-tale calculation. Formal source correction.

### `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`

#### D67. `GenLimit.HallucinationDetection.labeledPrefix`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`

**Whitespace-normalized signature/definition**

```lean
def labeledPrefix
    (stream : LabeledStream α) (t : ℕ) : List (α × Bool) :=
  List.ofFn (fun i : Fin t => stream i)
```

**Paper counterpart:** Finite labeled history in Definition 2, pp. 7–8 §2.2, and proof of Theorem 2.3, pp. 12–13 §3.2.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Exact chronological list representation of the first `t` labeled entries.

#### D68. `GenLimit.HallucinationDetection.mem_labeledPrefix_iff`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`

**Whitespace-normalized signature/definition**

```lean
theorem mem_labeledPrefix_iff
    {stream : LabeledStream α} {t : ℕ} {q : α × Bool} :
    q ∈ labeledPrefix stream t ↔ ∃ i < t, stream i = q
```

**Paper counterpart:** Implicit finite-prefix fact in the proof of Theorem 2.3, pp. 12–13 §3.2.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Representation lemma only; no detection conclusion.

#### D69. `GenLimit.HallucinationDetection.negativeExampleTree`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`

**Whitespace-normalized signature/definition**

```lean
def negativeExampleTree : List (α × Bool) → OracleTree α
  | [] => .answer true
  | (_x, true) :: xs => negativeExampleTree xs
  | (x, false) :: xs =>
      .query x (.answer false) (negativeExampleTree xs)
```

**Paper counterpart:** Explicit strategy in proof of Theorem 2.3, pp. 12–13.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Queries exactly target-negative observed points and rejects on the first candidate-positive answer. Finite, at most one query per negative entry.

#### D70. `GenLimit.HallucinationDetection.eval_negativeExampleTree_eq_true_iff`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`

**Whitespace-normalized signature/definition**

```lean
theorem eval_negativeExampleTree_eq_true_iff
    (G : Set α) (xs : List (α × Bool)) :
    OracleTree.eval G (negativeExampleTree xs) = true ↔
      ∀ x b, (x, b) ∈ xs → b = false → x ∉ G
```

**Paper counterpart:** Correctness of finite test in proof of Theorem 2.3, pp. 12–13.

**Correspondence verdict:** Extra Lean result not claimed by the paper

**Difficulty verdict:** Preserved

**Audit:** Exact local semantics. Does not by itself establish eventual global subsethood.

#### D71. `GenLimit.HallucinationDetection.negativeExampleDetector`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`

**Whitespace-normalized signature/definition**

```lean
def negativeExampleDetector : NegativeExampleDetector α :=
  fun _t xs => negativeExampleTree (List.ofFn xs)
```

**Paper counterpart:** Detector strategy in proof of Theorem 2.3, pp. 12–13.

**Correspondence verdict:** Exact / formally equivalent

**Difficulty verdict:** Preserved

**Audit:** Named realization of the paper strategy. No public theorem directly states `DetectsWithNegativeExamples negativeExampleDetector C`.

#### D72. `GenLimit.HallucinationDetection.theorem_2_3`

**Bundle file label:** `GenLimitLean/GenLimit/Paper08_AutomatedHallucinationDetection/NegativeExamples.lean`

**Whitespace-normalized signature/definition**

```lean
theorem theorem_2_3
    (C : GenLimit.Generic.LanguageFamily α) :
    DetectableWithNegativeExamples C
```

**Paper counterpart:** Theorem 2.3, p. 8 §2.2.

**Correspondence verdict:** Faithful generalization

**Difficulty verdict:** Weakened / easier

**Audit:** Exact for every valid complete labeled enumeration. Arbitrary-type extension is vacuous when no such enumeration exists; no computation or query bound.


## 22. Completeness check

The declaration ledger contains 72 entries: 15 from `Definitions.lean`, 12 from `Reductions.lean`, 17 from `AngluinCondition.lean`, 14 from `Appendix.lean`, 8 from `ExampleOne.lean`, and 6 from `NegativeExamples.lean`. There are no public axioms in the primary Paper 08 modules. All named paper definitions and results listed in §4 have at least one paper-to-Lean row in §6.1. Section 6.2 contains exactly one reverse row for each of the 72 primary declarations, and every declaration has exactly one correspondence and one difficulty verdict in §21.
