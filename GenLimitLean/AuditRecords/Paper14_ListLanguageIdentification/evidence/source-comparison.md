# Stage 2: independent source comparison

## Identity, scope, and finding

The two selected propositions faithfully express the paper's main deterministic characterization and decomposition theorems. Their source-scope content is equivalent after the translations detailed below; the interfaces generalize the ambient universe and include the conservative case k=0. This is a statement comparison, not proof certification. The complete paper is substantially broader: the supplied native umbrella also represents the recursive learner, its stabilization, sufficiency, necessity, and peeling construction, but does not represent the canonical separation examples or the probabilistic/statistical development of Section 8.

The source is Moses Charikar, Chirag Pabbaraju, and Ambuj Tewari, *A Characterization of List Language Identification in the Limit*, arXiv:2511.04103v1, arXiv date 6 November 2025; its title page prints 7 November 2025. The official 30-page PDF has SHA-256 `fdc00078c5ca6f2794005d608ebae5c46a7b5f012e5a200891e10cfd1f4a32d4`. The complete extracted text has SHA-256 `c945dce40a41619030ef9bbc6acbdd42adaf6c442e7c947304d26d9ed48bf651`. No later edition or cited external paper was consulted.

The target list contains exactly `GenLimit.ListIdentification.Results.theorem_1` and `.theorem_2`. These are located by the export at `GenLimitLean/GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean:34` and `:46`. Raw Lean source, comments, theorem proof values, owner explanations, Stage 3 context, registry, PaperMaps, sibling reports, and old audits were not read. Raw snapshot entries were read only as bytes to verify the supplied manifest. No build or Git operation occurred.

All source pages, including introductory conventions, proof context, remarks, footnotes, and references, were read before opening Stage 1 or Lean mathematics. The independent 34-unit inventory was serialized and frozen at `results/qa/source-first-inventory.md`, SHA-256 `c9033f676604c6bcdad51d1033ba65b567188cb73295aa926258a94ce80242fd`; its prior-access freeze record has SHA-256 `4b917f985a3f3b23c02879ed8ef26e0ebfc46c99f3a92692af829c6f21ab1246`. The comparison matrix below preserves those independently assigned unit IDs.

Ghostscript renders were visually inspected for PDF pages 10–13, 15, 18–21, 23–24, 26–27. Their printed labels equal their one-based PDF numbers. Pypdf reports page labels 1–30. Thus “p11” below means printed page 11/PDF page 11, not the eleventh body page after a cover. Visual checks confirmed the strict inclusion and tell-tale formulas (4)–(6), Algorithm 1's descending-index constraint, Algorithm 2's unseen-string instruction, the probability threshold in Theorem 9, and the quantitative statements on pp24, 26–27. There is no appendix: references end at p30.

Stage 1 was consulted only after that inventory freeze, with its two expected hashes verified: reconstruction `9589a03b8f5bf286a76a8bf811afb27c1f80aeaeb27fd2a060386a945862535c`, run record `35e1a9c1471f47dbf73f2491b0ddb04001ed036fbc6fd6d396499d63e72c9202`. It was treated as fallible and its decisive expansions rechecked against canonical definition values, including the requested notation-disabled Psi supplement.

## Independent source model and assumptions

Section 3, p10, fixes a countable universe U and a countably indexed collection C=(L1,L2,…). Every language is nonempty; finite and countably infinite languages are permitted. Equal extensional languages may occur at different indices. An enumeration is a total infinite sequence with range exactly the target language. Input order is arbitrary and repetitions are allowed. The learner must succeed on every such complete positive presentation; success on a partial presentation, on one favorable enumeration, or on a distribution with smaller support would not satisfy this requirement.

Definition 1 writes a function U*→N^k. The surrounding introduction and Algorithm 1 instead allow at most k guesses. For positive k these existential learning notions agree by padding shorter lists with a fixed collection index. Repeating indices does not add semantic guesses. The source's positive-natural indexing translates to Lean's zero-based naturals by an index renaming, including fallback 1 versus fallback 0.

Definition 2 requires that at every sufficiently late time a guessed index denote the correct language. The successful slot and index may change. This is the BC criterion explicitly distinguished from EX on pp4–5. It does not require eventual stabilization of the whole tuple or even one fixed correct name. Source footnote 4 on p10 expressly concerns existence of list-valued functions and imposes no computational-power requirement. Consequently classical choices, undecidable language comparisons, or non-effective tell-tales do not by themselves weaken correspondence; claiming an ordinary executable learner would strengthen what was established.

For k≥1, Section 4 defines Ψ relative to the same complete collection, not a shrinking recursive subcollection. At depth 1, a finite T⊆L_i excludes every represented proper sublanguage containing T. At larger depth, every such sublanguage must satisfy the predecessor Ψ. The one T for i is chosen before the universal competing index. Recursive witnesses may then depend on that competitor and level. Theorem 7's proof extends Ψ to depth zero as False. No bound on tell-tale size, enumeration time, or convergence time is promised.

The statistical part uses a valid distribution with D(x)>0 iff x∈L (Definition 3). It is exact full support, not just absence of negative observations. Definition 4 quantifies ∃A ∀L ∀valid D ∃c1,c2>0 ∀t for an upper rate c1 R(c2 t). Lower rates instead quantify ∀A ∃L,D,c1,c2 and infinitely many t. No-rate means a strictly positive limsup of finite-sample error for some target/distribution for every learner. These are separate from eventual success on each adversarial presentation.

## Target dossiers and component matrix

### theorem_1: all directions of the characterization

The complete selected type, as printed in the target interface, is:

```lean
∀ {α : Type u_1} [DecidableEq.{u_1 + 1} α] {F : GenLimit.Generic.LanguageFamily.{u_1} α},
  (∀ (i : Nat), ∃ stream, GenLimit.Generic.Presents.{u_1} stream (F i)) →
    ∀ (k : Nat),
      Iff (GenLimit.ListIdentification.ListIdentifiable.{u_1} F k)
        (GenLimit.ListIdentification.KAngluinCondition.{u_1} F k)
```

Here `LanguageFamily α` is Nat→Set α and `Presents s L` is range(s)=L. Let H(F) denote the displayed presentation premise. Expansion of `ListIdentifier`, `ListIdentifiable`, `ListIdentifies`, `IdentifiesFrom`, `listOutput`, and `TargetInGuess` gives precisely:

∃ A:(t:Nat)→(Fin t→α)→(Fin k→Nat), ∀z ∀s, range(s)=F_z → ∃N ∀t≥N ∃r:Fin k, F_(A t (s restricted below t) r)=F_z.

The operator is chosen once per F,k before all targets and presentations. The threshold may depend on the particular source, and the successful slot may depend on t. The history consists of the first t elements, with t=0 allowed; the time-zero extra case has no effect on eventual success. No target index, future input, negative example, oracle, probability law, or randomness is passed to the operator.

The notation-disabled requested Psi value exposes `Exists (Finset α)` and the immediate predecessor application `x.1 j`. Thus the right side expands to ∀i Ψ(F,i,k), where Ψ(_,0)=False and

Ψ(F,i,k+1) ↔ ∃T:Finset α, T⊆F_i ∧ ∀j, T⊆F_j → F_j⊊F_i → Ψ(F,j,k).

The order of the last two hypotheses is immaterial; replacing the source's “T is not contained, or predecessor Ψ” by the displayed implication is logically equivalent. At k=1 the predecessor is False and gives exactly (4). Equal duplicates do not trigger strict inclusion; all represented proper sublanguages do. There is no index cutoff in Ψ, and no restriction to languages presently consistent with the observed history.

Necessity sends existence of a universally successful operator to the whole depth-k condition. Sufficiency sends the whole condition to one operator successful on every target and presentation. Neither direction specifies that the operator must be Algorithm 1, so the presence of alternative native arguments or witnesses does not change the existential theorem. The source locations are Theorem 1 p3, definitions pp10–11, and detailed Theorems 6–7 pp14–17. Native `theorem7_kAngluin_necessity` (GeneralNecessity:247), `theorem6_kAngluin_listIdentifiable` (Algorithm:280), and `listIdentifiable_iff_kAngluin` (GeneralNecessity:304) independently expose the two directions and combined statement.

**Classification:** equivalent on the source's k≥1/countable-universe/nonempty-language domain; faithful generalization in the native ambient formulation, with a conservative zero-list extension. There is no materially different quantifier, loss, or success criterion in the selected type.

### theorem_2: every conjunct of decomposition

The complete second selected type is:

```lean
∀ {α : Type u_1} [DecidableEq.{u_1 + 1} α] {F : GenLimit.Generic.LanguageFamily.{u_1} α},
  (∀ (i : Nat), ∃ stream, GenLimit.Generic.Presents.{u_1} stream (F i)) →
    ∀ (k : Nat),
      Iff (GenLimit.ListIdentification.ListIdentifiable.{u_1} F k)
        (GenLimit.ListIdentification.HasAngluinStratification.{u_1} F k)
```

The common left side and outer premise are exactly as above. The complete right side is:

∃layers:List(Set Nat), length(layers)=k ∧ [∀i ∃I, I∈layers ∧ i∈I] ∧ [∀I∈layers ∀i∈I ∃T:Finset α, T⊆F_i ∧ ∀j∈I, T⊆F_j → F_j⊆F_i → F_i⊆F_j].

The three conjuncts are exact length, coverage of every original index, and an ordinary relative tell-tale condition in every layer. The final reverse inclusion is essential: together with F_j⊆F_i it forces equality, thereby excluding proper sublanguages containing T. T can depend on I and i but must handle all j in that I. Languages outside I impose no constraint. A cover membership witness may depend on i.

This is not literally a list of separately indexed subfamily learner objects: the native definition uses their relative Angluin conditions. The translation is substantively supported rather than assumed from its name. `relativeIdentifier` (Stratification:192) chooses the least eligible index of I using chosen relative tell-tales; `relativeIdentifier_identifies_member` (:199) gives eventual extensional correctness for every represented member and presentation. `stratifiedIdentifier` (:242) outputs one such identifier's guess per list position, and `stratification_implies_listIdentifiable` (:251) supplies the reverse implication. The forward bridge `kAngluin_implies_stratification` (:155), together with necessity, supplies exactly k relative layers. The full equivalence also appears at :281.

For a nonempty layer, a countable reindexing and a default in-layer index turn this into the source's separately indexed one-output identification statement; eventually chosen eligible indices are in I. Empty layers have vacuous member obligations; for k≥1 they can be replaced by a singleton original language or repeated nonempty identifiable layer while keeping exactly k slots. Reindexing this interface as the literal prose of Theorem 2 is a small wrapper/assembly task, not missing decomposition mathematics. No native claim of computable reindexing is inferred.

The definition allows empty layers, overlaps, repeated layers, and infinitely many indices per layer. Their occurrences count toward length, although logical membership does not distinguish repeated occurrences. Theorem 2 pp3,17–18 asserts a union of k identifiable collections, without requiring disjointness. Its proof constructs peeled index layers; that stronger construction must not be substituted for an extra partition conjunct in the theorem. The native general relative result `exists_relative_stratification` (:103) supplies exactly k layers whose union equals any starting I, stronger than a one-way cover, but its type still does not state pairwise disjointness.

**Classification:** equivalent source content via the relative characterization and native single-layer learner assembly; faithful ambient generalization and zero-list extension as for theorem_1. A literal learner-valued decomposition wrapper is absent, while its needed mathematics is represented.

### Shared component comparison and boundary cases

| Component | Source | Canonical native evidence | Assessment |
|---|---|---|---|
| Universe and languages | Countable U; every L nonempty | Arbitrary α, H(F) supplies complete presentations | Faithful generalization: irrelevant ambient points need not be countable; each used language is nonempty and countably presentable. |
| Equality | No effective requirement (footnote 4) | Displayed DecidableEq α; classical choices in definitions | Extra formal instance, classically available; no computational restriction or language-membership decision procedure follows. |
| Collection | Positive-Nat indexed, duplicates allowed | Nat→Set α | Equivalent after zero-based renaming; no empty indexed family. Finite distinct collections can repeat names. |
| Learner cardinality | Exactly k in Definition 1, at most k elsewhere | Fin k→Nat; bounded list form and padding also exported | Equivalent existential notions for k≥1; native bounded output theorem does not silently truncate correct guesses. |
| Complete inputs | Every string eventually appears | range equality | Exact; partial-only streams are outside the success obligation. Repetitions admit finite nonempty targets. |
| Successful prediction | Correct language occurs at every late time | ∃N ∀t≥N ∃slot, equality of language sets | Exact BC semantics; no fixed-name stabilization in targets. |
| Ψ witness | Finite T before all strict competitors | Finset α and predecessor Ψ in full F | Exact, including empty T; no uniform size bound. |
| Relative layer | One-output identifiable subcollection | Ordinary relative tell-tales, native relative learner | Equivalent by explicit assembly; not an effective decomposition. |
| Number of layers | k, union covers C | length=k and covers every original index | Exact; duplicates/empty layers are padding, not extra language coverage. |
| k=0 | Outside main positive-k setting | Both sides false under H(F) | Conservative extension: Fin0 has no successful slot; Ψ0=False; empty layer-list cannot cover index0. |
| Empty language/type | Every source language nonempty | H(F) fails for any empty F_i, hence also empty α | No hidden success guarantee on empty languages; implication is inapplicable there. |
| Infinite/finite cases | Both permitted, no injectivity of streams | H(F), unrestricted total streams | Exact. Optional `InjectivePresentation` elsewhere is not a target hypothesis. |
| Rates/resources | Separate Section 8 claims | None in either selected type | No probability, sample complexity, convergence bound, or ordinary algorithmic effectiveness implied. |

## Complete source-to-native coverage

The independent source inventory has 34 units. “Equivalent” below concerns statement content in the applicable source domain; it never certifies proofs. “Assembly” identifies existing native ingredients requiring a wrapper. “Not represented” is bounded to this supplied complete native umbrella, not a claim about unseen repository or library modules.

| ID | Source location and claim | Native anchors and correspondence |
|---|---|---|
| S01 | Abstract; Theorem 1 p3, characterization iff | **Equivalent/generalized:** theorem_1; GeneralNecessity:304,315. Both directions checked above. |
| S02 | Theorem 2 pp3,17–18, k-fold identifiable union iff | **Equivalent via assembly/generalized:** theorem_2; Stratification:46,155,199,242,251,281. All cover/tell-tale conjuncts checked. |
| S03 | Theorem 3 p4, exponential/no-rate/best-rate summary | **Not represented:** no statistical law/error/rate definitions or theorems. Source best-rate qualification appears later in §8.3. |
| S04 | pp2–5, historical results and BC/EX/context comparisons | **Partial background support:** scalar tell-tale characterization in `GenLimit.Angluin`; Gold superfinite impossibility in Text.Superfinite:183,196,207,216 and finite-language learner in Text.Finite:120–133. These do not formalize the whole historical discussion, team comparisons, or generation/classification claims. |
| S05 | Example 4 pp5–6, co-singletons 2-learnable not 1 | **Not represented as specialization:** no exported family/learner or Ψ combinatorics for this collection. General characterization is relevant infrastructure, not the example's proof. |
| S06 | Example 5 pp6–8, co-doubleton family not 2-learnable | **Not represented as specialization:** neither family nor its failed depth-2 condition established by a supplied type. |
| S07 | Definitions 1–2 p10, prefix list and eventual success | **Equivalent:** Definitions:20–53; bounded-list alternative :59–68 and Algorithm padding :75–101. |
| S08 | Definition 3 p10, exact valid support | **Not represented:** no distribution type or positivity/support predicate. |
| S09 | Definition 4 p11 (1), rate upper bound and constants | **Not represented:** the entire ∃A∀L,D∃c1,c2∀t probability bound is absent. |
| S10 | Definition 4 p11 (2), infinitely-often rate lower bound | **Not represented:** no per-learner fixed target/law and infinite-time lower bound. |
| S11 | Definition 4 p11 (3), no-rate/optimal-rate | **Not represented:** no positive limsup loss or rate comparison. |
| S12 | (4)–(6) p11, recursive Ψ/global condition | **Equivalent:** Psi:23,31,39,49,58,77; requested Psi value confirms finite domain and depth shift. |
| S13 | Remark 1 p12, coherent/reusable witnesses, depth monotonicity | **Partly explicit, partly assembly:** psi_succ_mono:90, psi_mono:105, kAngluin_mono:116; psiTellTale:128 and spec:138 choose valid witnesses. Same-T reuse follows by applying monotonicity to each descendant; no separately stated lowest-depth reuse/coherence theorem. |
| S14 | Remark 2 p12, C_k fails k/satisfies k+1; C_infty fails all finite k | **Not represented:** concrete cofinite-family depth calculations absent. Preserve source explanatory problems below. |
| S15 | Algorithm 1 pp12–13, recursive list size ≤k | **Equivalent algorithmic semantics:** Algorithm listIdentify:31, descendingIndexSet:18, length bound:50. k+1 branch uses psiTellTale parameter k, whose specification is for Ψ at k+1; this is an intentional predecessor parameter, not an off-by-one error. |
| S16 | Claim 5.1 pp12–13 (7), first choice stabilizes to least limit candidate | **Faithful generalization:** Stabilization LevelEligible:18, LimitCandidate:61, limitChoice:71, levelChoice_stabilizes:108. Requires only T_i⊆F_i on I, weaker than source Ψ assumptions. LimitCandidate includes every conjunct i∈I,i≤z,F_z⊆F_i,T_i⊆F_z. |
| S17 | Theorem 6 pp14–15, specified recursive learner succeeds | **Equivalent/generalized:** listIdentify_eventually_contains_target Algorithm:137 for arbitrary I containing z; theorem6_kAngluin_sufficient:255 supplies bounded learner and theorem6_kAngluin_listIdentifiable:280 gives fixed-tuple existence. |
| S18 | Algorithm 2 pp15–17 and its strict-chain/length/nontermination invariants | **Literal construction not represented:** native target locking, strict-cone reduction, and slot deletion are different supporting constructions. Missing that precise adversary/invariant package does not make the existential lower-bound theorem materially different. |
| S19 | Theorem 7 p15, failed condition implies impossibility | **Equivalent by contrapositive:** GeneralNecessity theorem7_kAngluin_necessity:247 and natural-universe version:290. Necessity:207,226 separately handles k=1. |
| S20 | Remark 3 p17, strict finite-list hierarchy and generation contrast | **Not represented as examples/hierarchy:** general equivalences alone do not prove the concrete Ψ failures or generation claim. Scalar Gold results concern different families, not an all-k replacement. |
| S21 | §7 pp17–18 (8)–(9), peeling and residual depth/coverage | **Represented:** peelLayer Stratification:58 has no incoming proper-subset/tell-tale edge; relativeConditionTwo:68, residual Ψ:83, relative stratification:103, global stratification:155. No explicit pairwise-disjointness theorem. |
| S22 | Remark 4 p18, concatenate one-output stratum learners | **Represented:** relativeIdentifier:192, member correctness:199, stratifiedIdentifier:242, reverse bridge:251. |
| S23 | Definitions 5–6 p19, fair-bit randomized learner/event probability | **Not represented:** targetRecognitionBit is a deterministic truth indicator, not a random bit or probabilistic learner. |
| S24 | Figure 1; Definitions 7–9 pp19–21; events (10)–(13) | **Not represented:** native history/prefix chains are deterministic sequences of finite data, not probability-labelled binary computation trees or convergence events. |
| S25 | Theorem 9 pp21–22, deterministic⇒probabilistic all p and reverse p>k/(k+1) | **Not represented:** neither direction/probability threshold appears. No endpoint result inferred. |
| S26 | Procedure 2 pp21–22, first_C canonicalization and Top-k determinization | **Not represented:** native padding and least-index eligibility are not a frequency aggregator over 2^t randomized outputs. |
| S27 | Definition 10 p22; full-support iid enumeration a.s. | **Not represented:** deterministic Presents and presentation-existence lemmas do not supply an iid law or almost-sure claim. |
| S28 | Theorem 10 pp23–24, probabilistic/iid equivalence at each p | **Not represented:** no geometric resampling or odd/even fair-bit extractor. Both existence directions and their causal requirements remain outside native coverage. |
| S29 | Corollary 8.1 p24, failure-event probability≥1/(k+1) | **Not represented:** deterministic necessity cannot alone express this quantitative distributional conclusion. |
| S30 | Theorem 8 p18; Theorem 11 p24, limsup error≥1/(k+1); boosting pp25–26 | **Not represented:** no block aggregation, concentration, summability, Borel–Cantelli, or limsup error theorem in the native evidence. |
| S31 | Theorem 12 p26, R(t)=exp(−t) upper rate | **Not represented:** deterministic strata exist, but scalar statistical-rate ingredient and probability/rate conclusion are absent. This requires new mathematics, not merely a facade wrapper. |
| S32 | §8.3 p26, trivial one-sample zero-error case and nontriviality | **Not represented:** no k+1-common-string predicate or one-sample statistical theorem. |
| S33 | Theorem 13 p27, fixed target/law exp(−2t) lower bound infinitely often | **Not represented:** no common-string distribution construction, error probability, or exponential lower bound; randomized footnote also unrepresented. |
| S34 | pp27–30, acknowledgements/references; no appendix | **Inapplicable as internal formal claims.** Attributed external claims recorded as context; no external-source fidelity judgment. |

Algorithm 1 uses finite input sets, so its native implementation may ignore ordering while the general learner accepts ordered histories. This specializes the witness, not the theorem's presentation quantifier. It returns [] at zero depth or empty I, [0] on infeasibility at positive depth, and a chosen index followed by recursion otherwise. Source {1} is the renamed fallback. Native cons versus the source's union notation preserves at most k guesses and target membership; duplicates cannot cause a lost correct guess. `padIndexList` keeps every existing entry when length≤k and fills remaining slots with 0; the exported membership lemma explicitly establishes this. No cardinality assumption was inferred from an informal “list” label.

The native necessity support is significant additional coverage: `IsTargetLockingSequence` (Necessity:71), its existence theorems (:82,141), `removableTargetSlot` and `dropTargetGuess` (GeneralNecessity:48,68), preservation of a different target (:75), and `reducedAfterTargetLock` correctness for strict subtargets/cones (:109,167) are all present. `psi_of_identifiesOn_strictLanguageCone` (:199) establishes the depth predicate on the entire cone. These statements and definitions support necessity on arbitrary presented languages. Their use of classical semantic target tests in auxiliary constructions is permitted by footnote 4 and does not pass an extra oracle to the learner in the main statement. Proof bodies remain unexamined.

## Completeness of the native boundary and reverse mapping

The authoritative supplement manifest is `865b323d3ee3b6f36c1c1e067a3ee3e159ded9eba09b604c7113551865ad8a44`. Its four entries verified. It contains 491 declarations: 304 theorem types, 175 definition values/types, four inductives, four constructors, and four recursors. All theorem values are null. Exactly 121 entries belong to P14 modules; the remainder are imported deterministic infrastructure and prior scalar results. Census `root` flags are seeds, not selected targets.

`module-coverage.json` reconciles all 29 expected modules, 28 with declarations and the import-only umbrella with zero. Counts agree with the declaration rows. P14 modules are Definitions(9), Psi(23), Stabilization(11), Algorithm(23), Necessity(14), GeneralNecessity(20), Stratification(19), Overview(2), and the zero-declaration umbrella. Imports include Core.Basic/GenericGeneration/Identification/Text, three Paper00A semantic modules, five Paper00 text modules, and eight Support modules. Generated equations, recursors, size machinery, and private helpers were included in the census scan rather than treated as independent additional paper results. The historical original census is not the absence boundary.

Reverse correspondence is as follows: P14 Definitions/Psi map to Section 3/4; Stabilization/Algorithm map to Claim 5.1, Algorithm 1, Theorem 6; Necessity/GeneralNecessity provide the lower-bound theorem and supporting locking/slot-reduction lemmas; Stratification maps to Theorem 2's peeling and alternative learner; Overview exposes only the two selected equivalences. Core and Support give finite histories, samples, finite-set appearance, exact presentations, prefix extension, and eventual stabilization. The prior scalar modules supply one-language tell-tales/learners, locking, finite-language identification, and superfinite impossibility. They add legitimate mathematical support; they are not unseen statistical results.

The external type-dependency set across all 491 rows contains sets, finite sets, lists, naturals, equality/order, countability, functions and propositions; it contains no real-number, measure, probability-law, expectation, exponential-rate, or limsup interface. A scan of type/value dependencies also found no such probabilistic ingredients. This structural evidence, together with the actual substantive definitions/types, supports the Section 8 absence judgments. Names alone, or lack of a theorem_3 facade, would not have sufficed. The QA census records every declaration and module, with type/value hashes and domain flags; no raw proof value was inspected.

## Source questions, Stage 1 review, and remaining limits

These are questions about the pinned source, not silent repairs or Lean defects.

1. **Remark 2 p12:** the printed explanation says a proper sublanguage Z\G of Z\F has |G|<|F|, whereas the inclusion points toward larger removed sets. Its claim that recursively reached base languages have |F|=1 also does not fit arbitrary k. The hierarchy conclusions must be distinguished from this literal explanation; no native example theorem settles the discrepancy.
2. **Algorithm 2 p15:** its while-loop always requests a not-yet-seen string. The global model permits finite languages. A failed positive-depth Ψ language cannot be finite (its entire finite set would be a tell-tale), but at a depth-zero leaf the failed predicate is automatic and the language may be finite. Exhaustion and repetition need an explicit convention or argument. Native necessity does not assert this literal unseen-string routine.
3. **Theorem 10 pp23–24:** sampling D_sigma uses an entire presentation and variable random-bit scans. Definition 5 permits only t observed inputs and t bits at time t. A delayed causal simulation must be supplied to reconcile this description. In the reverse direction a,b are selected from the stream, while the subsequent independence explanation mentions selection from the even subsequence. The exact coupling/stopping convention deserves clarification. No native theorem is available to resolve either issue.
4. **Theorem 11 pp24–26:** the contradiction written in (16) posits one ε>0 uniformly for all targets and valid distributions, stronger than the literal negation of the stated ∀A∃L,D lower bound. A pointwise gap may suffice for the per-distribution boosting proof, but that is a repair to justify, not the quantifier text as printed. Batch sizes/counts also require integer rounding.
5. **Definition 4 p11:** R has a natural domain but is evaluated at c2 t with positive real scaling. Extension/rounding is implicit. Exact-k versus at-most-k is a second representational convention, resolved for positive k by padding as above; k=0 must be treated separately.
6. **Theorem 3 p4 and §8.3 pp26–27:** “best possible” needs the later nontriviality proviso; trivial collections admit zero error from one sample. Footnote 9 states an expected capacity inequality for randomized learners but does not itself establish every quantitative step of the deterministic exp(−2t) statement for random outputs. No extra randomized conclusion is certified here.

No mathematical correction to Stage 1's reconstruction of either selected type was needed. Its presentation premise, finite witnesses, immediate recursion, all layer conjuncts, witness dependencies, BC semantics, and k=0 analysis survive direct rechecking. Its “no statistical content” statement is valid for those selected types. It was not a whole-native-umbrella audit: expanding that observation into an absence claim required the separate full supplement and module reconciliation performed here. The source's explicit noncomputational footnote strengthens the justification for Stage 1's semantic reading without converting it into an effective theorem.

Remaining gaps are separated by kind. A literal decomposition into separately indexed scalar-learner objects, and a same-tell-tale reuse lemma, are small native assemblies/wrappers. The precise Algorithm 2 adversary/invariants and canonical-family calculations are absent as formal constructions or specializations, while the general lower-bound theorem is already represented. Section 8's distributions, randomized learners, probability events, thresholds, rates, and quantitative bounds are missing mathematics throughout the supplied boundary. They cannot be credited from deterministic theorem names or external citations.

The audit covers statements and displayed defining expressions under ordinary declared Lean/Mathlib meanings. It neither rechecks Lean proof bodies nor certifies the paper's proofs, the exporter's implementation, source-to-kernel compilation, an effective algorithm, fresh builds, or human approval. No decisive missing target interface remains: the supplied Psi supplement resolves the recursion ambiguity, and the full native supplement resolves the module-coverage ambiguity. Stage 3 explanations remained closed through report freeze.
