# P00A Stage 3 informed adjudication

The four omitted source results remain formalization gaps: Theorems 2-5 are not proved in the supplied frozen development. Their omission is already disclosed. The effective Theorem 1 and Corollaries 1-3 retain source-matching core statements under the stated effective coding and machine-normalization convention. No genuine Lean statement mistranslation is established for those core endpoints. Additional operational source properties remain outside their coverage.

The explanations resolve whether the semantic/effective distinction and alternative algorithms were intentional. They do not establish literal equality of source and Lean constructions: the phrase **extensionally equivalent** needs qualification because the emitted tell-tale sets can differ. This is documentation precision about a valid alternative specification, not a correction to the source theorem. Another documentation qualification is needed for Theorem 5: its complete result is missing, while Condition 3 and the identification-only implication already have mathematical support through Corollary 2.

Audit completion is separate from these verdicts. The three requested Stage 3 artifacts are complete; the four source formalization gaps and qualified matters have not been turned into passes.

## Reviewer continuity, source identity and frozen evidence

This is the **continuing Stage 2 reviewer**, proceeding only after the coordinator froze Stage 2 at 2026-11-14T00:04:11.408381Z. It is informed adjudication, **not a third independent blind review**. Stage 1, Stage 2, the original source-first inventory and the source-withheld supplement remain immutable. The supplement continued the original Lean-only Stage 1 context and was not fresh/blind; it remained source-withheld according to its run provenance. No mathematical bias or independence claim is inferred from that configuration.

The coordinator supplied task scope and requests to retain the semantic/effective distinction, coverage gaps, normalization and same-witness issues. It supplied no additional mathematical proof argument in this Stage 3 assignment. The local examples and arguments below are this worker's informed judgments, not independent external confirmations. No earlier shared-code or human approval is imported as source-specific approval.

Pinned source: Dana Angluin, *Inductive Inference of Formal Languages from Positive Data*, Information and Control 45(2), 117-135 (1980), DOI 10.1016/S0019-9958(80)90285-5; received June 29, 1979, revised January 29, 1980. Printed journal page equals one-based PDF page + 116. The package lacks an original expected PDF hash. Its bibliographic identity and complete 19 pages were checked during Stage 2; this is not a missing historical-hash match. Source bytes SHA256 `5d9903aa5e0b86a8e4ec1f344539bce328ce69d546561937ee68da338d79721c`; annotation-free reviewed PDF `52853b5d44876fd84f6ceb585d5cef43fa3eae7cdfcac6b6812baa886cb866cf`; full page-marked text `67e8243230c5a9cfb36230dfb6e0f53b6523e2ab58e409df0ba61ebd89a7e04e`. No annotations or alternative edition were used. Stage 3 reread source conventions/procedure portions and visually rechecked PDF pages 7-8 against the same derivative.

The frozen `source-inventory.md` hash remains `4c2fe21aeebe69ce513125c95ea1ac18a33774e6ced6c63dadc1dc616c8a4216`, saved before any Stage 1/Lean access. All hashes in the original Stage 1, supplemental Stage 1 and Stage 2 freeze files were reverified. Stage 3's first observed clock was 2026-11-14T00:09:17Z, after opening the authorized instructions/freeze/explanations; exact per-file timestamps are not exposed.

## Standing source and Lean claims

Source printed 119-120 / PDF 3-4 fixes a finite word alphabet and a family of nonempty languages with one joint effective membership algorithm. Presentations are arbitrary infinite sequences with range exactly the target, allowing repetition and noncomputability. A single effective machine works for the whole family. Its eventual correct index can depend on the presentation and need only denote the target. Guess streams may be finite, with convergence to their last guess, or infinite and eventually constant.

Lean `EffectiveIndexedFamily.mk` contains language, exact Boolean membership, `Computable₂ membership`, and all-member nonemptiness. `EffectiveInferrable` requires one total computable `List Nat -> Nat` identifier with eventual exact-index stability on every positive prefix sequence. `ConditionOne` requires one joint computable `(i,stage) -> Option Nat` emitter with finite tell-tale range, without a stopping certificate. `ConditionTwo` is nonuniform per-index Finset existence. `ConditionThree` counts distinct denoted language sets above a nonempty finite sample; it does not count indices. `ConditionFour` is one computable inclusion function uniform in the pair of indices. These definitions were rechecked in the exact code-only census, rather than inferred from comments.

A tell-tale for Li lies in Li and excludes any proper included family language containing it. The Lean implication `T subset Lj -> Lj subset Li -> Li subset Lj` is the same property. Empty tell-tales and duplicate indices are permitted. There are no probability distributions, losses, numerical rates, runtime bounds or sample-complexity promises in these eight claims.

The source has no extra membership/inclusion oracles for its inference machine. Fixed-family programs may incorporate the family's computable membership algorithm. For Corollary 3, the extra inclusion function is itself required computable, so the named emitter uses ordinary computation. The semantic auxiliary instead uses arbitrary functions/classical choices and contributes no effective guarantee. No pointwise decidability was promoted to a uniform algorithm, and no hypothetical realization of a desired separating family was treated as existence evidence.

## Coverage table: all original slots and linked targets

| Slot / source | Exact Lean target or absence | Stage 2 finding | Final disposition |
|---|---|---|---|
| C01 / Theorem 2, printed 127-129 / PDF 11-13 | TheoremTwoStatement : Prop, Effective.Definitions:92 | Statement only; no proof/witness | Formalization gap, correctly disclosed. |
| C02 / Theorem 5, printed 133 / PDF 17 | No Condition 5/full same-witness result; corollaryTwo supplies identification under Condition 3 | Full result absent | Formalization gap; distinguish existing identification-only support. |
| C03 / Theorem 4, printed 131-132 / PDF 15-16 | No effective conservative-separation witness/predicate in census | Absent | Formalization gap; source construction boundary question stays qualified. |
| C04 effective / Theorem 1, printed 121-122 / PDF 5-6 | theoremOne, Effective.Necessity:582 | Equivalent under explicit model conventions | Matches source core; qualified representation/model. |
| C04 semantic auxiliary | semanticallyInferrable_iff_conditionTwo, Semantic.Characterization:266 | Materially different effective scope | Correctly disclosed non-covering semantic support, not the source effective theorem. |
| C05 / Corollary 2, printed 123-124 / PDF 7-8 | corollaryTwo, Effective.Corollaries:609 | Equivalent core; alternate emitter; contextual strengthening absent | Mixed: matching core, qualified alternate construction/model, contextual operational gap. |
| C06 / Theorem 3, printed 129-130 / PDF 13-14 | No completed-output separation witness/result | Absent | Formalization gap; source boundary question stays qualified. |
| C07 / Corollary 1, printed 123 / PDF 7 | corollaryOne, Effective.Necessity:598 | Equivalent with global nonemptiness | Matches source context with explicit model/coding qualification. |
| C08 / Corollary 3, printed 124-125 / PDF 8-9 | corollaryThree, Effective.Corollaries:327 | Equivalent core; alternate emitter; contextual strengthening absent | Mixed: matching core, qualified alternate construction/model, contextual operational gap. |

Each original slot has exactly one JSON row. C04's two linked theorem targets are split in the table so the semantic support does not mask effective coverage. No additional endpoint was needed or treated as previously reconstructed merely because a comment/import named it.

## Existing-explanation inventory

The following are fallible explanations, not independent mathematical certificates. Their exact whole-file hashes are recorded in `adjudication-run.json` and in the table below. Relevant comments were extracted from the permitted frozen snapshot; theorem proof text was not displayed or audited.

- `stage3-context/PaperMap.md`, lines 20-35: semantic versus effective interfaces and ordinary computation rather than finite-query oracle computation; lines 48 and 125-128: Theorems 2-5 omitted, with only Theorem 2's proposition recorded; lines 50-58: alternative emitter explanation; lines 100-104: exact-index stability, duplicate names and nonemptiness.
- `current-registry.json`, `paper.formalization_scope` and the eight `claims[id=...]` objects: four core source statements claimed covered, four results explicitly uncovered, semantic support explicitly materially different. The strings saying an audit found no issue or mentioning kernel/human checks are metadata assertions; no referenced human ledger, historical review or axiom-audit file was read or certified here.
- `Effective/Definitions.lean`, comments at lines 16,25,29,40,47,53,59: joint effective membership, explicit Computable requirement, standard encoding claim, no halting certificate, and Conditions 1/3/4. These agree with the direct defining expressions.
- `Semantic/Definitions.lean`, comments at lines 20 and 33: repeat-last-guess normalization and nonempty source languages. `Semantic/Characterization.lean`, opening/line 265: non-effective analogue; lines 52 and 224-236: default 0 and classical tell-tale choice. This is disclosure of the semantic distinction, confirmed by exact definitions.
- `Effective/Sufficiency.lean`, comments at lines 242,336,357: bounded candidate search, default 0, pointwise equality to the semantic least-index function. These do not assert equality to an asynchronous source trace or all-time consistency.
- `Effective/Necessity.lean`, opening and lines 134,195,221: bounded stabilization tests, least provisional history and paired emission. This explains an alternate necessity construction; no full proof audit follows.
- `Effective/Corollaries.lean`, comments at lines 175,335,360: direct least-missing-point emitter; classical firstDifference restricted to finiteness analysis; finite-prefix witness emitter. Exact dependencies confirm that firstDifference is not a runtime dependency of conditionThreeEmitter.
- `Results/Overview.lean`, opening: separates the semantic analogue, reports omissions, and uses extensionally equivalent for the alternative emitters. The intended same-specification reading is supported; the literal same-range reading is too strong, as checked below.
- Remaining P00A umbrella/Stabilization/Semantic.Necessity comments were read as boundary context only; their claims about imported proof implementations were not used to certify proofs or expand this audit.

## Discrepancy dossiers and mathematical checks

### 1. Disclosed omissions remain omissions: C01, C02, C03 and C06

Stage 2 found no Theorem 2 proof and no matching Theorem 3/4/5 result in the supplied 569-record native census. The PaperMap and registry confirm that this is intentional scope, not a hidden construction elsewhere claimed covered. This resolves the disclosure question, not the mathematical work needed to formalize the results.

For C01, exact type `Prop` and definition value `exists F, ConditionTwo F.language and not EffectiveInferrable F` record the intended proposition. The frozen source-withheld Stage 1 supplement reconstructs it individually with all family/learner/tell-tale dependencies. A declaration naming this proposition is not a proof with that proposition as its type. No family witness follows. The semantic ConditionTwo equivalence permits noncomputable learners and therefore does not conflict with the negative effective existence statement or establish its witness.

For C03, the full source result requires an actual effectively inferrable family without a conservative effective identifier, not general implications about tell-tales. No conservative predicate or witness theorem appears. For C06, the finite range of a stage emitter does not give a uniform known halt/completion time; documenting that distinction correctly does not establish the source's diagonal halting-time witness. These are substantive source-result formalization gaps, not identified mistranslations of existing assertions.

C02 needs one finer distinction. Its full source Theorem 5 requires Conditions 3 and 5 and **one effective M** with identification, consistency, responsiveness and conservativeness. Condition 5 and that full operational bundle are absent. However, `ConditionThree` is formalized, and `corollaryTwo` already gives identification from it. Informally `(ConditionThree and ConditionFive) -> identification` follows by dropping the second premise. The registry sentence saying neither the hypotheses nor any conclusion component is represented is therefore too broad if read literally; it is defensible only as shorthand for no complete source-facing Theorem 5 interface. No new Lean theorem or selector predicate is inferred. Suggested wording: "Condition 5 and the full same-machine guarantee are unformalized; Condition 3 and the identification-only consequence are already available."

No proof or full construction audit of the unformalized source diagonal families was performed, and no metadata source_assessment overrides that limit.

### 2. Effective computation and total-prefix normalization: C04/C05/C07/C08

`Effective/Definitions.lean:29` explicitly describes Computable as the recursive-function version of the Turing requirement modulo standard encodings; `Semantic/Definitions.lean:20` explicitly describes repetition of a finite last guess. The exact types preserve ordinary total computation for membership, learner, emitter and inclusion where required. The explanation is consistent with the definitions, but comments alone do not prove equivalence of machine models.

The following is the limited mathematical justification, **informal and not Lean-checked**. From a source machine, on a finite prefix of length n, perform a bounded simulation (stopping if another unavailable sample is requested) and return its most recent guess or a default. As n and the simulation bound increase, every fixed finite source computation/event on that presentation becomes visible. If the successful source guess sequence is finite, its final correct guess eventually remains the returned value. If it is infinite and eventually a fixed correct index, all sufficiently long simulations return that same correct index. This yields a total computable finite-history identifier for ordinary identification. Conversely, run a total computable list learner after requesting each next datum; every call terminates and the resulting source guess stream is infinite and eventually correct. Word codes, list encodings and zero/one index shifts are effective recodings.

This supports equivalence of **identification existence** under the ordinary coding convention. It does not give identical traces, identical guess times, a computable family-to-program transformer, a rate, or preservation of operational consistency/responsiveness/conservativeness. No explicit formal asynchronous/prefix bridge is present in the inspected interface. The source's stronger operational statements remain separately assessed.

The semantic auxiliary is explicitly an arbitrary-function result with Condition 2, broader countable datum domains and no all-member nonemptiness. Its classical choices do not imply effective enumerators. The registry correctly marks it materially different and non-covering for effective Theorem 1. The effective endpoint independently supplies the proper source statement, so no source correction or extra realization hypothesis is needed.

### 3. Same specification does not mean the same emitted set: C05/C08

The PaperMap, registry and facade call the dovetailed emitters extensionally equivalent to the source stage procedures. The definitions and comments demonstrate intentional alternative constructions. Their **finite-tell-tale specifications** agree, but literal emitted-range equality is false in general.

A small exact example checks every relevant premise. Use the first three words of a unary alphabet in source enumeration order, with effective codes 0,1,2. Let an infinite computable indexing repeat only the two distinct languages

```text
T = {0,1,2},    U = {0,1}.
```

Both are nonempty recursive languages with a single trivial joint membership algorithm. Inclusion is uniformly decidable. Every nonempty finite sample has at most two distinct compatible family languages, so Condition 3 holds. Each member itself is a finite tell-tale, so Condition 2 holds. Duplicate indices cause no extra distinct languages. Take the target T.

For source Corollary 2, A starts at {0}. The only distinct compatible language with a proper included finite approximation is U, and every successful approximation prefix must reach code 2. The target prefix output is therefore all of T, after which U is incompatible and no further enlargement is possible. The source output set is {0,1,2}. The exact Lean conditionThreeEmitter always emits least target member 0 and, from U, only the least target-minus-candidate point 2. Candidates denoting T add no difference. Its entire output set is {0,2}.

For source Corollary 3, A starts empty; the only distinct proper included language is U. Its least witnessing prefix again reaches code 2, and the source emits the full target prefix {0,1,2}. The Lean conditionFourEmitter emits only the least point missing from U, namely 2, so its entire output set is {2}. These exact conclusions are analytic evaluations of the displayed definitions and source finite procedures, not conclusions extrapolated from finitely many tested stages. No finite experiment or compilation was used.

All three target subsets {0,1,2}, {0,2} and {2} are valid tell-tales for T relative to this family because each contains 2, which U lacks. Thus the example **does not refute either source theorem or Lean core corollary**. It refutes only a literal interpretation of unqualified range/trace equivalence. The smallest documentation repair is "alternative effective emitters satisfying the same finite-tell-tale specification". No source repair or Lean code change is called for by this example.

Two local checks support that intended explanation beyond the example, without certifying whole constructions or their formal proofs. Under Condition 3, only finitely many distinct family languages contain the least target member; each contributes at most one least missing witness, so the alternative output set can be finite despite infinite duplicate indices. A proper included competitor containing the least target member is eventually tested at a long enough finite prefix and supplies its missing witness. Under Condition 2, for each proper included Lj a tell-tale has some t outside Lj; the least missing point x_j satisfies x_j<=t. For a nonempty tell-tale all such outputs lie below its maximum. For an empty tell-tale there is no proper included family language, and the emitter has no such outputs. These checks explain why emitting fewer harmless target elements preserves the tell-tale specification; they do not certify every Lean/source proof step or program realization.

Exact helper interfaces already reconstructed in Stage 1/2 assert computability and IsEnumeratedTellTale for each named emitter under the right hypotheses. They are corroborating statement-level evidence, not proof-body review. The classical firstDifference definition is outside the runtime emitter dependency list, so no noncomputable oracle is being excused by the alternative-construction explanation.

### 4. Contextual same-machine consistency and responsiveness remain missing

The source printed 131 / PDF 15 says the constructed Theorem 1 machine is consistent and can be modified to be responsive; the Corollary 2 and 3 machines may also be chosen with both properties. Existing core theorem endpoints only assert identification. The exact type does not supply an unbundled consistency theorem on the same existential witness, and no such native property interface was found. The documentation does not establish one by calling its learner Angluin's construction.

A direct valid-history example prevents treating this as mere wrapper assembly for the existing named defaulting learner. Take a computable family with L0=L1={0}, L2={1}, and all remaining members repeats of {0} or {1}. It has nonempty members, joint recursive membership, Condition 3, Condition 2 and decidable inclusion. The one-element history [1] is a valid prefix of a positive presentation of L2. At length 1 the exact effectiveLearner scans only indices 0 and 1; both fail the observed-membership test, regardless of the emitter. It returns default 0, whose language {0} does not contain the observed datum 1. Thus this **named learner** is not consistent on every valid history. This is an informal exact-definition argument, not Lean-checked.

This does not say that no consistent/responsive identifying source machine exists; the source describes a different fallback that searches for a consistent hypothesis on valid samples. It shows that a proof about the current defaulting function cannot simply be bundled into the stronger property, and ordinary identification normalization need not preserve that property. Core C04/C05/C08 statements remain covered; the contextual stronger machine guarantees are additional formalization work. For Theorem 5, all four properties must belong to one selector-based machine; separate existential witnesses would not suffice.

### 5. Source-global assumptions, editorial labels and unresolved source proof questions

C07's nonemptiness is not a changed hypothesis: Section 4's opening on printed 123 / PDF 7 explicitly fixes nonempty recursive members before stating Corollary 1. Its conclusion intentionally forgets effective tell-tale selection. Exact witness dependencies agree: one M precedes targets/presentations; T_i follows i and precedes competitor j. No uniform halting selector is promised.

The source printed 124 / PDF 8 heading says COROLLARY 4 while its body explicitly defines Condition 4 and the next source Corollary 3 uses Conditions 2 and 4. Referring to that body as the inclusion condition is a source-context interpretation, not a mathematical source correction or an extra theorem to add.

Stage 2's Theorem 3 exponent/step-count convention and Theorem 4 least-unread-prime-power observations concern boundaries inside **unformalized source proof procedures**. The registry's no-known-issue notes are not arguments resolving them. They remain qualified questions from the pinned source, not accepted source errors, theorem refutations, or Lean error findings. The smallest justified action here is to retain the questions for a dedicated construction review; no source repair is accepted, and this stage did not broaden into that proof audit.

## Revised dispositions, limits and minimal remaining work

Four source result statements still need formalization if extending the paper's scope: Theorems 2-5. For Theorem 2 a statement exists without proof; Theorem 3 needs the halting-output separation interface/witness; Theorem 4 needs conservative semantics and a witness; Theorem 5 needs Condition 5 and one machine with the complete operational guarantee. These are acknowledged coverage gaps, not newly discovered erroneous translations.

For already covered statements, retain explicit coding/model qualifications and the semantic/effective separation. Improve the emitter-equivalence wording and the broad Theorem 5 omission sentence when documentation edits are separately authorized. Keep core corollary coverage separate from the contextual consistent/responsive Remark. No existing correction should be reported as an unexplained Lean bug, and no unsupported comment is promoted to a pass.

All local mathematical arguments here are informal and not Lean-checked. No complete source proof, full Lean theorem proof, full alternate algorithm construction, kernel/axiom audit, historical human review or source-specific prior approval was certified. No probabilistic or oracle theorem was silently introduced. Original frozen evidence was reverified, not rewritten. No Lean/library/registry/human record/Git changes, builds, external messages, network lookup or new subagents occurred. Only adjudication.md, adjudicated-claims.json and adjudication-run.json were written for coordinator validation. Requested model gpt-6.1-sol/xhigh; backend model/revision and applied reasoning configuration remain unobservable.

## Explanation file hashes

| Frozen file | SHA256 |
|---|---|
| `P00A/stage3-context/PaperMap.md` | `6f32b5720bf73db31b3e2637d235c0f4895031d9437b3273714de4ddb2930e24` |
| `P00A/stage3-context/current-registry.json` | `b3cb1bff106fbb95219aee4067d72a4b58eef2032d789a789c59841c9ae83099` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Effective/Corollaries.lean` | `68429e88e995968332af2d2628f6c860f6752bf5ed872b53fc55630981c0cd2b` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Effective/Definitions.lean` | `bb377c00f49b50c553226fb9d8b131d6739f0c0afd445b13fe04652e9ac6f2ff` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Effective/Necessity.lean` | `712f4f3b48e9f4c8208b6fa1621b098af672ee48a4fa04ac3c33882678b62add` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Effective/Stabilization.lean` | `96e56c77a04ee6795e16e894d29117bc7b9de4e679c09186ddb023d495d4e8ba` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Effective/Sufficiency.lean` | `4aeaf20cca04ee6e5a464d7131560a62147b8a90f397439195933db4626685ff` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Effective.lean` | `af3495be39797a64cc22a0de24c39091eeeb8e4b222f2d0ea629bbb1df764b31` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Results/Overview.lean` | `6ba136e66ef9433e0dba3d2d8423af1d1a5ee70f180e45efe188cd5bbe06c52e` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Semantic/Characterization.lean` | `453449e97a81b4d92597d9891ad76929ab6f4ac94f737bf41aa8ad8ae920bcdd` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Semantic/Definitions.lean` | `eee924a6cdc72f599d69e31fefad7f3467c47bedc9f6bfecf1ae2f373207bb58` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Semantic/Necessity.lean` | `3ec21a4d4fc7fa2feb9891e4a2458390fb85c2403c764c8c800b36de2a2e511c` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference/Semantic.lean` | `cc13cfbea9ef8cb63e6db81090ef8fb7fff95d8e063f3eeadf1760ea98597b30` |
| `owner/lean-snapshot/GenLimit/Paper00A_PositiveDataInference.lean` | `8bc54462f4cb3abb00a095b8f100943c87ec532cac826f44b419682ae072c0bb` |
