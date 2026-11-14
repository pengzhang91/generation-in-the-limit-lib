# P00A Stage 2 source comparison

All eight original slots were independently compared. The core statements of Theorem 1 and Corollaries 1-3 correspond to the effective Lean endpoints, subject to the explicit coding/model convention below. Theorem 2 is present only as a proposition definition; Theorems 3-5 have no matching result in the supplied native census. The additional semantic characterization is a distinct result and cannot replace the effective source theorem. These are model findings about statements/interfaces, not proof certification or human review.

## Identity, scope and source-first freeze

Source: Dana Angluin, *Inductive Inference of Formal Languages from Positive Data*, Information and Control 45(2) (1980), printed 117-135, DOI 10.1016/S0019-9958(80)90285-5. The source was received June 29, 1979 and revised January 29, 1980. Printed journal page = one-based PDF page + 116. The 1979 preliminary version is mentioned but was not supplied, read or substituted.

The package has **no original expected PDF hash**. The reviewed annotation-free derivative has SHA256 `52853b5d44876fd84f6ceb585d5cef43fa3eae7cdfcac6b6812baa886cb866cf`; the packaged source bytes hash to `5d9903aa5e0b86a8e4ec1f344539bce328ce69d546561937ee68da338d79721c`; page-marked text hashes to `67e8243230c5a9cfb36230dfb6e0f53b6523e2ab58e409df0ba61ebd89a7e04e`. All 19 pages of text and all 19 rendered annotation-free pages were read/visually inspected. Bibliographic identity is established with the missing-original-hash qualification, not an invented historical hash match. No annotation payload was inspected.

The independent source assertions, conventions, algorithm interfaces and questions were saved in `source-inventory.md` at 2026-11-13T23:48:39.202849Z before any Stage 1 or Lean access; its frozen SHA256 is `4c2fe21aeebe69ce513125c95ea1ac18a33774e6ced6c63dadc1dc616c8a4216`. The first post-access clock observation was 2026-11-13T23:49:04.310959Z; precise per-file access times are not exposed. The source index was used only for scope. An initial wrong-path index open failed; README/manifest were read before correcting that path. This administrative deviation did not expose Stage 1 or code during the source phase.

The frozen Stage 1 output hashes matched `stage1-freeze.json`. The original Stage 1 remains unchanged, including its four original no-endpoint rows. After the first Stage 2 draft, the coordinator commissioned a source-withheld supplemental reconstruction of the C01 proposition definition. It was frozen at 2026-11-14T00:01:19.912650Z and only then read by this worker; the first clock observation after opening its freeze was 2026-11-14T00:01:50Z. All three supplemental output hashes matched `stage1-supplement-freeze.json`. The supplement continues the original Lean-only Stage 1 context; it is not claimed to be a fresh or blind context. It adds one individually reconstructed proposition definition and its 18 dependencies, not a new theorem endpoint. The 34 original recursive records, including five target theorem types, exactly match their native records. All ten supplied Stage 1 SHA256SUMS entries matched. Snapshot identity is the supplied source-snapshot hash `befc88a67a9c004e5f3858848eef24b5aad80e157ec5e1d52f73fe42b8073d37`; the underlying repository was not re-exported or compiled. The 569-record census covers the 31 modules listed in snapshot.json. No whole-repository absence conclusion is made.

## Independent source inventory and comparison conventions

The independent inventory is preserved separately and not rewritten after code access. Its central findings are as follows.

- Printed 119-120 / PDF 3-4: the family has nonempty members and a **single jointly effective membership procedure**. Presentations are arbitrary infinite sequences with range exactly the target, allowing repetition. One effective machine must succeed on every presentation; the final index need only denote the target and may depend on the presentation. Source machines can have null, finite or infinite guess streams; a nonempty finite stream converges to its last guess.
- Condition 1, printed 121 / PDF 5: one uniform effective enumerator whose output range for each index is finite and tell-tale; no halting condition. Condition 2, printed 123 / PDF 7: only per-index finite tell-tale existence. Condition 1 prime, printed 129 / PDF 13: uniform effective complete output followed by halting. These are three different requirements.
- A tell-tale T for Li has T subset Li and no proper included family language containing T. Lean's `T subset Lj -> Lj subset Li -> Li subset Lj` is exactly this exclusion. Empty tell-tales are permitted; unique original-index recovery is not required.
- Condition 3, printed 123 / PDF 7, counts distinct denoted language sets compatible with a **nonempty** finite sample, not compatible indices. Condition 4, printed 124 / PDF 8, is a uniform effective inclusion decision procedure. Condition 5, printed 132 / PDF 16, is a partial recursive minimal-compatible-index selector on all nonempty finite samples admitting such an index.
- Theorem 5 requires one machine simultaneously identifying, consistent, responsive and conservative. Theorem 4 excludes even an identifying conservative machine without adding consistency/responsiveness. There are no distributions, losses, confidence levels, finite-sample rates or runtime complexity promises in any of the eight scoped claims.

For each effective result, natural numbers replace effectively encoded finite words and zero-based indices replace positive indices. Lean has total `M : List Nat -> Nat` and tests eventual stability on every finite prefix. This is the usual normalized effective-learning presentation of the source asynchronous Turing model: bounded simulation can turn successive finite prefixes into a last-seen guess, and a total prefix learner can be run after requests. This model/coding interpretation is mathematical comparison, **not a formally checked bridge theorem in the supplied snapshot**. The source admits stuttering/withholding, finite guess streams and arbitrary computation between requests; Lean named functions need not have the same operational traces. Any stronger operational comparison stays unresolved.

Write ID(M,L) for

```text
forall z s, range(s)=Lz ->
  exists k, Lk=Lz and exists N, forall t>=N, M(s[0:t])=k.
```

The single M is chosen before z and s; k and N may depend on the entire s. `EffectiveIndexedFamily.mk` carries language, exact Boolean membership, jointly `Computable₂ membership`, and every-member nonemptiness. `EffectiveInferrable F` is `exists M, Computable M and ID(M,F.language)`. This carries the source uniformity rather than inferring it from pointwise decidability. `ConditionOne` carries one jointly computable stage emitter. `ConditionFour` carries one jointly computable inclusion function. No family-to-program compiler or uniform convergence bound is supplied in either source claim.

## Full comparison matrix

`Equivalent` below assesses the indexed theorem/corollary sentence under the explicit coding/model convention. Literal procedure equality and the later contextual strengthened Remark are assessed separately. Exactly one JSON record remains assigned to each original slot; C04 is split here because it has two different linked endpoints.

| Unit | Source locator (printed / PDF) | Checked Lean anchor | Statement correspondence | Strength and scope |
|---|---|---|---|---|
| C01, Theorem 2 | 127-129 / 11-13 | Effective.Definitions:92, TheoremTwoStatement | Not covered as a result; statement only | Exact negative existence proposition defined, no family witness theorem. |
| C02, Theorem 5 | 133 / 17; definitions 131-132 / 15-16 | ConditionThree; corollaryTwo; full census search | Not covered | Identification from thickness alone lacks selector hypothesis and all three machine properties. |
| C03, Theorem 4 | 131-132 / 15-16 | EffectiveInferrable; full census search | Not covered | No effective separating family or conservative predicate/result found. |
| C04 effective, Theorem 1 | 121-122 / 5-6 | theoremOne, Effective.Necessity:582 | Equivalent | Both uniform effectiveness requirements and finite-range tell-tales retained; no extra realization premise. |
| C04 auxiliary semantic | compare 121,123 / 5,7 | semanticallyInferrable_iff_conditionTwo, Semantic.Characterization:266 | Substantively different from the effective source statement | Both existence notions weaken, datum/family scope broadens; no single strength ordering of biconditionals. |
| C05, Corollary 2 | 123-124 / 7-8 | corollaryTwo, Effective.Corollaries:609 | Equivalent core statement | Extensional finite thickness retained; no stronger index-finiteness assumption. |
| C06, Theorem 3 | 129-130 / 13-14 | ConditionOne; full census search | Not covered | Finite-range emitter lacks a completion certificate, but no halting-output separation theorem is present. |
| C07, Corollary 1 | 123 / 7 | corollaryOne, Effective.Necessity:598 | Equivalent | Effective identification implies semantic finite tell-tales; no effective selector is concluded. |
| C08, Corollary 3 | 124-125 / 8-9 | corollaryThree, Effective.Corollaries:327 | Equivalent core statement | One joint inclusion program retained; arbitrary noncomputable oracle not substituted. |

## Target and uncovered-slot dossiers

### C01 — negative effective existence is defined, not established

`TheoremTwoStatement : Prop` has definition value:

```text
exists F : EffectiveIndexedFamily,
  ConditionTwo F.language and not EffectiveInferrable F.
```

This agrees with the source Theorem 2 proposition, including nonemptiness/joint recursive membership through F. It is **only a definition**. The frozen `stage1-supplement.md` and `stage1-supplement.json` independently reconstruct the closed definition, its existential-family fields, per-index tell-tale witnesses and negated family-wide computable identifier. All 19 supplemental kind/type/value records were checked against the original frozen native census. The supplement explicitly distinguishes a declaration of type `Prop` from a proof whose type is `TheoremTwoStatement`; it supplies no concrete family or algorithm. It confirms the statement-only correspondence and leaves this slot **not covered as a proved source result**. Its scope does not prove that no other theorem exists; the separately reported native search supports the bounded absence finding. No native declaration depends on `TheoremTwoStatement`; no matching existential theorem, cancellation-machine enumeration, prime-power state construction, or diagonal-family witness was found. The absence finding uses all 569 native names and searches across all types/available definition values, not the empty endpoint array alone. `semanticallyInferrable_iff_conditionTwo` does not contradict the source: a noncomputable semantic identifier can exist for the source counterexample. A proposition, or a hypothetical conditional realization of it, would not establish the source existential witness.

### C02 — all four conclusions must share one effective machine

Theorem 5 is stronger than the corollary that finite thickness permits identification: its additional effective descriptive selector supports conservative selection. The source f may be partial off the required finite-sample domain. Source nonempty compatible samples have a minimal compatible language by finite thickness; thus f must halt there. Neither this selector interface nor a conservative/response state update appears in the native census. The existing `corollaryTwo` concludes `EffectiveInferrable`, so the extra conclusion cannot be inferred from its theorem type. No same-witness theorem or separate property assertions on a named witness were found. A total arbitrary selector, if supplied, would also not by itself satisfy the source partial-recursive requirement. The named source procedure is inventoried, but no corresponding Lean procedure is available for comparison.

### C03 — separation requires an actual effective family

Theorem 4 asserts `exists F, EffectiveInferrable F and not exists M, Computable M and ID(M,F) and Conservative(M,F)`. The source construction uses one infinite prime-power member and bounded-simulation finite members for each machine, combined by computable pairing. No such family, conservative predicate or source enumeration procedure was found in the supplied census. General locking/tell-tale lemmas and the effective iff supply implications, not this existential separating family. No proposed realization assumption was silently discharged. The source observation that the same family has Condition 3 is also unrepresented as a concrete witness fact.

### C04 — effective iff matches; semantic iff has separate scope

The effective target expands exactly to:

```text
forall F : EffectiveIndexedFamily,
 (exists M, Computable M and ID(M,F.language)) <->
 (exists emit, Computable₂ emit and forall i,
   let Ei = {x | exists stage, emit i stage=some x};
   Ei.Finite and Ei subset Li and
   forall j, Ei subset Lj -> Lj subset Li -> Li subset Lj).
```

The side conditions match Condition 1 and the source family model. The emitter is total in `(i,stage)` but need not have a known final emission; `none` and repeated outputs permit arbitrary idle behavior. This is a normal representation of an effective enumerator with finite range, not a uniformly halting completed finite-set selector. Native helper types `ConditionOne.effective_sufficiency` (Sufficiency:422) and `effectiveInferrable_conditionOne` (Necessity:574) assert the two implications with no extra realization/correctness hypothesis. Their proof bodies were not read. F's membership fields are source standing assumptions, not extra obligations postulating the conclusion.

The auxiliary semantic target instead states, for a countable nonempty type alpha and any `Nat -> Set alpha` family, `exists arbitrary M, ID(M,C)` iff `forall i exists finite Ti, tellTale(C,i,Ti)`. It has no effective membership, no computable learner, no uniform emitter, and allows empty family members. `chosenTellTale` uses classical choice; `constantTellTaleApproximation` ignores stage; `semanticLearner` makes classical predicate decisions. These broaden semantic scope while weakening effectivity on both sides; the biconditional should not be described as simply stronger or weaker than the effective source theorem. The effective endpoint separately covers the source, so this additional semantic result is not a missing effective statement.

### C05 — extensional thickness is preserved

`ConditionThree C` is `forall S : Finset Nat, S.Nonempty -> Finite {L | L in range C and S subset L}`. This matches the source exactly and allows infinite repeated naming, infinite total range, and no effective finite-superset bound. `corollaryTwo` concludes `exists M, Computable M and ID(M,F.language)`. It assumes neither Condition 4 nor a supplied emitter. `conditionThree_conditionOne` (Corollaries:602) separately asserts existence of the uniform finite-range emitter under the same thickness hypothesis. The later printed 131 consistent/responsive strengthening is additional source context: no corresponding same-witness property theorem was found, and the named defaulting learner can be inconsistent transiently. Core Corollary 2 equivalence therefore does not certify the stronger Remark.

### C06 — completed-output separation remains uncovered

The source Condition 1 prime requires a procedure which knows it has produced the whole finite tell-tale and halts for every family index. Lean `ConditionOne` deliberately gives only a jointly computable infinite stage interface with finite output range, so its definition does not accidentally strengthen to Condition 1 prime. No completed-tell-tale predicate, diagonal halting-time family, even/odd member learner or no-halting-selector theorem was found. Theorem 1 plus a semantic finite-set choice is not a replacement for the source Theorem 3 existential counterexample.

### C07 — effective premise, non-effective conclusion

`corollaryOne` expands to `forall F, EffectiveInferrable F -> forall i exists T : Finset Nat, T subset Li and forall j, T subset Lj -> Lj subset Li -> Li subset Lj`. The T witness is fixed before j and need not be selected computably. The source corollary sentence omits "nonempty", but the Section 4 convention on the same printed page explicitly supplies it. The F constructor therefore does not impose an unacknowledged stronger assumption. The source/Lean conclusions exclude proper included competitors without demanding exact original-index recovery or separation from superlanguages/incomparable languages.

### C08 — inclusion is uniformly effective

`corollaryThree` expands to `forall F, ConditionTwo F.language -> ConditionFour F -> EffectiveInferrable F`. `ConditionFour` is `exists inclusion, Computable₂ inclusion and forall i j, inclusion i j=true iff Li subset Lj`. This preserves the source uniformity and two-index dependence; pointwise `Decidable (Li subset Lj)` would not suffice, and was not substituted. The finite tell-tales in Condition 2 may be nonuniform; the inclusion program and membership program provide the effective access needed by the named alternative emitter. The contextual consistent/responsive Remark is not an assertion of this endpoint or another found same-witness result.

## Named algorithm-definition correspondence, separately from proof audit

The theorem types above quantify existential witnesses; they do not name the constructions whose definitions were inspected. Supporting helper theorem types specify some interfaces but their proof bodies do not enter the comparison.

| Source procedure | Inspected Lean definition and access | Interface correspondence and differences |
|---|---|---|
| Theorem 1 sufficiency, printed 121 / PDF 5 | effectiveLearner, Sufficiency:338; effectiveStageEligible:244; observedCheck:180; emissionCheck:231 | Both use current positive sample and finite tell-tale approximation, choosing a least bounded candidate. Lean scans i<=length with firstTrue, emission stages <length, and always outputs an index; source withholds when no candidate exists. Zero/one indexing shifts finite-stage bounds. Default 0 and empty-history output need not be consistent. Eventual specification matches; traces and the source consistency property are not literally preserved. |
| Theorem 1 necessity, printed 122 / PDF 6 | lockingEmitter, Necessity:224; provisionalHistory:197; stabilizationCandidateCheck:136; extensionAccepted:71 | Source grows a monotone history via detected changes and canonical samples. Lean tests least encoded candidate histories against bounded extensions, emits entries of provisional histories using paired stages, and does not decide universal locking at runtime. Both interfaces target a uniform finite tell-tale range; they are different constructions. |
| Corollary 2 emitter, printed 123-124 / PDF 7-8 | conditionThreeEmitter, Corollaries:364 | Source adapts an increasing target initial segment and emits its members. Lean enumerates the least target member and least target-minus-candidate witnesses using bounded prefix inclusion tests. It does not require complete inclusion or effective enumeration of all compatible languages. Output sets/order need not equal the paper's. |
| Corollary 3 emitter, printed 124-125 / PDF 8-9 | conditionFourEmitter, Corollaries:177 | Source repeatedly finds a proper included compatible candidate and enlarges a target prefix. Lean pairs (j,x), recognizes proper inclusion with the supplied program, and emits the least Li-minus-Lj point for all such j. It is an alternative finite-range tell-tale construction. |
| Theorems 2-4 diagonal constructions; Theorem 5 conservative selector loop | No corresponding native definitions found | Source interfaces are independently inventoried. No comparison of a missing algorithm, and no full construction proof audit, is claimed. |

Direct helper types checked: effectiveLearner_computable and effectiveLearner_eq_semanticLearner; lockingEmitter_computable; conditionThreeEmitter_computable and conditionThreeEmitter_isEnumeratedTellTale; conditionFourEmitter_computable and conditionFourEmitter_isEnumeratedTellTale; and the condition-to-ConditionOne implications. These assert computation/tell-tale specifications under the stated hypotheses. They do not certify proof steps here. The classical `firstDifference` mentioned in Stage 1 is not a dependency of `conditionThreeEmitter`; no runtime noncomputable minimum is inferred.

## Discrepancies, source questions and Stage 1 corrections

Material coverage gaps are C01/C02/C03/C06. C01 has a source-matching proposition definition but no asserted result; the other three lack the relevant statement/predicate/construction interfaces in this census. Operational differences in C04/C05/C08 are alternative constructions with the same theorem-level specification, and are not identified as Lean errors merely because they differ from source proof procedures. The semantic extra theorem has different scope and no claimed effective conclusion.

Unresolved source questions, preserved from the independent inventory:

1. Printed 124 / PDF 8 visibly labels the Condition 4 definition **COROLLARY 4**. This is a printed label anomaly, not an additional theorem to invent or a Lean error.
2. Printed 130 / PDF 14 displays the truncated prime-power family without an explicit positive-exponent lower bound; surrounding prose uses positive powers. Immediate diagonal halting/step-count conventions need clarification before a literal construction boundary audit.
3. Printed 132 / PDF 16 selects the least unread prime power after a distinguished guess while finite members always include the baseline prime. If that guess precedes every request, the least unread power can be the baseline already inserted into every finite member. A machine normalization or a larger unread exponent may be intended. This remains an unresolved source construction question; no theorem falsity or Lean bug is inferred.

Stage 1 was substantively accurate on the checked effective definitions and quantifiers. It intentionally stopped at empty endpoint arrays for four slots; Stage 2 extends that fallible intermediary with the source-aware native census search and the statement-only C01 finding. The later frozen source-withheld supplement confirms the C01 interpretation without changing the original Stage 1 artifacts or retroactively adding an endpoint to their absent-endpoint rows. No correspondence verdict changes after incorporating it. Its semantic/effective distinction is confirmed. Its source-free algorithm reconstruction is now compared and found to use different schedules/output choices from the paper; this is additional correspondence analysis, not a correction to its exact code reconstruction. No source hypothesis, same-witness property or effective uniformity was supplied merely by trusting a name.

## Coverage checklist and remaining limits

- Eight original slots retained individually; five linked target theorem types rechecked; both C04 targets split in the matrix; unlinked slots searched in the native census before findings.
- Source global conventions, Conditions 1, 1 prime, 2-5, nonempty targets/samples, duplicate indices, arbitrary presentations, empty tell-tales, finite guess streams and final-index witness dependencies addressed.
- All full-paper examples and remarks read as context. Pattern languages, restricted regular-expression examples and prime-multiple Example 4 are not additional claim-index slots, and no unprovided external Angluin 1979 edition was substituted.
- Source printed locators and one-based PDF locators supplied. Formula ambiguities checked on rendered annotation-free pages. Source inventory frozen before Stage 1/code access; later source-withheld supplement incorporated only after coordinator validation/freeze. Actual ordering and hashes recorded in stage2-run.json.
- Uniform algorithms distinguished from arbitrary functions, per-index existence, pointwise decidability and noncomputable oracles. No conditional realization premise is mistaken for an existence proof. Missing contextual same-witness consistency/responsiveness results are explicit.
- Named definition/interface audit completed as described; full correctness of alternative enumeration/locking constructions, asynchronous model normalization, suppressed proof arguments, and target proof-selected witnesses remain outside the certified scope.

No theorem proof bodies, owner files, stage3-context, registry/PaperMap assessments, old audit reports, other paper packages, human ledger or parent history were read. Shared-code names inside the permitted native census were used only as supplied dependency evidence. No source-specific prior approval is assumed. No network lookup, Lean compilation, Lake build, library edit or Git mutation was performed. Only the four authorized Stage 2 result artifacts are deliverables. Requested model is gpt-6.1-sol with xhigh reasoning; actual backend identity/revision and applied effort are not independently observable. Stop here for coordinator verification/freeze before any explanations or adjudication.

## Direct exact Lean interface evidence

These exact types and defining bodies were selected from the code-only native census; only definitions have values below. Standard external Lean/Mathlib encodings and meanings are trusted.

### GenLimit.Angluin.TheoremTwoStatement

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:92`; definition.

```lean
Prop
```

Definition value:

```lean
∃ F, And (@GenLimit.Angluin.ConditionTwo.{0} Nat F.language) (Not (GenLimit.Angluin.EffectiveInferrable F))
```

### GenLimit.Angluin.EffectiveIndexedFamily.mk

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:18`; constructor.

```lean
(language : GenLimit.Generic.LanguageFamily.{0} Nat) →
  (membership : Nat → Nat → Bool) →
    (∀ (i x : Nat),
        Iff (@Eq.{1} Bool (membership i x) Bool.true)
          (@Membership.mem.{0, 0} Nat (GenLimit.Generic.Language.{0} Nat) (@Set.instMembership.{0} Nat) (language i)
            x)) →
      @Computable₂.{0, 0, 0} Nat Nat Bool (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
          (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Primcodable.bool membership →
        @GenLimit.Angluin.AllNonempty.{0} Nat language → GenLimit.Angluin.EffectiveIndexedFamily
```

### GenLimit.Angluin.EffectiveInferrable

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:33`; definition.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F =>
  ∃ M,
    And
      (@Computable.{0, 0} (List.{0} Nat) Nat
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) M)
      (@GenLimit.Angluin.SemanticallyIdentifies.{0} Nat M F.language)
```

### GenLimit.Angluin.ConditionOne

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:49`; definition.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F =>
  ∃ emit,
    And
      (@Computable₂.{0, 0, 0} Nat Nat (Option.{0} Nat) (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
        (@Primcodable.option.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)) emit)
      (∀ (i : Nat), GenLimit.Angluin.IsEnumeratedTellTale F.language i (GenLimit.Angluin.enumeratedSet emit i))
```

### GenLimit.Angluin.IsEnumeratedTellTale

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:42`; definition.

```lean
GenLimit.Generic.LanguageFamily.{0} Nat → Nat → Set.{0} Nat → Prop
```

Definition value:

```lean
fun C i T =>
  And (@Set.Finite.{0} Nat T)
    (And (@HasSubset.Subset.{0} (Set.{0} Nat) (@Set.instHasSubset.{0} Nat) T (C i))
      (∀ (j : Nat),
        @HasSubset.Subset.{0} (Set.{0} Nat) (@Set.instHasSubset.{0} Nat) T (C j) →
          @HasSubset.Subset.{0} (GenLimit.Generic.Language.{0} Nat) (@Set.instHasSubset.{0} Nat) (C j) (C i) →
            @HasSubset.Subset.{0} (GenLimit.Generic.Language.{0} Nat) (@Set.instHasSubset.{0} Nat) (C i) (C j)))
```

### GenLimit.Angluin.ConditionThree

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:55`; definition.

```lean
GenLimit.Generic.LanguageFamily.{0} Nat → Prop
```

Definition value:

```lean
fun C =>
  ∀ (S : Finset.{0} Nat),
    @Finset.Nonempty.{0} Nat S →
      @Set.Finite.{0} (Set.{0} Nat)
        (@setOf.{0} (Set.{0} Nat) fun L =>
          And
            (@Membership.mem.{0, 0} (Set.{0} Nat) (Set.{0} (GenLimit.Generic.Language.{0} Nat))
              (@Set.instMembership.{0} (GenLimit.Generic.Language.{0} Nat))
              (@Set.range.{0, 1} (GenLimit.Generic.Language.{0} Nat) Nat C) L)
            (@HasSubset.Subset.{0} (Set.{0} Nat) (@Set.instHasSubset.{0} Nat) (@Finset.toSet.{0} Nat S) L))
```

### GenLimit.Angluin.ConditionFour

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:60`; definition.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F =>
  ∃ inclusion,
    And
      (@Computable₂.{0, 0, 0} Nat Nat Bool (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Primcodable.bool inclusion)
      (∀ (i j : Nat),
        Iff (@Eq.{1} Bool (inclusion i j) Bool.true)
          (@HasSubset.Subset.{0} (GenLimit.Generic.Language.{0} Nat) (@Set.instHasSubset.{0} Nat) (F.language i)
            (F.language j)))
```

### GenLimit.Angluin.IsTellTale

`GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:39`; definition.

```lean
{α : Type u_1} → GenLimit.Generic.LanguageFamily.{u_1} α → Nat → Finset.{u_1} α → Prop
```

Definition value:

```lean
fun {α} C i T =>
  And (@HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) (@Finset.toSet.{u_1} α T) (C i))
    (∀ (j : Nat),
      @HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) (@Finset.toSet.{u_1} α T) (C j) →
        @HasSubset.Subset.{u_1} (GenLimit.Generic.Language.{u_1} α) (@Set.instHasSubset.{u_1} α) (C j) (C i) →
          @HasSubset.Subset.{u_1} (GenLimit.Generic.Language.{u_1} α) (@Set.instHasSubset.{u_1} α) (C i) (C j))
```

### GenLimit.Angluin.TheoremOneStatement

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:73`; definition.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F => Iff (GenLimit.Angluin.EffectiveInferrable F) (GenLimit.Angluin.ConditionOne F)
```

### GenLimit.Angluin.CorollaryOneStatement

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:78`; definition.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F => GenLimit.Angluin.EffectiveInferrable F → @GenLimit.Angluin.ConditionTwo.{0} Nat F.language
```

### GenLimit.Angluin.CorollaryTwoStatement

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:82`; definition.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F => GenLimit.Angluin.ConditionThree F.language → GenLimit.Angluin.EffectiveInferrable F
```

### GenLimit.Angluin.CorollaryThreeStatement

`GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:87`; definition.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F =>
  @GenLimit.Angluin.ConditionTwo.{0} Nat F.language →
    GenLimit.Angluin.ConditionFour F → GenLimit.Angluin.EffectiveInferrable F
```
