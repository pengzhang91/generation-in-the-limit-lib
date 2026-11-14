# P00A Stage 1 — paper-withheld Lean reconstruction

This report reconstructs the supplied Lean interface only. All eight opaque slots are recorded: four have no registered Lean endpoint; the other four link five target declarations. No source claim, intended source algorithm, or source correspondence is inferred. Names and frozen module/line locations below are locators only.

## Access, provenance, and input census

The only mathematical input directory was `P00A/stage1/` in package `CLAIMS405_LE20_2026-11-13_d294766`. No files under sources, owner, stage2, stage3-context, registry, PaperMap, prior audits, raw source comments, or raw proof bodies were read. No network lookup, compilation, repository build, Git mutation, or library change was performed. The only output writes are this report, `stage1-claims.json`, and `stage1-run.json` in the sibling results directory.

Requested configuration: `gpt-6.1-sol`, reasoning `xhigh`, fresh Stage 1 worker context. These are the assigned/requested settings, not an independently measured backend identity. Backend model/revision, actual reasoning configuration, and backend context-reset guarantees are unavailable. The visible worker context contains the Stage 1 task plus platform, working-agreement, and environment instructions; no prior source comparison or source-specific audit content was consulted. No subagents were spawned by this worker.

`declarations.jsonl` has **34 recursive declaration records, including the five targets**, hence **29 non-target dependency records**. This is not 34 additional dependencies. All 34 records exactly match their records in the native census. The native census has 569 records: 187 definitions, 367 theorems, five inductives, five constructors, and five recursors, across 31 listed modules. It is supporting code-only evidence; parsing its metadata and selecting definitions does not constitute individual helper or proof review. Thirty-nine additional algorithm/structural definition bodies and six supporting theorem types were inspected. No theorem proof value is present in either supplied JSONL file.

All ten entries in the supplied `SHA256SUMS` matched fresh SHA-256 calculations. The manifest itself was separately hashed. The source-snapshot hash reported by `snapshot.json` is `befc88a67a9c004e5f3858848eef24b5aad80e157ec5e1d52f73fe42b8073d37`; no underlying repository snapshot was read or independently reconstructed.

| Actual input read | Bytes | SHA-256 |
|---|---:|---|
| `START_HERE.md` | 217 | `52dbb6f80b47a22d94f222fd499cc75c3e793e710b44d74dd69922866c1c02d7` |
| `PROMPT.md` | 3356 | `c63aad9d119a37687071a9dd61f3139f0f318647c5237a6cfd05e4ecd3e38de3` |
| `claim-slots.json` | 1421 | `93481f3efa011f2c7edffe875960222f162236ddc8070c48646ecf13aa34c057` |
| `01-target-statements.md` | 1513 | `76a7705e0de8b302cd437f98331fde7df5c0021701bab659c046ac1b1efffbf6` |
| `02-definition-dependencies.md` | 11588 | `0fde81b361ab622184a6099fb7e109060bc264bc111efce0f4a0c060292a4d21` |
| `external-boundary.txt` | 515 | `e3cbb360dda98b3e1c2b438d46955f2b6a63be9e0985c738a2707396400f7cdb` |
| `targets.txt` | 177 | `16205c3bbe619999ec664e9e0829942c9eba569522b8309eb739aa80e4763833` |
| `snapshot.json` | 1938 | `f297e62fdab3992cb741f6739d14e919c85a9a783c82f72fd7710fdfed278452` |
| `SHA256SUMS` | 854 | `22d7a63c46bbc5ab6fd04908992bb7997b811f8ddda1a3740df420be0981a492` |
| `declarations.jsonl` | 21802 | `8a7b0e04a23bcf1d0ac6bb8dfb09fb5cfcf34cd374ee0ed31bdff3cee833cdf3` |
| `native-declaration-census.jsonl` | 532427 | `0c8270eac1c5e679a1e1c3678d88a8c732f822d3a83184ea481ca0ee12987fb0` |

## Definition glossary and common quantifier expansion

Write `L_i=C i`, `prefix(s,t)=[s(0),…,s(t−1)]`, and `E_i={x | ∃ stage, emit i stage=some x}`. These are notation for the definitions below, not extra assumptions.

`Language α = Set α`; `LanguageFamily α = Nat → Set α`; `Stream α = Nat → α`. `Presents s L` means **range(s)=L**, not merely that every datum lies in L. A presentation is an infinite total stream; arbitrary repetitions, ordering, and noncomputable streams are included. No pause symbol occurs. An empty language has no such presentation. A finite nonempty language can be presented by repetitions. An exhausted finite target does not terminate the stream or restrict the correctness quantifier.

`Learner Info Name = List Info → Name`. `SemanticIdentifier α` specializes this to `List α → Nat`; `EffectiveIdentifier` specializes α to Nat. The learner takes the full ordered history, including repetitions, and always returns one natural-number hypothesis index. There is no optional hypothesis, generated point, set-valued support, distribution, loss, full-support law, or randomized procedure in these target types.

Define `ID(M,C)` as the following exact expansion of `SemanticallyIdentifies`:

```text
∀ z : Nat, ∀ s : Nat → α,
  range(s)=C z →
  ∃ k : Nat, C k=C z ∧
    ∃ N : Nat, ∀ t : Nat, N≤t → M(prefix(s,t))=k.
```

The existential k comes after both z and the entire s and may depend on them. N may additionally depend on k. The single M comes before all target indices and presentations. `textPrefix` is `List.map s (List.range t)`, so the first tested history at t=0 is empty. `IdentifiesInLimit` includes both denotation equality and `StabilizesTo`, whose conclusion is equality to the **same index** for every t≥N. This is eventual index stability, not only eventual correctness of changing equivalent indices, frequent success, or a limsup statement. The correct k need not equal the presented index z. No convergence rate, bound, probability, scale, or constant is supplied.

`SemanticallyInferrable C` is `∃ M, ID(M,C)` with no computability restriction. A family-specific arbitrary function can depend on C in its definition; its runtime type still takes only the history. `EffectiveInferrable F` is `∃ M, Computable M ∧ ID(M,F.language)`. This requires one total ordinary computable function of encoded finite natural-number lists, uniform across the fixed family's indices and streams. `∀ F, ∃ M` does not assert a single computable procedure taking an encoded family F to a program. F is not given an effective representation type for such a transformer.

`EffectiveIndexedFamily` is reconstructed from its constructor, not its name: it packages (i) `language : Nat → Set Nat`, (ii) `membership : Nat → Nat → Bool`, (iii) `∀ i x, membership i x=true ↔ x∈language i`, (iv) `Computable₂ membership`, and (v) `AllNonempty language`, meaning `∀ i, (language i).Nonempty`. Membership is jointly total computable in i,x. The language projection is `self.1`, and the separately inspected membership projection is `self.2`. This package imposes no injectivity or infinitude of members and no inclusion-decision field.

`IsTellTale C i T`, with `T : Finset α`, says:

```text
(T:Set α) ⊆ C i ∧
∀ j : Nat, (T:Set α) ⊆ C j → C j ⊆ C i → C i ⊆ C j.
```

Thus no proper sublanguage of C i represented in the family contains T. It need not distinguish C i from an incomparable language or a proper superlanguage. Empty T is permitted. `ConditionTwo C` is `∀ i, ∃ T : Finset α, IsTellTale C i T`. Its quantifier order is per-index existence, not a jointly computable selector. Equal languages at repeated indices cause no problem because the condition compares sets.

`IsEnumeratedTellTale C i E` is `E.Finite ∧ (E⊆C i ∧ ∀ j, E⊆C j → C j⊆C i → C i⊆C j)`. Unlike `IsTellTale`, it takes a set and includes a separate finiteness conjunct. `enumeratedSet emit i` aliases `Support.enumeratedSet`: x belongs iff some stage emits `some x`. `none` contributes nothing. `ConditionOne F` is `∃ emit, Computable₂ emit ∧ ∀ i, IsEnumeratedTellTale F.language i (E_i)`. A **single** total program serves all i and stages; each emitted set is finite, but repetitions and `none` can continue forever. The type supplies no known last emission, termination signal, finite-list output, computable cardinality bound, or uniform bound on tell-tale size.

`ConditionThree C` says `∀ S : Finset Nat, S.Nonempty → Set.Finite {L : Set Nat | L∈Set.range C ∧ (S:Set Nat)⊆L}`. It counts **distinct languages as sets**, not indices. It omits empty S, permits an infinite range, and gives no effective enumeration or computable numerical bound on these finite supersets.

`ConditionFour F` is `∃ inclusion : Nat → Nat → Bool, Computable₂ inclusion ∧ ∀ i j, inclusion i j=true ↔ F.language i⊆F.language j`. The one program decides inclusion for every pair. The Boolean equivalence specifies both outcomes. This is family-specific effective access, distinct from the membership access already carried by F.

The four statement wrappers are exact: `TheoremOneStatement F = (EffectiveInferrable F ↔ ConditionOne F)`; `CorollaryOneStatement F = (EffectiveInferrable F → ConditionTwo F.language)`; `CorollaryTwoStatement F = (ConditionThree F.language → EffectiveInferrable F)`; `CorollaryThreeStatement F = (ConditionTwo F.language → ConditionFour F → EffectiveInferrable F)`.

## Target dossier D1 — semantic equivalence (C04)

### `GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization:266`.

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] [Countable.{u_1 + 1} α] (C : GenLimit.Generic.LanguageFamily.{u_1} α),
  Iff (@GenLimit.Angluin.SemanticallyInferrable.{u_1} α C) (@GenLimit.Angluin.ConditionTwo.{u_1} α C)
```

For every universe level, every type α with explicit `Nonempty α` and `Countable α` instance hypotheses, and every C indexed by Nat, semantic identification is equivalent to per-index finite tell-tale existence. The complete quantifier skeleton is:

```text
∀ {α : Type u} [Nonempty α] [Countable α] (C : Nat → Set α),
  (∃ M : List α → Nat, ID(M,C)) ↔
  (∀ i : Nat, ∃ T_i : Finset α,
    T_i⊆C i ∧ ∀ j, T_i⊆C j → C j⊆C i → C i⊆C j).
```

`ID` expands exactly as above. The identifier is chosen for the whole family; a tell-tale may depend on C and i; it is fixed before the competing j is considered. Countability is a semantic typeclass hypothesis, not a supplied computable alphabet encoding, membership oracle, or algorithm. Neither C nor M is required to be computable. The runtime learner receives positive history only. The inspected semantic construction nevertheless makes classical decisions about C and classically chooses tell-tales, so this target cannot be read as an ordinary effective learner theorem.

No `AllNonempty C` hypothesis appears. Empty C i has no presentation, so the corresponding identification obligation is vacuous. Its tell-tale may be empty: the competing C j⊆C i premise forces C j empty, making the conclusion automatic. Repeated indices may denote the same set and the stabilized index may be any such name. Finite nonempty members and singleton alphabets are permitted. α itself is not permitted to be empty. No timing or computability claim is hidden in the biconditional.

Named definitions inspected: `chosenTellTale` uses `Classical.choose` on each tell-tale existence proof; `constantTellTaleApproximation` ignores its stage argument. The target type itself does not name that choice or `semanticLearner` as its witness. The no-proof-body boundary prevents identifying the witness chosen by the proof from the type alone.

## Target dossier D2 — effective equivalence (C04)

### `GenLimit.Angluin.theoremOne`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:582`.

```lean
∀ (F : GenLimit.Angluin.EffectiveIndexedFamily), GenLimit.Angluin.TheoremOneStatement F
```

For every F carrying exactly the membership and nonemptiness fields reconstructed above, the following propositions are equivalent:

```text
∀ F,
  (∃ M : List Nat → Nat, Computable M ∧ ID(M,F.language)) ↔
  (∃ emit : Nat → Nat → Option Nat,
    Computable₂ emit ∧
    ∀ i, E_i.Finite ∧
      (E_i⊆F.language i ∧
        ∀ j, E_i⊆F.language j →
          F.language j⊆F.language i → F.language i⊆F.language j)).
```

No conjunct is omitted: both computability requirements, per-index set finiteness, target containment, and both competing-language subset premises and resulting inclusion are essential. M and emit may depend on F and the respective implication hypothesis. A single chosen M is uniform over target indices and histories; a single chosen emit is uniform over both i and stage. The theorem does not assert one program uniform in arbitrary F, a numerical code extractor, or a computable complete finite tell-tale selector.

Every F member is nonempty by the constructor, so empty targets are excluded here. Equal languages at different indices are allowed, and both tell-tales and emitted sets may be empty. Emission is a stage-indexed total function, not an interactive enumerator with a stopping certificate. Finiteness of the **set of outputs** allows infinitely many repeated emissions. All positive presentations, including noncomputable ones and arbitrarily late first occurrences, remain in the conclusion. Final correctness is eventual stability of an index denoting the target, not point generation or novelty.

The definitions of `effectiveLearner` and `lockingEmitter` were inspected to expose concrete finite access and update rules (below). The target only states existence in each direction; no target type identifies these named functions as the proof's selected witnesses. Their proof correctness is outside this reconstruction.

## Target dossier D3 — finite-superset antecedent (C05)

### `GenLimit.Angluin.corollaryTwo`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:609`.

```lean
∀ (F : GenLimit.Angluin.EffectiveIndexedFamily), GenLimit.Angluin.CorollaryTwoStatement F
```

The exact expanded implication is:

```text
∀ F : EffectiveIndexedFamily,
  (∀ S : Finset Nat, S.Nonempty →
    Set.Finite {L : Set Nat | L∈range(F.language) ∧ (S:Set Nat)⊆L}) →
  ∃ M : List Nat → Nat, Computable M ∧ ID(M,F.language).
```

The finiteness condition is semantic: for each nonempty finite S, the indicated set of distinct language sets is finite. It does not enumerate those sets, bound their number, make inclusion decidable, or require finitely many indices. Repeated indices are ignored by `Set.range`. The empty finite set imposes no constraint, so the entire language range need not be finite. Nonemptiness and computable membership of every member are already supplied by F; there is no explicit `ConditionFour` hypothesis and no computable tell-tale antecedent.

M may depend on F and the hypothesis, but must serve all z and presentations as in `ID`. The final index and threshold occur after z and the entire presentation, and have no rate or uniform bound. Finite members are presented forever by repetition; no exhaustion event appears. The named `conditionThreeEmitter` was inspected, including its bounded rather than global inclusion tests. The target does not name it as the existential witness and no proof step was certified.

## Target dossier D4 — necessary finite tell-tales (C07)

### `GenLimit.Angluin.corollaryOne`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:598`.

```lean
∀ (F : GenLimit.Angluin.EffectiveIndexedFamily), GenLimit.Angluin.CorollaryOneStatement F
```

The exact expanded implication is:

```text
∀ F : EffectiveIndexedFamily,
  (∃ M : List Nat → Nat, Computable M ∧ ID(M,F.language)) →
  ∀ i : Nat, ∃ T_i : Finset Nat,
    T_i⊆F.language i ∧
    ∀ j, T_i⊆F.language j →
      F.language j⊆F.language i → F.language i⊆F.language j.
```

F includes all-member nonemptiness and jointly computable exact membership. The hypothesis's one total computable identifier serves the whole family; `ID` includes denotation equality and eventual stability of one hypothesis index. The conclusion is only a semantic finite tell-tale for each i. T_i may depend on the family and the hypothesis/witness; T_i is fixed before j. Neither a uniform computable selector i↦T_i, an output encoding of T_i, nor a known completion stage occurs. This declaration is a one-way necessity statement; it has no converse in its type.

Duplicate names, finite targets with repetitions, and empty tell-tales are permitted. Empty target languages are excluded by F. No support/loss/distribution interpretation is present. The locking-history and emitter definitions inspected as supporting evidence do not add an algorithmic conclusion to this target.

## Target dossier D5 — tell-tales plus inclusion decision (C08)

### `GenLimit.Angluin.corollaryThree`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:327`.

```lean
∀ (F : GenLimit.Angluin.EffectiveIndexedFamily), GenLimit.Angluin.CorollaryThreeStatement F
```

Let L_i=F.language i. The complete quantifier skeleton is:

```text
∀ F : EffectiveIndexedFamily,
  (∀ i, ∃ T_i : Finset Nat,
    T_i⊆L_i ∧ ∀ j, T_i⊆L_j → L_j⊆L_i → L_i⊆L_j) →
  (∃ inclusion : Nat → Nat → Bool,
    Computable₂ inclusion ∧
    ∀ i j, inclusion i j=true ↔ L_i⊆L_j) →
  ∃ M : List Nat → Nat, Computable M ∧ ID(M,F.language).
```

The first antecedent does not require computable access to the tell-tales; the second supplies one exact total computable inclusion function uniform in i,j. Membership is separately and already computable from F. The conclusion is one family-specific ordinary computable identifier, with no noncomputable oracle in its `Computable M` assertion. The named construction parameterizes an emitter by the supplied inclusion function, but the target gives no representation of F and no uniform code transformer on families or proofs. The existential witness M may depend on F and both hypotheses; each ID witness k,N may depend on the entire presentation.

The usual edge cases persist: duplicate language names are allowed; an empty tell-tale can suffice when there are no proper included family members; empty target languages are excluded by F; finite targets continue through repetitions. No effective convergence threshold, test for a tell-tale's completion, or numerical bound is present. The inspected emitter is parameterized by the inclusion function and outputs boundedly checked least differences, rather than assuming a bare unspecified inclusion oracle. Its proof of finiteness or learning correctness was not audited.

## Named algorithm definitions and access boundaries

These definitions are additional census evidence. Exact types and definition values are reproduced in Appendix B. The target types do not name any of these witnesses; the six supporting theorem **types** reproduced in Appendix C show related assertions without exposing or certifying their proof bodies.

### Semantic finite-history rule

`historySample xs` is `xs.toFinset`, using classical equality. An `IsTellTaleApproximation C A` is the conjunction of monotonicity `∀ i n m, n≤m → A i n⊆A i m` and `∀ i, ∃ T, IsTellTale C i T ∧ ∃ N, ∀ n≥N, A i n=T`. This second conjunct includes both tell-tale correctness and eventual **exact** equality of finite sets. The supplied constant approximation uses a classically chosen tell-tale at every stage.

For n=xs.length, `StageEligible C A xs i` means `i≤n ∧ A i n⊆historySample xs ∧ (historySample xs:Set α)⊆C i`. `semanticLearner` returns the least eligible i using classical predicate decisions and `Nat.find` if one exists, and 0 otherwise. Its information access includes arbitrary C membership and classical tell-tale choices captured in C,A, in addition to the actual history. It has no explicit persistent state: each call recomputes from the finite list. This is a semantic definition; no computability assertion is attached to it by its type.

### Ordinary finite checks and the effective learner

`Support.boundedAll p a n` starts at true and successively conjoins `p a k` for k<n. `Support.firstTrue p a n` starts at none and scans k<n, retaining the first `some k` thereafter. `Support.listContains` decides natural-number list membership. The corresponding Angluin names are aliases. These rules use finite recursion, not unbounded oracle decisions.

`Support.stageContents emit i n` collects the distinct `some` values emitted at stages <n by filtering `List.range n` and converting to a finset; the Angluin name is an alias. For n=xs.length, `observedCheck F xs i` checks every actual list entry against `F.membership i`; its `getD` default 0 is never needed at a checked index because the bound is n. `emissionAccepted` treats none as true and tests whether a some-value is in xs. `emissionCheck` conjoins these tests for stages <n. `effectiveStageEligible` is the conjunction of observedCheck and emissionCheck; it does not itself test i≤n. `effectiveLearner F emit xs` calls firstTrue with bound n+1, so it searches i≤n, and returns its first success or 0 if none.

Each call uses only the current finite history, F's computable membership procedure, and emit on finitely many (i,stage) pairs. There is no separate mutable state, future stream access, target-index argument, or stopping oracle. On the empty history both bounded conjunctions are true and index 0 is returned. On other histories the fallback may be an incorrect transient hypothesis. Total computability of emit is necessary for the supporting computability assertion; finiteness and tell-tale properties are further semantic correctness hypotheses. The type of `effectiveLearner_computable` asserts computability when emit is computable, and `effectiveLearner_eq_semanticLearner` asserts equality on lists of the given `List.ofFn` form. Their proofs were not inspected.

### Necessity-side finite-history enumeration

`decodedHistory code` decodes a list of Nat and substitutes [] when decoding fails. `historyInCheck` is the observed-membership test. `extensionAccepted F M (i,h) code` is true for a decoded extension outside L_i; for an extension entirely in L_i it requires `M(h++extension)=M h`. A failed extension decoding becomes [], whose appended-history equality is automatically true.

`stabilizationCandidateCheck F M (i,s) code` rejects a failed candidate decoding. A decoded history h is accepted iff it lies in L_i and every extension code <s passes extensionAccepted. `provisionalHistory F M i s` scans candidate codes <s+1, keeps the least accepted one, and decodes it, returning none if no candidate passes. At emitter stage `unpair(stage)=(s,k)`, `lockingEmitter` returns the k-th element of that provisional history, or none if the history or element is absent. All queries to a computable M and to membership are finite at each stage. The search tests only bounded extension codes at a given s; it does not decide the universal locking property at runtime.

`SyntacticallyStabilizing M L h` means h lies in L and `∀ extension within L, M(h++extension)=M h`. It does not itself assert that the frozen hypothesis denotes L. `IsLockingSequence M L h j` similarly includes history containment and equality to j on every permitted tail; taking the empty tail forces `M h=j`. These predicates are semantic specifications, not executable locking tests. No proof that the emitted set is finite, is a tell-tale, or reconstructs a source algorithm was audited here.

### Inclusion-decision emitter

`leastDifferenceCheck F (i,j) x` tests x∈L_i\L_j and that no y<x lies in that difference, using finite membership checks. `conditionFourEmitter F inclusion i stage` decodes `(j,x)=Nat.unpair stage`, and emits some x exactly when `inclusion j i=true`, `inclusion i j=false`, and leastDifferenceCheck holds; otherwise it emits none. With a correct inclusion function, it enumerates least missing members of L_i for proper included languages L_j. Repeated indices may repeat the same value. If there is no proper included member the enumerated set can be empty. The semantic tell-tale/finiteness assertion additionally assumes ConditionTwo in its supporting theorem type. At runtime the emitter takes the inclusion function as a parameter; under ConditionFour this parameter is total computable. The target does not require the completed tell-tales as runtime input.

### Finite-superset emitter

`noEarlierMemberCheck F i x` checks no y<x is in L_i; `leastMemberCheck` also checks x∈L_i. `prefixSubsetCheck F (j,i) m` checks `∀ y<m, y∈L_j → y∈L_i`. `conditionThreeEmitter F i stage` decodes a tuple `(t,(j,(m,x)))` with nested Nat.unpair. It emits some x iff either x is the least member of L_i, or all of the following hold: t is the least member of L_i; t∈L_j; prefixSubsetCheck(j,i,m) succeeds; x<m; and x is the least element of L_i\L_j. Otherwise it emits none. These are finite Boolean checks from membership; there is no full inclusion test. The finiteness/tell-tale assertion in its supporting theorem type assumes ConditionThree.

`firstDifference target candidate` is separately defined using classical existence decisions and Nat.find, returning the least target-minus-candidate element when one exists and 0 otherwise. It is not called by conditionThreeEmitter: inspecting that exact emitter dependency list prevents mistaking a semantic minimum used elsewhere for a runtime oracle. No emitter stopping rule, known bound on output distinctness, or certified learner proof was supplied by these definitions.

## Exhaustive slot and target coverage

| Slot | Supplied endpoints | Dossier/result |
|---|---|---|
| C01 | none | No supplied reconstruction target; no source inference. |
| C02 | none | No supplied reconstruction target; no source inference. |
| C03 | none | No supplied reconstruction target; no source inference. |
| C04 | `semanticallyInferrable_iff_conditionTwo`; `theoremOne` | D1 and D2, both reconstructed independently. |
| C05 | `corollaryTwo` | D3. |
| C06 | none | No supplied reconstruction target; no source inference. |
| C07 | `corollaryOne` | D4. |
| C08 | `corollaryThree` | D5. |

The full identifiers are reproduced in each dossier and exactly in `stage1-claims.json`. Every linked target is present in the frozen environment. No slot is merged away because another target shares definitions; each has its own JSON object. Empty endpoint arrays are an explicit absence of a reconstruction target, not a finding that the corresponding source claim is false, missing in the source, or adequately covered elsewhere.

## Limitations and external boundary

Standard Lean and Mathlib meanings are trusted, as instructed by `external-boundary.txt`: in particular total `Computable`/`Computable₂` under the displayed Nat/List/Option/Bool Primcodable encodings, set and finset operations, countability, and equality. Additional named algorithm inspection also trusts standard classical choice/decisions, Nat.find, Nat pairing/unpairing, list indexing/decoding, finite recursion, and Boolean operations. No recursive Mathlib audit or external lookup was performed. No decisive unresolved nonstandard constant remained in the inspected target/algorithm definitions.

The package has suppressed embedded proof arguments (`⋯`) in definition displays. Those are export suppression, not observed `sorry` holes. Theorem proof values are absent by design. Consequently this report certifies neither proof-body correctness nor fresh compilation. It supplies no source correspondence, claim completeness relative to the withheld paper, independent snapshot certification, or human review. The 569-record census is not a blanket helper audit. No unsupported mathematical statement is assigned to C01/C02/C03/C06. The actual backend revision and actual effective context isolation are unobservable beyond the visible worker context and assigned request.

## Appendix A — exact recursive interface evidence

The five target types are quoted in D1–D5. The following table inventories **all 34 recursive records**; all 29 non-target types and available definition values follow. Constructor fields are included explicitly. This preserves precise binders and encodings in addition to the expanded prose.

| Exact identifier | Kind | Frozen module:line | Review location |
|---|---|---|---|
| `GenLimit.Angluin.AllNonempty` | definition | `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:35` | Appendix A exact type/value |
| `GenLimit.Angluin.ConditionFour` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:60` | Appendix A exact type/value |
| `GenLimit.Angluin.ConditionOne` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:49` | Appendix A exact type/value |
| `GenLimit.Angluin.ConditionThree` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:55` | Appendix A exact type/value |
| `GenLimit.Angluin.ConditionTwo` | definition | `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:52` | Appendix A exact type/value |
| `GenLimit.Angluin.CorollaryOneStatement` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:78` | Appendix A exact type/value |
| `GenLimit.Angluin.CorollaryThreeStatement` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:87` | Appendix A exact type/value |
| `GenLimit.Angluin.CorollaryTwoStatement` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:82` | Appendix A exact type/value |
| `GenLimit.Angluin.EffectiveIdentifier` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:27` | Appendix A exact type/value |
| `GenLimit.Angluin.EffectiveIndexedFamily` | inductive | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:18` | Appendix A exact type/value |
| `GenLimit.Angluin.EffectiveIndexedFamily.language` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:19` | Appendix A exact type/value |
| `GenLimit.Angluin.EffectiveIndexedFamily.mk` | constructor | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:18` | Appendix A exact type/value |
| `GenLimit.Angluin.EffectiveInferrable` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:33` | Appendix A exact type/value |
| `GenLimit.Angluin.IsEnumeratedTellTale` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:42` | Appendix A exact type/value |
| `GenLimit.Angluin.IsTellTale` | definition | `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:39` | Appendix A exact type/value |
| `GenLimit.Angluin.SemanticIdentifier` | definition | `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:18` | Appendix A exact type/value |
| `GenLimit.Angluin.SemanticallyIdentifies` | definition | `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:24` | Appendix A exact type/value |
| `GenLimit.Angluin.SemanticallyInferrable` | definition | `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:30` | Appendix A exact type/value |
| `GenLimit.Angluin.TheoremOneStatement` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:73` | Appendix A exact type/value |
| `GenLimit.Angluin.corollaryOne` | theorem | `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:598` | D1–D5 |
| `GenLimit.Angluin.corollaryThree` | theorem | `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:327` | D1–D5 |
| `GenLimit.Angluin.corollaryTwo` | theorem | `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:609` | D1–D5 |
| `GenLimit.Angluin.enumeratedSet` | definition | `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:38` | Appendix A exact type/value |
| `GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo` | theorem | `GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization:266` | D1–D5 |
| `GenLimit.Angluin.theoremOne` | theorem | `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:582` | D1–D5 |
| `GenLimit.Generic.Language` | definition | `GenLimit.Core.GenericGeneration:21` | Appendix A exact type/value |
| `GenLimit.Generic.LanguageFamily` | definition | `GenLimit.Core.GenericGeneration:28` | Appendix A exact type/value |
| `GenLimit.Generic.Presents` | definition | `GenLimit.Core.GenericGeneration:50` | Appendix A exact type/value |
| `GenLimit.Generic.Stream` | definition | `GenLimit.Core.GenericGeneration:31` | Appendix A exact type/value |
| `GenLimit.IdentifiesInLimit` | definition | `GenLimit.Core.Identification:53` | Appendix A exact type/value |
| `GenLimit.Learner` | definition | `GenLimit.Core.Identification:18` | Appendix A exact type/value |
| `GenLimit.StabilizesTo` | definition | `GenLimit.Core.Identification:47` | Appendix A exact type/value |
| `GenLimit.Support.enumeratedSet` | definition | `GenLimit.Support.FiniteEnumeration:15` | Appendix A exact type/value |
| `GenLimit.textPrefix` | definition | `GenLimit.Core.Text:16` | Appendix A exact type/value |

### `GenLimit.Angluin.AllNonempty`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:35`.

```lean
{α : Type u_1} → GenLimit.Generic.LanguageFamily.{u_1} α → Prop
```

Definition value:

```lean
fun {α} C => ∀ (i : Nat), @Set.Nonempty.{u_1} α (C i)
```

### `GenLimit.Angluin.ConditionFour`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:60`.

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

### `GenLimit.Angluin.ConditionOne`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:49`.

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

### `GenLimit.Angluin.ConditionThree`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:55`.

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

### `GenLimit.Angluin.ConditionTwo`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:52`.

```lean
{α : Type u_1} → GenLimit.Generic.LanguageFamily.{u_1} α → Prop
```

Definition value:

```lean
fun {α} C => ∀ (i : Nat), ∃ T, @GenLimit.Angluin.IsTellTale.{u_1} α C i T
```

### `GenLimit.Angluin.CorollaryOneStatement`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:78`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F => GenLimit.Angluin.EffectiveInferrable F → @GenLimit.Angluin.ConditionTwo.{0} Nat F.language
```

### `GenLimit.Angluin.CorollaryThreeStatement`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:87`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F =>
  @GenLimit.Angluin.ConditionTwo.{0} Nat F.language →
    GenLimit.Angluin.ConditionFour F → GenLimit.Angluin.EffectiveInferrable F
```

### `GenLimit.Angluin.CorollaryTwoStatement`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:82`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F => GenLimit.Angluin.ConditionThree F.language → GenLimit.Angluin.EffectiveInferrable F
```

### `GenLimit.Angluin.EffectiveIdentifier`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:27`.

```lean
Type
```

Definition value:

```lean
GenLimit.Angluin.SemanticIdentifier.{0} Nat
```

### `GenLimit.Angluin.EffectiveIndexedFamily`

Kind: inductive. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:18`.

```lean
Type
```

Constructors: `GenLimit.Angluin.EffectiveIndexedFamily.mk`.

### `GenLimit.Angluin.EffectiveIndexedFamily.language`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:19`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → GenLimit.Generic.LanguageFamily.{0} Nat
```

Definition value:

```lean
fun self => self.1
```

### `GenLimit.Angluin.EffectiveIndexedFamily.mk`

Kind: constructor. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:18`.

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

### `GenLimit.Angluin.EffectiveInferrable`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:33`.

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

### `GenLimit.Angluin.IsEnumeratedTellTale`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:42`.

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

### `GenLimit.Angluin.IsTellTale`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:39`.

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

### `GenLimit.Angluin.SemanticIdentifier`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:18`.

```lean
Type u_1 → Type (max 0 u_1)
```

Definition value:

```lean
fun α => GenLimit.Learner.{u_1, 0} α Nat
```

### `GenLimit.Angluin.SemanticallyIdentifies`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:24`.

```lean
{α : Type u_1} → GenLimit.Angluin.SemanticIdentifier.{u_1} α → GenLimit.Generic.LanguageFamily.{u_1} α → Prop
```

Definition value:

```lean
fun {α} M C =>
  ∀ (z : Nat) (stream : GenLimit.Generic.Stream.{u_1} α),
    @GenLimit.Generic.Presents.{u_1} α stream (C z) →
      @GenLimit.IdentifiesInLimit.{u_1, 0, u_1} α Nat (GenLimit.Generic.Language.{u_1} α) C M stream (C z)
```

### `GenLimit.Angluin.SemanticallyInferrable`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:30`.

```lean
{α : Type u_1} → GenLimit.Generic.LanguageFamily.{u_1} α → Prop
```

Definition value:

```lean
fun {α} C => ∃ M, @GenLimit.Angluin.SemanticallyIdentifies.{u_1} α M C
```

### `GenLimit.Angluin.TheoremOneStatement`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:73`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F => Iff (GenLimit.Angluin.EffectiveInferrable F) (GenLimit.Angluin.ConditionOne F)
```

### `GenLimit.Angluin.enumeratedSet`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:38`.

```lean
(Nat → Nat → Option.{0} Nat) → Nat → Set.{0} Nat
```

Definition value:

```lean
GenLimit.Support.enumeratedSet
```

### `GenLimit.Generic.Language`

Kind: definition. Frozen source locator: `GenLimit.Core.GenericGeneration:21`.

```lean
Type u_1 → Type u_1
```

Definition value:

```lean
fun α => Set.{u_1} α
```

### `GenLimit.Generic.LanguageFamily`

Kind: definition. Frozen source locator: `GenLimit.Core.GenericGeneration:28`.

```lean
Type u_1 → Type u_1
```

Definition value:

```lean
fun α => Nat → GenLimit.Generic.Language.{u_1} α
```

### `GenLimit.Generic.Presents`

Kind: definition. Frozen source locator: `GenLimit.Core.GenericGeneration:50`.

```lean
{α : Type u_1} → GenLimit.Generic.Stream.{u_1} α → GenLimit.Generic.Language.{u_1} α → Prop
```

Definition value:

```lean
fun {α} stream L => @Eq.{u_1 + 1} (Set.{u_1} α) (@Set.range.{u_1, 1} α Nat stream) L
```

### `GenLimit.Generic.Stream`

Kind: definition. Frozen source locator: `GenLimit.Core.GenericGeneration:31`.

```lean
Type u_1 → Type u_1
```

Definition value:

```lean
fun α => Nat → α
```

### `GenLimit.IdentifiesInLimit`

Kind: definition. Frozen source locator: `GenLimit.Core.Identification:53`.

```lean
{Info : Type uInfo} →
  {Name : Type uName} →
    {Object : Type uObject} → (Name → Object) → GenLimit.Learner.{uInfo, uName} Info Name → (Nat → Info) → Object → Prop
```

Definition value:

```lean
fun {Info} {Name} {Object} denote learner stream target =>
  ∃ name,
    And (@Eq.{uObject + 1} Object (denote name) target)
      (@GenLimit.StabilizesTo.{uName} Name (fun t => learner (@GenLimit.textPrefix.{uInfo} Info stream t)) name)
```

### `GenLimit.Learner`

Kind: definition. Frozen source locator: `GenLimit.Core.Identification:18`.

```lean
Type uInfo → Type uName → Type (max uName uInfo)
```

Definition value:

```lean
fun Info Name => List.{uInfo} Info → Name
```

### `GenLimit.StabilizesTo`

Kind: definition. Frozen source locator: `GenLimit.Core.Identification:47`.

```lean
{Name : Type uName} → (Nat → Name) → Name → Prop
```

Definition value:

```lean
fun {Name} guess name => ∃ T, ∀ (t : Nat), @LE.le.{0} Nat instLENat T t → @Eq.{uName + 1} Name (guess t) name
```

### `GenLimit.Support.enumeratedSet`

Kind: definition. Frozen source locator: `GenLimit.Support.FiniteEnumeration:15`.

```lean
(Nat → Nat → Option.{0} Nat) → Nat → Set.{0} Nat
```

Definition value:

```lean
fun emit i => @setOf.{0} Nat fun x => ∃ stage, @Eq.{1} (Option.{0} Nat) (emit i stage) (@Option.some.{0} Nat x)
```

### `GenLimit.textPrefix`

Kind: definition. Frozen source locator: `GenLimit.Core.Text:16`.

```lean
{α : Type u_1} → (Nat → α) → Nat → List.{u_1} α
```

Definition value:

```lean
fun {α} stream t => @List.map.{0, u_1} Nat α stream (List.range t)
```

## Appendix B — exact additional algorithm definitions

Only the following 39 additional definition bodies were individually inspected. Generated match helpers have no source-line number in the export; their anchors explicitly retain `None`. No theorem proof bodies are included.

### `GenLimit.Angluin.IsTellTaleApproximation`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:56`.

```lean
{α : Type u_1} → GenLimit.Generic.LanguageFamily.{u_1} α → (Nat → Nat → Finset.{u_1} α) → Prop
```

Definition value:

```lean
fun {α} C A =>
  And
    (∀ (i n m : Nat),
      @LE.le.{0} Nat instLENat n m →
        @HasSubset.Subset.{u_1} (Finset.{u_1} α) (@Finset.instHasSubset.{u_1} α) (A i n) (A i m))
    (∀ (i : Nat),
      ∃ T,
        And (@GenLimit.Angluin.IsTellTale.{u_1} α C i T)
          (∃ N, ∀ (n : Nat), @LE.le.{0} Nat instLENat N n → @Eq.{u_1 + 1} (Finset.{u_1} α) (A i n) T))
```

### `GenLimit.Angluin.StageEligible`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization:45`.

```lean
{α : Type u_1} → GenLimit.Generic.LanguageFamily.{u_1} α → (Nat → Nat → Finset.{u_1} α) → List.{u_1} α → Nat → Prop
```

Definition value:

```lean
fun {α} C A xs i =>
  And (@LE.le.{0} Nat instLENat i (@List.length.{u_1} α xs))
    (And
      (@HasSubset.Subset.{u_1} (Finset.{u_1} α) (@Finset.instHasSubset.{u_1} α) (A i (@List.length.{u_1} α xs))
        (@GenLimit.Angluin.historySample.{u_1} α xs))
      (@HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α)
        (@Finset.toSet.{u_1} α (@GenLimit.Angluin.historySample.{u_1} α xs)) (C i)))
```

### `GenLimit.Angluin.chosenTellTale`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization:225`.

```lean
{α : Type u_1} →
  (C : GenLimit.Generic.LanguageFamily.{u_1} α) → @GenLimit.Angluin.ConditionTwo.{u_1} α C → Nat → Finset.{u_1} α
```

Definition value:

```lean
fun {α} C h i => @Classical.choose.{u_1 + 1} (Finset.{u_1} α) (@GenLimit.Angluin.IsTellTale.{u_1} α C i) ⋯
```

### `GenLimit.Angluin.constantTellTaleApproximation`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization:238`.

```lean
{α : Type u_1} →
  (C : GenLimit.Generic.LanguageFamily.{u_1} α) → @GenLimit.Angluin.ConditionTwo.{u_1} α C → Nat → Nat → Finset.{u_1} α
```

Definition value:

```lean
fun {α} C h i x => @GenLimit.Angluin.chosenTellTale.{u_1} α C h i
```

### `GenLimit.Angluin.historySample`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization:31`.

```lean
{α : Type u_1} → List.{u_1} α → Finset.{u_1} α
```

Definition value:

```lean
fun {α} xs => @List.toFinset.{u_1} α (fun a b => Classical.propDecidable (@Eq.{u_1 + 1} α a b)) xs
```

### `GenLimit.Angluin.semanticLearner`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization:54`.

```lean
{α : Type u_1} →
  GenLimit.Generic.LanguageFamily.{u_1} α → (Nat → Nat → Finset.{u_1} α) → GenLimit.Angluin.SemanticIdentifier.{u_1} α
```

Definition value:

```lean
fun {α} C A xs =>
  @dite.{1} Nat (∃ i, @GenLimit.Angluin.StageEligible.{u_1} α C A xs i)
    (Classical.propDecidable (∃ i, @GenLimit.Angluin.StageEligible.{u_1} α C A xs i))
    (fun h =>
      @Nat.find (@GenLimit.Angluin.StageEligible.{u_1} α C A xs)
        (fun a => Classical.propDecidable (@GenLimit.Angluin.StageEligible.{u_1} α C A xs a)) h)
    fun h => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))
```

### `GenLimit.Angluin.EffectiveIndexedFamily.membership`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:20`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Nat → Nat → Bool
```

Definition value:

```lean
fun self => self.2
```

### `GenLimit.Angluin.stageContents`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:17`.

```lean
(Nat → Nat → Option.{0} Nat) → Nat → Nat → Finset.{0} Nat
```

Definition value:

```lean
GenLimit.Support.stageContents
```

### `GenLimit.Angluin.boundedAll`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:116`.

```lean
{α : Type u_1} → (α → Nat → Bool) → α → Nat → Bool
```

Definition value:

```lean
fun {α} => @GenLimit.Support.boundedAll.{u_1} α
```

### `GenLimit.Angluin.listContains`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:129`.

```lean
List.{0} Nat → Nat → Bool
```

Definition value:

```lean
GenLimit.Support.listContains
```

### `GenLimit.Angluin.firstTrue`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:139`.

```lean
{α : Type u_1} → (α → Nat → Bool) → α → Nat → Option.{0} Nat
```

Definition value:

```lean
fun {α} => @GenLimit.Support.firstTrue.{u_1} α
```

### `GenLimit.Angluin.observedCheck`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:180`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → List.{0} Nat → Nat → Bool
```

Definition value:

```lean
fun F xs i =>
  @GenLimit.Angluin.boundedAll.{0} (Prod.{0, 0} Nat (List.{0} Nat))
    (fun p k =>
      F.membership (@Prod.fst.{0, 0} Nat (List.{0} Nat) p)
        (@List.getD.{0} Nat (@Prod.snd.{0, 0} Nat (List.{0} Nat) p) k
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@Prod.mk.{0, 0} Nat (List.{0} Nat) i xs) (@List.length.{0} Nat xs)
```

### `GenLimit.Angluin.emissionAccepted`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:203`.

```lean
(Nat → Nat → Option.{0} Nat) → Prod.{0, 0} Nat (List.{0} Nat) → Nat → Bool
```

Definition value:

```lean
fun emit p stage =>
  GenLimit.Angluin.emissionAccepted.match_1.{1} (fun x => Bool) (emit (@Prod.fst.{0, 0} Nat (List.{0} Nat) p) stage)
    (fun _ => Bool.true) fun x => GenLimit.Angluin.listContains (@Prod.snd.{0, 0} Nat (List.{0} Nat) p) x
```

### `GenLimit.Angluin.emissionCheck`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:231`.

```lean
(Nat → Nat → Option.{0} Nat) → List.{0} Nat → Nat → Bool
```

Definition value:

```lean
fun emit xs i =>
  @GenLimit.Angluin.boundedAll.{0} (Prod.{0, 0} Nat (List.{0} Nat)) (GenLimit.Angluin.emissionAccepted emit)
    (@Prod.mk.{0, 0} Nat (List.{0} Nat) i xs) (@List.length.{0} Nat xs)
```

### `GenLimit.Angluin.effectiveStageEligible`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:244`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → (Nat → Nat → Option.{0} Nat) → List.{0} Nat → Nat → Bool
```

Definition value:

```lean
fun F emit xs i => (GenLimit.Angluin.observedCheck F xs i).and (GenLimit.Angluin.emissionCheck emit xs i)
```

### `GenLimit.Angluin.effectiveLearner`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:338`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → (Nat → Nat → Option.{0} Nat) → GenLimit.Angluin.EffectiveIdentifier
```

Definition value:

```lean
fun F emit xs =>
  @Option.getD.{0} Nat
    (@GenLimit.Angluin.firstTrue.{0} (List.{0} Nat) (GenLimit.Angluin.effectiveStageEligible F emit) xs
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Nat xs)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```

### `GenLimit.Support.stageContents`

Kind: definition. Frozen source locator: `GenLimit.Support.FiniteEnumeration:20`.

```lean
(Nat → Nat → Option.{0} Nat) → Nat → Nat → Finset.{0} Nat
```

Definition value:

```lean
fun emit i n => @List.toFinset.{0} Nat instDecidableEqNat (@List.filterMap.{0, 0} Nat Nat (emit i) (List.range n))
```

### `GenLimit.Support.boundedAll`

Kind: definition. Frozen source locator: `GenLimit.Support.ComputableSearch:13`.

```lean
{alpha : Type u_1} → (alpha → Nat → Bool) → alpha → Nat → Bool
```

Definition value:

```lean
fun {alpha} p a n => @Nat.rec.{1} (fun x => Bool) Bool.true (fun k previous => previous.and (p a k)) n
```

### `GenLimit.Support.listContains`

Kind: definition. Frozen source locator: `GenLimit.Support.ComputableSearch:48`.

```lean
List.{0} Nat → Nat → Bool
```

Definition value:

```lean
fun xs x =>
  @Decidable.decide (@Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) xs x)
    (@List.instDecidableMemOfLawfulBEq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat) Nat.instLawfulBEq x
      xs)
```

### `GenLimit.Support.firstTrue`

Kind: definition. Frozen source locator: `GenLimit.Support.ComputableSearch:67`.

```lean
{alpha : Type u_1} → (alpha → Nat → Bool) → alpha → Nat → Option.{0} Nat
```

Definition value:

```lean
fun {alpha} p a n =>
  @Nat.rec.{1} (fun x => Option.{0} Nat) (@Option.none.{0} Nat)
    (fun k previous =>
      GenLimit.Support.firstTrue.match_1.{1} (fun previous => Option.{0} Nat) previous (fun i => @Option.some.{0} Nat i)
        fun _ =>
        @ite.{1} (Option.{0} Nat) (@Eq.{1} Bool (p a k) Bool.true) (instDecidableEqBool (p a k) Bool.true)
          (@Option.some.{0} Nat k) (@Option.none.{0} Nat))
    n
```

### `GenLimit.Angluin.emissionAccepted.match_1`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:None`.

```lean
(motive : Option.{0} Nat → Sort u_1) →
  (x : Option.{0} Nat) →
    (Unit → motive (@Option.none.{0} Nat)) → ((x : Nat) → motive (@Option.some.{0} Nat x)) → motive x
```

Definition value:

```lean
fun motive x h_1 h_2 => @Option.casesOn.{u_1, 0} Nat (fun x => motive x) x (h_1 Unit.unit) fun val => h_2 val
```

### `GenLimit.Support.firstTrue.match_1`

Kind: definition. Frozen source locator: `GenLimit.Support.ComputableSearch:None`.

```lean
(motive : Option.{0} Nat → Sort u_1) →
  (previous : Option.{0} Nat) →
    ((i : Nat) → motive (@Option.some.{0} Nat i)) → (Unit → motive (@Option.none.{0} Nat)) → motive previous
```

Definition value:

```lean
fun motive previous h_1 h_2 =>
  @Option.casesOn.{u_1, 0} Nat (fun x => motive x) previous (h_2 Unit.unit) fun val => h_1 val
```

### `GenLimit.Angluin.noEarlierMemberCheck`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:24`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Nat → Nat → Bool
```

Definition value:

```lean
fun F i x => @GenLimit.Angluin.boundedAll.{0} Nat (fun i y => (F.membership i y).not) i x
```

### `GenLimit.Angluin.leastMemberCheck`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:29`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Nat → Nat → Bool
```

Definition value:

```lean
fun F i x => (F.membership i x).and (GenLimit.Angluin.noEarlierMemberCheck F i x)
```

### `GenLimit.Angluin.prefixSubsetCheck`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:34`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prod.{0, 0} Nat Nat → Nat → Bool
```

Definition value:

```lean
fun F p m =>
  @GenLimit.Angluin.boundedAll.{0} (Prod.{0, 0} Nat Nat)
    (fun p y => (F.membership (@Prod.fst.{0, 0} Nat Nat p) y).not.or (F.membership (@Prod.snd.{0, 0} Nat Nat p) y)) p m
```

### `GenLimit.Angluin.leastDifferenceCheck`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:41`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prod.{0, 0} Nat Nat → Nat → Bool
```

Definition value:

```lean
fun F p x =>
  ((F.membership (@Prod.fst.{0, 0} Nat Nat p) x).and (F.membership (@Prod.snd.{0, 0} Nat Nat p) x).not).and
    (@GenLimit.Angluin.boundedAll.{0} (Prod.{0, 0} Nat Nat)
      (fun p y =>
        ((F.membership (@Prod.fst.{0, 0} Nat Nat p) y).and (F.membership (@Prod.snd.{0, 0} Nat Nat p) y).not).not)
      p x)
```

### `GenLimit.Angluin.conditionFourEmitter`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:177`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → (Nat → Nat → Bool) → Nat → Nat → Option.{0} Nat
```

Definition value:

```lean
fun F inclusion i stage =>
  have jx := Nat.unpair stage;
  @ite.{1} (Option.{0} Nat)
    (@Eq.{1} Bool
      (((inclusion (@Prod.fst.{0, 0} Nat Nat jx) i).and (inclusion i (@Prod.fst.{0, 0} Nat Nat jx)).not).and
        (GenLimit.Angluin.leastDifferenceCheck F (@Prod.mk.{0, 0} Nat Nat i (@Prod.fst.{0, 0} Nat Nat jx))
          (@Prod.snd.{0, 0} Nat Nat jx)))
      Bool.true)
    (instDecidableEqBool
      (((inclusion (@Prod.fst.{0, 0} Nat Nat jx) i).and (inclusion i (@Prod.fst.{0, 0} Nat Nat jx)).not).and
        (GenLimit.Angluin.leastDifferenceCheck F (@Prod.mk.{0, 0} Nat Nat i (@Prod.fst.{0, 0} Nat Nat jx))
          (@Prod.snd.{0, 0} Nat Nat jx)))
      Bool.true)
    (@Option.some.{0} Nat (@Prod.snd.{0, 0} Nat Nat jx)) (@Option.none.{0} Nat)
```

### `GenLimit.Angluin.firstDifference`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:338`.

```lean
Set.{0} Nat → Set.{0} Nat → Nat
```

Definition value:

```lean
fun target candidate =>
  @dite.{1} Nat
    (∃ x, And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) target x) (x ∉ candidate))
    (Classical.propDecidable
      (∃ x, And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) target x) (x ∉ candidate)))
    (fun h =>
      @Nat.find
        (fun n => And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) target n) (n ∉ candidate))
        (fun a =>
          @instDecidableAnd (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) target a)
            (a ∉ candidate)
            (Classical.propDecidable (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) target a))
            (@instDecidableNot (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) candidate a)
              (Classical.propDecidable
                (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) candidate a))))
        h)
    fun h => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))
```

### `GenLimit.Angluin.conditionThreeEmitter`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:364`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Nat → Nat → Option.{0} Nat
```

Definition value:

```lean
fun F i stage =>
  have t := @Prod.fst.{0, 0} Nat Nat (Nat.unpair stage);
  have j := @Prod.fst.{0, 0} Nat Nat (Nat.unpair (@Prod.snd.{0, 0} Nat Nat (Nat.unpair stage)));
  have m :=
    @Prod.fst.{0, 0} Nat Nat
      (Nat.unpair (@Prod.snd.{0, 0} Nat Nat (Nat.unpair (@Prod.snd.{0, 0} Nat Nat (Nat.unpair stage)))));
  have x :=
    @Prod.snd.{0, 0} Nat Nat
      (Nat.unpair (@Prod.snd.{0, 0} Nat Nat (Nat.unpair (@Prod.snd.{0, 0} Nat Nat (Nat.unpair stage)))));
  @ite.{1} (Option.{0} Nat)
    (@Eq.{1} Bool
      ((GenLimit.Angluin.leastMemberCheck F i x).or
        (((((GenLimit.Angluin.leastMemberCheck F i t).and (F.membership j t)).and
                  (GenLimit.Angluin.prefixSubsetCheck F (@Prod.mk.{0, 0} Nat Nat j i) m)).and
              (@Decidable.decide (@LT.lt.{0} Nat instLTNat x m) (x.decLt m))).and
          (GenLimit.Angluin.leastDifferenceCheck F (@Prod.mk.{0, 0} Nat Nat i j) x)))
      Bool.true)
    (instDecidableEqBool
      ((GenLimit.Angluin.leastMemberCheck F i x).or
        (((((GenLimit.Angluin.leastMemberCheck F i t).and (F.membership j t)).and
                  (GenLimit.Angluin.prefixSubsetCheck F (@Prod.mk.{0, 0} Nat Nat j i) m)).and
              (@Decidable.decide (@LT.lt.{0} Nat instLTNat x m) (x.decLt m))).and
          (GenLimit.Angluin.leastDifferenceCheck F (@Prod.mk.{0, 0} Nat Nat i j) x)))
      Bool.true)
    (@Option.some.{0} Nat x) (@Option.none.{0} Nat)
```

### `GenLimit.Angluin.decodedHistory`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:29`.

```lean
Nat → List.{0} Nat
```

Definition value:

```lean
fun code =>
  @Option.getD.{0} (List.{0} Nat) (@Encodable.decode.{0} (List.{0} Nat) (@List.encodable.{0} Nat Nat.encodable) code)
    (@List.nil.{0} Nat)
```

### `GenLimit.Angluin.historyInCheck`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:40`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Nat → List.{0} Nat → Bool
```

Definition value:

```lean
fun F i history => GenLimit.Angluin.observedCheck F history i
```

### `GenLimit.Angluin.extensionAccepted`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:71`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily →
  GenLimit.Angluin.EffectiveIdentifier → Prod.{0, 0} Nat (List.{0} Nat) → Nat → Bool
```

Definition value:

```lean
fun F M p code =>
  have extension := GenLimit.Angluin.decodedHistory code;
  @ite.{1} Bool
    (@Eq.{1} Bool (GenLimit.Angluin.historyInCheck F (@Prod.fst.{0, 0} Nat (List.{0} Nat) p) extension) Bool.true)
    (instDecidableEqBool (GenLimit.Angluin.historyInCheck F (@Prod.fst.{0, 0} Nat (List.{0} Nat) p) extension)
      Bool.true)
    (@Decidable.decide
      (@Eq.{1} Nat
        (M
          (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
            (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) (@Prod.snd.{0, 0} Nat (List.{0} Nat) p)
            extension))
        (M (@Prod.snd.{0, 0} Nat (List.{0} Nat) p)))
      (instDecidableEqNat
        (M
          (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
            (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) (@Prod.snd.{0, 0} Nat (List.{0} Nat) p)
            extension))
        (M (@Prod.snd.{0, 0} Nat (List.{0} Nat) p))))
    Bool.true
```

### `GenLimit.Angluin.stabilizationCandidateCheck`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:136`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → GenLimit.Angluin.EffectiveIdentifier → Prod.{0, 0} Nat Nat → Nat → Bool
```

Definition value:

```lean
fun F M p code =>
  GenLimit.Angluin.stabilizationCandidateCheck.match_1.{1} (fun x => Bool)
    (@Encodable.decode.{0} (List.{0} Nat) (@List.encodable.{0} Nat Nat.encodable) code) (fun _ => Bool.false)
    fun history =>
    (GenLimit.Angluin.historyInCheck F (@Prod.fst.{0, 0} Nat Nat p) history).and
      (@GenLimit.Angluin.boundedAll.{0} (Prod.{0, 0} Nat (List.{0} Nat)) (GenLimit.Angluin.extensionAccepted F M)
        (@Prod.mk.{0, 0} Nat (List.{0} Nat) (@Prod.fst.{0, 0} Nat Nat p) history) (@Prod.snd.{0, 0} Nat Nat p))
```

### `GenLimit.Angluin.provisionalHistory`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:197`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → GenLimit.Angluin.EffectiveIdentifier → Nat → Nat → Option.{0} (List.{0} Nat)
```

Definition value:

```lean
fun F M i s =>
  @Option.bind.{0, 0} Nat (List.{0} Nat)
    (@GenLimit.Angluin.firstTrue.{0} (Prod.{0, 0} Nat Nat) (GenLimit.Angluin.stabilizationCandidateCheck F M)
      (@Prod.mk.{0, 0} Nat Nat i s)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@Encodable.decode.{0} (List.{0} Nat) (@List.encodable.{0} Nat Nat.encodable))
```

### `GenLimit.Angluin.lockingEmitter`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:224`.

```lean
GenLimit.Angluin.EffectiveIndexedFamily → GenLimit.Angluin.EffectiveIdentifier → Nat → Nat → Option.{0} Nat
```

Definition value:

```lean
fun F M i stage =>
  have sk := Nat.unpair stage;
  @Option.bind.{0, 0} (List.{0} Nat) Nat (GenLimit.Angluin.provisionalHistory F M i (@Prod.fst.{0, 0} Nat Nat sk))
    fun history =>
    @GetElem?.getElem?.{0, 0, 0} (List.{0} Nat) Nat Nat
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Nat as)) (@List.instGetElem?NatLtLength.{0} Nat) history
      (@Prod.snd.{0, 0} Nat Nat sk)
```

### `GenLimit.Angluin.SyntacticallyStabilizing`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Stabilization:17`.

```lean
GenLimit.Angluin.EffectiveIdentifier → Set.{0} Nat → List.{0} Nat → Prop
```

Definition value:

```lean
fun M L history =>
  And (@GenLimit.Angluin.ListWithin.{0} Nat history L)
    (∀ (extension : List.{0} Nat),
      @GenLimit.Angluin.ListWithin.{0} Nat extension L →
        @Eq.{1} Nat
          (M
            (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
              (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) history extension))
          (M history))
```

### `GenLimit.Angluin.IsLockingSequence`

Kind: definition. Frozen source locator: `GenLimit.Support.Locking:29`.

```lean
{α : Type u_1} → {β : Sort u_2} → (List.{u_1} α → β) → GenLimit.Generic.Language.{u_1} α → List.{u_1} α → β → Prop
```

Definition value:

```lean
fun {α} {β} M L xs j =>
  And (@GenLimit.Angluin.ListWithin.{u_1} α xs L)
    (∀ (tail : List.{u_1} α),
      @GenLimit.Angluin.ListWithin.{u_1} α tail L →
        @Eq.{u_2} β
          (M
            (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α)
              (@instHAppendOfAppend.{u_1} (List.{u_1} α) (@List.instAppend.{u_1} α)) xs tail))
          j)
```

### `GenLimit.Angluin.ListWithin`

Kind: definition. Frozen source locator: `GenLimit.Support.Locking:25`.

```lean
{α : Type u_1} → List.{u_1} α → GenLimit.Generic.Language.{u_1} α → Prop
```

Definition value:

```lean
fun {α} xs L =>
  ∀ (x : α),
    @Membership.mem.{u_1, u_1} α (List.{u_1} α) (@List.instMembership.{u_1} α) xs x →
      @Membership.mem.{u_1, u_1} α (GenLimit.Generic.Language.{u_1} α) (@Set.instMembership.{u_1} α) L x
```

### `GenLimit.Angluin.stabilizationCandidateCheck.match_1`

Kind: definition. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:None`.

```lean
(motive : Option.{0} (List.{0} Nat) → Sort u_1) →
  (x : Option.{0} (List.{0} Nat)) →
    (Unit → motive (@Option.none.{0} (List.{0} Nat))) →
      ((history : List.{0} Nat) → motive (@Option.some.{0} (List.{0} Nat) history)) → motive x
```

Definition value:

```lean
fun motive x h_1 h_2 => @Option.casesOn.{u_1, 0} (List.{0} Nat) (fun x => motive x) x (h_1 Unit.unit) fun val => h_2 val
```

## Appendix C — supporting theorem types only

These six statements were inspected to delimit what the supplied named algorithms assert. They are not additional opaque-slot targets, and their proofs were not reviewed.

### `GenLimit.Angluin.effectiveLearner_computable`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:344`.

```lean
∀ (F : GenLimit.Angluin.EffectiveIndexedFamily) {emit : Nat → Nat → Option.{0} Nat},
  @Computable₂.{0, 0, 0} Nat Nat (Option.{0} Nat) (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.option.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)) emit →
    @Computable.{0, 0} (List.{0} Nat) Nat
      (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (GenLimit.Angluin.effectiveLearner F emit)
```

### `GenLimit.Angluin.effectiveLearner_eq_semanticLearner`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Sufficiency:359`.

```lean
∀ (F : GenLimit.Angluin.EffectiveIndexedFamily) (emit : Nat → Nat → Option.{0} Nat) (t : Nat) (xs : Fin t → Nat),
  @Eq.{1} Nat (GenLimit.Angluin.effectiveLearner F emit (@List.ofFn.{0} Nat t xs))
    (@GenLimit.Angluin.semanticLearner.{0} Nat F.language (GenLimit.Angluin.stageContents emit)
      (@List.ofFn.{0} Nat t xs))
```

### `GenLimit.Angluin.conditionFourEmitter_isEnumeratedTellTale`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:278`.

```lean
∀ (F : GenLimit.Angluin.EffectiveIndexedFamily) (inclusion : Nat → Nat → Bool),
  (∀ (i j : Nat),
      Iff (@Eq.{1} Bool (inclusion i j) Bool.true)
        (@HasSubset.Subset.{0} (GenLimit.Generic.Language.{0} Nat) (@Set.instHasSubset.{0} Nat) (F.language i)
          (F.language j))) →
    @GenLimit.Angluin.ConditionTwo.{0} Nat F.language →
      ∀ (i : Nat),
        GenLimit.Angluin.IsEnumeratedTellTale F.language i
          (GenLimit.Angluin.enumeratedSet (GenLimit.Angluin.conditionFourEmitter F inclusion) i)
```

### `GenLimit.Angluin.conditionThreeEmitter_isEnumeratedTellTale`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries:553`.

```lean
∀ (F : GenLimit.Angluin.EffectiveIndexedFamily),
  GenLimit.Angluin.ConditionThree F.language →
    ∀ (i : Nat),
      GenLimit.Angluin.IsEnumeratedTellTale F.language i
        (GenLimit.Angluin.enumeratedSet (GenLimit.Angluin.conditionThreeEmitter F) i)
```

### `GenLimit.Angluin.exists_syntacticallyStabilizing`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Stabilization:23`.

```lean
∀ {M : GenLimit.Angluin.EffectiveIdentifier} {L : Set.{0} Nat},
  @Set.Nonempty.{0} Nat L →
    (∀ (stream : Nat → Nat),
        GenLimit.Presents stream L →
          ∃ guess T,
            ∀ (t : Nat), @LE.le.{0} Nat instLENat T t → @Eq.{1} Nat (M (@GenLimit.textPrefix.{0} Nat stream t)) guess) →
      ∃ history, GenLimit.Angluin.SyntacticallyStabilizing M L history
```

### `GenLimit.Angluin.effectiveInferrable_conditionOne`

Kind: theorem. Frozen source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Necessity:574`.

```lean
∀ {F : GenLimit.Angluin.EffectiveIndexedFamily},
  GenLimit.Angluin.EffectiveInferrable F → GenLimit.Angluin.ConditionOne F
```

