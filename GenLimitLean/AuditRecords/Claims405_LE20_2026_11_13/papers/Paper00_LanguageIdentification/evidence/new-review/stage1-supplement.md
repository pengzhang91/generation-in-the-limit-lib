# P00 Stage 1 supplement — paper-withheld native reconstruction

This supplement reconstructs all 26 unique supplied native target declarations. The supplemental slot mapping has 30 target–slot links across seven labels (C01, C02, C03, C05, C06, C15, C16); shared targets are reviewed once. The target records are all marked `theorem` by the exporter. The 98-record recursive package consists of 64 definitions, three inductives, three constructors and 28 theorem signatures: 26 targets plus two auxiliary existence signatures. The 72 dependency records are preserved in the appendix.

This is continued Lean-only Stage 1 exposure, not a new source-comparison stage and not a fresh-from-zero reviewer. Earlier context included the six original supplied targets, their 57 recursive records and selective code-only census checks; the full 693-record census had been parsed for bounded mechanical checks, not individually semantically audited. The original code-only report’s glossary is reused for unchanged dependencies. No source paper, Stage 2 finding/report, owner material, registry, PaperMap, developer explanation, source comments/proofs, or other audit was read. The supplemental slot labels are supplied locators; no source meaning or verified source correspondence is inferred from the selection.

The original three Stage 1 artifacts remain byte-for-byte unchanged. The original claim-slot table and its 13 no-endpoint entries are historical frozen scope records; the supplemental mappings do not rewrite that original scope or retroactively certify source coverage.

Requested model/reasoning remain `gpt-6.1-sol / xhigh`; actual backend identifier/revision and actual reasoning configuration are not observable and are not invented. This turn continues the original paper-withheld context; no backend isolation attestation is available. First explicit supplemental clock observation: 2026-11-13 23:59:54 UTC. Exact supplemental start time was not captured.

## Input provenance

All six manifest entries match the actual supplemental input bytes. SHA-256 values below include the manifest’s own computed hash. Earlier Stage 1 inputs and original artifacts are separately hashed in the supplemental run manifest, with the original report identified as reused code-only context.

| Input | Bytes | SHA-256 |
|---|---:|---|
| `stage1-supplement-input/PROMPT.md` | 1212 | `fe5ce01116fe2210fe060f472422dca8e6b205802c47016a746930697a0b6dce` |
| `stage1-supplement-input/SHA256SUMS` | 506 | `62fa9f7944031fd43e25d1a8beb847ba662dec2c66d7bf62e996cca8e4265449` |
| `stage1-supplement-input/declarations.jsonl` | 71764 | `745d5ce1bdab493e4018068bf1330ad9ce960d6180cdb1854d01433e0ad8d7e8` |
| `stage1-supplement-input/definition-dependencies.md` | 29682 | `3a7050ac4e8dfdbee97677de8f351e226978f2ff80e0e51f13a84b846eb4b1c5` |
| `stage1-supplement-input/target-statements.md` | 13855 | `d6ea045f490658e855d16cefd6008a766a0ec1609a5ba24c10450a04e42231a5` |
| `stage1-supplement-input/targets-by-slot.json` | 2128 | `c6f3e2426097d3197d60f85e6a0252fc6875a56aab0cece3f6447dba91b6aeb1` |
| `stage1-supplement-input/targets.txt` | 1600 | `259d56b05146a4fd9da8caa2db5fe052b57f45db8ca0747b12ea6ffda65980c3` |

## Shared exact meanings and representation boundary

`Language = Set Nat`; `LanguageFamily = Nat → Language`. An arbitrary name-valued learner is a total function `List Info → Name`, and a text learner has `Info = Nat`. These types impose no computability requirement. Fixed-parameter dependence on a naming, class, family or allowable map is semantic unless additional effective data is actually assumed. Histories are finite observed prefixes; `textPrefix stream t` lists positions 0,…,t−1, so time t’s next datum is not yet included.

`IdentifiesInLimit denote M stream target` means

```text
∃ name, denote name = target ∧
  ∃ T : Nat, ∀ t : Nat, T ≤ t → M (textPrefix stream t) = name.
```

The name is fixed after a per-run time. It is not enough that moving names always denote the right object. Semantic naming uses sets themselves as names and identity denotation, so the semantic version is eventual equality of the entire output set. No pointwise-membership limit, probability, support loss, fresh-element generation, density, frequency or limsup condition is substituted.

`Abstract.Naming Name Object` carries denotation, a chosen name for every object, and `denotes (nameOf object) = object`. `Text.Naming Name` carries only `Name → Language`; there is no right-inverse/coverage requirement. The distinction is retained in every target. Countability and surjectivity are mathematical properties, not effective enumeration certificates. Classical decision in an exported definition is not evidence that arbitrary set membership, equality, subset or infinite-extension compatibility can be computed.

`Presents stream L` is exactly `Set.range stream = L` for a total infinite `Nat → Nat` stream. This allows arbitrary repetitions and delays, but has no blanks or finite termination. Therefore the empty language has no such presentation. Informants instead provide pairs `(u,b)` with `b = true ↔ u ∈ L` and require every natural u to appear; an empty language does have all-false complete informants.

Auxiliary predicates returning `Prop`, including `IsStabilizing`, `IsLocking`, `IsTellTale`, `Generic.IsFiniteTellTale`, `IsInclusionAntichain` and `IsSuperfinite`, are definitions, not independently proved existence/characterization theorems. Their exact definition bodies and `kind` tags are recorded below. The two auxiliary `_proof_1` records are theorem signatures only; their bodies are absent. Embedded `⋯` in `Nat.find` values suppresses proof arguments, not missing mathematical definitions or proof holes.

The trusted external boundary is standard Lean/Mathlib meaning. No library audit is performed. Along with the original Stage 1 vocabulary, this package uses ordinary finite-set image, set nonemptiness and list append. There are no unresolved native `GenLimit.*` dependencies. No fresh compilation, proof-body review, construction certification or human certification was performed.

## Supplemental mapping (locators only)

| Slot label | Unique target dossier references |
|---|---|
| C01 | S04 `GenLimit.Gold.Abstract.distinguishable_of_identifiable`, S05 `GenLimit.Gold.Abstract.distinguishable_of_identifies`, S07 `GenLimit.Gold.Abstract.identificationByEnumeration_identifies`, S02 `GenLimit.Gold.Abstract.collapsingUncertainty_implies_identifiable`, S03 `GenLimit.Gold.Abstract.distinguishable_implies_identifiable_of_countable`, S06 `GenLimit.Gold.Abstract.firstCompatibleIndex_stabilizes` |
| C02 | S01 `GenLimit.Gold.Abstract.allowableSequences_countable`, S14 `GenLimit.Gold.Text.enumerationLearner_identifiesOnText`, S13 `GenLimit.Gold.Text.enumerationLearner_identifiesFamily_of_isInclusionAntichain`, S15 `GenLimit.Gold.Text.enumerationLearner_stabilizesTo_leastCover` |
| C03 | S10 `GenLimit.Gold.Informant.informantEnumerationLearner_stabilizesTo_leastEqualName`, S08 `GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback_stabilizesTo_leastEqualName`, S11 `GenLimit.Gold.Informant.leastEqualName_spec`, S09 `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesOnInformant` |
| C05 | S20 `GenLimit.Gold.Text.finiteLearner_identifiesOnText`, S19 `GenLimit.Gold.Text.finiteLanguages_semanticallyIdentifiable`, S16 `GenLimit.Gold.Text.eventually_sample_eq_of_finite` |
| C06 | S24 `GenLimit.Gold.Text.identifiesClass_semanticLearner`, S23 `GenLimit.Gold.Text.identifiableWith_implies_semanticallyIdentifiable`, S25 `GenLimit.Gold.Text.superfinite_not_identifiableWith`, S26 `GenLimit.Gold.Text.superfinite_not_text_identifiable`, S12 `GenLimit.Gold.Text.all_finite_and_infinite_not_semanticallyIdentifiable`, S17 `GenLimit.Gold.Text.exists_locking_of_identifiesLanguage`, S18 `GenLimit.Gold.Text.exists_stabilizing_of_identifiesLanguage`, S21 `GenLimit.Gold.Text.finite_tellTale_of_semantic_identification`, S22 `GenLimit.Gold.Text.finite_tellTale_of_semanticallyIdentifiable` |
| C15 | S25 `GenLimit.Gold.Text.superfinite_not_identifiableWith`, S26 `GenLimit.Gold.Text.superfinite_not_text_identifiable` |
| C16 | S25 `GenLimit.Gold.Text.superfinite_not_identifiableWith`, S26 `GenLimit.Gold.Text.superfinite_not_text_identifiable` |

## S01: `GenLimit.Gold.Abstract.allowableSequences_countable`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:142`. Universe parameters: `u_1, u_2`. Supplemental labels: C02.

**Exact exported type:**

```lean
∀ {Object : Type u_1} {Info : Type u_2} [Countable.{u_1 + 1} Object]
  {allowable : GenLimit.Gold.Abstract.Allowable.{u_2, u_1} Info Object},
  (∀ (object : Object), @Set.Countable.{u_2} (Nat → Info) (allowable object)) →
    @Set.Countable.{u_2} (Nat → Info) (@GenLimit.Gold.Abstract.allowableSequences.{u_2, u_1} Info Object allowable)
```

**Reconstruction.** For an arbitrary information type and a countable object type, if the set of allowed complete streams for every individual object is countable, then the set of all complete streams allowed for at least one object is countable. No information-type countability, object nonemptiness, naming, learner, distinguishability or collapsing-uncertainty condition occurs in this target.

**Assumptions and binder scope:**

- Object : Type u_1 and Info : Type u_2 are implicit; Countable Object is a typeclass binder.
- allowable : Object → Set (Nat → Info) is implicit.
- The sole proposition premise is ∀ object, Set.Countable (allowable object).

**Expanded quantifiers and witness dependencies:**

```text
∀ {Object} {Info} [Countable Object] {allowable}, (∀ object, (allowable object).Countable) → {stream | ∃ object, stream ∈ allowable object}.Countable. The existential object lies inside membership of each stream; it is not one object generating all streams.
```

**Algorithm, input access and effectiveness.** This is a cardinality/set-union assertion. It supplies no named enumeration of streams, no computable enumeration, no learner, and no oracle. Countable is not replaced with recursively enumerable.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- Object and individual allowable sets may be empty; the union is then correspondingly empty.
- No global finite bound on allowed streams is asserted; overlaps between different objects’ stream sets are allowed.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Abstract.Allowable`, `GenLimit.Gold.Abstract.allowableSequences`.


## S02: `GenLimit.Gold.Abstract.collapsingUncertainty_implies_identifiable`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:129`. Universe parameters: `u_1, u_2, u_3`. Supplemental labels: C01.

**Exact exported type:**

```lean
∀ {Name : Type u_1} {Object : Type u_2} {Info : Type u_3}
  (naming : GenLimit.Gold.Abstract.Naming.{u_2, u_1} Name Object)
  {allowable : GenLimit.Gold.Abstract.Allowable.{u_3, u_2} Info Object},
  @GenLimit.Gold.Abstract.CollapsingUncertainty.{u_3, u_2} Info Object allowable →
    ∀ (enumeration : Nat → Object),
      @Function.Surjective.{1, u_2 + 1} Nat Object enumeration →
        @GenLimit.Gold.Abstract.Identifiable.{u_1, u_2, u_3} Name Object Info naming allowable
```

**Reconstruction.** Given a naming and an allowable map with collapsing uncertainty, every supplied surjective enumeration of objects yields semantic identifiability: some total finite-history learner identifies every object on every stream allowed for it. The type itself does not select the named enumeration learner; the separate identificationByEnumeration_identifies target does.

**Assumptions and binder scope:**

- Implicit Name : Type u_1, Object : Type u_2, Info : Type u_3.
- Explicit naming : Abstract.Naming Name Object includes denotes/nameOf and denotes (nameOf object) = object.
- Implicit allowable; proposition premise CollapsingUncertainty allowable.
- Then explicit enumeration : Nat → Object followed by Function.Surjective enumeration. No Countable or Nonempty typeclass assumptions occur.

**Expanded quantifiers and witness dependencies:**

```text
∀ {Name Object Info}, ∀ naming, ∀ {allowable}, CU allowable → ∀ enumeration, Surjective enumeration → ∃ learner : List Info → Name, ∀ object stream, stream ∈ allowable object → ∃ name, naming.denotes name = object ∧ ∃ T, ∀ t ≥ T, learner (textPrefix stream t) = name. learner may depend on naming, allowable and the supplied enumeration; name/T follow object and stream. CU means ∀ target stream ∈ allowable target, ∀ object ≠ target, ∃ T, ∀ t ≥ T, ¬ Compatible allowable (textPrefix stream t) object.
```

**Algorithm, input access and effectiveness.** The varying learner input is a finite List Info; naming, allowable and any enumeration are fixed parameters. Compatibility is ∃ full allowable stream with this exact prefix, an unrestricted semantic predicate. firstCompatibleIndex uses Classical.propDecidable and Nat.find to return the least compatible enumeration index, or 0 if none exists; identificationByEnumeration returns naming.nameOf of the selected object. No target or future stream is supplied to the learner, and no state beyond the given history is specified. Neither classical compatibility decisions nor an unbounded least-index search certify ordinary computation. No explicit oracle type/interface is present. Countability and surjectivity, where actually assumed, are mathematical properties rather than effective enumeration certificates.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- Surjectivity is an actual premise, not an effective object enumerator. It entails that an object is available as enumeration 0 without an extra Nonempty binder.
- The existential learner is chosen before all target objects/streams. CU exclusion times are separately allowed to depend on each competing object.
- Allowed streams need not exist for every object; such per-object requirements are vacuous. Repeated enumeration values are allowed.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Abstract.Allowable`, `GenLimit.Gold.Abstract.CollapsingUncertainty`, `GenLimit.Gold.Abstract.Compatible`, `GenLimit.Gold.Abstract.Identifiable`, `GenLimit.Gold.Abstract.Identifies`, `GenLimit.Gold.Abstract.IdentifiesOn`, `GenLimit.Gold.Abstract.Naming`, `GenLimit.Gold.Abstract.Naming.denotes`, `GenLimit.Gold.Abstract.Naming.mk`, `GenLimit.IdentifiesInLimit`, `GenLimit.Learner`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S03: `GenLimit.Gold.Abstract.distinguishable_implies_identifiable_of_countable`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:197`. Universe parameters: `u_1, u_2, u_3`. Supplemental labels: C01.

**Exact exported type:**

```lean
∀ {Info : Type u_1} {Object : Type u_2} {Name : Type u_3} [Countable.{u_1 + 1} Info] [Countable.{u_2 + 1} Object]
  [Nonempty.{u_2 + 1} Object] (naming : GenLimit.Gold.Abstract.Naming.{u_2, u_3} Name Object)
  {allowable : GenLimit.Gold.Abstract.Allowable.{u_1, u_2} Info Object},
  (∀ (object : Object), @Set.Countable.{u_1} (Nat → Info) (allowable object)) →
    @GenLimit.Gold.Abstract.Distinguishable.{u_1, u_2} Info Object allowable →
      @GenLimit.Gold.Abstract.Identifiable.{u_3, u_2, u_1} Name Object Info naming allowable
```

**Reconstruction.** Under countability of the information type and object type, nonemptiness of objects, a supplied naming and countability of each object’s allowable stream set, disjointness of the allowable sets for different objects implies existence of one learner identifying all objects on all their allowed streams. This is a semantic existence conclusion and does not name identificationByEnumeration or assert collapsing uncertainty.

**Assumptions and binder scope:**

- Implicit Info : Type u_1, Object : Type u_2, Name : Type u_3.
- Countable Info; Countable Object; Nonempty Object.
- Explicit naming with a chosen right inverse of denotation; implicit allowable.
- ∀ object, Set.Countable (allowable object), followed by Distinguishable allowable.

**Expanded quantifiers and witness dependencies:**

```text
∀ {Info Object Name} [Countable Info] [Countable Object] [Nonempty Object], ∀ naming {allowable}, (∀ object, (allowable object).Countable) → (∀ o₁ o₂ stream, stream ∈ allowable o₁ → stream ∈ allowable o₂ → o₁ = o₂) → ∃ learner, ∀ object stream, stream ∈ allowable object → ∃ name, denotes name = object ∧ ∃ T, ∀ t ≥ T, learner (prefix stream t) = name. No bound or chosen witness algorithm is specified.
```

**Algorithm, input access and effectiveness.** The varying learner input is a finite List Info; naming, allowable and any enumeration are fixed parameters. Compatibility is ∃ full allowable stream with this exact prefix, an unrestricted semantic predicate. firstCompatibleIndex uses Classical.propDecidable and Nat.find to return the least compatible enumeration index, or 0 if none exists; identificationByEnumeration returns naming.nameOf of the selected object. No target or future stream is supplied to the learner, and no state beyond the given history is specified. Neither classical compatibility decisions nor an unbounded least-index search certify ordinary computation. No explicit oracle type/interface is present. Countability and surjectivity, where actually assumed, are mathematical properties rather than effective enumeration certificates.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- Countable Info does not make all infinite streams countable; the separate per-object stream-countability assumption is retained.
- Name need not be countable or effectively represented. Arbitrary multiple names for an object are allowed, but one name must become fixed along each run.
- Object itself is explicitly nonempty, while each allowable stream set can be empty.
- This target is not a theorem that distinguishability makes the specific least-compatible learner succeed.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Abstract.Allowable`, `GenLimit.Gold.Abstract.Distinguishable`, `GenLimit.Gold.Abstract.Identifiable`, `GenLimit.Gold.Abstract.Identifies`, `GenLimit.Gold.Abstract.IdentifiesOn`, `GenLimit.Gold.Abstract.Naming`, `GenLimit.Gold.Abstract.Naming.denotes`, `GenLimit.Gold.Abstract.Naming.mk`, `GenLimit.IdentifiesInLimit`, `GenLimit.Learner`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S04: `GenLimit.Gold.Abstract.distinguishable_of_identifiable`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:93`. Universe parameters: `u_1, u_2, u_3`. Supplemental labels: C01.

**Exact exported type:**

```lean
∀ {Name : Type u_1} {Object : Type u_2} {Info : Type u_3}
  {naming : GenLimit.Gold.Abstract.Naming.{u_2, u_1} Name Object}
  {allowable : GenLimit.Gold.Abstract.Allowable.{u_3, u_2} Info Object},
  @GenLimit.Gold.Abstract.Identifiable.{u_1, u_2, u_3} Name Object Info naming allowable →
    @GenLimit.Gold.Abstract.Distinguishable.{u_3, u_2} Info Object allowable
```

**Reconstruction.** If there exists one total learner identifying every object on all its allowed streams using the supplied naming, then any one complete stream allowed for two objects forces those objects equal. No countability, nonemptiness, enumeration or collapsing assumption is present.

**Assumptions and binder scope:**

- Implicit Name/Object/Info and implicit naming/allowable.
- The only proposition premise is Identifiable naming allowable, i.e. existence of one globally identifying learner.

**Expanded quantifiers and witness dependencies:**

```text
∀ {Name Object Info naming allowable}, (∃ learner, ∀ object stream, stream ∈ allowable object → ∃ name, denotes name = object ∧ ∃ T, ∀ t ≥ T, learner (prefix stream t) = name) → ∀ o₁ o₂ stream, stream ∈ allowable o₁ → stream ∈ allowable o₂ → o₁ = o₂. The learner is before all objects/streams; correct names/T can differ between target/run instances.
```

**Algorithm, input access and effectiveness.** The theorem takes a semantic existence hypothesis and concludes disjointness. It does not build a learner or decide distinguishability. The learner sees only finite prefixes. No computability constraint occurs.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- Allowed stream sets may be empty; overlap requirements without a shared stream are vacuous.
- Distinguishability concerns complete streams, not a uniform finite prefix that separates all objects.
- The absence of Countable/Nonempty binders is material; the stronger aggregate theorem’s common assumptions are not imported here.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Abstract.Allowable`, `GenLimit.Gold.Abstract.Distinguishable`, `GenLimit.Gold.Abstract.Identifiable`, `GenLimit.Gold.Abstract.Identifies`, `GenLimit.Gold.Abstract.IdentifiesOn`, `GenLimit.Gold.Abstract.Naming`, `GenLimit.Gold.Abstract.Naming.denotes`, `GenLimit.Gold.Abstract.Naming.mk`, `GenLimit.IdentifiesInLimit`, `GenLimit.Learner`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S05: `GenLimit.Gold.Abstract.distinguishable_of_identifies`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:74`. Universe parameters: `u_1, u_2, u_3`. Supplemental labels: C01.

**Exact exported type:**

```lean
∀ {Name : Type u_1} {Object : Type u_2} {Info : Type u_3}
  {naming : GenLimit.Gold.Abstract.Naming.{u_2, u_1} Name Object}
  {allowable : GenLimit.Gold.Abstract.Allowable.{u_3, u_2} Info Object}
  {learner : GenLimit.Learner.{u_3, u_1} Info Name},
  @GenLimit.Gold.Abstract.Identifies.{u_1, u_2, u_3} Name Object Info naming allowable learner →
    @GenLimit.Gold.Abstract.Distinguishable.{u_3, u_2} Info Object allowable
```

**Reconstruction.** For any fixed total learner, if it identifies all objects on their allowed streams, then a complete stream allowable for two objects forces those objects equal. The supplied learner is an implicit parameter rather than an existential conclusion.

**Assumptions and binder scope:**

- Implicit Name/Object/Info, naming, allowable, and learner : List Info → Name.
- The sole proposition premise is Identifies naming allowable learner. No countability, nonemptiness or enumeration is assumed.

**Expanded quantifiers and witness dependencies:**

```text
∀ {Name Object Info naming allowable learner}, (∀ object stream, stream ∈ allowable object → ∃ name, denotes name = object ∧ ∃ T, ∀ t ≥ T, learner (prefix stream t) = name) → ∀ o₁ o₂ stream, stream ∈ allowable o₁ → stream ∈ allowable o₂ → o₁ = o₂.
```

**Algorithm, input access and effectiveness.** This is a consequence of an assumed globally successful semantic learner, not an algorithm to find such a learner. Fixed-name stabilization, rather than mere semantic correctness of arbitrary changing names, is the assumed success notion.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- No theorem of finite-time decidable discrimination is stated.
- No allowed streams for a target makes that target’s identification premise vacuous.
- The learner hypothesis is uniform over all objects and streams; it is not merely success on a single target/run.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Abstract.Allowable`, `GenLimit.Gold.Abstract.Distinguishable`, `GenLimit.Gold.Abstract.Identifies`, `GenLimit.Gold.Abstract.IdentifiesOn`, `GenLimit.Gold.Abstract.Naming`, `GenLimit.Gold.Abstract.Naming.denotes`, `GenLimit.Gold.Abstract.Naming.mk`, `GenLimit.IdentifiesInLimit`, `GenLimit.Learner`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S06: `GenLimit.Gold.Abstract.firstCompatibleIndex_stabilizes`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:29`. Universe parameters: `u_1, u_2`. Supplemental labels: C01.

**Exact exported type:**

```lean
∀ {Info : Type u_1} {Object : Type u_2} {allowable : GenLimit.Gold.Abstract.Allowable.{u_1, u_2} Info Object},
  @GenLimit.Gold.Abstract.CollapsingUncertainty.{u_1, u_2} Info Object allowable →
    ∀ (enumeration : Nat → Object) (henumeration : @Function.Surjective.{1, u_2 + 1} Nat Object enumeration)
      {target : Object} {stream : Nat → Info},
      @Membership.mem.{u_1, u_1} (Nat → Info) (Set.{u_1} (Nat → Info)) (@Set.instMembership.{u_1} (Nat → Info))
          (allowable target) stream →
        @GenLimit.StabilizesTo.{0} Nat
          (fun t =>
            @GenLimit.Gold.Abstract.firstCompatibleIndex.{u_1, u_2} Info Object allowable enumeration
              (@GenLimit.textPrefix.{u_1} Info stream t))
          (@GenLimit.Gold.Abstract.firstEnumerationIndex.{u_2} Object enumeration henumeration target)
```

**Reconstruction.** With collapsing uncertainty and any supplied surjective object enumeration, along any stream allowed for a target the named firstCompatibleIndex becomes exactly the least enumeration index whose value equals that target, and remains that index forever. This is stronger than eventual correct object denotation: it fixes the least preimage index even when the enumeration repeats objects.

**Assumptions and binder scope:**

- Implicit Info/Object/allowable.
- CollapsingUncertainty allowable.
- Explicit enumeration and its surjectivity proof henumeration.
- Implicit target and stream; stream ∈ allowable target. No naming or countability binder occurs.

**Expanded quantifiers and witness dependencies:**

```text
∀ {Info Object allowable}, CU allowable → ∀ enumeration henumeration {target stream}, stream ∈ allowable target → ∃ T, ∀ t ≥ T, firstCompatibleIndex allowable enumeration (prefix stream t) = firstEnumerationIndex enumeration henumeration target. firstEnumerationIndex is min {n | enumeration n = target}. The limit index depends on enumeration/target (and formally on its surjectivity proof argument), not on the particular allowed stream; T may depend on the complete run and all fixed parameters.
```

**Algorithm, input access and effectiveness.** The varying learner input is a finite List Info; naming, allowable and any enumeration are fixed parameters. Compatibility is ∃ full allowable stream with this exact prefix, an unrestricted semantic predicate. firstCompatibleIndex uses Classical.propDecidable and Nat.find to return the least compatible enumeration index, or 0 if none exists; identificationByEnumeration returns naming.nameOf of the selected object. No target or future stream is supplied to the learner, and no state beyond the given history is specified. Neither classical compatibility decisions nor an unbounded least-index search certify ordinary computation. No explicit oracle type/interface is present. Countability and surjectivity, where actually assumed, are mathematical properties rather than effective enumeration certificates.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- The least-preimage index exists by surjectivity, including repeated target values.
- For arbitrary incompatible histories the selector defaults to 0; valid target prefixes always admit a compatible target preimage under surjectivity.
- No uniform convergence time or effective test for reaching the limit is stated.
- firstEnumerationIndex uses a suppressed proof argument; its proof body was not inspected.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Abstract.Allowable`, `GenLimit.Gold.Abstract.CollapsingUncertainty`, `GenLimit.Gold.Abstract.Compatible`, `GenLimit.Gold.Abstract.firstCompatibleIndex`, `GenLimit.Gold.Abstract.firstEnumerationIndex`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S07: `GenLimit.Gold.Abstract.identificationByEnumeration_identifies`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:104`. Universe parameters: `u_1, u_2, u_3`. Supplemental labels: C01.

**Exact exported type:**

```lean
∀ {Name : Type u_1} {Object : Type u_2} {Info : Type u_3}
  (naming : GenLimit.Gold.Abstract.Naming.{u_2, u_1} Name Object)
  {allowable : GenLimit.Gold.Abstract.Allowable.{u_3, u_2} Info Object},
  @GenLimit.Gold.Abstract.CollapsingUncertainty.{u_3, u_2} Info Object allowable →
    ∀ (enumeration : Nat → Object),
      @Function.Surjective.{1, u_2 + 1} Nat Object enumeration →
        @GenLimit.Gold.Abstract.Identifies.{u_1, u_2, u_3} Name Object Info naming allowable
          (@GenLimit.Gold.Abstract.identificationByEnumeration.{u_1, u_2, u_3} Name Object Info naming allowable
            enumeration)
```

**Reconstruction.** For any naming and allowable map with collapsing uncertainty, and every surjective enumeration of objects, the specifically defined identificationByEnumeration learner identifies all objects on every allowed stream. The statement directly names the successful learner; there is no need to infer that witness from an existential proof.

**Assumptions and binder scope:**

- Implicit Name/Object/Info; explicit naming with a chosen right inverse.
- Implicit allowable and premise CollapsingUncertainty allowable.
- Then enumeration : Nat → Object and Function.Surjective enumeration. No Countable/Nonempty typeclass assumptions or per-object stream-countability premise occur.

**Expanded quantifiers and witness dependencies:**

```text
∀ {Name Object Info}, ∀ naming {allowable}, CU allowable → ∀ enumeration, Surjective enumeration → ∀ object stream, stream ∈ allowable object → ∃ name, naming.denotes name = object ∧ ∃ T, ∀ t ≥ T, identificationByEnumeration naming allowable enumeration (prefix stream t) = name. The learner is fixed before object/stream; the correct name and T are per run.
```

**Algorithm, input access and effectiveness.** The varying learner input is a finite List Info; naming, allowable and any enumeration are fixed parameters. Compatibility is ∃ full allowable stream with this exact prefix, an unrestricted semantic predicate. firstCompatibleIndex uses Classical.propDecidable and Nat.find to return the least compatible enumeration index, or 0 if none exists; identificationByEnumeration returns naming.nameOf of the selected object. No target or future stream is supplied to the learner, and no state beyond the given history is specified. Neither classical compatibility decisions nor an unbounded least-index search certify ordinary computation. No explicit oracle type/interface is present. Countability and surjectivity, where actually assumed, are mathematical properties rather than effective enumeration certificates.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- The actual output on any history is nameOf (enumeration (firstCompatibleIndex ... history)); the conclusion is expressed through Identifies rather than explicitly naming nameOf object as its existential witness.
- Enumeration duplicates and multiple names in the naming are allowed.
- An object with no allowable stream imposes no run condition. The theorem does not require countability of the allowed streams.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Abstract.Allowable`, `GenLimit.Gold.Abstract.CollapsingUncertainty`, `GenLimit.Gold.Abstract.Compatible`, `GenLimit.Gold.Abstract.Identifies`, `GenLimit.Gold.Abstract.IdentifiesOn`, `GenLimit.Gold.Abstract.Naming`, `GenLimit.Gold.Abstract.Naming.denotes`, `GenLimit.Gold.Abstract.Naming.mk`, `GenLimit.Gold.Abstract.Naming.nameOf`, `GenLimit.Gold.Abstract.firstCompatibleIndex`, `GenLimit.Gold.Abstract.identificationByEnumeration`, `GenLimit.IdentifiesInLimit`, `GenLimit.Learner`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S08: `GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback_stabilizesTo_leastEqualName`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:98`. Universe parameters: `(none)`. Supplemental labels: C03.

**Exact exported type:**

```lean
∀ {C : GenLimit.LanguageFamily} {info : GenLimit.Gold.Informant.InformantStream} {z fallback : Nat},
  GenLimit.Gold.Informant.IsInformantFor info (C z) →
    @GenLimit.StabilizesTo.{0} Nat
      (fun t =>
        GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback C fallback
          (@GenLimit.textPrefix.{0} GenLimit.Gold.Informant.InformantDatum info t))
      (GenLimit.Gold.Informant.leastEqualName C z)
```

**Reconstruction.** For every arbitrary indexed family, complete correct informant for C z, and arbitrary natural fallback, the named fallback learner eventually outputs exactly the least index n with C n = C z at every subsequent time. The stable target index is independent of fallback and the particular informant by its definition; the convergence time need not be uniform.

**Assumptions and binder scope:**

- Implicit C : Nat → Set Nat, info : Nat → (Nat × Bool), z : Nat and fallback : Nat.
- IsInformantFor info (C z), packaging both correct labels and occurrence of every natural. No effectiveness or injectivity of C is assumed.

**Expanded quantifiers and witness dependencies:**

```text
∀ {C info z fallback}, ((∀ t, (info t).2 = true ↔ (info t).1 ∈ C z) ∧ (∀ u, ∃ t, (info t).1 = u)) → ∃ T, ∀ t ≥ T, informantEnumerationLearnerWithFallback C fallback (prefix info t) = leastEqualName C z. leastEqualName = min {n | C n = C z}. T follows C/info/z/fallback and may depend on all of them.
```

**Algorithm, input access and effectiveness.** At history h, form {i ∈ Finset.range h.length | ∀ datum ∈ h, datum.2 = true ↔ datum.1 ∈ C i}, then return its minimum if nonempty and fallback otherwise. informantEnumerationLearner fixes fallback = 0. The procedure uses only the observed labeled prefix and fixed C/fallback; z, the true target and future labels are not inputs. The family C is an arbitrary Nat → Set Nat, and filter dependency metadata includes Classical.propDecidable. A uniform membership mechanism for C would suffice for the finite checks, but none is assumed or certified. leastEqualName is a classical semantic reference using extensional equality of full languages, not a computable label-recognition routine supplied to the learner.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- fallback is arbitrary, not restricted to a compatible or correct index; early outputs can be incorrect. At [] the finite candidate range is empty and the fallback is returned.
- Equal family languages at distinct indices are allowed; the stable index need not be z.
- Informant completeness permits repeats, arbitrary order and unbounded delays; it is not a rate hypothesis.
- Empty languages have complete all-false informants, so this is not positive-text empty-target vacuity.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Informant.InformantCompatible`, `GenLimit.Gold.Informant.InformantComplete`, `GenLimit.Gold.Informant.InformantCorrect`, `GenLimit.Gold.Informant.InformantDatum`, `GenLimit.Gold.Informant.InformantLearner`, `GenLimit.Gold.Informant.InformantStream`, `GenLimit.Gold.Informant.IsInformantFor`, `GenLimit.Gold.Informant.IsInformantFor.mk`, `GenLimit.Gold.Informant.informantCompatibleIndices`, `GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback`, `GenLimit.Gold.Informant.leastEqualName`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.StabilizesTo`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.Support.leastEquivalentIndex`, `GenLimit.Support.leastEquivalentIndex._proof_1`, `GenLimit.textPrefix`.


## S09: `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesOnInformant`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:159`. Universe parameters: `(none)`. Supplemental labels: C03.

**Exact exported type:**

```lean
∀ {C : GenLimit.LanguageFamily} {info : GenLimit.Gold.Informant.InformantStream} {z : Nat},
  GenLimit.Gold.Informant.IsInformantFor info (C z) →
    @GenLimit.Gold.Informant.IdentifiesOnInformant.{0} Nat (GenLimit.Gold.Text.familyNaming C)
      (GenLimit.Gold.Informant.informantEnumerationLearner C) info (C z)
```

**Reconstruction.** On every complete correct informant for C z, the specific fallback-0 informantEnumerationLearner identifies C z using C as the natural-index naming. Thus some index denoting exactly C z becomes the fixed output. The type of this target does not itself identify that index as leastEqualName, although another supplied target does.

**Assumptions and binder scope:**

- Implicit C, info and z.
- IsInformantFor info (C z), with both correctness and completeness.

**Expanded quantifiers and witness dependencies:**

```text
∀ {C info z}, IsInformantFor info (C z) → ∃ n : Nat, C n = C z ∧ ∃ T, ∀ t ≥ T, informantEnumerationLearner C (prefix info t) = n. n and T follow the informant; the learner depends only on fixed C and its observed prefix.
```

**Algorithm, input access and effectiveness.** At history h, form {i ∈ Finset.range h.length | ∀ datum ∈ h, datum.2 = true ↔ datum.1 ∈ C i}, then return its minimum if nonempty and fallback otherwise. informantEnumerationLearner fixes fallback = 0. The procedure uses only the observed labeled prefix and fixed C/fallback; z, the true target and future labels are not inputs. The family C is an arbitrary Nat → Set Nat, and filter dependency metadata includes Classical.propDecidable. A uniform membership mechanism for C would suffice for the finite checks, but none is assumed or certified. leastEqualName is a classical semantic reference using extensional equality of full languages, not a computable label-recognition routine supplied to the learner.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- The conclusion is eventual fixed-index identification, not all-time consistency or pointwise language approximation.
- Duplicated language indices are allowed; n need not equal z.
- Incomplete or incorrectly labeled histories are outside the theorem, although the learner remains a total function on such finite lists.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Informant.IdentifiesOnInformant`, `GenLimit.Gold.Informant.InformantCompatible`, `GenLimit.Gold.Informant.InformantComplete`, `GenLimit.Gold.Informant.InformantCorrect`, `GenLimit.Gold.Informant.InformantDatum`, `GenLimit.Gold.Informant.InformantLearner`, `GenLimit.Gold.Informant.InformantStream`, `GenLimit.Gold.Informant.IsInformantFor`, `GenLimit.Gold.Informant.IsInformantFor.mk`, `GenLimit.Gold.Informant.informantCompatibleIndices`, `GenLimit.Gold.Informant.informantEnumerationLearner`, `GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.familyNaming`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.StabilizesTo`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.textPrefix`.


## S10: `GenLimit.Gold.Informant.informantEnumerationLearner_stabilizesTo_leastEqualName`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:146`. Universe parameters: `(none)`. Supplemental labels: C03.

**Exact exported type:**

```lean
∀ {C : GenLimit.LanguageFamily} {info : GenLimit.Gold.Informant.InformantStream} {z : Nat},
  GenLimit.Gold.Informant.IsInformantFor info (C z) →
    @GenLimit.StabilizesTo.{0} Nat
      (fun t =>
        GenLimit.Gold.Informant.informantEnumerationLearner C
          (@GenLimit.textPrefix.{0} GenLimit.Gold.Informant.InformantDatum info t))
      (GenLimit.Gold.Informant.leastEqualName C z)
```

**Reconstruction.** For every complete correct informant for C z, the named informantEnumerationLearner with fallback 0 stabilizes exactly to the least natural index whose family language equals C z. The theorem fixes this index before the existential convergence time and does not merely assert existence of some equivalent name.

**Assumptions and binder scope:**

- Implicit arbitrary family C, informant info and target index z.
- IsInformantFor info (C z). No decidability or effective family representation premise.

**Expanded quantifiers and witness dependencies:**

```text
∀ {C info z}, IsInformantFor info (C z) → ∃ T, ∀ t ≥ T, informantEnumerationLearner C (prefix info t) = min {n : Nat | C n = C z}. The min exists since z is such an index. T may depend on C,z,info; no rate is given.
```

**Algorithm, input access and effectiveness.** At history h, form {i ∈ Finset.range h.length | ∀ datum ∈ h, datum.2 = true ↔ datum.1 ∈ C i}, then return its minimum if nonempty and fallback otherwise. informantEnumerationLearner fixes fallback = 0. The procedure uses only the observed labeled prefix and fixed C/fallback; z, the true target and future labels are not inputs. The family C is an arbitrary Nat → Set Nat, and filter dependency metadata includes Classical.propDecidable. A uniform membership mechanism for C would suffice for the finite checks, but none is assumed or certified. leastEqualName is a classical semantic reference using extensional equality of full languages, not a computable label-recognition routine supplied to the learner.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- The least index is defined by full extensional equality of languages, not syntactic index equality; C may repeat languages.
- At t = 0 the learner outputs 0 even when its eventual correct name is different.
- All natural inputs must eventually occur with correct Boolean labels; an arbitrary sound positive-only sequence does not meet the premise.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Informant.InformantCompatible`, `GenLimit.Gold.Informant.InformantComplete`, `GenLimit.Gold.Informant.InformantCorrect`, `GenLimit.Gold.Informant.InformantDatum`, `GenLimit.Gold.Informant.InformantLearner`, `GenLimit.Gold.Informant.InformantStream`, `GenLimit.Gold.Informant.IsInformantFor`, `GenLimit.Gold.Informant.IsInformantFor.mk`, `GenLimit.Gold.Informant.informantCompatibleIndices`, `GenLimit.Gold.Informant.informantEnumerationLearner`, `GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback`, `GenLimit.Gold.Informant.leastEqualName`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.StabilizesTo`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.Support.leastEquivalentIndex`, `GenLimit.Support.leastEquivalentIndex._proof_1`, `GenLimit.textPrefix`.


## S11: `GenLimit.Gold.Informant.leastEqualName_spec`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:31`. Universe parameters: `(none)`. Supplemental labels: C03.

**Exact exported type:**

```lean
∀ (C : GenLimit.LanguageFamily) (z : Nat),
  @Eq.{1} GenLimit.Language (C (GenLimit.Gold.Informant.leastEqualName C z)) (C z)
```

**Reconstruction.** For every family C and index z, the language at the classically selected least equal-name index is exactly C z. The target statement asserts denotation equality only; the least-index interpretation comes from the reviewed Nat.find-based definition.

**Assumptions and binder scope:**

- Explicit C : Nat → Language and z : Nat. No informant, learner, countability, effectiveness or additional proposition premise.

**Expanded quantifiers and witness dependencies:**

```text
∀ C : Nat → Set Nat, ∀ z : Nat, C (leastEqualName C z) = C z. leastEqualName C z = leastEquivalentIndex C z = Nat.find (∃ n, C n = C z). The selected index is a deterministic function of C,z, not a per-stream existential index.
```

**Algorithm, input access and effectiveness.** leastEquivalentIndex uses Nat.find with Classical.propDecidable for extensional language equality and a suppressed existence proof. It is a mathematical selector; no procedure deciding equality of arbitrary languages or computing this index from effective descriptions is supplied.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- This theorem is not an informant-convergence assertion by itself.
- The underlying family can be constant or have duplicate entries; z always supplies a matching index.
- The auxiliary existence theorem’s signature is supplied, but its proof body is excluded.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Informant.leastEqualName`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.Support.leastEquivalentIndex`, `GenLimit.Support.leastEquivalentIndex._proof_1`.


## S12: `GenLimit.Gold.Text.all_finite_and_infinite_not_semanticallyIdentifiable`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:196`. Universe parameters: `(none)`. Supplemental labels: C06.

**Exact exported type:**

```lean
∀ {𝒞 : Set.{0} GenLimit.Language},
  (∀ (F : Finset.{0} Nat),
      @Membership.mem.{0, 0} (Set.{0} Nat) (Set.{0} GenLimit.Language) (@Set.instMembership.{0} GenLimit.Language) 𝒞
        (@Finset.toSet.{0} Nat F)) →
    (∃ L,
        And
          (@Membership.mem.{0, 0} GenLimit.Language (Set.{0} GenLimit.Language)
            (@Set.instMembership.{0} GenLimit.Language) 𝒞 L)
          (@Set.Infinite.{0} Nat L)) →
      Not (GenLimit.Gold.Text.SemanticallyIdentifiable 𝒞)
```

**Reconstruction.** For any class of languages, if every Finset Nat viewed as a language belongs to the class and some infinite language belongs to it, then the class has no total semantic learner identifying all its members on all their positive texts. This target expresses the finite-language inclusion premise via every finite-set representation.

**Assumptions and binder scope:**

- Implicit 𝒞 : Set Language.
- First premise: ∀ F : Finset Nat, (F : Set Nat) ∈ 𝒞.
- Second premise: ∃ L, L ∈ 𝒞 ∧ Set.Infinite L.

**Expanded quantifiers and witness dependencies:**

```text
∀ {𝒞}, (∀ F : Finset Nat, (F : Set Nat) ∈ 𝒞) → (∃ L, L ∈ 𝒞 ∧ L.Infinite) → ¬ ∃ M : List Nat → Set Nat, ∀ K ∈ 𝒞, ∀ stream, range stream = K → ∃ name, name = K ∧ ∃ T, ∀ t ≥ T, M (prefix stream t) = name. The infinite witness is inside the premise; the denied learner would be one global function for the entire fixed class.
```

**Algorithm, input access and effectiveness.** A semantic learner is an arbitrary total List Nat → Set Nat function. Its output is the entire language set; semanticNaming is identity denotation. This is a semantic representation, not a natural-number program code or a membership-decision algorithm. Existential learners may depend on the fixed class but must work uniformly over all its target languages and presentations. No effectiveness, oracle model, complexity, source-specific construction or proof of a construction is asserted.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- The two premises must both hold; an infinite member alone does not invoke this target.
- 𝒞 need not be countable or effectively indexed.
- No one universal failing target or effective counterexample generator is supplied by this negated existence statement.
- The empty language is included among finite representations, while its Nat-valued text-identification clause is vacuous.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.IdentifiesClass`, `GenLimit.Gold.Text.IdentifiesLanguage`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.SemanticallyIdentifiable`, `GenLimit.Gold.Text.SemanticallyIdentifiesClass`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.semanticNaming`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S13: `GenLimit.Gold.Text.enumerationLearner_identifiesFamily_of_isInclusionAntichain`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:188`. Universe parameters: `(none)`. Supplemental labels: C02.

**Exact exported type:**

```lean
∀ {C : GenLimit.LanguageFamily},
  GenLimit.Gold.Text.IsInclusionAntichain C →
    GenLimit.Gold.Text.IdentifiesFamily C (GenLimit.Gold.Text.enumerationLearner C)
```

**Reconstruction.** If an indexed family has the property that inclusion between any two family languages implies equality of those languages, then the named positive-text enumerationLearner identifies every indexed language on every text for it. Equal languages at different indices are allowed; the antichain property is about sets, not distinctness of indices.

**Assumptions and binder scope:**

- Implicit C : Nat → Language.
- IsInclusionAntichain C, exactly ∀ i j, C i ⊆ C j → C i = C j. No effectiveness or injectivity condition.

**Expanded quantifiers and witness dependencies:**

```text
∀ {C}, (∀ i j, C i ⊆ C j → C i = C j) → ∀ z stream, range stream = C z → ∃ n : Nat, C n = C z ∧ ∃ T, ∀ t ≥ T, enumerationLearner C (prefix stream t) = n. The learner is fixed for C before z/stream. n and T are inside the per-run conclusion; a companion theorem determines n as leastCover.
```

**Algorithm, input access and effectiveness.** At history h, compatibleIndices C h filters i < h.length by ∀ u ∈ h, u ∈ C i. enumerationLearner outputs the minimum of this finite set, or 0 if it is empty. Its only varying input is the finite positive history; C is a fixed semantic family. It does not read z, the true language, a leastCover value or future text. In particular it does not test C z ⊆ C i: that full-target condition defines the semantic limit index leastCover used in the conclusion. Classical membership filtering is used without a computability or oracle assumption on C. With additional uniform membership decisions the finite checks are executable, but that realization is not part of these targets. The definition recomputes from a history; it has no additional state/update field.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- No claim is made that n = z. Duplicate equal languages satisfy the stated antichain condition.
- If the family has only empty languages, no positive texts exist and identification is vacuous. If it contains an empty and a nonempty language it cannot satisfy this antichain predicate.
- No uniform convergence bound, decidable inclusion test, computable naming or ordinal/canonical index coding is supplied.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.IdentifiesFamily`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.IsInclusionAntichain`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.PositiveCompatible`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.compatibleIndices`, `GenLimit.Gold.Text.enumerationLearner`, `GenLimit.Gold.Text.enumerationLearnerWithFallback`, `GenLimit.Gold.Text.familyNaming`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.textPrefix`.


## S14: `GenLimit.Gold.Text.enumerationLearner_identifiesOnText`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:166`. Universe parameters: `(none)`. Supplemental labels: C02.

**Exact exported type:**

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {z : Nat},
  GenLimit.Presents stream (C z) →
    @Eq.{1} GenLimit.Language (C (GenLimit.Gold.Text.leastCover C z)) (C z) →
      @GenLimit.Gold.Text.IdentifiesOnText.{0} Nat (GenLimit.Gold.Text.familyNaming C)
        (GenLimit.Gold.Text.enumerationLearner C) stream (C z)
```

**Reconstruction.** For a text presenting C z, if the language at the least index covering C z is in fact exactly C z, the named positive-text enumerationLearner identifies C z on that text. Both premises are required; mere coverage by a least candidate does not imply correct target denotation.

**Assumptions and binder scope:**

- Implicit C, stream : Nat → Nat and z : Nat.
- Presents stream (C z), then the separate equality C (leastCover C z) = C z.

**Expanded quantifiers and witness dependencies:**

```text
∀ {C stream z}, range stream = C z → C (leastCover C z) = C z → ∃ n : Nat, C n = C z ∧ ∃ T, ∀ t ≥ T, enumerationLearner C (prefix stream t) = n. leastCover = min {i | C z ⊆ C i}; n/T are formally quantified after both premises. Companion stabilization chooses leastCover as a suitable n.
```

**Algorithm, input access and effectiveness.** At history h, compatibleIndices C h filters i < h.length by ∀ u ∈ h, u ∈ C i. enumerationLearner outputs the minimum of this finite set, or 0 if it is empty. Its only varying input is the finite positive history; C is a fixed semantic family. It does not read z, the true language, a leastCover value or future text. In particular it does not test C z ⊆ C i: that full-target condition defines the semantic limit index leastCover used in the conclusion. Classical membership filtering is used without a computability or oracle assumption on C. With additional uniform membership decisions the finite checks are executable, but that realization is not part of these targets. The definition recomputes from a history; it has no additional state/update field.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- The equality premise cannot be dropped: leastCover may denote a strict superset in an arbitrary family.
- The theorem is stated for a single universally quantified presented run; it does not assume or conclude an inclusion antichain for the entire family.
- C may duplicate languages; the selected correct index need not be z.
- No valid text presents C z = ∅.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.PositiveCompatible`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.compatibleIndices`, `GenLimit.Gold.Text.enumerationLearner`, `GenLimit.Gold.Text.enumerationLearnerWithFallback`, `GenLimit.Gold.Text.familyNaming`, `GenLimit.Gold.Text.leastCover`, `GenLimit.Gold.Text.leastCover._proof_1`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.textPrefix`.


## S15: `GenLimit.Gold.Text.enumerationLearner_stabilizesTo_leastCover`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:155`. Universe parameters: `(none)`. Supplemental labels: C02.

**Exact exported type:**

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {z : Nat},
  GenLimit.Presents stream (C z) →
    @GenLimit.StabilizesTo.{0} Nat
      (fun t => GenLimit.Gold.Text.enumerationLearner C (@GenLimit.textPrefix.{0} Nat stream t))
      (GenLimit.Gold.Text.leastCover C z)
```

**Reconstruction.** On every positive text presenting C z, regardless of antichain or equality assumptions, enumerationLearner C eventually outputs the least index i whose language C i contains C z, and keeps exactly that index forever. The conclusion permits that covering language to strictly contain the target, so this theorem alone is not target identification.

**Assumptions and binder scope:**

- Implicit C : Nat → Language, stream : Nat → Nat and z : Nat.
- The sole proposition premise is Presents stream (C z). No equality C (leastCover C z) = C z or antichain assumption occurs.

**Expanded quantifiers and witness dependencies:**

```text
∀ {C stream z}, range stream = C z → ∃ T, ∀ t ≥ T, enumerationLearner C (prefix stream t) = leastCover C z, where leastCover C z = min {i : Nat | C z ⊆ C i}. The limit depends only on C,z, not on the particular presentation. T can depend on C,z,stream. Existence of a covering index follows since z covers itself.
```

**Algorithm, input access and effectiveness.** At history h, compatibleIndices C h filters i < h.length by ∀ u ∈ h, u ∈ C i. enumerationLearner outputs the minimum of this finite set, or 0 if it is empty. Its only varying input is the finite positive history; C is a fixed semantic family. It does not read z, the true language, a leastCover value or future text. In particular it does not test C z ⊆ C i: that full-target condition defines the semantic limit index leastCover used in the conclusion. Classical membership filtering is used without a computability or oracle assumption on C. With additional uniform membership decisions the finite checks are executable, but that realization is not part of these targets. The definition recomputes from a history; it has no additional state/update field.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- This fixes an index, not merely its denotation. Repeated equal languages are permitted and the index can differ from z.
- The algorithm only checks finitely many i < prefix.length at each step; leastCover itself is not given to it.
- At [] or an exhausted candidate set the fallback is 0, whether compatible or not. Such early outputs do not weaken eventual stabilization.
- The Nat.find subset predicate defining leastCover is classical; no computable full-language inclusion oracle is certified.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.PositiveCompatible`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.compatibleIndices`, `GenLimit.Gold.Text.enumerationLearner`, `GenLimit.Gold.Text.enumerationLearnerWithFallback`, `GenLimit.Gold.Text.leastCover`, `GenLimit.Gold.Text.leastCover._proof_1`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.textPrefix`.


## S16: `GenLimit.Gold.Text.eventually_sample_eq_of_finite`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Finite:71`. Universe parameters: `(none)`. Supplemental labels: C05.

**Exact exported type:**

```lean
∀ {stream : Nat → Nat} {L : GenLimit.Language},
  GenLimit.Presents stream L →
    @Set.Finite.{0} Nat L →
      ∃ T,
        ∀ (t : Nat),
          @LE.le.{0} Nat instLENat T t → @Eq.{1} (Set.{0} Nat) (@Finset.toSet.{0} Nat (GenLimit.sample stream t)) L
```

**Reconstruction.** For a positive stream whose range is a finite language L, there is a time after which the finite set of values seen in every prefix has underlying set exactly L. This is a deterministic fact about a supplied stream, not a learner existence or a probabilistic sampling theorem.

**Assumptions and binder scope:**

- Implicit stream : Nat → Nat and L : Language.
- Presents stream L, then Set.Finite L.

**Expanded quantifiers and witness dependencies:**

```text
∀ {stream L}, range stream = L → L.Finite → ∃ T : Nat, ∀ t : Nat, T ≤ t → (sample stream t : Set Nat) = L. sample stream t = Finset.image stream (Finset.range t); T may depend on the entire presenting stream and L.
```

**Algorithm, input access and effectiveness.** The finite set sample stream t is directly computable from the first t values; the theorem does not compute a time after which all values have appeared or provide an observable stopping test. No probability distribution or independent draws are involved.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- t counts positions 0 through t−1; stream t is not yet sampled.
- Arbitrary repetitions, order and arbitrarily delayed first occurrences are allowed. No cardinality-only time bound follows from the type.
- The empty L case has an inconsistent presentation premise, since range stream is nonempty.

**Native dependency dossiers reviewed:** `GenLimit.Language`, `GenLimit.Presents`, `GenLimit.sample`.


## S17: `GenLimit.Gold.Text.exists_locking_of_identifiesLanguage`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Locking:335`. Universe parameters: `(none)`. Supplemental labels: C06.

**Exact exported type:**

```lean
∀ {M : GenLimit.Gold.Text.TextLearner.{0} GenLimit.Language} {L : GenLimit.Language},
  @Set.Nonempty.{0} Nat L →
    @GenLimit.Gold.Text.IdentifiesLanguage.{0} GenLimit.Language GenLimit.Gold.Text.semanticNaming M L →
      ∃ σ, GenLimit.Gold.Text.IsLocking M L σ
```

**Reconstruction.** If L is nonempty and one fixed semantic learner identifies L on every positive text for it, then there exists a finite history σ entirely in L at which the learner already outputs L and from which every finite continuation consisting only of elements of L keeps the output exactly L. The correctness conjunct is part of IsLocking and must be retained.

**Assumptions and binder scope:**

- Implicit M : List Nat → Language and L : Language.
- Set.Nonempty L.
- IdentifiesLanguage semanticNaming M L, quantifying over every stream presenting L.

**Expanded quantifiers and witness dependencies:**

```text
∀ {M L}, L.Nonempty → (∀ stream, range stream = L → ∃ name, name = L ∧ ∃ T, ∀ t ≥ T, M (prefix stream t) = name) → ∃ σ : List Nat, HistoryIn σ L ∧ M σ = L ∧ ∀ τ : List Nat, HistoryIn τ L → M (σ ++ τ) = L. σ is chosen after M,L and before all τ; there is no given-text quantifier outside it.
```

**Algorithm, input access and effectiveness.** M is a fixed arbitrary total semantic learner List Nat → Set Nat. The conclusion is existence of a finite legal history, not an algorithm receiving M/L and computing such a history, not a computable convergence test and not a claim that every presented run reaches this particular history. There is no stream argument in the theorem. Legal continuations are all finite lists whose entries lie in L; they need not be complete texts, have distinct entries, or contain any new value.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- Nonempty L is an explicit hypothesis and is not replaced with infinite or finite L.
- σ is one legal history, not asserted to be a prefix of every or any particular supplied text. It need not have distinct entries; the definition allows σ = [].
- Every τ is a finite legal continuation, including [] and lists with repetitions; there is no requirement that σ ++ τ enumerate all of L.
- Existence has no effective search, length bound, canonical choice or recognizable-locking certificate.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.HistoryIn`, `GenLimit.Gold.Text.IdentifiesLanguage`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.IsLocking`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.semanticNaming`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S18: `GenLimit.Gold.Text.exists_stabilizing_of_identifiesLanguage`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Locking:299`. Universe parameters: `(none)`. Supplemental labels: C06.

**Exact exported type:**

```lean
∀ {M : GenLimit.Gold.Text.TextLearner.{0} GenLimit.Language} {L : GenLimit.Language},
  @Set.Nonempty.{0} Nat L →
    @GenLimit.Gold.Text.IdentifiesLanguage.{0} GenLimit.Language GenLimit.Gold.Text.semanticNaming M L →
      ∃ σ, GenLimit.Gold.Text.IsStabilizing M L σ
```

**Reconstruction.** If L is nonempty and a fixed semantic learner identifies L on every positive text, then some finite history σ consisting of elements of L has the property that every finite L-valued continuation leaves the learner’s output unchanged from M σ. IsStabilizing itself contains no conjunct M σ = L; that distinction is preserved instead of silently strengthening its definition.

**Assumptions and binder scope:**

- Implicit semantic learner M and language L.
- Set.Nonempty L followed by IdentifiesLanguage semanticNaming M L.

**Expanded quantifiers and witness dependencies:**

```text
∀ {M L}, L.Nonempty → (∀ stream, range stream = L → ∃ name, name = L ∧ ∃ T, ∀ t ≥ T, M (prefix stream t) = name) → ∃ σ : List Nat, HistoryIn σ L ∧ ∀ τ : List Nat, HistoryIn τ L → M (σ ++ τ) = M σ. σ may depend on M,L, but must work for every finite legal τ. The IsStabilizing expansion has no separate M σ = L requirement.
```

**Algorithm, input access and effectiveness.** M is a fixed arbitrary total semantic learner List Nat → Set Nat. The conclusion is existence of a finite legal history, not an algorithm receiving M/L and computing such a history, not a computable convergence test and not a claim that every presented run reaches this particular history. There is no stream argument in the theorem. Legal continuations are all finite lists whose entries lie in L; they need not be complete texts, have distinct entries, or contain any new value.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- No arbitrary observed-run prefix is given, and no assertion that all runs encounter this σ is part of the type.
- Legal σ/τ may be empty or contain repeats. No completeness condition applies to either finite list.
- This reconstructs the exact predicate rather than importing the stronger IsLocking conjunction.
- No effective method to find σ or bound its length is supplied.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.HistoryIn`, `GenLimit.Gold.Text.IdentifiesLanguage`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.IsStabilizing`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.semanticNaming`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S19: `GenLimit.Gold.Text.finiteLanguages_semanticallyIdentifiable`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Finite:133`. Universe parameters: `(none)`. Supplemental labels: C05.

**Exact exported type:**

```lean
GenLimit.Gold.Text.SemanticallyIdentifiable GenLimit.Gold.Text.finiteLanguages
```

**Reconstruction.** There exists one total set-valued learner on finite positive histories that eventually outputs exactly L on every positive text for every finite language L. The type names no particular learner or representation transformation; it asserts semantic existence for the whole finite-language class.

**Assumptions and binder scope:**

- No binders or hypotheses. The class is finiteLanguages = {L | Set.Finite L}, and semanticNaming is identity on Language.

**Expanded quantifiers and witness dependencies:**

```text
∃ M : List Nat → Set Nat, ∀ L : Set Nat, L.Finite → ∀ stream : Nat → Nat, range stream = L → ∃ name : Set Nat, name = L ∧ ∃ T : Nat, ∀ t ≥ T, M (prefix stream t) = name. M precedes all L/texts; name/T follow each run.
```

**Algorithm, input access and effectiveness.** A semantic learner is an arbitrary total List Nat → Set Nat function. Its output is the entire language set; semanticNaming is identity denotation. This is a semantic representation, not a natural-number program code or a membership-decision algorithm. Existential learners may depend on the fixed class but must work uniformly over all its target languages and presentations. No effectiveness, oracle model, complexity, source-specific construction or proof of a construction is asserted.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- No existential witness is selected from proof code. The separately supplied finiteLearner results describe a Finset-valued learner, while this type is set-valued.
- The empty finite language has no valid Nat-valued positive text; that clause is vacuous.
- No time uniform over finite targets or their presentation schedules is given.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.IdentifiesClass`, `GenLimit.Gold.Text.IdentifiesLanguage`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.SemanticallyIdentifiable`, `GenLimit.Gold.Text.SemanticallyIdentifiesClass`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.finiteLanguages`, `GenLimit.Gold.Text.semanticNaming`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S20: `GenLimit.Gold.Text.finiteLearner_identifiesOnText`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Finite:96`. Universe parameters: `(none)`. Supplemental labels: C05.

**Exact exported type:**

```lean
∀ {stream : Nat → Nat} {L : GenLimit.Language},
  GenLimit.Presents stream L →
    @Set.Finite.{0} Nat L →
      @GenLimit.Gold.Text.IdentifiesOnText.{0} (Finset.{0} Nat) GenLimit.Gold.Text.finiteNaming
        GenLimit.Gold.Text.finiteLearner stream L
```

**Reconstruction.** For any stream presenting a finite language L, the specifically defined observed-elements learner finiteLearner identifies L on that stream using Finset Nat names interpreted as their underlying sets. One finite-set name denoting L becomes the exact fixed output.

**Assumptions and binder scope:**

- Implicit stream : Nat → Nat and L : Language.
- Presents stream L followed by Set.Finite L.

**Expanded quantifiers and witness dependencies:**

```text
∀ {stream L}, range stream = L → L.Finite → ∃ F : Finset Nat, (F : Set Nat) = L ∧ ∃ T, ∀ t ≥ T, finiteLearner (prefix stream t) = F. finiteLearner h = h.toFinset. F/T follow stream,L; the learner and naming are fixed.
```

**Algorithm, input access and effectiveness.** finiteLearner is exactly List.toFinset on natural-number histories using decidable Nat equality. It can be realized by starting with ∅ and inserting each new observed value, outputting the accumulated Finset; that is a description of this finite-list operation, not certification of the theorem’s proof. It receives no target, target size, future stream, family oracle or end-of-data signal. The concrete finite-list operation is directly computable, while no formal computability/complexity certificate occurs in the theorem statement.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- The prefix may repeat elements or delay first occurrences arbitrarily; only exact range equality and finiteness are assumed.
- At [] finiteLearner outputs ∅. Empty L still has no valid total Nat-valued presentation.
- No bound on T from |L| alone, learning termination announcement, or behavior guarantee for incomplete/incorrect target presentations occurs.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.finiteLearner`, `GenLimit.Gold.Text.finiteNaming`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S21: `GenLimit.Gold.Text.finite_tellTale_of_semantic_identification`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:123`. Universe parameters: `(none)`. Supplemental labels: C06.

**Exact exported type:**

```lean
∀ {M : GenLimit.Gold.Text.TextLearner.{0} GenLimit.Language} {𝒞 : Set.{0} GenLimit.Language} {L : GenLimit.Language},
  GenLimit.Gold.Text.SemanticallyIdentifiesClass M 𝒞 →
    @Membership.mem.{0, 0} GenLimit.Language (Set.{0} GenLimit.Language) (@Set.instMembership.{0} GenLimit.Language) 𝒞
        L →
      @Set.Infinite.{0} Nat L → ∃ D, GenLimit.Gold.Text.IsTellTale 𝒞 L D
```

**Reconstruction.** If a fixed semantic learner identifies an entire class 𝒞, and L is an infinite member of that class, then L contains a finite set D such that any class member K lying between D and L under inclusion must equal L. This excludes proper class sublanguages of L containing D; it does not make D distinguish L from all supersets or incomparable class members.

**Assumptions and binder scope:**

- Implicit M : List Nat → Language, 𝒞 : Set Language and L : Language.
- SemanticallyIdentifiesClass M 𝒞.
- L ∈ 𝒞.
- Set.Infinite L.

**Expanded quantifiers and witness dependencies:**

```text
∀ {M 𝒞 L}, (∀ K ∈ 𝒞, ∀ stream, range stream = K → ∃ name, name = K ∧ ∃ T, ∀ t ≥ T, M (prefix stream t) = name) → L ∈ 𝒞 → L.Infinite → ∃ D : Finset Nat, (D : Set Nat) ⊆ L ∧ ∀ K : Set Nat, K ∈ 𝒞 → (D : Set Nat) ⊆ K → K ⊆ L → K = L. D may depend on M,𝒞,L and is selected before K; no text parameter is supplied for D.
```

**Algorithm, input access and effectiveness.** The conclusion is semantic existence of a Finset Nat, not a procedure enumerating/finding a tell-tale, a uniform computable map L ↦ D, or a stopping test from observed data. The class and semantic learner may be arbitrary noncomputable mathematical objects. IsTellTale/Generic.IsFiniteTellTale are definition-valued predicates; they impose the stated subset/equality conditions but do not independently prove existence. No proof-body or witness-construction certification is performed.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- The infinite-L hypothesis is explicit and must not be dropped merely because a finite target could have a trivial finite tell-tale.
- D need not be nonempty and need not be a prefix, ordered list, canonical finite sample, or output of a named program.
- The K ⊆ L premise is essential; D ⊆ K alone does not force equality.
- No single D for the whole class, uniform size bound or computable tell-tale assignment is asserted.

**Native dependency dossiers reviewed:** `GenLimit.Generic.IsFiniteTellTale`, `GenLimit.Generic.Language`, `GenLimit.Generic.LanguageClass`, `GenLimit.Gold.Text.IdentifiesClass`, `GenLimit.Gold.Text.IdentifiesLanguage`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.IsTellTale`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.SemanticallyIdentifiesClass`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.semanticNaming`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S22: `GenLimit.Gold.Text.finite_tellTale_of_semanticallyIdentifiable`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:161`. Universe parameters: `(none)`. Supplemental labels: C06.

**Exact exported type:**

```lean
∀ {𝒞 : Set.{0} GenLimit.Language} {L : GenLimit.Language},
  GenLimit.Gold.Text.SemanticallyIdentifiable 𝒞 →
    @Membership.mem.{0, 0} GenLimit.Language (Set.{0} GenLimit.Language) (@Set.instMembership.{0} GenLimit.Language) 𝒞
        L →
      @Set.Infinite.{0} Nat L → ∃ D, GenLimit.Gold.Text.IsTellTale 𝒞 L D
```

**Reconstruction.** If a class is semantically identifiable, each supplied infinite member L has some finite tell-tale D contained in L that rules out all proper class sublanguages of L containing D. The learner is existentially assumed rather than supplied as an explicit parameter.

**Assumptions and binder scope:**

- Implicit 𝒞 : Set Language and L : Language.
- SemanticallyIdentifiable 𝒞 = ∃ M, SemanticallyIdentifiesClass M 𝒞.
- L ∈ 𝒞 followed by Set.Infinite L.

**Expanded quantifiers and witness dependencies:**

```text
∀ {𝒞 L}, (∃ M : List Nat → Set Nat, ∀ K ∈ 𝒞, ∀ stream, range stream = K → ∃ name, name = K ∧ ∃ T, ∀ t ≥ T, M (prefix stream t) = name) → L ∈ 𝒞 → L.Infinite → ∃ D : Finset Nat, (D : Set Nat) ⊆ L ∧ ∀ K ∈ 𝒞, (D : Set Nat) ⊆ K → K ⊆ L → K = L. The outer target depends on 𝒞,L; a witness D may be obtained using an existentially chosen learner, but no computable choice is specified.
```

**Algorithm, input access and effectiveness.** The conclusion is semantic existence of a Finset Nat, not a procedure enumerating/finding a tell-tale, a uniform computable map L ↦ D, or a stopping test from observed data. The class and semantic learner may be arbitrary noncomputable mathematical objects. IsTellTale/Generic.IsFiniteTellTale are definition-valued predicates; they impose the stated subset/equality conditions but do not independently prove existence. No proof-body or witness-construction certification is performed.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- D is per target L, chosen before all K; the statement does not give one finite set that works for every infinite member.
- Finite D can be empty; no nonempty, size, minimality, order or program-code restriction is stated.
- Tell-tale means exclusion of proper sublanguages between D and L, not separation from arbitrary distinct languages.
- The conclusion is not a uniform algorithmic characterization or a converse sufficiency theorem.

**Native dependency dossiers reviewed:** `GenLimit.Generic.IsFiniteTellTale`, `GenLimit.Generic.Language`, `GenLimit.Generic.LanguageClass`, `GenLimit.Gold.Text.IdentifiesClass`, `GenLimit.Gold.Text.IdentifiesLanguage`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.IsTellTale`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.SemanticallyIdentifiable`, `GenLimit.Gold.Text.SemanticallyIdentifiesClass`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.semanticNaming`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S23: `GenLimit.Gold.Text.identifiableWith_implies_semanticallyIdentifiable`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:95`. Universe parameters: `u_1`. Supplemental labels: C06.

**Exact exported type:**

```lean
∀ {Name : Type u_1} {N : GenLimit.Gold.Text.Naming.{u_1} Name} {𝒞 : Set.{0} GenLimit.Language},
  @GenLimit.Gold.Text.IdentifiableWith.{u_1} Name N 𝒞 → GenLimit.Gold.Text.SemanticallyIdentifiable 𝒞
```

**Reconstruction.** For any name type and any name-to-language map, existence of a total learner identifying a class with eventual fixed correct names implies existence of a total semantic set-valued learner identifying that same class. The semantic existence conclusion does not itself name its witness; the companion semanticLearner theorem gives the explicit denotation postcomposition.

**Assumptions and binder scope:**

- Implicit Name : Type u_1, N : Text.Naming Name and 𝒞 : Set Language.
- IdentifiableWith N 𝒞. Text.Naming only stores Name → Language; it has no right-inverse, injectivity or surjectivity requirement.

**Expanded quantifiers and witness dependencies:**

```text
∀ {Name N 𝒞}, (∃ M : List Nat → Name, ∀ L ∈ 𝒞, ∀ stream, range stream = L → ∃ n : Name, N.language n = L ∧ ∃ T, ∀ t ≥ T, M (prefix stream t) = n) → ∃ S : List Nat → Set Nat, ∀ L ∈ 𝒞, ∀ stream, range stream = L → ∃ name, name = L ∧ ∃ T, ∀ t ≥ T, S (prefix stream t) = name. Both M and S are before the class’s target/run quantifiers.
```

**Algorithm, input access and effectiveness.** This is semantic conversion of an existence guarantee. The explicit operation reviewed in semanticLearner is S h = N.language (M h). If N or M is noncomputable, the statement imposes no effective coding or executable compiler. No converse is stated.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- No extra coverage of N outside the identified class is required.
- A noninjective naming is allowed; fixed-name convergence of M suffices for set-output convergence after denotation.
- Empty-language positive-text clauses remain vacuous.
- The semantic conclusion is about set outputs, not membershipwise decisions or natural-number hypothesis codes.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.IdentifiableWith`, `GenLimit.Gold.Text.IdentifiesClass`, `GenLimit.Gold.Text.IdentifiesLanguage`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.SemanticallyIdentifiable`, `GenLimit.Gold.Text.SemanticallyIdentifiesClass`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.semanticNaming`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S24: `GenLimit.Gold.Text.identifiesClass_semanticLearner`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:84`. Universe parameters: `u_1`. Supplemental labels: C06.

**Exact exported type:**

```lean
∀ {Name : Type u_1} {N : GenLimit.Gold.Text.Naming.{u_1} Name} {M : GenLimit.Gold.Text.TextLearner.{u_1} Name}
  {𝒞 : Set.{0} GenLimit.Language},
  @GenLimit.Gold.Text.IdentifiesClass.{u_1} Name N M 𝒞 →
    GenLimit.Gold.Text.SemanticallyIdentifiesClass (@GenLimit.Gold.Text.semanticLearner.{u_1} Name N M) 𝒞
```

**Reconstruction.** For a fixed learner M and a fixed arbitrary name-to-language map N, if M identifies every language in 𝒞 using N, then the specifically defined semanticLearner N M identifies that class semantically. At each history it simply outputs the denotation N.language (M history).

**Assumptions and binder scope:**

- Implicit Name : Type u_1, N : Text.Naming Name, M : List Nat → Name and 𝒞 : Set Language.
- IdentifiesClass N M 𝒞. No injectivity/surjectivity/effectiveness of N is assumed.

**Expanded quantifiers and witness dependencies:**

```text
∀ {Name N M 𝒞}, (∀ L ∈ 𝒞, ∀ stream, range stream = L → ∃ n, N.language n = L ∧ ∃ T, ∀ t ≥ T, M (prefix stream t) = n) → ∀ L ∈ 𝒞, ∀ stream, range stream = L → ∃ name : Set Nat, name = L ∧ ∃ T, ∀ t ≥ T, semanticLearner N M (prefix stream t) = name. The converted function is fixed from N,M before all L/texts.
```

**Algorithm, input access and effectiveness.** semanticLearner N M history = N.language (M history), without extra observations, state or future data. This is a named semantic postcomposition. No computability of N, execution on a representation of arbitrary sets, or program transformation is certified.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- The premise is eventual fixed original name, and the conclusion is eventual fixed semantic set.
- The result is one direction only; no converse from semantic stabilization to stabilization of original codes is claimed.
- 𝒞 may be empty or arbitrary/unindexed. With an empty class the per-language property is vacuous, but the given learner remains a total function.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.IdentifiesClass`, `GenLimit.Gold.Text.IdentifiesLanguage`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.SemanticallyIdentifiesClass`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.semanticLearner`, `GenLimit.Gold.Text.semanticNaming`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S25: `GenLimit.Gold.Text.superfinite_not_identifiableWith`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:207`. Universe parameters: `u_1`. Supplemental labels: C06, C15, C16.

**Exact exported type:**

```lean
∀ {Name : Type u_1} (N : GenLimit.Gold.Text.Naming.{u_1} Name) {𝒞 : Set.{0} GenLimit.Language},
  GenLimit.Gold.Text.IsSuperfinite 𝒞 → Not (@GenLimit.Gold.Text.IdentifiableWith.{u_1} Name N 𝒞)
```

**Reconstruction.** For every name type and every naming of that type by languages, a class containing all finite languages and at least one infinite language is not identifiable by any total learner using that naming. The impossibility is uniform across arbitrary representations; no effective coding restriction weakens the learner quantification.

**Assumptions and binder scope:**

- Implicit Name : Type u_1; explicit N : Text.Naming Name.
- Implicit 𝒞 : Set Language and premise IsSuperfinite 𝒞 = finiteLanguages ⊆ 𝒞 ∧ ∃ L, L ∈ 𝒞 ∧ L.Infinite.

**Expanded quantifiers and witness dependencies:**

```text
∀ {Name}, ∀ N : Text.Naming Name, ∀ {𝒞}, ((∀ K, K.Finite → K ∈ 𝒞) ∧ (∃ L, L ∈ 𝒞 ∧ L.Infinite)) → ¬ ∃ M : List Nat → Name, ∀ L ∈ 𝒞, ∀ stream, range stream = L → ∃ n : Name, N.language n = L ∧ ∃ T, ∀ t ≥ T, M (prefix stream t) = n. The denied M could depend on N,𝒞 but must work across the class and all texts.
```

**Algorithm, input access and effectiveness.** The conclusion refutes existence of any total history-to-name function for the fixed N and 𝒞, not only one named algorithm. N is an arbitrary denotation map, without computability, surjectivity, injectivity or chosen nameOf requirements. No counterexample-generation program is stated.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- Both superfinite components are retained; an infinite member alone is insufficient for this premise.
- Name need not be Nat, countable or nonempty as a separate hypothesis.
- No one fixed failing target/text for all learners is asserted.
- Supplemental mapping repeats this same target under C06, C15 and C16; it is reconstructed once, not counted as three distinct theorems.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.ContainsAllFiniteLanguages`, `GenLimit.Gold.Text.IdentifiableWith`, `GenLimit.Gold.Text.IdentifiesClass`, `GenLimit.Gold.Text.IdentifiesLanguage`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.IsSuperfinite`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.Gold.Text.finiteLanguages`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## S26: `GenLimit.Gold.Text.superfinite_not_text_identifiable`

Exporter kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:216`. Universe parameters: `u_1`. Supplemental labels: C06, C15, C16.

**Exact exported type:**

```lean
∀ {Name : Type u_1} (N : GenLimit.Gold.Text.Naming.{u_1} Name) {𝒞 : Set.{0} GenLimit.Language},
  (∀ (F : Finset.{0} Nat),
      @Membership.mem.{0, 0} (Set.{0} Nat) (Set.{0} GenLimit.Language) (@Set.instMembership.{0} GenLimit.Language) 𝒞
        (@Finset.toSet.{0} Nat F)) →
    (∃ L,
        And
          (@Membership.mem.{0, 0} GenLimit.Language (Set.{0} GenLimit.Language)
            (@Set.instMembership.{0} GenLimit.Language) 𝒞 L)
          (@Set.Infinite.{0} Nat L)) →
      Not (@GenLimit.Gold.Text.IdentifiableWith.{u_1} Name N 𝒞)
```

**Reconstruction.** For every arbitrary naming, if a class contains each Finset Nat as a language and contains some infinite language, then no total learner identifies the class using that naming on all positive texts. This has explicit finite-representation and infinite-member premises rather than the IsSuperfinite abbreviation.

**Assumptions and binder scope:**

- Implicit Name : Type u_1; explicit N : Text.Naming Name; implicit 𝒞.
- ∀ F : Finset Nat, (F : Set Nat) ∈ 𝒞.
- ∃ L, L ∈ 𝒞 ∧ Set.Infinite L.

**Expanded quantifiers and witness dependencies:**

```text
∀ {Name}, ∀ N, ∀ {𝒞}, (∀ F : Finset Nat, (F : Set Nat) ∈ 𝒞) → (∃ L, L ∈ 𝒞 ∧ L.Infinite) → ¬ ∃ M : List Nat → Name, ∀ L ∈ 𝒞, ∀ stream, range stream = L → ∃ n, N.language n = L ∧ ∃ T, ∀ t ≥ T, M (prefix stream t) = n. The premise’s existential infinite language is separate from the universal target L inside the denied learner property.
```

**Algorithm, input access and effectiveness.** An arbitrary total name-valued learner is excluded for the fixed naming/class. No program coding, oracle, recursive learner class, finite-state restriction, effective adversary or constructive failing-text procedure occurs in the type.

**Edge cases and limits:**

- Paper-withheld interface reconstruction only: no source correspondence, proof-body correctness, witness-construction certification, fresh Lean compilation or human certification.
- Names/module-line anchors are frozen exporter locators, not source semantics. Lean/Mathlib standard meanings are trusted without a recursive library audit.
- No rate, sample/resource bound, computable stopping criterion, random law, loss, density, frequency or limsup interpretation is introduced. StabilizesTo is exact equality at every t ≥ a per-run T.
- All types and definition values are supplied export data; embedded ⋯ suppresses proof arguments and is not treated as a proof hole.
- Every Finset representation, including ∅, is required to belong to the class. No Nat-valued positive text presents ∅.
- No equality or decidability assumptions on N/Name are present; Text.Naming has only a denotation field.
- This is a negated existence of a globally successful learner, not failure on every target or a uniform one-text failure.
- The same exact target is mapped to C06/C15/C16 and reviewed only once as a unique target.

**Native dependency dossiers reviewed:** `GenLimit.Gold.Text.IdentifiableWith`, `GenLimit.Gold.Text.IdentifiesClass`, `GenLimit.Gold.Text.IdentifiesLanguage`, `GenLimit.Gold.Text.IdentifiesOnText`, `GenLimit.Gold.Text.Naming`, `GenLimit.Gold.Text.Naming.language`, `GenLimit.Gold.Text.Naming.mk`, `GenLimit.Gold.Text.TextLearner`, `GenLimit.IdentifiesInLimit`, `GenLimit.Language`, `GenLimit.Learner`, `GenLimit.Presents`, `GenLimit.StabilizesTo`, `GenLimit.textPrefix`.


## Exact recursive dependency dossiers

The following 72 records exhaust all supplied recursive dependencies beyond the 26 target statements above. Each has its exported kind/type and exact available definition value, plus a natural-language reconstruction. Proposition-valued definitions are predicates, not separate assertions that their conditions hold or that witnesses exist. No theorem proof value was supplied or read.


### `GenLimit.Generic.IsFiniteTellTale`

Kind: `definition`. Anchor: `GenLimit.Support.FiniteTellTale:21`.

A definition-valued predicate: (D : Set α) ⊆ L and ∀ K ∈ H, (D : Set α) ⊆ K → K ⊆ L → K = L. It asserts no witness existence by itself and does not distinguish L from arbitrary supersets/incomparable languages.

Exact type:

```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → GenLimit.Generic.Language.{u_1} α → Finset.{u_1} α → Prop
```

Exact definition value:

```lean
fun {α} H L T =>
  And (@HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) (@Finset.toSet.{u_1} α T) L)
    (∀ (K : GenLimit.Generic.Language.{u_1} α),
      @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
          (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) H K →
        @HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) (@Finset.toSet.{u_1} α T) K →
          @HasSubset.Subset.{u_1} (GenLimit.Generic.Language.{u_1} α) (@Set.instHasSubset.{u_1} α) K L →
            @Eq.{u_1 + 1} (GenLimit.Generic.Language.{u_1} α) K L)
```


### `GenLimit.Generic.Language`

Kind: `definition`. Anchor: `GenLimit.Core.GenericGeneration:21`.

For any α, a generic language is Set α.

Exact type:

```lean
Type u_1 → Type u_1
```

Exact definition value:

```lean
fun α => Set.{u_1} α
```


### `GenLimit.Generic.LanguageClass`

Kind: `definition`. Anchor: `GenLimit.Core.GenericGeneration:24`.

For any α, a generic class is Set (Set α).

Exact type:

```lean
Type u_1 → Type u_1
```

Exact definition value:

```lean
fun α => Set.{u_1} (GenLimit.Generic.Language.{u_1} α)
```


### `GenLimit.Gold.Abstract.Allowable`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:24`.

Object → Set (Nat → Info); an object may have zero or many allowable complete streams.

Exact type:

```lean
Type uInfo → Type uObject → Type (max uObject uInfo)
```

Exact definition value:

```lean
fun Info Object => Object → Set.{uInfo} (Nat → Info)
```


### `GenLimit.Gold.Abstract.CollapsingUncertainty`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:69`.

For every allowed target stream and each different object, eventually all subsequent prefixes are incompatible with that competitor; time may depend on the competitor.

Exact type:

```lean
{Info : Type u_1} → {Object : Type u_2} → GenLimit.Gold.Abstract.Allowable.{u_1, u_2} Info Object → Prop
```

Exact definition value:

```lean
fun {Info} {Object} allowable =>
  ∀ ⦃target : Object⦄ ⦃stream : Nat → Info⦄,
    @Membership.mem.{u_1, u_1} (Nat → Info) (Set.{u_1} (Nat → Info)) (@Set.instMembership.{u_1} (Nat → Info))
        (allowable target) stream →
      ∀ (object : Object),
        @Ne.{u_2 + 1} Object object target →
          ∃ T,
            ∀ (t : Nat),
              @LE.le.{0} Nat instLENat T t →
                Not
                  (@GenLimit.Gold.Abstract.Compatible.{u_1, u_2} Info Object allowable
                    (@GenLimit.textPrefix.{u_1} Info stream t) object)
```


### `GenLimit.Gold.Abstract.Compatible`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:40`.

A history is compatible with an object iff some stream allowable for it has exactly that history as its prefix of the same length.

Exact type:

```lean
{Info : Type u_1} →
  {Object : Type u_2} → GenLimit.Gold.Abstract.Allowable.{u_1, u_2} Info Object → List.{u_1} Info → Object → Prop
```

Exact definition value:

```lean
fun {Info} {Object} allowable history object =>
  ∃ stream,
    And
      (@Membership.mem.{u_1, u_1} (Nat → Info) (Set.{u_1} (Nat → Info)) (@Set.instMembership.{u_1} (Nat → Info))
        (allowable object) stream)
      (@Eq.{u_1 + 1} (List.{u_1} Info) (@GenLimit.textPrefix.{u_1} Info stream (@List.length.{u_1} Info history))
        history)
```


### `GenLimit.Gold.Abstract.Distinguishable`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:57`.

Any complete stream simultaneously allowable for two objects forces those objects equal. This is not a finite-prefix separation definition.

Exact type:

```lean
{Info : Type u_1} → {Object : Type u_2} → GenLimit.Gold.Abstract.Allowable.{u_1, u_2} Info Object → Prop
```

Exact definition value:

```lean
fun {Info} {Object} allowable =>
  ∀ ⦃object₁ object₂ : Object⦄ ⦃stream : Nat → Info⦄,
    @Membership.mem.{u_1, u_1} (Nat → Info) (Set.{u_1} (Nat → Info)) (@Set.instMembership.{u_1} (Nat → Info))
        (allowable object₁) stream →
      @Membership.mem.{u_1, u_1} (Nat → Info) (Set.{u_1} (Nat → Info)) (@Set.instMembership.{u_1} (Nat → Info))
          (allowable object₂) stream →
        @Eq.{u_2 + 1} Object object₁ object₂
```


### `GenLimit.Gold.Abstract.Identifiable`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:94`.

There exists one total finite-history learner satisfying Identifies.

Exact type:

```lean
{Name : Type u_1} →
  {Object : Type u_2} →
    {Info : Type u_3} →
      GenLimit.Gold.Abstract.Naming.{u_2, u_1} Name Object →
        GenLimit.Gold.Abstract.Allowable.{u_3, u_2} Info Object → Prop
```

Exact definition value:

```lean
fun {Name} {Object} {Info} naming allowable =>
  ∃ learner, @GenLimit.Gold.Abstract.Identifies.{u_1, u_2, u_3} Name Object Info naming allowable learner
```


### `GenLimit.Gold.Abstract.Identifies`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:86`.

For every object and every stream allowable for it, IdentifiesOn holds.

Exact type:

```lean
{Name : Type u_1} →
  {Object : Type u_2} →
    {Info : Type u_3} →
      GenLimit.Gold.Abstract.Naming.{u_2, u_1} Name Object →
        GenLimit.Gold.Abstract.Allowable.{u_3, u_2} Info Object → GenLimit.Learner.{u_3, u_1} Info Name → Prop
```

Exact definition value:

```lean
fun {Name} {Object} {Info} naming allowable learner =>
  ∀ (object : Object) (stream : Nat → Info),
    @Membership.mem.{u_3, u_3} (Nat → Info) (Set.{u_3} (Nat → Info)) (@Set.instMembership.{u_3} (Nat → Info))
        (allowable object) stream →
      @GenLimit.Gold.Abstract.IdentifiesOn.{u_1, u_2, u_3} Name Object Info naming learner stream object
```


### `GenLimit.Gold.Abstract.IdentifiesOn`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:78`.

IdentifiesInLimit using naming.denotes for this learner, stream and object.

Exact type:

```lean
{Name : Type u_1} →
  {Object : Type u_2} →
    {Info : Type u_3} →
      GenLimit.Gold.Abstract.Naming.{u_2, u_1} Name Object →
        GenLimit.Learner.{u_3, u_1} Info Name → (Nat → Info) → Object → Prop
```

Exact definition value:

```lean
fun {Name} {Object} {Info} naming learner stream object =>
  @GenLimit.IdentifiesInLimit.{u_3, u_1, u_2} Info Name Object
    (@GenLimit.Gold.Abstract.Naming.denotes.{u_2, u_1} Name Object naming) learner stream object
```


### `GenLimit.Gold.Abstract.Naming`

Kind: `inductive`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:33`.

A record carrying denotes, nameOf and a right-inverse law; see Naming.mk.

Exact type:

```lean
Type uName → Type uObject → Type (max uName uObject)
```

Constructors: `GenLimit.Gold.Abstract.Naming.mk`.


### `GenLimit.Gold.Abstract.Naming.denotes`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:34`.

First projection of the naming: the denotation of a name.

Exact type:

```lean
{Name : Type uName} →
  {Object : Type uObject} → GenLimit.Gold.Abstract.Naming.{uObject, uName} Name Object → Name → Object
```

Exact definition value:

```lean
fun Name Object self => self.1
```


### `GenLimit.Gold.Abstract.Naming.mk`

Kind: `constructor`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:33`.

Constructs a naming from denotes : Name → Object, nameOf : Object → Name and ∀ object, denotes (nameOf object) = object.

Exact type:

```lean
{Name : Type uName} →
  {Object : Type uObject} →
    (denotes : Name → Object) →
      (nameOf : Object → Name) →
        (∀ (object : Object), @Eq.{uObject + 1} Object (denotes (nameOf object)) object) →
          GenLimit.Gold.Abstract.Naming.{uObject, uName} Name Object
```


### `GenLimit.Gold.Abstract.Naming.nameOf`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:35`.

Second projection of the naming: a chosen name for every object.

Exact type:

```lean
{Name : Type uName} →
  {Object : Type uObject} → GenLimit.Gold.Abstract.Naming.{uObject, uName} Name Object → Object → Name
```

Exact definition value:

```lean
fun Name Object self => self.2
```


### `GenLimit.Gold.Abstract.allowableSequences`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:155`.

The set {stream | ∃ object, stream ∈ allowable object}; the union of all objects’ allowable complete streams.

Exact type:

```lean
{Info : Type u_1} →
  {Object : Type u_2} → GenLimit.Gold.Abstract.Allowable.{u_1, u_2} Info Object → Set.{u_1} (Nat → Info)
```

Exact definition value:

```lean
fun {Info} {Object} allowable =>
  @setOf.{u_1} (Nat → Info) fun stream =>
    ∃ object,
      @Membership.mem.{u_1, u_1} (Nat → Info) (Set.{u_1} (Nat → Info)) (@Set.instMembership.{u_1} (Nat → Info))
        (allowable object) stream
```


### `GenLimit.Gold.Abstract.firstCompatibleIndex`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:133`.

Classically choose the least natural i whose enumerated object is compatible with the history, using Nat.find; if no i exists return 0.

Exact type:

```lean
{Info : Type u_1} →
  {Object : Type u_2} → GenLimit.Gold.Abstract.Allowable.{u_1, u_2} Info Object → (Nat → Object) → List.{u_1} Info → Nat
```

Exact definition value:

```lean
fun {Info} {Object} allowable enumeration history =>
  @dite.{1} Nat (∃ i, @GenLimit.Gold.Abstract.Compatible.{u_1, u_2} Info Object allowable history (enumeration i))
    (Classical.propDecidable
      (∃ i, @GenLimit.Gold.Abstract.Compatible.{u_1, u_2} Info Object allowable history (enumeration i)))
    (fun h =>
      @Nat.find (fun n => @GenLimit.Gold.Abstract.Compatible.{u_1, u_2} Info Object allowable history (enumeration n))
        (fun a =>
          Classical.propDecidable
            (@GenLimit.Gold.Abstract.Compatible.{u_1, u_2} Info Object allowable history (enumeration a)))
        h)
    fun h => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))
```


### `GenLimit.Gold.Abstract.firstEnumerationIndex`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:100`.

Nat.find of enumeration n = object, with existence supplied by surjectivity and equality decided classically. It is the least preimage index, not a computably supplied inverse.

Exact type:

```lean
{Object : Type uObject} →
  (enumeration : Nat → Object) → @Function.Surjective.{1, uObject + 1} Nat Object enumeration → Object → Nat
```

Exact definition value:

```lean
fun {Object} enumeration henumeration object =>
  @Nat.find (fun n => @Eq.{uObject + 1} Object (enumeration n) object)
    (fun a => Classical.propDecidable (@Eq.{uObject + 1} Object (enumeration a) object)) ⋯
```


### `GenLimit.Gold.Abstract.identificationByEnumeration`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:145`.

Output naming.nameOf of enumeration at firstCompatibleIndex for the current history.

Exact type:

```lean
{Name : Type u_1} →
  {Object : Type u_2} →
    {Info : Type u_3} →
      GenLimit.Gold.Abstract.Naming.{u_2, u_1} Name Object →
        GenLimit.Gold.Abstract.Allowable.{u_3, u_2} Info Object → (Nat → Object) → GenLimit.Learner.{u_3, u_1} Info Name
```

Exact definition value:

```lean
fun {Name} {Object} {Info} naming allowable enumeration history =>
  @GenLimit.Gold.Abstract.Naming.nameOf.{u_2, u_1} Name Object naming
    (enumeration (@GenLimit.Gold.Abstract.firstCompatibleIndex.{u_3, u_2} Info Object allowable enumeration history))
```


### `GenLimit.Gold.Informant.IdentifiesOnInformant`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Model:136`.

∃ n, N.language n = L ∧ eventual fixed output n on the prefixes of info.

Exact type:

```lean
{Name : Type u_1} →
  GenLimit.Gold.Text.Naming.{u_1} Name →
    GenLimit.Gold.Informant.InformantLearner.{u_1} Name →
      GenLimit.Gold.Informant.InformantStream → GenLimit.Language → Prop
```

Exact definition value:

```lean
fun {Name} N M info L =>
  ∃ n,
    And (@Eq.{1} GenLimit.Language (@GenLimit.Gold.Text.Naming.language.{u_1} Name N n) L)
      (@GenLimit.StabilizesTo.{u_1} Name
        (fun t => M (@GenLimit.textPrefix.{0} GenLimit.Gold.Informant.InformantDatum info t)) n)
```


### `GenLimit.Gold.Informant.InformantCompatible`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Model:45`.

For every datum occurring in the finite history, its label is true iff its natural number belongs to the candidate language.

Exact type:

```lean
List.{0} GenLimit.Gold.Informant.InformantDatum → GenLimit.Language → Prop
```

Exact definition value:

```lean
fun history L =>
  ∀ (datum : GenLimit.Gold.Informant.InformantDatum),
    @Membership.mem.{0, 0} GenLimit.Gold.Informant.InformantDatum (List.{0} GenLimit.Gold.Informant.InformantDatum)
        (@List.instMembership.{0} GenLimit.Gold.Informant.InformantDatum) history datum →
      Iff (@Eq.{1} Bool (@Prod.snd.{0, 0} Nat Bool datum) Bool.true)
        (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) L (@Prod.fst.{0, 0} Nat Bool datum))
```


### `GenLimit.Gold.Informant.InformantComplete`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Model:35`.

For every natural u there is a time whose first component is u; labels are constrained separately.

Exact type:

```lean
GenLimit.Gold.Informant.InformantStream → Prop
```

Exact definition value:

```lean
fun info => ∀ (u : Nat), ∃ t, @Eq.{1} Nat (@Prod.fst.{0, 0} Nat Bool (info t)) u
```


### `GenLimit.Gold.Informant.InformantCorrect`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Model:31`.

At every time, the Boolean is true iff the first component belongs to L.

Exact type:

```lean
GenLimit.Gold.Informant.InformantStream → GenLimit.Language → Prop
```

Exact definition value:

```lean
fun info L =>
  ∀ (t : Nat),
    Iff (@Eq.{1} Bool (@Prod.snd.{0, 0} Nat Bool (info t)) Bool.true)
      (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) L
        (@Prod.fst.{0, 0} Nat Bool (info t)))
```


### `GenLimit.Gold.Informant.InformantDatum`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Model:25`.

Nat × Bool: a natural and its Boolean label.

Exact type:

```lean
Type
```

Exact definition value:

```lean
Prod.{0, 0} Nat Bool
```


### `GenLimit.Gold.Informant.InformantLearner`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Model:132`.

A total function List InformantDatum → Name.

Exact type:

```lean
Type u_1 → Type (max u_1 0)
```

Exact definition value:

```lean
fun Name => List.{0} GenLimit.Gold.Informant.InformantDatum → Name
```


### `GenLimit.Gold.Informant.InformantStream`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Model:28`.

Nat → InformantDatum.

Exact type:

```lean
Type
```

Exact definition value:

```lean
Nat → GenLimit.Gold.Informant.InformantDatum
```


### `GenLimit.Gold.Informant.IsInformantFor`

Kind: `inductive`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Model:39`.

A Prop record packaging InformantCorrect and InformantComplete.

Exact type:

```lean
GenLimit.Gold.Informant.InformantStream → GenLimit.Language → Prop
```

Constructors: `GenLimit.Gold.Informant.IsInformantFor.mk`.


### `GenLimit.Gold.Informant.IsInformantFor.mk`

Kind: `constructor`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Model:39`.

Constructs IsInformantFor from BOTH correctness and completeness proofs for the same info and L.

Exact type:

```lean
∀ {info : GenLimit.Gold.Informant.InformantStream} {L : GenLimit.Language},
  GenLimit.Gold.Informant.InformantCorrect info L →
    GenLimit.Gold.Informant.InformantComplete info → GenLimit.Gold.Informant.IsInformantFor info L
```


### `GenLimit.Gold.Informant.informantCompatibleIndices`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:46`.

The finite set of i < history.length with InformantCompatible history (C i); classical proposition decision appears in dependency metadata.

Exact type:

```lean
GenLimit.LanguageFamily → List.{0} GenLimit.Gold.Informant.InformantDatum → Finset.{0} Nat
```

Exact definition value:

```lean
fun C history =>
  {i ∈ Finset.range (@List.length.{0} GenLimit.Gold.Informant.InformantDatum history) |
    GenLimit.Gold.Informant.InformantCompatible history (C i)}
```


### `GenLimit.Gold.Informant.informantEnumerationLearner`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:69`.

informantEnumerationLearnerWithFallback C 0.

Exact type:

```lean
GenLimit.LanguageFamily → GenLimit.Gold.Informant.InformantLearner.{0} Nat
```

Exact definition value:

```lean
fun C =>
  GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback C
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```


### `GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:61`.

Use leastCandidateWithFallback on informantCompatibleIndices with the supplied fallback.

Exact type:

```lean
GenLimit.LanguageFamily → Nat → GenLimit.Gold.Informant.InformantLearner.{0} Nat
```

Exact definition value:

```lean
fun C fallback history =>
  @GenLimit.Support.leastCandidateWithFallback.{0} Nat Nat.instLinearOrder
    (GenLimit.Gold.Informant.informantCompatibleIndices C history) fallback
```


### `GenLimit.Gold.Informant.leastEqualName`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:27`.

leastEquivalentIndex C z: the least n with C n = C z, using extensional equality of languages.

Exact type:

```lean
GenLimit.LanguageFamily → Nat → Nat
```

Exact definition value:

```lean
fun C z => @GenLimit.Support.leastEquivalentIndex.{0} GenLimit.Language C z
```


### `GenLimit.Gold.Text.ContainsAllFiniteLanguages`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:171`.

finiteLanguages ⊆ 𝒞.

Exact type:

```lean
Set.{0} GenLimit.Language → Prop
```

Exact definition value:

```lean
fun 𝒞 =>
  @HasSubset.Subset.{0} (Set.{0} GenLimit.Language) (@Set.instHasSubset.{0} GenLimit.Language)
    GenLimit.Gold.Text.finiteLanguages 𝒞
```


### `GenLimit.Gold.Text.HistoryIn`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Locking:30`.

Every natural occurring in the finite list history belongs to L; repeats and the empty list are allowed.

Exact type:

```lean
List.{0} Nat → GenLimit.Language → Prop
```

Exact definition value:

```lean
fun history L =>
  ∀ (x : Nat),
    @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) history x →
      @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) L x
```


### `GenLimit.Gold.Text.IdentifiableWith`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:50`.

∃ M, IdentifiesClass N M 𝒞, with fixed name type and naming.

Exact type:

```lean
{Name : Type u_1} → GenLimit.Gold.Text.Naming.{u_1} Name → Set.{0} GenLimit.Language → Prop
```

Exact definition value:

```lean
fun {Name} N 𝒞 => ∃ M, @GenLimit.Gold.Text.IdentifiesClass.{u_1} Name N M 𝒞
```


### `GenLimit.Gold.Text.IdentifiesClass`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:44`.

For every L ∈ 𝒞, IdentifiesLanguage N M L.

Exact type:

```lean
{Name : Type u_1} →
  GenLimit.Gold.Text.Naming.{u_1} Name → GenLimit.Gold.Text.TextLearner.{u_1} Name → Set.{0} GenLimit.Language → Prop
```

Exact definition value:

```lean
fun {Name} N M 𝒞 =>
  ∀ (L : GenLimit.Language),
    @Membership.mem.{0, 0} GenLimit.Language (Set.{0} GenLimit.Language) (@Set.instMembership.{0} GenLimit.Language) 𝒞
        L →
      @GenLimit.Gold.Text.IdentifiesLanguage.{u_1} Name N M L
```


### `GenLimit.Gold.Text.IdentifiesFamily`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:59`.

∀ z stream, Presents stream (C z) → IdentifiesOnText (familyNaming C) M stream (C z).

Exact type:

```lean
GenLimit.LanguageFamily → GenLimit.Gold.Text.TextLearner.{0} Nat → Prop
```

Exact definition value:

```lean
fun C M =>
  ∀ (z : Nat) (stream : Nat → Nat),
    GenLimit.Presents stream (C z) →
      @GenLimit.Gold.Text.IdentifiesOnText.{0} Nat (GenLimit.Gold.Text.familyNaming C) M stream (C z)
```


### `GenLimit.Gold.Text.IdentifiesLanguage`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:39`.

For every stream, Presents stream L → IdentifiesOnText N M stream L.

Exact type:

```lean
{Name : Type u_1} →
  GenLimit.Gold.Text.Naming.{u_1} Name → GenLimit.Gold.Text.TextLearner.{u_1} Name → GenLimit.Language → Prop
```

Exact definition value:

```lean
fun {Name} N M L =>
  ∀ (stream : Nat → Nat), GenLimit.Presents stream L → @GenLimit.Gold.Text.IdentifiesOnText.{u_1} Name N M stream L
```


### `GenLimit.Gold.Text.IdentifiesOnText`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:33`.

IdentifiesInLimit for the naming language map, the learner, a Nat-valued stream and target language.

Exact type:

```lean
{Name : Type u_1} →
  GenLimit.Gold.Text.Naming.{u_1} Name →
    GenLimit.Gold.Text.TextLearner.{u_1} Name → (Nat → Nat) → GenLimit.Language → Prop
```

Exact definition value:

```lean
fun {Name} N M stream L =>
  @GenLimit.IdentifiesInLimit.{0, u_1, 0} Nat Name GenLimit.Language (@GenLimit.Gold.Text.Naming.language.{u_1} Name N)
    M stream L
```


### `GenLimit.Gold.Text.IsInclusionAntichain`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:178`.

∀ i j, C i ⊆ C j → C i = C j. Equal languages at different indices are permitted; this does not require i = j.

Exact type:

```lean
GenLimit.LanguageFamily → Prop
```

Exact definition value:

```lean
fun C =>
  ∀ (i j : Nat),
    @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) (C i) (C j) →
      @Eq.{1} GenLimit.Language (C i) (C j)
```


### `GenLimit.Gold.Text.IsLocking`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Locking:69`.

HistoryIn σ L ∧ M σ = L ∧ ∀ τ, HistoryIn τ L → M (σ ++ τ) = L. All finite legal continuations preserve a correct output.

Exact type:

```lean
GenLimit.Gold.Text.TextLearner.{0} GenLimit.Language → GenLimit.Language → List.{0} Nat → Prop
```

Exact definition value:

```lean
fun M L σ =>
  And (GenLimit.Gold.Text.HistoryIn σ L)
    (And (@Eq.{1} GenLimit.Language (M σ) L)
      (∀ (τ : List.{0} Nat),
        GenLimit.Gold.Text.HistoryIn τ L →
          @Eq.{1} GenLimit.Language
            (M
              (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
                (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) σ τ))
            L))
```


### `GenLimit.Gold.Text.IsStabilizing`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Locking:62`.

HistoryIn σ L ∧ ∀ τ, HistoryIn τ L → M (σ ++ τ) = M σ. No correctness conjunct M σ = L is part of this predicate.

Exact type:

```lean
GenLimit.Gold.Text.TextLearner.{0} GenLimit.Language → GenLimit.Language → List.{0} Nat → Prop
```

Exact definition value:

```lean
fun M L σ =>
  And (GenLimit.Gold.Text.HistoryIn σ L)
    (∀ (τ : List.{0} Nat),
      GenLimit.Gold.Text.HistoryIn τ L →
        @Eq.{1} GenLimit.Language
          (M
            (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
              (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) σ τ))
          (M σ))
```


### `GenLimit.Gold.Text.IsSuperfinite`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:176`.

ContainsAllFiniteLanguages 𝒞 ∧ ∃ L, L ∈ 𝒞 ∧ Set.Infinite L.

Exact type:

```lean
Set.{0} GenLimit.Language → Prop
```

Exact definition value:

```lean
fun 𝒞 =>
  And (GenLimit.Gold.Text.ContainsAllFiniteLanguages 𝒞)
    (∃ L,
      And
        (@Membership.mem.{0, 0} GenLimit.Language (Set.{0} GenLimit.Language)
          (@Set.instMembership.{0} GenLimit.Language) 𝒞 L)
        (@Set.Infinite.{0} Nat L))
```


### `GenLimit.Gold.Text.IsTellTale`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:28`.

A definition alias for Generic.IsFiniteTellTale Nat 𝒞 L D; D is a Finset Nat, D ⊆ L, and no proper sublanguage K ∈ 𝒞 between D and L is allowed. It is a predicate, not an existence theorem.

Exact type:

```lean
Set.{0} GenLimit.Language → GenLimit.Language → Finset.{0} Nat → Prop
```

Exact definition value:

```lean
fun 𝒞 L D => @GenLimit.Generic.IsFiniteTellTale.{0} Nat 𝒞 L D
```


### `GenLimit.Gold.Text.Naming`

Kind: `inductive`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:25`.

A record containing only a denotation Name → Language; no coverage/right-inverse condition.

Exact type:

```lean
Type u_1 → Type u_1
```

Constructors: `GenLimit.Gold.Text.Naming.mk`.


### `GenLimit.Gold.Text.Naming.language`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:26`.

Projection of the name-to-language map.

Exact type:

```lean
{Name : Type u_1} → GenLimit.Gold.Text.Naming.{u_1} Name → Name → GenLimit.Language
```

Exact definition value:

```lean
fun Name self => self.1
```


### `GenLimit.Gold.Text.Naming.mk`

Kind: `constructor`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:25`.

Construct a Text.Naming from any Name → Language function.

Exact type:

```lean
{Name : Type u_1} → (Name → GenLimit.Language) → GenLimit.Gold.Text.Naming.{u_1} Name
```


### `GenLimit.Gold.Text.PositiveCompatible`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Consistency:19`.

Every observed natural belongs to L, with no negative data and no assertion that all of L has been observed.

Exact type:

```lean
List.{0} Nat → GenLimit.Language → Prop
```

Exact definition value:

```lean
fun history L =>
  ∀ (u : Nat),
    @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) history u →
      @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) L u
```


### `GenLimit.Gold.Text.SemanticallyIdentifiable`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:75`.

∃ M : TextLearner Language, SemanticallyIdentifiesClass M 𝒞.

Exact type:

```lean
Set.{0} GenLimit.Language → Prop
```

Exact definition value:

```lean
fun 𝒞 => ∃ M, GenLimit.Gold.Text.SemanticallyIdentifiesClass M 𝒞
```


### `GenLimit.Gold.Text.SemanticallyIdentifiesClass`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:70`.

IdentifiesClass with Language names and semanticNaming.

Exact type:

```lean
GenLimit.Gold.Text.TextLearner.{0} GenLimit.Language → Set.{0} GenLimit.Language → Prop
```

Exact definition value:

```lean
fun M 𝒞 => @GenLimit.Gold.Text.IdentifiesClass.{0} GenLimit.Language GenLimit.Gold.Text.semanticNaming M 𝒞
```


### `GenLimit.Gold.Text.TextLearner`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:30`.

Learner Nat Name, hence List Nat → Name.

Exact type:

```lean
Type u_1 → Type (max u_1 0)
```

Exact definition value:

```lean
fun Name => GenLimit.Learner.{0, u_1} Nat Name
```


### `GenLimit.Gold.Text.compatibleIndices`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:57`.

The finite filter {i < history.length | PositiveCompatible history (C i)}; its dependency metadata includes Classical.propDecidable.

Exact type:

```lean
GenLimit.LanguageFamily → List.{0} Nat → Finset.{0} Nat
```

Exact definition value:

```lean
fun C history => {i ∈ Finset.range (@List.length.{0} Nat history) | GenLimit.Gold.Text.PositiveCompatible history (C i)}
```


### `GenLimit.Gold.Text.enumerationLearner`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:81`.

enumerationLearnerWithFallback C 0.

Exact type:

```lean
GenLimit.LanguageFamily → GenLimit.Gold.Text.TextLearner.{0} Nat
```

Exact definition value:

```lean
fun C =>
  GenLimit.Gold.Text.enumerationLearnerWithFallback C (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```


### `GenLimit.Gold.Text.enumerationLearnerWithFallback`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:72`.

Return the minimum compatible index below history.length, or fallback if the finite candidate set is empty.

Exact type:

```lean
GenLimit.LanguageFamily → Nat → GenLimit.Gold.Text.TextLearner.{0} Nat
```

Exact definition value:

```lean
fun C fallback history =>
  @GenLimit.Support.leastCandidateWithFallback.{0} Nat Nat.instLinearOrder
    (GenLimit.Gold.Text.compatibleIndices C history) fallback
```


### `GenLimit.Gold.Text.familyNaming`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:55`.

The naming with natural indices and language map C.

Exact type:

```lean
GenLimit.LanguageFamily → GenLimit.Gold.Text.Naming.{0} Nat
```

Exact definition value:

```lean
fun C => @GenLimit.Gold.Text.Naming.mk.{0} Nat C
```


### `GenLimit.Gold.Text.finiteLanguages`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Finite:39`.

The class {L : Language | Set.Finite L}.

Exact type:

```lean
Set.{0} GenLimit.Language
```

Exact definition value:

```lean
@setOf.{0} GenLimit.Language fun L => @Set.Finite.{0} Nat L
```


### `GenLimit.Gold.Text.finiteLearner`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Finite:91`.

List.toFinset on lists of natural numbers using decidable Nat equality.

Exact type:

```lean
GenLimit.Gold.Text.TextLearner.{0} (Finset.{0} Nat)
```

Exact definition value:

```lean
@List.toFinset.{0} Nat instDecidableEqNat
```


### `GenLimit.Gold.Text.finiteNaming`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Finite:87`.

Names are Finset Nat and denotation is Finset.toSet.

Exact type:

```lean
GenLimit.Gold.Text.Naming.{0} (Finset.{0} Nat)
```

Exact definition value:

```lean
@GenLimit.Gold.Text.Naming.mk.{0} (Finset.{0} Nat) fun F => @Finset.toSet.{0} Nat F
```


### `GenLimit.Gold.Text.leastCover`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:28`.

The least n such that C z ⊆ C n, by Nat.find with classical subset decision. The target index z ensures existence; this is a semantic endpoint, not a value passed to the learner.

Exact type:

```lean
GenLimit.LanguageFamily → Nat → Nat
```

Exact definition value:

```lean
fun C z =>
  @Nat.find (fun n => @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) (C z) (C n))
    (fun a =>
      Classical.propDecidable (@HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) (C z) (C a)))
    ⋯
```


### `GenLimit.Gold.Text.leastCover._proof_1`

Kind: `theorem`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:None`.

Auxiliary THEOREM SIGNATURE only: ∀ C z, ∃ i, C z ⊆ C i. The proof body is absent.

Exact type:

```lean
∀ (C : GenLimit.LanguageFamily) (z : Nat),
  ∃ i, @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) (C z) (C i)
```


### `GenLimit.Gold.Text.semanticLearner`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:79`.

Map a history to N.language (M history): postcompose the original learner with the naming’s denotation.

Exact type:

```lean
{Name : Type u_1} →
  GenLimit.Gold.Text.Naming.{u_1} Name →
    GenLimit.Gold.Text.TextLearner.{u_1} Name → GenLimit.Gold.Text.TextLearner.{0} GenLimit.Language
```

Exact definition value:

```lean
fun {Name} N M history => @GenLimit.Gold.Text.Naming.language.{u_1} Name N (M history)
```


### `GenLimit.Gold.Text.semanticNaming`

Kind: `definition`. Anchor: `GenLimit.Paper00_LanguageIdentification.Text.Model:65`.

The naming whose name type is Language and whose language map is the identity.

Exact type:

```lean
GenLimit.Gold.Text.Naming.{0} GenLimit.Language
```

Exact definition value:

```lean
@GenLimit.Gold.Text.Naming.mk.{0} GenLimit.Language (@id.{1} GenLimit.Language)
```


### `GenLimit.IdentifiesInLimit`

Kind: `definition`. Anchor: `GenLimit.Core.Identification:53`.

∃ name, denote name = target ∧ StabilizesTo (fun t => learner (textPrefix stream t)) name.

Exact type:

```lean
{Info : Type uInfo} →
  {Name : Type uName} →
    {Object : Type uObject} → (Name → Object) → GenLimit.Learner.{uInfo, uName} Info Name → (Nat → Info) → Object → Prop
```

Exact definition value:

```lean
fun {Info} {Name} {Object} denote learner stream target =>
  ∃ name,
    And (@Eq.{uObject + 1} Object (denote name) target)
      (@GenLimit.StabilizesTo.{uName} Name (fun t => learner (@GenLimit.textPrefix.{uInfo} Info stream t)) name)
```


### `GenLimit.Language`

Kind: `definition`. Anchor: `GenLimit.Core.Basic:20`.

A language is Set Nat.

Exact type:

```lean
Type
```

Exact definition value:

```lean
Set.{0} Nat
```


### `GenLimit.LanguageFamily`

Kind: `definition`. Anchor: `GenLimit.Core.Basic:23`.

A family is a total map Nat → Language; indices may repeat languages.

Exact type:

```lean
Type
```

Exact definition value:

```lean
Nat → GenLimit.Language
```


### `GenLimit.Learner`

Kind: `definition`. Anchor: `GenLimit.Core.Identification:18`.

A total function List Info → Name. No computability restriction is included.

Exact type:

```lean
Type uInfo → Type uName → Type (max uName uInfo)
```

Exact definition value:

```lean
fun Info Name => List.{uInfo} Info → Name
```


### `GenLimit.Presents`

Kind: `definition`. Anchor: `GenLimit.Core.Basic:26`.

Set.range stream = L, so the infinite positive stream contains precisely all and only elements of L.

Exact type:

```lean
(Nat → Nat) → GenLimit.Language → Prop
```

Exact definition value:

```lean
fun stream L => @Eq.{1} (Set.{0} Nat) (@Set.range.{0, 1} Nat Nat stream) L
```


### `GenLimit.StabilizesTo`

Kind: `definition`. Anchor: `GenLimit.Core.Identification:47`.

∃ T, ∀ t, T ≤ t → guess t = name: one name at every sufficiently large time.

Exact type:

```lean
{Name : Type uName} → (Nat → Name) → Name → Prop
```

Exact definition value:

```lean
fun {Name} guess name => ∃ T, ∀ (t : Nat), @LE.le.{0} Nat instLENat T t → @Eq.{uName + 1} Name (guess t) name
```


### `GenLimit.Support.leastCandidateWithFallback`

Kind: `definition`. Anchor: `GenLimit.Support.LeastCandidate:20`.

For a finite subset of a linear order, return its minimum if nonempty, otherwise fallback.

Exact type:

```lean
{α : Type u_1} → [LinearOrder.{u_1} α] → Finset.{u_1} α → α → α
```

Exact definition value:

```lean
fun {α} [inst : LinearOrder.{u_1} α] candidates fallback =>
  @dite.{u_1 + 1} α (@Finset.Nonempty.{u_1} α candidates) (@Finset.decidableNonempty.{u_1} α candidates)
    (fun h => @Finset.min'.{u_1} α inst candidates h) fun h => fallback
```


### `GenLimit.Support.leastEquivalentIndex`

Kind: `definition`. Anchor: `GenLimit.Support.LeastCandidate:79`.

Nat.find for family n = family z, decided by Classical.propDecidable; its existence witness is suppressed in the exported value.

Exact type:

```lean
{β : Type u_1} → (Nat → β) → Nat → Nat
```

Exact definition value:

```lean
fun {β} family z =>
  @Nat.find (fun n => @Eq.{u_1 + 1} β (family n) (family z))
    (fun a => Classical.propDecidable (@Eq.{u_1 + 1} β (family a) (family z))) ⋯
```


### `GenLimit.Support.leastEquivalentIndex._proof_1`

Kind: `theorem`. Anchor: `GenLimit.Support.LeastCandidate:None`.

Auxiliary THEOREM SIGNATURE only: for each family and z, some i has family i = family z. No proof body is supplied or inspected.

Exact type:

```lean
∀ {β : Type u_1} (family : Nat → β) (z : Nat), ∃ i, @Eq.{u_1 + 1} β (family i) (family z)
```


### `GenLimit.sample`

Kind: `definition`. Anchor: `GenLimit.Core.Basic:30`.

The finite image of Finset.range t under stream, hence the set of distinct values at positions 0 through t−1. This is a deterministic finite set, not a random sampling law.

Exact type:

```lean
(Nat → Nat) → Nat → Finset.{0} Nat
```

Exact definition value:

```lean
fun stream t => @Finset.image.{0, 0} Nat Nat instDecidableEqNat stream (Finset.range t)
```


### `GenLimit.textPrefix`

Kind: `definition`. Anchor: `GenLimit.Core.Text:16`.

The list map stream (List.range t): entries at times 0 through t−1; length t.

Exact type:

```lean
{α : Type u_1} → (Nat → α) → Nat → List.{u_1} α
```

Exact definition value:

```lean
fun {α} stream t => @List.map.{0, u_1} Nat α stream (List.range t)
```


## Completion and remaining limits

Every supplied unique target has a dossier and a JSON object; shared mappings retain all seven slot labels without duplicating target counts. Exact theorem hypotheses, conclusion components and quantifier scopes are preserved. In particular the supplement keeps: least covering versus equal-language indices; arbitrary fallback versus fallback 0; type-level existential identification names versus fixed least-index conclusions; legal stabilizing versus correct locking histories; the explicit nonempty premise for locking/stabilizing existence; the infinite-member premises and one-sided sublanguage exclusion in tell-tale existence; and arbitrary naming versus identity semantic naming.

This remains a code-only reconstruction. It makes no statement about the source meaning of any slot, proof correctness, effective witness construction, fresh compilation or human certification. Original frozen Stage 1 files and all inputs are preserved. Only `stage1-supplement.md`, `stage1-supplement.json` and `stage1-supplement-run.json` are written. Stop here, without accessing source-comparison material.
