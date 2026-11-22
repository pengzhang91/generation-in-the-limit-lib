# #0 Language Identification map

Lean module: `GenLimit.Paper00_LanguageIdentification`.
Declaration namespace retained for API compatibility: `GenLimit.Gold`.
Main-results entry point:
`GenLimit.Paper00_LanguageIdentification.Results.Overview`.

Cross-paper umbrellas:

- `GenLimit.Bridges.Paper00ToPaper01`;
- `GenLimit.Bridges.Paper00ToPaper39`.

Source: E. Mark Gold, *Language Identification in the Limit*, Information
and Control 10 (1967), 447–474.

The registry inventories 14 numbered results and the three language-identification conclusions in §8. Lean proves 16 claims under the conventions below. The remaining claim, Corollary 10.1 on p. 464, has both a checked refutation of its printed direction and a proof of the reversed statement. [Source edition](https://doi.org/10.1016/S0019-9958(67)91165-5)

Audit record: Peng Zhang's Level 2 human review and its exact scope,
exclusions, historical paths, and source hashes are recorded only in the
[authoritative human-audit ledger](../AuditRecords/Human/README.md).

## Main declarations

- public source-facing facade:
  `GenLimit.Gold.Results.theorem_7_1`,
  `GenLimit.Gold.Results.theorem_I_6`,
  `GenLimit.Gold.Results.section_8_finite_superfinite_boundary`, and
  `GenLimit.Gold.Results.complete_informant_enumeration`;
- canonical complete abstract Theorem 7.1:
  `GenLimit.Gold.Abstract.theorem_7_1_clauses`;
- positive-text model: `GenLimit.Gold.Text.IdentifiesOnText`;
- finite-language learner:
  `GenLimit.Gold.Text.finiteLearner_identifiesFiniteLanguages`;
- sharp arbitrary-text boundary:
  `GenLimit.Gold.Text.finiteLanguages_maximal_semanticallyIdentifiable`;
- positive-text enumeration limit:
  `GenLimit.Gold.Text.enumerationLearner_stabilizesTo_leastCover`;
- locking-sequence lemma:
  `GenLimit.Gold.Text.exists_locking_of_identifiesLanguage`;
- finite tell-tale necessity:
  `GenLimit.Gold.Text.finite_tellTale_of_semantic_identification`;
- semantic superfinite obstruction:
  `GenLimit.Gold.Text.superfinite_not_semanticallyIdentifiable`;
- complete-informant enumeration:
  `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily`;
- #0-to-#01 separation:
  `GenLimit.GoldKMSeparation.generation_without_identification`;
- #0-to-#39 separation:
  `GenLimit.GoldDenseSeparation.dense_generation_without_identification`.

## Dependency layout

```text
Core.Basic
└─ Core.Text
   └─ Core.Identification
      ├─ Paper00_LanguageIdentification.Abstract.Model
      │  └─ Paper00_LanguageIdentification.Abstract.Enumeration
      └─ Paper00_LanguageIdentification.Text.Model
         ├─ Paper00_LanguageIdentification.Text.Consistency
         │  ├─ Paper00_LanguageIdentification.Text.Finite
         │  └─ Paper00_LanguageIdentification.Text.Enumeration
         ├─ Paper00_LanguageIdentification.Text.Locking
         │  └─ Paper00_LanguageIdentification.Text.Superfinite
         └─ Paper00_LanguageIdentification.Informant.Model
            └─ Paper00_LanguageIdentification.Informant.Enumeration

Paper00_LanguageIdentification.Abstract.Model + .Text.Model
└─ Paper00_LanguageIdentification.Abstract.TextSpecialization

Paper00_LanguageIdentification.Abstract + .Text + .Informant
└─ Paper00_LanguageIdentification.Semantic

Canonical result modules
└─ Paper00_LanguageIdentification.Results.Overview

Paper00_LanguageIdentification.Semantic + .Effective + .Results.Overview
└─ Paper00_LanguageIdentification umbrella

Core.OnlineGeneration + #0 + #01
└─ Bridges.Paper00ToPaper01

Bridges.Paper00ToPaper01 + Paper39_DenseGeneration.Patient.Main
└─ Bridges.Paper00ToPaper39
```

The #0 umbrella imports only shared Core material and #0 modules. The
comparison declarations remain in `GenLimit.Bridges`, so #01 and #39 do not
depend on #0.

The bounded least-candidate operation used by the text and informant
enumeration learners is shared through `GenLimit.Support.LeastCandidate`;
P12's feedback identifier uses the same selector.  Finite families of
eventual thresholds are combined through `GenLimit.Support.Stabilization`.

## Representation and indexing conventions

Gold fixes a nonempty finite alphabet and treats a language as a subset of
the finite strings over that alphabet (pp. 448–449). Lean fixes a countable
universe:

```lean
Language       := Set ℕ
LanguageFamily := ℕ → Language
```

The effective layer proves mutually inverse primitive recursive numberings for words over `Fin (k+1)`, including the unary alphabet. Assigning numbers to the letters of the fixed alphabet implements the word convention on p. 467. [Word numbering](../GenLimit/Paper00_LanguageIdentification/Effective/Words.lean)

Lean is zero-based:

- `textPrefix stream t` contains the ordered observations at positions
  `s < t`;
- `sample stream t` forgets order and repetition in the same strict prefix;
- the learner is also defined at `t = 0`, on the empty history;
- Gold's guess after its first `t` information units corresponds to the Lean
  guess on `textPrefix stream t`.

The extra initial Lean guess has no effect on limit identification.

A `LanguageFamily` is an indexed sequence, not a set of sets. It therefore
has at least one index and permits repeated languages. Set-valued classes
`𝒞 : Set Language` are used for representation-independent positive and
negative results. A `Naming Name` is not required to be injective, matching
Gold's allowance of multiple grammars for one language (p. 449).

## Source results

All entry points below are in `GenLimit.Gold.Results`. The registry links each claim to its defining proof module. [Results facade](../GenLimit/Paper00_LanguageIdentification/Results/Overview.lean)

| Source | Result | Entry point |
|---|---|---|
| Theorem 7.1, pp. 458–459 | Distinguishability is necessary. Collapsing uncertainty suffices for every enumeration. Countable presentation sets make distinguishability sufficient. | `theorem_7_1` |
| §8, p. 460, arbitrary informants | Enumeration learns any countable named class from complete truthful informants. | `section_8_named_informants` |
| §8, p. 460, restricted texts | A countable named class is ineffectively identifiable from recursive texts and from primitive recursive texts. | `section_8_restricted_texts` |
| §8, p. 460, arbitrary text | The class of all finite languages is maximal among identifiable classes containing it. | `section_8_finite_superfinite_boundary` |
| §10, Theorem 10.1, pp. 461–462 | A learner that matches every stabilization deadline of enumeration has all its own successful deadlines matched by enumeration. | `theorem_10_1_learning_time` |
| §11, Theorem 10.1, pp. 463–464 | A limiting-recursive translation preserves effective identification of arbitrary objects under the same presentation method. | `theorem_10_1_translation` |
| §11, Corollary 10.1, p. 464 | Testers can be compiled to range generators. The obstruction holds from generators to testers on the stated classes. | `corollary_10_1_corrected` |
| §11, Theorem 10.2, p. 465 | A partial function with a single-valued Σ⁰₂ graph cannot uniformly translate domains into complement domains on these classes. | `theorem_10_2` |
| Appendix I.1, p. 466 | A computable translation of tester to generator indices preserves identification. | `theorem_I_1` |
| Corollary I.2, pp. 466–467 | Generator nonidentifiability implies tester nonidentifiability. | `corollary_I_2` |
| I.3, p. 467 | Arbitrary, methodical and request informants have equal effective identifying power for each naming relation. | `theorem_I_3` |
| I.4, pp. 467–468 | A methodical informant suffices for tester learning of all primitive recursive languages. | `theorem_I_4` |
| I.5, pp. 468–469 | Even with methodical membership bits, no effective generator learner covers all recursive languages. | `theorem_I_5` |
| I.6, p. 469 | A computable learner emits a stable tester index for every finite language on arbitrary text. | `theorem_I_6` |
| I.7, pp. 469–470 | A computable learner identifies r.e. languages from primitive recursive text using generator indices. | `theorem_I_7` |
| I.8, pp. 470–471 | A superfinite generator-named class cannot be learned from recursive text. | `theorem_I_8` |
| I.9, pp. 471–473 | A superfinite tester-named class cannot be learned from primitive recursive text. | `theorem_I_9` |

## Abstract Theorem 7.1

`Abstract.Compatible allowable history object` is Gold's uncertainty-set
membership relation: it holds exactly when an allowable sequence for `object`
extends `history`. The formalized conditions are:

```text
Distinguishable allowable
  := no sequence is allowable for two distinct objects

CollapsingUncertainty allowable
  := along a target sequence, every wrong object is eventually incompatible
```

For a surjective `enumeration : ℕ → Object`,
`identificationByEnumeration` chooses the least compatible index and returns
a fixed chosen name of that object. Under collapsing uncertainty, the
finitely many wrong objects preceding the target's first index are all
eventually eliminated, proving convergence for every enumeration, including
enumerations with repetitions.

For the final clause, `allowableSequences_countable` proves that the union of
the countable allowable-sequence sets over a countable object type is
countable. The proof enumerates this union, uses finite-prefix disagreement
to identify the exact observed sequence, and uses distinguishability to
translate that sequence to its unique object. This follows Gold's proof on
p. 459 and remains intentionally noncomputable.

## Positive compatibility and the least-cover result

Although a Gold learner receives an ordered list, the canonical positive
enumeration learner uses only which elements have appeared:

```lean
PositiveCompatible history L :=
  ∀ u ∈ history, u ∈ L
```

The bridge lemma
`positiveCompatible_textPrefix_iff_consistent` identifies this predicate with
the shared Core predicate `Consistent`. Core's
`finite_scope_eventually_consistent_iff_target_subset` then yields, for every
fixed finite candidate scope,

```text
eventual compatibility of C i  ↔  C z ⊆ C i.
```

Accordingly, `enumerationLearner` stabilizes to `leastCover C z`. Exact
identification follows if that index denotes `C z`; the
`IsInclusionAntichain` hypothesis ensures this uniformly. This makes precise
Gold's observation on p. 461 that positive text can correct an undersized
hypothesis but can never refute an oversized one.

## Locking sequences, tell-tales, and the superfinite obstruction

`exists_stabilizing_of_identifiesLanguage` assumes that a semantic learner
identifies a nonempty target on every exact text. If no stabilizing finite
history existed, the proof would:

1. start from an arbitrary exact text for the target;
2. insert the next required target value, ensuring coverage;
3. append a target-consistent finite extension forcing another mind change;
4. take the limit of the nested histories.

The resulting `badText` still presents the target but contains arbitrarily
late forced mind changes, contradicting identification.

`exists_locking_of_identifiesLanguage` then completes the stabilizing history
to another exact target text and proves that its stable conjecture is the
target itself.

For an infinite class member `L`, the locking history is strengthened by one
target element and converted to a `Finset`. This yields an `IsTellTale 𝒞 L D`:

```text
D ⊆ L, and
for K ∈ 𝒞, D ⊆ K ⊆ L implies K = L.
```

If `𝒞` contains every finite language, `D` itself belongs to `𝒞`; the
tell-tale property therefore forces the finite set `D` to equal the infinite
target. This contradiction proves the semantic superfinite theorem.

This route is extensionally stronger about the learner—it rules out even
noncomputable learners on arbitrary texts—but intentionally weaker about the
counterexample text: unlike Appendix I.8, it does not certify that the bad
text is recursive.

## Complete informants

An informant datum is a pair `ℕ × Bool`. Correctness is

```text
label = true  ↔  queried element ∈ target,
```

and completeness requires every natural number to be queried at least once.
For any candidate `K ≠ L`, completeness eventually presents an element on
which `K` and `L` differ. Thus compatibility stabilizes to equality, rather
than the containment obtained from positive text.

The learner searches compatible indices below the current history length and
chooses their minimum. It stabilizes to `leastEqualName C z`, so repeated
indices for the same target cause no ambiguity in the final grammar name.

The effective methodical learner in I.4 enumerates primitive recursive programs and stabilizes to an index computing the actual membership bits. [Function learning](../GenLimit/Paper00_LanguageIdentification/Effective/FunctionLearning.lean)

## Bridges to #01 Language Generation and #39 Dense Generation

The bridge modules use paper-independent trace predicates from
`GenLimit.Core.OnlineGeneration`:

| Predicate | Trace-level guarantee |
|---|---|
| `FreshGeneratesInLimit stream output L` | Eventually `output t ∈ L` and `output t ∉ sample stream t`. This matches the current #01 conclusion. |
| `NovelGeneratesInLimit stream output L` | Eventually outputs are in `L`, avoid adversary observations through the current round, and never repeat a previous generator output. |

### Identification implies #01-style generation

`Gold.outputOfIdentifier` takes the current family index conjectured by a
Gold learner and classically chooses a value in that conjectured language
outside the current positive sample. For an `OracleFamily`, every language
is infinite, so such a value exists.

`Gold.identifier_implies_fresh_generation` proves that once the identifier
has stabilized to a name of the target, these outputs satisfy
`FreshGeneratesInLimit`.

The infinitude assumption is essential for this trace requirement:
`Gold.finite_target_not_fresh_generatable` proves that an exactly presented
finite target is eventually exhausted by the adversary sample, making fresh
valid output impossible.

### A same-family strict separation

`GenLimit.Bridges.Paper00ToPaper01` defines

```text
C 0       = ℕ
C (n + 1) = ℕ \ {n}.
```

The declarations `coSingletonQuery_spec` and
`coSingletonLanguage_infinite` package this as the uniformly Boolean-decidable
`coSingletonOracle`.

The universal member has no finite tell-tale: for every finite `D`, choose
`n ∉ D`; then

```text
D ⊆ ℕ \ {n} ⊊ ℕ.
```

Consequently:

| Comparison result | Lean declaration | Module |
|---|---|---|
| The co-singleton class is not semantically #0-identifiable from every arbitrary positive text. | `coSingleton_not_semanticallyIdentifiable` | `GenLimit.Bridges.Paper00ToPaper01` |
| The impossibility transfers to every fixed grammar naming relation. | `coSingleton_not_identifiableWith` | `GenLimit.Bridges.Paper00ToPaper01` |
| No natural-index learner satisfies `IdentifiesFamily` for the indexed co-singleton family. | `coSingleton_not_identifiesFamily` | `GenLimit.Bridges.Paper00ToPaper01` |
| The existing finite-query #01 machine fresh-generates on every exact presentation of every co-singleton target. | `coSingleton_km_generates` | `GenLimit.Bridges.Paper00ToPaper01` |
| Same-family #0/#01 separation. | `generation_without_identification` | `GenLimit.Bridges.Paper00ToPaper01` |
| Patient Scope additionally gives current-round adversary freshness, output non-repetition, and target-relative lower density at least `1 / 2`. | `coSingleton_patientScope_generation_and_lowerDensity` | `GenLimit.Bridges.Paper00ToPaper39` |
| Same-family #0/#39 separation. | `dense_generation_without_identification` | `GenLimit.Bridges.Paper00ToPaper39` |

The separation is not a theorem stated by Gold. It is a new comparison:
generation in the limit can succeed on a uniformly decidable countable family
of infinite languages even when exact Gold identification from arbitrary
positive text is impossible.

## Empty-language and presentation conventions

`Presents stream L` means `Set.range stream = L` for a total stream
`stream : ℕ → ℕ`. Therefore:

- exact texts allow arbitrary repetitions and ordering;
- every target element must occur;
- no total stream presents `∅`.

No pause or blank symbol has been added. As a result, identification claims
for the empty target are vacuous. In particular,
`finiteLearner_identifiesFiniteLanguages` includes `∅`, but there is no
`stream` satisfying its presentation premise for that target.

The locking lemma assumes `L.Nonempty` so that an exact base presentation can
be constructed. The finite-tell-tale theorem is stated for `L.Infinite` and
adds one known target element to its locking history; this avoids accidentally
invoking class identification on an empty candidate during the proof.

`IsSuperfinite 𝒞` nevertheless follows Gold's definition literally: `𝒞`
contains the language underlying every `Finset ℕ`, including `∅`, and also
contains at least one infinite language.

For indexed families:

- duplicate languages are permitted;
- the range need not be injectively or canonically enumerated;
- `IdentifiesFamily` requires success for every index and every exact text of
  its denoted language;
- `OracleFamily` additionally requires every indexed language to be infinite
  and supplies a correct Boolean membership function.

The presence of a Boolean function in `OracleFamily` is an access interface,
not a proof that the query or family is Turing-computable.

## Effective names and text conventions

A tester program halts on every word with its membership bit. The §11 generator is a partial recursive program with the target as its range. This convention represents the empty language. For each nonempty range a uniform compiler yields a total generator. I.7 already identifies a program computing the total text. [Names](../GenLimit/Paper00_LanguageIdentification/Effective/Names.lean) and [total generators](../GenLimit/Paper00_LanguageIdentification/Effective/TotalGenerators.lean)

Gold assumes each object has a name on p. 458. His proofs of I.8 and I.9 also treat absence of a required name as failure. The Lean endpoints explicitly combine that convention with success on every admissible text. The diagonal theorems apply directly given any infinite member with a presentation of the indicated kind. If success is quantified only over existing texts, adjoining one infinite language with no recursive text to the finite languages leaves both learners successful. Lean proves that counterexample as `superfinite_unpresentable_counterexample`. [Presentation boundary](../GenLimit/Paper00_LanguageIdentification/Effective/PresentationBoundary.lean)

For I.8 a recursive search extends finite histories to force further changes. For I.9 a primitive recursive clock revisits earlier prefixes with increasing evaluation bounds and only introduces a new word when a tester rejects it. This avoids assuming a primitive recursive learner or a primitive recursive universal interpreter. [Recursive obstructions](../GenLimit/Paper00_LanguageIdentification/Effective/RecursiveObstructions.lean) and [primitive recursive obstruction](../GenLimit/Paper00_LanguageIdentification/Effective/PrimitiveObstruction.lean)

The corollary on p. 464 rules out tester-to-generator translation as printed. The computable compiler in I.1 refutes it for §11 range generators. In the reverse direction a translation would turn the learner of I.7 into the tester learner excluded by I.9. For Theorem 10.2 the proof obtains a limit approximation from the Σ⁰₂ graph and combines domain and complement-domain programs into a tester. [Index obstructions](../GenLimit/Paper00_LanguageIdentification/Effective/IndexObstructions.lean)
