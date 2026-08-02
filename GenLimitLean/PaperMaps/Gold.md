# Gold paper map

Lean umbrella: `GenLimit.Gold`

Cross-paper umbrellas:

- `GenLimit.Bridges.GoldToKM`;
- `GenLimit.Bridges.GoldToDenseGeneration`.

Source: E. Mark Gold, *Language Identification in the Limit*, Information
and Control 10 (1967), 447–474.

This development is the **semantic first layer** of Gold's theory. In Gold's
terminology on pp. 457–460, it concerns possibly ineffective identification
from arbitrary presentations. It formalizes the extensional learning
arguments needed for comparison with KM and DenseGeneration, but it does not
yet formalize the recursion-theoretic restrictions on learners, texts, or
grammar names used in Appendix I.

Human audit status: Peng Zhang completed a Level 2 audit of the
shared Core prerequisites and Gold Text on 2 August 2026. This covers `Text.Model`,
`Text.Consistency`, `Text.Finite`, `Text.Locking`, and `Text.Superfinite`.
The Abstract Theorem 7.1 path, `Text.Enumeration`,
`Abstract.TextSpecialization`, Informant, and bridge paths have not yet been
human-audited.  See the dated [human audit record](../HUMAN_AUDIT.md) for the
exact scope, exclusions, and source hashes.

## Main declarations

- complete abstract Theorem 7.1:
  `GenLimit.Gold.Abstract.gold_theorem_7_1`;
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
- Gold-to-KM separation:
  `GenLimit.GoldKMSeparation.generation_without_identification`;
- Gold-to-DenseGeneration separation:
  `GenLimit.GoldDenseSeparation.dense_generation_without_identification`.

## Dependency layout

```text
Core.Basic
└─ Core.Text
   └─ Core.Identification
      ├─ Gold.Abstract.Model
      │  └─ Gold.Abstract.Enumeration
      └─ Gold.Text.Model
         ├─ Gold.Text.Consistency
         │  ├─ Gold.Text.Finite
         │  └─ Gold.Text.Enumeration
         ├─ Gold.Text.Locking
         │  └─ Gold.Text.Superfinite (also imports Gold.Text.Finite)
         └─ Gold.Informant.Model
            └─ Gold.Informant.Enumeration

Gold.Abstract.Model + Gold.Text.Model
└─ Gold.Abstract.TextSpecialization

Gold.Abstract + Gold.Text + Gold.Abstract.TextSpecialization + Gold.Informant
└─ Gold.Semantic
   └─ Gold umbrella

Core.OnlineGeneration + Gold.Text + KM
└─ Bridges.GoldToKM

Bridges.GoldToKM + DenseGeneration.Patient.Main
└─ Bridges.GoldToDenseGeneration
```

The Gold umbrella imports only shared Core material and Gold modules. The
comparison declarations remain in `GenLimit.Bridges`, so neither KM nor
DenseGeneration depends on Gold.

## Representation and indexing conventions

Gold fixes a nonempty finite alphabet and treats a language as a subset of
the finite strings over that alphabet (pp. 448–449). Lean fixes a countable
universe:

```lean
Language       := Set ℕ
LanguageFamily := ℕ → Language
```

This is an extensional encoding only. No effective translation between
strings and naturals is asserted in this layer. Gold's Appendix I instead
requires a primitive-recursive one-to-one correspondence when computability
classes must be preserved (p. 467).

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

## Source-to-Lean correspondence

| Gold source | Paper content | Lean declaration | Module | Scope of correspondence |
|---|---|---|---|---|
| §6, pp. 456–458 | An abstract identification situation assigns each object a set of allowable infinite information sequences; a learner maps finite histories to names. | `Abstract.Allowable`, `Abstract.Naming`, `Abstract.Compatible`, `Abstract.Identifies`, `Abstract.Identifiable` | `GenLimit.Gold.Abstract.Model` | Direct semantic model over arbitrary types; every object has a chosen name, expressing Gold's standing assumption that every object has at least one name. |
| §7, Theorem 7.1, pp. 458–459, first clause | Ineffective identifiability implies distinguishability: one information sequence cannot describe two distinct objects. | `Abstract.distinguishable_of_identifiable` | `GenLimit.Gold.Abstract.Enumeration` | Exact formalization of the necessity clause. |
| §7, Theorem 7.1, pp. 458–459, second clause | Collapsing uncertainty implies that identification by enumeration succeeds for any enumeration. | `Abstract.firstCompatibleIndex_stabilizes`; `Abstract.identificationByEnumeration_identifies`; `Abstract.collapsingUncertainty_implies_identifiable` | `GenLimit.Gold.Abstract.Enumeration` | Exact semantic formalization. Enumerations may repeat objects; the learner stabilizes to the first occurrence of the target. |
| §7, Theorem 7.1, p. 459, third clause | If every object's allowable-sequence set is countable, distinguishability is sufficient for ineffective identification. | `Abstract.allowableSequences_countable`; `Abstract.distinguishable_implies_identifiable_of_countable` | `GenLimit.Gold.Abstract.Enumeration` | Exact semantic formalization under Gold's standing countability assumptions on the information and object types. The proof enumerates all allowable sequences, identifies the observed sequence, and translates it to its unique object. |
| §7, Theorem 7.1, pp. 458–459 | All three clauses in one statement. | `Abstract.gold_theorem_7_1` | `GenLimit.Gold.Abstract.Enumeration` | Bundled paper-facing theorem. |
| §2, pp. 449–450; §6, pp. 456–457 | A learner maps the information seen so far to a grammar and succeeds when its guesses are eventually constant at one correct name. | `Learner`, `StabilizesTo`, `IdentifiesInLimit`; `Text.Naming`, `Text.TextLearner`, `Text.IdentifiesOnText`, `Text.IdentifiesLanguage`, `Text.IdentifiesClass`, `Text.IdentifiableWith` | `GenLimit.Core.Identification`; `GenLimit.Gold.Text.Model` | Generic strong name stabilization is shared; the concrete specialization is semantic over `ℕ` and deliberately omits effectiveness. |
| §2, p. 450 | A text lists only target strings, in arbitrary order and with every target string eventually occurring. | `Presents`; ordered access through `textPrefix` | `GenLimit.Core.Basic`; `GenLimit.Core.Text` | `Set.range stream = L` gives exactly Gold's coverage condition and permits repetitions. |
| §2 and §6, pp. 449, 457 | One language can have multiple grammar names, but identification requires eventual constancy of the guessed name. | `Text.Naming`; `Text.IdentifiesOnText` | `GenLimit.Gold.Text.Model` | Exact-name convergence is distinguished from mere eventual equality of denoted languages. |
| §2 and §§6–7, pp. 449–450, 456–459 | Arbitrary positive text is a concrete instance of Gold's abstract allowable-information-sequence model. | `Abstract.exactTextAllowable`; `Abstract.classTextAllowable`; `Abstract.identifiesOn_exactText_iff`; `Abstract.identifies_classTextAllowable_iff`; `Abstract.identifiable_classTextAllowable_iff` | `GenLimit.Gold.Abstract.TextSpecialization` | Exact semantic bridge between the independently defined abstract and concrete text interfaces. It is a specialization lemma, not a separately numbered theorem in Gold's paper. |
| §7, p. 459; Appendix Theorem I.6, p. 469 | The learner that conjectures exactly the positive examples seen so far identifies every finite language. | `finiteLearner`; `finiteLearner_identifiesOnText`; `finiteLearner_identifiesFiniteLanguages`; `finiteLanguages_identifiableWith` | `GenLimit.Gold.Text.Finite` | Formalizes the extensional core of I.6. It uses finite sets as names; compilation of those names to tester Turing machines is future work. |
| §7, pp. 458–459, Theorem 7.1, specialized to positive text | Identification by enumeration chooses the first enumerated language compatible with the finite positive information. | `compatibleIndices`; `enumerationLearnerWithFallback`; `enumerationLearner` | `GenLimit.Gold.Text.Enumeration` | Language-specific specialization. The bounded scope `i < history.length` makes the learner total and eventually exposes every fixed index. |
| §7, p. 459; §9, p. 461 | Positive text can eliminate a candidate only when it omits a target element; a strict superlanguage remains compatible forever. | `leastCover`; `enumerationLearnerWithFallback_stabilizesTo_leastCover`; `enumerationLearner_stabilizesTo_leastCover` | `GenLimit.Gold.Text.Enumeration` | The learner converges to the least index `i` satisfying `C z ⊆ C i`, not necessarily to the target's least exact name. |
| §7, pp. 458–459, collapsing uncertainty; text discussion on p. 459 | Enumeration succeeds when every wrong earlier object is eventually eliminated. | `IsInclusionAntichain`; `enumerationLearner_identifiesFamily_of_isInclusionAntichain` | `GenLimit.Gold.Text.Enumeration` | A paper-relevant sufficient specialization: containment among indexed languages forces equality, while duplicate indices remain allowed. This antichain corollary is not separately named by Gold. |
| §8–§9, pp. 460–461; diagonal idea behind Appendix I.8, pp. 470–471 | If no finite history stabilizes the learner, extend histories so that a target text forces infinitely many mind changes. | `IsStabilizing`; `IsLocking`; `exists_stabilizing_of_identifiesLanguage`; `exists_locking_of_identifiesLanguage` | `GenLimit.Gold.Text.Locking` | A semantic locking-sequence decomposition of Gold's arbitrary-text diagonal idea. Gold does not state a theorem under the modern name “locking sequence.” |
| Derived from the preceding locking argument | A learnable infinite class member has finite positive data excluding every proper class sublanguage below it. | `Text.IsTellTale`; `Text.finite_tellTale_of_semantic_identification`; `Text.finite_tellTale_of_semanticallyIdentifiable` | `GenLimit.Gold.Text.Superfinite` | Modern finite-tell-tale formulation; it is proof infrastructure, not a definition or named theorem in Gold's paper. |
| Table I and definition of superfinite, pp. 452–453; §8–§9, pp. 460–461 | Finite languages are identifiable, while every proper superclass is not identifiable from arbitrary text. | `Text.IsSuperfinite`; `Text.superfinite_not_semanticallyIdentifiable`; `Text.finiteLanguages_maximal_semanticallyIdentifiable` | `GenLimit.Gold.Text.Superfinite` | Matches Gold's ineffective arbitrary-text conclusion in §8. The proof uses tell-tales rather than reproducing Appendix I.8's effective recursive-text construction. |
| Appendix I.8, pp. 470–471 | Against an effective learner, construct a recursive bad text for the infinite target. | No declaration in the current layer | — | Not yet formalized. The present superfinite theorem quantifies over all arbitrary texts and even noncomputable learners, but does not prove the bad text recursive. |
| Appendix I.9, pp. 471–473 | Against an effective tester learner, construct a primitive-recursive bad text for the infinite target. | No declaration in the current layer | — | Not yet formalized. This requires codes for tester machines, a primitive-recursive guessing function, and Gold's computation-predicate diagonal construction. |
| §2, pp. 450–451 | An arbitrary informant labels membership correctly and eventually queries every string. | `Informant.InformantDatum`, `Informant.InformantStream`, `Informant.InformantCorrect`, `Informant.InformantComplete`, `Informant.IsInformantFor` | `GenLimit.Gold.Informant.Model` | Direct arbitrary-informant model over `ℕ`, allowing arbitrary order and repetitions. |
| §7, Theorem 7.1, pp. 458–459; §8, p. 460 | Informants have collapsing uncertainty; every countable named class is ineffectively identifiable by enumeration. | `candidate_eventually_informantCompatible_iff_eq`; `finite_scope_eventually_informantCompatible_iff_eq` | `GenLimit.Gold.Informant.Model` | Complete positive and negative labels eventually distinguish every extensionally unequal candidate in a fixed finite scope. |
| §7–§8, pp. 458–460 | Guess the first enumerated language agreeing with all informant data so far. | `leastEqualName`; `informantEnumerationLearner`; `informantEnumerationLearner_stabilizesTo_leastEqualName`; `informantEnumerationLearner_identifiesFamily` | `GenLimit.Gold.Informant.Enumeration` | Every indexed family is semantically identifiable; duplicate languages converge to the least index naming the target. The construction is noncomputable for arbitrary `Set ℕ` languages. |
| Appendix Theorem I.4, pp. 467–468 | Primitive-recursive languages are effectively tester-identifiable from a methodical informant. | No effective counterpart in the current layer | — | The semantic informant theorem captures the enumeration logic, but does not enumerate primitive-recursive programs or emit tester codes. |

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

This is Gold's §8 ineffective/countable-class result. It is not yet Appendix
I.4: neither family membership nor the learner is certified computable, and
the output indices are not Turing-machine tester codes.

## Bridges to KM and DenseGeneration

The bridge modules use paper-independent trace predicates from
`GenLimit.Core.OnlineGeneration`:

| Predicate | Trace-level guarantee |
|---|---|
| `FreshGeneratesInLimit stream output L` | Eventually `output t ∈ L` and `output t ∉ sample stream t`. This matches the current KM conclusion. |
| `NovelGeneratesInLimit stream output L` | Eventually outputs are in `L`, avoid adversary observations through the current round, and never repeat a previous generator output. |

### Identification implies KM-style generation

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

`GenLimit.Bridges.GoldToKM` defines

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
| The co-singleton class is not semantically Gold-identifiable from every arbitrary positive text. | `coSingleton_not_semanticallyIdentifiable` | `GenLimit.Bridges.GoldToKM` |
| The impossibility transfers to every fixed grammar naming relation. | `coSingleton_not_identifiableWith` | `GenLimit.Bridges.GoldToKM` |
| No natural-index learner satisfies `IdentifiesFamily` for the indexed co-singleton family. | `coSingleton_not_identifiesFamily` | `GenLimit.Bridges.GoldToKM` |
| The existing finite-query KM machine fresh-generates on every exact presentation of every co-singleton target. | `coSingleton_km_generates` | `GenLimit.Bridges.GoldToKM` |
| Same-family Gold/KM separation. | `generation_without_identification` | `GenLimit.Bridges.GoldToKM` |
| Patient Scope additionally gives current-round adversary freshness, output non-repetition, and target-relative lower density at least `1 / 2`. | `coSingleton_patientScope_generation_and_lowerDensity` | `GenLimit.Bridges.GoldToDenseGeneration` |
| Same-family Gold/DenseGeneration separation. | `dense_generation_without_identification` | `GenLimit.Bridges.GoldToDenseGeneration` |

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

## Semantic/effectivity boundary

The current layer formalizes:

- arbitrary positive texts and arbitrary complete informants;
- exact-name and semantic stabilization;
- finite-language learnability at the level of finite-set names;
- semantic least-compatible enumeration;
- the locking and tell-tale obstruction;
- Gold's §8 ineffective arbitrary-text and informant conclusions;
- semantic comparisons with the already formalized KM and Patient Scope
  generators.

The following remain for a future computability layer:

- effective learners and coded grammar names;
- tester and generator Turing machines and their denotation relations;
- recursive and primitive-recursive texts;
- methodical and request informants and Appendix Theorem I.3's effective
  equivalence;
- effective enumeration of primitive-recursive characteristic functions and
  Appendix I.4;
- Appendix I.5's recursive-language informant diagonal;
- compilation of the finite-set learner to testers in Appendix I.6;
- Appendix I.7's anomalous primitive-recursive-text/generator result;
- Appendix I.8's recursive bad text and Appendix I.9's
  primitive-recursive-text diagonal;
- effective and limiting-recursive translations between naming relations;
- Gold's learning-time, time-function, black-box, and inductive-inference
  results.

Accordingly, declarations called `semantic` or defined with
`noncomputable` must not be cited as formalizations of Gold's effective
Appendix I theorems. Conversely, the semantic negative results apply to a
strictly larger set of learners, so every future effective learner will
inherit those arbitrary-text impossibility corollaries.
