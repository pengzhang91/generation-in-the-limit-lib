# P00 Stage 1 — paper-withheld code-only reconstruction

Stage 1 is complete for the supplied interface package: six target theorem dossiers, all 51 recursively supplied non-theorem native declarations, and one coverage row for each of 17 opaque slots. Four slots have supplied endpoints (C01, C03, C05, C06); 13 have none. An absent endpoint is recorded as a gap, not as a reconstructed or passed source claim.

This report reconstructs statements and definition values. It does not certify theorem proofs, fresh compilation, correspondence with any paper, or human review. No mathematical input outside `P00/stage1/` was consulted. Original Lean source anchors below are frozen exporter locators only; those source files were not opened. No paper content is inferred from names.

## Scope, input census and provenance

The input was read in the prescribed order: `START_HERE.md`, `PROMPT.md`, `claim-slots.json`, then the supplied types, definition values, target list, snapshot, external boundary and manifest. `declarations.jsonl` contains 57 records: 45 definitions, three inductives, three constructors and six theorem statements. The complete 693-record `native-declaration-census.jsonl` was parsed for record counts and identity comparison; the six named algorithm-definition records were selectively inspected. All 57 recursive records exactly match their census counterparts. The census was not treated as an assertion that every helper was individually semantically reviewed, and no endpoint was added from it. All native `GenLimit.*` references recursively needed by the six target interfaces are present in the 57-record package.

The 10 entries in the supplied `SHA256SUMS` manifest match the actual input bytes. The manifest's own computed digest is also recorded below. The snapshot reports `source_snapshot_sha256 = befc88a67a9c004e5f3858848eef24b5aad80e157ec5e1d52f73fe42b8073d37`; that is snapshot provenance supplied by this package, not an independently recomputed hash of an original repository.

Requested configuration: `gpt-6.1-sol`, reasoning `xhigh`, fresh context. The execution context includes the task dispatch, environment/working agreements and Stage 1 inputs; no parent mathematical history was used. Actual backend model identifier, actual reasoning configuration, backend revision, and a machine-verifiable isolation attestation are not exposed here and are not invented. The first explicit clock observation was 2026-11-13 23:36:05 UTC; an exact start timestamp was not captured.

| Input relative to stage1/ | Bytes | SHA-256 |
|---|---:|---|
| `01-target-statements.md` | 3301 | `d22e9e99162a7cecbbb35bb9ba3d86ca4e72058566f8718e1834258a94277057` |
| `02-definition-dependencies.md` | 21084 | `989c90e92f4a7618afa64f861202b271762b35bc51de34c31eb52ecde4428fc3` |
| `PROMPT.md` | 3356 | `c63aad9d119a37687071a9dd61f3139f0f318647c5237a6cfd05e4ecd3e38de3` |
| `SHA256SUMS` | 854 | `3c1c9cddc2d6ebdfc34dd0c26b76d9e3f4b3de805449e87ae3dcdcc81f907b38` |
| `START_HERE.md` | 217 | `52dbb6f80b47a22d94f222fd499cc75c3e793e710b44d74dd69922866c1c02d7` |
| `claim-slots.json` | 2924 | `fa0ce493927a44c2189c1fa7a8901f49a74266db61eea33a1a053b44f683a091` |
| `declarations.jsonl` | 39821 | `3a8758ee6711bcb6f380ce8b84ea553d63323d0c58bfa18d695f75235a55608e` |
| `external-boundary.txt` | 705 | `fad3472420af3d149dcdae6825045d0708503843f68dd6736a7b6acaac822fb0` |
| `native-declaration-census.jsonl` | 612546 | `3797c5ae969b80feb7543ab369efaa67fbe834161d3ff2064b80f5ab48d0768d` |
| `snapshot.json` | 2322 | `9117230590580a10a9816909ff6bedf46635f2682e1de3c72ebfbd30fdcd023c` |
| `targets.txt` | 348 | `4b181b6a8724dc48f95658a9babf4ae1a419208665ed39018e050e740c8cced4` |

`START_HERE.md` and `PROMPT.md` supply task constraints; `claim-slots.json` supplies opaque slot mappings; `targets.txt`, `01-target-statements.md` and `declarations.jsonl` supply exact target types; `02-definition-dependencies.md` and `declarations.jsonl` supply native dependency interfaces/values; `external-boundary.txt` establishes the trusted external vocabulary; `snapshot.json` and the hashes establish package provenance. The native census supports only the bounded checks described above.

## Common conventions and external boundary

A learner is a total mathematical function on a finite list. “Causal” here means that the run's output is obtained from its finite observed prefix and fixed parameters; it does not establish computability or a resource bound. `textPrefix stream t` contains positions 0 through t−1. Every stabilization statement is `∃ T, ∀ t, T ≤ t → ...`, including the boundary time T. Correct names and convergence times are generally quantified after the target and complete stream; these witnesses are not information handed to the learner.

`IdentifiesInLimit denote M stream target` is `∃ name, denote name = target ∧ ∃ T, ∀ t ≥ T, M (textPrefix stream t) = name`. This is eventual fixed-name identification. The denotation equality alone does not permit outputs to oscillate forever among multiple correct names. With semantic names (sets of naturals) and identity denotation, fixed-name equality is equality of the entire target set, not merely pointwise stabilization of individual membership answers.

A positive text has type `Nat → Nat` and satisfies `Set.range stream = L`. It has no pause symbol, blank symbol, finite termination, label, or negative example. In particular no such text presents the empty language: `stream 0` belongs to the range. Therefore the empty-language identification clauses in the text model are vacuous, even though the empty language belongs to the finite-language class. Informants use a different type and do present the empty language by correct negative labels.

No target states a rate, a sample bound, a resource bound, a loss, a support-versus-single-sample comparison, a probability law, a full-support premise, a density/frequency guarantee, or a limsup conclusion. These are exact eventual-identification statements or nonexistence statements. No such additional interpretation is introduced.

The package explicitly trusts standard Lean/Mathlib meanings, without recursively auditing Mathlib. Its external constants are:

```text
And
Bool
Bool.true
Classical.propDecidable
Countable
Eq
Exists
Finset
Finset.Nonempty
Finset.decidableNonempty
Finset.filter
Finset.min'
Finset.range
Finset.toSet
Function.Surjective
HasSSubset.SSubset
HasSubset.Subset
Iff
LE.le
LinearOrder
List
List.instMembership
List.length
List.map
List.range
List.toFinset
Membership.mem
Nat
Nat.find
Nat.instLinearOrder
Ne
Nonempty
Not
OfNat.ofNat
Prod
Prod.fst
Prod.snd
Set
Set.Countable
Set.Finite
Set.Infinite
Set.instHasSSubset
Set.instHasSubset
Set.instMembership
Set.range
dite
id
instDecidableEqNat
instLENat
instOfNatNat
setOf
```

There is no unresolved decisive unknown native constant. Standard meanings of countability, finite/infinite sets, strict subset, surjectivity, finite filtering/minimum, `Nat.find`, classical proposition decision and ordinary list operations form the external semantic boundary.

## Definition glossary

Every non-theorem record in the recursive package has an entry below. The final appendix preserves each exact exported type and definition value (or constructor signature); this glossary supplies the concise semantic expansion.

| Exact identifier | Reconstruction |
|---|---|
| `GenLimit.Gold.Abstract.Allowable` | Object → Set (Nat → Info); an object may have zero or many allowable complete streams. |
| `GenLimit.Gold.Abstract.CollapsingUncertainty` | For every allowed target stream and each different object, eventually all subsequent prefixes are incompatible with that competitor; time may depend on the competitor. |
| `GenLimit.Gold.Abstract.Compatible` | A history is compatible with an object iff some stream allowable for it has exactly that history as its prefix of the same length. |
| `GenLimit.Gold.Abstract.Distinguishable` | Any complete stream simultaneously allowable for two objects forces those objects equal. This is not a finite-prefix separation definition. |
| `GenLimit.Gold.Abstract.Identifiable` | There exists one total finite-history learner satisfying Identifies. |
| `GenLimit.Gold.Abstract.Identifies` | For every object and every stream allowable for it, IdentifiesOn holds. |
| `GenLimit.Gold.Abstract.IdentifiesOn` | IdentifiesInLimit using naming.denotes for this learner, stream and object. |
| `GenLimit.Gold.Abstract.Naming` | A record carrying denotes, nameOf and a right-inverse law; see Naming.mk. |
| `GenLimit.Gold.Abstract.Naming.denotes` | First projection of the naming: the denotation of a name. |
| `GenLimit.Gold.Abstract.Naming.mk` | Constructs a naming from denotes : Name → Object, nameOf : Object → Name and ∀ object, denotes (nameOf object) = object. |
| `GenLimit.Gold.Abstract.Naming.nameOf` | Second projection of the naming: a chosen name for every object. |
| `GenLimit.Gold.Abstract.firstCompatibleIndex` | Classically choose the least natural i whose enumerated object is compatible with the history, using Nat.find; if no i exists return 0. |
| `GenLimit.Gold.Abstract.identificationByEnumeration` | Output naming.nameOf of enumeration at firstCompatibleIndex for the current history. |
| `GenLimit.Gold.Informant.IdentifiesFamilyFromInformant` | ∀ z info, IsInformantFor info (C z) → IdentifiesOnInformant (familyNaming C) M info (C z). |
| `GenLimit.Gold.Informant.IdentifiesOnInformant` | ∃ n, N.language n = L ∧ eventual fixed output n on the prefixes of info. |
| `GenLimit.Gold.Informant.InformantCompatible` | For every datum occurring in the finite history, its label is true iff its natural number belongs to the candidate language. |
| `GenLimit.Gold.Informant.InformantComplete` | For every natural u there is a time whose first component is u; labels are constrained separately. |
| `GenLimit.Gold.Informant.InformantCorrect` | At every time, the Boolean is true iff the first component belongs to L. |
| `GenLimit.Gold.Informant.InformantDatum` | Nat × Bool: a natural and its Boolean label. |
| `GenLimit.Gold.Informant.InformantLearner` | A total function List InformantDatum → Name. |
| `GenLimit.Gold.Informant.InformantStream` | Nat → InformantDatum. |
| `GenLimit.Gold.Informant.IsInformantFor` | A Prop record packaging InformantCorrect and InformantComplete. |
| `GenLimit.Gold.Informant.IsInformantFor.mk` | Constructs IsInformantFor from BOTH correctness and completeness proofs for the same info and L. |
| `GenLimit.Gold.Informant.informantCompatibleIndices` | The finite set of i < history.length with InformantCompatible history (C i); classical proposition decision appears in dependency metadata. |
| `GenLimit.Gold.Informant.informantEnumerationLearner` | informantEnumerationLearnerWithFallback C 0. |
| `GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback` | Use leastCandidateWithFallback on informantCompatibleIndices with the supplied fallback. |
| `GenLimit.Gold.Text.ContainsAllFiniteLanguages` | finiteLanguages ⊆ 𝒞. |
| `GenLimit.Gold.Text.IdentifiableWith` | ∃ M, IdentifiesClass N M 𝒞, with fixed name type and naming. |
| `GenLimit.Gold.Text.IdentifiesClass` | For every L ∈ 𝒞, IdentifiesLanguage N M L. |
| `GenLimit.Gold.Text.IdentifiesLanguage` | For every stream, Presents stream L → IdentifiesOnText N M stream L. |
| `GenLimit.Gold.Text.IdentifiesOnText` | IdentifiesInLimit for the naming language map, the learner, a Nat-valued stream and target language. |
| `GenLimit.Gold.Text.IsSuperfinite` | ContainsAllFiniteLanguages 𝒞 ∧ ∃ L, L ∈ 𝒞 ∧ Set.Infinite L. |
| `GenLimit.Gold.Text.Naming` | A record containing only a denotation Name → Language; no coverage/right-inverse condition. |
| `GenLimit.Gold.Text.Naming.language` | Projection of the name-to-language map. |
| `GenLimit.Gold.Text.Naming.mk` | Construct a Text.Naming from any Name → Language function. |
| `GenLimit.Gold.Text.SemanticallyIdentifiable` | ∃ M : TextLearner Language, SemanticallyIdentifiesClass M 𝒞. |
| `GenLimit.Gold.Text.SemanticallyIdentifiesClass` | IdentifiesClass with Language names and semanticNaming. |
| `GenLimit.Gold.Text.TextLearner` | Learner Nat Name, hence List Nat → Name. |
| `GenLimit.Gold.Text.familyNaming` | The naming with natural indices and language map C. |
| `GenLimit.Gold.Text.finiteLanguages` | The class {L : Language | Set.Finite L}. |
| `GenLimit.Gold.Text.finiteLearner` | List.toFinset on lists of natural numbers using decidable Nat equality. |
| `GenLimit.Gold.Text.finiteNaming` | Names are Finset Nat and denotation is Finset.toSet. |
| `GenLimit.Gold.Text.semanticNaming` | The naming whose name type is Language and whose language map is the identity. |
| `GenLimit.IdentifiesInLimit` | ∃ name, denote name = target ∧ StabilizesTo (fun t => learner (textPrefix stream t)) name. |
| `GenLimit.Language` | A language is Set Nat. |
| `GenLimit.LanguageFamily` | A family is a total map Nat → Language; indices may repeat languages. |
| `GenLimit.Learner` | A total function List Info → Name. No computability restriction is included. |
| `GenLimit.Presents` | Set.range stream = L, so the infinite positive stream contains precisely all and only elements of L. |
| `GenLimit.StabilizesTo` | ∃ T, ∀ t, T ≤ t → guess t = name: one name at every sufficiently large time. |
| `GenLimit.Support.leastCandidateWithFallback` | For a finite subset of a linear order, return its minimum if nonempty, otherwise fallback. |
| `GenLimit.textPrefix` | The list map stream (List.range t): entries at times 0 through t−1; length t. |

## Target D1: `GenLimit.Gold.Abstract.gold_theorem_7_1`

**Locator:** `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:275`. Kind: `theorem`. Linked slots: C01. Universe parameters: `u_1, u_2, u_3`.

**Exact exported type:**

```lean
∀ {Info : Type u_1} {Object : Type u_2} {Name : Type u_3} [Countable.{u_1 + 1} Info] [Countable.{u_2 + 1} Object]
  [Nonempty.{u_2 + 1} Object] (naming : GenLimit.Gold.Abstract.Naming.{u_2, u_3} Name Object)
  (allowable : GenLimit.Gold.Abstract.Allowable.{u_1, u_2} Info Object),
  (∀ (object : Object), @Set.Countable.{u_1} (Nat → Info) (allowable object)) →
    And
      (@GenLimit.Gold.Abstract.Identifiable.{u_3, u_2, u_1} Name Object Info naming allowable →
        @GenLimit.Gold.Abstract.Distinguishable.{u_1, u_2} Info Object allowable)
      (And
        (@GenLimit.Gold.Abstract.CollapsingUncertainty.{u_1, u_2} Info Object allowable →
          ∀ (enumeration : Nat → Object),
            @Function.Surjective.{1, u_2 + 1} Nat Object enumeration →
              @GenLimit.Gold.Abstract.Identifies.{u_3, u_2, u_1} Name Object Info naming allowable
                (@GenLimit.Gold.Abstract.identificationByEnumeration.{u_3, u_2, u_1} Name Object Info naming allowable
                  enumeration))
        (@GenLimit.Gold.Abstract.Distinguishable.{u_1, u_2} Info Object allowable →
          @GenLimit.Gold.Abstract.Identifiable.{u_3, u_2, u_1} Name Object Info naming allowable))
```

**Precise reconstruction.** For every information type Info, object type Object and name type Name (with the displayed independent universes), given Countable Info, Countable Object, Nonempty Object, a naming with denotes : Name → Object, nameOf : Object → Name and denotes (nameOf object) = object for every object, and an allowable map Object → Set (Nat → Info), assume each object's allowable set of complete streams is countable. The conclusion is a conjunction of three implications: (1) if one total finite-history learner identifies every object on every stream allowed for it, then a stream allowed for two objects forces those objects equal; (2) if, along each allowed target stream, every different object becomes permanently incompatible after a time allowed to depend on that target, stream and competing object, then for every surjective enumeration Nat → Object the specifically defined identificationByEnumeration learner identifies every object on all its allowable streams; (3) if allowed streams distinguish objects in the preceding disjointness sense, then some total finite-history learner identifies them all. Identification requires eventual constancy of one correct NAME on each individual stream, not merely eventual equality of denotations while names keep changing. The existence in (3) does not name its learner, and (3) does not assert collapsing uncertainty or the success of identificationByEnumeration under distinguishability alone.

**Expanded quantifier skeleton and dependencies:**

```text
∀ {Info : Type u_1} {Object : Type u_2} {Name : Type u_3},
[Countable Info] [Countable Object] [Nonempty Object],
∀ naming : Naming Name Object, ∀ allowable : Object → Set (Nat → Info),
(∀ object, (allowable object).Countable) →
  (Identifiable naming allowable → Distinguishable allowable) ∧
  ((CollapsingUncertainty allowable →
      ∀ enumeration : Nat → Object, Surjective enumeration →
        Identifies naming allowable
          (identificationByEnumeration naming allowable enumeration)) ∧
   (Distinguishable allowable → Identifiable naming allowable)).

Identifiable naming allowable :=
  ∃ learner : List Info → Name,
    ∀ object, ∀ stream, stream ∈ allowable object →
      ∃ name : Name, naming.denotes name = object ∧
        ∃ T : Nat, ∀ t : Nat, T ≤ t → learner (textPrefix stream t) = name.

Distinguishable allowable :=
  ∀ object₁ object₂ stream,
    stream ∈ allowable object₁ → stream ∈ allowable object₂ → object₁ = object₂.

CollapsingUncertainty allowable :=
  ∀ target stream, stream ∈ allowable target →
    ∀ object, object ≠ target → ∃ T : Nat, ∀ t : Nat, T ≤ t →
      ¬ Compatible allowable (textPrefix stream t) object.

Compatible allowable history object :=
  ∃ stream', stream' ∈ allowable object ∧
    textPrefix stream' history.length = history.
```

**Learner information, named procedure and computation boundary.** The learner's varying input is only a finite list history. Its fixed parameters are naming, allowable and enumeration. Define K(h) = { i : Nat | ∃ s, s ∈ allowable (enumeration i) ∧ textPrefix s h.length = h }. firstCompatibleIndex returns Nat.find of this predicate when K(h) is inhabited and returns 0 otherwise, using Classical.propDecidable both for existence and individual compatibility. identificationByEnumeration then returns naming.nameOf (enumeration (firstCompatibleIndex allowable enumeration h)). This examines compatibility with an entire allowable infinite extension as a semantic predicate; it does not receive the true object, the actual future stream, or a stopping certificate. There is no explicit recursive state or update in the definition: on each supplied history it recomputes the named selection. One may store the history and append the next datum to reproduce its inputs. Least compatible selection on an unbounded Nat domain plus arbitrary infinite-extension compatibility is not certified as ordinary effective computation. No explicit oracle interface is present either; describing oracle access would be an additional realization assumption. The third implication supplies an unspecified semantic learner; it must not be equated to this named learner from the theorem type.

**Edge cases and limits of the statement:**

- All three displayed conclusion components retain the common Countable Info, Countable Object, Nonempty Object and per-object countability hypotheses; the reconstruction does not strip hypotheses from individual implications merely because a proof might not need them.
- No countability, decidable equality, or effective coding assumption is made on Name. Naming includes a chosen right inverse nameOf; it is not just a possibly non-surjective denotation function. Denotes may have several names for one object, but convergence fixes one name on each stream.
- Countable Info does not itself make the set of infinite streams countable. The separate assumption that each allowable object is a countable set of streams is material and has not been dropped.
- An object may have no allowable streams. Identification for that object is then vacuous, and its overlap/collapsing requirements have no allowed-stream instance. The theorem does not assume any allowable stream exists. Object itself cannot be empty, because Nonempty Object is an explicit binder; a Naming then also supplies names.
- enumeration need only be surjective; repeated indices denoting the same object are permitted. Histories need not be valid in the function definition. If no enumerated object is compatible, the index fallback is 0 and the output is nameOf (enumeration 0), with no correctness promise for that invalid history. On a valid target prefix and a surjective enumeration, the target itself provides a compatible candidate.
- Collapsing times may depend on naming-independent target, stream, allowable map and the individual competing object. The identification name and convergence time are chosen after target and stream (and after fixed learner parameters); the time can also depend on the chosen name. No one time for all objects, streams, or competing objects is asserted.
- t is prefix length: textPrefix stream 0 = [] and textPrefix stream t consists of stream 0 through stream (t−1). The all-future condition includes t = T. There is no guaranteed correct output before T, no computable stopping test, rate, explicit constant, bounded number of changes or finite-data identification announcement.
- The first and third components jointly give a semantic equivalence between Identifiable and Distinguishable under the common assumptions. No component states Distinguishable → CollapsingUncertainty, or replaces the third component by a named enumeration algorithm guarantee.

**Recursively reviewed native definitions/constructors** (exact values/signatures in the appendix):

- `GenLimit.Gold.Abstract.Allowable`
- `GenLimit.Gold.Abstract.CollapsingUncertainty`
- `GenLimit.Gold.Abstract.Compatible`
- `GenLimit.Gold.Abstract.Distinguishable`
- `GenLimit.Gold.Abstract.Identifiable`
- `GenLimit.Gold.Abstract.Identifies`
- `GenLimit.Gold.Abstract.IdentifiesOn`
- `GenLimit.Gold.Abstract.Naming`
- `GenLimit.Gold.Abstract.Naming.denotes`
- `GenLimit.Gold.Abstract.Naming.mk`
- `GenLimit.Gold.Abstract.Naming.nameOf`
- `GenLimit.Gold.Abstract.firstCompatibleIndex`
- `GenLimit.Gold.Abstract.identificationByEnumeration`
- `GenLimit.IdentifiesInLimit`
- `GenLimit.Learner`
- `GenLimit.StabilizesTo`
- `GenLimit.textPrefix`

**Review limit.** Stage 1 reconstructs exported interfaces and definition values only. Theorem proofs, fresh compilation, source-paper correspondence, effectiveness proofs, and human certification were not reviewed.


## Target D2: `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily`

**Locator:** `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:170`. Kind: `theorem`. Linked slots: C03. Universe parameters: `(none)`.

**Exact exported type:**

```lean
∀ (C : GenLimit.LanguageFamily),
  GenLimit.Gold.Informant.IdentifiesFamilyFromInformant C (GenLimit.Gold.Informant.informantEnumerationLearner C)
```

**Precise reconstruction.** For every arbitrary family C : Nat → Set Nat, the specific informantEnumerationLearner C identifies every indexed language C z on every complete, correctly labeled informant for it. An informant is a sequence of pairs (u,b) with b = true iff u belongs to C z at every position, and each natural u appearing at some position. For each z and each such informant, there are an index n with C n = C z and a time T such that at every t ≥ T the learner on the first t labeled data outputs exactly n. It need not stabilize to the supplied target index z. At a history h it considers only indices i < length h that agree with every label in h, outputs their least element if any, and otherwise outputs 0. No computability or decidability of C is assumed.

**Expanded quantifier skeleton and dependencies:**

```text
∀ C : Nat → Set Nat, ∀ z : Nat, ∀ info : Nat → (Nat × Bool),
IsInformantFor info (C z) →
  ∃ n : Nat, C n = C z ∧
    ∃ T : Nat, ∀ t : Nat, T ≤ t →
      informantEnumerationLearner C (textPrefix info t) = n.

IsInformantFor info L packages BOTH:
  (∀ t : Nat, (info t).2 = true ↔ (info t).1 ∈ L), and
  (∀ u : Nat, ∃ t : Nat, (info t).1 = u).
```

**Learner information, named procedure and computation boundary.** At h : List (Nat × Bool), informantCompatibleIndices C h is the finite filter {i ∈ Finset.range h.length | InformantCompatible h (C i)}. Compatibility says ∀ datum ∈ h, datum.2 = true ↔ datum.1 ∈ C i. leastCandidateWithFallback selects Finset.min' on a nonempty candidate set and the given fallback otherwise; informantEnumerationLearnerWithFallback supplies that wrapper, and informantEnumerationLearner fixes fallback = 0. Thus only indices 0,…,h.length−1 are examined, with finite checks against all observed pairs; h.length is available from the input. There is no independent persistent state/update field; a history-fed implementation can append each new labeled datum and recompute. C is a fixed semantic family parameter, potentially noncomputable. The exported filter's dependency metadata explicitly includes Classical.propDecidable. With an additional uniform membership decision mechanism for (i,u) ↦ u ∈ C i, finite candidate construction and minimum selection could be carried out, but the supplied theorem asserts no such mechanism, computability, running-time bound, or oracle type. The learner never reads the actual future informant or its target index z.

**Edge cases and limits of the statement:**

- C is a Nat-indexed family with no injectivity, decidability, effectiveness or surjectivity onto all languages required. z is arbitrary. Different indices can denote the same language, so the stable index n need not equal z; the exact theorem does not assert that n is the least correct index.
- The whole learner is fixed once C is fixed, before z and info. The witnesses n and T can depend on C, z and the entire valid info in the proposition; those values are not additional learner inputs. There is no convergence rate uniform over texts or target indices.
- Correctness supplies both positive and negative labels: false is forced for numbers outside the language, true for numbers inside. Completeness requires each natural number at least once; it imposes no order, no bounded delay, and no requirement of infinitely many occurrences. Repeated numbers and repeated labeled data are allowed.
- At the empty history the candidate range is empty and output is 0. At a nonempty history with no compatible candidate in the finite range, output is again 0 even if C 0 disagrees with the history. The definition remains total on inconsistent histories, whereas the theorem guarantees convergence only for complete correct informants.
- Finite, infinite, empty and full-Nat target languages can all be family entries. In particular the empty language has complete informants with every label false, so the positive-text empty-language vacuity does not apply here.
- Only indices below history.length are tested. Target z need not yet be in this range early in the run; it enters when length exceeds z. The theorem is eventual fixed-index identification, not all-time consistency or all-time correctness.
- The output is a family index whose entire language equals C z. The target is not learned merely pointwise on any fixed finite set of test numbers, nor by success infinitely often, by limsup, in probability or in density.

**Recursively reviewed native definitions/constructors** (exact values/signatures in the appendix):

- `GenLimit.Gold.Informant.IdentifiesFamilyFromInformant`
- `GenLimit.Gold.Informant.IdentifiesOnInformant`
- `GenLimit.Gold.Informant.InformantCompatible`
- `GenLimit.Gold.Informant.InformantComplete`
- `GenLimit.Gold.Informant.InformantCorrect`
- `GenLimit.Gold.Informant.InformantDatum`
- `GenLimit.Gold.Informant.InformantLearner`
- `GenLimit.Gold.Informant.InformantStream`
- `GenLimit.Gold.Informant.IsInformantFor`
- `GenLimit.Gold.Informant.IsInformantFor.mk`
- `GenLimit.Gold.Informant.informantCompatibleIndices`
- `GenLimit.Gold.Informant.informantEnumerationLearner`
- `GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback`
- `GenLimit.Gold.Text.Naming`
- `GenLimit.Gold.Text.Naming.language`
- `GenLimit.Gold.Text.Naming.mk`
- `GenLimit.Gold.Text.familyNaming`
- `GenLimit.Language`
- `GenLimit.LanguageFamily`
- `GenLimit.StabilizesTo`
- `GenLimit.Support.leastCandidateWithFallback`
- `GenLimit.textPrefix`

**Review limit.** Stage 1 reconstructs exported interfaces and definition values only. Theorem proofs, fresh compilation, source-paper correspondence, effectiveness proofs, and human certification were not reviewed.


## Target D3: `GenLimit.Gold.Text.finiteLanguages_identifiableWith`

**Locator:** `GenLimit.Paper00_LanguageIdentification.Text.Finite:127`. Kind: `theorem`. Linked slots: C05. Universe parameters: `(none)`.

**Exact exported type:**

```lean
@GenLimit.Gold.Text.IdentifiableWith.{0} (Finset.{0} Nat) GenLimit.Gold.Text.finiteNaming
  GenLimit.Gold.Text.finiteLanguages
```

**Precise reconstruction.** There exists one total learner M : List Nat → Finset Nat such that for every finite language L : Set Nat and every infinite sequence stream : Nat → Nat whose range is exactly L, there exist a finite-set name F and a time T with (F : Set Nat) = L and, for every t ≥ T, M applied to the first t entries of stream equals F. M is chosen before L and stream; F and T are quantified after them. The naming is fixed to finiteNaming, which denotes a finite set by its underlying set. This theorem's type asserts existence and does not select a witness M; the other supplied target separately certifies finiteLearner.

**Expanded quantifier skeleton and dependencies:**

```text
∃ M : List Nat → Finset Nat,
  ∀ L : Set Nat, Set.Finite L →
    ∀ stream : Nat → Nat, Set.range stream = L →
      ∃ F : Finset Nat, (F : Set Nat) = L ∧
        ∃ T : Nat, ∀ t : Nat, T ≤ t → M (textPrefix stream t) = F.
```

**Learner information, named procedure and computation boundary.** The theorem supplies an existential total history-to-Finset function, not a named program in its type. It sees only a finite positive history. The separate reviewed target finiteLearner_identifiesFiniteLanguages certifies the concrete List.toFinset rule under the same finiteNaming and class; that is a separate named-witness guarantee, not additional syntax inside this existence theorem. No family membership oracle or information about the future is supplied to the existential learner. No computability predicate occurs in this theorem.

**Edge cases and limits of the statement:**

- finiteLanguages contains the empty language as well as all nonempty finite subsets. Presents stream ∅ cannot hold for a total Nat → Nat stream, because its range contains stream 0. Therefore identification of the empty target in this positive-text model is vacuous; there are no blank/pause symbols or finite texts in these definitions.
- Texts may repeat elements, start in any order and delay any particular target element arbitrarily, but their range must be exactly L. A merely sound stream whose range is a proper subset of L is not a presentation and is outside the guarantee.
- M is uniform across all finite L and all valid texts. F and T occur after stream; the formal witness dependency is per text, although equality of its underlying set with L fixes F extensionally. There is no uniform bound on T, no bound in terms of |L| in the type, and no requirement that a learner recognize convergence.
- The conclusion is exact eventual constancy of one Finset name. It is not generation of a fresh element, eventual subset correctness, a support loss, or a probability law.
- This existential target has no named witness in its statement. The separate named finiteLearner target is reviewed, but proof-level selection of the witness in this theorem was not inspected.

**Recursively reviewed native definitions/constructors** (exact values/signatures in the appendix):

- `GenLimit.Gold.Text.IdentifiableWith`
- `GenLimit.Gold.Text.IdentifiesClass`
- `GenLimit.Gold.Text.IdentifiesLanguage`
- `GenLimit.Gold.Text.IdentifiesOnText`
- `GenLimit.Gold.Text.Naming`
- `GenLimit.Gold.Text.Naming.language`
- `GenLimit.Gold.Text.Naming.mk`
- `GenLimit.Gold.Text.TextLearner`
- `GenLimit.Gold.Text.finiteLanguages`
- `GenLimit.Gold.Text.finiteNaming`
- `GenLimit.IdentifiesInLimit`
- `GenLimit.Language`
- `GenLimit.Learner`
- `GenLimit.Presents`
- `GenLimit.StabilizesTo`
- `GenLimit.textPrefix`

**Review limit.** Stage 1 reconstructs exported interfaces and definition values only. Theorem proofs, fresh compilation, source-paper correspondence, effectiveness proofs, and human certification were not reviewed.


## Target D4: `GenLimit.Gold.Text.finiteLanguages_maximal_semanticallyIdentifiable`

**Locator:** `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:229`. Kind: `theorem`. Linked slots: C06. Universe parameters: `(none)`.

**Exact exported type:**

```lean
And (GenLimit.Gold.Text.SemanticallyIdentifiable GenLimit.Gold.Text.finiteLanguages)
  (∀ (𝒞 : Set.{0} GenLimit.Language),
    @HasSSubset.SSubset.{0} (Set.{0} GenLimit.Language) (@Set.instHasSSubset.{0} GenLimit.Language)
        GenLimit.Gold.Text.finiteLanguages 𝒞 →
      Not (GenLimit.Gold.Text.SemanticallyIdentifiable 𝒞))
```

**Precise reconstruction.** Both of the following hold. First, the class of all finite subsets of Nat is semantically identifiable: some total M : List Nat → Set Nat eventually outputs exactly the target set on every positive text for every finite target. Second, for every class 𝒞 : Set (Set Nat) that strictly contains the entire class of finite languages, there does not exist any such semantic learner identifying all members of 𝒞. A positive text is an infinite Nat sequence with range exactly its language. Semantic identification still uses eventual constancy of the output name, but here names themselves are sets and semanticNaming is the identity. The theorem asserts maximality under strict class inclusion, not that every identifiable class is contained in the finite languages, not uniqueness of maximal classes, and not computable maximality.

**Expanded quantifier skeleton and dependencies:**

```text
(∃ M : List Nat → Set Nat,
   ∀ L : Set Nat, Set.Finite L →
     ∀ stream : Nat → Nat, Set.range stream = L →
       ∃ name : Set Nat, name = L ∧
         ∃ T : Nat, ∀ t : Nat, T ≤ t → M (textPrefix stream t) = name)
∧
(∀ 𝒞 : Set (Set Nat), finiteLanguages ⊂ 𝒞 →
   ¬ ∃ M : List Nat → Set Nat,
       ∀ L : Set Nat, L ∈ 𝒞 →
         ∀ stream : Nat → Nat, Set.range stream = L →
           ∃ name : Set Nat, name = L ∧
             ∃ T : Nat, ∀ t : Nat, T ≤ t → M (textPrefix stream t) = name).
```

**Learner information, named procedure and computation boundary.** The positive conjunct existentially chooses one total set-valued function on finite positive histories for the finite-language class. The negative conjunct denies existence of any such function for each proper extension. semanticNaming.language is the identity on Set Nat, so a semantic output denotes itself; this is not a natural-number program code or a uniform membership algorithm. No named algorithm appears in this type, and no source or proof was used to select its positive witness. Quantification over functions permits mathematical noncomputable learners; no oracle model, effective coding, resource bound or decision procedure is specified.

**Edge cases and limits of the statement:**

- The outermost And must retain both the existence assertion for finiteLanguages and the universal nonexistence assertion for every strict superset. Equality with finiteLanguages does not satisfy the strict-inclusion antecedent. Classes missing some finite languages are not covered by that implication.
- 𝒞 is an arbitrary set of languages, not a Nat-indexed family and not required to be countable. Strict superset means it contains all finite languages and has an additional member; the theorem states set-inclusion maximality and no comparison with incomparable classes.
- The positive witness M is chosen before all finite targets and all presentations. In the negative conjunct, the denied M could depend on the entire fixed 𝒞 but would have to work for all L ∈ 𝒞 and all texts. A stabilized semantic name equals the target L; convergence times remain per language/text.
- Semantic learners are arbitrary set-valued functions; semanticNaming makes equality of names extensional equality of sets. The positive conjunct is not an assertion about a specific numbered hypothesis system or an effective set representation.
- The empty language has no valid Nat-valued positive presentation, so its per-text requirement is vacuous. This does not remove it from finiteLanguages or from the inclusion condition.
- No rate, error bound, sample complexity, probability distribution, finite-support law, causal counterexample constructor or effective adversary is stated. Only eventual all-times equality after a per-run T occurs.

**Recursively reviewed native definitions/constructors** (exact values/signatures in the appendix):

- `GenLimit.Gold.Text.IdentifiesClass`
- `GenLimit.Gold.Text.IdentifiesLanguage`
- `GenLimit.Gold.Text.IdentifiesOnText`
- `GenLimit.Gold.Text.Naming`
- `GenLimit.Gold.Text.Naming.language`
- `GenLimit.Gold.Text.Naming.mk`
- `GenLimit.Gold.Text.SemanticallyIdentifiable`
- `GenLimit.Gold.Text.SemanticallyIdentifiesClass`
- `GenLimit.Gold.Text.TextLearner`
- `GenLimit.Gold.Text.finiteLanguages`
- `GenLimit.Gold.Text.semanticNaming`
- `GenLimit.IdentifiesInLimit`
- `GenLimit.Language`
- `GenLimit.Learner`
- `GenLimit.Presents`
- `GenLimit.StabilizesTo`
- `GenLimit.textPrefix`

**Review limit.** Stage 1 reconstructs exported interfaces and definition values only. Theorem proofs, fresh compilation, source-paper correspondence, effectiveness proofs, and human certification were not reviewed.


## Target D5: `GenLimit.Gold.Text.finiteLearner_identifiesFiniteLanguages`

**Locator:** `GenLimit.Paper00_LanguageIdentification.Text.Finite:120`. Kind: `theorem`. Linked slots: C05. Universe parameters: `(none)`.

**Exact exported type:**

```lean
@GenLimit.Gold.Text.IdentifiesClass.{0} (Finset.{0} Nat) GenLimit.Gold.Text.finiteNaming
  GenLimit.Gold.Text.finiteLearner GenLimit.Gold.Text.finiteLanguages
```

**Precise reconstruction.** The specifically defined total learner finiteLearner : List Nat → Finset Nat identifies every finite language using finiteNaming. For every finite L and every stream : Nat → Nat with range exactly L, there are F : Finset Nat and T : Nat such that (F : Set Nat) = L and for every t ≥ T, finiteLearner (textPrefix stream t) = F. Its exact rule is List.toFinset: output the finite set of all distinct entries in the observed history. The theorem fixes this witness before all target languages and all texts.

**Expanded quantifier skeleton and dependencies:**

```text
∀ L : Set Nat, Set.Finite L →
  ∀ stream : Nat → Nat, Set.range stream = L →
    ∃ F : Finset Nat, (F : Set Nat) = L ∧
      ∃ T : Nat, ∀ t : Nat, T ≤ t →
        finiteLearner (textPrefix stream t) = F.

finiteLearner history = history.toFinset.
```

**Learner information, named procedure and computation boundary.** finiteLearner is exactly @List.toFinset Nat instDecidableEqNat. At history h it returns all distinct observed natural numbers. An equivalent history-fed state description is F₀ = ∅, F at the next datum u is F ∪ {u}, and output F; this is a definition-level description of toFinset and not an inspected proof or an additional target theorem. There are no fixed target, class, family, language-membership or future-stream parameters. This particular operation on finite Nat lists uses decidable Nat equality and is directly computable in the ordinary sense; the theorem itself does not package a computability proof or a time/memory complexity claim. The output is a single finite-set name, not a generated data point, support distribution, or random law.

**Edge cases and limits of the statement:**

- For the empty history finiteLearner returns the empty Finset. On a valid text each output is the set of entries in the prefix, with repetitions removed. At prefix length t it has not yet observed stream t.
- Every finite language is in the class, including ∅; however ∅ has no total Nat-valued text of range ∅, so its identification clause is vacuous. The rule at [] is still explicitly defined.
- For nonempty finite L a valid text eventually has displayed every member; arbitrary repetitions and delays are allowed. There is no bound on when this happens from cardinality alone in the type, and no termination/recognition condition. These observations explain the statement without certifying its proof.
- A stream of range properly contained in L, or with any element outside L, fails Presents stream L and receives no target-L guarantee. Infinite languages are not in the quantified class. Function totality still defines outputs on all finite lists.
- The witnesses F and T follow L and stream; the named learner itself is fixed globally. Stability is exact Finset equality at every t ≥ T, not just semantic equality of a moving finite-set code.
- The finite-prefix output can be described by set insertion and is computable from observations alone; no claim about resource complexity is attached to the theorem.

**Recursively reviewed native definitions/constructors** (exact values/signatures in the appendix):

- `GenLimit.Gold.Text.IdentifiesClass`
- `GenLimit.Gold.Text.IdentifiesLanguage`
- `GenLimit.Gold.Text.IdentifiesOnText`
- `GenLimit.Gold.Text.Naming`
- `GenLimit.Gold.Text.Naming.language`
- `GenLimit.Gold.Text.Naming.mk`
- `GenLimit.Gold.Text.TextLearner`
- `GenLimit.Gold.Text.finiteLanguages`
- `GenLimit.Gold.Text.finiteLearner`
- `GenLimit.Gold.Text.finiteNaming`
- `GenLimit.IdentifiesInLimit`
- `GenLimit.Language`
- `GenLimit.Learner`
- `GenLimit.Presents`
- `GenLimit.StabilizesTo`
- `GenLimit.textPrefix`

**Review limit.** Stage 1 reconstructs exported interfaces and definition values only. Theorem proofs, fresh compilation, source-paper correspondence, effectiveness proofs, and human certification were not reviewed.


## Target D6: `GenLimit.Gold.Text.superfinite_not_semanticallyIdentifiable`

**Locator:** `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:183`. Kind: `theorem`. Linked slots: C06. Universe parameters: `(none)`.

**Exact exported type:**

```lean
∀ {𝒞 : Set.{0} GenLimit.Language},
  GenLimit.Gold.Text.IsSuperfinite 𝒞 → Not (GenLimit.Gold.Text.SemanticallyIdentifiable 𝒞)
```

**Precise reconstruction.** For every class 𝒞 : Set (Set Nat), if 𝒞 contains every finite language and also contains at least one infinite language L, then no total semantic finite-history learner M : List Nat → Set Nat identifies every language in 𝒞 on every positive text for it. IsSuperfinite is exactly the conjunction of finiteLanguages ⊆ 𝒞 and ∃ L, L ∈ 𝒞 ∧ Set.Infinite L. Semantic identification means eventual equality of the learner's entire output set with its target on each valid text. The negation ranges over all total set-valued learners, not merely a named procedure or an effective subclass.

**Expanded quantifier skeleton and dependencies:**

```text
∀ {𝒞 : Set (Set Nat)},
  ((finiteLanguages ⊆ 𝒞) ∧
    (∃ L : Set Nat, L ∈ 𝒞 ∧ Set.Infinite L)) →
  ¬ ∃ M : List Nat → Set Nat,
      ∀ L : Set Nat, L ∈ 𝒞 →
        ∀ stream : Nat → Nat, Set.range stream = L →
          ∃ name : Set Nat, name = L ∧
            ∃ T : Nat, ∀ t : Nat, T ≤ t → M (textPrefix stream t) = name.
```

**Learner information, named procedure and computation boundary.** No named algorithm is selected or refuted individually. The quantified learner type is List Nat → Set Nat; the negative conclusion excludes every such total semantic function if the premise holds. The learner can be tailored to the fixed class 𝒞 but its value on a run is a function only of the finite positive history. Arbitrary semantic dependence on 𝒞 is permitted by existential choice, without effectiveness or an oracle interface. The theorem does not posit a causal adversary or an effective counterexample-generation procedure.

**Edge cases and limits of the statement:**

- Both premise components are essential to the stated scope: containment of every finite language, and membership of at least one infinite language. The existence of an infinite member alone does not instantiate IsSuperfinite, and finiteLanguages itself fails the infinite-member component.
- The infinite-language witness can depend on 𝒞. No specific infinite language, family enumeration, countability of 𝒞, effective representation or decidability assumption appears.
- The conclusion is literally Not (∃ M, ...). It excludes one learner working uniformly over the whole class; it does not say each individual language is unlearnable, that every learner fails on every member, or that a fixed one counterexample works for all learners.
- The type does not give a constructive/effective counterexample informant/text or a program for finding a failing language for any input learner. Proof bodies were not inspected.
- Semantic convergence means eventual equality of the entire output set, not membershipwise limits or eventual correct denotations with oscillating names. There are no rates, constants, random distributions, losses, or frequency/limsup conclusions.
- As with the other positive-text targets, the empty language has no valid Nat-valued presentation and its positive-text identification clause is vacuous. Invalid or incomplete texts impose no identification requirement.

**Recursively reviewed native definitions/constructors** (exact values/signatures in the appendix):

- `GenLimit.Gold.Text.ContainsAllFiniteLanguages`
- `GenLimit.Gold.Text.IdentifiesClass`
- `GenLimit.Gold.Text.IdentifiesLanguage`
- `GenLimit.Gold.Text.IdentifiesOnText`
- `GenLimit.Gold.Text.IsSuperfinite`
- `GenLimit.Gold.Text.Naming`
- `GenLimit.Gold.Text.Naming.language`
- `GenLimit.Gold.Text.Naming.mk`
- `GenLimit.Gold.Text.SemanticallyIdentifiable`
- `GenLimit.Gold.Text.SemanticallyIdentifiesClass`
- `GenLimit.Gold.Text.TextLearner`
- `GenLimit.Gold.Text.finiteLanguages`
- `GenLimit.Gold.Text.semanticNaming`
- `GenLimit.IdentifiesInLimit`
- `GenLimit.Language`
- `GenLimit.Learner`
- `GenLimit.Presents`
- `GenLimit.StabilizesTo`
- `GenLimit.textPrefix`

**Review limit.** Stage 1 reconstructs exported interfaces and definition values only. Theorem proofs, fresh compilation, source-paper correspondence, effectiveness proofs, and human certification were not reviewed.


## Exhaustive slot coverage

Endpoint registration is taken only from `claim-slots.json`. No missing source statement has been supplied or inferred.

| Slot | Reviewed supplied declarations | Disposition |
|---|---|---|
| C01 | `GenLimit.Gold.Abstract.gold_theorem_7_1` (D1) | Complete code-only reconstruction of all supplied endpoints; no source/proof certification. |
| C02 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C03 | `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily` (D2) | Complete code-only reconstruction of all supplied endpoints; no source/proof certification. |
| C04 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C05 | `GenLimit.Gold.Text.finiteLanguages_identifiableWith` (D3), `GenLimit.Gold.Text.finiteLearner_identifiesFiniteLanguages` (D5) | Complete code-only reconstruction of all supplied endpoints; no source/proof certification. |
| C06 | `GenLimit.Gold.Text.finiteLanguages_maximal_semanticallyIdentifiable` (D4), `GenLimit.Gold.Text.superfinite_not_semanticallyIdentifiable` (D6) | Complete code-only reconstruction of all supplied endpoints; no source/proof certification. |
| C07 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C08 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C09 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C10 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C11 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C12 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C13 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C14 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C15 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C16 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |
| C17 | None supplied | No registered Lean endpoint; no source-claim reconstruction possible from this slot. |

The 13 empty slots are C02, C04 and C07–C17. Each has an empty declarations array, an empty linked-names-absent array and `no_registered_lean_endpoint = true`. This establishes only lack of a supplied endpoint in the frozen slot mapping; it does not prove the claim is absent from all code or describe what the source claim says. The full census was not used to infer mappings for these slots.

## Exact recursive native dependency appendix

These are the 51 non-theorem records from `declarations.jsonl`. Together with the six exact target types above they exhaust the 57-record supplied recursion. Definition bodies are mathematical data for reconstruction; theorem proof values are absent and were not read. `null` values on inductives/constructors indicate that constructor interfaces, not proof bodies, are supplied. No original source comments or proofs were opened.


### `GenLimit.Gold.Abstract.Allowable`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:24`.

```lean
Type uInfo → Type uObject → Type (max uObject uInfo)
```

Exact definition value:

```lean
fun Info Object => Object → Set.{uInfo} (Nat → Info)
```


### `GenLimit.Gold.Abstract.CollapsingUncertainty`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:69`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:40`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:57`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:94`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:86`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:78`.

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

Kind: `inductive`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:33`.

```lean
Type uName → Type uObject → Type (max uName uObject)
```

Constructors: `GenLimit.Gold.Abstract.Naming.mk`.


### `GenLimit.Gold.Abstract.Naming.denotes`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:34`.

```lean
{Name : Type uName} →
  {Object : Type uObject} → GenLimit.Gold.Abstract.Naming.{uObject, uName} Name Object → Name → Object
```

Exact definition value:

```lean
fun Name Object self => self.1
```


### `GenLimit.Gold.Abstract.Naming.mk`

Kind: `constructor`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:33`.

```lean
{Name : Type uName} →
  {Object : Type uObject} →
    (denotes : Name → Object) →
      (nameOf : Object → Name) →
        (∀ (object : Object), @Eq.{uObject + 1} Object (denotes (nameOf object)) object) →
          GenLimit.Gold.Abstract.Naming.{uObject, uName} Name Object
```


### `GenLimit.Gold.Abstract.Naming.nameOf`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:35`.

```lean
{Name : Type uName} →
  {Object : Type uObject} → GenLimit.Gold.Abstract.Naming.{uObject, uName} Name Object → Object → Name
```

Exact definition value:

```lean
fun Name Object self => self.2
```


### `GenLimit.Gold.Abstract.firstCompatibleIndex`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:133`.

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


### `GenLimit.Gold.Abstract.identificationByEnumeration`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Abstract.Model:145`.

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


### `GenLimit.Gold.Informant.IdentifiesFamilyFromInformant`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Model:144`.

```lean
GenLimit.LanguageFamily → GenLimit.Gold.Informant.InformantLearner.{0} Nat → Prop
```

Exact definition value:

```lean
fun C M =>
  ∀ (z : Nat) (info : GenLimit.Gold.Informant.InformantStream),
    GenLimit.Gold.Informant.IsInformantFor info (C z) →
      @GenLimit.Gold.Informant.IdentifiesOnInformant.{0} Nat (GenLimit.Gold.Text.familyNaming C) M info (C z)
```


### `GenLimit.Gold.Informant.IdentifiesOnInformant`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Model:136`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Model:45`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Model:35`.

```lean
GenLimit.Gold.Informant.InformantStream → Prop
```

Exact definition value:

```lean
fun info => ∀ (u : Nat), ∃ t, @Eq.{1} Nat (@Prod.fst.{0, 0} Nat Bool (info t)) u
```


### `GenLimit.Gold.Informant.InformantCorrect`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Model:31`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Model:25`.

```lean
Type
```

Exact definition value:

```lean
Prod.{0, 0} Nat Bool
```


### `GenLimit.Gold.Informant.InformantLearner`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Model:132`.

```lean
Type u_1 → Type (max u_1 0)
```

Exact definition value:

```lean
fun Name => List.{0} GenLimit.Gold.Informant.InformantDatum → Name
```


### `GenLimit.Gold.Informant.InformantStream`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Model:28`.

```lean
Type
```

Exact definition value:

```lean
Nat → GenLimit.Gold.Informant.InformantDatum
```


### `GenLimit.Gold.Informant.IsInformantFor`

Kind: `inductive`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Model:39`.

```lean
GenLimit.Gold.Informant.InformantStream → GenLimit.Language → Prop
```

Constructors: `GenLimit.Gold.Informant.IsInformantFor.mk`.


### `GenLimit.Gold.Informant.IsInformantFor.mk`

Kind: `constructor`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Model:39`.

```lean
∀ {info : GenLimit.Gold.Informant.InformantStream} {L : GenLimit.Language},
  GenLimit.Gold.Informant.InformantCorrect info L →
    GenLimit.Gold.Informant.InformantComplete info → GenLimit.Gold.Informant.IsInformantFor info L
```


### `GenLimit.Gold.Informant.informantCompatibleIndices`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:46`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:69`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:61`.

```lean
GenLimit.LanguageFamily → Nat → GenLimit.Gold.Informant.InformantLearner.{0} Nat
```

Exact definition value:

```lean
fun C fallback history =>
  @GenLimit.Support.leastCandidateWithFallback.{0} Nat Nat.instLinearOrder
    (GenLimit.Gold.Informant.informantCompatibleIndices C history) fallback
```


### `GenLimit.Gold.Text.ContainsAllFiniteLanguages`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:171`.

```lean
Set.{0} GenLimit.Language → Prop
```

Exact definition value:

```lean
fun 𝒞 =>
  @HasSubset.Subset.{0} (Set.{0} GenLimit.Language) (@Set.instHasSubset.{0} GenLimit.Language)
    GenLimit.Gold.Text.finiteLanguages 𝒞
```


### `GenLimit.Gold.Text.IdentifiableWith`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:50`.

```lean
{Name : Type u_1} → GenLimit.Gold.Text.Naming.{u_1} Name → Set.{0} GenLimit.Language → Prop
```

Exact definition value:

```lean
fun {Name} N 𝒞 => ∃ M, @GenLimit.Gold.Text.IdentifiesClass.{u_1} Name N M 𝒞
```


### `GenLimit.Gold.Text.IdentifiesClass`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:44`.

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


### `GenLimit.Gold.Text.IdentifiesLanguage`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:39`.

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

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:33`.

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


### `GenLimit.Gold.Text.IsSuperfinite`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:176`.

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


### `GenLimit.Gold.Text.Naming`

Kind: `inductive`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:25`.

```lean
Type u_1 → Type u_1
```

Constructors: `GenLimit.Gold.Text.Naming.mk`.


### `GenLimit.Gold.Text.Naming.language`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:26`.

```lean
{Name : Type u_1} → GenLimit.Gold.Text.Naming.{u_1} Name → Name → GenLimit.Language
```

Exact definition value:

```lean
fun Name self => self.1
```


### `GenLimit.Gold.Text.Naming.mk`

Kind: `constructor`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:25`.

```lean
{Name : Type u_1} → (Name → GenLimit.Language) → GenLimit.Gold.Text.Naming.{u_1} Name
```


### `GenLimit.Gold.Text.SemanticallyIdentifiable`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:75`.

```lean
Set.{0} GenLimit.Language → Prop
```

Exact definition value:

```lean
fun 𝒞 => ∃ M, GenLimit.Gold.Text.SemanticallyIdentifiesClass M 𝒞
```


### `GenLimit.Gold.Text.SemanticallyIdentifiesClass`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:70`.

```lean
GenLimit.Gold.Text.TextLearner.{0} GenLimit.Language → Set.{0} GenLimit.Language → Prop
```

Exact definition value:

```lean
fun M 𝒞 => @GenLimit.Gold.Text.IdentifiesClass.{0} GenLimit.Language GenLimit.Gold.Text.semanticNaming M 𝒞
```


### `GenLimit.Gold.Text.TextLearner`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:30`.

```lean
Type u_1 → Type (max u_1 0)
```

Exact definition value:

```lean
fun Name => GenLimit.Learner.{0, u_1} Nat Name
```


### `GenLimit.Gold.Text.familyNaming`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:55`.

```lean
GenLimit.LanguageFamily → GenLimit.Gold.Text.Naming.{0} Nat
```

Exact definition value:

```lean
fun C => @GenLimit.Gold.Text.Naming.mk.{0} Nat C
```


### `GenLimit.Gold.Text.finiteLanguages`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Finite:39`.

```lean
Set.{0} GenLimit.Language
```

Exact definition value:

```lean
@setOf.{0} GenLimit.Language fun L => @Set.Finite.{0} Nat L
```


### `GenLimit.Gold.Text.finiteLearner`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Finite:91`.

```lean
GenLimit.Gold.Text.TextLearner.{0} (Finset.{0} Nat)
```

Exact definition value:

```lean
@List.toFinset.{0} Nat instDecidableEqNat
```


### `GenLimit.Gold.Text.finiteNaming`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Finite:87`.

```lean
GenLimit.Gold.Text.Naming.{0} (Finset.{0} Nat)
```

Exact definition value:

```lean
@GenLimit.Gold.Text.Naming.mk.{0} (Finset.{0} Nat) fun F => @Finset.toSet.{0} Nat F
```


### `GenLimit.Gold.Text.semanticNaming`

Kind: `definition`. Exporter locator: `GenLimit.Paper00_LanguageIdentification.Text.Model:65`.

```lean
GenLimit.Gold.Text.Naming.{0} GenLimit.Language
```

Exact definition value:

```lean
@GenLimit.Gold.Text.Naming.mk.{0} GenLimit.Language (@id.{1} GenLimit.Language)
```


### `GenLimit.IdentifiesInLimit`

Kind: `definition`. Exporter locator: `GenLimit.Core.Identification:53`.

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

Kind: `definition`. Exporter locator: `GenLimit.Core.Basic:20`.

```lean
Type
```

Exact definition value:

```lean
Set.{0} Nat
```


### `GenLimit.LanguageFamily`

Kind: `definition`. Exporter locator: `GenLimit.Core.Basic:23`.

```lean
Type
```

Exact definition value:

```lean
Nat → GenLimit.Language
```


### `GenLimit.Learner`

Kind: `definition`. Exporter locator: `GenLimit.Core.Identification:18`.

```lean
Type uInfo → Type uName → Type (max uName uInfo)
```

Exact definition value:

```lean
fun Info Name => List.{uInfo} Info → Name
```


### `GenLimit.Presents`

Kind: `definition`. Exporter locator: `GenLimit.Core.Basic:26`.

```lean
(Nat → Nat) → GenLimit.Language → Prop
```

Exact definition value:

```lean
fun stream L => @Eq.{1} (Set.{0} Nat) (@Set.range.{0, 1} Nat Nat stream) L
```


### `GenLimit.StabilizesTo`

Kind: `definition`. Exporter locator: `GenLimit.Core.Identification:47`.

```lean
{Name : Type uName} → (Nat → Name) → Name → Prop
```

Exact definition value:

```lean
fun {Name} guess name => ∃ T, ∀ (t : Nat), @LE.le.{0} Nat instLENat T t → @Eq.{uName + 1} Name (guess t) name
```


### `GenLimit.Support.leastCandidateWithFallback`

Kind: `definition`. Exporter locator: `GenLimit.Support.LeastCandidate:20`.

```lean
{α : Type u_1} → [LinearOrder.{u_1} α] → Finset.{u_1} α → α → α
```

Exact definition value:

```lean
fun {α} [inst : LinearOrder.{u_1} α] candidates fallback =>
  @dite.{u_1 + 1} α (@Finset.Nonempty.{u_1} α candidates) (@Finset.decidableNonempty.{u_1} α candidates)
    (fun h => @Finset.min'.{u_1} α inst candidates h) fun h => fallback
```


### `GenLimit.textPrefix`

Kind: `definition`. Exporter locator: `GenLimit.Core.Text:16`.

```lean
{α : Type u_1} → (Nat → α) → Nat → List.{u_1} α
```

Exact definition value:

```lean
fun {α} stream t => @List.map.{0, u_1} Nat α stream (List.range t)
```


## Access boundary and completion status

Mathematical evidence was restricted to the supplied Stage 1 directory. No `sources/`, `owner/`, `stage2/`, `stage3-context/`, registry, PaperMap, prior audit, bookkeeping record, raw Lean source/comment/proof, source paper, external research source or parent mathematical history was read. The tool calls performed bounded local reads, hashing, parsing and output validation; no Git operation, library modification, Lean compilation or build was run. Only the three requested result files were written.

All six supplied targets and all 17 slots are accounted for. Correctness of proof bodies, source correspondence, fresh compilation, and human certification remain outside Stage 1. The report and claims hashes are stored in `stage1-run.json`; that manifest intentionally omits a recursively self-referential hash of its own final bytes. Work stops at Stage 1.
