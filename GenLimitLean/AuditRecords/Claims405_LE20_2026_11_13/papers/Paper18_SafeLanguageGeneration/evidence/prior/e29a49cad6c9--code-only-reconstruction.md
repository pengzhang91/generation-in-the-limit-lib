# Stage 1: code-only reconstruction of P18

## Input census and method

This reconstruction concerns exactly eight targets in `GenLimit.Paper18_SafeLanguageGeneration.Results.Overview`. Mathematical evidence was restricted to the supplied `stage1/` interface, including `explicit-target-types/`. Both SHA256 manifests verified: 11 main entries and two supplement entries. The supplement preserves the original signatures and exposes implicit applications; it adds no assumptions. Its eight records agree with the target list. The declaration census is 92 records: 79 definitions, 11 theorem types, one inductive type and one constructor. Eight theorem records are targets; the other three are auxiliary certificate types. No theorem proof value was supplied or inspected.

The principal mathematical inputs are `01-target-statements.md` (SHA256 `e627a72fbb42f0592c01f54520cbb14db33c7c22b6a775c19b073d6c6701941b`), `02-definition-dependencies.md` (`d2950a78d253655ebd946747b1d1f74219d764cb606040fddfa7e19add07f190`), `declarations.jsonl` (`fbd6d42fd3cb700d66901c5a8468385e5d3c34b2a8845cdbfd176d4a3ef5083d`) and the explicit-type records (`8a140819d687dfcd8e4e5251894d375f372da1e8144715666fd640e92cd229e6`). The accompanying run record inventories all 15 input files, including manifests, configuration and boundary metadata, with actual byte hashes.

The snapshot reports a dirty working-tree byte snapshot captured at `2026-11-10T05:49:22.951260+00:00`, branch `work/non-p38`, recorded HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`. These are supplied metadata, not independently checked repository facts. Its 45 source-file entries were not opened. Lean `v4.24.0` and the supplied Mathlib lock are configuration evidence, not a fresh compilation. All source anchors below are exported locators; names contribute no mathematical interpretation. Every target's original printed type is reproduced verbatim.

## Definition glossary and observation model

**Sets, families and prefixes.** `Generic.Language α` is `Set α`; a `LanguageFamily α` is `Nat → Set α`, with no injectivity, effective indexing or decidable membership requirement. `Stream α = Nat → α`. `Presents s L` means `range s = L`. A history operator has type `(t : Nat) → (Fin t → Input) → Output`, so its input is the ordered prefix of length `t`, including repetitions. `sample s t` and `sequenceSample xs` retain only its finite set of observed values. `textPrefix s t` is the list `s 0, …, s (t−1)`. A total ordinary presentation cannot present the empty set.

**Labels.** `Tagged α = α × Bool`. `taggedRange s b = {x | ∃n, s n = (x,b)}`. `LabeledPresents s T H` requires separately that the true-tag range equal `T` and the false-tag range equal `H`. Thus false labels enumerate the harmful set; they do not enumerate the complement of the target. Overlap is allowed: a point in both sets must appear with each label. Each designated member must appear sometime, without a delay bound or a requirement to repeat infinitely often. Either set may be empty if that label never occurs; both empty admit no labeled stream. `historyTaggedSample xs b` selects one label. `historyObservedSample xs` and `observedSample s t` discard labels and include both kinds of observations.

**Output and success.** A `SafeGenerator α` is a total history function returning one `Option α`. `safeOutput G s t = G t (s restricted to Fin t)`. `SafeCorrectAt G T H s t` means that for some `x` the output is `some x`, `x ∈ T \ H`, and `x` is absent from the entire observed prefix, including harmful observations. This is a single-output condition; there is no distribution, support, sampling law or full-support hypothesis. Freshness concerns observations, not earlier generated outputs, so repeated generation of an as-yet-unobserved point is allowed.

`BottomCorrectAt` conjoins **finiteness of `T \ H`** with output `none`. `SafelyGenerates` has two implications: an infinite difference requires `SafeCorrectAt` at every sufficiently large time; a finite difference requires `BottomCorrectAt` at every sufficiently large time. The latter includes empty and nonempty finite differences, regardless of whether every safe point has already been observed. Neither branch restricts earlier mistakes. `EventuallyBottom` merely says the output is eventually always `none`. `SafelyGeneratesFamilies G targets harmfuls` universally quantifies independent indices `i,j` and every labeled presentation of their pair. `SafelyGeneratesInfiniteDifferences` instead directly demands eventual `SafeCorrectAt` on every such presentation. `AllCrossDifferencesInfinite` means `∀ i j, Infinite (targets i \ harmfuls j)`.

Every eventual assertion has form `∃T ∀t, T ≤ t → …`; no uniform rate, computable bound or frequently-only conclusion is asserted. Its threshold may depend on the fixed generator, actual family members and full stream. Equal family entries and repeated indices remain covered. No learner or generator type itself asserts ordinary computability, randomness or a program representation.

**Two identification notions.** `SafeIdentifier α` is a tagged-history operator returning a natural-number index. `identifierOutput` evaluates it on the prefix. `DifferenceRepresented C T H` means `∃i, C i = T \ H`. `SafelyIdentifiesFrom` only requires the *denoted set* of the output index to equal that difference eventually; the index need not stabilize. By contrast `Angluin.SemanticIdentifier α = List α → Nat`; `SemanticallyIdentifies M C` requires, on every ordinary presentation of every `C z`, `IdentifiesInLimit C M s (C z)`. The latter contains `∃k, C k = C z ∧ StabilizesTo (M on prefixes) k`, and `StabilizesTo` fixes one eventual index. These notions differ when duplicate indices denote one set.

**Machine predicates.** `boundedHalts c f` is `isSome (Code.evaln f c 0)`. `leftLanguage = Nat`; `rightLanguage c = {n | n % 2 = 0 ∨ boundedHalts c (n / 2) ≠ true}`. `DiffEmptyInstance c` tests whether their difference is empty. `LanguagePairCode = Code × Code`. `codedLanguage c = {n | Code.eval c n = Part.some 1}`. `TotalBooleanDecider c` means `∀n ∃b : Bool, Code.eval c n = Part.some (encode b)`; the hidden Boolean domain is supported by the exported `Bool`/`Bool.encodable` dependencies. Validity conjoins total Boolean decision for both codes and infinitude of both coded languages. `CodedDiffEmpty` tests emptiness of their set difference. The supplement exposes the product's `Primcodable` instance, so these are ordinary computability predicates on machine codes, not on arbitrary semantic sets.

**Oracles and padding.** `SetDifferenceOracle α = Set α → Set α → Bool`; correctness means `O X Y = true ↔ X \ Y = ∅` for every semantic pair `X,Y`. `OracleSafeAlgorithm α` is simply a function from such an oracle to a safe generator. There is no encoded oracle-query protocol or effectiveness restriction. `verticalPad L = {(x,n) | x ∈ L ∧ 0 < n}`: second coordinate zero is excluded.

## D1 — `GenLimit.SafeGeneration.Results.theorem_3_1`

Source anchor: `GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean:53`.

```lean
And (∀ (i : Nat), Set.Infinite.{0} (GenLimit.SafeGeneration.SafeIdentification.candidateFamily i))
  (And (∀ (j : Nat), Set.Infinite.{0} (GenLimit.SafeGeneration.SafeIdentification.harmfulFamily j))
    (And
      (∀ (j : Nat),
        GenLimit.SafeGeneration.SafeIdentification.DifferenceRepresented.{0}
          GenLimit.SafeGeneration.SafeIdentification.candidateFamily
          (GenLimit.SafeGeneration.SafeIdentification.candidateFamily 0)
          (GenLimit.SafeGeneration.SafeIdentification.harmfulFamily j))
      (∀
        (M :
          GenLimit.SafeGeneration.SafeIdentification.SafeIdentifier.{0}
            GenLimit.SafeGeneration.SafeIdentification.Point),
        ∃ j,
          And
            (GenLimit.SafeGeneration.SafeIdentification.DifferenceRepresented.{0}
              GenLimit.SafeGeneration.SafeIdentification.candidateFamily
              (GenLimit.SafeGeneration.SafeIdentification.candidateFamily 0)
              (GenLimit.SafeGeneration.SafeIdentification.harmfulFamily j))
            (And
              (GenLimit.SafeGeneration.LabeledPresents.{0} (GenLimit.SafeGeneration.SafeIdentification.diagonalStream M)
                (GenLimit.SafeGeneration.SafeIdentification.candidateFamily 0)
                (GenLimit.SafeGeneration.SafeIdentification.harmfulFamily j))
              (Not
                (GenLimit.SafeGeneration.SafeIdentification.SafelyIdentifiesFrom.{0} M
                  GenLimit.SafeGeneration.SafeIdentification.candidateFamily
                  (GenLimit.SafeGeneration.SafeIdentification.candidateFamily 0)
                  (GenLimit.SafeGeneration.SafeIdentification.harmfulFamily j)
                  (GenLimit.SafeGeneration.SafeIdentification.diagonalStream M)))))))
```

Write `C = candidateFamily`, `H = harmfulFamily`, `d_M = diagonalStream M`. The quantifier skeleton is

`(∀i Infinite(C i)) ∧ (∀j Infinite(H j)) ∧ (∀j ∃k, C k = C 0 \ H j) ∧ (∀M ∃j, (∃k, C k = C 0 \ H j) ∧ LabeledPresents d_M (C 0) (H j) ∧ ¬∃T ∀t≥T, C(M(d_M↾t)) = C 0 \ H j)`.

All four conjuncts matter. The families and target `C 0` are fixed before the arbitrary identifier; the harmful index may depend on that identifier. The stream is the named function of `M`, not a further unspecified existential. The represented difference index need not equal the harmful index or any learner output. Failure concerns eventual semantic correctness, already weaker than stabilizing on one index.

The point space is three disjoint copies of `Nat`: `commonPoint n = inl n`, `stagedPoint n = inr(inl n)`, `safePoint n = inr(inr n)`. Their ranges are the corresponding spines. Defining values give `C 0 = univ`, `C 1 = safeSpine`, and `C(a+2) = safeSpine ∪ {stagedPoint k | a ≤ k}`. They give `H 0 = commonSpine ∪ stagedSpine`, and `H(a+1) = commonSpine ∪ {stagedPoint k | k < a}`. Consequently the differences from `C 0` are represented by `C 1` at `j=0`, and by `C(a+2)` at `j=a+1`. Every such difference is infinite. The locator `finiteHarmful a` still denotes an infinite set because it includes the entire common spine.

The diagonal state stores a phase and finite tagged history, initially zero and empty. Each step appends the four observations `(common n,true)`, `(staged n,true)`, `(safe n,true)`, `(common n,false)`, then queries `M` on that extended prefix. If its denotation equals the current `tailSafe phase`, the step increments phase and appends `(staged phase,false)` using the old phase; otherwise it appends `(common 0,false)` and retains phase. Histories grow by five. The stream at time `t` reads entry `t` from state `t/5+1`; the auxiliary certificate supplies its bounds. No ordinary computability of the semantic equality test or stream is claimed.

The learner receives that labeled prefix, without `j` or a separate harmful-set description as an argument. Even supplying the fixed target and family as background does not change the quantified obstruction. This target has no finite/empty-difference escape: all its displayed differences contain the infinite safe spine. It supplies one adversarial presentation per identifier, not failure on every presentation and not an explicit uniform selection program for `j`.

## D2 — `GenLimit.SafeGeneration.Results.theorem_5_1`

Source anchor: `GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean:80`.

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] (G : GenLimit.SafeGeneration.SafeGenerator.{u_1} (Prod.{u_1, 0} α Nat))
  (C : GenLimit.Generic.LanguageFamily.{u_1} α),
  (∀ (i : Nat), Set.Infinite.{u_1} (C i)) →
    (GenLimit.SafeGeneration.SafelyGeneratesFamilies.{u_1} G (fun i => GenLimit.SafeGeneration.verticalPad.{u_1} (C i))
        fun i => GenLimit.SafeGeneration.verticalPad.{u_1} (C i)) →
      ∃ M, GenLimit.Angluin.SemanticallyIdentifies.{u_1} M C
```

Skeleton: `∀{α}[Countable α] ∀G ∀C, (∀i Infinite(C i)) → SGF(G,pad∘C,pad∘C) → ∃M ∀z ∀s, Presents s (C z) → ∃k, C k = C z ∧ ∃T ∀t≥T, M(textPrefix s t)=k`.

The one identifier `M : List α → Nat` works for the whole original family. It may depend on `α`, its countability witness, `G`, `C` and the hypotheses; the eventual index and time may depend on the presented member and stream. The supplement's explicit application and the exported type of `SemanticallyIdentifies` fix this hidden witness domain. No computable map from `G` to `M`, effective enumeration of `α`, or computability of `M` appears.

The generator observes tagged pairs `(x,n)` in `α × Nat`. Its target index and harmful index are independent, even though both families are the same padded family. In particular `i=j` has empty difference and requires eventual `none`; different indices may also denote identical sets. Directly from padding, a padded difference is empty if the original difference is empty and infinite whenever the original difference is nonempty, because every surviving `x` has all positive natural coordinates. Thus the hypothesis must handle empty differences as well as infinite ones; padding removes the finite nonempty case on these pairs.

The resulting identifier receives only an ordinary positive-data list from the original target language, not harmful labels, target index or padded coordinates. Every original member is assumed infinite, so empty/finite members cannot satisfy the premise. An empty underlying type cannot satisfy that premise either. Ordinary presentations allow repetitions and arbitrary enumeration delays. The conclusion fixes one eventual representing index, not necessarily the original `z`; duplicate representations remain permitted. This is a conditional semantic implication, with the existence of the requisite safe generator left as a hypothesis.

## D3 — `GenLimit.SafeGeneration.Results.theorem_6_1`

Source anchor: `GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean:98`.

```lean
Not
  (∃ P,
    And (ComputablePred.{0} P)
      (∀ (pair : GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.LanguagePairCode),
        GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.IsValidLanguagePair pair →
          Iff (P pair) (GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.CodedDiffEmpty pair)))
```

Skeleton: `¬∃P : (Code×Code) → Prop, ComputablePred P ∧ ∀pair, Valid(pair) → (P(pair) ↔ codedLeft(pair) \ codedRight(pair) = ∅)`.

No ordinary computable predicate on the entire machine-pair representation agrees with difference emptiness on all valid pairs. The promise has four conjuncts: each machine is a total Boolean decider, and each accepted language is infinite. The predicate may behave arbitrarily on invalid pairs; validity itself is neither a required input certificate to a program nor claimed decidable. A partially defined procedure terminating only on promised inputs is not separately quantified by this statement.

The compared sets are natural-number inputs accepted by output exactly `1`, not sets of programs or distributions. Equality and repeated machine codes are allowed, and equal accepted languages give an empty difference. Infinitude of each language does not ensure an infinite difference: empty and finite differences remain relevant to the tested property. There is no learner observation stream or oracle here. The result is unconditional within this concrete representation and promise domain; it does not establish undecidability for every conceivable encoding of semantic sets.

## D4 — `GenLimit.SafeGeneration.Results.theorem_6_1_restricted`

Source anchor: `GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean:106`.

```lean
Not (ComputablePred.{0} GenLimit.SafeGeneration.DiffEmpty.DiffEmptyInstance)
```

Skeleton: `¬ComputablePred (fun c : Code => Nat \ rightLanguage c = ∅)`.

This unconditional negative result has one machine code as input, with no validity or infinitude promise in its type. Expanding the value, the difference is exactly `{2m+1 | boundedHalts c m = true}`. Its emptiness says that evaluation of `c` on input zero succeeds at no bounded fuel. Under the declared standard `evaln` semantics this is nonhalting on zero. If a successful fuel exists, standard monotonic bounded evaluation makes infinitely many odd inputs survive; the even numbers always belong to the right language. The exact formal target is the noncomputability of `DiffEmptyInstance`, not an additional exported reduction-equivalence theorem.

All machine codes, including ones that halt and ones that diverge, belong to the input domain. There is no natural-language target index, stream, query interface or probabilistic loss. This fixed family differs from the first-bounded-halt construction in D6: its difference is empty or infinite, whereas D6's is always finite. No theorem here asserts a uniform executable generator merely because membership in these bounded-evaluation sets is expressible.

## D5 — `GenLimit.SafeGeneration.Results.theorem_6_1_of_hard_embedding`

Source anchor: `GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean:111`.

```lean
∀ {Rep : Type u_1} [inst : Primcodable.{u_1} Rep] (left right : Rep → Set.{0} Nat) (encode : Nat.Partrec.Code → Rep),
  Computable.{0, u_1} encode →
    (∀ (c : Nat.Partrec.Code),
        Iff (Eq.{1} (SDiff.sdiff.{0} (left (encode c)) (right (encode c))) EmptyCollection.emptyCollection.{0})
          (GenLimit.SafeGeneration.DiffEmpty.DiffEmptyInstance c)) →
      Not
        (ComputablePred.{u_1} fun r => Eq.{1} (SDiff.sdiff.{0} (left r) (right r)) EmptyCollection.emptyCollection.{0})
```

Skeleton: `∀{Rep}[Primcodable Rep] ∀left right encode, Computable encode → (∀c, (left(encode c) \ right(encode c)=∅ ↔ DiffEmptyInstance c)) → ¬ComputablePred (fun r : Rep => left r \ right r = ∅)`.

This transfers the restricted predicate's hardness through a supplied total computable map `encode : Code → Rep` and a supplied exact equivalence for every code. Both hypotheses are essential. The output predicate ranges over every `r : Rep`; agreement on the encoding's image suffices for the transfer. Injectivity or surjectivity of `encode` is unnecessary. Collisions must respect the required equivalence.

The semantic maps `left,right : Rep → Set Nat` have no decidability, computability, total-Boolean-machine or infinitude hypotheses. `Primcodable Rep` supplies the representation for the ordinary computability claims; it does not make those semantic maps executable. Unlike D3, there is no validity promise restricting the conclusion. The target supplies neither a particular representation nor an embedding certificate: it is conditional in these parameters. Empty, finite and infinite interpreted differences are unrestricted except for what the stipulated equivalence forces on encoded inputs. There is no observation model or oracle assumption.

## D6 — `GenLimit.SafeGeneration.Results.corollary_6_1_printed_reduction_collapses`

Source anchor: `GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean:127`.

```lean
∀ (G : GenLimit.SafeGeneration.SafeGenerator.{0} Nat)
  (stream : GenLimit.Generic.Stream.{0} (GenLimit.SafeGeneration.Tagged.{0} Nat)) (c : Nat.Partrec.Code),
  Iff
    (GenLimit.SafeGeneration.SafelyGenerates.{0} G GenLimit.SafeGeneration.DiffEmpty.leftLanguage
      (GenLimit.SafeGeneration.DiffEmpty.PrintedReduction.printedRightLanguage c) stream)
    (GenLimit.SafeGeneration.EventuallyBottom.{0} G stream)
```

Skeleton: `∀G : SafeGenerator Nat ∀s : Nat → (Nat×Bool) ∀c : Code, SafelyGenerates G Nat (printedRightLanguage c) s ↔ ∃T ∀t≥T, safeOutput G s t = none`.

There is **no labeled-presentation hypothesis**. The equivalence holds even for arbitrary streams that do not present the displayed pair. `FirstBoundedHalt c n` means bounded evaluation succeeds at `n` and fails at every smaller fuel. `printedRightLanguage c` contains exactly the numbers that are not such a first fuel. Because two distinct naturals cannot both be first, `Nat \ printedRightLanguage c` has at most one element. It is empty if no bounded fuel succeeds; otherwise it is the singleton of the first successful fuel.

Both cases are finite and therefore invoke the bottom branch of `SafelyGenerates`. Its infinite-difference implication is vacuous; its finite-difference implication is exactly eventual `none`, with finiteness already secured. Success here cannot distinguish the no-halt case from the first-halt case by requiring eventual production of the singleton. The constant-`none` generator satisfies the displayed eventual behavior for every code and stream. This consequence follows from the definitions; it is not a claim about an unseen source argument.

`G`, the stream and the code are all universal; the threshold can depend on all of them. Early `some` outputs are allowed, and the equivalence demands neither immediate bottom nor a halting-dependent threshold. The construction is not D4's odd-tail right language. Its identifier is only a locator; the conclusion is a diagnostic semantic equivalence, not a further undecidability assertion or a furnished hardness certificate.

## D7 — `GenLimit.SafeGeneration.Results.theorem_6_2`

Source anchor: `GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean:138`.

```lean
∃ targets harmfuls,
  And (∀ (i : Nat), Set.Infinite.{0} (targets i))
    (And (∀ (j : Nat), Set.Infinite.{0} (harmfuls j))
      (∀ (O : GenLimit.SafeGeneration.SetDifferenceOracle.{0} (Prod.{0, 0} Nat Nat)),
        GenLimit.SafeGeneration.IsCorrectSetDifferenceOracle.{0} O →
          ∀ (A : GenLimit.SafeGeneration.OracleSafeAlgorithm.{0} (Prod.{0, 0} Nat Nat)),
            Not (GenLimit.SafeGeneration.SafelyGeneratesFamilies.{0} (A O) targets harmfuls)))
```

The supplement exposes `α = Nat × Nat` throughout. Together with `LanguageFamily α = Nat → Set α`, it fixes the hidden existential domains: both witnesses are families of subsets of `Nat × Nat`. Skeleton:

`∃targets harmfuls : Nat → Set(Nat×Nat), (∀i Infinite(targets i)) ∧ (∀j Infinite(harmfuls j)) ∧ ∀O, Correct(O) → ∀A : Oracle→SafeGenerator, ¬SGF(A O,targets,harmfuls)`.

The same two families are chosen before all oracles and algorithms; their witnesses are not named in the exported target type. Correctness means the oracle decides emptiness of `X \ Y` for **every** semantic pair of subsets of `Nat × Nat`. Nevertheless no function `A` of the declared type yields one successful family generator. This quantifies over arbitrary such functions, including ones constant at any selected generator. At any fixed correct oracle, it therefore rules out every finite-history generator, without a bound on oracle use or a computability restriction. It is not merely a theorem about encoded programs that make some specified class of queries.

Expanding the final negation retains failure of `∀i j s, LabeledPresents s (targets i) (harmfuls j) → SafelyGenerates …`. Classically this supplies a failing pair and valid stream depending on `O,A`, but the statement names none and does not specify which success branch fails. Individual targets and harmful sets are infinite; their differences need not be. In particular the type contains no all-cross-infinite assumption. Finite differences demand eventual `none` and infinite ones eventual fresh safe output. Neither labels nor oracle correctness reveal the actual indices to the generator as ordinary inputs. The theorem claims no computable families or computable witness selection, and supplies no representation of its semantic-set oracle.

## D8 — `GenLimit.SafeGeneration.Results.theorem_6_3`

Source anchor: `GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean:151`.

```lean
∀ {α : Type u_1} (targets harmfuls : GenLimit.Generic.LanguageFamily.{u_1} α)
  (hCross : GenLimit.SafeGeneration.AllCrossDifferencesInfinite.{u_1} targets harmfuls),
  GenLimit.SafeGeneration.SafelyGeneratesInfiniteDifferences.{u_1}
    (GenLimit.SafeGeneration.infiniteDifferenceGenerator.{u_1} targets harmfuls hCross) targets harmfuls
```

Skeleton: `∀{α} ∀targets harmfuls ∀hCross : (∀i j Infinite(targets i \ harmfuls j)), ∀i j ∀s, LabeledPresents s (targets i) (harmfuls j) → ∃T ∀t≥T, SafeCorrectAt (infiniteDifferenceGenerator targets harmfuls hCross) (targets i) (harmfuls j) s t`.

The witness is the named generator, depending on both whole indexed families and the cross-infinitude certificate. It returns `some (safeValue … xs)` on every history, including the empty one. No `Countable`, `Primcodable`, effective membership, set-difference oracle or ordinary computability hypothesis occurs.

The defining construction uses both label-specific samples. `ConsistentAt C xs b i` means the observed `b`-tagged sample is included in `C i`. `CriticalAt … n` additionally requires `C n ⊆ C i` for every consistent `i ≤ n`. Candidate finsets restrict indices to `i < t`. `upperFocus` chooses the greatest critical target index for true labels, defaulting to zero if there are none. `lowerFocus` chooses the least consistent harmful index for false labels, also defaulting to zero. `focusedDifference` is the selected target minus selected harmful set. The helper certificate asserts this difference infinite under `hCross`. `safeValue` calls `freshFromInfinite` on it and the entire observed sample; the latter uses `Classical.choose` and its nonemptiness certificate. Thus all-time selection is fresh from the focused difference, while the target theorem supplies eventual correctness relative to the actual pair. Early focus choices need not match the actual pair.

At `t=0` both candidate finsets are empty, both focus indices are zero, and cross-infinitude still permits a choice outside the empty observed sample. The generator never returns `none`; finite/empty actual differences are excluded by the premise, not handled by a bottom branch here. Cross-infinitude forces every target infinite but does not require harmful sets infinite; an empty harmful set is compatible with an all-true presentation. Empty or finite universes cannot satisfy the premise. Duplicate family entries are allowed. No uniform threshold across streams or family pairs is promised. Because semantic inclusion/equality decisions and classical choice are present, the supplied values establish a mathematical history function, not an ordinary computable implementation.

## Exhaustive declaration coverage

The row numbers below are the 1-based records in `declarations.jsonl`. Prefixes expand exactly as follows: `G = GenLimit`, `A = GenLimit.Angluin`, `Q = GenLimit.Generic`, `S = GenLimit.SafeGeneration`, `SI = GenLimit.SafeGeneration.SafeIdentification`, `D = GenLimit.SafeGeneration.DiffEmpty`, `ME = GenLimit.SafeGeneration.DiffEmpty.MachineEncoding`, `PR = GenLimit.SafeGeneration.DiffEmpty.PrintedReduction`, `U = GenLimit.Support`, `R = GenLimit.SafeGeneration.Results`. A prefix plus each terminal identifier denotes one exported declaration. Grouping avoids repeating definition bodies; every record appears exactly once.

| Export records | Prefix | Terminal identifiers | Interpretation/coverage |
|---|---|---|---|
| 1, 2, 3, 4 | G | `IdentifiesInLimit`, `Learner`, `StabilizesTo`, `textPrefix` | glossary; D2: list learner, naming, stabilization, prefixes |
| 5, 6 | A | `SemanticIdentifier`, `SemanticallyIdentifies` | glossary; D2: one eventual representing index |
| 7, 8, 9, 10, 11, 12, 13 | Q | `FiniteHistoryOperator`, `Language`, `LanguageFamily`, `Presents`, `Stream`, `sample`, `sequenceSample` | glossary: semantic family, stream and finite-sample model |
| 14, 26 | S | `AllCrossDifferencesInfinite`, `SafelyGeneratesInfiniteDifferences` | glossary; D8: premise and eventual-output conclusion |
| 15, 18, 22, 24, 25 | S | `BottomCorrectAt`, `EventuallyBottom`, `SafeCorrectAt`, `SafelyGenerates`, `SafelyGeneratesFamilies` | glossary; D2–D7: finite/infinite branches and family quantifiers |
| 19, 21, 27 | S | `IsCorrectSetDifferenceOracle`, `OracleSafeAlgorithm`, `SetDifferenceOracle` | glossary; D7: semantic oracle and unrestricted algorithm functions |
| 20, 23, 28, 32, 33, 36, 37, 39 | S | `LabeledPresents`, `SafeGenerator`, `Tagged`, `historyObservedSample`, `historyTaggedSample`, `observedSample`, `safeOutput`, `taggedRange` | glossary: labels, total history output and both-tag freshness |
| 16, 17, 29, 30 | S | `ConsistentAt`, `CriticalAt`, `consistentIndices`, `criticalIndices` | D8: consistency, criticality and bounded candidate sets |
| 31, 34, 35, 38, 40 | S | `focusedDifference`, `infiniteDifferenceGenerator`, `lowerFocus`, `safeValue`, `upperFocus` | D8: focus choices and named generator |
| 41 | S | `verticalPad` | glossary; D2: positive-coordinate padding |
| 42, 43, 44 | U | `freshFromInfinite`, `greatestCandidateWithFallback`, `leastCandidateWithFallback` | D8: classical fresh selection and min/max fallbacks |
| 45, 46, 47, 48 | D | `DiffEmptyInstance`, `boundedHalts`, `leftLanguage`, `rightLanguage` | glossary; D4: bounded evaluation and odd safe tail |
| 49 | R | `corollary_6_1_printed_reduction_collapses` | D6: exact target and diagnostic equivalence |
| 50 | R | `theorem_3_1` | D1: exact target, fixed families and diagonal failure |
| 51 | R | `theorem_5_1` | D2: exact target and conditional semantic identification |
| 52 | R | `theorem_6_1` | D3: exact target, machine-pair promise |
| 53 | R | `theorem_6_1_of_hard_embedding` | D5: exact target and supplied hardness embedding |
| 54 | R | `theorem_6_1_restricted` | D4: exact target and restricted undecidability |
| 55 | R | `theorem_6_2` | D7: exact target and oracle-uniform obstruction |
| 56 | R | `theorem_6_3` | D8: exact target and named semantic generator |
| 57, 65, 66, 68, 72, 87, 88, 89 | SI | `DiagonalState`, `diagonalState`, `diagonalStream`, `frontBlock`, `nextState`, `DiagonalState.history`, `DiagonalState.mk`, `DiagonalState.phase` | D1: state, five-entry recursion, history/phase and stream |
| 58, 59, 60, 61, 70 | SI | `DifferenceRepresented`, `Point`, `SafeIdentifier`, `SafelyIdentifiesFrom`, `identifierOutput` | glossary; D1: point type, representation and semantic success |
| 62, 63, 64, 67, 69, 71, 73, 74, 75, 76, 77 | SI | `candidateFamily`, `commonPoint`, `commonSpine`, `finiteHarmful`, `harmfulFamily`, `limitHarmful`, `safePoint`, `safeSpine`, `stagedPoint`, `stagedSpine`, `tailSafe` | D1: explicit three-spine families and their differences |
| 78 | S | `safeValue._proof_1` | D8; limits: focused difference infinite, type only |
| 79 | U | `freshFromInfinite._proof_1` | D8; limits: infinite set minus finite sample nonempty, type only |
| 80, 81, 82, 83, 84 | ME | `CodedDiffEmpty`, `IsValidLanguagePair`, `LanguagePairCode`, `TotalBooleanDecider`, `codedLanguage` | glossary; D3: representation, total-Boolean and infinitude promises |
| 85, 86 | PR | `FirstBoundedHalt`, `printedRightLanguage` | D6: first bounded halt and its complement |
| 90, 92 | SI | `candidateFamily.match_1`, `harmfulFamily.match_1` | D1: generated Nat case eliminators for displayed family/recursion values |
| 91 | SI | `diagonalStream._proof_2` | D1; limits: diagonal history index in bounds, type only |

## Interpretation limits

This is reconstruction of the supplied interface, not an audit of theorem proofs, source correspondence or the paper. No paper, raw source comments, source proof bodies, PaperMap, registry, owner material, other stages, other packages, old/human audit or other result was consulted. Only the two newly produced outputs were read back for output validation. No library/frozen input edits, Git operation, Lean invocation, build, network lookup or human certification occurred.

Standard Lean/Mathlib meanings are accepted only at `external-constant-boundary.txt`, including sets, classical choice, machine evaluation, coding and ordinary computability. The `⋯` fragments in exported defining values suppress embedded proof terms; they are not evidence of holes. The three auxiliary theorem types certify focused-difference infinitude, availability of a fresh element, and diagonal-stream indexing bounds; their bodies were not checked. Exact implementation properties beyond the shown types/values, kernel acceptance, effective witness extraction and any intended source-paper correspondence remain outside this stage. The explicit supplement resolves hidden type applications but does not enlarge any hypothesis or reveal proof witnesses.
