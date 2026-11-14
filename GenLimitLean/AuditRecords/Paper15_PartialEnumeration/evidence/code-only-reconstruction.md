# Stage 1: reconstruction from the Lean interface only

This report reconstructs 13 declarations in `GenLimit.KleinbergWei.PartialEnumeration.Results` from the supplied Stage1 types, recursively necessary project definition values and constructors, and the declared standard Lean/Mathlib boundary. Every original target type is quoted below. A source anchor identifies the exported declaration; the underlying source file was not opened. No paper interpretation or proof-correctness claim is made.

## Input census and access boundary

The initial `stage1/` inventory contained 15 files: the 13 files covered by its `SHA256SUMS`, that manifest itself, and the nested `explicit-target-types/SHA256SUMS`. The top-level verification passed for all 13 entries; the nested verification passed for both its entries. The explicit-type supplement was present at initial handoff and covered by the initial top-level manifest. Its types only disambiguate applications and domains; they add no hypothesis. The manifest hashes are `37aff64a95e921e745dc4e1e080965d43681d39dd4648275b4d60e1e32f2519d` and `28e3360de750b08196352af1807f1ec827231d360512017305ad01a5fd24e3a0`, respectively. All 15 actual file hashes are recorded in `stage1-run.json`.

`01-target-statements.md` supplies the targets; `02-definition-dependencies.md` and the 119 records in `declarations.jsonl` supply the project interface (13 targets and 106 dependency records). `explicit-target-types/types.jsonl` supplies 13 explicit renderings. `START_HERE.md`, `PROMPT.md`, `targets.txt`, the boundary file, and snapshot/build metadata delimit scope. The metadata declares Lean 4.24.0 and Mathlib v4.24.0, with locked Mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. This records metadata, not fresh compilation. The snapshot describes a dirty working-tree byte snapshot at commit `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`; those facts were not independently checked with Git.

Content access followed this order: top-level inventory; both checksum validations; START_HERE and PROMPT; manifests, snapshot, target list, package/toolchain metadata, external boundary and supplement README; original and explicit target types; dependency export; a bounded reread of its middle section and declaration census; its topology/certificate section; selected declaration records resolving choice, least-element predicates and hidden finite-set domains; finally a complete input hash census and manifest metadata. The first long dependency display was truncated, so the bounded rereads supplied the missing material. No paper, owner material, later stage, prior result, registry, PaperMap, other audit package, raw library source or theorem proof body, external mathematical website, or repository build was consulted. Source/module names serve only as locators.

## Definition glossary and binder resolution

Here `PE` abbreviates `GenLimit.KleinbergWei.PartialEnumeration`, `FT` its `FullTopology` namespace, and `WP` its `WarmupPriority` namespace. They are editorial abbreviations. Every element domain below is `Nat`, every language is a subset of `Nat`, and family indices are natural numbers. In the dossiers, H means the four assumptions: all `C i` infinite, `range stream = E`, E infinite, and `E ⊆ C z`.

**G1 — data, prefixes, freshness.** `Language = Set Nat`, `LanguageFamily = Nat → Language`, and `Presents stream L` is exactly `range stream = L` (`Core/Basic.lean:20,23,26`). Thus a presentation is an infinite stream covering every member of its presented set and containing nothing else. Repetition and arbitrary delays are allowed in general. A stream cannot present the empty language; it can present a nonempty finite language by repeating values. `sample stream t` is the finite image of indices strictly below t (`Basic.lean:30`), whereas `textPrefix stream t` is the ordered list `[stream 0,…,stream (t−1)]` (`Core/Text.lean:16`). At t=0 both are empty. `Consistent C stream t i` means this sample is contained in `C i` (`Basic.lean:34`). It uses positive data alone, not a negative example or complete finite membership table. List order/repetition remains available to a learner even though consistency discards it.

`FreshGeneratesInLimit stream output L` means `∃ T : Nat, ∀ t : Nat, T ≤ t → output t ∈ L ∧ output t ∉ sample stream t` (`Core/OnlineGeneration.lean:16`). Both conjuncts hold on the same eventual tail. Freshness is against already observed inputs, excluding indices t and later. This definition alone does not forbid repeating earlier outputs, require eventual coverage of L, or identify L or a correct index. Neither an error rate nor a convergence bound is included.

**G2 — finite intersections and the selected witness.** `intersectionOf C I = {u | ∀ i : Nat, i ∈ I → u ∈ C i}` (`PE/SemiIndex.lean:14`). An empty index set therefore yields all natural numbers, not the empty set. `prefixIntersection C stream t s` intersects exactly the consistent indices i<s (`PE/FiniteScope.lean:24`). Its s=0 value is again all natural numbers. `admissibleScopes` contains those s in `Finset.range (t+2)` whose prefix intersection is infinite (`:35`); `selectedScope` is its maximum (`:56`). Thus scopes range from 0 through t+1, and 0 supplies nonemptiness even for arbitrary families. `selectedIndices` filters the consistent indices below this scope (`SemiIndex.lean:18`); `selectedIntersection` uses that scope (`FiniteScope.lean:79`). The exported `selectedIntersection_infinite` type states infinitude for every C, stream and t (`:83`).

`freshOutput C stream t` applies `Support.freshFromInfinite` to this selected intersection and `sample stream t` (`FiniteScope.lean:89`). The latter choice definition and its exported existence-predicate type select a member of the infinite set minus the finite seen set (`Support/Fresh.lean:15`, generated `_proof_1`). The displayed proof ellipsis is an erased embedded proof, not an admitted theorem. Its proposition and dependency link are supplied. `GeneratesFromPartialEnumeration C stream z` applies G1's eventual freshness predicate to this named `freshOutput` and `C z` (`FiniteScope.lean:106`). This is a particular classical semantic witness; no computable representation or oracle implementation is supplied. Its value depends on C and the finite observed sample, not on E or the distinguished target index z.

`SemiIndexGenerates C stream z` means every selected intersection is infinite and, for some T, every selected intersection at t≥T is contained in `C z` (`SemiIndex.lean:50`). `SemiIndexTraceGenerates C indices z` states the same two clauses for an explicitly supplied trace `indices : Nat → Finset Nat` (`PE/ElementSemiIndex.lean:48`). These predicates neither require the finite index set to stabilize nor require its intersection to equal the target. They do not themselves assert element output or freshness.

**G3 — the named intersection trace.** An `IdentifiedIntersectionState` packages `chain : Nat → Language`, a chosen natural index, and an antitone-chain proof; `identified` is the chain at that chosen index (`PE/AccurateIntersection.lean:156–162`, constructor included). `consistencyIntersectionState C stream t j` has chain `prefixIntersection C stream t` and chosen index j (`PE/RuleTwoReset.lean:138`). `consistencyChainState` chooses index 0 (`PE/AlgorithmOneRun.lean:35`). The label “identified” here is just a chain projection, not a claim of identification in the limit.

Write a(t) for `algorithmOneChosen C stream t` (`AlgorithmOneRun.lean:45`). It starts at a(0)=0. At the transition t→t+1, compare the entire prefix-intersection chains at these times. If equal, increment a(t) when the old chain at a(t)+1 is infinite, and otherwise keep a(t). If unequal, use `ruleTwoResetIndex`; replace its zero result by 1. A rule-two candidate k must be positive, have equal old/new kth chain sets, and have infinite old kth set (`RuleTwoReset.lean:31`). A greatest candidate additionally dominates every candidate (`:38`). The reset chooses such a greatest candidate if one exists, and returns 0 otherwise (`:53`); it is not assumed that a greatest candidate always exists.

`algorithmOneState` uses a(t) as its chosen index (`AlgorithmOneRun.lean:64`), and `algorithmOneIndices C stream t` is the finite set of consistent indices below a(t) (`:616`). Hence its intersection equals the state's identified set by direct expansion. The supplied dependency theorem type states this set is infinite at every t if every family language is infinite (`:648`); this report does not inspect its proof. The trace is named, but deciding set equality, infinitude and greatest-candidate existence is semantic. Neither decidable membership nor effective enumeration of the family is a hypothesis. Repeated equal languages at different indices are permitted; index multiplicity supplies no distinctness assumption.

**G4 — warmup state and timing.** `IncomparableChoice = Nat → Option AggressiveGuess` (`PE/WarmupPriorityRun.lean:686`). An aggressive guess has an arbitrary language, a proof it is infinite, and a natural token (`:39–42`, constructor). There is no accuracy, computability, causality or fairness restriction on this external sequence. For old/current intersection sets at t and t+1, `algorithmOneAggressiveGuess` returns none when equal; when unequal and new⊆old, it chooses old with token 2; otherwise if old⊆new, it chooses new with token 2; otherwise it uses `incomparable t` (`:837`). The branch order, including equality first, is part of the definition.

`nextAbove L h bound` is the least member of L strictly greater than bound, from its `Nat.find` predicate and exported existence type (`:45`, generated `_proof_1`). `tokenCutoff L h bound k` iterates this successor k+1 times (`:58`). `tokenWindow` contains all unused members of the guessed language up to that cutoff, starting from `max used` (`:86`). It can also contain unused members below that maximum; the constructor imposes no token lower bound. State is `Support.PriorityRound.State`: finite used set, finite queue, optional previous output (`Support/PriorityRound.lean:17–19`, constructor). It starts with both sets empty and previous output none (`WarmupPriorityRun.lean:134`).

At a step, insert the current input into used, remove that used set from the old queue, and, for a present guess, union in its token window (`priorityAtStep`, `:139`). `leastOutput` is the least natural x outside this enlarged used set that lies in the preferred set **or** the current infinite language (`Support/PriorityRound.lean:25,30,39,64`). This is the least of a union, with no separate rule always choosing the preferred set first. A step inserts both input and emitted output into used, erases the output from the preferred queue, and records it (`:72`). `runState`, `runOutput`, `emittedAtStep`, and `step` supply this recursion (`WarmupPriorityRun.lean:191,199,335,345`). The named `algorithmOneWarmupOutput` feeds the G3 intersection sequence and the preceding guess sequence into that run (`:947`).

At time t this run sees `stream t`; its aggressive comparison uses the intersection at t+1, whose consistency sample includes this same input. It needs no later input through that comparison, although the unrestricted external choice may itself encode arbitrary information. The used-set recursion implies distinct outputs avoiding every input observed through the current step, but the eventual-validity target below only asserts target membership. Queue members can lie outside the current intersection. The run remains semantic, using infinitude/equality/subset tests, least-element selection and an arbitrary choice parameter.

**G5 — order, density and charging.** `OrderedLanguage.mk` takes a carrier language, an injective `Nat → Nat` enumeration, and equality of its range with the carrier (`Core/OrderedDensity.lean:24–26`). Thus this constructor entails an infinite carrier and excludes finite or empty carriers. It does not impose the usual numerical increasing order. The ranks relevant to A are `{i : Nat | enumeration i ∈ A}` (`:44`; `PE.orderedRankSet`, `DensityAccounting.lean:49`). `prefixCount K A n` counts such ranks below n (`OrderedDensity.lean:33`); `prefixRatio` is 0 at n=0 and the real count divided by n otherwise (`:197`). `lowerDensity K A` is the real `Filter.liminf` of these ratios along `atTop` (`:237`). Thus it is an ordered lower asymptotic density, not a temporal output frequency, ordinary limit, upper density or probability. Elements outside the carrier do not affect it.

`WarmupChargeCertificate K enumerated output good bad` is a data-bearing type, with a fully exported constructor (`PE/DensityAccounting.lean:84`). Its fields require: `enumerated \ output = good ∪ bad`; good and bad are disjoint; a finite exception-rank set; and total functions `goodCharge,badCharge : Nat → Nat`. For each rank i of good, `enumeration (goodCharge i)` belongs to output, `goodCharge i ≤ i+1`, and goodCharge is injective on all good ranks. For each rank i of bad outside the finite exception set, the analogous output-membership and ≤i+1 conditions hold; badCharge is injective on those nonexceptional bad ranks. Nothing requires the two charge functions to have disjoint images, or either function to be globally injective outside its stipulated domain. A charge may go one rank to the right. There is no numeric bound on the finite exception set, no required subset-of-carrier assumption for the four languages, and no certificate-production theorem among the targets. This is conditional accounting data, not merely the hypothesis that an algorithm was run.

**G6 — full-text identification and topology.** `Learner Info Name = List Info → Name` (`Core/Identification.lean:18`). `StabilizesTo guess name` means `∃ T : Nat, ∀ t≥T, guess t = name` (`:47`). `IdentifiesInLimit denote learner stream target` means `∃ name, denote name = target ∧ StabilizesTo (fun t => learner (textPrefix stream t)) name` (`:53`). `Angluin.ExtensionalIdentifier Nat` returns languages themselves; `ExtensionalIdentifies M X` means every L∈X and every full stream presenting L is so identified with denotation id; `ExtensionallyIdentifiable X` existentially chooses one M for the entire class (`Bridges/AngluinToPaper02.lean:20,25,34`; generic language/stream/presentation values in `Core/GenericGeneration.lean:21,24,31,50`). `FT.IdentifiableOnFullTexts` is exactly that last property (`PE/FullTextIdentification.lean:136`). Outputs are extensional sets, not required initially to belong to X, and no effectiveness restriction is present. Stabilization is eventual equality of returned sets to L, not convergence of an arbitrary numerical coding or correctness only infinitely often.

`Point X` is the subtype of languages in X. `basicOpen X F`, with **F : Finset Nat**, comprises those points containing F. `FullOpen X O` means every K∈O has some such finite F⊆K with `basicOpen X F ⊆ O` (`PE/FullTopology.lean:14,16,24`). The hidden existential F is a finite set, resolved by `basicOpen`'s exported domain and explicit dependency application, not an arbitrary language. `Specializes K L` means every full open containing K also contains L (`:70`), fixing the orientation. Directly from basic opens this is equivalent to underlying K⊆L; that observation is a derivation from the exported definitions, not an extra input.

`TDPoint K` supplies **O : Set (Point X)**, open and containing K, such that every L∈O with underlying L⊆K equals K (`FullTopology.lean:98`). `TDSpace` requires this for every point (`:116`). No separate closure operator is exported or required: the explicit subset restriction is retained. If closure vocabulary is used, the closure-of-singleton direction derived from these opens is the downset `{L | L⊆K}`, which is exactly the region isolated by this O. `TOneSpace` requires `∀ K L : Point X, Specializes K L → K=L` (`:128`). There is no countability assumption in its definition. `AllNonempty X` says every point's underlying language is nonempty (`PE/FullTextSeparation.lean:72`); it allows X itself to be empty.

`RefutedByHistory history L` means some element of that list is absent from L (`FullTextSeparation.lean:24`). `SeparatesFromFullText K L` means every full presentation of K eventually has every subsequent prefix refuting L, with a threshold allowed to depend on that presentation (`:36`). `SeparatedInLimit X` quantifies this property over **ordered** distinct pairs K,L in X (`:78`). It is a positive-data refutation property with no learner or stabilization of guesses. Full coverage supplies a separating element when K\L is nonempty; partial coverage may omit it forever.

## 1. `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_5`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:28`. Original type, verbatim:

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  (∀ (i : Nat), Set.Infinite.{0} (C i)) →
    GenLimit.Presents stream E →
      Set.Infinite.{0} E →
        HasSubset.Subset.{0} E (C z) →
          GenLimit.KleinbergWei.PartialEnumeration.GeneratesFromPartialEnumeration C stream z
```

Under H, the named `freshOutput C stream` eventually outputs only members of `C z` absent from the observed prefix. Expanded quantifiers are `∀ C stream E z, H → ∃ T : Nat, ∀ t : Nat, T≤t → (freshOutput C stream t∈C z ∧ freshOutput C stream t∉sample stream t)`. T may depend on the family, presentation, E and z; there is no uniform bound. The witness itself has only C and stream as arguments, so E and z are specification parameters, not supplied target information.

Dependency anchors: G1 and G2, particularly `FiniteScope.lean:89,106` and `Core/OnlineGeneration.lean:16`. Every family member, including unused indices, must be infinite; E must also be infinite and merely contained in the target. Thus this is full coverage of an infinite subset E, which may be a proper target subset. It neither covers the whole target nor identifies it. Empty and finite E are excluded. Repetitions and slow revelations in stream are allowed. Freshness is relative to earlier inputs and is weaker than a no-repeated-output assertion. The type does not certify ordinary computation or any output law, support distribution, rate or error bound.

## 2. `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_7`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:29`. Original type, verbatim:

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  (∀ (i : Nat), Set.Infinite.{0} (C i)) →
    GenLimit.Presents stream E →
      Set.Infinite.{0} E →
        HasSubset.Subset.{0} E (C z) → GenLimit.KleinbergWei.PartialEnumeration.SemiIndexGenerates C stream z
```

For every C, stream, E and z satisfying H, all intersections of `selectedIndices C stream t` are infinite, and there is a threshold after which every one of those intersections is a subset of `C z`. The exact expanded skeleton is `∀ C stream E z, H → [(∀ t : Nat, Infinite (intersectionOf C (selectedIndices C stream t))) ∧ ∃ T : Nat, ∀ t : Nat, T≤t → intersectionOf C (selectedIndices C stream t)⊆C z]`.

Dependency anchors: G1–G2, `SemiIndex.lean:18,50` and `FiniteScope.lean:24,35,56`. The selected finite set is determined from C and the prefix, not from a supplied z. This conclusion gives an infinite permitted set at every time, including t=0, and eventual target containment; it need not stabilize or equal the target. It has no element-output or fresh-output conjunct. Empty selected indices are legitimate and mean the entire universe; infinitude would still hold, while eventual containment imposes the stated additional restriction. No distinctness of indexed languages, decidable membership, computability, full target coverage or effective threshold is assumed or concluded. H excludes finite or empty E and finite target languages.

## 3. `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_8`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:30`. Original type, verbatim:

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  (∀ (i : Nat), Set.Infinite.{0} (C i)) →
    GenLimit.Presents stream E →
      Set.Infinite.{0} E →
        HasSubset.Subset.{0} E (C z) →
          And
            (GenLimit.KleinbergWei.PartialEnumeration.SemiIndexTraceGenerates C
              (GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices C stream) z)
            (∀ (T : Nat),
              ∃ t,
                And (LE.le.{0} T t)
                  (HasSubset.Subset.{0} E
                    (GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C
                      (GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices C stream t))))
```

Under H, the specifically named `algorithmOneIndices C stream` trace has two semi-index properties: its intersection is infinite at every t, and it is eventually contained in `C z`. In addition, for every threshold T there exists a time t≥T at which the **entire** E lies in that same intersection. In symbols the full skeleton is `∀ C stream E z, H → [(∀ t, Infinite I_t) ∧ (∃ T₀ : Nat, ∀ t≥T₀, I_t⊆C z)] ∧ [∀ T : Nat, ∃ t : Nat, T≤t ∧ E⊆I_t]`, with `I_t = intersectionOf C (algorithmOneIndices C stream t)`.

Dependency anchors: G1, G2's trace predicate (`ElementSemiIndex.lean:48`), and G3 (`AlgorithmOneRun.lean:45,616`). The frequent-time witness t can depend on T; there is no assertion that E is contained at every sufficiently late time. This is whole-set containment at each successful time, stronger than accommodating just the observed sample. The eventual target threshold and these frequent-time witnesses are separately quantified. The family and stream define the trace without E or z as run inputs. Repeated indices' languages may coincide. Empty intersections of index constraints still denote Nat. No stabilization of index sets, equality with E or `C z`, fresh element generator, ordinary algorithm or quantitative frequency is asserted.

## 4. `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_2_1`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:31`. Original type, verbatim:

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  (∀ (i : Nat), Set.Infinite.{0} (C i)) →
    GenLimit.Presents stream E →
      Set.Infinite.{0} E →
        HasSubset.Subset.{0} E (C z) →
          GenLimit.KleinbergWei.PartialEnumeration.GeneratesFromPartialEnumeration C stream z
```

The complete proposition is: for every C, stream, E and z, if every `C i` is infinite, stream has range E, E is infinite and E⊆`C z`, then there is a natural T such that for every natural t≥T, `freshOutput C stream t` belongs to `C z` and is not in the finite set of inputs seen at times below t. This is `∀ C stream E z, H → ∃ T : Nat, ∀ t≥T, output_t∈C z ∧ output_t∉sample stream t`, with the named output fixed by G2.

Dependency anchors: G1–G2 and `FiniteScope.lean:89,106`. Its original type is identical to the type of theorem_1_5; the different identifier supplies no extra mathematical clause. The witness is parameterized by C and stream, while the correctness threshold may depend on the target index and the enumerated infinite subset. Partial target coverage, repetitions and unbounded waiting for any element are permitted. Nothing says the output eventually enumerates the target, is numerically increasing, avoids earlier outputs, or produces a learned language/index. Empty/finite E and finite family languages violate explicit hypotheses. The theorem gives semantic eventual generation with a classical choice witness and no computability, rate or probability guarantee.

## 5. `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_2_2`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:32`. Original type, verbatim:

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  (∀ (i : Nat), Set.Infinite.{0} (C i)) →
    GenLimit.Presents stream E →
      Set.Infinite.{0} E →
        HasSubset.Subset.{0} E (C z) →
          And
            (∀ (t : Nat),
              Set.Infinite.{0}
                (GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C
                  (GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices C stream t)))
            (And
              (∃ T,
                ∀ (t : Nat),
                  LE.le.{0} T t →
                    HasSubset.Subset.{0}
                      (GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C
                        (GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices C stream t))
                      (C z))
              (∀ (T : Nat),
                ∃ t,
                  And (LE.le.{0} T t)
                    (And
                      (HasSubset.Subset.{0} E
                        (GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C
                          (GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices C stream t)))
                      (HasSubset.Subset.{0}
                        (GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C
                          (GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices C stream t))
                        (C z)))))
```

Under H, let `I_t = intersectionOf C (algorithmOneIndices C stream t)`. The conclusion has **three** clauses: (1) for every natural t, I_t is infinite; (2) there exists a natural T₀ such that for every t≥T₀, I_t⊆`C z`; (3) for every natural T, there is a natural t≥T such that **both** E⊆I_t and I_t⊆`C z`. Thus the last two containments share one late time, rather than being separately witnessed. The skeleton is `∀ C stream E z, H → (∀ t, Infinite I_t) ∧ ((∃ T₀, ∀ t≥T₀, I_t⊆C z) ∧ (∀ T, ∃ t≥T, E⊆I_t ∧ I_t⊆C z))`.

Dependency anchors: G1–G3, particularly `AlgorithmOneRun.lean:45,616` and `SemiIndex.lean:14`. Infinitude holds from the initial state, whereas target containment is eventual and the sandwich property is cofinal in time. No density of good times, bounded gaps or eventual E-containment follows as an asserted clause. E can be a proper infinite target subset, and neither containment is equality. The trace may change forever. The named trace sees C and stream rather than z; its semantic equality and infinitude tests give no ordinary computational implementation. Empty constraint sets and repeated family languages are governed by G2, without additional exclusions.

## 6. `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_2_4`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:34`. Original type, verbatim:

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  (∀ (i : Nat), Set.Infinite.{0} (C i)) →
    GenLimit.Presents stream E →
      Set.Infinite.{0} E →
        HasSubset.Subset.{0} E (C z) →
          And
            (GenLimit.KleinbergWei.PartialEnumeration.SemiIndexTraceGenerates C
              (GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices C stream) z)
            (∀ (T : Nat),
              ∃ t,
                And (LE.le.{0} T t)
                  (HasSubset.Subset.{0} E
                    (GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C
                      (GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices C stream t))))
```

For all C, stream, E and z satisfying H, the `algorithmOneIndices` trace has an infinite intersection at every natural time, has intersections contained in `C z` on some eventual tail, and contains the whole E at times beyond every prescribed natural threshold. Expanded: `∀ C stream E z, H → ((∀ t, Infinite I_t) ∧ ∃ T₀ : Nat, ∀ t≥T₀, I_t⊆C z) ∧ (∀ T : Nat, ∃ t : Nat, T≤t ∧ E⊆I_t)`, with I_t the named trace's intersection.

Dependency anchors: G1–G3, `ElementSemiIndex.lean:48`, `AlgorithmOneRun.lean:45,616`. This original type is identical to theorem_1_8's original type. The threshold T₀ and the cofinal witnesses t have their stated dependencies; E-containment is not declared eventual. At a selected cofinal time before T₀ the type does not separately require target containment, although arbitrarily late witnesses can also be chosen after T₀. There is no pointwise fresh element, stabilization, full target enumeration, index identification or rate assertion. C may repeat languages, and E's presentation may repeat elements. Infinite-family and infinite-E hypotheses exclude exhausted finite data sets, while the empty-index-intersection convention remains Nat. The witness is semantic, not an effective program specification.

## 7. `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_3_1_eventual_validity`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:36`. Original type, verbatim:

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat}
  (hLanguagesInfinite : ∀ (i : Nat), Set.Infinite.{0} (C i)),
  GenLimit.Presents stream E →
    Set.Infinite.{0} E →
      HasSubset.Subset.{0} E (C z) →
        ∀ (incomparable : GenLimit.KleinbergWei.PartialEnumeration.WarmupPriority.IncomparableChoice),
          ∃ T,
            ∀ (t : Nat),
              LE.le.{0} T t →
                Membership.mem.{0, 0} (C z)
                  (GenLimit.KleinbergWei.PartialEnumeration.WarmupPriority.algorithmOneWarmupOutput C stream
                    hLanguagesInfinite incomparable t)
```

For every C, stream, E, z and proof `hLanguagesInfinite` that all family languages are infinite, if stream presents infinite E⊆`C z`, then **for every** external `incomparable : Nat → Option AggressiveGuess` there exists a natural T after which each named `algorithmOneWarmupOutput C stream hLanguagesInfinite incomparable t` belongs to `C z`. The order is `∀ C stream E z hLanguagesInfinite, Presents stream E → Infinite E → E⊆C z → ∀ incomparable, ∃ T : Nat, ∀ t : Nat, T≤t → output_t∈C z`. In particular T may depend on incomparable; a common threshold for all choices is not claimed.

Dependency anchors: G1, G3–G4; the named output is at `WarmupPriorityRun.lean:947`, external choice at `:686`, guess rule at `:837`. The chosen infinite guess languages need not be true targets. The step includes input t and may compare consistency through t+1; arbitrary external choices carry no information restriction. The conclusion is eventual membership only: no density, stabilization, E-containment, full coverage, rate or freshness conjunct appears in this target, even though G4's run enforces used-set avoidance. All family languages and E must be infinite; the target cannot be finite or exhausted. The proof-valued infinitude argument supplies semantic existence, not effective membership or infinitude procedures.

## 8. `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_3_1_density_certificate`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:38`. Original type, verbatim:

```lean
∀ {K : GenLimit.KleinbergWei.OrderedLanguage} {enumerated output good bad : GenLimit.Language}
  (hcert : GenLimit.KleinbergWei.PartialEnumeration.WarmupChargeCertificate K enumerated output good bad) {α : Real},
  LE.le.{0} α (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K enumerated) →
    LE.le.{0} (HDiv.hDiv.{0, 0, 0} α 3) (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K output)
```

For every ordered language K, every four languages enumerated, output, good and bad, **every supplied certificate** `hcert : WarmupChargeCertificate K enumerated output good bad`, and every real α, if α≤lowerDensity K enumerated, then α/3≤lowerDensity K output. The skeleton is `∀ K enumerated output good bad hcert, ∀ α : Real, α≤d_K(enumerated) → α/3≤d_K(output)`. The certificate precedes α, so its data need not depend on α. No certificate existence or construction for the named warmup run is asserted.

Dependency anchors: G5, `DensityAccounting.lean:84` constructor, and `Core/OrderedDensity.lean:33,44,197,237`. All decomposition, separate injectivity, finite exceptions, output-membership and ≤i+1 conditions in G5 are essential assumptions. Charges from the two parts may collide, and arbitrary finite bad exceptions are allowed. α has no positivity or unit-interval hypothesis; neither good nor bad must be nonempty. Empty enumerated or output sets are allowed when the certificate conditions can be met; the ambient ordered carrier remains infinite by its constructor. The conclusion is a liminf bound over ranks with constant 1/3, not a finite-prefix inequality, temporal output guarantee, uniform rate, statistical law or effective result. Changes outside K's carrier have no density contribution.

## 9. `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_3_5_fixed_pod_endgame`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:40`. Original type, verbatim:

```lean
∀ (K : GenLimit.KleinbergWei.OrderedLanguage) (output : GenLimit.Language) (α : Real),
  (∀ (s : Nat),
      LE.le.{0} 2 s →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} α (HAdd.hAdd.{0, 0, 0} 2 (HDiv.hDiv.{0, 0, 0} 4 ↑s)))
          (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K output)) →
    LE.le.{0} (HDiv.hDiv.{0, 0, 0} α 2) (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K output)
```

For every ordered language K, language output and real α, if for every natural s with 2≤s one has `α / (2 + 4 / (s : Real)) ≤ lowerDensity K output`, then `α/2 ≤ lowerDensity K output`. The exact quantifier skeleton is `∀ K output α, [∀ s : Nat, 2≤s → α/(2+4/(s:Real))≤d_K(output)] → α/2≤d_K(output)`. K, output and α stay fixed across the entire family of scale inequalities. A scale-dependent output set would not satisfy this same statement.

Dependency anchors: G5 for density and `OrderedLanguage.mk`; the explicit target rendering resolves all divisions/additions in the bound as real operations, with only s and its comparison natural. There is no α≥0 assumption, no requirement output⊆carrier, and no extra data structure, charging certificate or algorithm premise. The scales 0 and 1 are outside the antecedent; in particular the formula does not impose a condition involving division by zero at s=0. Empty output is permitted subject to the scale inequalities. This is a conditional analytic passage from all finite scale bounds to the factor 1/2 lower-density bound. Its identifier does not add a pod, generation mechanism, finite-stage error rate, certificate-production result or computational claim.

## 10. `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_4_9`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:42`. Original type, verbatim:

```lean
∀ (X : Set.{0} GenLimit.Language),
  (∀ (L : GenLimit.Language), Membership.mem.{0, 0} X L → Set.Nonempty.{0} L) →
    Iff (GenLimit.KleinbergWei.PartialEnumeration.FullTopology.IdentifiableOnFullTexts X)
      (And (Set.Countable.{0} X) (GenLimit.KleinbergWei.PartialEnumeration.FullTopology.TDSpace X))
```

For each class X of languages, assume every language L∈X is nonempty. Then X is extensionally identifiable on all full texts **if and only if** X is countable and every point satisfies G6's TDPoint condition. Expanded on the left: `∃ M : List Nat → Set Nat, ∀ L∈X, ∀ stream : Nat → Nat, range stream=L → ∃ name : Set Nat, name=L ∧ ∃ T : Nat, ∀ t≥T, M(textPrefix stream t)=name`. Expanded on the right: X is countable and `∀ K∈X, ∃ O : Set(Point X), FullOpen X O ∧ K∈O ∧ ∀ L∈O, L⊆K → L=K`.

Dependency anchors: G1 and G6, `FullTextIdentification.lean:136`, `Bridges/AngluinToPaper02.lean:20,25,34`, `FullTopology.lean:24,98,116`. One learner M must serve the whole class; the stabilizing threshold depends on L and its presentation. Countability concerns the collection of languages, not merely the natural-number element universe. Finite nonempty targets and repeated/delayed text elements are allowed; infinite targets are not required. X itself may be empty, making learner obligations vacuous. Excluding empty member languages avoids vacuous full-text learning obligations for unpresentable targets. There is no computability restriction on M, enumerability of X, effective telltale data, partial-text conclusion or bound on stabilization time.

## 11. `GenLimit.KleinbergWei.PartialEnumeration.Results.corollary_4_10_full_text`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:44`. Original type, verbatim:

```lean
∀ {X : Set.{0} GenLimit.Language},
  GenLimit.KleinbergWei.PartialEnumeration.FullTopology.AllNonempty X →
    Iff (GenLimit.KleinbergWei.PartialEnumeration.FullTopology.SeparatedInLimit X)
      (GenLimit.KleinbergWei.PartialEnumeration.FullTopology.TOneSpace X)
```

For every class X whose member languages are nonempty, the following are equivalent: every ordered pair of distinct points K,L is separated from full texts, and X satisfies G6's TOneSpace definition. The separation side expands to `∀ K L : Point X, K≠L → ∀ stream : Nat → Nat, range stream=K → ∃ T : Nat, ∀ t≥T, ∃ x : Nat, x∈textPrefix stream t ∧ x∉L`. The topology side is `∀ K L : Point X, [∀ O : Set(Point X), FullOpen X O → K∈O → L∈O] → K=L`.

Dependency anchors: G6, `FullTextSeparation.lean:24,36,72,78` and `FullTopology.lean:16,24,70,128`. The threshold may depend on both points and stream. Both ordered directions are required across distinct points; no single common refuting element or threshold is chosen uniformly. This is persistent eventual refutation, not merely infinitely many successful guesses and not an existential learning algorithm. Countability, target infinitude and effective data access are absent. Empty X and singleton classes satisfy the pairwise conditions vacuously; empty member languages are excluded. Full coverage, with repetitions and arbitrary timing allowed, is essential to the separation interpretation. The statement provides no separation guarantee for streams whose range is only an infinite subset of a point.

## 12. `GenLimit.KleinbergWei.PartialEnumeration.Results.corollary_4_10_partial_text_counterexample`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:46`. Original type, verbatim:

```lean
And
  (GenLimit.KleinbergWei.PartialEnumeration.FullTopology.TOneSpace
    GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.counterexampleClass)
  (And
    (Set.Infinite.{0}
      GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.commonLanguage)
    (And
      (Set.Infinite.{0}
        GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.leftLanguage)
      (And
        (Set.Infinite.{0}
          GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.rightLanguage)
        (And
          (Not
            (HasSubset.Subset.{0}
              GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.leftLanguage
              GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.rightLanguage))
          (And
            (Not
              (HasSubset.Subset.{0}
                GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.rightLanguage
                GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.leftLanguage))
            (And
              (GenLimit.Presents
                GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.commonStream
                GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.commonLanguage)
              (And
                (HasSubset.Subset.{0}
                  GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.commonLanguage
                  GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.leftLanguage)
                (And
                  (HasSubset.Subset.{0}
                    GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.commonLanguage
                    GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.rightLanguage)
                  (And
                    (∀ (t : Nat),
                      Not
                        (GenLimit.KleinbergWei.PartialEnumeration.FullTopology.RefutedByHistory
                          (GenLimit.textPrefix.{0}
                            GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.commonStream
                            t)
                          GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.leftLanguage))
                    (∀ (t : Nat),
                      Not
                        (GenLimit.KleinbergWei.PartialEnumeration.FullTopology.RefutedByHistory
                          (GenLimit.textPrefix.{0}
                            GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.commonStream
                            t)
                          GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.rightLanguage)))))))))))
```

This closed statement has no hypotheses or existentially chosen class. Its definitions are `commonStream n=n+2`, `commonLanguage=range commonStream={2,3,…}`, `leftLanguage=commonLanguage∪{0}`, `rightLanguage=commonLanguage∪{1}`, and `counterexampleClass={leftLanguage,rightLanguage}` (`PE/PartialSeparationCounterexample.lean:21,23,25,27,29`, in the FT namespace). Its eleven conjuncts assert: the class is TOneSpace; commonLanguage is infinite; leftLanguage is infinite; rightLanguage is infinite; left is not a subset of right; right is not a subset of left; commonStream presents commonLanguage; commonLanguage⊆left; commonLanguage⊆right; for every t its prefix does not refute left; and for every t its prefix does not refute right.

Dependency anchors: those five definition values, plus G1 and G6's TOneSpace and RefutedByHistory definitions. The skeleton is this fixed conjunction, with independent `∀ t : Nat` in its last two clauses. The shared stream covers the infinite common subset fully, while omitting forever each target's distinguishing marker. At t=0 the prefix is empty; at every later t all seen elements remain in both targets. This specific stream has no repetitions, though general presentation definitions allow them. The class has two distinct, incomparable, infinite, nonempty languages and thus no empty-target vacuity. The theorem does not literally quantify over all learners, negate an exported partial-separation predicate, or assert impossibility of every form of identification. Its exact evidence is simultaneous permanent nonrefutation despite the stated TOneSpace property. No contradiction with full-text separation follows, because this stream presents neither left nor right.

## 13. `GenLimit.KleinbergWei.PartialEnumeration.Results.corollary_4_11`

Source anchor: `GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean:48`. Original type, verbatim:

```lean
∀ {X : Set.{0} GenLimit.Language},
  GenLimit.KleinbergWei.PartialEnumeration.FullTopology.AllNonempty X →
    Iff (GenLimit.KleinbergWei.PartialEnumeration.FullTopology.SeparatedInLimit X)
      (∀ (K L : GenLimit.KleinbergWei.PartialEnumeration.FullTopology.Point X), HasSubset.Subset.{0} ↑K ↑L → Eq.{1} K L)
```

For every class X with all member languages nonempty, `SeparatedInLimit X` holds if and only if for every K,L in `Point X`, underlying K⊆underlying L implies K=L as subtype points. Expanded: the persistent full-text refutation condition `∀ K≠L, ∀ stream presenting K, ∃ T : Nat, ∀ t≥T, ∃ x∈textPrefix stream t, x∉L` is equivalent to `∀ K L : Point X, K⊆L → K=L`. The explicit type fixes both coerced objects as subsets of Nat and fixes the conclusion as equality in `Point X`, not equality of family indices.

Dependency anchors: G6, `FullTextSeparation.lean:24,36,72,78`, `FullTopology.lean:14`. The right side forbids strict inclusion between different class languages. Its quantifier order requires this for every ordered pair, hence supplies both directional noncontainments for any distinct pair. No countability, infinite-target, computability or effective uniformity assumption appears. Empty X and one-point X make the pairwise requirement vacuous, while AllNonempty still excludes an empty member language. Streams cover their source point fully, may repeat values and may postpone distinguishing values arbitrarily; each separating threshold may depend on the stream. The result concerns pairwise refutation and inclusion, without claiming an identifier, stabilization of outputs, any partial-presentation guarantee or a uniform finite observation bound.

## Exhaustive coverage and limits

| # | Target suffix | Assumptions / inputs | Exact conclusion modes | Main anchors |
|---|---|---|---|---|
| 1 | theorem_1_5 | H | one named element output; eventual membership and prefix freshness together | G1–G2 |
| 2 | theorem_1_7 | H | selected intersections infinite always; target containment eventually | G1–G2 |
| 3 | theorem_1_8 | H | named trace infinite always, contained eventually; whole E contained cofinally | G1–G3 |
| 4 | theorem_2_1 | H | same full type as #1 | G1–G2 |
| 5 | theorem_2_2 | H | three clauses: always infinite; eventual containment; cofinal simultaneous sandwich | G1–G3 |
| 6 | theorem_2_4 | H | same full type as #3 | G1–G3 |
| 7 | theorem_3_1_eventual_validity | H with explicit infinitude proof; every external choice | choice-dependent eventual target membership | G1,G3–G4 |
| 8 | theorem_3_1_density_certificate | ordered K; supplied complete certificate; α≤enumerated liminf | output liminf≥α/3 | G5 |
| 9 | theorem_3_5_fixed_pod_endgame | fixed K, output, real α; all natural scales s≥2 | scale bounds imply output liminf≥α/2 | G5 |
| 10 | theorem_4_9 | every class member nonempty | full-text semantic identification iff countable plus TDPoint everywhere | G1,G6 |
| 11 | corollary_4_10_full_text | AllNonempty X | full-text eventual refutation iff specialization forces equality | G6 |
| 12 | corollary_4_10_partial_text_counterexample | fixed definitions, no hypotheses | all eleven conjuncts, including both perpetual nonrefutations | G1,G6 and concrete definitions |
| 13 | corollary_4_11 | AllNonempty X | full-text eventual refutation iff inclusion forces point equality | G6 |

All 13 targets have a quoted original type, explicit binder resolution, source anchor, expanded quantifier reconstruction, dependency anchors, information model, edge cases and limitation statement. The semantic reconstruction needed no additional project interface. The exported ellipses occur in embedded proof terms; the supplying existence propositions and constructor requirements are available. Standard Lean/Mathlib meanings, including finite sets, set equality/inclusion, antitone chains, `Nat.find`, choice and real `Filter.liminf`, are accepted at the declared boundary rather than recursively audited. There are no stochastic laws or support-valued output objects among these target types. Single-element outputs, language-valued hypothesis outputs, intersection-valued traces and density of language sets have been kept distinct.

No fresh Lean elaboration, targeted compilation, full Lake build, proof-body audit, source-paper correspondence review or human certification was performed. Those are outside Stage1. The declared configuration is `gpt-6.1-sol`, reasoning effort `xhigh`, fresh fork `none`; the provider/backend model identifier is unavailable to this reviewer and was not independently measured. The run JSON distinguishes that declared configuration from unavailable backend observability. This report and its run record are the only newly written artifacts and are frozen at mode 0444.
