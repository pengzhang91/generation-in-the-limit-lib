# P12: Stage 1 code-only reconstruction

## Scope, evidence, and interpretation boundary

This is a paper-withheld interpretation of exactly eight exported target types and their recursively supplied defining values. The only mathematical/input material read was `stage1/` in package `P12_2026-11-10_6062058`. Identifiers and source anchors below locate evidence; they supply no intended meaning. No paper, source file at those anchors, developer commentary, PaperMap, registry, previous report, other package, or later-stage material was consulted.

The census is 97 distinct declarations: 8 target theorems and 89 dependencies, comprising 79 definitions, 3 inductive structures, 3 constructors, and 4 generated recursion-obligation theorems. All eight target names agree between `targets.txt`, the root-marked JSON records, and the target statements. All 11 entries in the original `SHA256SUMS` match their actual bytes. A subsequently authorized additive `explicit-target-types/` supplement supplies the same eight kernel types with implicit arguments printed explicitly; both entries in its nested manifest also match. The run record contains actual sizes and SHA256 hashes for all 15 input files, including both manifests, and records the supplement access timing.

| Input | Role in reconstruction |
|---|---|
| `START_HERE.md`, `PROMPT.md` | Access restrictions and required reconstruction method |
| `targets.txt`, `01-target-statements.md` | Exact scope, target types, source anchors |
| `02-definition-dependencies.md`, `declarations.jsonl` | Project definition values, structure constructors/projections, dependency metadata |
| `external-constant-boundary.txt` | 63 standard Lean/Mathlib constants assumed at the boundary |
| `snapshot.json` | Supplied snapshot provenance and source locators; underlying files were not opened |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Declared Lean 4.24.0, package configuration, Mathlib v4.24.0 / revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` |
| `SHA256SUMS` | Original input integrity manifest |
| `explicit-target-types/README.md`, `types.jsonl`, `SHA256SUMS` | Additive code-only explicit root types and separately checked two-entry manifest |

Standard meanings of sets, membership, subset, union, intersection, finite/infinite sets, finite cardinality, natural/integer numbers, `Fin`, injectivity, Boolean decision, options, monotonicity, classical logic, and well-founded recursion are assumed, not independently audited. The four generated theorem types justify recursion into earlier natural stages; their proof bodies are unavailable. Printed `⋯` occurs inside supplied values and is not evidence of a hole. No missing project body decisive for the following interpretation was identified. This does not certify the exporter, proof correctness, source correspondence, fresh compilation, or human review.

## Definition glossary and shared semantics

**Objects.** In `GenLimit.Generic`, `Language α = Set α`, `LanguageClass α = Set (Set α)`, `LanguageFamily α = Nat → Set α`, and `Stream α = Nat → α`. A class is an arbitrary collection; a family is an indexed sequence with possible repeated languages. `UUS C` means exactly `∀ L ∈ C, L.Infinite`; it says nothing about the number of languages. `Countable α` in targets 1.3–1.4 supplies a proposition about the alphabet, not an effective enumeration.

**Observation and output.** `FiniteHistoryOperator Input Output` is `(n : Nat) → (Fin n → Input) → Output`; `Generator α` specializes both types to `α`. `sample s n` is the finite set `{s(k) | k < n}`; `output G s n` applies `G` to that ordered prefix. `observedThrough s t = sample s (t+1)` and `outputAt G s t = output G s (t+1)`. Thus stage zero already has one observation, and ordinary stage `t` output sees exactly `s(0), …, s(t)`. Histories preserve order and multiplicity even though the freshness test uses a set.

`CorrectAt G L s t` is the conjunction `outputAt G s t ∈ L` and `outputAt G s t ∉ observedThrough s t`. Failure is an invalid output or an already observed value. There is one deterministic output, no numerical loss, law, distribution, support condition, expectation, failure probability, limsup, or rate. Prior generated outputs and queried values are absent from this freshness set. No pairwise distinctness condition is imposed on an sample-only generator's successive outputs; repeating a still-unobserved value is allowed by this predicate.

**Presentation predicates.** `Presents s L` means `range s = L`; `StreamIn s L` means `range s ⊆ L`. `InjectivePresentation`, aliased by `ExactEnumeration`, adds injectivity to exact range equality. Every input model used below is injective, so inputs have no repeated values. `InfiniteOmissionEnumeration s L` means injectivity plus `range s ⊆ L`; it allows zero, finitely many, or infinitely many omissions. It still presents an infinite observed subset, because the stream is total on `Nat` and injective.

`SetDifferenceAtMost A B i` means there exists a finite set `F` whose underlying set equals `A \ B` and whose cardinality is at most `i`; `MissingAtMost` aliases this definition. `EnumerationWithOmissionsAtMost s L i` means injectivity, `range s ⊆ L`, and `|L \ range s| ≤ i`. `ValuesOutsideAtMost s L i` bounds `|range s \ L|`. `InjectiveValueContaminatedPresentationAtMost`, aliased by `NoisyEnumerationWithLevel`, requires injectivity, `L ⊆ range s`, and that outside-value bound. Thus bounded noise adds at most `i` distinct nonmembers and omits no target elements. `InjectiveValueContaminatedPresentation`, aliased by `NoisyEnumeration`, replaces the bound with finiteness of `range s \ L`. It means unknown finite contamination, never infinitely many contaminants. No positions, arrival times, or ratios are bounded; injectivity makes counts of contaminating values also counts of contaminating positions.

**Three threshold orders.** For a correctness predicate `K` and admissibility predicate `A`, the exported generic templates expand as follows (membership hypotheses are retained):

- `IsUniformEventuallyCorrect K A G C`: `∃ T, ∀ L ∈ C, ∀ s, A s L → ∀ t ≥ T, K G L s t`.
- `IsTargetwiseEventuallyCorrect K A G C`: `∀ L ∈ C, ∃ T, ∀ s, A s L → ∀ t ≥ T, K G L s t`.
- `IsPresentationwiseEventuallyCorrect K A G C`: `∀ L ∈ C, ∀ s, A s L → ∃ T, ∀ t ≥ T, K G L s t`.

Here and below each `T` may depend on parameters preceding its existential, including the chosen generator; it cannot depend on subsequent universally quantified data. `IsUniformGenerator` and `IsNonuniformGenerator` use exact enumerations and respectively the first two templates. Their `InfiniteOmission` variants replace admissibility with arbitrary injective substreams. `IsUniformNoisyGenerator` and `IsNonuniformNoisyGenerator` use unknown finite contamination and respectively the first two templates. `IsNoisyLimitGenerator` uses the third. `IsLimitGeneratorWithNoiseLevel`, `IsLimitGeneratorWithOmissions`, and `IsLimitGeneratorWithoutRepetitions` use the third template with their indicated admissibility. Every corresponding `Generatable…` predicate existentially quantifies a single generator before these target/stream quantifiers.

**No observations.** `WithoutSamplesGenerator.mk` takes a sequence `a : Nat → α` and a proof that `a` is injective. Its projection `output` is that sequence. `GeneratesInLimitWithoutSamples a C` is `∀ L ∈ C, ∃ T_L, ∀ t ≥ T_L, a(t) ∈ L`; its uniform version moves `∃ T` before `∀ L ∈ C`. Their existential wrappers choose one injective sequence for the whole class. There is no input, query, or freshness relative to samples; injectivity supplies nonrepetition among all outputs, including the initial segment.

**Core cover.** `classIntersection D = {x | ∀ L ∈ D, x ∈ L}`; `languageIntersection` aliases it. `IsNondecreasingCover C D` means `D` is monotone under class inclusion and `C = ⋃ n, D(n)`. `IsIncreasingInfiniteCoreCover` adds `∀ n, (classIntersection (D(n))).Infinite`; `HasIncreasingInfiniteCoreCover` existentially chooses `D`. Empty stages are permitted. The intersection of an empty stage is the entire alphabet by the universal formula. Cores need not be named, effective, or supplied by an algorithm.

**Optional queries.** `FeedbackGenerator.mk` contains two arbitrary functions. At stage `t`, `query` takes `Fin (t+1) → α` observations and `Fin t → Option Bool` previous responses, returning either no query or one `α`. Its `output` takes the same observations and `Fin (t+1) → Option Bool` responses, so it can use the current answer. `feedbackQuery` supplies those histories. `membershipAnswer L q = decide (q ∈ L)` is the semantic membership bit. `actualFeedbackResponse` recursively supplies `none` for no query and `some` of that bit otherwise. `actualFeedbackOutput` runs the output with these truthful responses; `FeedbackCorrectAt` imposes the same membership-and-stream-freshness conjunction.

`CompatibleResponses` requires only equality of response/query `isSome` flags at every stage, not truthful bits. `HasAtMostQueries G b` requires, for every stream and every compatible response sequence, both finiteness of the set of query stages and its `Set.ncard ≤ b`. The explicit finiteness conjunct matters: this is an actual finite cap, with each queried stage counted, including repeated queries of one value. It imposes no fixed latest query time. `IsLimitFeedbackGeneratorWithQueries` conjoins this global cap with presentationwise eventual correctness on truthful runs for every exact target enumeration. Its existential wrapper is `GeneratableInLimitWithQueries`.

**Mandatory queries and identification.** `MandatoryQueryMachine α β` has a query function returning one `α` at every stage, using the current observation prefix and previous Boolean answers, and an output function returning `β` using that prefix and answers through the current stage. `actualMandatoryQueryResponse` recursively returns truthful membership bits; `actualMandatoryQueryOutput` uses them. `TotalFeedbackGenerator α` specializes `β = α`; `actualTotalFeedbackOutput` and `TotalFeedbackCorrectAt` give its actual output and membership/freshness condition. `IsLimitTotalFeedbackGenerator` requires presentationwise eventual correctness on exact enumerations, and its existential wrapper chooses one machine. There is no query budget.

`FeedbackIdentifier α` specializes the same machine to `β = Nat`; `actualIdentifierOutput` is its actual output index. `NonuniformlyIdentifiesWithFeedback I C` means `∀ z, ∃ T_z, ∀ s, ExactEnumeration s (C z) → ∀ t ≥ T_z, C(actualIdentifierOutput I (C z) s t) = C z`. The existential wrapper chooses one identifier for the family. Correctness is equality of languages, not equality to index `z`, eventual constancy of indices, or fresh generation.

**Computation boundary.** All fields above are unrestricted mathematical functions; no exported predicate requires recursive/partial-recursive/computable functions, decidable target membership, running time, or an executable class presentation. Truthful query evaluation represents semantic access to target membership and is compatible with an oracle interpretation; it does not establish ordinary computation or even an effective implementation relative to that oracle. An existential machine for each class/family is not a uniform program taking a class/family as input. The constructors describe available information, and cannot justify stronger computational claims.

## Target dossiers

The following Lean blocks reproduce the exported types verbatim. All eight source anchors belong to module `GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview`, path `GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean`. Some existential domains are suppressed by the original pretty printer. The supplement directly prints `@… Nat` for 1.1 and 1.7 and `@… Int` for 1.5–1.6, establishing `C₁,C₂ : LanguageClass Nat` in 1.1, `C : LanguageClass Int` in 1.5–1.6, and `C : LanguageClass Nat` in 1.7. These explicit arguments agree with the original dependency metadata. The original signatures below are preserved; no new assumption is added.

### 1.1 — `GenLimit.NoiseLossFeedback.Results.theorem_1_1`

Source anchor: `GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview`, `Overview.lean:221`.

```lean
∃ C₁ C₂,
  And (GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutSamples.{0} C₁)
    (And (GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutSamples.{0} C₂)
      (Not (GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutRepetitions.{0} (Union.union.{0} C₁ C₂))))
```

There exist two classes of subsets of `Nat`, `C₁` and `C₂`, together satisfying all three conjuncts: one injective sequence is eventually in each member of `C₁`, with a target-dependent threshold; another injective sequence is in every member of `C₂` after one common threshold; and their class union admits no sample-only generator that is eventually correct on every injective exact enumeration.

Quantifier skeleton: `∃ C₁,C₂, [(∃ a injective, ∀ L∈C₁, ∃ T_L, ∀ t≥T_L, a(t)∈L) ∧ (∃ b injective, ∃ T, ∀ L∈C₂, ∀ t≥T, b(t)∈L) ∧ ¬∃ G, ∀ L∈C₁∪C₂, ∀ s exact L, ∃ T, ∀ t≥T, CorrectAt G L s t]`.

The two positive witnesses need not coincide. They receive only time; the impossible union learner receives the full ordered sample prefix. The negative conclusion says every such generator has some union target and exact stream with failures arbitrarily late. It is not a statement about a union of two individual languages, a named separating class, computable witnesses, or output-output nonrepetition. No explicit infinitude hypothesis on these classes is present, although each positive no-sample property forces each member to contain an infinite tail. The targets/classes are existentially unspecified.

### 1.2 — `GenLimit.NoiseLossFeedback.Results.theorem_1_2`

Source anchor: `GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview`, `Overview.lean:233`.

```lean
∀ (C : GenLimit.Generic.LanguageClass.{0} Nat),
  GenLimit.Generic.UUS.{0} C →
    And
      (Iff (GenLimit.NoiseLossFeedback.UniformlyNoisilyGeneratable.{0} C)
        (GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutSamples.{0} C))
      (Iff (GenLimit.NoiseLossFeedback.NonuniformlyNoisilyGeneratable.{0} C)
        (GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutSamples.{0} C))
```

For each class `C` of subsets of `Nat` whose every member is infinite, two equivalences hold together. Uniform eventual generation under arbitrary finite contamination is equivalent to a uniform no-sample injective output sequence. Targetwise eventual generation under the same contamination model is equivalent to a no-sample injective sequence whose eventual membership threshold can depend on the target.

Quantifier skeleton, under `∀ L∈C, L.Infinite`: `(∃ G, ∃ T, ∀ L∈C, ∀ s noisy L, ∀ t≥T, CorrectAt G L s t) ↔ (∃ a injective, ∃ T, ∀ L∈C, ∀ t≥T, a(t)∈L)`; and `(∃ G, ∀ L∈C, ∃ T_L, ∀ s noisy L, ∀ t≥T_L, CorrectAt G L s t) ↔ (∃ a injective, ∀ L∈C, ∃ T_L, ∀ t≥T_L, a(t)∈L)`.

The noisy learner sees the prefix but not which observations are contaminants, their total number, or the target. Both thresholds on the noisy sides precede the stream quantifier; they cannot depend on the stream or its finite contamination count. The theorem asserts existence-level equivalences, with no named conversion, common witness, preservation of thresholds, or ordinary program. It does not equate the presentationwise noisy-limit predicate with either right side. The empty class satisfies the premise and both equivalences on `Nat`; arbitrary finite classes of infinite languages and repeated descriptions have no additional restriction.

### 1.3 — `GenLimit.NoiseLossFeedback.Results.theorem_1_3`

Source anchor: `GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview`, `Overview.lean:243`.

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] (C : GenLimit.Generic.LanguageClass.{u_1} α),
  Iff (GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutSamples.{u_1} C)
    (GenLimit.NoiseLossFeedback.HasIncreasingInfiniteCoreCover.{u_1} C)
```

For any type `α` at the displayed universe and any instance `Countable α`, every class `C` of languages over `α` has a no-sample eventually successful injective sequence if and only if it has a monotone countable cover by subclasses with infinite common intersections at every stage.

Quantifier skeleton: `∀ {α} [Countable α], ∀ C, [(∃ a injective, ∀ L∈C, ∃ T_L, ∀ t≥T_L, a(t)∈L) ↔ (∃ D:Nat→LanguageClass α, Monotone D ∧ C=⋃n D(n) ∧ ∀ n, {x | ∀ L∈D(n), x∈L}.Infinite)]`.

The cover is chosen for the whole class and every stage has an infinite intersection; neither stabilization of the cover nor an infinite intersection of all of `C` is required. An individual language need only enter some stage, after which it remains included. The sequence sees no observations. The cover is semantic data, with no finite enumeration or computable extraction guarantee. `UUS C` is not a hypothesis; either side itself forces each member infinite.

Degenerate cases matter here. If `C` is empty and `α` infinite, all stages may be empty and the intersection formula yields `α`, matching existence of an injective no-sample sequence. If `α` is finite, even an empty `C` has neither side: no injective `Nat → α` exists, and no subset of `α` is infinite. Empty stages are not evidence of a missing infinite-core obligation.

### 1.4 — `GenLimit.NoiseLossFeedback.Results.theorem_1_4`

Source anchor: `GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview`, `Overview.lean:252`.

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] {C : GenLimit.Generic.LanguageClass.{u_1} α},
  GenLimit.Generic.UUS.{u_1} C →
    And
      (∀ (gen : GenLimit.Generic.Generator.{u_1} α),
        GenLimit.NoiseLossFeedback.IsUniformGenerator.{u_1} gen C →
          GenLimit.NoiseLossFeedback.IsUniformInfiniteOmissionGenerator.{u_1} gen C)
      (∀ (gen : GenLimit.Generic.Generator.{u_1} α),
        GenLimit.NoiseLossFeedback.IsNonuniformGenerator.{u_1} gen C →
          GenLimit.NoiseLossFeedback.IsNonuniformInfiniteOmissionGenerator.{u_1} gen C)
```

For every countable alphabet and class all of whose languages are infinite, both implications hold for every given sample-only generator: uniform success on exact enumerations implies uniform success on all injective streams contained in the target; targetwise success on exact enumerations implies targetwise success on all such substreams.

Quantifier skeleton: `∀ {α} [Countable α] {C}, UUS C → [(∀ G, (∃ T ∀ L∈C ∀ s exact L ∀ t≥T, CorrectAt …) → (∃ T' ∀ L∈C ∀ s injective-in-L ∀ t≥T', CorrectAt …)) ∧ (∀ G, (∀ L∈C ∃ T_L ∀ s exact L ∀ t≥T_L, CorrectAt …) → (∀ L∈C ∃ T'_L ∀ s injective-in-L ∀ t≥T'_L, CorrectAt …))]`.

The generator is unchanged in each implication: this is stronger than merely producing some generator for the omission model. No equality of original and resulting threshold witnesses is stated. The second implication preserves targetwise threshold order, not presentationwise order. The observations contain no invalid values, but may omit infinitely many valid ones; the learner is not told which are missing. “Infinite omission” permits exact streams too. Empty `C` gives vacuous correctness implications; on finite `α`, `UUS` forces `C` empty. No repetition or exhaustion is allowed in an admissible infinite substream.

### 1.5 — `GenLimit.NoiseLossFeedback.Results.theorem_1_5`

Source anchor: `GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview`, `Overview.lean:266`.

```lean
∀ (i : Nat),
  ∃ C,
    And (GenLimit.Generic.UUS.{0} C)
      (And (GenLimit.NoiseLossFeedback.GeneratableInLimitWithOmissions.{0} C i)
        (And (Not (GenLimit.NoiseLossFeedback.GeneratableInLimitWithOmissions.{0} C (HAdd.hAdd.{0, 0, 0} i 1)))
          (And (GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel.{0} C i)
            (Not (GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel.{0} C (HAdd.hAdd.{0, 0, 0} i 1))))))
```

For each natural number `i`, there exists one class `C` of subsets of `Int` satisfying five conjuncts: every member is infinite; some generator handles at most `i` omissions; no generator handles at most `i+1` omissions; some generator handles at most `i` contaminating values; and no generator handles at most `i+1` contaminating values. The same class witnesses both separations at that level.

Quantifier skeleton: `∀ i, ∃ C:LanguageClass Int, UUS C ∧ (∃ G_o, ∀ L∈C ∀ s omission≤i L, ∃ T_{L,s}, ∀ t≥T, CorrectAt …) ∧ ¬∃ G'_o, …omission≤i+1… ∧ (∃ G_n, ∀ L∈C ∀ s noise≤i L, ∃ T_{L,s}, ∀ t≥T, CorrectAt …) ∧ ¬∃ G'_n, …noise≤i+1…`.

`C` can depend on `i`; `G_o` and `G_n` can depend on `C,i` and need not coincide. Both thresholds may depend on the entire presentation. The learners see prefixes, without a supplied list of missing/invalid values. The two noise models are different: omissions retain a subset; contamination includes the entire target. The bounds are “at most,” not exact counts. At `i=0`, both positive models reduce to injective exact enumeration, whereas the negative models allow one error of the corresponding kind. Each negative statement permits a counterexample with arbitrarily late membership/freshness failures; it gives no finite failure-time bound or explicit class construction in the target type.

### 1.6 — `GenLimit.NoiseLossFeedback.Results.theorem_1_6`

Source anchor: `GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview`, `Overview.lean:278`.

```lean
∃ C,
  And (∀ (i : Nat), GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel.{0} C i)
    (Not (GenLimit.NoiseLossFeedback.NoisilyGeneratableInLimit.{0} C))
```

There exists one class `C` of subsets of `Int` such that for every natural finite bound `i` there is a generator eventually correct for every injective complete-target enumeration with at most `i` contaminating values, yet no one generator is eventually correct for all injective complete-target enumerations having an arbitrary finite set of contaminants.

Quantifier skeleton: `∃ C:LanguageClass Int, [(∀ i, ∃ G_i, ∀ L∈C ∀ s noise≤i L, ∃ T_{i,L,s}, ∀ t≥T, CorrectAt …) ∧ ¬∃ G, ∀ L∈C ∀ s noisy L, ∃ T_{L,s}, ∀ t≥T, CorrectAt …]`.

The witness class is independent of `i`. The positive generators may depend on `i` and need not form an effective or uniformly given sequence of programs. The negative learner is not given a contamination bound. Both sides have presentationwise thresholds, so the separation is not caused by moving a threshold before the stream quantifier. The unbounded parameter ranges over finite contamination sizes; it does not allow infinitely many outside values. There is no explicit `UUS` conjunct here: one must not import it from 1.5. With finite target and finite contamination, no total injective presentation exists, and obligations for that target are vacuous. Negative generation for the whole existential class nevertheless requires some admissible failing target/stream for each candidate generator.

### 1.7 — `GenLimit.NoiseLossFeedback.Results.theorem_1_7`

Source anchor: `GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview`, `Overview.lean:287`.

```lean
∃ C,
  And (GenLimit.NoiseLossFeedback.GeneratableInLimitWithTotalFeedback.{0} C)
    (And (Not (GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutRepetitions.{0} C))
      (∀ (budget : Nat), Not (GenLimit.NoiseLossFeedback.GeneratableInLimitWithQueries.{0} C budget)))
```

There exists a class `C` of subsets of `Nat` with all three properties: a mandatory-query machine is presentationwise eventually correct using truthful target-membership answers at every stage; no sample-only generator has the corresponding exact-enumeration limit guarantee; and for every natural budget no optional-query generator satisfying that global finite cap has that guarantee.

Quantifier skeleton: `∃ C, [(∃ M, ∀ L∈C ∀ s exact L, ∃ T, ∀ t≥T, TotalFeedbackCorrectAt M L s t) ∧ (¬∃ G, ∀ L∈C ∀ s exact L, ∃ T, ∀ t≥T, CorrectAt G L s t) ∧ (∀ b, ¬∃ F, HasAtMostQueries F b ∧ (∀ L∈C ∀ s exact L, ∃ T, ∀ t≥T, FeedbackCorrectAt F L s t))]`.

The class and positive machine are chosen before every budget; no bounded-budget positive machine is claimed. The mandatory machine can query any alphabet value each stage and use the answer immediately. Its output still must be a target member absent from the observed stream prefix; query history alone does not make an element observed. All correctness thresholds may depend on target and stream. The cap for a candidate finite-query machine applies even to compatible answer histories with false bits and streams outside the class; a truthful-run-only cap is insufficient. Repeating a query spends another unit.

The ordinary impossibility and every-budget impossibility are separate conjuncts and both are retained. For each capped machine, impossibility entails some admissible target/stream with failures arbitrarily late. The theorem does not cover machines with merely a target-dependent finite cap, or guarantee index identification, computability, named witnesses, or a bound on convergence time. No `UUS` hypothesis/conjunct is stated; finite target presentations are inadmissible rather than exhausted and padded.

### 1.8 — `GenLimit.NoiseLossFeedback.Results.theorem_1_8`

Source anchor: `GenLimit.Paper12_NoiseLossAndFeedback.Results.Overview`, `Overview.lean:297`.

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat), GenLimit.NoiseLossFeedback.NonuniformlyIdentifiableWithFeedback.{0} C
```

For every indexed family `C : Nat → Set Nat`, there is one mandatory-membership-query identifier that eventually outputs an index for the correct target language, with a convergence threshold for each target index that is uniform over all its injective exact enumerations.

Quantifier skeleton: `∀ C, ∃ I:FeedbackIdentifier Nat, ∀ z:Nat, ∃ T_z, ∀ s:Nat→Nat, [Injective s ∧ range s=C(z)] → ∀ t≥T_z, C(actualIdentifierOutput I (C z) s t)=C(z)`.

The identifier may depend on the entire family. At time `t` it has observations through `t`, truthful answers to its previous queries, and its current membership answer before producing a natural index. No target index or full target set is supplied as an ordinary input: the target parameter in the actual-run definition supplies the membership oracle. The threshold may depend on `C,I,z`, but not the presentation or `t`.

Repeated family indices are allowed. Output indices may change forever among indices naming the same language; the condition neither forces the original index `z` nor syntactic stabilization. It is extensional eventual correctness at every sufficiently late stage, not correctness only frequently. No single class-wide threshold, no uniform computable map from family descriptions to identifiers, and no effective membership test for family languages is asserted.

A family has an index for every natural number, so it is not an empty class. Its entries may be empty or finite: those entries have no injective infinite exact presentation and their conditions are vacuous. An infinite proper substream does not qualify unless its range equals the target. The statement imposes no `UUS`, no distinctness of family entries, and no generation-freshness loss on identifier outputs.

## Exhaustive target coverage and common edge checks

| Target | Domain and hypotheses | Witness and threshold dependency | Complete conclusion / observation model | Covered edge cases |
|---|---|---|---|---|
| 1.1 | Two classes over `Nat`; no explicit hypothesis | Separate injective time-only sequences; targetwise / uniform thresholds | Both positive predicates; ordinary exact-input union impossibility | Class union, arbitrary-late failure, no named witnesses |
| 1.2 | `C` over `Nat`; `UUS C` | Existential generators/sequences; uniform and targetwise orders separately | Both directions of both equivalences; arbitrary finite contamination | Empty class; no presentationwise equivalence; unknown noise count |
| 1.3 | Any `Countable α`, any `C` | One injective sequence ↔ one monotone subclass sequence | Countable union equality and every infinite intersection | Empty stages/class; finite/empty alphabet; no effective cover |
| 1.4 | Any `Countable α`; `UUS C` | Every same given `G`; uniform and targetwise thresholds | Both exact-to-substream implications | Zero/finite/infinite omissions; empty class; same generator |
| 1.5 | `∀ i:Nat`; one `C` over `Int`; `UUS C` | Class depends on `i`; two positive generators; streamwise thresholds | All five conjuncts, simultaneous omission and contamination separations | `i=0`; at-most bounds; separate noise models |
| 1.6 | One `C` over `Int`; no `UUS` conjunct | `∀ i ∃ G_i`; no common unbounded-noise `G`; streamwise thresholds | All finite bounds positively, arbitrary finite contamination negatively | No infinitely contaminated streams; finite-target vacuity |
| 1.7 | One `C` over `Nat`; no `UUS` conjunct | One mandatory-query machine; all budgets negated; streamwise thresholds | Total feedback positive, ordinary negative, every finite budget negative | Optional/mandatory timing; global compatible-history cap; repeated queries |
| 1.8 | Every `Nat`-indexed family over `Nat` | `∀ C ∃ I ∀ z ∃ T_z ∀ s`; current answer available | Eventual language equality for every exact presentation | Repeated indices; changing correct indices; empty/finite entries |

All eventual conclusions use `∀ t ≥ T`; none promise correctness before `T`, a computable threshold, a quantitative sample bound, a rate, a limiting error fraction, or a probability. In the sample-based generation predicates, an exact stream never exhausts its target because injectivity on all naturals forces an infinite range. Finite targets with admissible finite-omission or finite-contamination models are likewise impossible to present; they are not padded by repetition. Finite targets can never admit an injective infinite substream. Consequently quantifiers over these presentations can be vacuous, whereas existence of a no-sample generator itself always requires an infinite alphabet. On an empty alphabet no sample-only generator exists either, because its zero-length-history case must return an element.

For negative existential generation claims over the inhabited alphabets `Nat` and `Int`, classical expansion gives the useful failure reading: every candidate generator has some target and admissible stream for which every proposed threshold is followed by a stage violating membership or freshness. For a query-budget claim, restrict this reading to candidates satisfying the cap; failure of the cap alone also prevents being a valid witness. No target type specifies a particular adversarial stream, loss constant, or named separating class.

Generated helper coverage is limited to its supplied interface: `actualFeedbackResponse._proof_1/_proof_2` and `actualMandatoryQueryResponse._proof_1/_proof_2` state well-foundedness and decrease of `Fin t` indices, while `actualFeedbackResponse.match_1` is ordinary option case analysis. The three structure constructors and their projections determine all observation/query/answer timing described above. These dependencies were interpreted by type/value only, with no proof audit or new build.
