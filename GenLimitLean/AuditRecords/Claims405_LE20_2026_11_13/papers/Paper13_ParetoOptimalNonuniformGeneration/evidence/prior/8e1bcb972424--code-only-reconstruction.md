# P13: Stage 1 paper-withheld reconstruction

This report reconstructs the supplied types and recursively necessary definition values. It uses only this package's `stage1/` interface. A declaration name or source path identifies evidence; it supplies no mathematical interpretation by itself. Nothing here certifies a proof body, correspondence with a paper, a fresh compilation, or a human review.

## Input census and evidence boundary

The original input has six target declarations and 124 dependencies: **130 declarations** comprising 78 definitions, 42 theorems (including the six targets), five inductives and five constructors. The six `root = true` records in `declarations.jsonl` agree exactly with `targets.txt`. The target Markdown contains their printed types; the dependency Markdown contains all 124 remaining declarations. All 130 records were considered. Every referenced project constant is exported; the dependency graph has 82 external Lean/Mathlib constants, all listed in `external-constant-boundary.txt`.

The controlling files are `START_HERE.md` and `PROMPT.md`. Mathematical evidence is `01-target-statements.md`, `02-definition-dependencies.md` and `declarations.jsonl`. `snapshot.json`, `SHA256SUMS`, `targets.txt`, `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` supply scope, integrity and environment metadata. Actual byte hashes of every Stage 1 file appear in `stage1-run.json`; the original eleven manifest entries were checked. The supplied toolchain is Lean 4.24.0, with Mathlib requested at v4.24.0 and pinned in the manifest to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. These metadata are not evidence of a build in this run.

The source anchors below reproduce exported locators; their source files were not opened. Standard meanings of natural numbers, finite sets/lists, sets, finiteness/infinity, choice, least-witness search, order and logic are accepted at the declared external boundary. No recursive external-body audit was made. Printed `⋯` terms suppress embedded proofs; theorem proof values are withheld. This leaves proof correctness and detailed tie choices outside the reconstruction, not additional mathematical hypotheses.

The additive `explicit-target-types/{README.md,types.jsonl,SHA256SUMS}` supplement was first accessed at approximately **2026-11-10 05:58:48 UTC**, after the original interface and draft reconstruction. Its separate two-entry manifest was verified. It contains the same six root names with explicit application arguments. The original signatures below are preserved verbatim. The supplement still prints `∃ G time` / `∃ G` without literal binder-domain annotations; its explicit `@AchievesTimeVector α G F time` applications, read with that definition's exported type, resolve G as `HistoryGenerator α` and time as `TimeVector`. No additional hypothesis or paper context is introduced.

## Definition glossary and shared semantics

Write `P = GenLimit.ParetoGeneration` below; unqualified project names refer to that namespace. These abbreviations shorten the prose and quantifier skeletons, not the original signatures.

**Objects and observations.** `Generic.Language α = Set α`; `F : Nat → Set α` is an arbitrary indexed family. `TimeVector = Nat → Nat`. A `HistoryGenerator α` is exactly `(t : Nat) → (Fin t → α) → α`, through `Generic.Generator` and `FiniteHistoryOperator`. It returns one element from a finite ordered history; it receives no coordinate, true language, infinite presentation, or correctness certificate as an argument. `sequenceSample xs` is the image of `xs` on all `Fin t`, a finite set that discards order and repetitions.

**Clean achievement.** `AchievesTimeVector G F time` means
`∀ i t (xs : Fin t → α), time i ≤ t → Injective xs → (∀ k, xs k ∈ F i) → (G t xs ∈ F i ∧ ∀ k, G t xs ≠ xs k)`.
The same G and time work for every coordinate, eligible length and eligible history. The threshold depends on the coordinate, not on the particular history. This is correctness and novelty at **every** eligible t at or beyond a specified threshold. It is stronger than an unspecified history-dependent eventual guarantee; it is not a claim about merely frequent success, a limsup, or a probabilistic rate.

**Noisy achievement.** `noisyExceptions F i S = {x ∈ S | x ∉ F i}`; `NoiseContainedAt F noise i S` says this set has cardinality at most `noise i`. `AchievesNoisyTimeVector` replaces the clean membership premise by this noise condition and retains injectivity, threshold, target membership and freshness against **all** history elements, including contaminants. Each `noise i` is an arbitrary natural-number budget for coordinate i; neither monotonicity nor one common bound is assumed. It counts distinct outside elements, not a fraction or a stochastic noise rate. Injectivity makes this count agree with outside positions on eligible histories.

**Realizability and positivity.** `PositiveTimeVector time` means `∀ i, 1 ≤ time i`. `RealizableTimeVectors F` contains exactly time vectors for which `∃ G, AchievesTimeVector G F time ∧ PositiveTimeVector time`. The noisy set makes the analogous replacement with fixed F and noise. Membership hides one generator chosen before all coordinates/histories, not one generator per coordinate. Positivity is an independent conjunct of membership, even though named bounds containing `complexity i + 1` are automatically positive.

**Comparisons.** `ImprovesSomewhere s b := ∃ i, s i < b i`; `WorseSomewhere s b := ∃ j, b j < s j`. Thus `ParetoOptimal A b` is
`∀ s, s ∈ A → (∃ i, s i < b i) → ∃ j, b j < s j`.
It does not itself assert `b ∈ A`, positivity, uniqueness, or a coordinatewise minimum. The targets supply membership/achievement separately. `PrefixParetoOptimal n A b` restricts both the improvement witness and the worsening witness to indices below n. Competitors remain whole vectors in A, with no tail restriction. The worsening coordinate need not precede the improving coordinate. `MatchesPrefix n s b := ∀ i, i < n → s i = b i`. Separately, `EarlierTradeoff b A` is stronger:
`∀ s ∈ A, ∀ i, s i < b i → ∃ j, j < i ∧ b j < s j`.
In particular improvement at coordinate zero is impossible under this property.

**Finite intersections and clean scores.** `indexedIntersection F W = {x | ∀ j ∈ W, x ∈ F j}`. A `FiniteIntersectionCandidate F U i W` consists of all three conditions `W ⊆ U`, `i ∈ W`, and finiteness of that intersection. Its score is the intersection's `Set.ncard`, its ordinary cardinality on these finite candidates. `exists_maximal_finiteIntersectionCandidate` exports existence of a candidate whose score bounds every other candidate's score, conditional on some candidate existing. The displayed choice value and its dependency list identify `procedureStepWitness` with a choice from that maximal-candidate existence, and an empty-set fallback when no candidate exists. `procedureStepComplexity` is that chosen score if candidates exist, otherwise zero. Zero therefore need not distinguish absence of candidates from a candidate with empty intersection.

**Stages and canonical clean complexity.** A `ProcedureStage F n` carries an order list, a total complexity function and a finite index witness for every coordinate. Its constructor requires: the list permutes `List.range n`; complexity is pairwise nondecreasing along it; at every decomposition `before ++ i :: after`, all finite-intersection candidates in `{i} ∪ before.toFinset` containing i have score at most `complexity i`; and, for `i < n` with positive complexity, the stored witness is a candidate within `range (i+1)` whose score equals that complexity. Every other j in a stored witness satisfies `j < i` and `complexity j < complexity i`. The last condition applies regardless of whether complexity is positive.

`canonicalProcedureStage F 0` uses empty order, zero complexity and empty witnesses. Extension chooses an `InsertionSplit` of the old order as `left ++ right`, inserts the new coordinate n between the parts, and sets only its complexity/witness. Its scope is `{n} ∪ left.toFinset`, and its new score is `procedureStepComplexity` in that scope. The split requires old complexities in left to be strictly below that insertion score; for each `right = before ++ i :: after`, the insertion score using `left ++ before ++ [i]` is at most the old complexity at i. These are constrained classical choices, not a numerical formula independent of F. Finally,
`canonicalComplexity F i = (canonicalProcedureStage F (i+1)).complexity i`.
Stage n's complexity in target 1 is preserved as that exact expression; the target does not replace its unrestricted suffix by this diagonal definition.

**Noisy scores and stages.** A `NoisyWitnessCandidate F noise U i S W` requires `W ⊆ U`, `i ∈ W`, a finite indexed intersection, and `NoiseContainedAt F noise j S` for every j in W. S need not be contained in that intersection. `NoisyProcedureSampleCandidate` existentially quantifies W. The exported maximal-sample theorem supplies a candidate sample S whose cardinality is at least every other candidate sample's cardinality, assuming candidates exist. `totalNoisyStepSample` chooses such a sample or the empty fallback; `totalNoisyStepComplexity` is its cardinality; `totalNoisyStepWitness` chooses a witnessing W when the chosen sample is a candidate, otherwise the empty set. This sample is a stored mathematical witness, not the learner's observed history.

`NoisyProcedureStage` adds stored witness sets to the clean stage data. Its constructor requires a permutation order, pairwise nondecreasing complexities, and the analogous prefix bound on cardinalities of **every** noisy candidate sample with **every** candidate W. For every old i, complexity equals its stored sample's cardinality; when positive, that sample and W form a noisy candidate in `range (i+1)`. Every j in W satisfies the corresponding noise condition on that stored sample, and every other j satisfies the same strict earlier-index and smaller-complexity conditions as above. Initialization is empty/zero. Extension uses the analogous noisy split inequalities, noisy insertion scope and score, and updates only the new coordinate's data. Define
`canonicalNoisyComplexity F noise i = (canonicalNoisyProcedureStage F noise (i+1)).complexity i`.
No closed formula in the clean complexity and noise budgets is supplied.

**Schedulers and output construction.** `IsUnboundedScheduler f` is precisely `Monotone f ∧ ∀ i, ∃ t, i < f t`: f is nondecreasing and strictly exceeds each index eventually, without a growth-rate assumption. `schedulerEntryTime f hf i = Nat.find …` selects the least t with `i < f t`, as identified by its exported proof dependency. At sample size t, the clean scan order is the order of `canonicalProcedureStage F (f t)`; the noisy order uses the corresponding noisy stage. Both generators actually use t equal to the cardinality of their deduplicated sample.

Starting with no selected indices, `greedyListScanBy` visits the order list and inserts an index exactly when its acceptance predicate holds. Clean acceptance requires that the whole sample lies in its language **and** that the intersection after insertion is infinite. Noisy acceptance requires the coordinate's noise condition **and** the same infinite-intersection condition. Output is a `freshFromInfinite` choice from the selected intersection minus the observed sample. Empty selected sets have intersection equal to all of α, so an infinite ambient type provides a total fallback. Choice and tests of arbitrary membership, finiteness and infinity are semantic operations here.

The exact bound formulas are
`schedulerTimeVector F f hf i = max (schedulerEntryTime f hf i) (canonicalComplexity F i + 1)`
and the same formula using `canonicalNoisyComplexity F noise i` for the noisy vector. `variantCanonicalTime c i = c i + 1`. `FiniteSublevels c` means `∀ t, {i | c i + 1 ≤ t}.Finite`. It bounds which coordinates have small thresholds; it is not finiteness of the family or a supplied cardinality bound for these sets.

**Scope of computation and histories.** A family indexed by Nat is not assumed effectively enumerated. No coding of α, decidable family membership, computable f, executable fresh-element selector, oracle machine, program-uniformity theorem, query bound or running-time bound is assumed. Named functions use classical choice and semantic tests; an effective or oracle implementation would require extra structure. Threshold “time” counts observations; score “complexity” counts intersection elements or maximal sample elements. There are no output laws, support losses, full-support assumptions, probabilities, or distributional claims: every conclusion concerns a single output.

No presentation completeness or coverage requirement appears. General generators can depend on history order; the named scheduler generators factor through its finite set. Outputs are not automatically appended to subsequent histories, so freshness does not ensure distinct outputs across separate calls unless earlier outputs occur in the later observations.

## Six target dossiers

### GenLimit.ParetoGeneration.Results.theorem_1

Source anchor (exported locator): `GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean:35`.

Exact original printed type:

```lean
∀ {α : Type u_1} [Infinite.{u_1 + 1} α] (F : Nat → Set.{u_1} α) (stage : Nat),
  ∃ G time,
    And (GenLimit.ParetoGeneration.AchievesTimeVector.{u_1} G F time)
      (And (GenLimit.ParetoGeneration.PositiveTimeVector time)
        (And
          (GenLimit.ParetoGeneration.MatchesPrefix stage time fun i =>
            HAdd.hAdd.{0, 0, 0}
              (GenLimit.ParetoGeneration.ProcedureStage.complexity.{u_1}
                (GenLimit.ParetoGeneration.canonicalProcedureStage.{u_1} F stage) i)
              1)
          (GenLimit.ParetoGeneration.PrefixParetoOptimal stage (GenLimit.ParetoGeneration.RealizableTimeVectors.{u_1} F)
            time)))
```

For every type α with an `Infinite α` instance, every indexed family F, and every natural stage, there exist a generator G and a whole time vector time such that all four components hold: clean achievement on the whole family; positivity at every coordinate; exact equality, below stage, with that stage's complexity plus one; and prefix optimality against all realizable whole vectors.

**Quantifier skeleton.** `∀ {α} [Infinite α] F stage, ∃ G : HistoryGenerator α, ∃ time : TimeVector, AchievesTimeVector G F time ∧ (∀ i, 1 ≤ time i) ∧ (∀ i < stage, time i = (canonicalProcedureStage F stage).complexity i + 1) ∧ (∀ s ∈ RealizableTimeVectors F, (∃ i < stage, s i < time i) → ∃ j < stage, time j < s j)`.

G and time are chosen after F and stage and before all coordinates, lengths and histories. G has the general finite-history signature; F and stage may determine its choice, but the active target index is not given during generation. Each comparison vector has its own existentially permitted generator, also serving its whole family. There is no requirement that a competitor be no worse on the suffix, nor any suffix matching promise for time. This proves a prefix tradeoff, not global optimality for time.

**Edges.** At stage zero both prefix conditions are vacuous, while global achievement and positivity remain. No finite-sublevels premise, language infinitude, distinctness of family entries, or computability premise is present. The witness is unspecified: this target does not identify G with a named scheduler generator or give a formula for time outside the prefix.

### GenLimit.ParetoGeneration.Results.theorem_4

Source anchor (exported locator): `GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean:49`.

Exact original printed type:

```lean
∀ {α : Type u_1} [inst : Infinite.{u_1 + 1} α] (F : Nat → Set.{u_1} α) (f : Nat → Nat)
  (hf : GenLimit.ParetoGeneration.IsUnboundedScheduler f),
  And
    (GenLimit.ParetoGeneration.AchievesTimeVector.{u_1} (GenLimit.ParetoGeneration.schedulerGenerator.{u_1} F f) F
      (GenLimit.ParetoGeneration.schedulerTimeVector.{u_1} F f hf))
    (GenLimit.ParetoGeneration.PositiveTimeVector (GenLimit.ParetoGeneration.schedulerTimeVector.{u_1} F f hf))
```

For every infinite ambient type, indexed family F, and scheduler f, a proof hf that f is nondecreasing and unbounded suffices for the **named** `schedulerGenerator F f` to achieve the **named** vector `schedulerTimeVector F f hf`; that vector is also positive. Both conjuncts must be retained.

**Quantifier skeleton.** `∀ {α} [inst : Infinite α] F f (hf : IsUnboundedScheduler f), AchievesTimeVector (schedulerGenerator F f) F T ∧ (∀ i, 1 ≤ T i)`, with `T i = max (min {t | i < f t}) (canonicalComplexity F i + 1)`. Expanded achievement quantifies `∀ i t xs` after these fixed parameters, followed by the threshold, injectivity and clean containment premises, and then both membership and freshness conclusions.

The generator is fixed by F and f and uses their full semantic definitions, deduplicated observations and the canonical stage at `f (card sample)`. It does not take hf or the true coordinate as a generation argument. The proof hf is used by the bound's entry-time definition. The threshold is a maximum, not a sum, asymptotic estimate, or upper bound with an omitted constant. No comparison or optimality conclusion appears.

**Edges.** Entry time can be zero, but the complexity-plus-one term makes T positive. f may have arbitrarily long constant stretches or large jumps; no strict increase at each step is required. Finite sublevels are not assumed. Noninjective histories remain in the generator's domain but have no target-correctness promise under this theorem.

### GenLimit.ParetoGeneration.Results.theorem_5

Source anchor (exported locator): `GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean:59`.

Exact original printed type:

```lean
∀ {α : Type u_1} [Infinite.{u_1 + 1} α] (F : Nat → Set.{u_1} α),
  GenLimit.ParetoGeneration.FiniteSublevels (GenLimit.ParetoGeneration.canonicalComplexity.{u_1} F) →
    ∃ G,
      And
        (GenLimit.ParetoGeneration.AchievesTimeVector.{u_1} G F fun i =>
          HAdd.hAdd.{0, 0, 0} (GenLimit.ParetoGeneration.canonicalComplexity.{u_1} F i) 1)
        (And
          (GenLimit.ParetoGeneration.PositiveTimeVector fun i =>
            HAdd.hAdd.{0, 0, 0} (GenLimit.ParetoGeneration.canonicalComplexity.{u_1} F i) 1)
          (GenLimit.ParetoGeneration.ParetoOptimal (GenLimit.ParetoGeneration.RealizableTimeVectors.{u_1} F) fun i =>
            HAdd.hAdd.{0, 0, 0} (GenLimit.ParetoGeneration.canonicalComplexity.{u_1} F i) 1))
```

For every infinite ambient type and indexed family F, **if** `FiniteSublevels (canonicalComplexity F)`, there exists one generator G achieving the exact vector `b i = canonicalComplexity F i + 1`. The vector is positive, and every realizable competitor that improves any coordinate worsens some coordinate.

**Quantifier skeleton.** `∀ {α} [Infinite α] F, FiniteSublevels c → ∃ G : HistoryGenerator α, AchievesTimeVector G F (fun i => c i + 1) ∧ PositiveTimeVector (fun i => c i + 1) ∧ (∀ s ∈ RealizableTimeVectors F, (∃ i, s i < c i + 1) → ∃ j, c j + 1 < s j)`, where `c = canonicalComplexity F`.

The finite-sublevels hypothesis means exactly `∀ t, {i | c i + 1 ≤ t}.Finite`; it supplies no explicit scheduler, finite-set enumeration, or numerical bound on the number of such indices. G is existential, chosen after F and the hypothesis and before all eligible observations. It can be chosen with knowledge of F; at use it takes only a history. The statement is semantic existence for each admissible family, not an effectively uniform program receiving a representation of F. All three conjunction components remain explicit even though achievement and positivity imply membership in the realizable set.

**Edges.** Unlike target 1, comparison ranges over all coordinates, without a fixed prefix; the worsening coordinate need not be earlier. This still does not give coordinatewise minimality or uniqueness. For threshold zero the sublevel condition is automatically empty; at larger thresholds it can fail, for example when infinitely many coordinates have uniformly bounded canonical complexity. Family indices may repeat; no deduplication of coordinates is required by the type.

### GenLimit.ParetoGeneration.Results.theorem_6

Source anchor (exported locator): `GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean:73`.

Exact original printed type:

```lean
∀ {α : Type u_1} [inst : Infinite.{u_1 + 1} α] (F : Nat → Set.{u_1} α) (noise f : Nat → Nat)
  (hf : GenLimit.ParetoGeneration.IsUnboundedScheduler f),
  And
    (GenLimit.ParetoGeneration.AchievesNoisyTimeVector.{u_1}
      (GenLimit.ParetoGeneration.noisySchedulerGenerator.{u_1} F noise f) F noise
      (GenLimit.ParetoGeneration.noisySchedulerTimeVector.{u_1} F noise f hf))
    (GenLimit.ParetoGeneration.PositiveTimeVector
      (GenLimit.ParetoGeneration.noisySchedulerTimeVector.{u_1} F noise f hf))
```

For every infinite ambient type, F, noise function and scheduler f with hf, the named `noisySchedulerGenerator F noise f` achieves the named noisy time vector, and that vector is positive. This is the noisy analogue of the fixed named construction, with no additional comparison claim.

**Quantifier skeleton.** `∀ {α} [inst : Infinite α] F (noise f : Nat → Nat) (hf : IsUnboundedScheduler f), AchievesNoisyTimeVector (noisySchedulerGenerator F noise f) F noise T ∧ PositiveTimeVector T`, where `T i = max (schedulerEntryTime f hf i) (canonicalNoisyComplexity F noise i + 1)`. Its expanded performance condition is `∀ i t xs, T i ≤ t → Injective xs → card {x ∈ sequenceSample xs | x ∉ F i} ≤ noise i → (G t xs ∈ F i ∧ ∀ k, G t xs ≠ xs k)`.

F, the entire noise function and f determine the generator before coordinate/history quantification. The true coordinate and labels identifying which observations are corrupt are not supplied. The algorithm applies each scanned coordinate's own noise test to the same observed sample. hf determines entry times but is not an argument of the generator. Correct output must avoid all observed elements, rather than only the clean portion.

**Edges.** Noise zero specializes the eligibility premise to clean containment, but the theorem does not assert equality of the noisy and clean named constructions or complexities. Arbitrarily large, nonmonotone coordinate budgets are allowed. No finite-sublevels premise, stochastic contamination law, rate, support condition or presentation completeness is required. As in target 4, repetition violates the performance premise rather than the function's domain.

### GenLimit.ParetoGeneration.Results.theorem_8

Source anchor (exported locator): `GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean:87`.

Exact original printed type:

```lean
∀ {α : Type u_1} [Infinite.{u_1 + 1} α] (F : Nat → Set.{u_1} α) (noise : Nat → Nat),
  GenLimit.ParetoGeneration.FiniteSublevels (GenLimit.ParetoGeneration.canonicalNoisyComplexity.{u_1} F noise) →
    And
      (Membership.mem.{0, 0} (GenLimit.ParetoGeneration.NoisyRealizableTimeVectors.{u_1} F noise)
        (GenLimit.ParetoGeneration.variantCanonicalTime
          (GenLimit.ParetoGeneration.canonicalNoisyComplexity.{u_1} F noise)))
      (GenLimit.ParetoGeneration.ParetoOptimal (GenLimit.ParetoGeneration.NoisyRealizableTimeVectors.{u_1} F noise)
        (GenLimit.ParetoGeneration.variantCanonicalTime
          (GenLimit.ParetoGeneration.canonicalNoisyComplexity.{u_1} F noise)))
```

For every infinite ambient type, F and noise, finite sublevels of `canonicalNoisyComplexity F noise` imply **both** that its plus-one vector belongs to `NoisyRealizableTimeVectors F noise` and that it is optimal relative to that set in the defined comparison sense.

**Quantifier skeleton.** `∀ {α} [Infinite α] F noise, FiniteSublevels c → ((∃ G : HistoryGenerator α, AchievesNoisyTimeVector G F noise b ∧ PositiveTimeVector b) ∧ (∀ s ∈ NoisyRealizableTimeVectors F noise, (∃ i, s i < b i) → ∃ j, b j < s j))`, where `c = canonicalNoisyComplexity F noise` and `b i = c i + 1`.

The outer syntax asserts set membership, not a separately named generator. Unfolding that membership exposes a single existential G and positivity; neither may be omitted. Its witness depends on the fixed family, noise and hypothesis before all coordinate/history quantifiers. Comparisons keep F and noise fixed. Each admissible competitor can have a different generator, but its witness must meet the same noise-budget generation criterion at all coordinates. There is no comparison against clean realizability, a different noise function, or a restricted named-scheduler class.

**Edges.** Finite sublevels concern the noisy score, not the clean score. The conclusion uses the exact plus-one vector without a remaining scheduler-entry penalty. It gives no explicit selected scheduler or computational implementation and no uniqueness or earlier-coordinate conclusion. Positivity follows both by expanding membership and from the plus-one formula; it is not an extra hypothesis.

### GenLimit.ParetoGeneration.Results.theorem_9_representative_endgame

Source anchor (exported locator): `GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean:103`.

Exact original printed type:

```lean
∀ {Achievable : Set.{0} GenLimit.ParetoGeneration.TimeVector}
  {representativeComplexity : GenLimit.ParetoGeneration.TimeVector},
  GenLimit.ParetoGeneration.VariantSchedulerCertificate Achievable representativeComplexity →
    GenLimit.ParetoGeneration.FiniteSublevels representativeComplexity →
      And (Membership.mem.{0, 0} Achievable (GenLimit.ParetoGeneration.variantCanonicalTime representativeComplexity))
        (GenLimit.ParetoGeneration.ParetoOptimal Achievable
          (GenLimit.ParetoGeneration.variantCanonicalTime representativeComplexity))
```

For an arbitrary implicit set `Achievable : Set TimeVector` and implicit `representativeComplexity : TimeVector`, a `VariantSchedulerCertificate` and finite sublevels imply that the plus-one vector belongs to Achievable and is optimal relative to Achievable.

**Quantifier skeleton.** `∀ {A : Set TimeVector} {c : TimeVector}, VariantSchedulerCertificate A c → FiniteSublevels c → (b ∈ A ∧ ∀ s ∈ A, (∃ i, s i < b i) → ∃ j, b j < s j)`, with `b i = c i + 1`. The certificate and finite-sublevels implications precede both conclusions.

The certificate's sole constructor supplies exactly two premises:
1. `∀ (f : Nat → Nat) (hf : IsUnboundedScheduler f), (fun i => max (schedulerEntryTime f hf i) (c i + 1)) ∈ A`.
2. `∀ s ∈ A, ∀ i, s i < c i + 1 → ∃ j, j < i ∧ c j + 1 < s j`.

These are substantial supplied hypotheses: realizability of **every** scheduler-delayed vector and an earlier-coordinate tradeoff for **every** improving coordinate of **every** member of A. The target does not establish the certificate or identify a semantic interpretation for A or c. In particular, the locator's word “representative” provides no construction or equivalence relation.

**Edges and knowledge.** This signature contains no α, language family, noise model or generator. Membership yields a generator only if some separately supplied meaning of A warrants that reading. A need not be assumed upward closed or composed only of positive vectors. The certificate prevents arbitrary bad comparison behavior, while finite sublevels provide the additional premise for exact membership. The claimed b is positive by arithmetic, but positivity is not an explicit third conclusion. No theorem about robustness, representatives, or effective learning can be inferred from the name alone.

## Exhaustive coverage table

| Target (namespace P.Results) | Parameters and hypotheses | Required conclusion components | Comparison domain / witness status |
|---|---|---|---|
| `theorem_1` | implicit α, infinite instance; F, stage | ∃ G and whole time: achievement; positivity; exact prefix; prefix tradeoff | All clean realizable vectors; G/time unspecified and jointly chosen |
| `theorem_4` | implicit α, named infinite instance; F, f, hf | Named clean generator achieves named maximum-bound vector; positivity | No optimization claim; generator fixed by F/f |
| `theorem_5` | implicit α, infinite instance; F; finite sublevels of clean c | ∃ G: achievement at c+1; positivity; global tradeoff | All clean realizable vectors; exact time fixed, G unspecified |
| `theorem_6` | implicit α, named infinite instance; F, noise, f, hf | Named noisy generator achieves named maximum-bound vector; positivity | No optimization claim; fixed F/noise/f |
| `theorem_8` | implicit α, infinite instance; F, noise; finite sublevels of noisy c | Membership of c+1; global tradeoff | All noisy realizable vectors for the same F/noise; membership includes ∃ G and positivity |
| `theorem_9_representative_endgame` | implicit A/c; two-part scheduler certificate; finite sublevels | Membership of c+1; global tradeoff | Arbitrary A; no generator interpretation supplied |

## Shared finite, empty and degenerate cases

The infinite-type assumptions concern α alone. No target requires each F i to be infinite or even nonempty. For a finite target with m elements, an injective clean history has length at most m; a history containing all m exhausts every possible fresh correct output. Thus a successful positive time threshold must put such exhausted histories below the threshold, and at larger lengths the containment/injectivity premises may be impossible. An empty clean target has no eligible positive-length histories, so its positive-threshold obligation is vacuous.

For a finite target with m elements and budget q, an eligible noisy injective sample has at most m+q elements. In an infinite ambient type one can include all m target elements and q outsiders; at that exhausted history no fresh target output exists. A threshold above m+q therefore makes the obligation vacuous. These finite cases must not be read as guarantees of indefinitely many outputs from a finite language. For an infinite target, finite observations do leave unseen target elements, though simultaneous compatibility across candidate coordinates is the construction's separate concern.

Repeated family entries are permitted; coordinates and their noise/threshold data still remain separate. The selected index sets do not contain repeated indices, and stage orders permute a range, so they contain each active index once. Empty intersections can be finite candidates of score zero; an empty *index* witness cannot be a candidate containing its target. With no selected coordinates the intersection is the entire ambient type. Positive target thresholds exclude t=0 performance obligations even though generators are defined there. No arbitrary finite prefix of a history must extend to a complete target enumeration for the theorem to apply.

## Validation and limits

Validation checked the six-target census, the 130-record export, original checksum manifest, internal project-dependency closure, exact signature inclusion and the two report formats. It did not run Lean or Lake, inspect theorem proofs, inspect source files named by anchors, consult a paper, check paper/source correspondence, or obtain human certification. No library, frozen input or Git state was changed. Only the two requested result files were written.

The configuration supplied for this isolated worker invocation is `gpt-6.1-sol`, reasoning effort `xhigh`, `fork_turns=none`. Backend revision is not exposed; this report does not independently attest the serving backend. There is no unresolved project-definition dependency at the exported-name level. Remaining limits are the declared standard-library boundary, suppressed embedded proof details, unspecified classical witnesses, and the absence of any supplied computational representation. Both outputs are frozen by their final SHA256 values; the JSON records the Markdown hash, and the JSON's own hash is reported externally to avoid a self-reference.
