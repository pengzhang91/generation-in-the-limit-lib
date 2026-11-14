# P19 — code-only reconstruction, Stage 1

## Input census and scope

This reconstructs exactly four target declarations and their 34 exported project definitions (38 unique exports), using only this package's `stage1/`. Both manifests passed byte verification: 11 entries in `stage1/SHA256SUMS`, and two in `stage1/explicit-target-types/SHA256SUMS`. Their SHA256 values are respectively `0da3ca3ab527edccf4f3aaf57a36a5df0575730720e51b8d579a9459ebee088f` and `d77fc6be16b1b1e9d99a33cc17e6b27ab774651375964a721b87d8a3dfa736d6`.

The 15 input files are those manifests; `START_HERE.md`, `PROMPT.md`, `targets.txt`, `01-target-statements.md`, `02-definition-dependencies.md`, `declarations.jsonl`, `external-constant-boundary.txt`, `snapshot.json`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`; and the supplement's `README.md` and `types.jsonl`. Individual hashes are in the run record. The two statement presentations agree; all project dependency names resolve within the 38 exports, and all 52 external dependency names occur in the declared boundary. Snapshot paths and identifiers serve only as anchors. The recorded snapshot is a dirty working-tree byte snapshot, not a claim that the named revision alone reproduces it.

Original printed signatures appear unchanged below. The explicit supplement disambiguates suppressed type arguments: every separation class is a `LanguageClass PaperColumnPoint`, and the exported definition of `PaperColumnPoint` is `Nat × Nat`. These classes are not on the polymorphic outer universe of the other assertions. No theorem proof value was supplied or inspected.

## Definition glossary

Write `G`, `Q`, and `S` for the namespaces `GenLimit.Generic`, `GenLimit.QuantifyingNoise`, and `GenLimit.Support`. These are abbreviations only.

**Objects and information.** `G.Language α = Set α`; `G.LanguageClass α = Set (Set α)`; `G.Stream α = Nat → α`. `G.FiniteHistoryOperator Input Output` is `(n : Nat) → (Fin n → Input) → Output`, and `G.Generator α` specializes both types to `α`. Thus a generator returns one point from an ordered, indexed finite history and its length. It is an arbitrary total mathematical function, with no computability requirement. Its type supplies no target membership oracle, class representation, target index, noise labels, or noise-bound argument. A witness can be selected for the class and, in fixed-level predicates, its noise bound. Countability of the point type supplies no executable encoding or enumeration to this function; the class itself need not be countable.

`G.sample s n` is the image of `Finset.range n` under `s`, hence the finite set of values at indices strictly below `n`. `Q.observed s t = G.sample s (t+1)`. `Q.outputAt g s t = g (t+1) (fun k : Fin (t+1) => s k.val)`. Define

`P(g,L,s,t) :⇔ outputAt g s t ∈ L ∧ outputAt g s t ∉ observed s t`.

This is exactly `Q.CorrectAt`: both target membership and input freshness are required. Time zero already includes `s 0`; time `t` sees `t+1` inputs. The generator's length-zero behavior is unused here. Freshness excludes every observed input, including contamination. It does not explicitly exclude earlier generated outputs.

**Contamination and admissibility.** `G.SetDifferenceAtMost A B i` is `∃ F : Finset α, (↑F : Set α) = A \ B ∧ F.card ≤ i`. The hidden witness domain follows from `Finset.card` and its exported type, not its name. `S.MissingAtMost` and then `Q.MissingAtMost` are aliases of this predicate: their orientation is `A \ B`, not `B \ A`. `G.ValuesOutsideAtMost s L i` substitutes `A = Set.range s`, `B = L`.

Both `Q.EnumerationWithNoiseAtMost` and `S.EnumerationWithNoiseAtMost` reduce to `G.InjectiveValueContaminatedPresentationAtMost`. Write their common predicate as

`A_i(s,L) :⇔ Function.Injective s ∧ L ⊆ Set.range s ∧ ∃ F : Finset α, ↑F = Set.range s \ L ∧ F.card ≤ i`.

It requires no repeated stream value, coverage of every target point sometime, and at most `i` distinct extraneous values over the entire stream. The primary budget counts values, not occurrences. Injectivity makes their counts coincide on these admissible streams; arbitrary repeated streams remain inadmissible. There is no bound on when target points or noise arrive, no tolerated omitted target points, and no probabilistic law or support-loss notion. At level zero the range equals `L`.

**Thresholds and generator witnesses.** Use the following complete expansions; every unmarked threshold, noise bound, and time is a natural number, `L : Set α`, and `s : Nat → α`:

```text
U_i(C)  := ∃ g : G.Generator α, ∃ T, ∀ L, L ∈ C →
             ∀ s, A_i(s,L) → ∀ t, T ≤ t → P(g,L,s,t).
N_i(C)  := ∃ g : G.Generator α, ∀ L, L ∈ C → ∃ T,
             ∀ s, A_i(s,L) → ∀ t, T ≤ t → P(g,L,s,t).
UD(C)   := ∃ g : G.Generator α, ∀ i, ∃ T, ∀ L, L ∈ C →
             ∀ s, A_i(s,L) → ∀ t, T ≤ t → P(g,L,s,t).
ND(C)   := ∃ g : G.Generator α, ∀ i, ∀ L, L ∈ C → ∃ T,
             ∀ s, A_i(s,L) → ∀ t, T ≤ t → P(g,L,s,t).
```

`G.IsUniformEventuallyCorrect` supplies the `∃ T` before the target; `G.IsTargetwiseEventuallyCorrect` supplies it after the target. `Q.IsUniformGeneratorAtNoiseLevel` and `Q.IsNonuniformGeneratorAtNoiseLevel` instantiate these with `CorrectAt` and `A_i`, leaving `g` fixed. Their `...GeneratableAtNoiseLevel` predicates existentially quantify `g`, giving `U_i` and `N_i`. The two `Is...NoiseDependentGenerator` predicates universally quantify `i` for a fixed `g`; the two `...NoiseDependentGeneratable` predicates put `∃ g` outside that quantifier, giving `UD` and `ND`.

For fixed-level predicates, `g` can depend on `C,i`, but never on the particular target or stream. Uniform `T` can depend on that choice and `C,i`; nonuniform `T` can additionally depend on `L`. In `UD` and `ND`, one `g` serves every finite noise bound without receiving the bound as input. Thresholds may depend on `i`; in `ND` also on `L`. All thresholds precede the stream. These are eventual, all-times-after-threshold assertions, with no explicit numerical rate, stopping algorithm, last-noise-relative clock, or stream-dependent waiting time.

**Closure and exhaustion.** `Q.AllLanguagesInfinite C` is `∀ L, L ∈ C → Set.Infinite L`. Define `K_i(C,S) = {L | L ∈ C ∧ MissingAtMost S L i}`; this is `Q.consistentLanguages`. For finite observations it permits at most `i` observed values outside a candidate language, without requiring that the observations already cover it. `Q.noisyCommonCore C S i` consists of points in every member of `K_i(C,S)`. `Q.noisyClosure C S i` equals that core when `K_i(C,S)` is nonempty, and equals `∅` otherwise. This conditional matters: the common core alone would be the whole universe when there are no candidates.

`Q.NoisyClosureWitnessAt C i d` is

`∃ S : Finset α, S.card = d ∧ K_i(C,↑S).Nonempty ∧ (noisyClosure C ↑S i).Finite`.

The domain of `S` is forced by the cardinality function and coercion. A finite closure may be empty; the consistent family may not. Write `F_i(C)` for `Q.FiniteNoisyClosureDimensionAt C i`, exactly `∃ B : Nat, ∀ d : Nat, B < d → ¬NoisyClosureWitnessAt C i d`. The bound need not be least, positive, or accompanied by a witness at the bound. This is a cardinality cutoff, not a time bound.

Write `E_i(C)` for `Q.HasFiniteDimensionExhaustionAt C i`, exactly

`∃ layers : Nat → G.LanguageClass α, Monotone layers ∧ C = ⋃ j, layers j ∧ ∀ j, F_i(layers j)`.

The domain of `layers` follows from the exported class-valued functions and union. Monotonicity uses inclusion of classes: `j ≤ k → layers j ⊆ layers k`. Every layer lies in `C`, and every target belongs to some layer. Layers need not be finite, strictly increasing, effectively given, or countable as sets of languages. Repetitions are allowed. Each layer has its own existential bound; no uniform bound across layers is asserted.

## Dossier 1: `GenLimit.QuantifyingNoise.Results.theorem_2_16`

Source anchor: `GenLimitLean/GenLimit/Paper19_EffectOfNoise/Results/Overview.lean:39`. Exact original exported type:

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] [Nonempty.{u_1 + 1} α] {C : GenLimit.Generic.LanguageClass.{u_1} α},
  GenLimit.QuantifyingNoise.AllLanguagesInfinite.{u_1} C →
    ∀ {i : Nat},
      LE.le.{0} 1 i →
        And
          (Iff (GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel.{u_1} C i)
            (GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel.{u_1} C 1))
          (Iff (GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel.{u_1} C i)
            (GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel.{u_1} C 1))
```

For every countable nonempty point type `α`, every class `C` all of whose members are infinite, and each natural `i ≥ 1`, uniform generation at level `i` is equivalent to uniform generation at level one; separately, nonuniform generation at level `i` is equivalent to nonuniform generation at level one. The two equivalences form a conjunction. Neither equates uniform with nonuniform generation.

Quantifier skeleton, with the glossary giving every inner binder:

`∀ {α} [Countable α] [Nonempty α] {C}, (∀ L∈C, Infinite L) → ∀ {i : Nat}, 1 ≤ i → ((U_i(C) ↔ U_1(C)) ∧ (N_i(C) ↔ N_1(C)))`.

Information and dependencies: each fixed-level existence chooses its own whole-history function for `C,i`; the equivalences do not say that witnesses on either side are identical, supply a named generator, or directly assert one generator for all levels. Uniform thresholds range over every target and admissible ordering; nonuniform thresholds vary with the target, still preceding the stream. No noise value or target identity is supplied at invocation.

Edges: `i=1` is included; `i=0` is excluded. Empty `C` satisfies the infinitude hypothesis vacuously, and both generation predicates then impose no correctness obligation. For finite `α`, that hypothesis forces `C` empty. The statement has no separate infinitude assumption on `α`, no bound on the number of languages, and no claimed rate relating the level-one and level-`i` thresholds.

## Dossier 2: `GenLimit.QuantifyingNoise.Results.theorem_2_17`

Source anchor: `GenLimitLean/GenLimit/Paper19_EffectOfNoise/Results/Overview.lean:53`. Exact original exported type:

```lean
∃ C,
  And (GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel.{0} C 0)
    (Not (GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel.{0} C 1))
```

There exists a class `C : Set (Set (Nat × Nat))` admitting uniform level-zero generation but admitting no nonuniform level-one generator. The same existential class occurs in both conjuncts. The explicit applications to `PaperColumnPoint`, together with `PaperColumnPoint = Nat × Nat`, determine this domain; the original suppressed binder alone would not display it.

Quantifier skeleton:

`∃ C : G.LanguageClass (Nat × Nat), (∃ g, ∃ T, ∀ L∈C, ∀ s, A_0(s,L) → ∀ t≥T, P(g,L,s,t)) ∧ ¬(∃ h, ∀ L∈C, ∃ R, ∀ s, A_1(s,L) → ∀ t≥R, P(h,L,s,t))`.

Information: the positive function is selected for the whole witness class, with no target argument. Its one threshold covers every noiseless injective exhaustive stream of every target in the class. The negative conjunct ranges over arbitrary total functions of the generator type, not merely computable procedures or functions receiving inadequate oracle access.

Classically, the negative conjunct means that for each proposed `h` there is a target `L∈C` such that for every threshold `R` there is an admissible level-one stream and a time `t≥R` at which either target membership or freshness fails. That stream may depend on `R`; the type does not require one fixed stream witnessing infinitely many errors. The failed target may depend on `h`.

Edges: there is no `AllLanguagesInfinite C` conjunct, no explicit description of its languages, and no relationship to an outside class. The negative conjunct rules out an empty witness class. Finite targets have no admissible injective exhaustive stream with a finite global contamination bound, so their individual correctness obligations are vacuous; the type does not exclude their membership. No theorem-level target naming or algorithm is extracted from existential existence.

## Dossier 3: `GenLimit.QuantifyingNoise.Results.theorem_2_18`

Source anchor: `GenLimitLean/GenLimit/Paper19_EffectOfNoise/Results/Overview.lean:62`. Exact original exported type:

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] [Nonempty.{u_1 + 1} α] {C : GenLimit.Generic.LanguageClass.{u_1} α},
  GenLimit.QuantifyingNoise.AllLanguagesInfinite.{u_1} C →
    And
      (And
        (Iff (GenLimit.QuantifyingNoise.FiniteNoisyClosureDimensionAt.{u_1} C 1)
          (∀ (i : Nat), LE.le.{0} 1 i → GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel.{u_1} C i))
        (Iff (GenLimit.QuantifyingNoise.FiniteNoisyClosureDimensionAt.{u_1} C 1)
          (GenLimit.QuantifyingNoise.UniformNoiseDependentGeneratable.{u_1} C)))
      (∃ D,
        And (GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel.{0} D 0)
          (Not (GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel.{0} D 1)))
```

For every countable nonempty `α` and class `C` of infinite languages, the result is a conjunction of two equivalences and a separate separation assertion. First, `F_1(C)` is equivalent to fixed-level uniform generation for every positive noise bound. Second, that same `F_1(C)` is equivalent to existence of one generator working uniformly at every natural noise bound. Finally there exists `D : G.LanguageClass (Nat × Nat)` with uniform level-zero generation and no uniform level-one generation.

Quantifier skeleton:

`∀ {α} [Countable α] [Nonempty α] {C}, AllLanguagesInfinite C → (((F_1(C) ↔ ∀ i : Nat, 1 ≤ i → U_i(C)) ∧ (F_1(C) ↔ UD(C))) ∧ ∃ D : G.LanguageClass (Nat × Nat), U_0(D) ∧ ¬U_1(D))`.

The first right side has order `∀ i≥1, ∃ g_i, ∃ T_i, ...`. The second has `∃ g, ∀ i : Nat, ∃ T_i, ...`, including zero. The theorem equates each with the closure condition, while preserving their different witness orders. A dimension witness `B` is shared across all sample cardinalities at level one; it is neither a generator threshold nor a promised computable constant. Uniform thresholds never depend on the particular target or stream. The learner sees only its indexed prefix.

The separation domain remains the fixed product type even when outer `α` has another universe. Its existential binder lies syntactically inside the outer assumptions, so dependence on those parameters is permitted; no relationship to `C` is specified. The two positive and negative occurrences refer to the same `D`; no identity with the witness in another target is asserted. There is no infinitude conjunct for `D`.

Edges: empty `C` has no nonempty consistent family, hence no closure witnesses, so `F_1(C)` holds (for example with bound zero); uniform generation is vacuous. Samples with no consistent language are excluded from dimension witnesses despite having empty closure. For the separation, classically `¬U_1(D)` says `∀ g, ∀ T, ∃ L∈D, ∃ s, A_1(s,L) ∧ ∃ t≥T, ¬P(g,L,s,t)`. Here the failing target can vary with `T`, unlike nonuniform failure. The assertion does not make noiseless uniform generation sufficient for the closure condition.

## Dossier 4: `GenLimit.QuantifyingNoise.Results.theorem_2_19`

Source anchor: `GenLimitLean/GenLimit/Paper19_EffectOfNoise/Results/Overview.lean:80`. Exact original exported type:

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] [Nonempty.{u_1 + 1} α] {C : GenLimit.Generic.LanguageClass.{u_1} α},
  GenLimit.QuantifyingNoise.AllLanguagesInfinite.{u_1} C →
    And
      (And
        (Iff (GenLimit.QuantifyingNoise.HasFiniteDimensionExhaustionAt.{u_1} C 1)
          (∀ (i : Nat), LE.le.{0} 1 i → GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel.{u_1} C i))
        (Iff (GenLimit.QuantifyingNoise.HasFiniteDimensionExhaustionAt.{u_1} C 1)
          (GenLimit.QuantifyingNoise.NonuniformNoiseDependentGeneratable.{u_1} C)))
      (∃ D,
        And (GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel.{0} D 0)
          (Not (GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel.{0} D 1)))
```

For every countable nonempty `α` and class `C` consisting of infinite languages, an increasing countable exhaustion by classes each having finite level-one noisy closure dimension is equivalent to nonuniform generation at every positive noise bound. The same exhaustion condition is also equivalent to one generator satisfying nonuniform correctness at every natural noise bound. A further conjunct gives `D : G.LanguageClass (Nat × Nat)` with nonuniform level-zero generation and no nonuniform level-one generation.

Quantifier skeleton:

`∀ {α} [Countable α] [Nonempty α] {C}, AllLanguagesInfinite C → (((E_1(C) ↔ ∀ i : Nat, 1 ≤ i → N_i(C)) ∧ (E_1(C) ↔ ND(C))) ∧ ∃ D : G.LanguageClass (Nat × Nat), N_0(D) ∧ ¬N_1(D))`.

Expanded dependencies are essential. The exhaustion side is `∃ layers, Monotone layers ∧ C=⋃j layers j ∧ ∀ j, ∃ B_j, ∀ d>B_j, ¬Witness(layers j,1,d)`. The first generation side is `∀ i≥1, ∃ g_i, ∀ L∈C, ∃ T_(i,L), ∀ s, ...`. The second is `∃ g, ∀ i : Nat, ∀ L∈C, ∃ T_(i,L), ∀ s, ...`. Each equivalence uses precisely the full exhaustion condition, including both monotonicity and equality of the union with `C`.

Information: no layer index, layer membership proof, target identity, or noise bound is an argument to the common generator. Layer bounds and targetwise thresholds are semantic witnesses, without an asserted effective dependence. Nonuniformity changes the threshold order, not the choice of one generator per target: even at a fixed level the same generator must serve the entire class.

Edges: repeated or empty layers are permitted; an empty class has the constant-empty exhaustion and vacuous generation predicates. No finite bound uniform in `j` is required. The separation class is on `Nat × Nat`, has no asserted infinitude condition, and is not identified with outer `C` or any other theorem's witness. Its binder remains under the outer hypotheses. The positive threshold may depend on its target but precedes every admissible level-zero ordering. Its negative conjunct has the same fixed-target-per-generator, varying-stream-per-threshold interpretation as in target 2.17. No single stream with infinitely many failures is claimed.

## External boundary and limits

Standard Lean/Mathlib meanings are assumed for the boundary's logic and equality, naturals and arithmetic/order instances, `Fin`/`Fin.val`, finite sets/cardinality/image/range/coercion, sets and membership/difference/range/finiteness/infinitude/nonemptiness, inclusion and indexed union with the supplied lattice instances, injectivity, monotonicity, products, `Countable`, `Nonempty`, and classical proposition decidability for the closure conditional. The supplied metadata pins Lean 4.24.0 and Mathlib input tag `v4.24.0`, resolved revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; these files were read, not compiled or fetched.

No decisive project definition is missing for statement reconstruction. Standard-library bodies were not recursively inspected. Proof correctness, current-source correspondence, intended paper semantics, executable realizability, fresh compilation, and human certification remain outside this stage. No paper, source beyond the interface, other package, prior result, or later-stage material supplied mathematical evidence. Only the two newly generated outputs are reopened for structural and hash validation.

## Exhaustive export coverage

The prefixes `G`, `Q`, and `S` have the exact expansions given in the glossary; `Q.Results` is `GenLimit.QuantifyingNoise.Results`. Every exported declaration appears once below. Dependency rows refer to the glossary, and target rows to their complete dossiers.

| # | Exported identifier (prefix-expanded) | Reconstruction coverage |
|---|---|---|
| 1 | `G.FiniteHistoryOperator` | Indexed total finite-history function; objects/information. |
| 2 | `G.Generator` | Same input/output point type; objects/information. |
| 3 | `G.InjectiveValueContaminatedPresentationAtMost` | All three admissibility conjuncts. |
| 4 | `G.IsTargetwiseEventuallyCorrect` | Threshold follows target and precedes stream. |
| 5 | `G.IsUniformEventuallyCorrect` | Threshold precedes target and stream. |
| 6 | `G.Language` | Set of points. |
| 7 | `G.LanguageClass` | Set of languages; no class-countability premise. |
| 8 | `G.SetDifferenceAtMost` | Exact finite-set witness and cardinal bound. |
| 9 | `G.Stream` | Total natural-indexed stream. |
| 10 | `G.ValuesOutsideAtMost` | Range-minus-target orientation. |
| 11 | `G.sample` | Finite image of indices below length. |
| 12 | `Q.AllLanguagesInfinite` | Memberwise infinitude; empty-class vacuity. |
| 13 | `Q.CorrectAt` | Target membership and input freshness. |
| 14 | `Q.EnumerationWithNoiseAtMost` | Alias chain to injective covered presentation. |
| 15 | `Q.FiniteNoisyClosureDimensionAt` | Natural cutoff with strict inequality. |
| 16 | `Q.HasFiniteDimensionExhaustionAt` | Increasing layers, exact union, each bound. |
| 17 | `Q.IsNonuniformGeneratorAtNoiseLevel` | Fixed generator; targetwise threshold. |
| 18 | `Q.IsNonuniformNoiseDependentGenerator` | Fixed generator outside all noise bounds. |
| 19 | `Q.IsUniformGeneratorAtNoiseLevel` | Fixed generator; class-wide threshold. |
| 20 | `Q.IsUniformNoiseDependentGenerator` | Fixed generator outside all noise bounds. |
| 21 | `Q.MissingAtMost` | Alias chain; observed-minus-candidate. |
| 22 | `Q.NoisyClosureWitnessAt` | Finite sample; cardinality; nonempty family; finite closure. |
| 23 | `Q.NonuniformGeneratableAtNoiseLevel` | Existential generator in N_i. |
| 24 | `Q.NonuniformNoiseDependentGeneratable` | Existential common generator in ND. |
| 25 | `Q.PaperColumnPoint` | Exact value Nat × Nat; all separation domains. |
| 26 | `Q.UniformGeneratableAtNoiseLevel` | Existential generator in U_i. |
| 27 | `Q.UniformNoiseDependentGeneratable` | Existential common generator in UD. |
| 28 | `Q.consistentLanguages` | Class membership and finite missing-at-most condition. |
| 29 | `Q.noisyClosure` | Conditional common core; empty-family branch. |
| 30 | `Q.noisyCommonCore` | Universal membership over consistent candidates. |
| 31 | `Q.observed` | Sample at t+1. |
| 32 | `Q.outputAt` | Generator applied to length-t+1 indexed prefix. |
| 33 | `S.EnumerationWithNoiseAtMost` | Alias to generic admissibility. |
| 34 | `S.MissingAtMost` | Alias to generic set difference budget. |
| 35 | `Q.Results.theorem_2_16` | Dossier 1: both positive-level equivalences. |
| 36 | `Q.Results.theorem_2_17` | Dossier 2: uniform-zero / nonuniform-one separation. |
| 37 | `Q.Results.theorem_2_18` | Dossier 3: two equivalences and uniform separation. |
| 38 | `Q.Results.theorem_2_19` | Dossier 4: two equivalences and nonuniform separation. |
