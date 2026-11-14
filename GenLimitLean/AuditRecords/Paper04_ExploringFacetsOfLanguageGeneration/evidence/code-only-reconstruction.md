# Stage 1: reconstruction from exported Lean interfaces

This report reconstructs exactly seven declarations from the supplied types and statement-relevant definition values. It does not assess proof correctness or agreement with any paper. Identifiers and source paths below are evidence locators, not evidence of intended meaning. All mathematical descriptions use the actual exported predicates.

## Input census and boundary

The only input directory was `stage1/` of this package. `declarations.jsonl` contains 88 declarations: 74 definitions, three inductive types, three constructors, and eight theorem types. Seven theorem types are targets; the eighth is the statement of the nonemptiness fact used by `greedyGenerator`. Thus 81 exports support the seven targets. No theorem proof values or source docstrings were supplied or inspected. The Markdown exports and JSON were used together; the latter also identifies dependencies hidden by pretty-printing, such as the `Finset` type of the witness in `WeakAngluinExistence`.

The 11 entries in `SHA256SUMS` match the actual bytes. The census includes that manifest itself as a twelfth input. Every `GenLimit.*` name listed in exported type/value dependencies is present among the 88 declarations. This establishes closure of those disclosed dependency lists, not an independent verification of the exporter. Source anchors refer to the captured source metadata; the original source files were not opened.

| Input | Bytes | SHA256 |
|---|---:|---|
| `stage1/01-target-statements.md` | 3369 | `0c9b21628166e51148758cc63df73cf6d6bfab4d9ceaf43ac583422494559859` |
| `stage1/02-definition-dependencies.md` | 41485 | `55ce53def024a47591f9e9aaa22b2247d2092118e4941922e21e3cbf40989372` |
| `stage1/PROMPT.md` | 1827 | `d79a9f3221e3fdc6cdb3835026d91ba49ca51b6fade5f30a27d10c5aba9eed4e` |
| `stage1/SHA256SUMS` | 928 | `d72c10f1bec01014937e765df8f6e92915b78685f79642afd19d24fa7f9c4fd9` |
| `stage1/START_HERE.md` | 189 | `af3a15fdcbff088f59d8ac373e92f0d0d546eca1aee13d3c51be7593e78ee86a` |
| `stage1/declarations.jsonl` | 73995 | `0aae3b6f2968fd9b920ab095c1d81183ad86ab3a9c4bdecdc2505c2b810189dc` |
| `stage1/external-constant-boundary.txt` | 1388 | `02e566ee6d202057c369c2d1fcc3080b2fb6cdc93b01ab6e809d17a133220208` |
| `stage1/lake-manifest.json` | 3100 | `994d8b6a379cea0e626d27fe8fa2fc74a2d966197a6998ecde6bd419634991aa` |
| `stage1/lakefile.toml` | 379 | `0fef48c5e314b7476f09da4caa5615d58a50937752aea1b192c0921a05b6e3d0` |
| `stage1/lean-toolchain` | 25 | `42779d67b81608af8a12aa4328d2ab47ca201925b3b2bd68369587b5340bb434` |
| `stage1/snapshot.json` | 14856 | `09dc04ad95ec4bb304d30031d8aa9aaac75b5d27d1e1098584a3ae1629f86f3a` |
| `stage1/targets.txt` | 315 | `c67a298e85e22edab33706260753ccff9d2ab70052aa700aff33f24a230524ca` |

The copied environment records Lean `v4.24.0`, Mathlib input revision `v4.24.0`, and locked Mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. `snapshot.json` labels the capture a dirty current-working-tree byte snapshot at `2026-11-10T05:06:30.317296+00:00`, with recorded Git head `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`; these are supplied metadata, not independently checked Git facts. No Git command, compilation, or fresh proof audit was performed.

Standard Lean/Mathlib meanings are the disclosed external boundary, including sets, finite sets, infinitude/countability, strict subset, classical choice, `Computable`, and `Language.IsRegular`. No external bodies were fetched. In particular, regularity has its standard finite-automaton meaning for languages of Boolean words, while `Computable` concerns the ordinary encoded finite-data function explicitly bearing that predicate. No conclusion below silently adds computability to other function types. Elided embedded proof terms `⋯` are treated as export elisions, not proof holes.

## Definition glossary and observation models

**Base data.** `Generic.Language α = Set α`, a class is a set of languages, and a family is a total map `Nat → Set α`. A family can repeat the same language at different indices. Its range forgets order and repetitions. `UUS H` means exactly `∀ L ∈ H, Set.Infinite L`; it does not assert decidable membership, a computable enumeration, or uniform effective access. `Infinite α` and `Countable α` are typeclass assumptions about the universe, not supplied algorithms.

A stream is a total `s : Nat → α`. `Presents s L` means `range s = L`; `StreamIn s L` means only `range s ⊆ L`. The former requires all target elements to occur eventually, without a deadline; both allow arbitrarily many repetitions. Write `S_t = {s(0), …, s(t−1)}` for `sample s t`. It is a finite set, so its cardinal counts distinct observations, not elapsed time; `S_0 = ∅`.

**Prefix generation.** A `FiniteHistoryOperator Input Output` has type `(t : Nat) → (Fin t → Input) → Output`. A `Generator α` returns one element of `α` from the entire ordered length-`t` prefix. Its `output G s t` uses only positions strictly below `t`. `CorrectAt G L s t` is the conjunction `output ∈ L` and `output ∉ S_t`. Novelty is relative to observed input, not to earlier generated outputs. Such a function may repeat its own outputs. It has no target index, oracle answer, or future stream input in its runtime arguments. It can depend on a fixed class/family through its mathematical definition. The function type alone states semantic totality, not ordinary computation.

`IsNonuniformGenerator G C` is `∀ i, ∃ d, ∀ s, Presents s (C i) → ∀ t, d ≤ |S_t| → CorrectAt G (C i) s t`; `NonuniformlyGeneratable C` places `∃ G` outside this formula. The generator is shared across the family; the threshold can depend on its index and the fixed family, but not on the presentation or time.

**The named prefix generator and its finite-intersection scale.** `familyIntersection C J = {x | ∀ j ∈ J, x ∈ C j}`; for empty `J` this is the whole universe. `selectedIndices C S 0 = ∅`. At step `n+1`, it adds index `n` precisely when `S ⊆ C n` and intersecting that candidate with all previously retained languages remains infinite; otherwise it keeps the old indices. Thus stage `t` examines indices `0,…,t−1`, retaining a compatible subcollection greedily, not necessarily every language containing `S`. `greedyCore C S t` is their intersection.

`greedyGenerator C t xs` uses classical choice from `greedyCore C (sequenceSample xs) t \ sequenceSample xs`. The displayed value elides the proof argument, but its dependency `greedyGenerator._proof_1` states exactly the nonemptiness of this set for every finite prefix on an infinite universe. This identifies the chosen set without inspecting a proof. It supplies no computable choice or effective test for infinitude.

For index `i`, `nonuniformComplexity C i` is the finite maximum over `J ⊆ {0,…,i}` of `|⋂_{j∈J} C j|` when `i ∈ J` and that intersection is finite, and `0` otherwise. The exported formula uses `Finset.sup` and `Set.ncard` under the finite-set guard. If no such finite intersection contributes, the value is `0`. This is a natural-number scale attached to the indexed presentation, not a computed running-time bound or a closure-dimension invariant of the range alone.

**Exhaustive generation.** `ExhaustiveAlgorithm α` is a prefix operator returning a sequence `Nat → α`. At stage `t`, put `E_t = range (A t prefix_t)`. Its distinguished single output is sequence position `0`. `generatedBefore A s t`, written `B_t`, contains just these distinguished outputs from stages `s < t`; it does not union the earlier infinite ranges. Therefore `B_t` is finite. `ExhaustiveCorrectAt A K s t` has both conjuncts:

1. `E_t \ K` is finite;
2. `K ⊆ S_t ∪ B_t ∪ E_t`.

Equivalently, the current sequence covers the target outside the finite set already observed or singly generated, and has only finitely many distinct out-of-target values. It is a condition on its range, not on the frequency of erroneous sequence positions. It imposes no uniform finite-error bound, no ordering constraint, and no single-output freshness or correctness condition. A repeated wrong value can occur infinitely often in the sequence while contributing only one range error. `IsExhaustiveGenerator A H` requires `∀ K ∈ H, ∀ s presenting K, ∃ tStar, ∀ t ≥ tStar` both conjuncts. The cutoff may depend on the entire presentation; no rate is supplied. `ExhaustivelyGeneratable H` is semantic existence of one such `A`.

**Feedback game.** A completed feedback round stores `(input x, query y, answer a, output z)`. At history `h`, the adversary supplies `x=A.input h`; the generator chooses `y=G.query h x`; the adversary answers `a=A.answer h x y`; the generator chooses `z=G.output h x y a`. History starts empty and appends completed rounds. Thus there is one query and one output per round; the learner sees all previous rounds and the current input, query and answer when choosing output. The current answer is available before the current output. The adversary may choose inputs adaptively from history.

`FeedbackAdversaryConsistent A G K` requires the resulting input stream to present `K` and every answer to be true iff its queried element is in `K`. `feedbackSampleThrough … t` is `S_{t+1}` of that input stream, including the current input. Consistent languages through `t` are members of the class containing this sample and matching every answer at rounds `s ≤ t`. Their intersection, with that sample removed, is `feedbackEffectiveIntersection`. Here “effective” names a residual set of common possibilities; its definition asserts no computability. Under a consistent actual play, the actual target belongs to the consistent class, so that class is nonempty.

`IsUniformFeedbackGeneratorAt G H d` requires every output to lie in `K \ S_{t+1}` whenever `|S_{t+1}| ≥ d`, for every `K ∈ H` and every adversary consistent with that target and `G`. `UniformlyGeneratableWithFeedback H = ∃ G d` this property. Neither strategy is required computable.

`GFDimensionAtLeast H d` means: for every generator strategy `G`, there exist `K ∈ H`, a consistent adversary `A`, and a time `t` with both `d ≤ t+1` and `d ≤ |S_{t+1}|`, at which the effective intersection is empty. The target, adversary and time may all depend on `G`. `HasFiniteGFDimension H = ∃ d, ¬GFDimensionAtLeast H d`. No numerical least dimension, tree construction, or equality of optimal constants occurs in this interface.

**Two-language adaptive membership dialogues.** A query is `(b,n) : Bool × Nat`, asking membership of `n` in `L₁` for `b=true`, and in `L₀` otherwise. Answers are Boolean and must agree with those memberships. An algorithm is a function from `(completed-round history, (current input, current answered-query list))` to either a new query (`Sum.inl`) or an output number (`Sum.inr`). A completed round records its input, a finite answered-query trace, and output. `QueryTraceValid` checks that each query is exactly the algorithm's next action on the preceding trace and that its answer is correct; `RoundValid` also checks the final output action and input. `ExecutionValid` aligns one valid completed round with each input of a finite prefix. `ExecutionOutputsAt … t z` existentially supplies such an execution on the first `t+1` inputs and selects its round-`t` output.

The learner can query either candidate, repeatedly and adaptively, with no fixed query-count bound. A completed round must have a finite trace. Its runtime arguments contain neither the target-selection Boolean nor an explicit presentation/index of the two languages: their information reaches it through the input stream and the two membership oracles. Its local action map is the object constrained by `Computable`; the arbitrary languages and their membership oracles need not be computable. This is an oracle interaction implemented by an ordinary computable finite-data action rule, not an ordinary computation of those memberships.

`NonuniformTwoLanguageMembershipGuarantee A L₀ L₁` means `∃ d₀ d₁, ∀ b s`, if `s` presents selected `L_b`, then at every round `t`: **(a)** some valid execution output exists, and **(b)** every valid execution output lies in `L_b \ S_{t+1}` whenever `|S_{t+1}| ≥ d_b`. Both thresholds are chosen before target Boolean, stream and time; they can depend on `A` and the pair. Clause (a) applies even below threshold. Clause (b) is universal over valid outputs; the statement does not rely on a separately supplied uniqueness theorem. `UniversalTwoLanguageMembershipGenerator A` conjoins `Computable A` with this guarantee for every distinct pair of infinite subsets of `Nat`. `TheoremSevenStatement` negates existence of such an `A`.

None of these models contains a probability measure, output distribution, support law, full-support hypothesis, expectation, loss function, limsup, or frequently-successful conclusion. The exhaustive range condition and the single-output membership/freshness conditions must not be interchanged.

## Target dossiers

All identifiers below are fully qualified. Types are reproduced from `declarations.jsonl`, with their universe annotations. In the explanatory skeletons, `Correct` and the other abbreviated predicates mean exactly the expanded glossary definitions.

### 1. `GenLimit.CharikarPabbaraju.Results.theorem_1`

Source anchor: `GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean:22`.

Exact exported type:

```lean
∀ {α : Type u_1} [Infinite.{u_1 + 1} α] [Countable.{u_1 + 1} α] (C : GenLimit.Generic.LanguageFamily.{u_1} α),
  GenLimit.Generic.UUS.{u_1} (Set.range.{u_1, 1} C) → GenLimit.CharikarPabbaraju.NonuniformlyGeneratable.{u_1} C
```

For every infinite countable universe and every `Nat`-indexed family all of whose languages are infinite, there exists one prefix generator that produces an unobserved target member after an index-dependent number of distinct observations, on every presentation of that target. Countability does not impose an effective encoding or effective family membership.

Quantifier skeleton:

`∀ {α} [Infinite α] [Countable α], ∀ C, UUS(range C) → ∃ G, ∀ i, ∃ d, ∀ s, Presents s (C i) → ∀ t, d ≤ |S_t| → (out ∈ C i ∧ out ∉ S_t)`.

The common `G` precedes `i`; the index-dependent `d` precedes the presentation. This is stronger than allowing an arbitrary cutoff separately for each presentation, but does not specify a single threshold for the family. The type is an existence statement with no named witness, `Computable G`, family oracle interface, or effective procedure mapping descriptions of families to generator programs. The glossary describes exactly what a prefix generator observes.

Repeated indices are allowed and can receive different witnesses `d`, even when they name the same language. The family cannot have empty range because it is indexed by all naturals. UUS excludes finite or empty target languages and hence exhausted infinite targets at a finite prefix. Repeating inputs can delay reaching the threshold arbitrarily, so there is no time bound depending only on `d`. A full presentation of an infinite language eventually has arbitrarily many distinct samples; after the threshold is reached the conclusion holds at every later stage. No condition is imposed before threshold, and no prohibition on reusing earlier generated outputs is present.

### 2. `GenLimit.CharikarPabbaraju.Results.theorem_2`

Source anchor: `GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean:31`.

Exact exported type:

```lean
GenLimit.CharikarPabbaraju.TheoremSevenStatement
```

This exported type is the closed proposition `TheoremSevenStatement`, expanded in the glossary. It says that there is no single computable adaptive membership-dialogue action rule working with the stated nonuniform guarantee for every pair of distinct infinite languages of natural numbers.

Quantifier skeleton, retaining the output-existence conjunct, is:

`¬∃ A, Computable A ∧ ∀ L₀ L₁, L₀ ≠ L₁ → Infinite L₀ → Infinite L₁ → ∃ d₀ d₁, ∀ b s, Presents s L_b → ∀ t, [(∃ z, Exec(A,L₀,L₁,s,t,z)) ∧ (∀ z, Exec(…) → d_b ≤ |S_{t+1}| → z ∈ L_b \ S_{t+1})]`.

The one program lies outside the language-pair quantifiers. There are pair-dependent and target-dependent thresholds, but no stream-dependent threshold. The target-selection Boolean occurs in the specification, not in the algorithm's input. Both candidate membership oracles are available, and each round may use any finite adaptive query trace. The computability restriction is on the action rule on finite lists; neither oracle is assumed decidable by ordinary computation.

Equivalently in classical logic, every computable rule has some distinct infinite pair on which no two thresholds make the guarantee hold. This is a failure of a uniform program across pairs; it does not assert that each individual pair lacks a specialized program, or that each target lacks a semantic generator. The statement supplies no named bad pair. Its negated guarantee may fail because a required output execution does not exist, or because a valid output is incorrect after a proposed threshold. It therefore cannot simply be restated as infinitely many wrong outputs by an otherwise terminating algorithm.

Equal pairs and finite or empty languages are outside the universal premise. Infinite targets retain unseen members after every finite sample. Repetitions remain allowed and the threshold counts distinct inputs, including the current round's input. Failure of execution cannot hide below threshold: output existence is required at every round. No finite time/query complexity bound, probabilistic qualification, or requirement that generated values never repeat is included.

### 3. `GenLimit.CharikarPabbaraju.Results.theorem_3`

Source anchor: `GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean:35`.

Exact exported type:

```lean
∃ C,
  And (Set.Countable.{0} C)
    (And (GenLimit.Generic.UUS.{0} C)
      (And (∀ (K : GenLimit.Generic.Language.{0} (List.{0} Bool)), Membership.mem.{0, 0} C K → Language.IsRegular.{0} K)
        (Not (GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable.{0} C))))
```

There exists a class of languages over finite Boolean words such that it is countable as a set, every member is infinite, every member is regular, and there is no exhaustive prefix operator for the class in the precise range-based sense above. All four conjuncts concern the same existentially chosen class.

Quantifier skeleton:

`∃ H : Set (Set (List Bool)), Countable H ∧ (∀ K ∈ H, Infinite K) ∧ (∀ K ∈ H, IsRegular K) ∧ ¬∃ A, ∀ K ∈ H, ∀ s, Presents s K → ∃ tStar, ∀ t ≥ tStar, [Finite(E_t \ K) ∧ K ⊆ S_t ∪ B_t ∪ E_t]`.

The existential witness is unspecified: no family enumeration, automata, computable membership predicates, or concrete counterexample class is exported by this signature. Set countability is not a uniform effective listing. Regularity is asserted individually; no function constructing automata from class indices is supplied. The excluded `A` ranges over all semantic total prefix-to-sequence functions, so this is stronger than merely excluding computable ones. Such an `A` would observe positive prefixes only, with no feedback or membership queries.

Negating exhaustive generation means that each proposed `A` fails for some member and presentation, with no eventual cutoff after which both range conditions persist. It does not mean that every stage fails, or that an infinite number of wrong distinct values must be generated: target coverage can fail instead. The class cannot be empty under all the conjuncts, since over the inhabited word universe a constant prefix operator would vacuously generate an empty class. Every member is infinite, so finite-target exhaustion is excluded. Countability of the class is compatible with repetitions in a possible enumeration but does not specify one. This is a separation between individual regularity/infinite targets and this particular collective exhaustive-generation property, not a statement about automata identification or output rates.

### 4. `GenLimit.CharikarPabbaraju.Results.theorem_4`

Source anchor: `GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean:44`.

Exact exported type:

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] (F : GenLimit.Generic.LanguageFamily.{u_1} α),
  GenLimit.Generic.UUS.{u_1} (Set.range.{u_1, 1} F) →
    Iff (GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable.{u_1} (Set.range.{u_1, 1} F))
      (GenLimit.CharikarPabbaraju.WeakAngluinExistence.{u_1} (Set.range.{u_1, 1} F))
```

For a family on a countable universe, assuming every language in its range is infinite, semantic exhaustive generation of that range is equivalent to a finite-witness condition on proper sublanguages in the same range.

Quantifier skeleton:

`∀ {α} [Countable α], ∀ F, UUS(range F) → [(∃ A, ∀ K ∈ range F, ∀ s presenting K, ∃ tStar, ∀ t ≥ tStar, ExhaustiveCorrectAt A K s t) ↔ (∀ L ∈ range F, ∃ T : Finset α, T ⊆ L ∧ ∀ L' ∈ range F, T ⊆ L' → L' ⊊ L → Finite(L \ L'))]`.

Both directions of the equivalence are asserted. For each target `L`, its finite `T` is selected before the competitor `L'`. It need not identify `L` exactly: a proper sublanguage containing `T` is allowed when it omits only finitely many elements of `L`. Only proper contained competitors are constrained. Supersets, incomparable languages, equal languages, and proper sublanguages failing to contain `T` impose no condition. There is no uniform bound on `|T|` or on the finite difference, and no effective witness-selection or witness-enumeration requirement. `T=∅` is allowed when it satisfies the condition.

The left side uses one prefix operator for all targets; its eventual cutoff may depend on target and presentation. The right side is pointwise existence of finite sets, not existence of a computable map from indices to witnesses. Neither side adds a membership oracle. `F` supplies a semantic natural-number listing of the class; repeated indices disappear on taking the range. The type assumes countability but not a displayed `Infinite α` instance; UUS together with the necessarily nonempty family range forces the universe to contain an infinite language. Therefore empty classes and exhausted finite targets are not instances of this theorem's premises. The equivalence makes no quantitative relation between witness size, sample threshold, or convergence time.

### 5. `GenLimit.CharikarPabbaraju.Results.theorem_5`

Source anchor: `GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean:53`.

Exact exported type:

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] {C : GenLimit.Generic.LanguageClass.{u_1} α},
  GenLimit.Generic.UUS.{u_1} C →
    Iff (GenLimit.CharikarPabbaraju.UniformlyGeneratableWithFeedback.{u_1} C)
      (GenLimit.CharikarPabbaraju.HasFiniteGFDimension.{u_1} C)
```

For any class on a countable universe, if every member is infinite, uniform generation with one truthful membership-feedback query per round is equivalent to failure of the stated adversarial obstruction at some finite natural scale.

Quantifier skeleton:

`∀ {α} [Countable α] {H}, UUS H → [(∃ G d, ∀ K ∈ H, ∀ A, Consistent A G K → ∀ t, d ≤ |S_{t+1}| → out_t ∈ K \ S_{t+1}) ↔ (∃ e, ¬[∀ G, ∃ K ∈ H, ∃ A, Consistent A G K ∧ ∃ t, e ≤ t+1 ∧ e ≤ |S_{t+1}| ∧ EffectiveIntersection H A G t = ∅])]`.

The left generator and threshold are common to all targets and consistent adaptive adversaries. The right finite obstruction scale is class-wide; within the negated formula, the adversarial target and play can depend on each proposed `G`. Classical negation yields some strategy avoiding every qualifying empty-intersection situation, but the exact exported form is the negation shown. The theorem asserts equivalence of existence properties, not that the two displayed natural numbers are equal, optimal, or computable from each other.

The consistent-language intersection uses all sample observations and all query answers through the current round, after feedback and before assessing output. An empty residual intersection says no element outside the observed sample is common to every currently consistent class member. The round-count requirement `e ≤ t+1` is explicitly present alongside `e ≤ |S_{t+1}|`; the latter already implies the former because there are at most `t+1` distinct inputs, but neither conjunct has been silently dropped. The dimension is defined through strategies and attainable histories, not through a standalone combinatorial closure formula supplied elsewhere.

Neither side requires computable strategies, a computably represented class, effective search of the intersection, or a computable numerical dimension. Countability permits semantic choices without furnishing their implementation. There is no claimed rate in elapsed rounds: repeated inputs may delay reaching the distinct-sample threshold. Correctness is all qualifying rounds, including the threshold, and freshness excludes only presented inputs. Threshold zero is allowed.

Here `H` can be empty and UUS is then vacuous. A generator strategy still exists even on an empty universe because its methods receive a current element as an argument; identity-based methods suffice. With no target in the class the success conditions are vacuous and the existential-target obstruction is false, so both sides can hold. Under a consistent play with a nonempty class, the actual target prevents the consistent-language set from being empty; empty-intersection conclusions therefore reflect lack of a shared fresh element, not inconsistent evidence. Finite target exhaustion is excluded by UUS for actual members.

### 6. `GenLimit.CharikarPabbaraju.Results.theorem_6`

Source anchor: `GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Detailed.lean:22`.

Exact exported type:

```lean
∀ {α : Type u_1} [inst : Infinite.{u_1 + 1} α] (C : GenLimit.Generic.LanguageFamily.{u_1} α),
  GenLimit.Generic.UUS.{u_1} (Set.range.{u_1, 1} C) →
    ∀ {i t : Nat} (stream : GenLimit.Generic.Stream.{u_1} α),
      GenLimit.Generic.StreamIn.{u_1} stream (C i) →
        LE.le.{0}
            (Max.max.{0} (HAdd.hAdd.{0, 0, 0} i 1)
              (HAdd.hAdd.{0, 0, 0} (GenLimit.CharikarPabbaraju.nonuniformComplexity.{u_1} C i) 1))
            (Finset.card.{u_1} (GenLimit.Generic.sample.{u_1} stream t)) →
          GenLimit.Generic.CorrectAt.{u_1} (GenLimit.CharikarPabbaraju.greedyGenerator.{u_1} C) (C i) stream t
```

For every infinite universe and indexed family of infinite languages, the particular classical `greedyGenerator C` is correct at any stage whose number of distinct sample elements is at least `max(i+1, nonuniformComplexity C i + 1)`, on every stream staying inside `C i`. No countability instance or full presentation is required.

Quantifier skeleton:

`∀ {α} [inst : Infinite α], ∀ C, UUS(range C) → ∀ {i t : Nat}, ∀ s, range s ⊆ C i → max(i+1, complexity C i+1) ≤ |S_t| → [output(greedyGenerator C,s,t) ∈ C i ∧ output(…) ∉ S_t]`.

Here `complexity C i+1` in the skeleton denotes `(nonuniformComplexity C i) + 1`, not complexity at index `i+1`. The exact type above fixes this association. Both additive ones matter. The `i+1` term guarantees enough prefix length for index `i` to have been considered; the other term places sample cardinal strictly above every finite intersection size contributing to the scale. The finite-intersection maximum uses subsets of indices through `i` containing `i`; it is not a maximum over the entire infinite family. No asymptotic order notation, hidden multiplicative constant, or unspecified rate occurs.

The named generator sees the length-`t` positive prefix and is defined using semantic subset and infinitude tests plus classical choice. Its definition depends on `C`; no effective input format or ordinary computability is asserted. The result identifies a semantic witness and explicit mathematical threshold, which is distinct from supplying a uniform executable procedure computing that threshold or the chosen point from family membership oracles.

`StreamIn` is weaker than `Presents`: the stream need never enumerate the whole target. If it repeats only finitely many values below the threshold, the implication never activates; the statement does not promise eventual correctness on such a stream. Whenever the threshold does activate, both correctness conjuncts hold at that very stage, not merely later or infinitely often. At `t=0` it cannot activate because the maximum is at least one while the sample is empty. Infinite universes make the initial empty-index intersection infinite, and UUS excludes target exhaustion. Duplicated family languages remain permitted, while index order and duplication can alter this numerical bound. Earlier generated outputs are not excluded from reuse.

### 7. `GenLimit.CharikarPabbaraju.Results.theorem_7`

Source anchor: `GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Detailed.lean:36`.

Exact exported type:

```lean
GenLimit.CharikarPabbaraju.TheoremSevenStatement
```

This target has exactly the same exported type as target 2: `TheoremSevenStatement`. It independently occupies `Results/Detailed.lean:36`; its identifier is separately covered rather than inferred from a numbering convention.

Its full quantifier skeleton is again:

`¬∃ A, Computable A ∧ ∀ L₀ L₁, L₀ ≠ L₁ → Infinite L₀ → Infinite L₁ → ∃ d₀ d₁, ∀ b s, Presents s L_b → ∀ t, [(∃ z, Exec(A,L₀,L₁,s,t,z)) ∧ (∀ z, Exec(…) → d_b ≤ |S_{t+1}| → z ∈ L_b \ S_{t+1})]`.

Thus its meaning and limitations are the same as target 2: one ordinary computable finite-data action rule cannot satisfy all distinct infinite pairs, even with both membership oracles and arbitrary finite adaptive query traces per completed round. Thresholds may depend on the pair and target but not the stream. The hidden target Boolean is not given to the action rule; it receives past rounds, current input and current query-answer trace. Total completion at every round is a separate conjunct from thresholded correctness, and failure need not consist solely of wrong outputs. Equal pairs and finite/empty targets are excluded; repetitions are allowed; distinct observations through round `t` are counted. No named adverse pair, query bound, distributional law, or result about all noncomputable action rules is asserted. The duplicate type does not authorize treating these two targets as different mathematical claims.

## Exhaustive coverage and interpretive limits

| Target | Source anchor within Results | Fully covered content | Computation and time qualification |
|---|---|---|---|
| `GenLimit.CharikarPabbaraju.Results.theorem_1` | `Overview.lean:22` | Infinite/countable universe, all-infinite indexed family, shared generator, index-dependent threshold, both correctness conjuncts | Semantic existence; every presentation and every stage after distinct-sample threshold |
| `GenLimit.CharikarPabbaraju.Results.theorem_2` | `Overview.lean:31` | Expanded closed lower bound; pair/target thresholds; all-round existence and universal output correctness | Excludes one computable action rule across all distinct infinite pairs; oracle dialogues |
| `GenLimit.CharikarPabbaraju.Results.theorem_3` | `Overview.lean:35` | Same class is countable, all-infinite, individually regular, and not exhaustively generatable | Excludes semantic prefix-to-sequence operators; both eventual range conditions retained |
| `GenLimit.CharikarPabbaraju.Results.theorem_4` | `Overview.lean:44` | Both directions; finite witness inside each target; all proper contained competitors with witness have finite deficit | Semantic equivalence; no uniform/effective witness assignment or convergence rate |
| `GenLimit.CharikarPabbaraju.Results.theorem_5` | `Overview.lean:53` | Both directions; shared feedback threshold; exact adversarial intersection obstruction and both size constraints | Semantic strategies; one query per round, all qualifying stages, no numerical identity claimed |
| `GenLimit.CharikarPabbaraju.Results.theorem_6` | `Detailed.lean:22` | Named greedy witness; infinite universe; only stream containment; exact maximum threshold; both correctness conjuncts | Classical choice and semantic tests; pointwise bound for every qualifying stage, no countability needed |
| `GenLimit.CharikarPabbaraju.Results.theorem_7` | `Detailed.lean:36` | Entire closed lower bound independently covered; exact duplicate of target 2 | Same effective/oracle boundary and all-round termination conjunct as target 2 |

The seven coverage entries match `targets.txt` exactly, with no extra audited target. The glossary expands the definitions needed to distinguish their observation interfaces, witness dependencies, finite-intersection scale, feedback dimension, range conditions, and boundary cases. The evidence supports these statement reconstructions only. It does not establish fresh compilability, kernel trust or proof-axiom status, source/paper correspondence, intended numbering, effective realizability of unrestricted witnesses, or human certification. No paper, source proof/comment, owner material, other-stage context, old audit, registry interpretation, or other results were consulted.
