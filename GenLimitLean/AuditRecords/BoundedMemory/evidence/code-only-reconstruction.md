# 31 — Paper31_BoundedMemory — On Language Generation in the Limit with Bounded Memory — Lean statement reconstruction

## 1. Scope, source, and method

This report reconstructs only the formal mathematical content of the attached bundle `31__Paper31_BoundedMemory__lean-source-bundle.txt`. The bundle header identifies repository commit `dfcd13534f9d51642a9f88904268e95454c88f7f`; the local file inspected here has SHA-256 `0ec532428136a18169c63cf3d5fecd8dcc8c9fc5ab4eacf2288a323a7f3d4ea1`. The bundle contains 21 Lean source files: 17 declaration-bearing primary modules under `GenLimit/Paper31_BoundedMemory/`, one primary umbrella module with imports only, two `GenLimit/Core` dependency modules, and one shared ordered-density dependency module.

The reconstruction uses declaration signatures and formal definition equations. It does **not** use comments, docstrings, declaration names, theorem labels, module names, or the paper title as evidence for mathematical meaning. Names and paths are reported only so that each claim can be located. The bodies of theorem proofs and tactic scripts are ignored. Bodies of definitions are used only where they determine the defined object.

A declaration is treated as **materially substantive** when it fixes a model, success criterion, density quantity, hard instance, nontrivial construction, nontrivial invariant, or a logical implication/equivalence used in a main conclusion. Public coercion instances, one-step simp equations, and elementary indexing identities are not given full individual essays; they are recorded in the reviewed-support ledger in §24 so that the scope decision is explicit.

No axiom declarations occur in the primary modules. Many constructions are declared `noncomputable` and use classical choice internally. Therefore existence in Lean must not be read as an effective algorithm unless the declaration separately supplies an effective interface; none of the principal existence theorems does so.

### Classification vocabulary

- **Semantic/extensional:** a proposition about sets, functions, streams, limits, or eventual behavior, without an implementation model.
- **Constructive:** the statement supplies a concrete function/structure by a definition whose operations are explicit at the mathematical level. This does not by itself imply computability.
- **Computable/effective:** would require decidable operations, an oracle interface, recursive realizability, or an explicit algorithmic theorem. The primary results generally do not have this status.
- **Machine-level/runtime-bounded:** would require a representation and resource bound. No principal result has this status.
- **Probabilistic:** would quantify over probability spaces or random variables. No primary result is probabilistic.
- **Conditional:** the conclusion is an implication from explicitly supplied hypotheses, such as success of another generator or existence of a learner.

## 2. Dependency/interface ledger

These declarations are imported interfaces, not results attributed to the primary Paper 31 modules.

### 2.1 `GenLimitLean/GenLimit/Core/Basic.lean`

- `GenLimit.Language` is definitionally `Set ℕ`, and `GenLimit.LanguageFamily` is `ℕ → Set ℕ`.
- `GenLimit.Presents stream L` means `Set.range stream = L`.
- `GenLimit.sample stream t` is the finite set of distinct observations at indices strictly below `t`.
- `GenLimit.Consistent C stream t i` means that every sampled value before `t` belongs to `C i`.
- `GenLimit.MembershipOracle C` packages a Boolean function `query : ℕ → ℕ → Bool` with the exact specification `query i u = true ↔ u ∈ C i`.

The primary Paper 31 declarations do not take `MembershipOracle` or `Consistent` as arguments. This dependency module also exports elementary sample/presentation lemmas; they are background interfaces rather than Paper 31 results.

### 2.2 `GenLimitLean/GenLimit/Core/Countable.lean`

- `GenLimit.Generic.Language α` is definitionally `Set α`.
- `GenLimit.Generic.LanguageClass α` is `Set (Set α)`.
- `GenLimit.Generic.LanguageFamily α` is `ℕ → Set α`.
- `GenLimit.Generic.Stream α` is `ℕ → α`.
- `GenLimit.Generic.Generator α` is `∀ t : ℕ, (Fin t → α) → α`, a function on a finite history of exactly length `t`.
- `GenLimit.Generic.Presents stream L` means `Set.range stream = L`. Thus the stream contains no element outside `L` and every element of `L` occurs at least once; repetitions are permitted.
- `GenLimit.Generic.StreamIn stream L` means `Set.range stream ⊆ L`.
- `GenLimit.Generic.sample stream t` is the finite set of distinct values at indices strictly below `t`.
- `GenLimit.Generic.output G stream t` runs a finite-history generator on the prefix strictly before `t`.
- `GenLimit.Generic.CorrectAt G L stream t` means the output at time `t` lies in `L` and is absent from the sample before time `t`.

Dependency theorems used repeatedly say that exact presentations eventually reveal every fixed target element and every fixed finite target subset; an exact presentation of an infinite set reaches every finite sample cardinality; an injective stream is finitely repeating; and samples are monotone. These are interface facts, not primary Paper 31 conclusions.

### 2.3 `GenLimitLean/GenLimit/Shared/KleinbergWei/OrderedDensity.lean`

`GenLimit.KleinbergWei.OrderedLanguage` is a structure with:

1. a carrier `Set ℕ`;
2. an enumeration `ℕ → ℕ`;
3. injectivity of that enumeration; and
4. equality between its range and the carrier.

Consequently, an `OrderedLanguage` supplies a duplicate-free ordering of an infinite countable carrier. For such `K` and a set `A`:

- `K.prefixCount A n` counts indices `< n` whose enumerated value lies in `A`;
- `K.prefixRatio A n` is `0` at `n = 0` and otherwise `prefixCount/n` in `ℝ`;
- `K.upperDensity A` is `limsup` of these ratios along `atTop`;
- `K.lowerDensity A` is `liminf` of these ratios along `atTop`.

The density order is supplied to the evaluator. None of the memoryless, window, or buffer generator types receives this order as a runtime input.

### 2.3 Temporal notation

- `∃ T, ∀ t, T ≤ t → P t` means eventual truth after a finite threshold.
- `∃ᶠ t in atTop, P t` means `P` occurs arbitrarily late (frequently), not eventually and not with a probability.
- Outer run densities are real `limsup`s over time or window start position.

## 3. Base memoryless set model

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/Definitions.lean`

#### `MemorylessSetGenerator`

For every type `α`, `MemorylessSetGenerator α` is the function type `α → Set α`. At a round the formal object receives exactly one element `x : α` and returns a set. It receives no target set, family index, presentation prefix, prior state, membership oracle, enumeration, certificate, bound, or density order. The family may nevertheless be captured extensionally when the function is chosen. Classification: semantic function type; no effectiveness or resource claim.

#### `ValidSetOutput`

For `G : α → Set α`, target `K : Set α`, and current element `x : α`, `ValidSetOutput G K x` is the conjunction

1. `G x` is infinite, and
2. `G x ⊆ K`.

There is no freshness requirement relative to observations, no requirement that `x ∈ K`, and no requirement that `G x` be decidable or enumerable. The success predicates supply `x ∈ K` indirectly through exact presentation. Classification: extensional validity predicate.

#### `IsArbitraryPresentationMemorylessGenerator`

`IsArbitraryPresentationMemorylessGenerator G H` means, in binder order:

1. for every set `K`,
2. if `K ∈ H`,
3. then for every stream `stream : ℕ → α`,
4. if `stream` exactly presents `K`,
5. there exists a time `T` such that for every `t ≥ T`,
6. `G (stream t)` is an infinite subset of `K`.

The threshold may depend on `K` and on the complete stream. The generator at time `t` still sees only `stream t`. Repetitions are unrestricted. Classification: semantic, eventual, adversarial, non-probabilistic.

#### `ArbitraryPresentationMemorylessGeneratable`

`ArbitraryPresentationMemorylessGeneratable H` means that there exists one memoryless set generator `G` satisfying the preceding property simultaneously for every member of `H`. The generator is selected after `H` is fixed and may encode all of `H`; it is not uniform across all classes. Classification: existential semantic claim.

#### `FinitelyRepeating`

For a stream `stream : ℕ → α`, `FinitelyRepeating stream` means that for every element `x : α`, the set of times `{t | stream t = x}` is finite. This does not require injectivity: each element may occur more than once, but only finitely many times. On an infinite time domain, a finitely repeating exact presentation can exist only for an infinite target. Classification: extensional stream restriction.

#### `IsFinitelyRepeatingMemorylessGenerator`

`IsFinitelyRepeatingMemorylessGenerator G H` has the same quantifier order as the arbitrary-presentation predicate, but after exact presentation it additionally assumes `FinitelyRepeating stream`. Only then must an eventual threshold with infinite-subset outputs exist. The threshold may depend on the target and stream. Classification: semantic conditional success criterion.

#### `FinitelyRepeatingMemorylessGeneratable`

`FinitelyRepeatingMemorylessGeneratable H` means that there exists one `G : α → Set α` satisfying `IsFinitelyRepeatingMemorylessGenerator G H`. For finite target languages, the quantified class of finitely repeating exact presentations is empty, so the success obligation for those targets is vacuous. This vacuity is important in later theorems that omit an infinitude assumption.

#### `singletonCore`

For a class `H` and point `x`,

`singletonCore H x = {y | ∀ K, K ∈ H → x ∈ K → y ∈ K}`.

Thus it is the intersection of every member of `H` that contains `x`; if no member contains `x`, the universal condition makes the core all of `α`. Runtime access is irrelevant: this is an extensional set definition.

#### `singletonCore_subset`

For every `H`, `x`, and `K`, if `K ∈ H` and `x ∈ K`, then `singletonCore H x ⊆ K`. This is a direct consequence of the defining universal quantifier. Classification: semantic support lemma; no hidden assumptions.

#### `InfiniteSingletonCores`

`InfiniteSingletonCores H` means: for every `x`, if `x` belongs to the union `⋃₀ H`, then `singletonCore H x` is infinite. Points outside the union impose no condition. For `H = ∅` the predicate is vacuously true.

## 4. Arbitrary repetitions

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/ArbitraryRepetitions.lean`

The section containing the necessity direction has the typeclass assumption `[Countable α]`. This is a proposition-level countability interface; no enumeration is supplied to the resulting generator at runtime.

#### `basePresentation`

Given `[Countable α]`, a set `K : Set α`, and a witness `hK : K.Nonempty`, `basePresentation K hK : ℕ → α` is a noncomputably chosen stream obtained from a chosen surjection `ℕ → K`. The choice uses the nonemptiness witness and countability of the ambient type. It is not an effective enumeration theorem.

#### `basePresentation_presents`

For every nonempty `K` in a countable ambient type, `basePresentation K hK` exactly presents `K`. Quantifiers are exactly `K`, then its nonemptiness witness. Classification: semantic existence via classical choice.

#### `repeatedPointPresentation`

Given nonempty `K` and an arbitrary `x : α`, `repeatedPointPresentation K hK x` outputs `x` at every even time and `basePresentation K hK (t/2)` at every odd time. The definition itself does not require `x ∈ K`.

#### `repeatedPointPresentation_presents`

If additionally `x ∈ K`, the repeated-point stream exactly presents `K`. It repeats `x` infinitely often and so is generally not finitely repeating. This is the adversarial access pattern used only in the arbitrary-repetition regime.

#### `arbitrary_success_implies_pointwise`

Assume `[Countable α]`. Given:

1. `G` and `H`;
2. `hG : IsArbitraryPresentationMemorylessGenerator G H`;
3. `K ∈ H`; and
4. `x ∈ K`,

then `ValidSetOutput G K x` already holds pointwise: `G x` is infinite and contained in `K`. The conclusion is not merely eventual, and the statement requires no presentation witness from the caller. The separately declared repeated-point presentation explains, at the statement level, how arbitrary repetitions can test one observation indefinitely. Classification: semantic implication; countability is a hidden ambient assumption.

#### `arbitrary_memoryless_necessity`

Under `[Countable α]`, if `H` is arbitrary-presentation memorylessly generatable, then `InfiniteSingletonCores H`. No countability or infinitude assumption on `H` is present in this declaration. Access audit: the existential generator sees only a point, but arbitrary repetitions force every possible pointwise output to work for every target containing that point. Classification: semantic necessity.

#### `arbitrary_memoryless_sufficiency`

For arbitrary `α`, with no countability assumption, if `InfiniteSingletonCores H`, then `H` is arbitrary-presentation memorylessly generatable. The existential conclusion itself does not name a witness. Separately, the public definition `singletonCore`, the theorem `singletonCore_subset`, and the premise `InfiniteSingletonCores H` jointly certify the pointwise function `x ↦ singletonCore H x`, with validity from time `0`. This is explicit at the set-theoretic level but not computational, because membership in the core is a higher-order universal predicate over `H`.

#### `theorem_3_1`

Assume `[Countable α]`. In binder order, for every class `H : Set (Set α)`, every proof that `H` is countable, and every proof that each `K ∈ H` is infinite,

`ArbitraryPresentationMemorylessGeneratable H ↔ InfiniteSingletonCores H`.

Both supplied hypotheses on `H` are syntactically present but redundant relative to the separately exported necessity and sufficiency implications; only ambient `[Countable α]` occurs in the stronger necessity declaration. Thus the displayed equivalence is stated under stronger assumptions than those separate declarations require, but it remains formally quantified over the supplied assumptions. There is no circularity: the right side is a direct extensional core condition. For `H = ∅`, both sides hold vacuously. Classification: exact semantic equivalence, non-effective.

## 5. Finitely repeating presentations over `ℕ`

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/FinitelyRepeating.lean`

This module fixes both the example type and language-family index to `ℕ`. The numerical value of the current observation is used as a search-depth bound; this is representation-sensitive.

#### `prefixCore`

For `langs : ℕ → Set ℕ`, depth `n`, and observed number `x`, `prefixCore langs n x` consists of all `y` such that, for every index `j ≤ n`, if `x ∈ langs j` then `y ∈ langs j`. It is the intersection of the first `n+1` indexed languages that contain `x`. Repeated languages and index order matter.

#### `mem_prefixCore`, `prefixCore_mono`, and `prefixCore_zero_infinite`

- `mem_prefixCore` says `x ∈ prefixCore langs n x` for every `langs,n,x`.
- `prefixCore_mono` says that if `m ≤ n`, then the deeper core at `n` is contained in the shallower core at `m`.
- `prefixCore_zero_infinite` says that if `langs 0` is infinite, then `prefixCore langs 0 x` is infinite for every `x`; if `x ∉ langs 0` the core is universal, and if `x ∈ langs 0` it equals `langs 0`.

These are extensional set facts and supply the nonemptiness of the search predicate used next.

#### `selectedDepth`

`selectedDepth langs x` is the greatest natural `n ≤ x` for which `prefixCore langs n x` is infinite. It is noncomputable because it tests infinitude of arbitrary sets. The observation `x` is used not just as data but as a numerical upper bound. No oracle or decision procedure is supplied.

#### `selectedDepth_le`, `selectedDepth_core_infinite`, and `le_selectedDepth_of_infinite`

- `selectedDepth_le` gives `selectedDepth langs x ≤ x` unconditionally.
- `selectedDepth_core_infinite` assumes every `langs n` is not needed; it assumes only `langs 0` is infinite and concludes the selected core is infinite.
- `le_selectedDepth_of_infinite` says that if `n ≤ x` and `prefixCore langs n x` is infinite, then `n ≤ selectedDepth langs x`.

#### `finitelyRepeatingGenerator`

The noncomputable memoryless generator is

`finitelyRepeatingGenerator langs x = prefixCore langs (selectedDepth langs x) x`.

At runtime it receives only `x`; the entire indexed family and semantic infinitude tests are compiled into the function. It has no target index or history.

#### `finitelyRepeatingGenerator_infinite`

If every `langs n` is infinite, then for every input `x`, the output of `finitelyRepeatingGenerator langs` is infinite. The separately exported theorem `selectedDepth_core_infinite` requires only infinitude of `langs 0`, so the all-indices premise here is stronger than is needed for this particular output-infinitude conclusion.

#### `indexedIntersection`, `prefixSignature`, and `prefixCore_eq_indexedIntersection`

For a fixed `z`:

- `indexedIntersection langs S` is the intersection of the languages whose indices lie in a finite set `S : Finset (Fin (z+1))`.
- `prefixSignature langs z x` is the finite set of indices at most `z` whose language contains `x`.
- `prefixCore_eq_indexedIntersection` identifies `prefixCore langs z x` with the indexed intersection at this signature.

These definitions expose the fact that only finitely many signatures are possible for a fixed target index `z`.

#### `finiteIntersectionPiece` and `finiteIntersectionEnvelope`

For each finite signature `S`, `finiteIntersectionPiece langs S` equals its indexed intersection if that intersection is finite, and equals `∅` otherwise. `finiteIntersectionEnvelope langs z` is the union of these pieces over every finite signature on `Fin (z+1)`.

`finiteIntersectionPiece_finite` and `finiteIntersectionEnvelope_finite` assert, respectively, that each piece and the entire finite union are finite. `mem_finiteIntersectionEnvelope_of_prefixCore_finite` says that if `prefixCore langs z x` is finite, then `x` lies in this envelope. These declarations are noncomputable because finiteness is tested classically.

#### `badPoints`

For a target index `z`, `badPoints langs z` is the set of numbers `x` satisfying both `x ∈ langs z` and failure of the containment `finitelyRepeatingGenerator langs x ⊆ langs z`.

#### `badPoints_subset` and `badPoints_finite`

`badPoints_subset` states

`badPoints langs z ⊆ Set.Iio z ∪ finiteIntersectionEnvelope langs z`.

Thus a bad target point is either numerically below the target index or belongs to the finite envelope. `badPoints_finite` concludes that the bad-point set is finite. This is a substantive representation-dependent fact: the ambient order on natural-number examples is used through `x < z`.

#### `finitelyRepeating_avoids_finite_set`

For any type `α`, any finitely repeating stream, and any finite set `S : Set α`, there exists `T` such that `stream t ∉ S` for all `t ≥ T`. The finite set need not be contained in the stream range or in a target. Classification: semantic eventuality lemma.

#### `finitelyRepeatingGenerator_succeeds`

For every enumeration `langs : ℕ → Set ℕ`, if every `langs n` is infinite, then the explicit `finitelyRepeatingGenerator langs` satisfies `IsFinitelyRepeatingMemorylessGenerator` on `Set.range langs`. Quantifier expansion: for every target value in the range, every exact finitely repeating presentation of that target eventually sees only inputs on which the output is an infinite subset of the target. The generator is family-specific and noncomputable.

#### `theorem_1_1_enumerated`

Under the same infinitude assumption, the range of any enumerated family `langs : ℕ → Set ℕ` is finitely-repeating memorylessly generatable. Repetitions in the family enumeration are allowed. The separately exported declaration `finitelyRepeatingGenerator_succeeds` certifies an explicit family-dependent candidate, although this existential theorem does not expose the witness in its result type. Classification: semantic existence.

#### `theorem_1_1`

For every `H : Set (Set ℕ)`, if `H` is countable and every member of `H` is infinite, then `FinitelyRepeatingMemorylessGeneratable H`.

The generator is chosen after the whole class `H` is given. The statement supplies no enumeration to the caller, no membership oracle, and no effectiveness. If `H` is empty, the conclusion is obtained vacuously. Countability is used to select a surjective enumeration when `H` is nonempty. Classification: semantic, noncomputable existence theorem.

## 6. Element-output and index-output separations

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/OutputSeparations.lean`

### 6.1 Stream constructions used by the obstruction statements

#### `infiniteEnumeration`

Assuming `[Countable α]`, for every infinite set `S : Set α` and proof `hS : S.Infinite`, this noncomputable definition chooses a bijective enumeration of the subtype `S` and returns its underlying `α`-valued stream. The associated declarations `infiniteEnumeration_mem`, `infiniteEnumeration_injective`, and `infiniteEnumeration_presents` state, respectively, that every term lies in `S`, the stream is injective, and its range is exactly `S`. This is classical choice, not an effective enumeration interface.

#### `injective_finitelyRepeating`

For every stream on any type, injectivity implies `FinitelyRepeating`. This supplies the presentation restriction for all repetition-free adversarial streams constructed in this and later modules.

#### `interleave`

For streams `left,right : ℕ → α`, `interleave left right` takes `left (t/2)` at even `t` and `right (t/2)` at odd `t`. `interleave_streamIn` says that if both streams stay in `K`, then the interleaving stays in `K`. `interleave_presents_of_right` says that if the left stream stays in `K` and the right stream exactly presents `K`, then their interleaving exactly presents `K`. `interleave_finitelyRepeating` says finite repetition of both streams implies finite repetition of the interleaving. These are deterministic stream combinators; they give the adversary complete control of a subsequence while preserving exactness.

#### `prepend`

`prepend head tail` has value `head` at time `0` and `tail n` at time `n+1`. `prepend_presents` says that if `head ∈ K` and `tail` presents `K`, the prepended stream also presents `K`; `prepend_finitelyRepeating` says finite repetition is preserved. These declarations expose that a finite prefix can seed later freshness obstructions.

### 6.2 Memoryless element output

#### `MemorylessElementGenerator`

For a type `α`, `MemorylessElementGenerator α` is `α → α`. It receives only the current observed element and returns one element. It has no state, target, family index, sample, or oracle input.

#### `ElementCorrectAt`

For `G`, target `K`, stream, and time `t`, correctness means both:

1. `G (stream t) ∈ K`; and
2. `G (stream t)` is not in `GenLimit.Generic.sample stream (t+1)`.

The sample through `t+1` contains all observations at indices `0,…,t`, so the generated element must differ from the current observation as well as every earlier observation. This is stronger than the core dependency predicate `CorrectAt`, which samples strictly before `t`.

#### `IsFinitelyRepeatingElementGeneratorOn`

`IsFinitelyRepeatingElementGeneratorOn G K` means: for every stream presenting `K`, if the stream is finitely repeating, then there exists `T` such that `ElementCorrectAt G K stream t` holds for every `t ≥ T`. The threshold depends on the stream. There is one fixed target `K`; this predicate does not quantify over a family.

#### `element_bad_set_infinite_obstruction`

Assume `[Countable α]`. Given an infinite target `K`, an infinite subset `B ⊆ K`, and a memoryless element generator `G` such that every `x ∈ B` satisfies either `G x ∉ K` or `G x = x`, then `G` is not a successful finitely-repeating element generator on `K`. The disjunction is pointwise and may choose a different branch for different `x`. Classification: semantic impossibility theorem.

#### `goodFiber`

For `G,K,B,y`, `goodFiber G K B y` is the set of `x ∈ K \ B` with `G x = y`. It is an exact fiber restricted to the “good” domain outside `B`.

#### `element_infinite_fiber_obstruction`

Assume `[Countable α]`. If `K` is infinite, `y ∈ K`, and `goodFiber G K B y` is infinite, then `G` fails `IsFinitelyRepeatingElementGeneratorOn G K`. No finiteness or subset hypothesis on `B` is required in this declaration. The adversary can first present `y` and later feed infinitely many distinct inputs mapped to the already seen `y`.

#### `goodImage` and `goodImage_infinite_of_finite_fibers`

`goodImage G K B` is the image `G '' (K \ B)`. If `K \ B` is infinite and every restricted fiber `goodFiber G K B y` is finite, then `goodImage G K B` is infinite. This is a finite-fiber counting principle over sets, with no computability assumptions.

#### `element_finite_fibers_obstruction`

Assume `[Countable α]`. If:

1. `K` is infinite;
2. `B` is finite;
3. every `x ∈ K \ B` has `G x ∈ K` and `G x ≠ x`; and
4. every good fiber is finite,

then `G` still fails on `K`. The statement handles the complementary branch to the infinite-fiber obstruction: infinitely many distinct good outputs can be inserted before their corresponding inputs so that each output is already seen.

#### `theorem_3_2_element`

Assume `[Countable α]`. For every infinite `K : Set α` and every function `G : α → α`,

`¬ IsFinitelyRepeatingElementGeneratorOn G K`.

Thus no memoryless single-element function succeeds on even one infinite target against all finitely repeating exact presentations. The result is fully semantic: it does not assume or conclude computability, and the adversarial presentation may depend on `G`. It is not vacuous because an infinite subset of a countable type has an injective exact presentation.

### 6.3 Memoryless index output

#### `MemorylessIndexGenerator`

`MemorylessIndexGenerator α ι` is `α → ι`. The output index is determined only by the current example.

#### `IsFinitelyRepeatingIndexGenerator`

For `G : α → ι` and `langs : ι → Set α`, success means, in binder order:

1. for every target index `target`;
2. for every stream;
3. if the stream presents `langs target` and is finitely repeating;
4. then eventually, for every time `t`,
5. `langs (G (stream t)) ⊆ langs target`.

The output index need not equal the target. The output language need not be infinite, distinct from other indexed languages, or fresh; only one-sided containment is required. The same index type is used for available outputs, but this model has no persistent state.

#### `indexLanguageZero`, `indexLanguageOne`, `indexLanguages`, and `commonMultiples`

The two indexed languages over `ℕ` are:

- `indexLanguageZero = {n | n mod 4 = 0 or 1}`;
- `indexLanguageOne = {n | n mod 4 = 0 or 2}`.

`indexLanguages : Fin 2 → Set ℕ` maps index `0` to the first and index `1` to the second. `commonMultiples = {n | n mod 4 = 0}` is contained in both. The declarations `commonMultiples_infinite`, `commonMultiples_subset_zero`, `commonMultiples_subset_one`, and `indexLanguages_infinite` assert the corresponding infinitude and containments. `indexLanguageZero_not_subset_one` and `indexLanguageOne_not_subset_zero` state that neither language is contained in the other.

#### `index_fiber_obstruction`

Let `G : ℕ → Fin 2`, choose output index `i`, target index `target`, and an infinite set `A`. If:

1. `A ⊆ commonMultiples`;
2. `G x = i` for every `x ∈ A`; and
3. `indexLanguages i` is not contained in `indexLanguages target`,

then `G` fails the finitely-repeating index-generation predicate on the two-language family. The infinite set `A` consists of points valid for either target, while the constant output index is wrong for the chosen target.

#### `theorem_3_2_index`

For every function `G : ℕ → Fin 2`, `G` is not a successful finitely-repeating index generator for `indexLanguages`. The two output indices are the only available outputs. The theorem is representation-specific to this index family but has no runtime or computability premise.

#### `theorem_3_2`

The declaration is one conjunction with the following exact content:

1. every one of the two `indexLanguages` is infinite;
2. for every infinite `K ⊆ ℕ` and every memoryless element generator `G : ℕ → ℕ`, `G` fails on `K`; and
3. for every memoryless index generator `G : ℕ → Fin 2`, `G` fails on the displayed two-language family.

The first conjunct is descriptive witness data. The second is universal over all infinite targets; the third is an existential-hard-family result with the family fixed by definition. Together they separate infinite-set output from element and index output in the finitely repeating regime, but the conjunction does not itself restate the positive set-output theorem.

## 7. Incremental approximate identification

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalIdentification.lean`

This module is universe-polymorphic in the example type `α`. Its finite family is indexed by `Fin (N+1)`, so the family is nonempty even when `N = 0`.

### 7.1 Almost-containment relations

#### `AlmostContained`

For sets `A,B : Set α`, `AlmostContained A B` means that the set difference `A \ B` is finite. This is one-sided containment modulo finitely many exceptions.

#### `AlmostEquivalent`

`AlmostEquivalent A B` is the conjunction of `AlmostContained A B` and `AlmostContained B A`; equivalently, both one-sided differences are finite. Equality of indices or sets is not required.

#### `StrictAlmostContained`

`StrictAlmostContained A B` means `A \ B` is finite but `B \ A` is not finite. It is asymmetric. The declarations `almostContained_refl`, `almostContained_trans`, `almostEquivalent_refl`, `almostEquivalent_symm`, `almostEquivalent_trans`, `strictAlmostContained_irrefl`, and `strictAlmostContained_trans` establish the expected reflexive/transitive/equivalence and strict-order laws. These are semantic set relations, not effective tests.

### 7.2 Noncomputable relabeling

#### `AlmostOrder`

For a family `langs : Fin (N+1) → Set α`, `AlmostOrder langs` is a wrapper structure containing one original index. A noncomputable partial-order instance declares `i ≤ j` exactly when either the wrapped indices are equal or the corresponding languages are strictly almost-contained in the forward direction. Almost-equivalent and incomparable languages remain incomparable at the partial-order level.

#### `almostOrderIso`

`almostOrderIso langs` is a noncomputably selected order isomorphism from `Fin (N+1)` to a linear extension of that finite partial order. It uses only finiteness and classical selection; no algorithm for comparing arbitrary sets is asserted.

#### `relabeledIndex` and `topologicallyRelabeled`

`relabeledIndex langs i` is the original index occupying position `i` in the chosen linear extension. `topologicallyRelabeled langs i` is `langs (relabeledIndex langs i)`.

`relabeledIndex_bijective` states that the relabeling map is bijective. `range_topologicallyRelabeled` states exact equality of represented collections:

`Set.range (topologicallyRelabeled langs) = Set.range langs`.

Repeated equal languages remain as repeated indices even though set range forgets multiplicity.

#### `strictAlmostContained_implies_lt_relabel`

For the relabeled family, whenever the language at index `i` is strictly almost-contained in the language at index `j`, one has `i < j`. Classification: semantic finite-order theorem about the noncomputably selected relabeling.

### 7.3 Incremental learner and run

#### `IncrementalLearner`

`IncrementalLearner α ι` is `ι → α → ι`. Its persistent state is exactly its previous output in `ι`; on each update it receives that state and the current example. It does not receive the target, time, complete history, future data, or a separate work tape.

#### `incrementalRun`

For learner, initial state, and stream, the run is defined by:

- state `0` is `initial`;
- state `t+1` is `learner (state t) (stream t)`.

Thus state `t` has processed exactly the first `t` observations. The initial state is an existentially selected index in later success predicates.

#### `nextIndex`

On `Fin (N+1)`, `nextIndex i` increments the numerical index by one when `i.val < N` and otherwise leaves the final index fixed. `nextIndex_eq_self_iff`, `nextIndex_val_le`, and `nextIndex_ge` respectively characterize the fixed point, bound the step by one, and prove monotonicity.

#### `orderedIncrementalLearner`

For a family `langs`, the learner maps `(i,x)` to `i` if `x ∈ langs i`, and to `nextIndex i` otherwise. This is noncomputable because membership in arbitrary sets is used with classical decidability. The family is compiled into the learner; no membership oracle is an input.

`orderedIncrementalLearner_ge` and `orderedIncrementalLearner_val_le_succ` say that a single update never decreases the index and increases it by at most one. `orderedIncrementalRun_monotone` and `orderedIncrementalRun_step_le` lift these facts to the run from initial index `0`.

#### `monotone_fin_eventually_constant`

For every monotone function `f : ℕ → Fin (n+1)`, there exist a time `T` and value `m` such that `f t = m` for every `t ≥ T`. This is finite-state compactness; it contains no convergence rate.

#### `adjacent_run_hits`

If `f : ℕ → Fin (N+1)` starts at `0`, increases by at most one in numerical value at each step, and at time `T` has value at least `z.val`, then some `t ≤ T` satisfies `f t = z`. This prevents skipped indices. It is deterministic and finite combinatorics.

### 7.4 Identification criteria and conclusions

#### `ApproximatelyIdentifiesRun`

Given `langs`, learner, initial index, target index, and stream, the run approximately identifies the target when there exists `T` such that for every `t ≥ T`, the language indexed by the current state is `AlmostEquivalent` to the target language. The predicate itself neither requires the state to stabilize nor requires it to equal the target index. Separately, the ordered-run declarations establish monotonicity and eventual constancy for their displayed candidate.

#### `IncrementallyApproximatelyIdentifiable`

A family is incrementally approximately identifiable if there exist one learner and one initial index such that, for every target index and every exact presentation of its language, the corresponding run eventually outputs only almost-equivalent languages. There is **no** finite-repetition or injectivity restriction: arbitrary repetitions are allowed. The learner may depend on the entire indexed family.

#### `ordered_run_target_absorbing`

For the ordered learner, if a stream stays inside `langs target` and the run reaches `target` at time `t`, then it remains exactly at `target` at every later time. The assumption is only `StreamIn`, not exact presentation.

#### `theorem_5_2_ordered`

For any finite indexed family, if its indices satisfy the supplied topological condition

`StrictAlmostContained (langs i) (langs j) → i < j`

for all `i,j`, then the family is incrementally approximately identifiable. No language infinitude, countability of `α`, finite-repetition condition, oracle, or effectiveness assumption appears. The result type is existential and does not expose its learner. Classification: semantic, non-effective existence theorem.

#### `theorem_5_2`

For every `raw : Fin (N+1) → Set α` and every supplied proof that each `raw i` is infinite, there exists a family `langs` such that:

1. `Set.range langs = Set.range raw`; and
2. `langs` is incrementally approximately identifiable.

The infinitude hypothesis is redundant relative to the separately exported relabeling declarations and `theorem_5_2_ordered`, which have no infinitude premise. The theorem's own conclusion records only set-range equality; it does **not** state that the existential `langs` is a permutation of `raw`. Separately, `relabeledIndex_bijective` and `range_topologicallyRelabeled` exhibit a bijective reindexing with the required range, and `strictAlmostContained_implies_lt_relabel` together with `theorem_5_2_ordered` certifies that displayed candidate. No computable topological sorting or membership decision is established.

## 8. Exact incremental identification obstruction

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/ExactIdentificationObstruction.lean`

#### `exactPrepend`

`exactPrepend head tail` is the stream with first value `head` and subsequent values from `tail`. It is extensionally the same stream combinator as the public `prepend` in the earlier module, but is separately defined here. The local supporting lemmas show that it presents `insert head K` when the tail presents `K`, and preserves finite repetition.

#### `ExactlyIdentifiesRun`

For an incremental learner, initial state, target state, and stream, `ExactlyIdentifiesRun` means that there exists `T` such that the run state is **equal to the target index** for every `t ≥ T`. This is index equality, not language equality and not almost-equivalence.

#### `IncrementallyExactlyIdentifiableOnFinitelyRepeating`

For `langs : ι → Set α`, the predicate means there exist one learner `ι → α → ι` and one initial state such that, for every target index and every stream, exact presentation plus finite repetition imply eventual exact equality of the run state to that target. The state type is exactly `ι`; no larger hidden-state type, auxiliary memory, or synonym output index is allowed.

#### `incrementalRun_prepend`

For every learner, initial state, head, tail, and time `t`, the state after `t+1` observations on the prepended stream equals the state after `t` observations on the tail when initialized at `learner initial head`. This is an exact run-alignment identity.

#### `states_distinct_of_aligned_exact_runs`

Suppose two full streams, after offsets `offset₁` and `offset₂`, are aligned with runs on the same tail from states `state₁` and `state₂`. If the two full runs exactly converge to distinct target indices, then `state₁ ≠ state₂`. All alignment equations are universally quantified over tail time. The theorem is a deterministic indistinguishability principle: equal states plus an identical future would force identical future behavior.

#### `exactObstructionCore` and `exactObstructionCoreStream`

`exactObstructionCore` is the range of `n ↦ 3n`. `exactObstructionCoreStream n = 3n`. The declarations `exactObstructionCoreStream_injective`, `exactObstructionCoreStream_presents`, `exactObstructionCoreStream_finitelyRepeating`, and `exactObstructionCore_infinite` state that this stream is injective, exactly presents the core, is finitely repeating, and the core is infinite. Separate lemmas state that `1` and `2` are outside the core.

#### `exactObstructionLanguages`

The indexed family on `Fin 3` is:

- index `0`: `exactObstructionCore ∪ {1}`;
- index `1`: `exactObstructionCore ∪ {2}`;
- index `2`: `exactObstructionCore ∪ {1,2}`.

`exactObstructionLanguages_infinite` states every member is infinite. `exactObstructionLanguages_injective` states that the indexing is injective, hence the family has exactly three distinct represented sets.

#### `proposition_5_1`

The declaration is the conjunction:

1. every displayed obstruction language is infinite;
2. the language-indexing function is injective; and
3. the family is **not** incrementally exactly identifiable on finitely repeating exact presentations.

The negative clause quantifies over every learner whose state/output type is precisely `Fin 3` and every initial `Fin 3` state. The adversary may choose the target and stream after seeing the learner. The result does not exclude a learner with more than three states, hidden work memory, synonym indices, an encoded natural output, or a non-index state. It is semantic and contains no runtime bound.

## 9. Incremental index-generation obstruction

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalIndexObstruction.lean`

### 9.1 Interface

#### `IncrementalIndexGeneratesRun`

For a family `langs : ι → Set α`, incremental generator, initial index, target index, and stream, this predicate means there exists `T` such that, for every `t ≥ T`,

`langs (incrementalRun generator initial stream t) ⊆ langs target`.

The state and emitted index are the same `ι`. Exact target-index convergence is not required unless the family has no nontrivial containment.

#### `IncrementallyIndexGenerableOnFinitelyRepeating`

The family has this property if there exist one incremental generator and one initial index such that every exact finitely repeating presentation of every target eventually satisfies the preceding one-sided language containment. The target is not given to the generator.

#### `incrementalIndexGeneratesRun_exact_of_antichain`

If a supplied hypothesis says `langs i ⊆ langs j → i = j` for every pair of indices, then any run satisfying incremental index generation for target `target` also exactly identifies `target`. This converts one-sided validity to exact state convergence on an inclusion antichain. The hypothesis is stronger than injectivity: it rules out containment between distinct entries.

### 9.2 Finite-prefix alignment

#### `prefixStream`, `prefixState`, and `prefixSupport`

For a finite list `xs` and infinite tail:

- `prefixStream xs tail` prepends the list entries in order before the tail;
- `prefixState generator initial xs` is the state reached by feeding the list in order;
- `prefixSupport xs K` is `K` with all list entries inserted.

`prefixStream_presents` says that if the tail presents `K`, the prefixed stream presents `prefixSupport xs K`. `prefixStream_finitelyRepeating` preserves finite repetition. `incrementalRun_prefixStream` states that after `xs.length + t` steps on the prefixed stream, the state equals the state after `t` steps on the tail initialized at `prefixState generator initial xs`. These statements permit exact comparison of runs with different finite prefixes and the same future.

The finite-state combinatorial declarations `fin3_exhaust_of_pairwise`, `fin3_eq_first_of_ne`, and `fin3_two_permutations` characterize how three pairwise distinct values exhaust `Fin 3` and constrain two triples of pairwise distinct states. They make no mathematical assumption beyond the cardinality of `Fin 3`.

### 9.3 Triangle family and conclusions

#### `appendixTriangleLanguages`

Given a set `T` and points `a,b,c`, the `Fin 3` family is:

- index `0`: `T ∪ {a,b}`;
- index `1`: `T ∪ {a,c}`;
- index `2`: `T ∪ {b,c}`.

#### `appendixTriangleLanguages_infinite`

If `T` is infinite, then every one of the three languages is infinite, for arbitrary `a,b,c`.

#### `appendixTriangleLanguages_antichain`

If `a,b,c` are pairwise distinct and none belongs to `T`, then for all indices `i,j`, containment of the `i`th triangle language in the `j`th implies `i = j`. Thus the indexed family is an inclusion antichain. No countability assumption is needed for this set-theoretic statement.

#### `proposition_A_2`

Assume `[Countable α]`, an infinite `T : Set α`, pairwise distinct `a,b,c`, and `a,b,c ∉ T`. Then the triangle family is **not** incrementally index-generable on finitely repeating exact presentations. The state/output type is exactly `Fin 3`. The statement is stronger than a failure of exact identification because its success predicate asks only eventual containment; antichainhood forces equality. It remains representation-sensitive and non-effective.

#### `theorem_A_1_triangle`

Under the same countability, infinitude, distinctness, and exclusion assumptions, the triangle family is not incrementally exactly identifiable on finitely repeating presentations. This follows semantically because exact identification would imply index-generation validity. It does not add a larger-state impossibility.

#### `theorem_A_1`

There exists an injectively indexed family `langs : Fin 3 → Set ℕ` such that every language is infinite and the family is not incrementally exactly identifiable on finitely repeating exact presentations. The witness is existential in the statement; no target or presentation is fixed in advance. Again, the learner is restricted to exactly three index states.

## 10. Incremental element coding and generation

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalElementCoding.lean`

This module is fixed to examples and output states in `ℕ`. Its central construction is semantically important for the memory audit: a generated natural number is used simultaneously as the emitted target element and as an unbounded code for the full observed history.

### 10.1 Codebook

#### `ElementCodeRequest`

For `N`, an `ElementCodeRequest N` is a triple consisting of an index `i : Fin (N+1)`, a finite list `history : List ℕ`, and a natural `salt`. The projections used in the file make this formally `Fin (N+1) × (List ℕ × ℕ)`.

#### `defaultElementCodeRequest` and `elementCodeRequestAt`

The default request is `(0, [], 0)`. `elementCodeRequestAt r` decodes the natural number `r` through Lean's `Encodable.decode`, using the default if decoding fails. `elementCodeRequestAt_encode` says that encoding any valid request and then applying this decoder returns exactly that request. These are representation-level mathematical encodings, not bit-complexity claims.

#### `freshElementCode`

Given a finite family `langs`, proofs that every language is infinite, a request-code stage `r`, and a finite set `used`, `freshElementCode` noncomputably chooses a point in the language named by the decoded request at `r` that is outside both `used` and `Finset.range (r+1)`. Thus it is greater than `r` and globally fresh relative to the supplied finite set. Choice depends extensionally on arbitrary infinite sets.

The associated theorems `freshElementCode_mem`, `freshElementCode_not_mem`, and `freshElementCode_gt` state exactly these three properties.

#### `elementCodeUsed` and `elementCodewordAt`

`elementCodeUsed langs hInfinite r` recursively records the finite set of codewords allocated at stages below `r`. `elementCodewordAt langs hInfinite r` is the fresh point selected at stage `r` against that set.

The substantive invariants are:

- `elementCodewordAt_mem`: the codeword at `r` lies in the language named by `elementCodeRequestAt r`;
- `elementCodewordAt_not_used`: it was not allocated at an earlier stage;
- `elementCodewordAt_gt`: it is numerically greater than `r`;
- `elementCodeUsed_mono`: earlier used sets are included in later ones;
- `earlier_elementCodeword_used`: a codeword from stage `r` belongs to every later used set at stage `s > r`;
- `elementCodewordAt_injective`: distinct request-code stages receive distinct natural numbers.

All are semantic consequences of a noncomputable global allocation.

#### `elementCode`

`elementCode langs hInfinite i history salt` is the codeword at the natural encoding of the triple `(i,history,salt)`.

- `elementCode_mem` says every such code belongs to `langs i`.
- `elementCode_triple_injective` says the map from the full triple to its natural codeword is injective.
- `elementCode_salt_injective` says that for fixed `i` and history, varying the salt gives distinct codewords.
- `exists_elementCode_gt` says that for every numerical bound there is a salt whose codeword is above the bound.
- `nextElementCodeSalt` chooses the least such salt noncomputably, and `nextElementCode_gt` records the strict inequality.

These declarations establish an unbounded, lossless, language-respecting code space. They do not establish efficient encoding, decoding, or membership.

#### `elementCodingCell`

For index `i`, `elementCodingCell` is the range of `salt ↦ elementCode i [] salt`. The theorems state that each cell is infinite, lies inside `langs i`, distinct-index cells are pairwise disjoint, and each cell is cofinal in the natural-number order. These are stronger coding resources than merely choosing one element from each language.

### 10.2 Full-history premise and incremental element success

#### `elementHistoryPrefix`

`elementHistoryPrefix stream t` is the list of the first `t` stream values, in chronological order. Its zero and successor lemmas identify the empty prefix and append the current value at the end.

#### `FullInformationIndexLearner`

A full-information index learner is an arbitrary function `List ℕ → Fin (N+1)`. It receives the entire finite history as a list.

#### `EventuallyAlmostContainedHypotheses`

For `langs` and a full-history learner `M`, this predicate means: for every target index and every exact presentation of its target language, there exists `T` such that for all `t ≥ T`,

`AlmostContained (langs (M (elementHistoryPrefix stream t))) (langs target)`.

Only one-sided almost-containment is required. There is no finite-repetition assumption, no computability, and no bound on when stabilization occurs.

#### `IncrementalElementGeneratesRun`

For a target set, incremental learner `G : ℕ → ℕ → ℕ`, initial natural state, and stream, success means that there exists `T` such that for every `t ≥ T`, the state after the first `t` observations belongs to

`target \ Set.range (fun s : Fin t => stream s)`.

Thus the state itself is the generated element, it lies in the target, and it is absent from every observation seen so far. At time `t` the next input `stream t` has not yet been processed.

#### `IncrementallyElementGenerable`

A family `langs : Fin (N+1) → Set ℕ` is incrementally element-generable if there exist one natural-state incremental learner and one initial natural number such that every target and every exact presentation satisfy `IncrementalElementGeneratesRun`. Repetitions are unrestricted. The state space is all of `ℕ`, not the finite language-index type.

### 10.3 Compiler

#### `decodeElementCode`

This noncomputable total function is `Function.invFun` of the injective request-to-codeword map. On valid codewords, `decodeElementCode_code` says it returns the exact `(index,history,salt)` request. On natural numbers outside the codeword range, its behavior is unspecified by any semantic guarantee.

#### `codingCompiledGenerator`

Given `langs`, infinitude proofs, and a full-history learner `M`, the compiled update on previous natural state `state` and current input `x`:

1. decodes `state` to a prior request;
2. takes the decoded history and appends `x`;
3. asks `M` for an index on that full history;
4. chooses a salt whose corresponding codeword is above `max state x`; and
5. returns that codeword.

The update has only the formal incremental inputs `(state,x)`, but the state is a lossless code for the unbounded history along intended runs. The construction is noncomputable and family-specific.

#### `codingCompiledInitial`

The initial state is the codeword for `(M [], [], 0)`. Hence it is already a valid code.

#### Run invariants

- `codingCompiledGenerator_gt_state` and `codingCompiledGenerator_gt_input` say each update is strictly larger than both the preceding state and current datum.
- `codingCompiled_run_is_code` says that at every time `t` there exists a salt such that the run state is exactly the code for `M`'s hypothesis on the exact first-`t` history and that same history.
- `codingCompiled_run_gt_seen` says every earlier observed value `stream s`, for `s < t`, is strictly below the state at time `t`.
- `codingCompiled_run_fresh` concludes the state is absent from the range of all first-`t` observations.
- `codingCompiled_time_le_run` says the state at time `t` is at least `t`, providing escape from every fixed finite set.

These declarations formally expose the answer-encoding mechanism. The model is “incremental” in arity, but not bounded in information content: natural-valued states can carry arbitrarily long histories.

#### `elementCodingBadSet`

For a target index, this is the union over all indices `i` of `langs i \ langs target` when `langs i` is almost-contained in the target, and `∅` otherwise. Since the index type is finite and each included difference is finite, `elementCodingBadSet_finite` says the union is finite. `mem_elementCodingBadSet` gives the corresponding membership introduction rule.

#### `incremental_coding_compilation`

For a finite nonempty family of infinite languages, a full-history learner `M`, and the hypothesis `EventuallyAlmostContainedHypotheses langs M`, the family is incrementally element-generable.

Quantifier/access audit: `M` may inspect the entire finite history and may be noncomputable; the compiler stores that history in its natural-valued output. Eventual one-sided errors form a finite bad set, and the increasing code eventually escapes it. The theorem is semantic and conditional, with no machine-level memory or runtime bound.

#### `incrementalLearnerOnHistory`

This definition replays an incremental learner on a finite list by `foldl`, starting from its initial state. `incrementalLearnerOnHistory_prefix` identifies this replay with `incrementalRun` on the corresponding stream prefix.

#### `incremental_element_generation_of_approximate_identification`

If every language is infinite and the family is incrementally approximately identifiable, then it is incrementally element-generable. The approximate learner is replayed as a full-history learner; mutual almost-equivalence supplies the one-sided premise required by the compiler. No presentation restriction is added.

#### `incrementallyElementGenerable_of_range_eq`

If two `Fin (N+1)`-indexed families have equal set ranges and the first is incrementally element-generable, then the second is also incrementally element-generable. The same natural-state generator and initial state are reused after selecting an index representing the same target set. This transfer is extensional in the represented collection and tolerates duplicate indices.

#### `incremental_element_generation`

For every `raw : Fin (N+1) → Set ℕ`, if every `raw i` is infinite, then `raw` is incrementally element-generable against **all** exact presentations.

This is a positive semantic theorem for every nonempty finite family. It does not contradict the three-index exact-identification obstruction because the state/output type here is `ℕ`, not `Fin (N+1)`, and the codeword state carries the full history. It asserts no computability, finite-bit memory, output-size bound, membership oracle, or runtime bound.

## 11. Ordered-density interfaces and canonical memoryless generator

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/MemorylessDensity.lean`

### 11.1 Monotonicity

`orderedPrefixCount_mono`, `orderedPrefixRatio_mono`, `orderedLowerDensity_mono`, and `orderedUpperDensity_mono` state, in that order, that set inclusion `A ⊆ B` implies monotonicity of every finite prefix count, every finite prefix ratio, lower density, and upper density relative to the same `OrderedLanguage K`. These are extensional analytic facts. No measurability or probability structure is involved.

### 11.2 Repetition-free success and finite bad inputs

#### `IsRepetitionFreeMemorylessGeneratorOn`

For `G : ℕ → Set ℕ` and one target `K`, this predicate means: every injective exact presentation of `K` has an eventual threshold after which `G (stream t)` is an infinite subset of `K`. Binder order is stream, presentation proof, injectivity proof, then threshold. An injective exact presentation exists only when `K` is infinite.

#### `densityBadInputs`

`densityBadInputs G K` is `{x | x ∈ K ∧ ¬ G x ⊆ K}`. It records containment failure but not output finiteness. Under a `WindowSetGenerator` or the canonical generator, infinitude is handled separately.

#### `densityBadInputs_finite`

If `K` is infinite and `G` succeeds on every repetition-free exact presentation of `K`, then `densityBadInputs G K` is finite. This converts an eventual property quantified over all injective enumerations into a pointwise finite-exception statement. Classification: semantic necessity; the bad set may depend on `G` and `K` and is not effectively computed.

### 11.3 Finite partitions and lower-density bound

#### `IsFinitePartition`

For `pieces : Fin (m+1) → Set ℕ` and `K`, this is the conjunction that distinct pieces are disjoint and their indexed union equals `K`. All `m+1` entries are present, but the definition itself does not require nonemptiness or infinitude.

#### `partitionBadInputs`

This is the union, over all piece indices, of `densityBadInputs G (pieces i)`. `partitionBadInputs_finite` says it is finite if every piece is infinite and `G` succeeds repetition-freely on every piece.

#### `maximumPartitionLowerDensity`

For an ordered language `K`, this noncomputable real is the maximum, over the nonempty finite index type `Fin (m+1)`, of `K.lowerDensity (pieces i)`. `piece_lowerDensity_le_maximum` gives the defining upper bound for each piece.

#### `lemma_4_3_lower_density_bound_from_partition`

Given, in order:

1. `K : OrderedLanguage`;
2. `pieces : Fin (m+1) → Set ℕ`;
3. a proof that the pieces form a finite partition of `K.carrier`;
4. a proof that every piece is infinite;
5. a memoryless set generator `G`;
6. proofs that `G` succeeds on every piece for all injective exact presentations;
7. a stream presenting `K.carrier`; and
8. proof that this stream is injective,

there exists `T` such that for every `t ≥ T`,

`K.lowerDensity (G (stream t)) ≤ maximumPartitionLowerDensity K pieces`.

The generator is not assumed successful on the whole carrier, only on each piece. The formal hypothesis `IsFinitePartition` includes both pairwise disjointness and exact coverage; both remain part of this theorem's stated assumptions. Classification: conditional semantic density theorem.

### 11.4 Finite-family core and canonical generator

#### `finiteFamilySignature`

For a finite family and point `x`, this noncomputable finite set contains exactly the indices whose language contains `x`.

#### `finiteFamilyIntersection`

For a finite signature, this is the set of all `y` belonging to every indexed language in the signature. For the empty signature it is universal.

#### `finiteFamilyCore`

`finiteFamilyCore langs x = {y | ∀ i, x ∈ langs i → y ∈ langs i}`. It is the intersection of all members of the finite family containing `x`.

`finiteFamilyCore_eq_intersection` equates it with the signature intersection. `mem_finiteFamilyCore` says `x` belongs to its own core. `finiteFamilyCore_subset` says that whenever `x ∈ langs i`, the core is contained in `langs i`.

#### `canonicalDensityGenerator`

For a finite nonempty indexed family, the noncomputable memoryless function outputs `finiteFamilyCore langs x` if that core is infinite, and outputs `Set.univ` otherwise. The fallback makes every output infinite but may be invalid for any particular target. The current point is the only runtime input; the whole family and an infinitude test are embedded in the function.

`canonicalDensityGenerator_infinite` says every output is infinite, unconditionally.

#### `finiteSignaturePiece` and `finiteCoreInputs`

`finiteSignaturePiece` keeps a finite family intersection exactly when it is finite and otherwise returns `∅`. `finiteCoreInputs` is the set of `x` for which `finiteFamilyCore langs x` is finite. The declarations `finiteSignaturePiece_finite` and `finiteCoreInputs_finite` show each kept piece and the global set of finite-core inputs are finite. Finiteness follows because the finite family has only finitely many signatures.

#### `canonicalDensityGenerator_succeeds`

For every `langs : Fin (m+1) → Set ℕ`, with **no explicit infinitude assumption**, the canonical generator is a successful finitely-repeating memoryless generator on `Set.range langs`.

The absence of an infinitude hypothesis is partly substantive and partly vacuous: if a target language is finite, no infinite-time stream can both present it exactly and be finitely repeating, so that target contributes no runs to the success predicate. For any actual finitely repeating exact presentation, the stream eventually avoids the finite set of inputs with finite core, after which the core is infinite and contained in the target. The theorem is noncomputable and semantic.

## 12. Partition into infinite zero-lower-density pieces

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/ZeroDensityPartition.lean`

#### `paperBlockBoundary`

This recursively defined sequence satisfies

- `paperBlockBoundary 0 = 0`;
- `paperBlockBoundary (t+1) = paperBlockBoundary t + (t+1)^2(1+paperBlockBoundary t)`.

`paperBlockBoundary_lt_succ` and `paperBlockBoundary_strictMono` state strict growth; `paperBlockBoundary_index_le` states `t ≤ paperBlockBoundary t`; and `paperBlockBoundary_unbounded` states that for every `n` some next boundary exceeds `n`. These are explicit arithmetic properties, with no asymptotic assumption supplied externally.

#### `paperBlockIndex`

For each position `n`, `paperBlockIndex n` is the least `t` such that `n < paperBlockBoundary (t+1)`. It is declared noncomputable through `Nat.find`, although the recurrence is arithmetical. `paperBlockIndex_bounds` states that `n` lies in the half-open block

`[paperBlockBoundary (paperBlockIndex n), paperBlockBoundary (paperBlockIndex n + 1))`.

`paperBlockIndex_boundary` says that the boundary at index `t` belongs to block `t`.

#### `paperZeroDensityPiece`

For an ordered language `K`, a positive-or-zero natural `m`, and `i : Fin m`, the piece consists of those carrier elements whose unique enumeration position `n` has block index congruent to `i.val mod m`. Since an inhabitant `i : Fin m` can exist only when `m > 0`, the definition is well typed without a separate positivity premise.

`enumeration_mem_paperZeroDensityPiece_iff` gives the exact residue test at an enumeration position. `paperZeroDensityPiece_subset_carrier` proves containment in `K.carrier`.

#### Partition properties

- `paperZeroDensityPieces_pairwiseDisjoint` says distinct residue indices give disjoint pieces, for any `m`.
- `paperZeroDensityPieces_cover` assumes `0 < m` and says their indexed union equals `K.carrier`.
- `paperZeroDensityPiece_infinite` assumes `0 < m` and says every piece is infinite.

The pieces depend on the supplied density ordering, not merely on the carrier set.

#### Density estimates

`prefixCount_paperZeroDensityPiece_le` says that at the end of a block `t` owned by another residue, the count of the chosen piece is at most the preceding boundary. `paperBlockBoundary_ratio_le` bounds the ratio of consecutive boundaries by `1/(t+1)`. `prefixRatio_paperZeroDensityPiece_le` combines these into a corresponding prefix-ratio bound.

`frequently_prefixRatio_paperZeroDensityPiece_le` states that when `m ≥ 2`, for every piece and every `ε > 0`, arbitrarily late prefix lengths have ratio at most `ε`. This is a frequent smallness statement, not convergence of the ratio to zero.

#### `paperZeroDensityPiece_lowerDensity`

For `m ≥ 2`, every piece has lower density exactly `0` in `K`'s ordering. Nonnegativity supplies the reverse inequality. Upper density is not asserted to be zero.

#### `lemma_4_4_zero_lower_density_partition`

For every `OrderedLanguage K`, every natural `m`, and proof `2 ≤ m`, there exists `pieces : Fin m → Set ℕ` such that:

1. distinct pieces are disjoint;
2. their union is exactly `K.carrier`;
3. every piece is infinite; and
4. every piece has `K.lowerDensity = 0`.

The existential conclusion itself does not name its witness. The preceding public declarations jointly certify that `paperZeroDensityPiece K m` has all four displayed properties. The theorem is semantic/analytic, not probabilistic. It requires the ordering contained in `K`; it does not claim that one partition works simultaneously for all orderings of the same carrier.

## 13. Symmetric-chain decomposition of finite Boolean lattices

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/SymmetricChain.lean`

This is a primary combinatorial support module. It makes no language-generation or stream claim by itself.

### 13.1 Canonical ground set `Finset.range n`

#### `IsSymmetricChain`

For `n` and a finite set `C` of finite subsets of `ℕ`, the predicate is the conjunction:

1. every `A ∈ C` is contained in `Finset.range n`;
2. every two `A,B ∈ C` are comparable by inclusion; and
3. there exists `low` such that:
   - `2*low ≤ n`;
   - every member has cardinality between `low` and `n-low`; and
   - for every rank `r` in that interval, some `A ∈ C` has cardinality `r`.

The definition does not explicitly state uniqueness at each rank, but chain comparability plus equal cardinality forces it via later theorems. It is a saturated symmetric chain in rank terms.

#### `Decomposition`

A `Decomposition n` contains a finite set `chains` such that every member satisfies `IsSymmetricChain n`, and every finite subset `A ⊆ Finset.range n` belongs to exactly one chain. The `existsUnique_mem` field is the partition property.

#### `RankWitness`, `chainLow`, `chainTop`, and `chainMiddle`

`RankWitness n C low` packages the rank interval conditions. `chainLow` noncomputably chooses a valid lower rank when one exists; `chainLow_spec`, `chainLow_twice_le`, `chainLow_card_bounds`, and `chainLow_rank_exists` expose its properties for a symmetric chain.

`chainTop` noncomputably chooses the unique member at rank `n - chainLow n C`; `chainTop_spec`, `chainTop_subset_range`, `eq_chainTop_of_mem_of_card_eq`, `mem_ne_top_card_lt`, and `mem_subset_chainTop` state its membership, rank, uniqueness, and maximality.

`chainMiddle` chooses the member at rank `n/2`; `chainMiddle_spec`, `eq_of_mem_chain_of_card_eq`, and `chainMiddle_unique` state existence and uniqueness. These choices are mathematical, not executable data structures.

#### `longCarrier` and `shortCarrier`

For a symmetric chain on `range n`:

- `longCarrier n C` keeps all old members and adds `n` to the old top;
- `shortCarrier n C` takes every non-top old member and inserts `n`.

`longCarrier_symmetric` says the long carrier is symmetric on `range (n+1)`. `shortCarrier_symmetric` says the short carrier is symmetric when `2*chainLow n C < n`. `long_short_disjoint` states the two carriers are disjoint. Supporting declarations characterize membership, erasure of the new element, and preservation of inclusions and cardinalities.

#### `nextChains` and `nextDecomposition`

`nextChains D` is the union of all long carriers of old chains and the short carriers of exactly those old chains satisfying the split inequality. `nextChains_finite` and `nextChains_chain_spec` give finiteness and symmetry. `nextDecomposition D` packages these chains into a `Decomposition (n+1)` and asserts unique coverage of every subset of `range (n+1)`.

#### `zeroDecomposition` and `rangeDecomposition`

`zeroDecomposition` has the single chain containing the empty set. `rangeDecomposition` recursively applies `nextDecomposition`, producing a decomposition for every `n`. Although some component choices are noncomputable, the statement is a concrete recursive existence construction at the finite-set level.

#### `decomposition_ncard`

For **every** `Decomposition n`, the finite number of chains is exactly

`Nat.choose n (n/2)`.

The count is forced by the unique middle-rank member in every chain and unique coverage of the middle layer. It is not merely an upper or lower bound.

#### `symmetric_chain_decomposition_range`

For every `n`, there exists `D : Decomposition n` whose chain count is exactly `Nat.choose n (n/2)`. Since `decomposition_ncard` applies to every decomposition, the numerical clause is not an extra witness constraint but an exact property.

### 13.2 Arbitrary finite ground type

#### `IsFintypeSymmetricChain`

For a finite type `α`, this is the same chain/rank condition with `Fintype.card α` replacing `n`; there is no separate carrier-subset condition because all finite subsets are subsets of the whole type.

#### `FintypeDecomposition`

This structure contains finitely many such chains and requires every `Finset α` to belong to exactly one chain.

#### Encoding and transport declarations

`codeEmbedding`, `decodeFinset`, `decodeCarrier`, and `decodeChains` transport the canonical decomposition on `range (Fintype.card α)` to `α` through a selected equivalence with a finite ordinal. The associated injectivity, cardinality, subset, and symmetry theorems ensure no sets or chains are merged. These declarations use a noncomputable finite equivalence but preserve exact combinatorial structure.

#### `fintypeDecomposition` and `fintypeDecomposition_ncard`

For every finite type `α`, `fintypeDecomposition α` is a decomposition of its Boolean lattice, and its number of chains is

`Nat.choose (Fintype.card α) (Fintype.card α / 2)`.

#### `symmetric_chain_decomposition_fintype`

For every type `α` with `[Fintype α]`, there exists a `FintypeDecomposition α` with exactly the central-binomial number of chains. There are no decidability, order, or countability hypotheses beyond the finite-type instance. Classification: finite combinatorial existence theorem; non-probabilistic and not a runtime statement.

## 14. Sperner-type hard instance for memoryless upper density

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/SpernerHardInstance.lean`

### 14.1 Uniform pieces

#### `spernerTargetOrder`

This `OrderedLanguage` has carrier `Set.univ`, identity enumeration, injectivity by identity, and range equal to the universe. Density is therefore ordinary density in initial natural-number intervals.

#### `roundRobinPiece`

For `i : Fin N`, `roundRobinPiece i = {x | x mod N = i.val}`. Distinct pieces are pairwise disjoint (`roundRobinPieces_pairwiseDisjoint`); if `N > 0` they cover `ℕ` (`roundRobinPieces_cover`) and each is infinite (`roundRobinPiece_infinite`).

The prefix-count bounds imply `prefixRatio_roundRobin_bounds`: for positive `n`, the ratio lies between `1/N - 1/n` and `1/N + 1/n`. Consequently `tendsto_prefixRatio_roundRobin` gives convergence to `1/N`, and `roundRobinPiece_upperDensity` states exact upper density `1/N` in `spernerTargetOrder`. The same convergence also fixes the lower density, although no separate declaration here states it.

### 14.2 Middle-layer signatures

#### `middleLayer`

`middleLayer n` is the finite set of all subsets of `Fin n` with cardinality `n/2`. `middleLayer_card` states that its cardinality is `Nat.choose n (n/2)`, and `middleWidth_pos` states this number is positive for every `n`.

#### `middleSignature`

This noncomputable function bijectively enumerates the middle layer by `Fin (Nat.choose n (n/2))`. The declarations state:

- `middleSignature_mem`: every enumerated signature belongs to the middle layer;
- `middleSignature_card`: every signature has size `n/2`;
- `middleSignature_injective`: different indices have different signatures;
- `middleSignature_surjective`: every subset of `Fin n` of size `n/2` is some signature;
- `middleSignature_eq_of_subset`: inclusion between two enumerated signatures forces equality of their indices.

The last statement is the antichain property, obtained from equal cardinalities rather than assumed as an axiom.

For `n ≥ 2`, `exists_middleSignature_not_mem` says that for every coordinate `j` some middle signature omits `j`. If `j ≠ ℓ`, `exists_middleSignature_mem_not_mem` gives a middle signature containing `j` and omitting `ℓ`.

### 14.3 Hard family

#### `spernerHardLanguage`

For coordinate `j : Fin n`, this language is the union of exactly those round-robin pieces whose middle signature contains `j`. `mem_spernerHardLanguage_iff` gives the existential owner/signature characterization.

For `n ≥ 2`, every hard language is infinite, is not universal, and the map `j ↦ spernerHardLanguage n j` is injective (`spernerHardLanguage_infinite`, `spernerHardLanguage_ne_univ`, `spernerHardLanguage_injective`).

#### `spernerHardFamily`

This `Fin (n+1)` family places `Set.univ` at index `0` and the `n` side languages at successor indices. For `n ≥ 2`, `spernerHardFamily_injective` says all `n+1` languages are distinct, and `spernerHardFamily_infinite` says all are infinite.

#### Signature forcing

`mem_hardLanguage_iff_signature` identifies the unique owner of a number `x` as the residue `x mod Nat.choose n (n/2)` and says membership in side language `j` is exactly membership of `j` in that owner's signature.

`hardIntersection_subset_piece` says: for a fixed signature index `i`, the intersection of all side languages whose coordinates lie in `middleSignature n i` is contained in `roundRobinPiece i`. This is the forcing step; it is one-sided containment, not equality.

### 14.4 Bad inputs and eventual bound

#### `spernerTotalBadInputs`

For a memoryless set generator, this is the union of its containment-bad inputs over all members of the hard family.

#### `spernerTotalBadInputs_finite`

For `n ≥ 2`, if `G` succeeds under finitely repeating exact presentations on the range of `spernerHardFamily n`, then the total bad-input set is finite. This premise is stronger than repetition-free success: the public theorem `injective_finitelyRepeating` shows that every injective presentation belongs to the permitted finitely repeating class.

#### `output_subset_owner_piece`

For any `x` outside the total bad-input set, `G x` is contained in the unique round-robin piece owned by `x`. No success assumption appears directly in this theorem; finiteness and eventual avoidance enter in the next declaration.

#### `eventually_sperner_upperDensity_bound`

For `n ≥ 2`, any successful memoryless set generator on the hard family, any stream, a supplied proof that the stream presents the universal target, and injectivity of the stream, there exists `T` such that for all `t ≥ T`,

`upperDensity (G (stream t)) ≤ 1 / Nat.choose n (n/2)`

in the identity target order. The exact-presentation and injectivity premises are both part of the theorem's formal binder structure. The conclusion is an eventual pointwise density bound along that supplied stream.

#### `twoHardFamily`

For the two-language endpoint, index `0` is universal and index `1` is the odd residue class modulo `2`. The family is injective and both languages are infinite. Its reciprocal-binomial bound is `1`, so the density upper bound is the universal trivial bound.

#### `lemma_4_7_sperner_hard_instance`

For every `k ≥ 2`, there exist, in this order, an `OrderedLanguage K`, an injective family `langs : Fin k → Set ℕ`, and a target index such that:

1. every language is infinite;
2. the target language equals `K.carrier`; and
3. for every memoryless set generator `G`, if `G` succeeds on the family under finitely repeating exact presentations, then for every stream presenting `K.carrier`, if the stream is injective, there exists a threshold after which every output has upper density at most
   `1 / Nat.choose (k-1) ((k-1)/2)`.

The hard family and target order are chosen before `G`; the stream is universally quantified after `G`. The theorem is an eventual pointwise upper bound, stronger than merely bounding the outer run `limsup`. It is semantic and fixed to `ℕ`; no computability, oracle, or runtime interface appears in the theorem type, and several surrounding candidate definitions are explicitly noncomputable.

## 15. Sperner achievability for the canonical memoryless generator

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/SpernerAchievability.lean`

### 15.1 Relative signatures

#### `OtherIndex`

For a target in a family indexed by `Fin (n+1)`, `OtherIndex target` is the subtype of indices unequal to the target. `otherIndex_card` states that this finite type has exactly `n` elements.

#### `relativeSignature`

For a point `x`, this noncomputable finite set contains exactly the non-target indices whose languages contain `x`. `mem_relativeSignature_iff` gives the pointwise membership equivalence.

#### `relativeRegion`

For signature `B`, the region consists of those `x` that lie in the target and have relative signature exactly `B`.

#### `relativeCore`

For signature `B`, the core consists of target points that lie in every non-target language indexed by `B`. Thus it is the target intersected with the upward intersection specified by `B`.

`relativeRegion_subset_target` and `relativeRegion_subset_relativeCore` state the obvious containments. `mem_relativeCore_iff_signature_superset` says that `x` lies in the core exactly when it lies in the target and its actual relative signature contains `B`.

#### `finiteFamilyCore_eq_relativeCore`

If `x` lies in exact relative region `B`, then the global finite-family core at `x` equals `relativeCore langs target B`. This is an exact equality of sets, not just containment.

### 15.2 Minimal infinite signatures

#### `infiniteRelativeSignatures`

This noncomputable finite set consists of all signatures `B` whose exact relative region is infinite.

#### `minimalInfiniteSignatures`

This keeps the inclusion-minimal members of `infiniteRelativeSignatures`. `minimalInfiniteRegion_infinite` says every selected signature indeed has an infinite exact region.

#### `minimalInfiniteSignatures_antichain`

The selected signatures form an antichain under subset inclusion. `minimalInfiniteSignatures_card_le` applies the finite Boolean-lattice bound and concludes that their number is at most `Nat.choose n (n/2)`.

#### `exists_minimalInfiniteSignature_subset`

If an exact relative region for `C` is infinite, then there exists `B` in the minimal infinite signatures with `B ⊆ C`. This is a finite minimal-element theorem; no choice over an infinite family is involved beyond classical decidability of set infinitude.

### 15.3 Upper-density calculus

`orderedPrefixCount_union_le`, `orderedPrefixRatio_union_le`, and `orderedUpperDensity_union_le` state finite subadditivity for two sets at the count, ratio, and upper-density levels.

`indexedUnion S sets` is the union over a finite index set `S`. `indexedUnion_finite` says a finite union of finite sets is finite. `orderedUpperDensity_indexedUnion_le_sum` states that the upper density of a finite indexed union is at most the sum of the component upper densities.

`orderedUpperDensity_finite_eq_zero` states that every finite subset has upper density zero in every `OrderedLanguage`. These are deterministic limsup facts.

### 15.4 Cover and large core

#### `finiteRelativeRegionEnvelope`

This is the finite union of all exact relative regions that are finite. `finiteRelativeRegionEnvelope_finite` asserts the union is finite.

#### `minimalInfiniteCoreUnion`

This is the union of the relative cores indexed by minimal infinite signatures.

#### `target_subset_finiteEnvelope_union_minimalCores`

Every target point belongs either to the finite-region envelope or to one of the minimal infinite cores. The statement is a one-sided cover of `langs target`.

#### `minimalInfiniteCoreUnion_upperDensity_eq_one`

If `K.carrier = langs target`, then the union of minimal infinite cores has upper density exactly `1` in `K`'s ordering. Since each core is contained in the target, this says a subset of the target loses only upper-density-zero mass; the finite envelope provides the omitted part.

#### `exists_minimalInfiniteCore_large_density`

Under the same carrier equality, there exists a minimal infinite signature `B` such that

`1 / Nat.choose n (n/2) ≤ K.upperDensity (relativeCore langs target B)`.

The quantifier is existential after `langs,target,K`; no algorithm for finding `B` is provided. The numerical lower bound is exactly the reciprocal central-binomial quantity shown above.

### 15.5 Recurrence and canonical output

#### `frequently_mem_infinite_subset_of_presents`

If a stream exactly presents `K`, `A` is infinite, and `A ⊆ K`, then `stream t ∈ A` occurs arbitrarily late. No finite-repetition assumption is needed: exact presentation of infinitely many distinct elements prevents all of `A` from appearing in one finite prefix.

#### `canonicalDensityGenerator_eq_relativeCore`

If `x` belongs to region `B` and `relativeCore langs target B` is infinite, then the canonical density generator's output at `x` equals that relative core. The fallback `Set.univ` is excluded by the supplied infinitude witness.

#### `canonicalDensityGenerator_frequently_sperner_dense`

For any finite family `langs : Fin (n+1) → Set ℕ`, target index, ordered language `K` whose carrier equals that target, stream, and exact-presentation proof, arbitrarily late times satisfy

`1 / Nat.choose n (n/2) ≤ K.upperDensity (canonicalDensityGenerator langs (stream t))`.

No injectivity, finite-repetition, or infinitude assumption on the non-target languages occurs. The target is automatically infinite because it is the carrier of an `OrderedLanguage`. The conclusion is frequent, not eventual.

#### `lemma_4_8_sperner_achievability`

For `n` with a supplied proof `1 ≤ n`, a family `langs : Fin (n+1) → Set ℕ`, and a supplied proof that every member is infinite, there exists a memoryless set generator `G` such that:

1. `G` succeeds on the family under finitely repeating exact presentations; and
2. for every target, every ordered realization `K` of that target, and every exact finitely repeating presentation, arbitrarily late outputs have upper density at least `1 / Nat.choose n (n/2)`.

The existential conclusion itself does not name `G`. However, the separately exported theorems `canonicalDensityGenerator_succeeds` and `canonicalDensityGenerator_frequently_sperner_dense` jointly certify `canonicalDensityGenerator langs` with strictly weaker premises: neither requires `1 ≤ n` or family-wide infinitude, and the frequent-density theorem requires exact presentation but not finite repetition. Thus those three assumptions are redundant relative to the stronger exported component statements, although they remain part of this declaration's quantifier structure. Classification: semantic, order-robust achievability; noncomputable and not runtime-bounded.

## 16. Memoryless minimax closure and lower-density obstruction

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/MinimaxClosure.lean`

### 16.1 Outer run density and guarantee

#### `memorylessRunUpperDensity`

For ordered target `K`, memoryless generator `G`, and stream, this real is

`limsup_t K.upperDensity (G (stream t))`.

It is an outer temporal `limsup` of inner ordered upper densities. It is not the density of a union of outputs and not an eventual infimum.

#### `MemorylessUpperDensityGuarantee`

For natural `k` and real `σ`, the guarantee has the following exact quantifier order:

1. for every `langs : Fin k → Set ℕ`;
2. if `langs` is injective;
3. and every `langs i` is infinite;
4. then there exists a family-specific memoryless set generator `G` such that:
   - `G` succeeds on `Set.range langs` under finitely repeating exact presentations; and
   - for every target index and every `OrderedLanguage K`, if `K.carrier = langs target`, then for every exact finitely repeating presentation of `K.carrier`,
     `σ ≤ memorylessRunUpperDensity K G stream`.

The adversary chooses the target, the duplicate-free density order, and the stream after `G` is selected. The generator does not receive any of them at runtime. The family is required to have exactly `k` distinct infinite languages through injectivity. For `k=0`, several quantifiers are vacuous; the main exact theorem excludes that case.

#### `memorylessAdmissibleUpperDensities`

This is the intersection of `[0,1]` with the set of reals satisfying the guarantee.

#### `memorylessMinimaxUpperDensity`

This is the real supremum `sSup` of the admissible set. It is noncomputable. The definition alone does not establish nonemptiness or boundedness; later declarations do so for the relevant values.

#### `memorylessSpernerValue`

This is

`1 / (Nat.choose (k-1) ((k-1)/2) : ℝ)`,

with natural-number subtraction truncated at zero. `memorylessSpernerValue_mem_Icc` states it always lies in `[0,1]`.

### 16.2 Limsup support lemmas

- `memorylessRunUpperDensity_le_one` says every run upper density is at most `1`, without any success or presentation assumption.
- `memorylessRunUpperDensity_ge_of_frequently` says frequent pointwise lower bounds by `σ` imply `σ` is at most the run `limsup`.
- `memorylessRunUpperDensity_le_of_eventually` says an eventual pointwise upper bound by `σ` bounds the run `limsup` above.
- `orderedUpperDensity_carrier_eq_one` and `orderedLowerDensity_carrier_eq_one` state that the full carrier has both densities equal to `1`.

These are analytic translations between frequent/eventual statements and the outer `limsup`.

### 16.3 Exact memoryless value

#### `memorylessSpernerValue_guaranteed`

For `k ≥ 1`, `memorylessSpernerValue k` satisfies `MemorylessUpperDensityGuarantee k`. The guarantee itself existentially quantifies a family-specific generator. Separately, the public canonical-success and frequent-density declarations certify `canonicalDensityGenerator` as an explicit candidate; injectivity remains part of the guarantee's input class even though those candidate declarations do not require it.

#### `memorylessSpernerValue_admissible`

For `k ≥ 1`, the same value belongs to `memorylessAdmissibleUpperDensities k`.

#### `admissibleUpperDensity_le_spernerValue`

For `k ≥ 1`, every admissible `σ` is at most the Sperner value. The hard instance is chosen from `lemma_4_7`; the admissible guarantee supplies a generator for that family, and the identity/injective hard stream yields an eventual upper bound on its run `limsup`.

#### `memorylessAdmissibleUpperDensities_bddAbove`

For every `k`, the admissible set is bounded above by `1`.

#### `theorem_4_1_memoryless_minimax_upper_density`

For every `k ≥ 1`,

`memorylessMinimaxUpperDensity k = 1 / Nat.choose (k-1) ((k-1)/2)`.

This is an equality of the actual supremum in the preceding order-robust guarantee and includes the actual outer run `limsup`. It is not an algorithmic minimax theorem: all strategies are arbitrary set-valued functions, the family-specific generator may be noncomputable, and there is no complexity or representation bound.

### 16.4 Zero lower-density hard family

#### `zeroLowerDensityHardFamily`

For `m`, this `Fin (m+2)` family places the universal carrier at index `0` and the `m+1` zero-lower-density partition pieces at successor indices.

For `m ≥ 1`:

- `zeroLowerDensityHardFamily_injective` says all `m+2` languages are distinct;
- `zeroLowerDensityHardFamily_infinite` says all are infinite;
- `zeroLowerDensityHardFamily_partition` says the side pieces partition the universal target; and
- `zeroLowerDensityPartition_maximum_eq_zero` says the maximum lower density of those pieces is exactly zero.

The family and density order are fixed by the definitions.

#### `theorem_4_2_indexed`

For every `m ≥ 1`, there exist an ordered language `K`, an injective family of `m+2` infinite languages, and a target whose language is `K.carrier`, such that every successful memoryless set generator and every injective exact presentation of the target satisfy both:

1. there exists `T` after which every output has lower density exactly `0`; and
2. for every real `σ > 0`, it is not the case that arbitrarily late outputs have lower density at least `σ`.

The second clause is logically implied by the first and positivity of `σ`; it is an explicit redundant endgame rather than an independent stronger obstruction. The success premise is for all finitely repeating presentations, while the tested target stream is injective, hence a special finitely repeating presentation.

#### `theorem_4_2_no_uniform_positive_lower_density`

For every `k ≥ 3`, the same conclusion holds with a family indexed by `Fin k`; its statement directly quantifies the `k`-member witness. It rules out any positive lower-density behavior even frequently on the selected hard target for every successful generator. It does not define or compute a lower-density minimax supremum, and it does not concern upper density.

## 17. Distinct sliding-window model and finite exceptions

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/DistinctWindows.lean`

### 17.1 Window interface

#### `DistinctWindow`

For a type `α` and width `W`, a distinct window is a function `Fin W → α` together with a proof that it is injective. It is an ordered tuple; equality remembers position. When `W = 0`, the tuple is empty and injectivity is vacuous.

#### `WindowSetGenerator`

This structure contains a function from distinct windows to sets and a proof that **every** output set is infinite. Infinitude is part of the generator type, unlike `MemorylessSetGenerator`, where it is checked in `ValidSetOutput`. The structure has no persistent state and receives only the current window.

#### `ValidWindowOutput`

For generator, target `L`, and window, validity is only `G w ⊆ L`; output infinitude is already guaranteed by the structure. There is no freshness or density condition in validity.

#### `windowAt`

Given a stream, a proof that it is injective, a start position, and width `W`, `windowAt` is the ordered tuple `i ↦ stream (start+i)`, with distinctness derived from stream injectivity. The proof object `hstream` is required to form the subtype but is not data observed by the generator.

#### `IsRepetitionFreeWindowGeneratorOn`

For every stream and every injectivity proof, if the stream exactly presents `L`, then there exists `T` such that every window starting at `start ≥ T` has output contained in `L`. The width is fixed in `G`. The threshold is by first position of the window. This model is restricted to repetition-free presentations, not all finitely repeating presentations.

### 17.2 Adversarial construction

The following declarations are in a section assuming `[Countable α]`, positive `W`, infinite `L`, and a fixed window generator `G`.

#### `baseEnum` and `nextBase`

`baseEnum` is a noncomputably chosen injective exact enumeration of `L`. Given a finite forbidden set `F`, `nextBase F` selects the first base-enumeration value outside `F`. Theorems record membership in `L` and avoidance of `F`.

#### `BadWindowsOutsideFinite`

This proposition says that for every finite `F`, there exists a distinct width-`W` window such that every entry lies in `L \ F` and `G`'s output is not contained in `L`. It is the negation pattern of a uniform finite-exception conclusion.

#### `badWindow`

Assuming `hbad : BadWindowsOutsideFinite L G`, this noncomputably chooses one such bad window for each finite `F`. `badWindow_mem`, `badWindow_not_mem`, and `badWindow_bad` expose its defining properties.

#### `selectedBlock`, `advance`, and `used`

For finite used set `F`, `selectedBlock F` is an ordered block of length `W+1`: first `nextBase F`, followed by a bad window chosen outside `F` and outside that new pivot. `selectedBlock_mem`, `selectedBlock_not_mem`, and `selectedBlock_injective` say every block entry lies in `L`, avoids `F`, and the block is injective.

`advance F` adds all block entries to `F`. `used s` iterates this operation from the empty set. Supporting theorems state monotonicity, freshness of the current block, and membership of all earlier blocks in later used sets.

#### `badPresentation`

This stream flattens the stage blocks of size `W+1`. `badPresentation_mem` says all values lie in `L`; `badPresentation_injective` says the entire stream is injective. The base-pivot bookkeeping declarations `base_prefix_used`, `base_eventually_used`, and `mem_used_exists_block` imply `badPresentation_presents`: its range is exactly `L`.

#### `bad_window_occurs`

At each stage `s`, the width-`W` window beginning at `s(W+1)+1` is exactly the selected bad window for that stage. Hence bad windows occur arbitrarily late in the constructed injective exact presentation.

#### `badWindows_force_failure`

If `W > 0`, `L` is infinite, and bad windows exist outside every finite set, then `G` does not satisfy `IsRepetitionFreeWindowGeneratorOn G L`. The theorem is conditional and semantic; the adversarial stream depends on `G` and on the choice of bad windows.

#### `lemma_4_11_finite_exception`

Assume `[Countable α]`, `W > 0`, infinite `L`, and successful repetition-free window generator `G`. Then there exists a finite set `B : Finset α` such that:

1. every element of `B` lies in `L`; and
2. for every distinct width-`W` window, if every entry lies in `L` and outside `B`, then `G w ⊆ L`.

The finite exceptional set is uniform over all windows, not merely windows appearing in one presentation. It may depend on `G,L,W` and is not computably produced. Positive width is essential to the stated theorem; no analogous conclusion is asserted for `W=0`.

## 18. Sliding-window hard instance and exact minimax value

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/WindowHardInstance.lean`

### 18.1 Sparse positions and density order

#### `WindowSquare` and `WindowNonSquare`

`WindowSquare t` means `t = q*q` for some natural `q`; `WindowNonSquare t` is its negation. `windowSquare_iff_sqrt` characterizes squares through `Nat.sqrt`, and `windowSquare_mul_self` supplies square witnesses.

`betweenWindowSquares m = (m+1)^2 + (m+1)` is a nonsquare. It is strictly increasing, and `windowNonSquare_infinite` concludes that the nonsquare set is infinite.

#### `windowDensityOrder`

This noncomputable function exchanges square and nonsquare positions by rank:

- a square `t` is sent to the `sqrt(t)`-th nonsquare;
- a nonsquare `t` is sent to the square of the number of earlier nonsquares.

`windowDensityOrder_involutive` states applying it twice returns `t`; hence `windowDensityOrder_injective` and `windowDensityOrder_surjective` make it a permutation of `ℕ`.

#### `windowHardTargetOrder`

This `OrderedLanguage` has universal carrier and enumeration `windowDensityOrder`. Thus density is evaluated in the permuted order, not in the identity order used by the hard presentation.

#### `windowSeparator` and `windowPositivePiece`

- `windowSeparator` is the set of nonsquare natural numbers.
- For `i : Fin N`, `windowPositivePiece i` is the set of squares whose square root is congruent to `i.val mod N`.

`windowDensityOrder_mem_separator_iff` says an enumerated value lies in the separator exactly at a **square enumeration position**. `windowDensityOrder_mem_positivePiece_iff` says an enumerated value lies in positive piece `i` exactly at a nonsquare position whose nonsquare rank has residue `i`.

#### Density and partition properties

- `windowSeparator_upperDensity` states that the separator has upper density `0` in `windowHardTargetOrder`.
- `windowPositivePiece_upperDensity_le` states each positive piece has upper density at most `1/N` when `N > 0`.
- `windowSeparator_union_positivePiece_upperDensity_le` gives the same `1/N` upper bound for the union of the separator with one positive piece.
- `windowPositivePiece_infinite` states every positive piece is infinite for positive `N`.
- `windowPositivePieces_pairwiseDisjoint` and `windowSeparator_disjoint_positivePiece` give disjointness.
- `windowSeparator_union_positivePieces` states that, for positive `N`, the separator together with all positive pieces covers `ℕ`.

Only an upper bound, not exact density, is asserted for a positive piece.

### 18.2 Hard family

#### `windowHardLanguage`

For `j : Fin n`, this language is the separator together with every positive piece whose middle-layer signature contains `j`. Membership is characterized by `mem_windowHardLanguage_iff` as a disjunction between separator membership and such a positive-piece witness.

Every side language is infinite (`windowHardLanguage_infinite`) because it contains the infinite separator, without any lower bound on `n`.

#### `windowPieceOwner`

For any number `x`, this is the residue class of `Nat.sqrt x` modulo the central-binomial width. For square `x`, `mem_windowPositivePiece_owner` says `x` belongs to its owner piece, and `windowPositivePiece_owner_unique` says any positive-piece membership determines the same owner.

`mem_windowHardLanguage_of_not_separator_iff` says that for a non-separator point, membership in side language `j` is exactly membership of `j` in the owner's middle signature.

For `n ≥ 2`, every side language is non-universal and the side-language map is injective. `windowHardFamily` adds the universal target at index `0`; for `n ≥ 2` it is injective, and for every `n` all family members are infinite.

### 18.3 Uniform finite exception and forced intersections

#### `finiteFamily_window_exception`

For positive width, any finite indexed family of infinite languages, and a single window generator successful on each member, there exists one finite set `B` such that, uniformly for every family index and every distinct window whose entries lie in that language outside `B`, the output lies in that language. This consolidates the per-language finite sets from `lemma_4_11`. If the index type `Fin m` is empty the statement is vacuous after choosing any finite `B`, but later applications have nonempty families.

#### `windowHardIntersection_subset_separator_union_piece`

For each middle-signature owner `i`, the intersection of all side languages named by coordinates in that signature is contained in `windowSeparator ∪ windowPositivePiece i`.

#### `windowHardIntersection_all_subset_separator`

For `n ≥ 2`, the intersection of **all** side languages is contained in the separator. These are one-sided forcing containments.

### 18.4 Geometry of the fixed identity stream

#### `identityWindow`

This is `windowAt id` at a given start and width. Its entries are the consecutive numbers `start+i`.

#### `square_window_index_unique`

If `start ≥ W^2`, then any two square entries in the width-`W` identity window have the same position. Equivalently, such a window contains at most one square. The statement applies also to `W=0`, where there are no positions.

#### `identityWindow_signature_geometry`

For any implicit `n`, if `start ≥ W^2`, then either every entry of the identity window lies in the separator, or there exists one positive-piece owner such that every entry lies in the separator or that same positive piece. The owner is not claimed unique in the all-separator branch.

#### `eventually_windowHard_upperDensity_bound`

For `n ≥ 2`, positive width `W`, and any `WindowSetGenerator ℕ W` successful repetition-freely on every member of `windowHardFamily n`, there exists `T` such that every identity window starting at or after `T` has output upper density at most

`1 / Nat.choose n (n/2)`

in `windowHardTargetOrder`. The threshold combines avoidance of the uniform finite exceptional set with the `W^2` sparse-square geometry. The hard stream is fixed as identity; no target or presentation input is supplied to `G`.

### 18.5 Fixed hard instance before width

#### `lemma_4_12_single_hard_instance`

For every `k ≥ 2`, there exist, **before any window width is chosen**:

1. an ordered target `K`;
2. an injective family `langs : Fin k → Set ℕ` of infinite languages;
3. a target index;
4. a stream; and
5. a proof that the stream is injective,

such that the target language equals `K.carrier`, the stream exactly presents that carrier, and the following holds:

for every `W > 0` and every width-`W` window set generator, if that generator succeeds on every family member for every repetition-free exact presentation, then eventually all windows of the fixed stream have upper density at most

`1 / Nat.choose (k-1) ((k-1)/2)`.

This quantifier order is stronger than choosing a different hard stream for each width or generator. For `k=2`, the numerical bound is `1`, so the asserted upper bound is the universal trivial bound. No computational lower bound is asserted.

### 18.6 Window minimax definitions

#### `windowRunUpperDensity`

For ordered target, width-`W` generator, injective stream, and its injectivity proof, this is the `limsup` over window start positions of the inner upper density of each window output.

#### `WindowUpperDensityGuarantee`

For `k,W,σ`, the quantifier order is:

1. every injective `Fin k` family of infinite languages;
2. there exists a family-specific width-`W` window generator `G` such that:
   - `G` succeeds repetition-freely on every family member; and
   - for every target, every ordered realization of that target, every injective stream and exact-presentation proof,
     `σ ≤ windowRunUpperDensity K G stream hstream`.

The stream injectivity proof is part of the evaluator's construction of windows, not runtime data for `G`. There is no separate finite-repetition premise because every quantified stream is injective.

#### `windowAdmissibleUpperDensities` and `windowMinimaxUpperDensity`

The admissible set is `[0,1]` intersected with the guarantee values; the minimax value is its noncomputable supremum.

### 18.7 Achievability and exact closure

#### `canonicalWindowGenerator`

For positive `W`, this generator ignores all but the first element of the window and applies the canonical memoryless density generator to it. Infinitude follows from the canonical output theorem. Positive width is needed to select position `0 : Fin W`.

#### `canonicalWindowGenerator_succeeds`

For every finite nonempty indexed family and every positive width, the canonical window generator succeeds repetition-freely on every member. As before, for finite target languages the absence of an injective exact presentation makes the obligation vacuous.

#### `canonicalWindowRunUpperDensity_eq`

On every injective stream, the window run density of the lifted generator equals the memoryless run density of the canonical memoryless generator, because the first element of the start-indexed window is exactly `stream start`.

#### `windowSpernerValue_guaranteed` and `windowSpernerValue_admissible`

For `k ≥ 1` and `W > 0`, the same reciprocal central-binomial value as in the memoryless model is guaranteed and admissible.

#### `windowAdmissibleUpperDensity_le_spernerValue`

Under the same hypotheses, every admissible window density is at most that value. The separately exported `lemma_4_12_single_hard_instance` has the matching hard-instance quantifier order, with the hard data fixed before width and generator.

#### `theorem_4_10_window_minimax_upper_density`

For every `k ≥ 1` and positive width `W`,

`windowMinimaxUpperDensity k W = 1 / Nat.choose (k-1) ((k-1)/2)`.

The formal value is independent of positive `W`. This is an exact semantic minimax equality with an outer run `limsup`; it is not a statement that additional window entries are computationally useless under a resource-bounded implementation. No theorem is stated for `W=0`.

## 19. Adaptive bounded-buffer model and lower bound

### File label: `GenLimitLean/GenLimit/Paper31_BoundedMemory/AdaptiveBuffer.lean`

### 19.1 Buffer semantics

#### `BufferState`

For type `α` and capacity `b`, a buffer state is a list `xs : List α` with proof `xs.length ≤ b`. The list is ordered and may contain repeated values; distinctness is not required.

#### `emptyBufferState`

The empty list is the designated initial buffer state for every `α,b`.

#### `BufferSetGenerator`

A buffer set generator contains:

1. `output : BufferState α b → α → Set α`;
2. a proof that every output is infinite;
3. `update : BufferState α b → α → BufferState α b`; and
4. `update_supported`: every value occurring in the updated list must either have occurred in the previous list or equal the current input.

The support condition forbids synthesizing a wholly new buffered value, but it permits deletion, reordering, and duplication of old/current values, subject only to the length bound. It places no restriction on the output set: outputs may contain arbitrary elements and need not be derived from the buffer. The whole family can be compiled into `output` and `update`.

#### `bufferState` and `bufferOutputAt`

The state at time `0` is empty; state `t+1` is obtained by updating state `t` with `stream t`. `bufferOutputAt G stream t` applies `G.output` to the state **before** processing `stream t` together with the current input. This timing is part of the formal semantics.

#### `IsRepetitionFreeBufferGeneratorOn`

For every stream and every proof that it is injective, exact presentation of `L` implies an eventual threshold after which every buffer output is contained in `L`. Infinitude is already built into `BufferSetGenerator`. The injectivity proof is a premise, not a runtime argument to `output` or `update`.

#### `bufferRunUpperDensity`

This is the temporal `limsup` of the ordered upper densities of `bufferOutputAt G stream t`.

#### `BufferUpperDensityGuarantee`

For `k,b,σ`, the exact quantifier order is:

1. every injective `Fin k` family of infinite languages;
2. there exists one family-specific capacity-`b` buffer generator such that:
   - it succeeds repetition-freely on every family member; and
   - for every target, every ordered realization of that target, and every injective exact presentation,
     `σ ≤ bufferRunUpperDensity K G stream`.

The target, order, and stream are adversarially selected after the generator. The buffer generator receives only its bounded list and current example, not the target or density order. There is no computability, bit-size, or update-time condition.

#### `bufferAdmissibleUpperDensities` and `bufferMinimaxUpperDensity`

The admissible set is `[0,1]` intersected with the guarantee values, and the minimax value is its noncomputable supremum. `bufferRunUpperDensity_ge_of_frequently` converts frequent per-round density lower bounds into a lower bound on this outer `limsup`.

### 19.2 Greedy residual construction

#### `bufferResidual`

Given a family and buffer state `M`, this noncomputable finite set contains exactly those family indices whose language contains every value occurring in `M.1`. Multiplicity and order of the list do not affect the residual predicate.

#### `bufferResidualAfter`

This filters the residual to indices whose language also contains the current input `x`. `bufferResidualAfter_subset` states it is a subset of the prior residual. `bufferResidual_empty` says the empty buffer leaves every family index possible.

#### `bufferResidualCore`

For state `M` and input `x`, this is the set of `y` that belong to every residual language which contains `x`. Languages in the residual that omit `x` impose no condition.

#### `bufferCanonicalOutput`

This outputs the residual core if it is infinite and otherwise outputs `Set.univ`. `bufferCanonicalOutput_infinite` states every output is infinite. The infinitude test and family membership are noncomputable.

#### `ShouldStore`

The current input should be stored exactly when the buffer is not full and filtering by that input makes the residual a proper subset of its previous value. This is a semantic proper-subset test over the finite index set.

#### `greedyBufferUpdate` and `greedyBufferGenerator`

If `ShouldStore` holds, the update appends the current input; otherwise it leaves the state unchanged. There is no eviction. The generator combines this update with `bufferCanonicalOutput`, and its support proof records that appended values are current inputs. The family is built into the generator.

#### `greedyBufferState` and stabilization

`greedyBufferState` is the run state of the greedy generator. Its length is monotone and increases strictly whenever storage occurs. `greedyStoreTimes` is the set of such times; `greedyStoreTimes_finite` states it is finite. Consequently `greedyBufferState_eventually_constant` says that for every family and every stream there exists a time after which the entire buffer state is constant. No rate is given.

#### `greedyBuffer_residual_length_bound`

At every time,

`card(current residual) + current buffer length ≤ k`.

Each stored example consumes one buffer slot and strictly removes at least one residual index. This is the central finite-capacity invariant.

### 19.3 Run invariants and target preservation

#### `bufferState_entry_seen`

For **any** buffer generator satisfying `update_supported`, every value in the state at time `t` equals some stream value at an earlier time `s < t`. This is the formal no-synthesis consequence.

#### `bufferState_entries_mem_of_presents`

If the stream presents `L`, then every entry in every buffer state lies in `L`.

#### `target_mem_greedyBufferResidual`

On a presentation of `langs target`, the true target index belongs to the greedy residual at every time. Therefore `residual_nonempty_on_presentation` concludes that the residual is nonempty throughout the run.

#### Residual monotonicity

`greedyBufferResidual_succ_subset` and `greedyBufferResidual_antitone` state that the residual can only shrink with time. This is set inclusion on finite index sets, not merely nonincreasing cardinality.

### 19.4 Padding a residual family

#### `residualCoreFor`

For a finite residual index set `R`, this is the intersection rule that includes only languages in `R` that contain the current input.

#### `paddedResidualIndex` and `paddedResidualFamily`

Given residual `R`, fallback index, and target output size `q`, `paddedResidualIndex` enumerates the residual while positions below `R.card` are available and uses the fallback for any remaining positions. `paddedResidualFamily` maps these indices back to languages. Duplicate fallback languages are permitted.

If the fallback belongs to `R`, `paddedResidualIndex_mem` says every padded index lands in `R`. If `R.card ≤ q`, `paddedResidualIndex_surjective_on` says every residual index appears somewhere in `Fin q`.

#### `finiteFamilyCore_paddedResidualFamily`

If the fallback belongs to `R` and `R.card ≤ m+1`, then the finite-family core of the padded `Fin (m+1)` family at every `x` equals `residualCoreFor langs R x`.

#### `canonicalDensityGenerator_padded_eq_buffer`

Under the analogous residual membership and cardinality assumptions, the canonical density generator for the padded residual family equals the buffer canonical output at every input. This is an exact equality that transfers memoryless density statements to the stabilized buffer state.

### 19.5 Validity and density branches

#### `greedyBufferGenerator_succeeds`

For every natural `k,b` and every family `langs : Fin k → Set ℕ`, the greedy generator succeeds repetition-freely on every indexed language. No family-wide infinitude assumption occurs. If a target is finite, the quantified injective exact presentations are absent, so that component is vacuous. If `k=0`, the universal quantifier over targets is empty.

#### `greedyBuffer_frequently_sperner_dense_of_residual_card_le`

Fix a target/order/stream with exact presentation, a stabilization time `T`, and assume the stabilized residual has cardinality at most `n+1`. Then arbitrarily late outputs of the greedy buffer generator have upper density at least

`1 / Nat.choose n (n/2)`.

No injectivity premise appears in this declaration. Its conclusion is a frequent lower bound for the actual greedy-buffer outputs under the supplied stabilization and residual-cardinality assumptions.

#### `residualIntersection`

For residual index set `R`, this is the intersection of all `langs i` with `i ∈ R`.

#### Stable nonfull branch

`stabilized_nonfull_residualAfter_eq` states that if the greedy buffer is stable after `T` and its stabilized length is strictly below capacity, then every later current input leaves the residual unchanged after filtering.

`stabilized_nonfull_stream_mem_residual` concludes that every later stream value belongs to every stabilized residual language.

`bufferResidualCore_eq_intersection_of_all_mem` says that when the current input belongs to every residual language, the buffer residual core equals the full residual intersection.

`residualIntersection_upperDensity_eq_one_of_tail` says that if an exact presentation of `K.carrier` has all values from time `T` onward in a residual intersection, then that intersection has upper density exactly `1` in `K`. The finite prefix is the only possible part of the carrier outside the intersection.

`greedyBuffer_eventually_density_one_of_stable_nonfull` adds injectivity of the stream and concludes that every output from time `T` onward has upper density exactly `1`. Injectivity is used to ensure the tail, and hence the output core, is infinite. `greedyBuffer_runDensity_one_of_stable_nonfull` converts this eventual equality into `1 ≤ bufferRunUpperDensity`; combined with the universal upper bound on set densities, the run value is effectively `1`, although the theorem states only the lower inequality.

### 19.6 Stated lower value and main theorem

#### `adaptiveBufferLowerValue`

For `k,b`, this noncomputable real is defined piecewise:

- if `b ≤ k-3`, it is
  `1 / Nat.choose (k-b-1) ((k-b-1)/2)`;
- otherwise it is `1`.

All subtractions are natural-number truncated subtraction.

#### `adaptiveBuffer_low_regime_guaranteed`

For `k ≥ 1` and `b ≤ k-3`, the reciprocal value in the first branch satisfies `BufferUpperDensityGuarantee k b`. This is the exact low-regime guarantee stated by the theorem; no implementation or convergence-rate bound is included.

#### `adaptiveBuffer_high_regime_guaranteed`

For `k ≥ 1` and `k-2 ≤ b`, the guarantee value is exactly `1`. This is the strongest possible value within the admissible interval `[0,1]`, but the theorem remains semantic and supplies no implementation or rate bound.

#### `adaptiveBufferLowerValue_guaranteed` and `adaptiveBufferLowerValue_admissible`

For every `k ≥ 1` and every `b`, the piecewise value is guaranteed and belongs to the admissible set. In the branch where `b ≤ k-3` is false, natural arithmetic supplies the high-regime inequality.

#### `theorem_4_15_adaptive_buffer_lower_bound`

For every `k ≥ 1` and every buffer capacity `b`,

`adaptiveBufferLowerValue k b ≤ bufferMinimaxUpperDensity k b`.

This is only a **lower bound** on the minimax supremum. No matching upper bound or equality is formalized in the bundle. The theorem is semantic and noncomputable; it does not claim that the greedy update can be implemented from finite representations of arbitrary languages or that `b` list entries correspond to a bounded number of bits.

## 20. Explicit quantifier-and-access ledger

This ledger restates the principal declarations in the order in which objects are fixed and records exactly what the formal generator/learner receives during a run.

### `theorem_3_1` — `ArbitraryRepetitions.lean`

- **Fixed first:** countable ambient type instance; class `H`; proofs that `H` is countable and all its members are infinite.
- **Existential object:** on the left side, one function `G : α → Set α` for the whole class.
- **Runtime access:** current element only.
- **Adversary:** target `K ∈ H`, then any exact presentation with arbitrary repetitions.
- **Conclusion:** equivalence with infinitude of every singleton common core.
- **Redundant displayed conditions:** the two assumptions on `H` are unnecessary relative to the separately exported necessity and sufficiency declarations; ambient countability remains in the necessity declaration.
- **Class:** semantic/extensional equivalence; noncomputable.

### `theorem_1_1` — `FinitelyRepeating.lean`

- **Fixed first:** countable class `H ⊆ Set ℕ`, all members infinite.
- **Existential object:** one family-specific `G : ℕ → Set ℕ`.
- **Runtime access:** current natural-number example only.
- **Adversary:** target and exact finitely repeating stream.
- **Conclusion:** eventual infinite-subset validity.
- **Separately exported candidate:** `finitelyRepeatingGenerator langs` uses the numerical value of the example as a search-depth bound and semantic infinitude tests; the existential theorem itself does not expose its witness.
- **Class:** semantic existence, not effective.

### `theorem_3_2` — `OutputSeparations.lean`

- **Element clause:** target `K` and `G : ℕ → ℕ` are fixed, then an adversarial finitely repeating exact stream witnesses failure. `G` sees only the current element.
- **Index clause:** the two-language family is fixed before `G : ℕ → Fin 2`; an adversarial target and stream witness failure. Output validity is one-sided language containment.
- **Class:** universal semantic impossibility; no computational lower bound.

### `theorem_5_2` — `IncrementalIdentification.lean`

- **Fixed first:** a finite nonempty indexed family `raw` and a family-wide infinitude proof that is redundant relative to the separately exported relabeling and ordered-identification declarations.
- **Existential object:** a family with the same set range, then a learner and initial finite index inside its identification predicate. The result type does not state that this family is a permutation; separate public declarations exhibit such a relabeling candidate.
- **Runtime access:** previous finite index and current example.
- **Adversary:** target and arbitrary exact presentation, repetitions unrestricted.
- **Conclusion:** eventual almost-equivalence of the currently indexed language to the target.
- **Class:** semantic, noncomputable relabeling and membership tests.

### `proposition_5_1`, `proposition_A_2`, and `theorem_A_1`

- **Fixed first:** a concrete or existential three-language family.
- **Universal object:** every learner/generator with state type exactly `Fin 3` and every initial state.
- **Runtime access:** previous index and current example.
- **Adversary:** target and exact finitely repeating presentation.
- **Conclusion:** failure of exact convergence, or even eventual one-sided index validity for the triangle family.
- **Scope limitation:** no statement about larger hidden-state spaces, synonym indices, or natural-valued encoded states.
- **Class:** representation-sensitive semantic impossibility.

### `incremental_element_generation` — `IncrementalElementCoding.lean`

- **Fixed first:** any finite nonempty family of infinite subsets of `ℕ`.
- **Existential object:** one learner `ℕ → ℕ → ℕ` and initial natural state.
- **Runtime access:** previous natural output/state and current input.
- **Adversary:** target and arbitrary exact presentation.
- **Conclusion:** eventually the state is a fresh target element relative to all seen examples.
- **Crucial fact about the separately exported compiled candidate:** its previous natural state losslessly encodes the complete finite history and current index hypothesis.
- **Class:** semantic/noncomputable; not bounded-bit memory.

### `lemma_4_3_lower_density_bound_from_partition`

- **Fixed first:** ordered target, finite partition, infinitude of pieces, generator, success proofs on pieces, target stream, exactness, injectivity.
- **Runtime access of `G`:** current point only.
- **Conclusion:** eventual pointwise upper bound on **lower** density by the maximum piece lower density.
- **Class:** conditional analytic theorem with both disjointness and coverage in its formal partition premise.

### `lemma_4_4_zero_lower_density_partition`

- **Fixed first:** ordered language and `m ≥ 2`.
- **Existential object:** one order-dependent `Fin m` partition.
- **Conclusion:** pairwise disjoint, covering, infinite pieces, each lower density zero.
- **Class:** semantic existence; separate public declarations certify an explicit order-dependent candidate, not a partition simultaneous across all orderings.

### `lemma_4_7_sperner_hard_instance`

- **Fixed first:** `k ≥ 2`; then the theorem chooses one ordered target, injective `k`-family, and target index.
- **Universal object:** every memoryless set generator successful on that family.
- **Adversary after generator:** every injective exact target presentation.
- **Conclusion:** eventual pointwise upper-density bound by the reciprocal central binomial coefficient.
- **Class:** semantic hard instance, not a runtime lower bound.

### `lemma_4_8_sperner_achievability`

- **Fixed first:** `n ≥ 1`, a `Fin (n+1)` family, and a supplied family-wide infinitude proof.
- **Existential object:** one family-specific memoryless set generator.
- **Adversary:** target, any duplicate-free density order of that target, and exact finitely repeating presentation.
- **Conclusion:** validity plus frequent upper-density lower bound.
- **Redundant relative to exported components:** the public canonical-success and frequent-density declarations establish the displayed candidate under weaker premises, omitting `n ≥ 1`, family-wide infinitude, and finite repetition in the density clause.
- **Class:** semantic, order-robust achievability.

### `theorem_4_1_memoryless_minimax_upper_density`

- **Outer universal:** every injectively indexed `k`-family of infinite languages.
- **Existential:** a generator may be tailored to that family.
- **Inner universal:** target, every ordered realization, every exact finitely repeating presentation.
- **Payoff:** outer temporal `limsup` of inner ordered upper densities.
- **Conclusion:** exact supremum for `k ≥ 1`.
- **Class:** noncomputable semantic minimax equality.

### `theorem_4_2_no_uniform_positive_lower_density`

- **Existential hard data:** one ordered target and injective `k`-family of infinite languages.
- **Universal generator:** every generator successful on the whole family.
- **Universal stream:** every injective exact presentation of the selected target.
- **Conclusion:** eventual lower density exactly zero, plus the logically redundant denial of any positive frequent lower bound.
- **Class:** semantic obstruction, not a lower-density minimax equality.

### `lemma_4_11_finite_exception`

- **Fixed first:** countable ambient type, `W > 0`, infinite target, successful window generator.
- **Existential object:** finite exceptional set `B ⊆ L`.
- **Universal after `B`:** every distinct window whose entries lie in `L \ B`.
- **Conclusion:** output containment in `L`.
- **Runtime access:** window only; no state.
- **Class:** semantic compactness/finite-exception theorem.

### `lemma_4_12_single_hard_instance`

- **Fixed hard data before width:** ordered target, injective family, target, fixed injective exact stream.
- **Universal next:** every positive width, then every successful window generator of that width.
- **Conclusion:** eventual upper-density bound on the fixed stream.
- **Class:** strong-quantifier semantic hard instance.

### `theorem_4_10_window_minimax_upper_density`

- **Family-specific strategy:** one width-`W` window generator chosen per family.
- **Runtime access:** exactly the ordered distinct window, no state.
- **Adversary:** target, all ordered realizations, injective exact stream.
- **Payoff:** outer `limsup` over start positions.
- **Conclusion:** exact reciprocal-binomial value for every `W > 0`, independent of `W`.
- **Class:** semantic minimax equality, not a computational equivalence between widths.

### `theorem_4_15_adaptive_buffer_lower_bound`

- **Family-specific strategy:** a capacity-`b` buffer generator chosen per family.
- **Runtime access:** ordered list of at most `b` prior examples and current example.
- **Transition constraint:** every updated buffer value must be old or current; deletion/reordering/duplication are allowed.
- **Adversary:** target, all ordered realizations, injective exact stream.
- **Payoff:** outer run `limsup`.
- **Conclusion:** the piecewise `adaptiveBufferLowerValue` is at most the minimax supremum.
- **Class:** semantic lower bound only; no matching upper bound.

## 21. Statement-level risk flags

### 21.1 Vacuity from missing presentations

1. **Finite targets under finitely repeating or injective presentation restrictions.** An infinite-time stream whose every value appears only finitely often cannot have finite range. Likewise an injective stream has infinite range. Therefore success obligations for finite target languages are empty in `IsFinitelyRepeatingMemorylessGenerator`, `IsRepetitionFreeMemorylessGeneratorOn`, `IsRepetitionFreeWindowGeneratorOn`, and `IsRepetitionFreeBufferGeneratorOn`. This explains why declarations such as `canonicalDensityGenerator_succeeds` and `greedyBufferGenerator_succeeds` can omit language infinitude without producing a nonvacuous finite-language algorithm.

2. **Empty classes and empty index types.** A class `H = ∅` makes family success predicates and `InfiniteSingletonCores` vacuous. `Fin 0` has no target indices, so the guarantee predicates for `k=0` have vacuous target clauses; the main minimax equalities explicitly assume `k ≥ 1`.

3. **Impossible carrier equality.** An `OrderedLanguage` has an injective enumeration from `ℕ`, hence an infinite carrier. Any implication whose premise equates that carrier with a finite target is vacuous. The principal minimax predicates independently require all family members infinite, so this issue is mostly confined to general helper declarations.

4. **Width zero.** The window interface exists for `W=0`, but the finite-exception lemma and exact minimax theorem assume `W>0`. No conclusion about the zero-width model should be inferred.

### 21.2 Redundant or stronger-than-needed hypotheses

Several theorem signatures are stronger than separately exported declarations that jointly establish the same displayed conclusions:

- `theorem_3_1`: the separately exported necessity and sufficiency implications omit `H.Countable` and `∀ K∈H, K.Infinite`; ambient `[Countable α]` remains in the necessity declaration.
- `finitelyRepeatingGenerator_infinite`: its premise quantifies infinitude of every indexed language, while `selectedDepth_core_infinite` supplies the corresponding core-infinitude fact from infinitude of the zeroth language alone.
- `theorem_5_2`: the separately exported topological relabeling declarations and `theorem_5_2_ordered` have no family-wide infinitude premise and jointly give the same existence conclusion.
- `lemma_4_8_sperner_achievability`: `canonicalDensityGenerator_succeeds` and `canonicalDensityGenerator_frequently_sperner_dense` jointly certify the displayed candidate without `n≥1` or family-wide infinitude, and the latter has no finite-repetition premise.
- `theorem_4_2_indexed` and `theorem_4_2_no_uniform_positive_lower_density`: the second no-positive-frequent clause follows from the first eventual-zero clause.

These are not inconsistencies. They are overstrong interfaces or redundant endgames and must not be mistaken for additional content of the stated conclusions.

### 21.3 Classical choice and noncomputability

The principal positive constructions are not effective algorithms in the formal statements:

- arbitrary sets are tested for membership, finiteness, infinitude, and almost-containment using classical propositions;
- countable and infinite sets are enumerated using chosen equivalences or surjections;
- topological orders are chosen noncomputably;
- codewords are chosen outside finite sets by classical choice;
- minimax values are `sSup`s and run values use `limsup`/`liminf`;
- no representation of an infinite set output is supplied.

Although `GenLimit.Core.Basic` defines a `MembershipOracle`, no primary Paper 31 model or theorem takes such an oracle as an argument. There is no query bound, decidable membership assumption, recursive enumeration, Turing-machine model, or finite running-time theorem.

### 21.4 Answer-encoding and hidden information channels

The strongest flag is in `IncrementalElementCoding.lean`. The formal state/output is a natural number, and `codingCompiled_run_is_code` states that it encodes:

- the exact complete finite history;
- the full-information learner's current index; and
- an auxiliary salt.

Thus `incremental_element_generation` is not a bounded-information-memory theorem. It uses a one-register incremental interface whose register ranges over unbounded natural numbers. The state is also a generated target element, and the codebook is constructed inside the target languages. This is an explicit answer/history-encoding input channel, not a merely possible implementation detail.

Related representation channels include:

- `selectedDepth langs x` uses the magnitude of the current natural-number example as a search bound;
- a family-specific set-valued generator may extensionally encode the entire family in its graph;
- a buffer stores at most `b` examples, but each example is an unbounded natural number and the output set can be an arbitrary noncomputable set;
- no theorem relates “number of stored examples” to bits of memory.

### 21.5 Representation sensitivity

1. **Canonical universe.** The finitely repeating universal construction, density results, element coding, window model, and buffer model are stated on `ℕ`. Generic countable-type results occur only in selected early and obstruction modules. No transport theorem turns all `ℕ`-specific results into arbitrary countable-universe results.

2. **Index order and repetitions.** `prefixCore` and `selectedDepth` depend on the enumeration order of `langs : ℕ → Set ℕ`. `Set.range langs` forgets repeated indices, but the generator construction does not.

3. **Relabeling.** `theorem_5_2` produces an approximately identifiable relabeling with equal set range; it does not literally assert `IncrementallyApproximatelyIdentifiable raw` for the original indexing.

4. **Exact-state obstructions.** The three-language negative results use `Fin 3` as the entire persistent state/output type. They do not rule out extra states, duplicate hypotheses, synonym indices, or natural-valued codes.

5. **Exactly `k` distinct languages.** Minimax and hard-instance statements use injective `Fin k` indexing. Results for noninjective representations or multiplicities are not identical statements.

6. **Density order.** Density depends on an `OrderedLanguage`. The minimax guarantees quantify over every ordered realization of a target, while hard instances choose a particular order. The generator does not receive the order.

7. **Buffer support semantics.** `update_supported` restricts only which values may appear, not their order or multiplicity. Reading it as “keep or evict a subset of distinct past examples” would be stronger than the Lean structure.

### 21.6 Exact-presentation strength

Every learning/generation success criterion uses exact range equality. There is no noise, omission, delayed-validity, partial text, negative data, or approximate presentation model. Exactness supplies the mathematical fact that every target element appears somewhere, even though the runtime generator does not receive a certificate or future information.

Thresholds are existential and may depend on the entire target stream. No uniform sample complexity is asserted.

### 21.7 Output notions are different and must not be conflated

- Memoryless, window, and buffer **set** outputs must be infinite subsets of the target eventually; they need not be fresh relative to the sample.
- Memoryless **element** outputs must lie in the target and be absent from the sample including the current observation.
- Memoryless and incremental **index** outputs are valid through one-sided containment of the represented language in the target; equality follows only under an antichain condition.
- Incremental **element** generation treats the persistent state itself as the generated element and requires freshness relative to all processed inputs.
- Approximate identification requires finite symmetric difference, not containment or exact index convergence.

Positive results in one model do not directly imply positive results in another without an explicit compilation theorem.

### 21.8 Redundancy, circularity, and consistency audit

No primary axiom is introduced, and no principal theorem has a conclusion that simply repeats one of its assumptions. The main constructions are connected by explicit implications rather than by assuming the desired result.

There are routine definitional equalities and redundant conjuncts, especially the second clause of the lower-density obstruction, but no circular definition of success in terms of itself. Some implications may hold vacuously because their presentation hypotheses are impossible; this is vacuity rather than inconsistency.

At the signature level, no pair of primary declarations is contradictory. This report did not independently replay the bundle through the Lean kernel, so this is a statement-level consistency audit, not a fresh compilation certificate.

## 22. Concise list of what the Lean statements do **not** establish

1. They do not compare the formal statements with any author paper, informal theorem, or intended interpretation.
2. They do not give computable generators, decidable membership tests, oracle algorithms, query bounds, running times, sample complexities, or bit-complexity bounds.
3. They do not show that memory measured in stored examples is bounded in bits; natural-valued states and examples may encode unbounded information.
4. They do not give a transport theorem for all `ℕ`-specific results to every arbitrary countable example type.
5. They do not address noisy, incomplete, approximate, or adversarially corrupted presentations; presentation is exact range equality.
6. They do not provide a single generator uniform across all language families; the existential generator is selected after the family is fixed.
7. They do not require freshness of set-valued outputs, only infinitude and target containment.
8. They do not prove that a memoryless element generator works on any infinite target; they prove the opposite.
9. They do not rule out exact incremental identification with a larger hidden state space than the language-index type.
10. They do not turn the approximate-identification relabeling theorem into an exact-identification theorem.
11. They do not prove an exact adaptive-buffer minimax value; only the lower bound `adaptiveBufferLowerValue ≤ bufferMinimaxUpperDensity` is stated.
12. They do not state the window minimax theorem for `W=0`.
13. They do not produce a positive uniform lower-density minimax value for `k≥3`; the formal result supplies a hard family with eventual lower density zero.
14. They do not assert that frequent upper-density lower bounds hold eventually; `∃ᶠ` means arbitrarily late occurrences only.
15. They do not assert that the positive pieces in the window hard instance have upper density exactly `1/N`; only an upper bound is stated.
16. They do not formalize probability, randomization, expected performance, or high-probability guarantees.
17. They do not constrain the representation size of an infinite output set or require it to be enumerable.
18. They do not establish nonvacuous success for finite targets under injective or finitely repeating presentation restrictions.
19. They do not establish uniqueness of any successful generator, learner, relabeling, partition, or hard instance.
20. They do not establish that the hard-instance impossibilities are computational rather than information-theoretic/semantic.

## 23. Uncertainty statement

The natural-language translations above were reconstructed from the attached source signatures and definition equations alone. The main uncertainty is judgment about which public support declarations are “materially substantive” rather than merely indexing or simp infrastructure. To make that judgment auditable, §24 lists every remaining public primary declaration not separately expanded above and records its exact support role. No inference from comments, paper prose, theorem names, or proof tactics is used as mathematical evidence.

## 24. Reviewed public support-declaration ledger

The declarations below were inspected but are classified as exact unfolding equations, local construction invariants, elementary finite arithmetic, or transport infrastructure rather than additional paper-level end results. Each name and its formal role is recorded so that no public primary declaration is silently ignored.

### `ArbitraryRepetitions.lean`

- `repeatedPointPresentation_even`: for every `K,hK,x,n`, the repeated-point stream at `2*n` equals `x`.
- `repeatedPointPresentation_odd`: at `2*n+1`, it equals `basePresentation K hK n`.

### `OutputSeparations.lean`

- `interleave_even` and `interleave_odd`: exact evaluation of `interleave` at `2*n` and `2*n+1`.
- `prepend_zero` and `prepend_succ`: exact evaluation of `prepend` at zero and successors.
- `chosenGoodPreimage`: under `[Countable α]` and infinitude of `goodImage G K B`, noncomputably chooses a preimage in `K\B` of the `n`th injectively enumerated image value.
- `chosenGoodPreimage_mem`: every chosen preimage lies in `K\B`.
- `chosenGoodPreimage_image`: applying `G` to it gives the corresponding `infiniteEnumeration` value of the good image.
- `chosenGoodPreimage_injective`: the chosen-preimage stream is injective.

### `IncrementalIdentification.lean`

- `AlmostOrder.ext`: two wrapped indices are equal when their `val` fields are equal.
- `almostOrderEquiv`: the wrapper `AlmostOrder langs` is equivalent to `Fin (N+1)`.
- `instFintypeAlmostOrder`: transports the finite-type instance across that equivalence.
- `almostOrderLinearExtensionEquiv`: the underlying type is equivalent to its `LinearExtension` wrapper.
- `instFintypeLinearExtensionAlmostOrder`: supplies finiteness of the linear-extension type.
- `instPartialOrderAlmostOrder`: installs the partial order whose comparison is equality or strict almost-containment; this semantic content is described in §7.2.
- `incrementalRun_zero` and `incrementalRun_succ`: exact recursion equations for the initial and successor run states.

### `ExactIdentificationObstruction.lean`

- `one_not_mem_exactObstructionCore` and `two_not_mem_exactObstructionCore`: `1` and `2` are not multiples of `3` in the defined core.
- `exactObstructionLanguages_zero`, `exactObstructionLanguages_one`, and `exactObstructionLanguages_two`: exact unfolding of the three displayed language values.

### `IncrementalIndexObstruction.lean`

- `prefixStream_nil`, `prefixStream_cons`: recursion equations for finite-prefix streams.
- `prefixState_nil`, `prefixState_cons`: recursion equations for the state after a finite prefix.
- `prefixSupport_nil`, `prefixSupport_cons`: recursion equations for the set obtained by inserting prefix entries.
- `prepend_presents_insert'`: if a tail presents `K`, prepending `head` presents `insert head K`.
- `incrementalRun_prepend'`: the same run-alignment equality as `incrementalRun_prepend`, for the shared `prepend` definition.
- `prefixStream_append`: prefixing `xs ++ ys` equals prefixing `xs` before the stream already prefixed by `ys`.

### `IncrementalElementCoding.lean`

- `elementCodeRequestAt_encode`: decoding the encoding of a request returns the request.
- `elementCodewordAt_not_used`: the stage-`r` codeword is absent from the used set at stage `r`.
- `elementCodeUsed_mono`: the used-code finsets are monotone in stage.
- `earlier_elementCodeword_used`: a codeword allocated at `r` is in every used set at a later stage `s`.
- `elementCodingCell_infinite`: each empty-history coding cell is infinite.
- `elementCodingCell_subset`: the cell for index `i` is contained in `langs i`.
- `elementCodingCell_pairwiseDisjoint`: cells for distinct indices are disjoint.
- `elementCodingCell_cofinal`: above every natural bound there is an element of each cell.
- `elementHistoryPrefix_zero` and `elementHistoryPrefix_succ`: exact empty-prefix and append-current equations.
- `decodeElementCode_code`: decoding any valid codeword returns its exact index/history/salt triple.
- `codingCompiledGenerator_gt_state` and `codingCompiledGenerator_gt_input`: the compiled next state is strictly above the prior state and current input.
- `mem_elementCodingBadSet`: an element in a finite one-sided hypothesis error is in the global bad set.
- `incrementalLearnerOnHistory_prefix`: replaying the incremental learner on the first `t` stream values equals its run state at `t`.

### `MemorylessDensity.lean`

- `finiteSignaturePiece_finite`: every conditionally retained finite-family intersection piece is finite.
- `partitionBadInputs_finite`, `piece_lowerDensity_le_maximum`, `finiteFamilyCore_eq_intersection`, `mem_finiteFamilyCore`, and `finiteFamilyCore_subset` are already translated in §11; their exact names are repeated here because they are support lemmas rather than terminal results.

### `ZeroDensityPartition.lean`

- `paperBlockBoundary_zero` and `paperBlockBoundary_succ`: the two recursion equations for block boundaries.
- `paperBlockIndex_upper`: `n` is strictly below the end boundary of its selected block.
- `paperBlockIndex_lower`: `n` is at least the start boundary of its selected block.
- `paperBlockIndex_le_of_lt_boundary`: if `n` lies before boundary `t+1`, its block index is at most `t`.
- `blockNumber_residue`: `(m*q+i.val) mod m = i.val` for `i : Fin m`.
- `paperBlockIndex_lt_of_lt_boundary_of_residue_ne`: before the end of a foreign-owned block, a position of residue `r` has strictly smaller block index.
- `index_lt_boundary_of_foreign_block`: the corresponding enumeration position lies before the foreign block's start.
- `orderedLowerDensity_nonneg'`: every ordered lower density is nonnegative.

### `SymmetricChain.lean`

- `IsSymmetricChain.exists_rankWitness`: every symmetric-chain proof supplies a lower-rank witness.
- `not_mem_of_subset_range`: `n` is absent from any finset contained in `range n`.
- `erase_insert_fresh`, `insert_fresh_card`, `insert_subset_range_succ`, and `subset_range_succ`: exact erasure, cardinality, and range-containment facts for adjoining the new ground element.
- `mem_longCarrier_iff`: membership in the long carrier is membership in the old chain or equality to the new top.
- `mem_shortCarrier_iff`: membership in the short carrier is insertion of `n` into a non-top old member.
- `insert_fresh_injective_on`: insertion of the fresh element is injective on subsets of `range n`.
- `erase_mem_of_mem_long` and `erase_mem_of_mem_short`: erasing `n` from a member of either new carrier returns an old-chain member.
- `mem_short_has_new`: every short-carrier member contains `n`.
- `erase_subset_range` and `insert_erase_new`: erasure returns a subset of `range n`, and reinserting a present `n` recovers the original set.
- `origin_eq_of_common_member`: two old chains giving rise to new carriers with a common member must be the same old chain.
- `nextCarrier_eq_long_or_short`: any next-stage chain containing a member from an old chain's split is that old chain's long or short carrier.
- `chainLow_le_half` and `half_le_chainHigh`: the chosen lower rank is at most `n/2`, which lies below the high rank.
- `codeEmbedding_univ`: the image of the finite-type universe under the chosen code embedding is `range (card α)`.
- `mem_decodeFinset_iff`, `decode_map_code`, `map_decode_of_subset`, and `decode_card_of_subset`: exact membership, inverse, and cardinality facts for finite-set transport.
- `decode_subset_decode` and `decode_injective_on_range`: transport preserves inclusion and is injective on the canonical finite range.
- `mem_decodeCarrier_iff`: membership in a decoded chain is existence of an old member decoding to the given finset.
- `decodeCarrier_injective_on_decomposition`: distinct old decomposition chains remain distinct after decoding.
- `decodeChains_finite` and `decodeChains_ncard`: decoded chain sets are finite and preserve chain count.
- `decodeCarrier_symmetric`: decoding transports the symmetric-chain predicate.
- `map_code_subset_range`: every encoded finite subset lies in the canonical range.

### `SpernerHardInstance.lean`

- `mem_roundRobinPiece_iff`: membership is exactly the residue equation.
- `spernerTarget_prefixCount_roundRobin_eq_filter`: the prefix count equals the cardinality of the residue-filtered initial range.
- `prefixCount_roundRobin_lower` and `prefixCount_roundRobin_upper`: the count is between `n/N` and `n/N+1` for `N>0`.
- `roundRobinPiece_subset_hardLanguage`: a piece is contained in side language `j` when the piece signature contains `j`.
- `spernerHardFamily_zero` and `spernerHardFamily_succ`: exact target and side-language unfolding equations.
- `twoHardFamily_zero` and `twoHardFamily_one`: exact unfolding of the two endpoint languages.
- `twoHardFamily_injective` and `twoHardFamily_infinite`: the endpoint family has two distinct infinite languages.
- `orderedUpperDensity_le_one`: every ordered upper density is at most one.

### `SpernerAchievability.lean`

- `mem_infiniteRelativeSignatures_iff`: membership is equivalent to infinitude of the exact relative region.
- `mem_minimalInfiniteSignatures_iff`: membership is equivalent to minimality among infinite-region signatures.
- `indexedUnion_empty`: the union over an empty finite index set is empty.
- `indexedUnion_insert`: inserting an index turns the indexed union into the union of its set with the prior indexed union.

### `MinimaxClosure.lean`

- `orderedUpperDensity_nonneg'`: every ordered upper density is nonnegative.
- `zeroLowerDensityHardFamily_zero` and `zeroLowerDensityHardFamily_succ`: exact unfolding of the target and side entries.
- `zeroLowerDensityPieces_injective`: for `m≥1`, distinct partition indices give distinct zero-density pieces.
- `zeroLowerDensityPiece_ne_carrier`: no one such piece equals the full carrier when `m≥1`.

### `DistinctWindows.lean`

- `baseEnum_mem` and `baseEnum_injective`: the chosen base enumeration lies in `L` and is injective.
- `exists_baseEnum_not_mem`: every finite forbidden set misses some base-enumeration value.
- `nextBase_mem` and `nextBase_not_mem`: the selected pivot lies in `L` and outside the forbidden set.
- `selectedBlock_zero` and `selectedBlock_succ`: exact pivot and bad-window entries of a selected block.
- `subset_advance` and `selectedBlock_mem_advance`: prior used points and all current block points belong to the advanced finset.
- `used_mono`: used finsets are monotone in stage.
- `block_fresh_at_stage` and `earlier_block_used`: a current block is fresh from the current used set, while every earlier block belongs to every later used set.
- `pivot_at_stage`: the first position of stage `s` in the flattened presentation is the stage pivot.

### `WindowHardInstance.lean`

- `betweenWindowSquares_nonsquare` and `betweenWindowSquares_strictMono`: the explicit separator witnesses are nonsquares and form a strictly increasing sequence.
- `windowHardTarget_prefixCount_separator`: separator prefix count equals the number of square positions below `n`.
- `count_windowSquare_le_sqrt_add_one`: that number is at most `sqrt(n)+1`.
- `tendsto_natSqrtCast_atTop` and `tendsto_sqrt_add_one_div`: the real square root diverges and `(sqrt(n)+1)/n` tends to zero.
- `windowHardTarget_prefixCount_positivePiece_le` and `windowHardTarget_prefixRatio_positivePiece_le`: positive-piece counts and ratios are bounded by the corresponding round-robin piece.
- `windowPositivePiece_subset_hardLanguage` and `windowSeparator_subset_hardLanguage`: the defining positive pieces and separator lie in the appropriate side languages.
- `windowHardLanguage_ne_univ` and `windowHardLanguage_injective`: for `n≥2`, side languages are proper and pairwise distinct.
- `windowHardFamily_zero`, `windowHardFamily_succ`, `windowHardFamily_injective`, and `windowHardFamily_infinite`: exact unfolding, distinctness for `n≥2`, and infinitude.
- `identityWindow_apply`: the `i`th identity-window entry is `start+i`.
- `windowRunUpperDensity_le_one`: every window run upper density is at most one.
- `windowRunUpperDensity_ge_of_frequently` and `windowRunUpperDensity_le_of_eventually`: frequent pointwise lower bounds and eventual pointwise upper bounds transfer to the outer window `limsup`.
- `windowAdmissibleUpperDensities_bddAbove`: the admissible window values are bounded above by one.

### `AdaptiveBuffer.lean`

- `mem_bufferResidual_iff`: an index is residual exactly when its language contains every value in the buffer list.
- `greedyBufferUpdate_of_shouldStore` and `greedyBufferUpdate_of_not_shouldStore`: exact append and no-change cases of the greedy update.
- `greedyBufferState_zero` and `greedyBufferState_succ`: exact empty-initial and successor-state equations.
- `greedyBufferState_succ_of_shouldStore` and `greedyBufferState_succ_of_not_shouldStore`: exact state evolution in the two storage branches.
- `greedyBufferState_length_step_le`, `greedyBufferState_length_mono`, and `greedyBufferState_length_strict_of_shouldStore`: length is nondecreasing and strictly increases at store times.
- `bufferResidual_eq_of_val_eq`: buffer states with equal underlying lists have equal residuals.
- `bufferResidual_append`: when a new state list is the old list with `x` appended, its residual equals `bufferResidualAfter`.
- `bufferResidualCore_eq_residualCoreFor`: the two residual-core definitions are definitionally equal.
- `bufferOutputAt_greedyBufferGenerator`: the greedy run output unfolds to `bufferCanonicalOutput` at the greedy state and current input.

### Umbrella file

`GenLimitLean/GenLimit/Paper31_BoundedMemory.lean` contains imports only and introduces no public declaration.
