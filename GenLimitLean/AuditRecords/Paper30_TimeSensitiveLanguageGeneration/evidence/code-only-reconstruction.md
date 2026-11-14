# P30: code-only Stage 1 reconstruction

## Scope and input census

This is a statement and definition reconstruction, with source content withheld. It covers all four opaque slots and all eight distinct supplied targets. C01 and C02 have exactly the same supplied endpoint; nothing in this package establishes a semantic distinction between those slots. All slots have endpoints, and the slot file reports no absent linked names.

Read inputs: `stage1/START_HERE.md`, `stage1/PROMPT.md`, `stage1/claim-slots.json`, `stage1/01-target-statements.md`, all of `stage1/02-definition-dependencies.md`, `stage1/declarations.jsonl`, `stage1/native-declaration-census.jsonl`, `stage1/targets.txt`, `stage1/snapshot.json`, `stage1/external-boundary.txt`, and `stage1/SHA256SUMS`. All ten manifest entries match their SHA-256 hashes; exact hashes of all eleven files are in `stage1-run.json`. An initial attempt to read `P30/PROMPT.md` found no file and supplied no evidence; the actual prompt is inside Stage 1.

The recursive extract has 118 records: 84 definitions, 24 theorem types, five inductives and five constructors. All target types and recursively necessary definition values in that extract were inspected. The native census has 1,071 records (754 theorem types, 287 definitions, ten each inductives/constructors/recursors). It was parsed as supporting code, not individually reviewed in full. Selected census statements about the run's output history and stage bound support the operational reading below; their proofs were not inspected. The manifest's source snapshot digest is `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc`, recorded as supplied metadata, not independently recomputed from source.

No paper, other stage, registry, PaperMap, human record, previous audit, Git, raw source comment or theorem proof body was consulted. No Lean compilation, mathematical edit, proof certification or source-correspondence assessment occurred. Exported `⋯` tokens suppress proof arguments; they are not evidence of proof holes. All recorded recursive type/value dependencies resolve either within the 118 records or to the explicitly supplied standard Lean/Mathlib boundary. No decisive project definition is missing. Standard meanings of finite sets, classical choice, limits and real division are trusted.

## Shared definition glossary

Here and below `TS` abbreviates `GenLimit.TimeSensitive`, `DM` abbreviates `GenLimit.KleinbergWei.DensityMeasures`; these are display abbreviations only. `∀ eventually` means there exists a natural threshold after which every natural index satisfies the predicate. Limits, liminf and limsup are along natural `atTop`; all density values are real numbers.

**Finite sets and deadlines.** For a sequence `A : Nat → α`, write `P_A(n) = {A(k) | k < n}`. This is `TS.sequencePrefix A n`; `TS.targetPrefix R i = P_R(i)`. Sets count distinct values, so repetitions do not create extra elements. Define

- `PW(S,R,F,i) = P_R(i) ∩ P_S(F(i))` (`prefixWiseElements`).
- `TW(S,R,D,i) = {R(j) | j < i and R(j) ∈ P_S(D(j))}` (`timelyElements`). Thus timeliness requires an output time **strictly below** `D(j)`; being output exactly at that time is insufficient.
- `p(S,R,F,i) = |PW|/i` and `d(S,R,D,i) = |TW|/i` for `i > 0`, each explicitly zero at `i = 0` (`prefixWiseDensity`, `timelyDensity`). The denominator is the number of ranks `i`, even when `R` repeats values.
- `lowerPrefixWiseDensity = liminf p`, `lowerTimelyDensity = liminf d`, `upperTimelyDensity = limsup d`.
- `targetIntersectionCount R L i = |{x ∈ P_R(i) | x ∈ L}|`.

`TS.Deadline` packages a function `D : Nat → Nat` and monotonicity. `IsUnbounded` is `∀ t, ∃ n, t ≤ D(n)`. Given that proof, `D.inverse(t)` is the least `n` with `t ≤ D(n)`, not the last rank below time `t`. `NatSuperlinear` is `∀ q > 0, ∃ N, ∀ n ≥ N, q*n ≤ D(n)`. `EventuallyStrict` is `∃ N, ∀ a b, N ≤ a → a < b → D(a) < D(b)`.

`deadlineExceptionCount D F i = |{j < i | D(j) < F(i)}|`; its ratio is that count divided by `i` for positive `i`, zero at zero. Notice the strict exception inequality. `catchupRatio e i = e(i)/i`, again zero at zero. `natRatio g i = g(i)/i` with the same zero convention. All casts in these ratios are to `Real`.

**Languages and the named index selector.** `GenLimit.Language = Set Nat`, `LanguageFamily = Nat → Set Nat`. `Presents stream L` means `range stream = L`; repetitions and arbitrary presentation order are permitted. `sample stream t = {stream(k) | k < t}`. `Consistent C stream t n` means this sample is a subset of `C(n)`.

`DM.FirstOccurrence C z` means `∀ i < z, C(i) ≠ C(z)`; later duplicates are allowed. `SC_t(n)`, abbreviating `StrictCritical C stream t n`, means consistency at `n` **and** `∀ i < n, Consistent C stream t i → C(n) ⊊ C(i)`. It uses strict containment of full languages, not a finite-sample approximation. The exact deterministic selector is:

1. `scopedStrictCriticalIndices` is `{n < t+1 | SC_t(n)}`; `scopedFocus` is its greatest element if nonempty, otherwise `0` (`greatestCandidateWithFallback`).
2. `BadStrictCritical C stream t w n` is `SC_t(n) ∧ w ∉ C(n)`. `firstBadStrictCritical` is the least such `n` if any exists, otherwise `0`.
3. `boundaryCandidates` is `{n < firstBadStrictCritical | SC_t(n) ∧ w ∈ C(n)}`.
4. `selectIndex C stream t w` uses `scopedFocus` when **every** strict-critical language contains `w`. Otherwise it takes the greatest boundary candidate if nonempty, falling back to `scopedFocus` if empty.
5. `g(0) = 0`; `g(t+1) = selectIndex C stream t (stream(t))`, where `g = DM.guessIndex C stream`.

Thus `g(t+1)` uses the sample strictly before time `t` plus the current symbol `stream(t)`. The selector is a named, total classical mathematical function of the entire family and the finite stream prefix. It branches on unrestricted subset/strict-subset relations, quantification over all indices and existence of a bad index, with `Classical.propDecidable` and least-number selection. No effective family, decision-oracle interface, ordinary computability theorem, runtime bound or randomized law is an input or conclusion of these targets.

`AccurateAt C stream z r` means `C(g(r)) = C(z)`, not necessarily `g(r) = z`. `IndexValidInLimit` means `∃ T, ∀ t ≥ T, C(g(t)) ⊆ C(z)`.

**Ordered family and named output machine.** `KleinbergWei.OrderedLanguage` consists of a carrier `L`, an injective enumeration `e : Nat → Nat`, and `range e = L`. Consequently every such carrier is infinite. `TS.CanonicallyOrderedFamily F` packages a language family, one such order for each index with matching carrier, and the additional requirement that equal languages have exactly equal enumeration functions. `F.guess stream t = DM.guessIndex F.language stream t`.

For an order `O`, `OnTimeUnusedRank O used t r` is `t < r ∧ O.enumeration(r) ∉ used`. `onTimeUnusedRank` is the **least** such `r`, and `onTimeUnused` is the corresponding enumerated value. Its supplied existence type is for every ordered language, finite used set and time; there is no finite/exhausted-order fallback. `greedyUsed stream t outputs = sample stream (t+1) ∪ outputs.toFinset`; `greedyRoundOutput` applies this least-rank choice. It avoids all observed inputs through time `t` and all prior outputs. It is one output value per time, not a set-valued support or distribution.

The machine state is `(stage : Nat, outputs : List Nat)`, initially `(0, [])`. At time `t` with old state `(s,h)`:

- `a = F.guess stream (s+1)` (`totalizedRoundActive`; its time argument itself is ignored).
- `y = greedyRoundOutput (F.order a) stream t h` (`totalizedRoundOutput`).
- Append `y` to `h`, obtaining `h'`.
- Define `crossed` by `gcgThreshold(s+1) ≤ d(outputHistoryStream h', (F.order a).enumeration, id, t+1)`, where `gcgThreshold(m) = 1/2 - (1/2)^m` and `outputHistoryStream h' k = h'.getD k 0`.
- Set the next stage to `s+1` iff **both** `s < t` and `crossed` hold; otherwise retain `s`. Store `h'` in either case. Equality with the threshold is sufficient.

`totalizedGCGRun F stream 0` is the initial state; `Run(t+1) = Step F stream t (Run(t))`. `totalizedGCGOutput F stream t` is the round output from `Run(t)`, so the displayed output and the appended output are the same witness. Write this sequence as `Y_{F,stream}`. The recursion gives the output history through times `<t`; the supplied census statements `totalizedGCGRun_outputs_eq`, `outputs_length`, `outputs_succ`, `outputs_toFinset` and `stage_le_time` explicitly state the corresponding history identities and `stage ≤ t`. Their types were used as supporting evidence, not their proof steps certified. Hence the active guess uses inputs through stage `s ≤ t`, and the greedy choice uses inputs through `t`. The named output takes `F` and `stream`; it does not take the target index `z` or an exception function. Classical operations in the selector and real threshold comparison prevent inferring an ordinary executable implementation from this definition alone.

**Constructed rate profile.** For the rate target, `a(t)=D.inverse(t)` and `B(t)=flooredRateBudget H t = floor_Nat(t*H(t))`. `NatLittleOAlongRealBudget a b` is exactly `∀ q > 0, ∃ T, ∀ t ≥ T, (q*a(t) : Real) ≤ b(t)`. Its natural-budget variant replaces that last inequality by `q*a(t) ≤ B(t)`. `NatSublinear f` is `∀ q > 0, ∃ N, ∀ i ≥ N, q*f(i) ≤ i`.

`NaturalFeasibleProfile` stores a deadline, its natural-superlinearity and eventual-strictness proofs, a natural budget tending to infinity and its natural little-o condition. `P = ofRawRate D hD hstrict H hfeasible` has precisely deadline `D` and budget `B`; its additional proof fields are supplied, not separately audited. The rest of its named rate construction is:

- `deadlineMidpointScale D n = Nat.sqrt(n*D(n))`; `slowDeadlineWitness D hD i` is the least `n` with `i ≤ deadlineMidpointScale D n`.
- For a budget `B → ∞`, `inverseBudgetEnvelope D ... B ... m n` is the least `Q > 0` such that `∀ t, B(t)/(m+1) ≤ n → D.inverse(t) < Q`, where `/` here is natural division. The supplied existence type is `inverseBudgetBound_exists`. The test quantifies over all times and is classical.
- `f_0 = slowDeadlineWitness`; `f_{m+1}(n) = inverseBudgetEnvelope D ... B ... m n` is `P.diagonalFamily`. Its monotonicity and natural sublinearity appear as supplied theorem types.
- `sublinearThreshold f hf m q` chooses a threshold `N` with `∀ i ≥ N, (q+1)*f_m(i) ≤ i` by `Classical.choose`. This is a chosen witness, not a least one.
- `A(0)=0`; `A(k+1)=max(A(k)+1, max((k+1)^2, max_{m<k+2} sublinearThreshold f hf m k))` is `diagonalCutoff`. `ell(i)` is `Nat.findGreatest (A(k) ≤ i) i`, i.e. the greatest qualifying `k ≤ i` (`diagonalLevel`). Then `c(i)=max(ell(i), max_{m<ell(i)+1} f_m(i))` is `countableDiagonal`.
- `P.prefixDeadline(i)=D(c(i))` (`slowedDeadline` applied to that family); call it `D'`. Its unboundedness is supplied as a theorem type.
- `P.prefixTau(t)=D'.inverse(t+1)` (`strictDeadlineInverse`); `P.prefixBudget(t)=Nat.sqrt(P.prefixTau(t)*B(t))`.
- `P.prefixRate(t)=natRatio P.prefixBudget t`; `r(t)=P.monotonePrefixRate(t)=sup_{u ≥ t} P.prefixRate(u)` (the real `iSup` in the exported definition).

This fixes the rate witness, including choice-dependent thresholds and its distinction between the strict inverse at `t+1` in `prefixTau` and the inverse at `t` in the final conclusion. There is no language-generation algorithm in this rate endpoint.

## Per-target dossiers

The exact kernel types, including universe/implicit binders and explicit instances, are at the cited JSONL rows and the corresponding heading in `01-target-statements.md`. The following formulas normalize notation only; source anchors are exported metadata, not independently inspected source files.

### T1 — finite counting (C01 and C02)

**Identifier:** `GenLimit.TimeSensitive.Results.theorems_1_2_pathwise_counting_core`. Theorem; exported source `GenLimit.Paper30_TimeSensitiveLanguageGeneration.Results.Overview:49`; exact type `[declarations.jsonl, row 67](../stage1/declarations.jsonl#L67)`.

**Complete normalized type / quantifier skeleton:**

`∀ {α : Type u} (S R : Nat → α) (L : Set α) {T i t : Nat}, (∀ k : Nat, T ≤ k → S(k) ∈ L) → |PW(S,R,(fun _ => t),i)| ≤ targetIntersectionCount R L i + T`.

Thus for any such sequences, target set and three natural parameters, eventual membership of every output from the specified time `T` implies the finite number of distinct target-prefix values appearing among outputs before `t` is at most the number of distinct target-prefix values in `L`, plus `T`. `T` is an input bound in the hypothesis, not an existentially constructed uniform time. There is no relation required between `i`, `t` and `T` and no injectivity, presentation, correctness-before-`T`, deadline or density hypothesis. The conclusion is a single finite cardinality inequality, with exactly additive constant `T`.

**Access / edge cases:** This concerns supplied paths; it specifies no learner, family oracle, randomness or computation. Repeated input/output values are deduplicated. At `i=0` or `t=0` the left set is empty; `T=0` requires all outputs in `L`. An empty `L` cannot satisfy the tail-membership hypothesis for a supplied total `S`, so that implication is vacuous. C01/C02 share this dossier without inventing a second claim.

### T2 — constructed rate envelope (C03)

**Identifier:** `GenLimit.TimeSensitive.Results.appendix_D_rate_core`. Theorem; exported source `GenLimit.Paper30_TimeSensitiveLanguageGeneration.Results.Overview:72`; exact type `[row 61](../stage1/declarations.jsonl#L61)`.

**Complete normalized type / quantifier skeleton:** For every `D : Deadline`, `hD : D.NatSuperlinear`, `hstrict : D.EventuallyStrict`, and `H : Nat → Real`, assume in order `(∀ t, 0 ≤ H(t))`, `Antitone H`, `H → 0`, and `hfeasible : NatLittleOAlongRealBudget (D.inverse ...) (fun t => t*H(t))`. With the **named** `P = NaturalFeasibleProfile.ofRawRate D hD hstrict H hfeasible`, and `r=P.monotonePrefixRate`, the conclusion is

`Antitone r ∧ (r → 0 ∧ ((∀ eventually t, r(t) ≤ H(t)) ∧ ((fun t => natRatio (P.prefixDeadline.inverse ...) t / r(t)) → 0)))`.

All four conjuncts concern this same constructed profile. Each `q>0` feasibility threshold may depend on `D,H,q`; the eventual domination time and convergence witnesses may depend on all inputs. The quotient uses the inverse of **the constructed prefix deadline**, not the original deadline. `hfeasible` is an explicit, unproved-by-this-statement premise, not a consequence asserted for every vanishing rate. See the glossary for the entire recursively fixed witness construction, natural flooring, square roots and chosen thresholds.

**Access / edge cases:** This is a deterministic semantic rate construction using global functions, least witnesses, classical choice and a real tail supremum; no uniform effective program or complexity bound follows. There is no existential unspecified replacement rate and no generator/density guarantee in this type. The statement does not separately assert strict positivity of `r`; real division is Lean's total division (including denominator zero). All basic ratios are zero at time zero. `H≡0`, though nonnegative/antitone/vanishing, cannot satisfy the feasibility premise for an unbounded deadline inverse; the premise must be retained. No convergence rate or uniform threshold across deadlines/raw rates is supplied.

### T3 — lower density transfer (C03)

**Identifier:** `GenLimit.TimeSensitive.Results.lemma_2_density_endgame`. Theorem; exported source `GenLimit.Paper30_TimeSensitiveLanguageGeneration.Results.Overview:60`; exact type `[row 62](../stage1/declarations.jsonl#L62)`.

**Complete normalized type / quantifier skeleton:**

`∀ {α : Type u} (S R : Nat → α), Injective R → ∀ (D : Deadline) (F : Nat → Nat), (deadlineExceptionRatio D F → 0) → lowerPrefixWiseDensity S R F ≤ lowerTimelyDensity S R D.toFun`.

For the supplied injective rank enumeration, if the fraction of ranks `j<i` with `D(j)<F(i)` tends to zero, then the liminf density of target-prefix values found before common time `F(i)` is at most the liminf fraction found before their individual deadlines `D(j)`. No monotonicity, growth, little-o representation or computability assumption is imposed on `F`; `D` has only its packaged monotonicity here. Its unboundedness is not required. The premise is a full limit to zero and the conclusion compares two liminfs; it neither creates `F` nor asserts a pointwise inequality at every `i`.

**Access / edge cases:** No presentation or eventual-correctness premise on `S`, no language family, named learner or probabilistic law. Repetitions in `S` are allowed; repetitions in `R` are excluded by the explicit injectivity hypothesis. At zero all densities/exception ratios are zero. The equality `D(j)=F(i)` is not exceptional because both prefixes use strict output-time boundaries. Bounded deadlines are not excluded if the given exception-limit premise holds, for example with identically zero `F`.

### T4 — upper density implication (C04)

**Identifier:** `GenLimit.TimeSensitive.Results.theorem_4_density_endgame`. Theorem; exported source `GenLimit.Paper30_TimeSensitiveLanguageGeneration.Results.Overview:101`; exact type `[row 63](../stage1/declarations.jsonl#L63)`.

**Complete normalized type / quantifier skeleton:**

`∀ {α : Type u} (S R : Nat → α), (∀ m N : Nat, ∃ i : Nat, N ≤ i ∧ (1/2-(1/2)^m) ≤ d(S,R,id,i)) → 1/2 ≤ upperTimelyDensity S R id`.

For every approximation level and every lower time bound, the premise supplies some possibly level/bound-dependent index at which the density is at least that level's threshold. Its conclusion is a limsup lower bound, with the identity deadline `D(j)=j`. It does not assert eventual density at least `1/2`, a liminf bound, a true density limit, or attainment of `1/2` at any finite time. The cofinal threshold-crossing premise is retained and not established here.

**Access / edge cases:** Arbitrary sequences and arbitrary `α`; no injectivity, language membership, family, learner or random semantics. Thresholds at `m=0` and `m=1` are `-1/2` and `0`; all larger approximation levels are still quantified. Time zero has density zero and cannot discharge the positive-level premise beyond arbitrary `N`. Repeated ranks are counted as distinct values only once.

### T5 — named output lower bound and correctness (C04)

**Identifier:** `GenLimit.TimeSensitive.Results.theorem_4_totalized_gcg_lower`. Theorem; exported source `GenLimit.Paper30_TimeSensitiveLanguageGeneration.Results.Overview:115`; exact type `[row 66](../stage1/declarations.jsonl#L66)`.

**Complete normalized type / quantifier skeleton:**

`∀ (F : CanonicallyOrderedFamily) (stream : Nat → Nat) (z : Nat), Presents stream (F.language z) → FirstOccurrence F.language z → ((∃ T : Nat, ∀ t : Nat, T ≤ t → Y_{F,stream}(t) ∈ F.language z) ∧ 1/2 ≤ upperTimelyDensity Y_{F,stream} (F.order z).enumeration id)`.

For each given presentation and first-occurring target index, the **same named output sequence** has both eventual target membership and upper timely density at least one half in that target's specified enumeration. The correctness threshold may depend on the family, stream and target. The procedure itself receives `F,stream`, not `z`, and is fixed before this threshold exists. Its exact access/state/update/output rules are in the glossary.

**Access / edge cases:** No distribution, law, full-support condition, expected loss or probability-one quantifier occurs. The claim is per deterministic presentation, hence also universally applicable by its outer binders, but it supplies no effective uniform program or uniform correctness time. The ordered-family constructor excludes empty and finite target languages. Stream repetitions and repeated language indices remain allowed; the first-occurrence premise restricts earlier equal languages, while canonical ordering synchronizes all equal languages. The conclusion is limsup, not liminf or an eventual half-density bound. Correctness means eventual membership; freshness follows from the named output rule, not a separate conjunct in this target.

### T6 — conditional exact upper density (C04)

**Identifier:** `GenLimit.TimeSensitive.Results.theorem_4_totalized_gcg_eq_of_turnTaking`. Definition alias with value `GenLimit.TimeSensitive.totalizedGCG_theorem_4_eq_of_turnTaking`; exported source `GenLimit.Paper30_TimeSensitiveLanguageGeneration.Results.Overview:130`; exact type `[row 65](../stage1/declarations.jsonl#L65)`. The aliased theorem's supplied anchor is `GenLimit.Paper30_TimeSensitiveLanguageGeneration.TotalizedGCGMain:195`.

**Complete normalized type / quantifier skeleton:** For every `F,stream,z`, assume `Presents stream (F.language z)` and `FirstOccurrence F.language z`; then for every `exceptions : Nat → Nat`, assume

`∀ eventually i, 2*|TW(Y_{F,stream},(F.order z).enumeration,id,i)| ≤ i + 2*exceptions(i)`

and `catchupRatio exceptions → 0`. The conclusion is

`(∃ T : Nat, ∀ t ≥ T, Y_{F,stream}(t) ∈ F.language z) ∧ upperTimelyDensity Y_{F,stream} (F.order z).enumeration id = 1/2`.

The exception function is an arbitrary universally bound input after the presentation premises. Its eventual numeric counting inequality and vanishing normalized size are both required; the theorem does not construct it or assert them for every presentation. The counting-inequality threshold and correctness threshold need not be equal, and may depend on these data. Equality concerns the same named output sequence as T5, with exactly the same density scale.

**Access / edge cases:** This type supplies no additional turn-taking algorithm, pairing rule or stream restriction beyond its two explicit numeric hypotheses. No monotonicity or computability of `exceptions` is required. Its zero-time ratio is defined as zero, and the counting premise is merely eventual. Family, repetition and classical-computation boundaries are as in T5. Exact limsup `1/2` does not imply convergence of densities or eventual equality at finite times.

### T7 — universal named guarantee and exact-density presentation (C04)

**Identifier:** `GenLimit.TimeSensitive.Results.theorem_4_totalized_gcg`. Definition alias with value `GenLimit.TimeSensitive.totalizedGCG_theorem_4`; exported source `GenLimit.Paper30_TimeSensitiveLanguageGeneration.Results.Overview:135`; exact type `[row 64](../stage1/declarations.jsonl#L64)`. The aliased theorem's supplied anchor is `GenLimit.Paper30_TimeSensitiveLanguageGeneration.TotalizedGCGMain:255`.

**Complete normalized type / quantifier skeleton:** For every `F : CanonicallyOrderedFamily` and `z : Nat`, `FirstOccurrence F.language z` implies the conjunction

1. `∀ stream : Nat → Nat, Presents stream (F.language z) → ((∃ T, ∀ t ≥ T, Y_{F,stream}(t) ∈ F.language z) ∧ 1/2 ≤ upperTimelyDensity Y_{F,stream} (F.order z).enumeration id)`;
2. `∃ stream : Nat → Nat, Presents stream (F.language z) ∧ ((∃ T, ∀ t ≥ T, Y_{F,stream}(t) ∈ F.language z) ∧ upperTimelyDensity Y_{F,stream} (F.order z).enumeration id = 1/2)`.

The universal branch's threshold can depend on each stream; the existential branch chooses a presentation depending on `F,z` and then a threshold for that very presentation. Both branches use the same named map `Y`, not independently chosen generators. All presentation/correctness/density conjuncts are retained. The existential witness is semantic existence in the supplied type; no named construction, causality, oracle or computability property of that particular stream is claimed here.

**Access / edge cases:** This does not give density at most one half for every presentation: only the existential presentation attains equality, while the universal branch supplies a lower bound. It gives no lower-density guarantee and no universal true limit. The output algorithm, classical access, infinite-carrier restriction, canonical order and duplicate-index conditions are exactly those of T5. No randomized generator or measurable/adaptive adversarial game is quantified in this target.

### T8 — named selector's eventual validity and cofinal accuracy (C04)

**Identifier:** `GenLimit.TimeSensitive.appendix_E_accurate_oracle_from_paper07`. Theorem; exported source `GenLimit.Paper30_TimeSensitiveLanguageGeneration.AccurateBridge:25`; exact type `[row 73](../stage1/declarations.jsonl#L73)`.

**Complete normalized type / quantifier skeleton:**

`∀ {C : LanguageFamily} {stream : Nat → Nat} {z : Nat}, Presents stream (C z) → FirstOccurrence C z → (IndexValidInLimit C stream z ∧ (∀ t : Nat, ∃ r : Nat, t ≤ r ∧ AccurateAt C stream z r))`.

After unfolding, the conclusion is precisely

`(∃ T : Nat, ∀ u : Nat, T ≤ u → C(g(u)) ⊆ C(z)) ∧ (∀ t : Nat, ∃ r : Nat, t ≤ r ∧ C(g(r)) = C(z))`,

where **both conjuncts use the fixed** `g = DM.guessIndex C stream` reconstructed in the glossary. The single eventual-validity threshold depends on `C,stream,z`; each accurate time `r` can additionally depend on the requested bound `t`. Accuracy is cofinal/infinitely often with weak boundary `t≤r`, not eventual equality, index stabilization, or a prescribed rate of accurate times. Equality of languages need not be equality of indices, even under the first-occurrence premise because later equal copies are permitted.

**Access / edge cases:** `C` is any family of subsets of naturals; no infinitude, computable membership, ordered enumeration or canonical-order hypothesis occurs here. A presentation of an empty target cannot exist, but nonempty finite targets are allowed. Repetitions in the presentation and family remain allowed; the `z=0` first-occurrence premise is vacuous. The theorem provides a named total classical selector property, not an explicitly represented oracle procedure or ordinary-computability result. No density, freshness, word-generation, stochastic law or uniform bound on `T`/`r` is asserted.

## Exhaustive slot and target coverage

| Slot | Supplied exact targets | Dossiers | Outcome |
|---|---|---|---|
| C01 | `GenLimit.TimeSensitive.Results.theorems_1_2_pathwise_counting_core` | T1 | Complete finite counting statement |
| C02 | `GenLimit.TimeSensitive.Results.theorems_1_2_pathwise_counting_core` | T1 | Same supplied endpoint; no invented distinction |
| C03 | `GenLimit.TimeSensitive.Results.appendix_D_rate_core`; `GenLimit.TimeSensitive.Results.lemma_2_density_endgame` | T2, T3 | All four rate conjuncts and conditional liminf transfer |
| C04 | `GenLimit.TimeSensitive.Results.theorem_4_density_endgame`; `GenLimit.TimeSensitive.Results.theorem_4_totalized_gcg`; `GenLimit.TimeSensitive.Results.theorem_4_totalized_gcg_eq_of_turnTaking`; `GenLimit.TimeSensitive.Results.theorem_4_totalized_gcg_lower`; `GenLimit.TimeSensitive.appendix_E_accurate_oracle_from_paper07` | T4, T7, T6, T5, T8 | Every supplied endpoint and all conjunctions reconstructed |

No slot is absent/unlinked and no supplied target was omitted. This dossier stops at code-only reconstruction for coordinator validation and freeze; it makes no comparison with withheld source claims.
