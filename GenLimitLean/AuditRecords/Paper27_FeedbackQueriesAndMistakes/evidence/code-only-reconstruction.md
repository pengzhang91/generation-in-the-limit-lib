# P27 — Stage 1 code-only reconstruction

## Evidence and scope

This is a reconstruction of exported Lean interfaces, not a judgment about a withheld source. All input reads were confined to `stage1/`. There are **10 opaque slots, 13 target declarations, 134 recursive interface records (103 definitions, 6 inductives, 6 constructors, 19 theorem statements), and 1,457 native census records**. All supplied targets are present; no slot is unlinked or endpoint-free. The recursive records contain 13 target theorem statements and 6 supporting theorem statements; no theorem proof values are supplied or reviewed. Definition values and constructor types were read as semantic evidence. Pretty-printer `⋯` suppresses proof terms, not mathematical conditions.

Primary exact-type anchors below are the 1-based lines of `stage1/declarations.jsonl`; readable copies occur under the matching identifier headings in `01-target-statements.md` and `02-definition-dependencies.md`. Reported module/line anchors are export metadata, not raw sources opened by this reviewer. Every one of the 134 recursive records matches the native census in identifier and type. The census was parsed for this support check and metadata; its 1,457 helpers were not all individually interpreted.

`external-boundary.txt` authorizes standard Lean/Mathlib meanings. The recursive dependency boundary consists of the listed standard primitives, collections, logic, classical choice/decidability, and instance projections. No decisive unknown project definition remains outside the supplied recursive records. Mathlib internals, proof correctness, compilation, source correspondence, intended theorem naming, and human certification remain outside this stage. No source paper, later stage, owner notes, PaperMap, registry interpretation, prior audit, raw Lean comment/proof, Git state, browser, or build was accessed. No additional agents were spawned.

All learner/strategy quantification below is **semantic existence of total functions**. Neither `Countable` nor an existential strategy supplies a computable enumeration, ordinary program, effective uniform compiler, query complexity bound, or runtime guarantee. Several named interface functions explicitly use `Classical.choose` and classical proposition decisions. Oracle replies are specified by their equations; they are not implemented membership decision procedures for arbitrary target sets. Outputs are elements or entire sets, never probability laws or randomized support guarantees. No rate, numerical mistake bound, or uniform stabilization time occurs.

## Shared definition glossary

The exact identifiers and record anchors for each group appear in the provenance table after the glossary. Let `H : Set (Set α)` be a target class, `s : Nat → α` a stream, `P_t(s) = [s(0), …, s(t−1)]`, and `A_t(s)` the finite set of those values. Thus `P_0=[]`, repetitions remain in the list, and `A_t` removes repetitions. Write `x\Hlist` informally as exclusion from the values of a list, not exclusion from previous generated outputs.

### G0. Basic data, presentations, and all-infinite classes

`Language α = Set α`, `LanguageClass α = Set (Set α)`, `Stream α = Nat → α`. `textPrefix` maps the stream over `List.range t`; `streamPrefix` is that same list. `sample s t` is the finite image of `Finset.range t`; `sequenceSample xs` is the finite image of the whole finite tuple. `Presents s L` means exactly `Set.range s = L`: every sample belongs to `L` and every point of `L` appears eventually; no distinctness or order condition. An empty language has no presentation of this form. `UUS H` means `∀L∈H, Set.Infinite L`, with no requirement that `H` itself be nonempty.

### G1. Inner covers

`HasCountableInnerCover H` is `Nonempty (CountableInnerCover H)`. Its constructor supplies `C : Nat → Set α`, a certificate `∀i, Infinite (C i)`, and `∀L∈H, ∃i, C i ⊆ L`. The whole sequence is chosen before the target-dependent index. It is a total Nat-indexed sequence of infinite sets, even if `H` is empty. It need not consist of members of `H`; there is no converse containment, union-equality, disjointness, injectivity, or effective enumeration requirement. Repeated indices/sets are allowed.

`HasFiniteInnerCover H` is `Nonempty (FiniteInnerCover H)`. Its constructor supplies `m : Nat`, `C : Fin m → Set α`, `∀i, Infinite (C i)`, and `∀L∈H, ∃i, C i ⊆ L`. Here `m=0` is allowed and its coverage premise forces `H` empty. The definition does not require a positive cover size or a nonempty class.

### G2. Element output with correctness feedback (`EM`)

A `SourceElementMistakeStrategy α` is `e : List α → List Bool → α`. Define `R_L(h,x)` to be the Boolean that is true exactly when `x∈L ∧ x∉h` (`sourceElementReply`). Feedback is a fold over the supplied sample list, with state `(h,b)` initially `([],[])`. Reading the first sample `a` when `h=[]` produces `([a],b)` without a reply. Every subsequent step on `a` produces

`(h ++ [a], b ++ [R_L(h, e(h,b))])`.

`sourceElementFeedback` takes the second component; `sourceElementOutput e L h = e(h, feedback(e,L,h))`. Thus on a sample prefix of positive length `t`, the current output sees `t` samples and the `t−1` replies to outputs on earlier nonempty sample prefixes. At length zero it sees no samples or replies. The reply for the current output arrives only when the next sample is folded in. The state/update uses the old `h`, before appending that next sample.

`SourceElementMistakeCorrect e L h` requires both membership of the current output in `L` and exclusion from `h`. `EM(H) := SourceElementMistakeGeneratable H` expands to

`∃e, ∀L∈H, ∀s, Presents s L → ∃T, ∀t≥T, sourceElementOutput e L (P_t(s)) ∈ L ∧ sourceElementOutput e L (P_t(s)) ∉ P_t(s)`.

One strategy works for the whole class. `T` may depend on `e,L,s`; no bound is given. Freshness is against observed samples, not all earlier generated outputs.

### G3. Infinite set output with representative correctness feedback (`SM`)

`SourceSetMistakeStrategy` supplies `S : List α → List Bool → Set α` and a constructor certificate `∀h b, Infinite (S h b)`, including malformed histories. The `Countable α` instance is used by `sourceCanonicalRank` to classically choose an injection `α → Nat`. `sourceFirst C hC` chooses a member with the least occurring rank, using `Nat.find` and `Classical.choose`; it depends on the chosen rank map and a nonemptiness certificate. `sourceSetFirst S h b` applies this selection to `S h b`, whose infinitude provides nonemptiness. This is semantic minimum-rank selection, not an effective set enumeration.

The feedback state/fold is the G2 fold with reply `R_L(h, sourceSetFirst S h b)`. Only the selected representative is tested; this Boolean does **not** assert the correctness of the entire set. `sourceSetOutput S L h = S h (sourceSetFeedback S L h)`. `SourceSetMistakeCorrect` requires the **whole** returned set to be contained in `L \ {x | x∈h}`. Therefore

`SM(H) := ∃S with its global infinitude certificate, ∀L∈H, ∀s presenting L, ∃T, ∀t≥T, sourceSetOutput S L P_t(s) ⊆ L \ A_t(s)`.

The same selected `Countable` instance enters feedback and hence this predicate. Output timing is the same as G2.

### G4. Adaptive membership queries with element or infinite set outputs (`EQ`, `SQ`)

`SourceQueryPolicy α` is `(t : Nat) → (Fin (t+1) → α) → List Bool → α`. At round `t` it has the first `t+1` samples and prior replies. Put `B_0=[]` and

`B_{t+1} = B_t ++ [membershipAnswer L (q t (s restricted to Fin(t+1)) B_t)]`.

`membershipAnswer L x` is the classically decided Boolean `x∈L`. This is exactly the recursion of `sourceQueryFeedback`; its generated helper is a Nat case split. The query is issued before its current reply. `SourceElementQueryStrategy` consists of `q` and an element output function `o(t, samples : Fin(t+1)→α, answers)`. `SourceSetQueryStrategy` consists of `q`, a set output function of the same arguments, and a constructor certificate

`∀t samples answers, answers.length=t+1 → Infinite (o t samples answers)`.

No infinitude promise is made at other answer lengths. In either case the actual round-`t` output uses `B_{t+1}`, so **it sees the current query answer**, and the first `t+1` samples. Query and output may be different elements. There is one query per such round; query policies have no target argument.

`EQ(H) := ∃(q,o), ∀L∈H, ∀s presenting L, ∃T, ∀t≥T, sourceElementQueryOutput(q,o,L,s,t) ∈ L \ A_{t+1}(s)`.

`SQ(H) := ∃(q,o,certificate), ∀L∈H, ∀s presenting L, ∃T, ∀t≥T, sourceSetQueryOutput(q,o,L,s,t) ⊆ L \ A_{t+1}(s)`.

These abbreviate `SourceElementQueryGeneratable` and `SourceSetQueryGeneratable`. The actual set output is always infinite because its actual answer list has length `t+1`, including pre-stabilization rounds. A strategy is chosen before `L` and its presentation; the threshold may depend on both.

### G5. No sample inputs, with correctness or membership replies (`ZEM`, `ZSQ`)

`ZeroExampleElementMistakeStrategy α = List Bool → α`. Starting at `b_0=[]`, let `x_t=e(b_t)` and `b_{t+1}=b_t ++ [membershipAnswer L x_t]`. `zeroExampleMistakeOutput` is `x_t`, before the reply to `x_t`. Here correctness feedback is simply membership because no sample exclusion occurs. `ZEM(H)` expands to `∃e, ∀L∈H, ∃T, ∀t≥T, x_t∈L`. There is **no freshness or no-repeat clause**.

`ZeroExampleSetQueryStrategy` supplies `q : Nat → List Bool → α`, `S : Nat → List Bool → Set α`, and `∀t b, b.length=t+1 → Infinite (S t b)`. Feedback obeys `b_{t+1}=b_t ++ [membershipAnswer L (q t b_t)]`. Output at round `t` is `S t b_{t+1}`, after the current reply. `ZSQ(H)` expands to `∃(q,S,certificate), ∀L∈H, ∃T, ∀t≥T, S t b_{t+1} ⊆ L`. Actual sets are infinite at every round; there is no sample stream, presentation, or freshness requirement. These are the two `ZeroExample…Generatable` predicates. Each threshold can depend on its target and fixed strategy; no sample-dependent threshold is needed because no samples enter.

### G6. Eventually correct feedback on arbitrary sample streams (`ECM`, `ECQ`)

Both `…Generatable` predicates first existentially choose a strategy, then universally quantify `L∈H`, **every** sample stream `s : Nat→α`, and **every** observed Boolean stream `v : Nat→Bool`. They have **no `Presents s L` or samples-within-`L` premise**.

For `ECM := EventuallyCorrectMistakeGeneratable`, use a G2 element strategy but round-`t` output is `x_t=e(P_{t+1}(s),P_t(v))`. Its feedback premise is

`∃N, ∀t≥N, v(t)=R_L(P_{t+1}(s),x_t)`.

The required conclusion is `∃T, ∀t≥T, x_t∈L ∧ x_t∉P_{t+1}(s)`. Thus output precedes the current observed reply. An arbitrary finite initial segment of replies is permitted.

For `ECQ := EventuallyCorrectQueryGeneratable`, use a G4 set-query strategy. Its premise is

`∃N, ∀t≥N, v(t)=membershipAnswer L (q t (s restricted to Fin(t+1)) P_t(v))`.

Its output is `S t (s restricted to Fin(t+1)) P_{t+1}(v)`, **after** the current observed reply, and its required conclusion is `∃T, ∀t≥T, output_t ⊆ L \ A_{t+1}(s)`. The strategy's length-conditional infinitude certificate makes all these actual outputs infinite. In each case, feedback correctness is an implication premise about the supplied `s,v`; `N` is merely existential, may depend on all the fixed data, and need not be known to the learner. `T` may depend on the whole run; no relation or bound between `N` and `T` is asserted.

### G7. No-feedback element/set generation (`G`, `SG`)

`FiniteHistoryOperator Input Output = (t : Nat) → (Fin t → Input) → Output`. `Generator α` returns an element; `SetGenerator α` returns a set. `output g s t = g t (s restricted to Fin t)` and `setOutput` is the analogous set. Neither gets target membership or any feedback.

`G(H) := GeneratableInLimit H` is

`∃g, ∀L∈H, ∀s, Presents s L → ∃T, ∀t≥T, g t (s restricted to Fin t)∈L ∧ g t (s restricted to Fin t)∉A_t(s)`.

`SG(H) := SetGeneratableInLimit H` is

`∃S, (∀t xs, Infinite (S t xs)) ∧ (∀L∈H, ∀s, Presents s L → ∃T, ∀t≥T, S t (s restricted to Fin t)⊆L ∧ Disjoint (S t (s restricted to Fin t)) A_t(s))`.

The global infinitude certificate includes all histories, all times, and histories that cannot present a target. `SetCorrectAt` retains both subset and disjointness conjuncts. Existential witnesses are uniform over the target class and its presentations, whereas thresholds are pointwise. No relation to a named algorithm or effective program is specified by `G` or `SG` alone.

### G8. Freshening and locking

`noFeedbackOutputOnList g h = g h.length (List.get h)`. `ListWithin h L` means `∀x∈h, x∈L`. `NoFeedbackCorrectOnList g L h` requires output membership in `L` **and** exclusion from `h`. `IsSelfLockingHistory g L h` is

`ListWithin h L ∧ ∀tail, ListWithin tail L → NoFeedbackCorrectOnList g L (h ++ tail)`.

The universally allowed finite tails include the empty list, arbitrary lengths and repetitions. The condition says every finite target-valued extension gives a correct output; it does not state output constancy. `SelfLocksAlongEveryPresentation g H` is `∀L∈H, ∀s presenting L, ∃n, IsSelfLockingHistory g L (P_n(s))`. The lock length can depend on `g,L,s`.

`EverywhereFresh g` is `∀t xs, g t xs ∉ sequenceSample xs`. On an infinite universe, `freshenedGenerator g` returns `g t xs` if it is outside the seen finite set; otherwise it returns `freshFromInfinite Set.univ … seen`. The latter classically chooses a point of `Set.univ \ seen`. This fallback guarantees universe freshness, with no target argument. `freshFromInfinite C hC seen` in general chooses an element of `C \ seen`, using the supplied infinitude certificate; its existence proof is suppressed. These are named semantic procedures with explicit choice boundaries, not a computability assertion.

### G9. Named gap data and procedure

`NoFeedbackLockingGap.GapUniverse = Sum Nat Nat`; `target = Set.range Sum.inl`; `basePresentation n = Sum.inl n`. The `target_infinite` supporting theorem supplies an infinitude certificate.

`spikeHistory n` is `[inl 0, …, inl (n−1)] ++ [inl (n+1)]`, of length `n+1` (at `n=0` it is `[inl 1]`). `IsSpike xs` means `∃n, List.ofFn xs = spikeHistory n`; this is equality of entire ordered histories, not their underlying sets. The named generator takes `t,xs`. If `IsSpike xs`, it returns `inr 0`; otherwise it returns `freshFromInfinite target target_infinite (sequenceSample xs)`. Its branch test is classical proposition decision, and its non-spike selection uses classical choice. It reads the complete finite sample tuple and no oracle; it has no additional persistent state. This description reconstructs the definition, without certifying any theorem about it.

### Shared edge cases and dependencies

Every `∃strategy` precedes all target/run quantifiers, so witnesses are class-wide; separate predicates or conjuncts may use different witnesses. Stabilization is all-time beyond a finite threshold, never merely frequent or limsup. Ordinary `G`, `SG`, `EM`, `SM`, `EQ`, and `SQ` conclusions are required only on presentations; they impose no on-target success obligation when no presentation exists. `ECM`/`ECQ` instead quantify arbitrary sample streams under their stated feedback premise. None of the freshness conditions prohibits repeating an output before that point is sampled. Repeated sample values, duplicate targets/classes, and repeated cover sets are allowed. Main universal results with an all-infinite premise exclude finite/exhausted target languages; the predicate definitions themselves do not silently add that premise. Empty target classes make target-quantified obligations vacuous, while total-strategy existence and global set-infinitude certificates still remain. Countable inner covers retain infinitely many indexed entries even for an empty class; finite inner covers may have size zero.

## Definition provenance

Each entry names the exact reviewed recursive identifiers (supporting theorems were read only for their types). `declarations.jsonl:N` is an exact input anchor.

| Glossary | Exact identifier and input record |
|---|---|
| G0 | `GenLimit.FeedbackQueries.streamPrefix` — `declarations.jsonl:105`<br>`GenLimit.Generic.Language` — `declarations.jsonl:119`<br>`GenLimit.Generic.LanguageClass` — `declarations.jsonl:120`<br>`GenLimit.Generic.Presents` — `declarations.jsonl:121`<br>`GenLimit.Generic.Stream` — `declarations.jsonl:125`<br>`GenLimit.Generic.UUS` — `declarations.jsonl:126`<br>`GenLimit.Generic.sample` — `declarations.jsonl:128`<br>`GenLimit.Generic.sequenceSample` — `declarations.jsonl:129`<br>`GenLimit.textPrefix` — `declarations.jsonl:133` |
| G1 | `GenLimit.FeedbackQueries.CountableInnerCover` — `declarations.jsonl:2`<br>`GenLimit.FeedbackQueries.CountableInnerCover.mk` — `declarations.jsonl:3`<br>`GenLimit.FeedbackQueries.FiniteInnerCover` — `declarations.jsonl:13`<br>`GenLimit.FeedbackQueries.FiniteInnerCover.mk` — `declarations.jsonl:14`<br>`GenLimit.FeedbackQueries.HasCountableInnerCover` — `declarations.jsonl:15`<br>`GenLimit.FeedbackQueries.HasFiniteInnerCover` — `declarations.jsonl:16` |
| G2 | `GenLimit.FeedbackQueries.SourceElementMistakeCorrect` — `declarations.jsonl:40`<br>`GenLimit.FeedbackQueries.SourceElementMistakeGeneratable` — `declarations.jsonl:41`<br>`GenLimit.FeedbackQueries.SourceElementMistakeGenerates` — `declarations.jsonl:42`<br>`GenLimit.FeedbackQueries.SourceElementMistakeStrategy` — `declarations.jsonl:43`<br>`GenLimit.FeedbackQueries.SourceElementMistakeSucceedsOn` — `declarations.jsonl:44`<br>`GenLimit.FeedbackQueries.sourceElementFeedback` — `declarations.jsonl:84`<br>`GenLimit.FeedbackQueries.sourceElementFeedbackRun` — `declarations.jsonl:85`<br>`GenLimit.FeedbackQueries.sourceElementFeedbackStep` — `declarations.jsonl:86`<br>`GenLimit.FeedbackQueries.sourceElementOutput` — `declarations.jsonl:87`<br>`GenLimit.FeedbackQueries.sourceElementReply` — `declarations.jsonl:90`<br>`GenLimit.FeedbackQueries.sourceElementReply._proof_1` — `declarations.jsonl:91` |
| G3 | `GenLimit.FeedbackQueries.SourceSetMistakeCorrect` — `declarations.jsonl:53`<br>`GenLimit.FeedbackQueries.SourceSetMistakeGeneratable` — `declarations.jsonl:54`<br>`GenLimit.FeedbackQueries.SourceSetMistakeGenerates` — `declarations.jsonl:55`<br>`GenLimit.FeedbackQueries.SourceSetMistakeStrategy` — `declarations.jsonl:56`<br>`GenLimit.FeedbackQueries.SourceSetMistakeStrategy.mk` — `declarations.jsonl:57`<br>`GenLimit.FeedbackQueries.SourceSetMistakeStrategy.output` — `declarations.jsonl:58`<br>`GenLimit.FeedbackQueries.SourceSetMistakeSucceedsOn` — `declarations.jsonl:59`<br>`GenLimit.FeedbackQueries.sourceCanonicalRank` — `declarations.jsonl:83`<br>`GenLimit.FeedbackQueries.sourceFirst` — `declarations.jsonl:92`<br>`GenLimit.FeedbackQueries.sourceFirst._proof_1` — `declarations.jsonl:93`<br>`GenLimit.FeedbackQueries.sourceSetFeedback` — `declarations.jsonl:96`<br>`GenLimit.FeedbackQueries.sourceSetFeedbackRun` — `declarations.jsonl:97`<br>`GenLimit.FeedbackQueries.sourceSetFeedbackStep` — `declarations.jsonl:98`<br>`GenLimit.FeedbackQueries.sourceSetFirst` — `declarations.jsonl:99`<br>`GenLimit.FeedbackQueries.sourceSetFirst._proof_1` — `declarations.jsonl:100`<br>`GenLimit.FeedbackQueries.sourceSetOutput` — `declarations.jsonl:101`<br>`GenLimit.FeedbackQueries.sourceSetReply` — `declarations.jsonl:104`<br>`_private.GenLimit.Paper27_FeedbackQueriesAndMistakes.ElementMistake.0.GenLimit.FeedbackQueries.sourceRankWitness` — `declarations.jsonl:134` |
| G4 | `GenLimit.FeedbackQueries.SourceElementQueryGeneratable` — `declarations.jsonl:45`<br>`GenLimit.FeedbackQueries.SourceElementQueryGenerates` — `declarations.jsonl:46`<br>`GenLimit.FeedbackQueries.SourceElementQueryStrategy` — `declarations.jsonl:47`<br>`GenLimit.FeedbackQueries.SourceElementQueryStrategy.mk` — `declarations.jsonl:48`<br>`GenLimit.FeedbackQueries.SourceElementQueryStrategy.output` — `declarations.jsonl:49`<br>`GenLimit.FeedbackQueries.SourceElementQueryStrategy.query` — `declarations.jsonl:50`<br>`GenLimit.FeedbackQueries.SourceElementQuerySucceedsOn` — `declarations.jsonl:51`<br>`GenLimit.FeedbackQueries.SourceQueryPolicy` — `declarations.jsonl:52`<br>`GenLimit.FeedbackQueries.SourceSetQueryGeneratable` — `declarations.jsonl:60`<br>`GenLimit.FeedbackQueries.SourceSetQueryGenerates` — `declarations.jsonl:61`<br>`GenLimit.FeedbackQueries.SourceSetQueryStrategy` — `declarations.jsonl:62`<br>`GenLimit.FeedbackQueries.SourceSetQueryStrategy.mk` — `declarations.jsonl:63`<br>`GenLimit.FeedbackQueries.SourceSetQueryStrategy.output` — `declarations.jsonl:64`<br>`GenLimit.FeedbackQueries.SourceSetQueryStrategy.query` — `declarations.jsonl:65`<br>`GenLimit.FeedbackQueries.SourceSetQuerySucceedsOn` — `declarations.jsonl:66`<br>`GenLimit.FeedbackQueries.membershipAnswer` — `declarations.jsonl:81`<br>`GenLimit.FeedbackQueries.sourceElementQueryFeedback` — `declarations.jsonl:88`<br>`GenLimit.FeedbackQueries.sourceElementQueryOutput` — `declarations.jsonl:89`<br>`GenLimit.FeedbackQueries.sourceQueryFeedback` — `declarations.jsonl:94`<br>`GenLimit.FeedbackQueries.sourceQueryFeedback.match_1` — `declarations.jsonl:95`<br>`GenLimit.FeedbackQueries.sourceSetQueryFeedback` — `declarations.jsonl:102`<br>`GenLimit.FeedbackQueries.sourceSetQueryOutput` — `declarations.jsonl:103` |
| G5 | `GenLimit.FeedbackQueries.ZeroExampleElementMistakeGeneratable` — `declarations.jsonl:67`<br>`GenLimit.FeedbackQueries.ZeroExampleElementMistakeGenerates` — `declarations.jsonl:68`<br>`GenLimit.FeedbackQueries.ZeroExampleElementMistakeStrategy` — `declarations.jsonl:69`<br>`GenLimit.FeedbackQueries.ZeroExampleElementMistakeSucceedsOn` — `declarations.jsonl:70`<br>`GenLimit.FeedbackQueries.ZeroExampleSetQueryGeneratable` — `declarations.jsonl:71`<br>`GenLimit.FeedbackQueries.ZeroExampleSetQueryGenerates` — `declarations.jsonl:72`<br>`GenLimit.FeedbackQueries.ZeroExampleSetQueryStrategy` — `declarations.jsonl:73`<br>`GenLimit.FeedbackQueries.ZeroExampleSetQueryStrategy.mk` — `declarations.jsonl:74`<br>`GenLimit.FeedbackQueries.ZeroExampleSetQueryStrategy.output` — `declarations.jsonl:75`<br>`GenLimit.FeedbackQueries.ZeroExampleSetQueryStrategy.query` — `declarations.jsonl:76`<br>`GenLimit.FeedbackQueries.ZeroExampleSetQuerySucceedsOn` — `declarations.jsonl:77`<br>`GenLimit.FeedbackQueries.zeroExampleMistakeFeedback` — `declarations.jsonl:106`<br>`GenLimit.FeedbackQueries.zeroExampleMistakeFeedback.match_1` — `declarations.jsonl:107`<br>`GenLimit.FeedbackQueries.zeroExampleMistakeOutput` — `declarations.jsonl:108`<br>`GenLimit.FeedbackQueries.zeroExampleQueryFeedback` — `declarations.jsonl:109`<br>`GenLimit.FeedbackQueries.zeroExampleQueryOutput` — `declarations.jsonl:110` |
| G6 | `GenLimit.FeedbackQueries.EventuallyCorrectMistakeFeedback` — `declarations.jsonl:4`<br>`GenLimit.FeedbackQueries.EventuallyCorrectMistakeGeneratable` — `declarations.jsonl:5`<br>`GenLimit.FeedbackQueries.EventuallyCorrectMistakeGenerates` — `declarations.jsonl:6`<br>`GenLimit.FeedbackQueries.EventuallyCorrectMistakeSucceedsOn` — `declarations.jsonl:7`<br>`GenLimit.FeedbackQueries.EventuallyCorrectQueryFeedback` — `declarations.jsonl:8`<br>`GenLimit.FeedbackQueries.EventuallyCorrectQueryGeneratable` — `declarations.jsonl:9`<br>`GenLimit.FeedbackQueries.EventuallyCorrectQueryGenerates` — `declarations.jsonl:10`<br>`GenLimit.FeedbackQueries.EventuallyCorrectQuerySucceedsOn` — `declarations.jsonl:11`<br>`GenLimit.FeedbackQueries.eventuallyCorrectMistakeOutput` — `declarations.jsonl:78`<br>`GenLimit.FeedbackQueries.eventuallyCorrectQueryOutput` — `declarations.jsonl:79` |
| G7 | `GenLimit.Generic.CorrectAt` — `declarations.jsonl:111`<br>`GenLimit.Generic.FiniteHistoryOperator` — `declarations.jsonl:112`<br>`GenLimit.Generic.GeneratableInLimit` — `declarations.jsonl:113`<br>`GenLimit.Generic.GeneratesSetInLimitOn` — `declarations.jsonl:114`<br>`GenLimit.Generic.Generator` — `declarations.jsonl:115`<br>`GenLimit.Generic.IsInfiniteSetGenerator` — `declarations.jsonl:116`<br>`GenLimit.Generic.IsLimitGenerator` — `declarations.jsonl:117`<br>`GenLimit.Generic.IsSetLimitGenerator` — `declarations.jsonl:118`<br>`GenLimit.Generic.SetCorrectAt` — `declarations.jsonl:122`<br>`GenLimit.Generic.SetGeneratableInLimit` — `declarations.jsonl:123`<br>`GenLimit.Generic.SetGenerator` — `declarations.jsonl:124`<br>`GenLimit.Generic.output` — `declarations.jsonl:127`<br>`GenLimit.Generic.setOutput` — `declarations.jsonl:130` |
| G8 | `GenLimit.Angluin.ListWithin` — `declarations.jsonl:1`<br>`GenLimit.FeedbackQueries.EverywhereFresh` — `declarations.jsonl:12`<br>`GenLimit.FeedbackQueries.IsSelfLockingHistory` — `declarations.jsonl:17`<br>`GenLimit.FeedbackQueries.NoFeedbackCorrectOnList` — `declarations.jsonl:18`<br>`GenLimit.FeedbackQueries.SelfLocksAlongEveryPresentation` — `declarations.jsonl:39`<br>`GenLimit.FeedbackQueries.freshenedGenerator` — `declarations.jsonl:80`<br>`GenLimit.FeedbackQueries.noFeedbackOutputOnList` — `declarations.jsonl:82`<br>`GenLimit.Support.freshFromInfinite` — `declarations.jsonl:131`<br>`GenLimit.Support.freshFromInfinite._proof_1` — `declarations.jsonl:132` |
| G9 | `GenLimit.FeedbackQueries.NoFeedbackLockingGap.GapUniverse` — `declarations.jsonl:19`<br>`GenLimit.FeedbackQueries.NoFeedbackLockingGap.IsSpike` — `declarations.jsonl:20`<br>`GenLimit.FeedbackQueries.NoFeedbackLockingGap.basePresentation` — `declarations.jsonl:21`<br>`GenLimit.FeedbackQueries.NoFeedbackLockingGap.generator` — `declarations.jsonl:22`<br>`GenLimit.FeedbackQueries.NoFeedbackLockingGap.spikeHistory` — `declarations.jsonl:23`<br>`GenLimit.FeedbackQueries.NoFeedbackLockingGap.target` — `declarations.jsonl:24`<br>`GenLimit.FeedbackQueries.NoFeedbackLockingGap.target_infinite` — `declarations.jsonl:25` |

## Per-target dossiers

Each exact type below is copied verbatim from its supplied JSONL record. Glossary expansions preserve the associated constructors, certificates, feedback equations, and threshold dependencies.

### D01 — C01 — `GenLimit.FeedbackQueries.Results.theorem_3_1`

**Anchors:** `stage1/declarations.jsonl:29`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.theorem_3_1`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:56`.

**Reconstruction.** For every universe-polymorphic type α with Countable and Infinite instances and every class H, if every member of H is infinite, existence of one G2 element strategy succeeding eventually on every presentation of every member is equivalent to a G1 Nat-indexed inner cover by infinite sets.

**Quantifiers and dependencies.** ∀{α : Type u}[Countable α][Infinite α], ∀H, (∀L∈H, Infinite L) → (EM(H) ↔ HasCountableInnerCover H). Expand EM as ∃e ∀L∈H ∀s, Presents s L → ∃T ∀t≥T; expand the cover as ∃C, (∀i, Infinite(C i)) ∧ (∀L∈H, ∃i, C i⊆L). e/C precede L,s; T and the cover index may depend on L, and T on s.

**Information and algorithm scope.** G0–G2. The learner receives the sample list and delayed correctness bits according to G2. No membership-query channel or named strategy is part of this type.

**Edge cases and limits.** No nonempty-class hypothesis or bound on T; empty H still needs strategy/cover witnesses. Duplicate cover sets and repeated samples are permitted. This is an iff of existence properties, not equality of procedures or computability.

**Exact exported type:**

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] [Infinite.{u_1 + 1} α] (targets : GenLimit.Generic.LanguageClass.{u_1} α),
  (∀ (L : GenLimit.Generic.Language.{u_1} α),
      @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
          (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) targets L →
        @Set.Infinite.{u_1} α L) →
    Iff (@GenLimit.FeedbackQueries.SourceElementMistakeGeneratable.{u_1} α targets)
      (@GenLimit.FeedbackQueries.HasCountableInnerCover.{u_1} α targets)
```

### D02 — C02 — `GenLimit.FeedbackQueries.Results.theorem_3_2`

**Anchors:** `stage1/declarations.jsonl:33`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.theorem_3_2`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:66`.

**Reconstruction.** Under the same Countable, Infinite, and all-targets-infinite assumptions, existence of a G3 infinite-set strategy whose representative receives feedback and whose whole output is eventually fresh and contained in the target is equivalent to existence of a G2 element strategy.

**Quantifiers and dependencies.** ∀{α : Type u}[inst : Countable α][Infinite α], ∀H, (∀L∈H, Infinite L) → (SM_inst(H) ↔ EM(H)). Each side has its own ∃strategy ∀L∈H ∀presentation ∃T ∀t≥T. SM uses the displayed Countable instance in its chosen rank map and representative feedback.

**Information and algorithm scope.** G0, G2, G3. The set strategy always outputs an infinite set. Its feedback tests the least-ranked representative for target membership and sample freshness, while success tests containment of the entire set. Both schedules have delayed feedback.

**Edge cases and limits.** No assertion that a given element/set pair have equal outputs, equal thresholds, or identical feedback histories. Set output nonemptiness and infinitude are certificates of the strategy, including off-run histories; mere truth of a representative reply is not full-set correctness.

**Exact exported type:**

```lean
∀ {α : Type u_1} [inst : Countable.{u_1 + 1} α] [Infinite.{u_1 + 1} α]
  (targets : GenLimit.Generic.LanguageClass.{u_1} α),
  (∀ (L : GenLimit.Generic.Language.{u_1} α),
      @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
          (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) targets L →
        @Set.Infinite.{u_1} α L) →
    Iff (@GenLimit.FeedbackQueries.SourceSetMistakeGeneratable.{u_1} α inst targets)
      (@GenLimit.FeedbackQueries.SourceElementMistakeGeneratable.{u_1} α targets)
```

### D03 — C03 — `GenLimit.FeedbackQueries.Results.theorem_3_3`

**Anchors:** `stage1/declarations.jsonl:34`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.theorem_3_3`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:77`.

**Reconstruction.** There exists a class H of languages over Nat for which a G4 adaptive membership-query strategy with single-element output succeeds eventually on all target presentations, but no G4 strategy with infinite set outputs has that property.

**Quantifiers and dependencies.** ∃H : Set (Set Nat), EQ(H) ∧ ¬SQ(H). The first conjunct is ∃(q,o), ∀L∈H ∀s presenting L, ∃T ∀t≥T, output∈L\A_{t+1}. The negated conjunct denies existence of any (q,S,infinitude certificate) satisfying ∀L∈H ∀s presenting L ∃T ∀t≥T, output⊆L\A_{t+1}.

**Information and algorithm scope.** G0, G4. Each query sees samples through index t and earlier bits; output sees the current query answer as well. The theorem names no separating class or particular strategy; those existential witnesses are not recoverable from the withheld theorem proof.

**Edge cases and limits.** No UUS/all-targets-infinite, class-nonempty, cardinality, rate, or explicit class description is a conjunct. Do not import such properties from a theorem name or an unrelated census example. The negative statement concerns infinite set output with the stated certificate and timing.

**Exact exported type:**

```lean
∃ targets,
  And (@GenLimit.FeedbackQueries.SourceElementQueryGeneratable.{0} Nat targets)
    (Not (@GenLimit.FeedbackQueries.SourceSetQueryGeneratable.{0} Nat targets))
```

### D04 — C04 — `GenLimit.FeedbackQueries.Results.theorem_3_4`

**Anchors:** `stage1/declarations.jsonl:35`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.theorem_3_4`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:85`.

**Reconstruction.** For a Countable infinite universe and a class whose every language is infinite, existence of one G4 set-query strategy succeeding eventually on every target presentation is equivalent to a countable inner cover by infinite sets.

**Quantifiers and dependencies.** ∀{α : Type u}[Countable α][Infinite α], ∀H, (∀L∈H, Infinite L) → (SQ(H) ↔ HasCountableInnerCover H). SQ expands to ∃(q,S,certificate) ∀L∈H ∀presentation ∃T ∀t≥T. The cover is chosen before the target-dependent containment index.

**Information and algorithm scope.** G0, G1, G4. Each round has one membership query, then an infinite set output using the current answer; success is whole-set containment in L minus all t+1 observed samples. No named implementing strategy is in this endpoint.

**Edge cases and limits.** Both directions preserve semantic rather than effective existence. Set infinitude holds at actual rounds before T as well; correctness need only hold after T. Empty H and repeated cover sets are allowed.

**Exact exported type:**

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] [Infinite.{u_1 + 1} α] (targets : GenLimit.Generic.LanguageClass.{u_1} α),
  (∀ (L : GenLimit.Generic.Language.{u_1} α),
      @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
          (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) targets L →
        @Set.Infinite.{u_1} α L) →
    Iff (@GenLimit.FeedbackQueries.SourceSetQueryGeneratable.{u_1} α targets)
      (@GenLimit.FeedbackQueries.HasCountableInnerCover.{u_1} α targets)
```

### D05 — C05 — `GenLimit.FeedbackQueries.Results.corollary_3_6`

**Anchors:** `stage1/declarations.jsonl:26`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.corollary_3_6`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:95`.

**Reconstruction.** For every Nat-indexed family of classes on a Countable infinite universe, if every language in every indexed class is infinite, two implications hold together: if every indexed class admits EM, their union admits EM; and if every indexed class admits SQ, their union admits SQ.

**Quantifiers and dependencies.** ∀{α : Type u}[Countable α][Infinite α], ∀classes : Nat→Set(Set α), (∀i L, L∈classes i → Infinite L) → ((∀i, EM(classes i)) → EM(⋃i,classes i)) ∧ ((∀i, SQ(classes i)) → SQ(⋃i,classes i)). Premise strategies may depend on i; each conclusion chooses one strategy for the whole union before L and its presentation. ∃T remains run-dependent.

**Information and algorithm scope.** G0, G2, G4. The two branches retain their respective sample/reply schedules. The type does not provide an effective selector from i to a strategy, and the union learner is not given a hidden target index.

**Edge cases and limits.** Both implications are retained; neither is an iff here. Classes may repeat, overlap, or be empty, and a target may belong to several indices. There is no finite-union restriction, common time bound, or uniform program certificate on the family.

**Exact exported type:**

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] [Infinite.{u_1 + 1} α]
  (classes : Nat → GenLimit.Generic.LanguageClass.{u_1} α),
  (∀ (i : Nat) (L : GenLimit.Generic.Language.{u_1} α),
      @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
          (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) (classes i) L →
        @Set.Infinite.{u_1} α L) →
    And
      ((∀ (i : Nat), @GenLimit.FeedbackQueries.SourceElementMistakeGeneratable.{u_1} α (classes i)) →
        @GenLimit.FeedbackQueries.SourceElementMistakeGeneratable.{u_1} α (⋃ i, classes i))
      ((∀ (i : Nat), @GenLimit.FeedbackQueries.SourceSetQueryGeneratable.{u_1} α (classes i)) →
        @GenLimit.FeedbackQueries.SourceSetQueryGeneratable.{u_1} α (⋃ i, classes i))
```

### D06 — C06 — `GenLimit.FeedbackQueries.Results.corollary_3_7`

**Anchors:** `stage1/declarations.jsonl:27`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.corollary_3_7`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:108`.

**Reconstruction.** For a Countable infinite universe and all-infinite target class, the conjunction of two implications holds: EM implies a no-sample correctness-feedback element strategy ZEM; SQ implies a no-sample set-query strategy ZSQ.

**Quantifiers and dependencies.** ∀{α : Type u}[Countable α][Infinite α], ∀H, (∀L∈H, Infinite L) → (EM(H)→ZEM(H)) ∧ (SQ(H)→ZSQ(H)). Each no-sample conclusion independently has ∃strategy ∀L∈H ∃T ∀t≥T, with no presentation quantifier. ZEM requires x_t∈L; ZSQ requires S_t⊆L with global actual-round infinitude.

**Information and algorithm scope.** G0, G2, G4, G5. ZEM sees prior membership/correctness bits and emits before its current reply. ZSQ issues a membership query using t and prior bits, and its infinite set output sees the current answer. Neither receives sample elements.

**Edge cases and limits.** No freshness or pairwise novelty conclusion is present for either zero-example predicate. No converse or identity of premise and conclusion strategies is claimed. Both implication conjuncts are needed.

**Exact exported type:**

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] [Infinite.{u_1 + 1} α] (targets : GenLimit.Generic.LanguageClass.{u_1} α),
  (∀ (L : GenLimit.Generic.Language.{u_1} α),
      @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
          (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) targets L →
        @Set.Infinite.{u_1} α L) →
    And
      (@GenLimit.FeedbackQueries.SourceElementMistakeGeneratable.{u_1} α targets →
        @GenLimit.FeedbackQueries.ZeroExampleElementMistakeGeneratable.{u_1} α targets)
      (@GenLimit.FeedbackQueries.SourceSetQueryGeneratable.{u_1} α targets →
        @GenLimit.FeedbackQueries.ZeroExampleSetQueryGeneratable.{u_1} α targets)
```

### D07 — C07 — `GenLimit.FeedbackQueries.Results.corollary_3_8`

**Anchors:** `stage1/declarations.jsonl:28`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.corollary_3_8`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:121`.

**Reconstruction.** Under Countable, Infinite, and all-targets-infinite assumptions, two characterizations hold together: ECM is equivalent to a countable inner cover, and ECQ is equivalent to a countable inner cover. ECM and ECQ must tolerate arbitrary finite initial reply errors on arbitrary sample streams as specified in G6.

**Quantifiers and dependencies.** ∀{α : Type u}[Countable α][Infinite α], ∀H, (∀L∈H, Infinite L) → (ECM(H)↔HasCountableInnerCover H) ∧ (ECQ(H)↔HasCountableInnerCover H). In each eventual-feedback predicate: ∃strategy ∀L∈H ∀s v, (∃N ∀t≥N, feedback equation) → ∃T ∀t≥T, success equation. The two iff conjuncts may use different strategies/covers.

**Information and algorithm scope.** G0–G2, G4, G6. No Presents premise may be added. ECM output sees t+1 samples and only t observed bits; ECQ output sees t+1 samples and t+1 bits, including the current observed answer. ECM success is element membership and freshness; ECQ success is entire infinite-set containment outside all observed samples.

**Edge cases and limits.** N and T need not coincide, be known, or have a uniform rate. The feedback premise constrains only a tail of v. Repeated/off-target sample values are allowed. Neither equivalence identifies a computable algorithm or bounds the number of initial incorrect bits.

**Exact exported type:**

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] [Infinite.{u_1 + 1} α] (targets : GenLimit.Generic.LanguageClass.{u_1} α),
  (∀ (L : GenLimit.Generic.Language.{u_1} α),
      @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
          (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) targets L →
        @Set.Infinite.{u_1} α L) →
    And
      (Iff (@GenLimit.FeedbackQueries.EventuallyCorrectMistakeGeneratable.{u_1} α targets)
        (@GenLimit.FeedbackQueries.HasCountableInnerCover.{u_1} α targets))
      (Iff (@GenLimit.FeedbackQueries.EventuallyCorrectQueryGeneratable.{u_1} α targets)
        (@GenLimit.FeedbackQueries.HasCountableInnerCover.{u_1} α targets))
```

### D08 — C08 — `GenLimit.FeedbackQueries.Results.theorem_3_9_of_selfLocking`

**Anchors:** `stage1/declarations.jsonl:37`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.theorem_3_9_of_selfLocking`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:142`.

**Reconstruction.** For any infinite type α with DecidableEq and any target class H, assume that every no-feedback element generator that succeeds on H has its freshened generator self-lock along every presentation of every target in H. Under that explicit assumption, existence of a no-feedback infinite-set generator is equivalent to existence of a no-feedback element generator.

**Quantifiers and dependencies.** ∀{α : Type u}[inst : Infinite α][DecidableEq α], ∀H, (∀g, IsLimitGenerator g H → SelfLocksAlongEveryPresentation (freshenedGenerator_inst g) H) → (SG(H)↔G(H)). The premise expands to ∀g, successful(g) → ∀L∈H ∀s presenting L, ∃n, [ListWithin P_n(s) L ∧ ∀tail, ListWithin tail L → correct((freshened g),L,P_n(s)++tail)]. Existential SG/G witnesses and their per-run T follow that assumption.

**Information and algorithm scope.** G0, G7, G8. No feedback or membership queries occur. Freshening preserves an already sample-fresh output and otherwise classically chooses a universe-fresh point. The locking assumption refers to freshened g, not g itself, and quantifies all successful g.

**Edge cases and limits.** This endpoint is conditional; the self-locking premise must not be dropped. No Countable instance is required. Locking is correctness after every finite target-valued extension, not constancy of output; n may depend on g,L,s. No effective method for finding n or implementing choice is provided.

**Exact exported type:**

```lean
∀ {α : Type u_1} [inst : Infinite.{u_1 + 1} α] [DecidableEq.{u_1 + 1} α]
  (targets : GenLimit.Generic.LanguageClass.{u_1} α),
  (∀ (gen : GenLimit.Generic.Generator.{u_1} α),
      @GenLimit.Generic.IsLimitGenerator.{u_1} α gen targets →
        @GenLimit.FeedbackQueries.SelfLocksAlongEveryPresentation.{u_1} α
          (@GenLimit.FeedbackQueries.freshenedGenerator.{u_1} α inst gen) targets) →
    Iff (@GenLimit.Generic.SetGeneratableInLimit.{u_1} α targets) (@GenLimit.Generic.GeneratableInLimit.{u_1} α targets)
```

### D09 — C08 — `GenLimit.FeedbackQueries.Results.theorem_3_9_set_to_element`

**Anchors:** `stage1/declarations.jsonl:38`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.theorem_3_9_set_to_element`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:135`.

**Reconstruction.** For every type α and target class H, existence of a no-feedback generator producing infinite fresh target subsets eventually along all target presentations implies existence of a no-feedback element generator correct and sample-fresh eventually along all those presentations.

**Quantifiers and dependencies.** ∀{α : Type u}{H : Set(Set α)}, SG(H) → G(H). SG means ∃S, global all-history infinitude ∧ ∀L∈H ∀s presenting L ∃T ∀t≥T, subset and disjointness. G means ∃g ∀L∈H ∀s presenting L ∃T ∀t≥T, membership and freshness.

**Information and algorithm scope.** G0, G7. There are no typeclass premises at this endpoint, including no Nonempty, Infinite, Countable, or DecidableEq premise. Both learners see only the finite sample tuple. No named selection procedure is asserted by the type.

**Edge cases and limits.** The antecedent retains its all-history infinite-set certificate, even when target obligations are vacuous. This is only the displayed implication and does not independently establish the reverse direction or a computational transformation.

**Exact exported type:**

```lean
∀ {α : Type u_1} {targets : GenLimit.Generic.LanguageClass.{u_1} α},
  @GenLimit.Generic.SetGeneratableInLimit.{u_1} α targets → @GenLimit.Generic.GeneratableInLimit.{u_1} α targets
```

### D10 — C09 — `GenLimit.FeedbackQueries.Results.theorem_3_9_appendix_A_8_gap`

**Anchors:** `stage1/declarations.jsonl:36`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.theorem_3_9_appendix_A_8_gap`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:153`.

**Reconstruction.** For the G9 named universe, target, generator, and base stream, four statements hold together: (1) the generator is a limit element generator for the singleton class containing target; (2) it is fresh on every finite sample tuple, including off-target tuples; (3) basePresentation presents target; and (4) no prefix of basePresentation is a self-locking history for that generator and target.

**Quantifiers and dependencies.** IsLimitGenerator gap.generator {gap.target} ∧ (EverywhereFresh gap.generator ∧ (Presents gap.basePresentation gap.target ∧ ¬∃n, IsSelfLockingHistory gap.generator gap.target (P_n(gap.basePresentation)))). Conjunct (1) expands to ∀L∈{target} ∀s presenting L ∃T ∀t≥T, membership and sample freshness. Conjunct (2) is ∀t xs, freshness. Conjunct (4) denies ∃n [within(prefix,L) ∧ ∀tail within L, correct(prefix++tail)].

**Information and algorithm scope.** G0, G7–G9. This endpoint fixes all four named objects; the spike test compares the full ordered history to the G9 spike list. On a spike the output is inr 0; otherwise it is a classically selected unseen target element. No oracle or persistent state beyond the input tuple is used.

**Edge cases and limits.** All four conjuncts are retained. The no-lock assertion concerns prefixes of this particular base presentation, not every presentation or every finite history. The type does not say the generator fails to generate its target; the first conjunct explicitly asserts success. Proofs of the branch properties and convergence were not examined.

**Exact exported type:**

```lean
And
  (@GenLimit.Generic.IsLimitGenerator.{0} GenLimit.FeedbackQueries.NoFeedbackLockingGap.GapUniverse
    GenLimit.FeedbackQueries.NoFeedbackLockingGap.generator
    (@Singleton.singleton.{0, 0}
      (GenLimit.Generic.Language.{0} GenLimit.FeedbackQueries.NoFeedbackLockingGap.GapUniverse)
      (GenLimit.Generic.LanguageClass.{0} GenLimit.FeedbackQueries.NoFeedbackLockingGap.GapUniverse)
      (@Set.instSingletonSet.{0}
        (GenLimit.Generic.Language.{0} GenLimit.FeedbackQueries.NoFeedbackLockingGap.GapUniverse))
      GenLimit.FeedbackQueries.NoFeedbackLockingGap.target))
  (And
    (@GenLimit.FeedbackQueries.EverywhereFresh.{0} GenLimit.FeedbackQueries.NoFeedbackLockingGap.GapUniverse
      GenLimit.FeedbackQueries.NoFeedbackLockingGap.generator)
    (And
      (@GenLimit.Generic.Presents.{0} GenLimit.FeedbackQueries.NoFeedbackLockingGap.GapUniverse
        GenLimit.FeedbackQueries.NoFeedbackLockingGap.basePresentation
        GenLimit.FeedbackQueries.NoFeedbackLockingGap.target)
      (Not
        (∃ n,
          @GenLimit.FeedbackQueries.IsSelfLockingHistory.{0} GenLimit.FeedbackQueries.NoFeedbackLockingGap.GapUniverse
            GenLimit.FeedbackQueries.NoFeedbackLockingGap.generator GenLimit.FeedbackQueries.NoFeedbackLockingGap.target
            (@GenLimit.textPrefix.{0} GenLimit.FeedbackQueries.NoFeedbackLockingGap.GapUniverse
              GenLimit.FeedbackQueries.NoFeedbackLockingGap.basePresentation n)))))
```

### D11 — C10 — `GenLimit.FeedbackQueries.Results.theorem_3_10_finiteInnerCover_sufficient`

**Anchors:** `stage1/declarations.jsonl:31`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.theorem_3_10_finiteInnerCover_sufficient`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:167`.

**Reconstruction.** For every nonempty Countable type α and every target class H, existence of a finite inner cover of H by infinite sets suffices for no-feedback element generation in the limit on H.

**Quantifiers and dependencies.** ∀{α : Type u}[Nonempty α][Countable α]{H : Set(Set α)}, HasFiniteInnerCover H → G(H). The premise packages ∃m C, (∀i : Fin m, Infinite(C i)) ∧ (∀L∈H, ∃i, C i⊆L). The conclusion is ∃g ∀L∈H ∀s presenting L ∃T ∀t≥T, g-output∈L and outside A_t(s).

**Information and algorithm scope.** G0, G1, G7. No feedback channel, given presentation index, or named algorithm occurs. Nonempty and Countable are actual assumptions; Infinite α is not an outer assumption. Existential g may depend on the class and available cover existence, and T may depend on L,s.

**Edge cases and limits.** A size-zero finite cover is allowed for an empty target class; no nonempty-class condition is added. Every covered target contains an infinite member of the cover. There is no converse, effective compiler, named witness, or rate guarantee here.

**Exact exported type:**

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] [Countable.{u_1 + 1} α] {targets : GenLimit.Generic.LanguageClass.{u_1} α},
  @GenLimit.FeedbackQueries.HasFiniteInnerCover.{u_1} α targets → @GenLimit.Generic.GeneratableInLimit.{u_1} α targets
```

### D12 — C10 — `GenLimit.FeedbackQueries.Results.theorem_3_10_countableInnerCover_example`

**Anchors:** `stage1/declarations.jsonl:30`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.theorem_3_10_countableInnerCover_example`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:176`.

**Reconstruction.** There exists a target class H over Nat such that every language in H is infinite, H is no-feedback element-generatable in the limit, and H has a countable inner cover by infinite sets.

**Quantifiers and dependencies.** ∃H : Set(Set Nat), UUS(H) ∧ (G(H) ∧ HasCountableInnerCover H). Thus after H: ∀L∈H, Infinite L; independently ∃g ∀L∈H ∀s presenting L ∃T ∀t≥T, correct and fresh; independently ∃C : Nat→Set Nat, (∀i Infinite(C i)) ∧ (∀L∈H ∃i C i⊆L).

**Information and algorithm scope.** G0, G1, G7. The declaration existentially asserts the class, generator, and cover through the indicated predicates; it names none of them. Only the generator sample-history interface is known, with no feedback or effective enumeration guarantee.

**Edge cases and limits.** There is no class-nonempty condition, no assertion that finite inner covers fail, no properness or minimality of the countable cover, and no rate. The witness cannot be identified by inspecting a withheld theorem proof or importing a familiar example.

**Exact exported type:**

```lean
∃ targets,
  And (@GenLimit.Generic.UUS.{0} Nat targets)
    (And (@GenLimit.Generic.GeneratableInLimit.{0} Nat targets)
      (@GenLimit.FeedbackQueries.HasCountableInnerCover.{0} Nat targets))
```

### D13 — C10 — `GenLimit.FeedbackQueries.Results.theorem_3_10_noFiniteInnerCover_example`

**Anchors:** `stage1/declarations.jsonl:32`; `stage1/01-target-statements.md` heading `GenLimit.FeedbackQueries.Results.theorem_3_10_noFiniteInnerCover_example`; exported source `GenLimit.Paper27_FeedbackQueriesAndMistakes.Results.Overview:184`.

**Reconstruction.** There exists a target class H over Nat × Nat whose every language is infinite and which is no-feedback element-generatable in the limit, but which has no finite inner cover by infinite sets.

**Quantifiers and dependencies.** ∃H : Set(Set(Nat×Nat)), UUS(H) ∧ (G(H) ∧ ¬HasFiniteInnerCover H). After H, the successful generator is ∃g ∀L∈H ∀s presenting L ∃T ∀t≥T, membership and sample freshness. The last conjunct denies existence of any m, C : Fin m→Set(Nat×Nat), global component-infinitude certificates and target-dependent containment indices.

**Information and algorithm scope.** G0, G1, G7. The universe is exactly the product Nat×Nat, not the G9 sum. No named class, no named generator, and no query access are given; the existential witness is not extracted from a proof body.

**Edge cases and limits.** The negation ranges over every finite size, including zero, and every possible such cover, with no effective restriction. A countable-cover property is not an explicit conjunct of this endpoint. All three positive/negative components are retained; no computational or rate claim is added.

**Exact exported type:**

```lean
∃ targets,
  And (@GenLimit.Generic.UUS.{0} (Prod.{0, 0} Nat Nat) targets)
    (And (@GenLimit.Generic.GeneratableInLimit.{0} (Prod.{0, 0} Nat Nat) targets)
      (Not (@GenLimit.FeedbackQueries.HasFiniteInnerCover.{0} (Prod.{0, 0} Nat Nat) targets)))
```

## Exhaustive slot coverage

| Slot | Reviewed declarations / dossiers | Disposition |
|---|---|---|
| C01 | D01 — `GenLimit.FeedbackQueries.Results.theorem_3_1` | Supplied endpoint(s) reconstructed; none missing |
| C02 | D02 — `GenLimit.FeedbackQueries.Results.theorem_3_2` | Supplied endpoint(s) reconstructed; none missing |
| C03 | D03 — `GenLimit.FeedbackQueries.Results.theorem_3_3` | Supplied endpoint(s) reconstructed; none missing |
| C04 | D04 — `GenLimit.FeedbackQueries.Results.theorem_3_4` | Supplied endpoint(s) reconstructed; none missing |
| C05 | D05 — `GenLimit.FeedbackQueries.Results.corollary_3_6` | Supplied endpoint(s) reconstructed; none missing |
| C06 | D06 — `GenLimit.FeedbackQueries.Results.corollary_3_7` | Supplied endpoint(s) reconstructed; none missing |
| C07 | D07 — `GenLimit.FeedbackQueries.Results.corollary_3_8` | Supplied endpoint(s) reconstructed; none missing |
| C08 | D08 — `GenLimit.FeedbackQueries.Results.theorem_3_9_of_selfLocking`<br>D09 — `GenLimit.FeedbackQueries.Results.theorem_3_9_set_to_element` | Supplied endpoint(s) reconstructed; none missing |
| C09 | D10 — `GenLimit.FeedbackQueries.Results.theorem_3_9_appendix_A_8_gap` | Supplied endpoint(s) reconstructed; none missing |
| C10 | D11 — `GenLimit.FeedbackQueries.Results.theorem_3_10_finiteInnerCover_sufficient`<br>D12 — `GenLimit.FeedbackQueries.Results.theorem_3_10_countableInnerCover_example`<br>D13 — `GenLimit.FeedbackQueries.Results.theorem_3_10_noFiniteInnerCover_example` | Supplied endpoint(s) reconstructed; none missing |

All 13 declarations in `targets.txt` occur exactly once in the dossiers and in their assigned slot. All 10 slot objects report `no_registered_lean_endpoint=false` and have no absent linked names; this is an input status, not source-correspondence certification.

## Input hash census

Hashes were computed from the bytes actually read. Every entry listed in supplied `SHA256SUMS` matched.

| Stage 1 input | Bytes | SHA-256 |
|---|---:|---|
| `01-target-statements.md` | 9420 | `923ac66a82c11bc8c071c17ed2f1c8bb7677b314a8c8631bb58be8c23e4451af` |
| `02-definition-dependencies.md` | 71039 | `b55d87f1dd0a8854a0fdd797c92aa8d3d269831a670c895f4a5f20b9413a5c03` |
| `PROMPT.md` | 3356 | `c63aad9d119a37687071a9dd61f3139f0f318647c5237a6cfd05e4ecd3e38de3` |
| `SHA256SUMS` | 854 | `9b4b24f8d9872c5d78c74567d6e26f10d0e609c7075a2fb796de502996d1c9b2` |
| `START_HERE.md` | 217 | `52dbb6f80b47a22d94f222fd499cc75c3e793e710b44d74dd69922866c1c02d7` |
| `claim-slots.json` | 2364 | `f5bca2f378d881d5d43fdc29daec361362898d8811b3ef8db2556509b8d9819d` |
| `declarations.jsonl` | 128850 | `7efa75d45bf2e62927ba4eb3fb298861080d7060434eef50f4f9ae56e1dbcbdc` |
| `external-boundary.txt` | 1449 | `bb0564f2c532ca9637ea1e8742625b32f54117a8c70ce0d8c36469617136f566` |
| `native-declaration-census.jsonl` | 1862490 | `f9f268bbba2727bec1fc2fc21cde918915b5961a012c5f035d6dbe22f8d7cd27` |
| `snapshot.json` | 3008 | `e4a7ef13cab9cd77e221ebe5f900cde77cf024f427d92b7e2f5c22b1e794a364` |
| `targets.txt` | 724 | `ad5b1c1d885de2c572a1fb80d0d8e750bb3fe5cbc71de962369c1339677be548` |

## Remaining limitations and stop boundary

The source is withheld, so no claim-to-source match or complete-source coverage judgment is possible. The separating/existence examples D03, D12, and D13 name no witnesses in their exact types. The proof placeholders for choice/rank/existence certificates are treated only through supplied types and standard choice semantics; no proof steps, hidden witness constructions, executable extraction, or fresh compilation were certified. D08 expressly requires its self-locking premise; D10 reconstructs a particular named procedure and four claims about it without auditing proofs. The native census supplies code-only context rather than individual review of every helper. No unknown project-definition boundary was found in the recursive interface; the standard-library boundary is documented above.

Stage 1 ends after validating the three result files, coverage, and hashes. No later-stage evidence is accessed.
