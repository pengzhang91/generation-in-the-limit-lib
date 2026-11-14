# P29 Stage 1: paper-withheld code reconstruction

This report reconstructs the five supplied target types for all four opaque slots. Names and module paths serve as locators only. It does not identify source-paper claims.

## Input census and access boundary

Inputs were confined to the eleven files listed in the supplied stage1 directory: START_HERE.md, PROMPT.md, claim-slots.json, targets.txt, 01-target-statements.md, 02-definition-dependencies.md, declarations.jsonl, native-declaration-census.jsonl, snapshot.json, external-boundary.txt, and SHA256SUMS. All ten manifest entries matched freshly calculated SHA-256 values; actual hashes, including SHA256SUMS itself, are recorded in stage1-run.json.

The recursive export has 39 declarations: 27 definitions whose values were reconstructed and 12 theorem types (five targets, two existence interfaces, and five literal/typeclass proof-helper types). All theorem proof values are absent. Every GenLimit dependency of these declarations is present in the same recursive export. No missing custom semantic definition was found. The native census was parsed for schema/count (389 records); its first record was displayed, but no broader census helper was used as substantive evidence or individually certified.

The supplied snapshot's source_snapshot_sha256 is metadata only, not an independently checked source tree. No source Lean files, raw comments, theorem proof bodies, source paper, Git, registry, PaperMaps, old audits, human records, parent conversation, other stages, or owner material were consulted. General operating instructions and the coordinator's scope assignment were visible. Standard Lean/Mathlib meanings in external-boundary.txt are trusted without a recursive Mathlib audit. No build or proof certification was performed.

## Shared definitions and information access

All unqualified MistakeBounded identifiers below have prefix GenLimit.MistakeBounded. The glossary reconstructs every definition in the recursive export; each exact type and value remains available under its exact identifier in ../stage1/02-definition-dependencies.md and ../stage1/declarations.jsonl.

**GenLimit.Generic.Stream** — Stream α = Nat → α. Source: GenLimit.Core.GenericGeneration:31; declarations.jsonl record 1.

**GenLimit.Generic.sample** — sample observed t = image of observed on Finset.range t, namely the set of observations with indices s < t; the current observed t is excluded. Source: GenLimit.Core.GenericGeneration:63; declarations.jsonl record 2.

**GenLimit.MistakeBounded.DyadicUpperBudget** — DyadicUpperBudget B v b = B < (2 : Real)^(b+1) * v. The inequality is strict. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.PositiveTargetWeight:52; declarations.jsonl record 3.

**GenLimit.MistakeBounded.FiniteClassClosureDimensionAtMost** — For every I : Finset (Fin N), if finiteClassIntersection L I is finite then its Set.ncard is ≤ d. Only finite intersections are cardinality bounded; infinite intersections impose no inequality. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedAlgorithm:70; declarations.jsonl record 5.

**GenLimit.MistakeBounded.FirstActivated** — FirstActivated A k a = (k < A a) ∧ (∀ t : Nat, t<a → A t ≤ k). It records the first active round, not just some active round. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.CountableWeightedRun:461; declarations.jsonl record 6.

**GenLimit.MistakeBounded.LastMistakeBefore** — LastMistakeBefore trace last = ∀ t : Nat, last ≤ t → trace t = false. This is an inclusive no-error endpoint. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.Definitions:46; declarations.jsonl record 7.

**GenLimit.MistakeBounded.MistakeTrace** — Nat → Bool. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.Definitions:14; declarations.jsonl record 8.

**GenLimit.MistakeBounded.TotalMistakesAtMost** — TotalMistakesAtMost trace b = ∀ t : Nat, mistakeCount trace t ≤ b. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.Definitions:42; declarations.jsonl record 14.

**GenLimit.MistakeBounded.countableSemanticGenerated** — At t, chooses gₜ as infiniteFreshWeightedMaximizer over Finset.range(activeCount t), countableSemanticWeight activeCount initialWeight L observed t, L, and sample observed t. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.CountableWeightedRun:76; declarations.jsonl record 15.

**GenLimit.MistakeBounded.countableSemanticWeight** — State w₀(i)=initialWeight i if i<activeCount 0, else 0. For wₜ₊₁(i), if i<activeCount t, use U(wₜ,L,observed t,gₜ)(i). Otherwise, if i<activeCount(t+1) and ∀ s≤t, observed s∈L i, set initialWeight i; otherwise set 0. Here gₜ maximizes using range(activeCount t), wₜ, and sample observed t. The first branch applies even without monotonicity; under the theorem hypothesis it covers previously active indices. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.CountableWeightedRun:52; declarations.jsonl record 16.

**GenLimit.MistakeBounded.countableTargetTrace** — countableTargetTrace L g k t = decide (g t ∉ L k). Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.CountableWeightedRun:40; declarations.jsonl record 17.

**GenLimit.MistakeBounded.disjointPairLanguage** — For i : Fin 2, returns L₀ if i=0 and L₁ otherwise; hence its entries 0 and 1 are L₀ and L₁. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedAlgorithm:615; declarations.jsonl record 18.

**GenLimit.MistakeBounded.finiteClassIntersection** — finiteClassIntersection L I = {x | ∀ i : Fin N, i∈I → x∈L i}. The empty-index intersection is all of α. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedAlgorithm:62; declarations.jsonl record 22.

**GenLimit.MistakeBounded.finiteSemanticGenerated** — At t, chooses gₜ as infiniteFreshWeightedMaximizer over Finset.univ : Finset (Fin N), finiteSemanticWeight L observed t, L, and sample observed t. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedRun:42; declarations.jsonl record 23.

**GenLimit.MistakeBounded.finiteSemanticWeight** — State w₀(i)=1 for every i : Fin N. Recursion: wₜ₊₁ = U(wₜ,L,observed t,gₜ), where gₜ is the fresh weighted maximizer over all Fin N, weights wₜ, and sample observed t. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedRun:27; declarations.jsonl record 24.

**GenLimit.MistakeBounded.finiteSemanticWeight.match_1** — Natural-number case splitter: the zero branch receives Unit.unit; the successor branch receives its predecessor t. This supports the preceding state recursion. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedRun:None; declarations.jsonl record 25.

**GenLimit.MistakeBounded.finiteTargetTrace** — finiteTargetTrace L g k t = decide (g t ∉ L k), with k : Fin N. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedAlgorithm:44; declarations.jsonl record 26.

**GenLimit.MistakeBounded.freshWeightedMaximizer** — Classical.choose of an existential witness y satisfying y ∉ seen and ∀ x ∉ seen, weightedScore I w L x ≤ weightedScore I w L y. It takes a fresh-point existence proof; there is no specified effective tie-breaking rule. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.WeightedMaximizer:126; declarations.jsonl record 27.

**GenLimit.MistakeBounded.geometricPrefix** — G(base,i) = Σ j∈Finset.range i, if 0<j then base^j else 0; equivalently the sum of base^j for 1≤j<i. The j=0 contribution is zero. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.TradeoffDiagnostic:18; declarations.jsonl record 28.

**GenLimit.MistakeBounded.infiniteFreshWeightedMaximizer** — Calls freshWeightedMaximizer using the Infinite α instance to obtain a point outside the finite seen set. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.WeightedMaximizer:167; declarations.jsonl record 29.

**GenLimit.MistakeBounded.initialPrefixWeight** — initialPrefixWeight w n = Σ i < n, w i, including the empty prefix at n=0. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.CountableWeightedRun:320; declarations.jsonl record 30.

**GenLimit.MistakeBounded.mistakeCount** — mistakeCount trace t = cardinality of {s < t | trace s = true}. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.Definitions:17; declarations.jsonl record 31.

**GenLimit.MistakeBounded.paperDoublingActiveCount** — A(t)=2^(t+1) as a natural number; rounds start with two active indices, 0 and 1. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.PolynomialPrior:58; declarations.jsonl record 32.

**GenLimit.MistakeBounded.polynomialPrior** — p(i) = (1 : Real) / ((i+1 : Nat) cast to Real)^2. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.PolynomialPrior:47; declarations.jsonl record 33.

**GenLimit.MistakeBounded.polynomialPriorLogBudget** — β(k) = Nat.floor (Real.logb 2 (((Real.pi^2)/6) / polynomialPrior k)). This is the real logarithm followed by the natural-valued floor, not Nat.log or a ceiling. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.PolynomialPrior:338; declarations.jsonl record 34.

**GenLimit.MistakeBounded.updateWeight** — U(w,L,o,g)(i) = 0 if o ∉ L i; otherwise w i if g ∈ L i; otherwise 2*w i. Observation inconsistency takes precedence over generated-point membership. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.WeightedStep:34; declarations.jsonl record 37.

**GenLimit.MistakeBounded.weightedScore** — weightedScore I w L x = Σ i ∈ I, if x ∈ L i then w i else 0. Source: GenLimit.Paper29_MistakeBoundedLanguageGeneration.WeightedStep:27; declarations.jsonl record 39.

The two existence interfaces used by the maximizer have the following scope: exists_fresh_of_infinite takes Infinite α and an arbitrary finite seen set and returns some x outside seen. exists_fresh_weightedScore_maximizer takes any finite index set, real weight function, language sets, and finite seen set, plus the hypothesis that a fresh point exists; it returns a fresh y whose score is at least every fresh x's score. Their proof bodies were not supplied or assessed. The five auxiliary proof-helper types only establish the literal/typeclass facts used in the printed definitions; their proof values are absent.

The named generated streams select one point per round using Classical.choose. They are semantic functions with a fixed but computationally unspecified choice of maximizer, not a theorem merely asserting that some unspecified generator exists. Their interfaces use arbitrary language sets, classical membership tests, exact real-valued weights, and maximization over the whole unseen portion of α. No ordinary implementation, finite-time oracle algorithm, effective enumeration of α, randomness, probability law, or complexity result is encoded in the target types.

At round t the sample contains only observations with index <t. The state at t is recursively determined from those same earlier observations; observed t is consumed by the transition to t+1. Although the complete stream function is passed as a parameter, the displayed recursion uses no future observation. The target, dimension, activation time, weight bound, and mistake budget do not enter the generated-point selection. The score examines finitely many active indices but searches semantically over all fresh α points. Freshness is relative to past observations, not past generated outputs; it neither forbids repeated generated outputs nor forbids g(t)=observed(t).

The trace is a Boolean point-membership error for the one generated point: true exactly when g(t)∉L(target). Counts cover indices strictly less than the counting time. No support loss or distributional loss occurs.

## Target dossiers

For each dossier, the exact exported Lean type is reproduced verbatim below. The complete explicit instantiation detail, including universe variables and implicit binders, is thereby preserved; the accompanying skeleton unfolds only the definitions described above.

### C01 / target 1: GenLimit.MistakeBounded.Results.theorem_4_1

Exact identifier/source anchor: GenLimit.Paper29_MistakeBoundedLanguageGeneration.Results.Overview:42; exact export: ../stage1/declarations.jsonl, record 9. Full explicit type also appears in ../stage1/01-target-statements.md under this identifier.

~~~lean
∀ {α : Type u_1} [inst : Infinite.{u_1 + 1} α] (activeCount : Nat → Nat) (initialWeight : Nat → Real)
  (language : Nat → Set.{u_1} α) (observed : Nat → α),
  @Monotone.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder activeCount →
    (∀ (i : Nat),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (initialWeight i)) →
      @Function.Injective.{1, u_1 + 1} Nat α observed →
        ∀ {totalBound : Real},
          (∀ (n : Nat),
              @LE.le.{0} Real Real.instLE (GenLimit.MistakeBounded.initialPrefixWeight initialWeight n) totalBound) →
            ∀ (target activation budget : Nat),
              GenLimit.MistakeBounded.FirstActivated activeCount target activation →
                (∀ (t : Nat),
                    @Membership.mem.{u_1, u_1} α (Set.{u_1} α) (@Set.instMembership.{u_1} α) (language target)
                      (observed t)) →
                  @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (initialWeight target) →
                    GenLimit.MistakeBounded.DyadicUpperBudget totalBound (initialWeight target) budget →
                      GenLimit.MistakeBounded.TotalMistakesAtMost
                        (@GenLimit.MistakeBounded.countableTargetTrace.{u_1} α language
                          (@GenLimit.MistakeBounded.countableSemanticGenerated.{u_1} α inst activeCount initialWeight
                            language observed)
                          target)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) activation budget)
~~~

**Reconstruction and quantifiers.** Fix any type α with Infinite α; any A : Nat → Nat, w : Nat → Real, L : Nat → Set α, and o : Nat → α. In the exact hypothesis order assume Monotone A, every w(i)≥0, and Injective o. For any implicit real B bounding every finite prefix Σ(i<n)w(i), and then any natural k,a,b, assume FirstActivated A k a, ∀t,o(t)∈L(k), w(k)>0, and B<2^(b+1)w(k). For the named countable generated stream g(A,w,L,o), conclude ∀t, #{s<t | g(s)∉L(k)}≤a+b.

The activation hypothesis is the conjunction k<A(a) and ∀t<a,A(t)≤k. The prefix-weight premise includes n=0. B is a common real upper bound, not an assumed value of an infinite sum. The budget inequality is strict; equality at its upper endpoint is excluded. The target, activation, and budget are universal parameters under these hypotheses; the generator uses none of them. The same stream satisfies the implication for each eligible tuple, not a newly chosen stream depending on that tuple.

**Access and algorithm.** The countable state, admission-consistency test, score, update priority, and classical maximizer are exactly the shared definitions above. At time t the active indices are i<A(t); an inactive index admitted for t+1 is initialized only when all observations through and including t lie in its language. Target positivity and total-prefix boundedness are analysis assumptions, not extra runtime inputs.

**Edges and scope.** The conclusion bounds all finite-prefix mistake counts and includes pre-activation rounds; it states no last-error deadline. An activation a=0 is allowed and makes its earlier-round clause vacuous. A target never activated cannot meet FirstActivated. An injective infinite observation stream lying in the target implies the target is infinite; other languages may be empty or finite, and indexed languages need not be distinct. Zero target weight is expressly excluded. A=0 at some rounds and an empty active set are allowed by the definitions; Infinite α keeps the fresh domain nonempty. The bound is conditional, not an unconditional assertion for all A,w,L,o.


### C02 / target 2: GenLimit.MistakeBounded.Results.theorem_5_1

Exact identifier/source anchor: GenLimit.Paper29_MistakeBoundedLanguageGeneration.Results.Overview:71; exact export: ../stage1/declarations.jsonl, record 10. Full explicit type also appears in ../stage1/01-target-statements.md under this identifier.

~~~lean
∀ {α : Type u_1} [inst : Infinite.{u_1 + 1} α] {N : Nat} (language : Fin N → Set.{u_1} α) (observed : Nat → α)
  (target : Fin N),
  (∀ (t : Nat),
      @Membership.mem.{u_1, u_1} α (Set.{u_1} α) (@Set.instMembership.{u_1} α) (language target) (observed t)) →
    @Function.Injective.{1, u_1 + 1} Nat α observed →
      ∀ {d : Nat},
        @GenLimit.MistakeBounded.FiniteClassClosureDimensionAtMost.{u_1} α N language d →
          And
            (GenLimit.MistakeBounded.TotalMistakesAtMost
              (@GenLimit.MistakeBounded.finiteTargetTrace.{u_1} α N language
                (@GenLimit.MistakeBounded.finiteSemanticGenerated.{u_1} α inst N language observed) target)
              (@Min.min.{0} Nat instMinNat (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (GenLimit.MistakeBounded.LastMistakeBefore
              (@GenLimit.MistakeBounded.finiteTargetTrace.{u_1} α N language
                (@GenLimit.MistakeBounded.finiteSemanticGenerated.{u_1} α inst N language observed) target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
~~~

**Reconstruction and quantifiers.** Fix any α with Infinite α, any implicit N : Nat, L : Fin N → Set α, o : Nat → α, and k : Fin N. Assume first ∀t,o(t)∈L(k), then Injective o. For any implicit natural d satisfying D(L,d)=FiniteClassClosureDimensionAtMost L d, the named finite stream g(L,o) has BOTH (1) ∀t, #{s<t | g(s)∉L(k)}≤min(Nat.log 2 N,d+1), and (2) ∀t,d+1≤t → g(t)∈L(k).

D(L,d) quantifies over every Finset of Fin N indices; whenever that subfamily intersection is finite, its natural cardinality is at most d. It is not a bound on the size of infinite intersections, and there is no omitted nonempty-index premise. The count and eventual-correctness conclusions refer to the same stream and target. Nat.log 2 N is the natural-number base-two logarithm (floor on N≥1); the other term in the minimum is d+1. No minimum is applied to the timing threshold.

**Access and algorithm.** The finite stream uses every Fin N index in its score and begins each at weight 1. Its state changes with the shared update U using o(t) and g(t). Neither k nor d is an input to the generator; it needs no supplied closure-dimension value to define its semantic output. Classical maximization and membership access have the boundaries described above.

**Edges and scope.** No k : Fin 0 exists, so the theorem's N=0 case has no target instantiation. On every actual instantiation N≥1. The endpoint d+1 is inclusive for correctness: errors at t=d are still allowed, and no error is required there or earlier. The count excludes index t itself. For N=1 the first count bound is 0. The empty-index intersection is α and therefore infinite under the typeclass assumption, so its finite-cardinality antecedent is false. No finiteness/infinitude assumption is made about every individual family member, nor must indexed sets be different. The target's valid injective stream forces its infinitude. The result is conditional on D(L,d).


### C02 / target 3: GenLimit.MistakeBounded.Results.theorem_5_1_order_diagnostic

Exact identifier/source anchor: GenLimit.Paper29_MistakeBoundedLanguageGeneration.Results.Overview:94; exact export: ../stage1/declarations.jsonl, record 11. Full explicit type also appears in ../stage1/01-target-statements.md under this identifier.

~~~lean
∀ {α : Type u_1} {L₀ L₁ : Set.{u_1} α},
  @Set.Infinite.{u_1} α L₀ →
    @Set.Infinite.{u_1} α L₁ →
      @Disjoint.{u_1} (Set.{u_1} α)
          (@OmegaCompletePartialOrder.toPartialOrder.{u_1} (Set.{u_1} α)
            (@CompleteLattice.instOmegaCompletePartialOrder.{u_1} (Set.{u_1} α)
              (@CompleteBooleanAlgebra.toCompleteLattice.{u_1} (Set.{u_1} α)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{u_1} (Set.{u_1} α)
                  (@Set.instCompleteAtomicBooleanAlgebra.{u_1} α)))))
          (@HeytingAlgebra.toOrderBot.{u_1} (Set.{u_1} α)
            (@Order.Frame.toHeytingAlgebra.{u_1} (Set.{u_1} α)
              (@CompleteDistribLattice.toFrame.{u_1} (Set.{u_1} α)
                (@CompleteBooleanAlgebra.toCompleteDistribLattice.{u_1} (Set.{u_1} α)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{u_1} (Set.{u_1} α)
                    (@Set.instCompleteAtomicBooleanAlgebra.{u_1} α))))))
          L₀ L₁ →
        ∀ (x : α),
          And
            (@GenLimit.MistakeBounded.FiniteClassClosureDimensionAtMost.{u_1} α
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@GenLimit.MistakeBounded.disjointPairLanguage.{u_1} α L₀ L₁)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (Or
              (x ∉
                @GenLimit.MistakeBounded.disjointPairLanguage.{u_1} α L₀ L₁
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ⋯ (nat_lit 0))))
              (x ∉
                @GenLimit.MistakeBounded.disjointPairLanguage.{u_1} α L₀ L₁
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ⋯ (nat_lit 1)))))
~~~

**Reconstruction and quantifiers.** For any type α and implicit sets L₀,L₁ : Set α, assume in order that L₀ is infinite, L₁ is infinite, and they are disjoint. Then for every x : α conclude the conjunction D(disjointPairLanguage L₀ L₁,0) AND (x∉pair(0) OR x∉pair(1)). The pair entries are exactly L₀ and L₁. The disjunction does not require both nonmemberships and specifies no chosen side.

The dimension conjunct is the same universal finite-intersection predicate as above. For this pair, empty-index and singleton intersections are infinite and the full two-index intersection is empty. These consequences explain the predicate's content; they do not add hypotheses. x is universally quantified after the three set hypotheses; the dimension conjunct itself does not depend on x.

**Access and algorithm.** There is no learner, observed stream, output, target, time, or computation interface in this statement. It supplies a static dimension/nonmembership conjunction for every point. The name alone gives no claim about order of observing and generating.

**Edges and scope.** α has no explicit Infinite typeclass assumption here; infinitude is imposed on each of its two sets. Disjointness and their infinitude rule out identifying these two sets, but do not require that their union cover α. A point outside both satisfies both disjuncts; a point in one satisfies the other. The conclusion retains both its dimension predicate and its pointwise disjunction.


### C03 / target 4: GenLimit.MistakeBounded.Results.theorem_6_1

Exact identifier/source anchor: GenLimit.Paper29_MistakeBoundedLanguageGeneration.Results.Overview:106; exact export: ../stage1/declarations.jsonl, record 12. Full explicit type also appears in ../stage1/01-target-statements.md under this identifier.

~~~lean
∀ {α : Type u_1} [inst : Infinite.{u_1 + 1} α] (language : Nat → Set.{u_1} α) (observed : Nat → α),
  @Function.Injective.{1, u_1 + 1} Nat α observed →
    ∀ (target : Nat),
      (∀ (t : Nat),
          @Membership.mem.{u_1, u_1} α (Set.{u_1} α) (@Set.instMembership.{u_1} α) (language target) (observed t)) →
        GenLimit.MistakeBounded.TotalMistakesAtMost
          (@GenLimit.MistakeBounded.countableTargetTrace.{u_1} α language
            (@GenLimit.MistakeBounded.countableSemanticGenerated.{u_1} α inst
              GenLimit.MistakeBounded.paperDoublingActiveCount GenLimit.MistakeBounded.polynomialPrior language
              observed)
            target)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) target
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).pred
            (GenLimit.MistakeBounded.polynomialPriorLogBudget target))
~~~

**Reconstruction and quantifiers.** For every α with Infinite α, L : Nat → Set α, and o : Nat → α, assume Injective o. Then for every k : Nat, if ∀t,o(t)∈L(k), the named stream g = countableSemanticGenerated paperDoublingActiveCount polynomialPrior L o satisfies

    ∀t, #{s<t | g(s)∉L(k)} ≤ pred(Nat.clog 2 (k+1)) + β(k),

where A(t)=2^(t+1), p(i)=1/((i+1 : Nat) cast to Real)^2, and β(k)=Nat.floor(Real.logb 2 (((Real.pi^2)/6)/p(k))). The plus combines two natural numbers. Nat.clog is the base-two natural ceiling logarithm on the positive argument k+1, followed by saturated Nat.pred; β instead takes a real logarithm then the natural-valued floor. These two rounding operations must remain distinct.

No activation witness, free budget, prefix-weight-bound hypothesis, or asymptotic big-O statement occurs in this endpoint. The schedule and prior are fixed definition values; every valid target is assessed against this same generated stream. Dependence of the bound on k is explicit, not a single finite constant uniform over all target indices.

**Access and algorithm.** It is exactly the countable semantic state/update/maximizer with the displayed A and p. The first active set is {0,1}. Newly activated indices are initialized only if consistent with the entire observations received so far. Target k is used only to evaluate mistakes.

**Edges and scope.** k=0 and k=1 are allowed; the activation addend is 0 for both because the predecessor is saturated and the schedule begins with two active indices. The count concerns all times, with no specified last-mistake time or error-location bound. Other languages can be empty, finite, or repeated, while the valid target necessarily contains infinitely many distinct observed points. No enumeration-computability, membership decidability, effectiveness of real arithmetic, or deterministic finite implementation follows from the classical stream definition.


### C04 / target 5: GenLimit.MistakeBounded.Results.theorem_6_4_proof_diagnostic

Exact identifier/source anchor: GenLimit.Paper29_MistakeBoundedLanguageGeneration.Results.Overview:181; exact export: ../stage1/declarations.jsonl, record 13. Full explicit type also appears in ../stage1/01-target-statements.md under this identifier.

~~~lean
∀ (base i : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i →
    @Eq.{1} Nat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (GenLimit.MistakeBounded.geometricPrefix base i)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) base
            i))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (GenLimit.MistakeBounded.geometricPrefix base
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
~~~

**Reconstruction and quantifiers.** For every base,i : Nat, under the sole hypothesis 0<i,

    (G(base,i)+base^i)+1 = G(base,i+1)+1,

with G(base,i)=Σ(j<i), if 0<j then base^j else 0. Thus the equality adds the positive-i summand to the existing sum and retains the final +1 on both sides. There are no existential witnesses or hidden parameters.

**Access and algorithm.** This is a natural-number arithmetic equality only. It has no observation sequence, language, learner state, generated point, target loss, rate, oracle, or complexity component.

**Edges and scope.** There is no hypothesis base>1 or even base>0; bases 0 and 1 are included. The excluded case i=0 matters: G(base,0)=G(base,1)=0 and base^0=1, so the displayed equality would be 2=1. At i=1 the sum before adding base^i is empty of positive powers. No language-generation tradeoff can be reconstructed from this endpoint alone.


## Exhaustive coverage

| Slot | Exact endpoint(s) | Dossier | Status |
|---|---|---|---|
| C01 | GenLimit.MistakeBounded.Results.theorem_4_1 | Target 1 | Complete supplied type and recursively necessary values reconstructed |
| C02 | GenLimit.MistakeBounded.Results.theorem_5_1; GenLimit.MistakeBounded.Results.theorem_5_1_order_diagnostic | Targets 2 and 3 | Both endpoints, including both conjuncts of each, reconstructed |
| C03 | GenLimit.MistakeBounded.Results.theorem_6_1 | Target 4 | Exact schedule, prior, rounding, and bound reconstructed |
| C04 | GenLimit.MistakeBounded.Results.theorem_6_4_proof_diagnostic | Target 5 | Arithmetic equality and its sole positivity premise reconstructed |

All four slots have registered supplied Lean endpoints; no slot is absent or unlinked in claim-slots.json. This records supplied target coverage only, not source correspondence or proof correctness. There are five distinct reviewed targets, with none silently passed and none invented. The broader native census is supporting inventory only.
