# Paper 29: Mistake-Bounded Language Generation

This map records the correspondence between Jon Kleinberg, Charlotte Peale,
and Omer Reingold, *Mistake-Bounded Language Generation*, and the Lean
development under `GenLimit.Paper29_MistakeBoundedLanguageGeneration`.

## Source edition and scope

- Formalization source: arXiv:2605.10809v1, submitted 11 May 2026; the PDF is
  dated 12 May 2026.
- Source snapshot SHA-256:
  `c79335d8c0fec7e3960c141c034a34144e4928d118f27311c8d661f81ba61365`.
- Lean umbrella: `GenLimit.Paper29_MistakeBoundedLanguageGeneration`.
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Overview.lean).
- Finite tightness (5.3) and both noisy bounds (7.1–7.2) have independent proofs. Theorems 4.1 and 5.1 have checked qualifications. Theorem 6.1 and Modified-Greedy Lemmas 6.2–6.3 have constructive semantic bounds. Theorem 6.4 has a Lean refutation under its printed pointwise quantifiers.
- The development defines concrete semantic versions of Algorithms 1 and 3,
  but uses classical choice for maximizers and fresh points.  It does not
  claim an extracted implementation, finite computation, or running-time
  theorem.
- The source's generator-first move order and injective adversarial stream
  are represented explicitly.  Lean uses zero-based language and round
  indices; qualifications below state the resulting shifts.

## Claim-to-Lean correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definitions 1--2 | Shared `GenLimit.Generic` generation vocabulary in [`Core/ClassGeneration.lean`](../GenLimit/Core/ClassGeneration.lean) | Reused semantic interface | P29's concrete runs expose target membership, freshness, total mistakes, and last-mistake thresholds directly.  No second definitions of uniform and non-uniform generatability are introduced.  The paper reverses the standard move order, so its claimed time bounds require the shift described under Theorem 5.1. |
| Definition 3 | `MistakeTrace`, `mistakeCount`, `TotalMistakesAtMost`, `LastMistakeBefore`, `FinitelyManyMistakes` in [`Definitions.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Definitions.lean), and `worstCaseMistakes` in [`WorstCase.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/WorstCase.lean) | Full semantic interface | Prefix counts use rounds strictly before `t`.  `worstCaseMistakes : WithTop ℕ` is the exact supremum over admissible runs and is equivalent to uniform prefix bounds. |
| Algorithm 1; Theorem 4.1 | `Results.theorem_4_1` in [`Results/Overview.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Overview.lean), delegating to [`CountableWeightedRun.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/CountableWeightedRun.lean) | Full source repair at the semantic/classical boundary | The concrete run implements activation, inconsistent-language elimination, target-weight doubling, and fresh weighted maximization.  Lean adds the necessary assumption `0 < w₀(i)` and uses a division-free dyadic budget.  The printed statement permits zero target weight while displaying `log₂(W / w₀(i))`; [`PositiveTargetWeight.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/PositiveTargetWeight.lean) proves that no finite such budget exists at weight zero. |
| Definition 4 | `finiteClassIntersection`, `FiniteClassClosureDimensionAtMost` in [`FiniteWeightedAlgorithm.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/FiniteWeightedAlgorithm.lean) | Full upper-bound interface | The source maximum is represented by the exact universal upper-bound property needed downstream, avoiding an artificial value when no finite intersection exists. [`ClosureBridge.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/ClosureBridge.lean) identifies finite-family common cores and proves that P29's predicate implies Core's `ClosureDimensionAtMost`. |
| Theorem 5.1 | `Results.theorem_5_1` in [`Results/Overview.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Overview.lean) and its order diagnostic in [`Results/Supporting.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Supporting.lean), backed by [`FiniteWeightedRun.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/FiniteWeightedRun.lean) and [`FiniteWeightedAlgorithm.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/FiniteWeightedAlgorithm.lean) | Full source repair at the semantic/classical boundary | The concrete finite-class Algorithm 1 obtains at most `min(⌊log₂ N⌋, d+1)` total mistakes and no mistakes at or after zero-based round `d+1`.  The printed `d` bound is false under the paper's generator-first order: two disjoint infinite languages have closure dimension zero, but the first output must be wrong for one target.  This agrees with Remark 1's acknowledged possible shift by one. |
| Theorem 5.2, recalled from Kleinberg--Mullainathan and Li--Raman--Tewari | Shared closure-generation results under [`Paper02_LearningTheory`](../GenLimit/Paper02_LearningTheory.lean) | Reused; not duplicated | P29 uses the critical common-core choice condition.  The earlier theorem remains canonical in P02/Core; P29 proves that its concrete weighted choice satisfies the corresponding corrected generator-first condition. |
| Lemma 5.3 | `Results.lemma_5_3` in [`Results/Supporting.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Supporting.lean), backed by [FiniteLowerBound.lean](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/FiniteLowerBound.lean) | Full for every positive class size | A binary ray reverses the next bit predicted by each fresh output. The target enumerates its nonempty prefixes without repetition. Padding the depth-m family with infinite languages realizes exactly N targets. |
| Definition 5 | `modifiedGreedyFiniteIntersection`, `NonuniformComplexityAtMost` in [`ModifiedGreedy.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/ModifiedGreedy.lean) | Full upper-bound interface | As with Definition 4, Lean represents the finite maximum by the universal numerical upper bound actually used by the proof. |
| Theorem 6.1 | The integer bound `Results.theorem_6_1` in [`Results/Overview.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Overview.lean) and the paper’s real-valued bound `Results.theorem_6_1_displayed_bound` in [`Results/Supporting.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Supporting.lean), backed by [`PolynomialPrior.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/PolynomialPrior.lean) | Full source repair at the semantic/classical boundary | Lean instantiates Algorithm 1 with prior `1/(i+1)²` and an exponential active prefix.  It proves an exact natural-valued floor-log budget and the displayed real `O(log i)` inequality.  The source proof replaces `⌊log₂ i⌋` by `log₂ i` using equality; Lean uses the valid inequality. |
| Algorithm 3; Lemmas 6.2--6.3 | `Results.lemma_6_2`, `Results.lemma_6_3` in [`Results/Supporting.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Supporting.lean), backed by [`ModifiedGreedy.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/ModifiedGreedy.lean) | Full at the semantic/classical boundary | The concrete deterministic charging argument gives the printed `2(i-1)` mistake component and `max{i-1,m(Lᵢ)+1}` last-mistake component after translating one-based paper index `i` to zero-based Lean target `i-1`. |
| Theorem 6.4 | `Results.theorem_6_4_printed_false` in [TargetPriority.lean](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/TargetPriority.lean) via the Overview | Refuted as printed | For any proposed family, prioritize its second language through its Modified-Greedy cutoff and then resume the original algorithm. Its worst-case mistakes on language two are zero, while a single Big-O last-mistake bound still holds across all indices. The published lower bound requires at least one mistake on that language. |
| Lemma 7.1 | `Results.lemma_7_1` in [`Results/Supporting.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Supporting.lean), backed by [NoisyFinite.lean](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/NoisyFinite.lean) | Full | A causal fresh maximizer with noisy multiplicative weights gives the displayed comparator bound for every injective stream, horizon and learning rate in (0, 3/4]. |
| Lemma 7.2 | `Results.lemma_7_2` in [`Results/Supporting.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Supporting.lean), backed by [NoisyInfinite.lean](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/NoisyInfinite.lean) | Full, independent proof | The source drops the positive term log₂(π²/6)/γ in Appendix B.2.2. Our one-based activation schedule, separate first-language weight, and power-law tail prove the exact printed bound, including its zero additive budget at index one. A mistaken active target can hold at most half the current weight. |
| Theorems B.1 and B.3, recalled from Joshi et al. | — | External / not duplicated | These are prior-work reward-learning guarantees, not original P29 claims.  They would need their own pinned source and formalization before P29's downstream reductions could reuse them. |
| Lemma B.2 | `generation_of_demonstrations` in [Demonstrations.lean](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Demonstrations.lean) | Language-specific reduction | Prefix contexts reward precisely the fresh members. Demonstrator loss equals its membership errors, and freshening a learner output preserves the bound even if it originally repeats an observed item. |
| Theorems B.4--B.5; Lemma B.6 | — | Open | The binary and general-reward infinite-stream LfD results require a new real-valued online-reward API and potential argument.  The displayed ratios/logarithms also inherit the positive-target-weight guard needed by Theorem 4.1. |

## Shared infrastructure and code reuse

- [`Core/GenericGeneration.lean`](../GenLimit/Core/GenericGeneration.lean)
  now owns `sample_card_of_injective`.  The identical proofs formerly present
  in the finite weighted and Modified-Greedy developments were removed.
- [`ClosureBridge.lean`](../GenLimit/Paper29_MistakeBoundedLanguageGeneration/ClosureBridge.lean)
  proves that the common core of `Set.range language` is exactly P29's
  intersection of sample-consistent indices, and that P29's finite-family
  dimension bound implies shared Core `ClosureDimensionAtMost`.  The converse
  is intentionally absent because not every arbitrary subcollection must be
  realizable as a positive version space.
- Uniform and non-uniform generation vocabulary remains in
  [`Core/ClassGeneration.lean`](../GenLimit/Core/ClassGeneration.lean); P29
  does not introduce competing public definitions.
- P29's weighted membership-pattern maximizer, activation bookkeeping,
  mistake traces, and Modified-Greedy charging state are currently specific
  to this paper.  They remain local rather than being promoted prematurely to
  Core or Support.
- The source explicitly recalls the earlier uniform-generation guarantee in
  Theorem 5.2.  P29 reuses the shared closure vocabulary and proves only its
  weighted algorithm's critical-choice obligation.

## Appendix scope

The general reward-learning results in Appendix B.4–B.5 and the recalled Joshi et al. theorems are separate from the language-generation guarantees. The finite and countable noisy bounds above have independent proofs. All source-attributed human reviews refer to their recorded checkpoints.

## Human statement audit

Shuangping Li completed a Level 1 human audit of seven `Results/Overview.lean`
statements (Theorems 4.1, 5.1 in its corrected form, and 6.1, and Lemmas
6.2--6.3) and their defining interfaces on 13 November 2026 at checkpoint `c828be2`;
the [human-audit ledger](../AuditRecords/Human/README.md#29-mistake-bounded-language-generation-theorems-41-51-and-61-and-lemmas-62--63-level-1)
records the scope. `theorem_6_4_proof_diagnostic` and construction/proof
correspondence are outside that audit.
