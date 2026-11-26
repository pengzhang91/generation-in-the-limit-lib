# Paper 22: Language Generation with Replay

This map records the correspondence between Giorgio Racca, Michal Valko, and
Amartya Sanyal, *Language Generation with Replay: A Learning-Theoretic View
of Model Collapse*, and the Lean development under
`GenLimit.Paper22_LanguageGenerationWithReplay`.

## Source edition and scope

- Formalization source: arXiv:2603.11784v2, revised 5 July 2026 and accepted
  at ICML 2026.
- Audited PDF SHA-256:
  `336e313632cd6f63da3965bfcb18fe3c40be3d6556433f654054c6249e19f325`.
- Lean umbrella: `GenLimit.Paper22_LanguageGenerationWithReplay`.
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean).
- All six main theorems have unconditional proofs. Theorem 6.1 combines its
  countable-domain semantic result with a finite-query machine on `ℕ`.
  Theorem 7.1 uses an alternative recursive family construction.
- No uniform query-complexity, running-time, extracted-code, or separate
  Mathlib `Computable` theorem is claimed.

The source writes a countable class as an indexed sequence
`{h₁, h₂, ...}`.  Lean represents the same data by `ℕ → Set α`, allowing
repeated extensionally equal languages and preserving the index order used by
Algorithms 2 and 3.  Source one-based rounds and finite prefixes are shifted
uniformly to zero-based Lean indices.

## Claim-to-Lean correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definitions 3.1--3.2 | `IsReplaySequence`, `IsUniformReplayGeneratorAt`, and `UniformlyGeneratableWithReplay` in [`Uniform.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/Uniform.lean) | Full semantic interface | Replay inputs may be target elements or earlier outputs of the same generator.  Lean makes the source's positive sample-threshold convention explicit. |
| Algorithm 1 / Theorem 4.1 | `GenLimit.Replay.Results.theorem_4_1` in [`Results/Overview.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean), backed by [`Uniform.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/Uniform.lean) | Full | The burn-in generator repeats the first observation until the required number of distinct observations has appeared and then delegates to the ordinary uniform generator.  Both directions preserve the same positive threshold. |
| Definition 3.3 / Theorem 5.1 | `GenLimit.Replay.Results.theorem_5_1` in [`Results/Overview.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean), proved in [`NonuniformSeparation.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/NonuniformSeparation.lean) | Full | The source's positive and negative integer copies are represented by the support-isomorphic type `Sum ℕ ℕ`.  The adversarial stream is constructed recursively from the tested generator.  Ordinary non-uniform generation is discharged by the shared countable-class theorem from P02. |
| Definition 3.4 | `IsReplayEnumeration`, `IsLimitReplayGenerator`, and `GeneratableInLimitWithReplay` in [`LimitSeparation.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/LimitSeparation.lean) | Full semantic interface | Target coverage is required in addition to replay legality, while freshness excludes every observation in the finite input history. |
| Definition 6.2; Algorithm 2; Lemmas 6.3--6.5 | `ReplayFinitelyCriticalAt` and the finite-round results in [`WitnessProtection.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/WitnessProtection.lean), the persistent causal execution in [`CarriedCutoff.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/CarriedCutoff.lean), and the query realization in [`FiniteQueryTrace.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/FiniteQueryTrace.lean) | Full | The executable carried state follows the printed update `m ← max{m,xₜ}` and the proved-terminating repeat-until search.  Lean proves target criticality, witness protection, freshness, and eventual validity.  At every active round an explicit finite answer cache covers all consistency, finite-criticality, witness, and admissibility queries through the terminating cutoff; inactive rounds expose the finite consistency-query cache. |
| Theorem 6.1 | `GenLimit.Replay.Results.theorem_6_1` in [`Results/Overview.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean), supported by [`CarriedCutoff.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/CarriedCutoff.lean), [`FiniteQueryTrace.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/FiniteQueryTrace.lean), and [`CountableTransport.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/CountableTransport.lean) | Full | One encoding of the countable domain both transports the successful replay generator and specifies the oracle family used by the finite-query machine.  On the source's normalized `ℕ` universe, the literal machine is executable relative to that oracle and every round has a valid finite answered-query cache with a cutoff-dependent cardinality bound.  Lean also proves extensional locality: any second oracle agreeing on the cache produces the same transition.  An abstract `[Countable α]` supplies only a classical equivalence, so no stronger machine-computability transport is inferred from countability alone. |
| Lemmas 6.7--6.8 / Theorem 6.6 | `GenLimit.Replay.Results.theorem_6_6` in [`Results/Overview.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean), proved in [`LimitSeparation.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/LimitSeparation.lean) | Full | Lean uses the literal two-subclass construction on `Sum ℤ ℕ`; `Sum.inr n` represents marker `*^(n+1)`.  It proves uncountability, UUS, ordinary generation in the limit, and replay impossibility.  The ordinary generator is a simpler semantic implementation of the same marker-and-direction argument. |
| Theorem 7.1 | `GenLimit.Replay.Results.theorem_7_1` in [Overview](../GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean), proved in [ProperDiagonal.lean](../GenLimit/Paper22_LanguageGenerationWithReplay/ProperDiagonal.lean) | Full | A computable unbounded search finds finite legal transcripts ending in nonzero output. Universality guarantees that each search terminates on a temporary uniformly recursive family. The final family preserves all earlier queried answers and gives each nonzero row an odd word outside the even target. |
| Definition 3.5 / Theorem 7.3 | `GenLimit.Replay.Results.theorem_7_3` in [`Results/Overview.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean), proved in [`ProperSeparation.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/ProperSeparation.lean) | Full | The exact four languages over `ℤ` are formalized.  The adversarial stream is simultaneously a replay enumeration for two targets, while no family member is contained in their intersection. |

## Shared infrastructure and code reuse

- [`Core/GenericGeneration.lean`](../GenLimit/Core/GenericGeneration.lean) and
  [`Core/ClassGeneration.lean`](../GenLimit/Core/ClassGeneration.lean) provide
  the common language, stream, finite-sample, correctness, UUS, and ordinary
  generation interfaces.  P22 adds only replay-specific predicates.
- [`Support/AdaptiveMembershipDialogue.lean`](../GenLimit/Support/AdaptiveMembershipDialogue.lean)
  provides the deterministic query/action/round/trace/execution kernel shared
  with P04.  Theorem 7.1 retains only its indexed-family membership semantics,
  success predicate, certificate, and diagonal endgame locally.
- [`Paper02_LearningTheory/NonuniformCharacterization.lean`](../GenLimit/Paper02_LearningTheory/NonuniformCharacterization.lean)
  supplies the existing theorem that every countable UUS class is ordinarily
  non-uniformly generatable; Theorem 5.1 reuses it instead of reproving the
  positive half of the separation.
- [`Paper01_LanguageGeneration/FiniteQuery/Selection.lean`](../GenLimit/Paper01_LanguageGeneration/FiniteQuery/Selection.lean)
  supplies the shared indexed membership-oracle family and finite selection
  infrastructure used by Witness Protection.
- [`Paper10_UnionClosednessOfLanguageGeneration/Cardinality.lean`](../GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Cardinality.lean)
  supplies the powerset uncountability lemma used to prove that the Theorem
  6.6 witness is genuinely uncountable.
- The persistent-cutoff machine reuses the finite criticality, witness, and
  termination kernel from [`WitnessProtection.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/WitnessProtection.lean).
  The earlier restart-normalized machine remains as a proved executable variant;
  the source-facing Overview selects only the literal carried-cutoff version.
- [`FiniteQueryTrace.lean`](../GenLimit/Paper22_LanguageGenerationWithReplay/FiniteQueryTrace.lean)
  uses one exhaustive finite answer cache at the terminating cutoff.  Prefix
  nesting makes that cache sufficient for every earlier cutoff tested by the
  repeat-until loop.  The cache-agreement theorem proves that it determines
  the exact machine transition, without duplicating Algorithm 2's selector or
  correctness proof.
- Replay legality is endogenous to a generator's past outputs and is therefore
  not identified with the exogenous finite- or infinite-contamination APIs in
  Core.  No duplicate contamination definition is promoted.

## Proof correspondence

The paper uses Algorithm 3 and Lemma 7.2. The Lean construction instead
searches entire finite transcripts, with a fresh even word omitted by the
temporary target. It uses the generator's required termination only on exact
presentations of recursive infinite families. The earlier conditional
reduction and its diagnostic remain in `ProperMembershipLowerBound.lean`.

The source correspondence and the Lemma 7.2 diagnostic have been reviewed
   with AI assistance against the SHA-256-pinned arXiv v2 PDF. Shuangping Li
   completed a Level 1 human audit of the Overview statements of Theorems 4.1,
   5.1, 6.1, 6.6, and 7.3 on 12 November 2026 at checkpoint `6062058`; the
   [human-audit ledger](../AuditRecords/Human/README.md#22-language-generation-with-replay-theorems-41-51-61-66-and-73-level-1)
   records the scope. The merged Theorem 6.1 awaits Level 1 human review. Theorem 7.1 and construction/proof correspondence are
   outside that audit.

All currently exposed P22 proof declarations are kernel-checked, and the P22
development contains no `sorry`, `admit`, or paper-local axioms.
