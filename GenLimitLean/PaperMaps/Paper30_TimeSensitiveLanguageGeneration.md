# Paper 30: Time-Sensitive Language Generation

This map records the current Lean coverage of Atul Ganju, Travis McVoy,
Shaddin Dughmi, and Shang-Hua Teng, *A Theory of Time-Sensitive Language
Generation: Sparse Hallucination Beats Mode Collapse*.

## Source and scope

- Formalization source: [arXiv:2605.11302v2](https://arxiv.org/abs/2605.11302v2),
  dated 2026-05-19.
- Pinned PDF SHA-256:
  `c66e7e8848a3931c0f03023769ef70a78785b2eaec15e0f1724e625f8392416a`.
- Umbrella import:
  [`GenLimit.Paper30_TimeSensitiveLanguageGeneration`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration.lean).
- Public result facade:
  [`Results/Overview.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Results/Overview.lean).
- Theorems 1 and 2 have almost-sure Lean proofs. Theorem 3’s uniform expected hallucination bound has a counterexample. Theorem 4 has a repaired generator achieving its sharp upper-density guarantee.
- The code is semantic and classical. It does not claim an executable or
  runtime-verified implementation.
- Lean uses zero-based prefixes: `Finset.range n` contains the first `n`
  indices. This is the usual reindexing of the paper's one-based notation.

The source comparison below was AI-assisted. Shuangping Li later completed a
Level 1 human statement audit of Theorem 4 / Appendix Theorem 12 (see the final
section); no proof-correspondence audit is claimed.

## Source gaps and repair boundary

The inverse-deadline and GCG issues below concern the published proofs. Theorem 3 has a separate obstruction to the uniform rate in its statement.

- The generalized inverse is written as
  `D^{-1}(t) = min {n : D(n) >= t}` for a bare natural-valued deadline.  The
  minimum need not exist for a bounded deadline.  Lean therefore requires an
  explicit `Deadline.IsUnbounded` witness.  Moreover, in Appendix C's proof
  of Lemma 4 (the restatement of Lemma 1), setting
  `i_j = D^{-1}(t_j)` gives `t_j <= D(i_j)`, whereas the displayed prefix
  comparison uses the opposite inclusion and upper-bounds the output prefix
  at `D(i_j)` by the one at `t_j`.  The proof also selects low-density
  `i_j` from an unrestricted `liminf`, although the inverse of a merely
  nondecreasing deadline need not hit every index.  `Definitions.lean`
  records both diagnostics.  A clean prospective repair is to prove the
  barrier first for strictly increasing unbounded deadlines and choose
  `t_j = D(i_j)`; recovering the exact stated generality and rate remains
  open.
- Appendix Theorem 12 states both eventual consistency and
  `mu_up = 1/2`, but its printed proof establishes only the three-case lower
  bound `limsup >= 1/2` and then ends with "we have proven the first claim."
  Lean separately proves the missing consistency argument and instantiates a
  Kleinberg--Wei turn-taking upper bound with a concrete adaptive exact
  presentation whose catch-up rounds are logarithmically sparse.  Thus the
  repaired theorem's equality is proved rather than read out of the source's
  lower-bound argument.
- Appendix E's strict-rise queue may retain an early invalid final candidate.
  `Accurate` is only eventually subset-valid, so Algorithm 2 can append a
  non-target language before the validity time and then have no later
  consecutive strict-superset transition.  The finite-queue proof silently
  treats the final queued language as target-contained.  Lean's existential
  repair in [`TotalizedGCGMachine.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/TotalizedGCGMachine.lean)
  queues every `Accurate` guess.  It preserves `OnTimeUnused` and the exact
  threshold transition, makes the queue cofinal, and remains explicitly
  separate from the printed strict-rise Algorithm-2 diagnostic in
  [`Diagnostics/PrintedStrictRiseGCG.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Diagnostics/PrintedStrictRiseGCG.lean).
  Both versions reuse the ordered-family, `OnTimeUnused`, used-set, and
  greedy-output infrastructure in
  [`GCGCommon.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/GCGCommon.lean);
  only the candidate-queue policy and stage advancement differ.

## Main claims

| Source result | Lean status | Lean files and exact boundary |
|---|---|---|
| Definition 1 (measure-zero chain) | **Full at the structural, instance-level interface** | [`Definitions.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Definitions.lean) defines `MeasureZeroChain`; [`MeasureZeroExamples.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/MeasureZeroExamples.lean) and [`MeasureZeroDensity.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/MeasureZeroDensity.lean) verify two concrete chains. |
| Lemma 1 (Hallucination Barrier) | **Partial; source proof requires repair** | [`DensityReduction.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/DensityReduction.lean) proves the deterministic pathwise counting inequality and its eventual-consistency burn-in specialization. The universal adversarial enumeration, a corrected generalized-inverse diagonal, expectation/Markov argument, summability, and Borel--Cantelli conclusion are open. |
| Theorem 1 | **Full** | A fixed countable family of infinite languages defeats every eventually consistent random-tape generator under every deadline. Dominated convergence handles tape-dependent burn-in, and a diagonal presentation for the natural-number target has almost-sure lower timely density zero. [Impossibility.lean](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Impossibility.lean) |
| Theorem 2 | **Full** | A linear deadline bounds the common output horizon by a fixed multiple of the rank. On each intermediate presentation the expected hallucination rate tends to zero. The same presentation construction and Fatou argument give almost-sure lower timely density zero. [TimelyExpectation.lean](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/TimelyExpectation.lean) |
| Definition 2 (feasible profile) | **Partial, faithful natural-valued package** | [`FeasibleProfileDiagonal.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/FeasibleProfileDiagonal.lean), [`RateEnvelope.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/RateEnvelope.lean), and [`FlooredRateBudget.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/FlooredRateBudget.lean) construct a `NaturalFeasibleProfile` and prove the required diagonal/rate estimates. The literal real-valued source profile and discrete convexity of every composed prefix deadline are not packaged end to end. |
| Definition 3 (prefix-wise density) | **Full at the instance level** | `prefixWiseElements`, `prefixWiseDensity`, and `lowerPrefixWiseDensity` are in [`Definitions.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Definitions.lean). The paper's outer infima over targets, enumerations, and collections are not separately defined. |
| Lemma 2 | **Partial** | [`DensityReduction.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/DensityReduction.lean) proves the finite comparison and the vanishing-exception-ratio transfer; [`DeadlineDiagonal.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/DeadlineDiagonal.lean) constructs a simultaneous slowed deadline. The full source wrapper, including its feasible-profile and hallucination-rate obligations for a randomized generator, is open. |
| Lemma 3 (black-box reduction) | **Open** | The deterministic deadline/rate side conditions are available, but the randomized mixture, expectations, concentration, and almost-sure lower-density conclusion are not formalized. |
| Theorem 3 | **Uniform rate refuted** | Fix countably many infinite target columns sharing precisely zero. At every positive horizon two legal exact presentations can repeat zero throughout the observed history. Fresh distinct outputs force at least one expected hallucination rate to be at least one half. This contradicts the source supremum over enumerations for every vanishing bound. [UniformHallucination.lean](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/UniformHallucination.lean) |
| Definition 4 (upper timely density) | **Full at the instance level** | [`Definitions.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Definitions.lean) defines `upperTimelyDensity` using `limsup`. The paper's worst-case algorithm-level aggregation is not separately packaged. |
| Theorem 4 / Appendix Theorem 12 | **Full for the repaired GCG at the explicit indexed-family, instance-level worst-case interface** | [`GCGCommon.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/GCGCommon.lean) holds the infrastructure shared by both variants, while [`Diagnostics/PrintedStrictRiseGCG.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Diagnostics/PrintedStrictRiseGCG.lean) preserves the printed strict-rise skeleton and its documented defect outside the repaired proof path. [`TotalizedGCGMachine.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/TotalizedGCGMachine.lean), [`TotalizedGCGProgress.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/TotalizedGCGProgress.lean), and [`TotalizedGCGMain.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/TotalizedGCGMain.lean) implement the queue-all-guesses repair and prove stage termination, eventual consistency, cofinal checkpoints, and `upperTimelyDensity >= 1/2` on every exact presentation. [`AccurateCausality.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/AccurateCausality.lean) and [`OnlineTotalizedGCG.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/OnlineTotalizedGCG.lean) give the finite-history online realization. [`TurnTakingUpperBound.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/TurnTakingUpperBound.lean), [`AdaptivePresentation.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/AdaptivePresentation.lean), [`AdaptivePresentationExact.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/AdaptivePresentationExact.lean), and [`AdaptiveUpperBound.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/AdaptiveUpperBound.lean) construct an adaptive exact presentation, bound catch-up exceptions by `Nat.log2 i`, and prove `<= 1/2`. The headline wrapper states the universal lower guarantee together with a concrete exact-presentation equality witness, with no certificate premise. A separately named `sInf` scalar for the logically equivalent outer aggregation is not required by downstream code. |

## Appendix result map

- Appendix C's Definition 5 and Lemma 4 restate/extend the measure-zero-chain
  obstruction. The structural chain and deterministic counting core are
  formalized. The independent random-tape diagonal proves Theorems 1 and 2. The quantitative inverse-deadline premise of Lemma 4 is a separate claim.
- Appendix Theorems 5--6 are source-level consequences on the impossibility
  side, proved by the same Lean endpoints as Theorems 1 and 2.
- Appendix D Lemmas 5--8 supply deterministic transfer, diagonal, and rate
  ingredients. Their corresponding cores are in `DensityReduction.lean`,
  `DeadlineDiagonal.lean`, `FeasibleProfileDiagonal.lean`, `RateEnvelope.lean`,
  and `FlooredRateBudget.lean`.
- Appendix Theorem 7 is Freedman's inequality, an external probability result;
  it is not re-proved or connected to a P30 randomized-run interface.
- Appendix Theorems 8 and 10 invoke prior dense-generation results. They are
  treated as dependencies, not duplicated P30 theorems.
- Appendix Lemmas 9--10 and Theorems 9 and 11 contain the randomized
  general-data-model extension. Only related deterministic deadline/profile
  infrastructure is present; the source-facing randomized endpoints are open.
- Appendix Theorem 12 restates Theorem 4. `Results.theorem_4` states both the
  universal guarantee and its sharpness witness in the Overview. The intermediate
  results and earlier declaration names are in
  [Results/Supporting.lean](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Results/Supporting.lean).

## Reuse and cross-paper dependencies

- [`Core/OrderedDensity.lean`](../GenLimit/Core/OrderedDensity.lean) supplies
  the shared ordered prefix density and `liminf`/`limsup` layer.
- [`Support/TurnTaking/Announcements.lean`](../GenLimit/Support/TurnTaking/Announcements.lean)
  supplies the paper-independent first-announcement partition and `FreshPlay`
  interface used by the stable greedy run.  The finite pairing core used by
  the adaptive upper bound is in
  [`Support/TurnTaking/Pairing.lean`](../GenLimit/Support/TurnTaking/Pairing.lean);
  P30 retains a compatibility alias and its timely-density specialization.
- [`Support/Asymptotics/NatLog.lean`](../GenLimit/Support/Asymptotics/NatLog.lean)
  supplies the shared `Nat.log2 i / i -> 0` endpoint used by the sparse
  catch-up construction.
- P07's `IndexValidInLimit` / `Accurate` results give eventual subset validity
  and arbitrarily late exact target guesses for an explicitly indexed family.
  [`AccurateBridge.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/AccurateBridge.lean)
  imports this theorem directly as the `Accurate` oracle contract used by
  Appendix E. The queue-totalized state machine consumes it in
  `TotalizedGCGMain.lean`.
- P09 contains per-round discrete-distribution definitions. P30 needs a
  stronger joint, history-dependent randomized-run semantics with a
  filtration, so P09 is groundwork rather than an end-to-end implementation.
- P15/P17 provide the paper's original partial-enumeration and contamination
  context. Recalled prior theorems should be reused instead of copied once the
  randomized wrapper exists.
- P39 proves a deterministic ordinary lower-density `1/2` result.  Its
  former paper-local first-announcement and `Nat.log2 i / i -> 0` utilities
  have been promoted to the shared Support modules above.  Ordinary
  ambient-prefix lower density does **not** by itself imply identity-deadline
  timely upper density, so P30 still proves its own timely-density
  specialization of the shared finite pairing argument.

## Probabilistic scope

The generator reads a finite positive history on a measurable random tape. The hard presentation for Theorems 1 and 2 is fixed before the tape. For Theorem 3 the source instead takes a supremum over presentations at each time. Its threshold can vary with the presentation in the appendix proof. The printed bound requires one threshold for every presentation. For example, the deadline D(n) = n⁴ and the rate H(t) = 1/√(t+1) meet the source feasibility conditions. Its inverse is of order t^(1/4), so H(t) exceeds the inverse-to-time ratio by a diverging factor. The counterexample applies to this profile as well. A pointwise version, the quantitative Hallucination Barrier, and the separate appendix extensions have their own proof obligations.

## Human statement audit

Shuangping Li completed a Level 1 human audit of the four totalized-GCG
`Results/Overview.lean` statements for Theorem 4 / Appendix Theorem 12 and
their defining interfaces on 13 November 2026 at checkpoint `c828be2`; the
[human-audit ledger](../AuditRecords/Human/README.md#30-time-sensitive-language-generation-theorem-4-and-appendix-theorem-12-level-1)
records the scope. Lean's `id` deadline is one step stricter than the source's
identity deadline. The other six Overview declarations, Theorems 1--3, and
construction/proof correspondence are outside that audit.
