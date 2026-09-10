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
- Overall status: **partial**. The checked development covers the paper's
  deterministic finite-prefix, deadline, density-transfer, feasible-profile,
  and Theorem 4 arithmetic endgames. It does not yet construct the paper's
  randomized process or prove its almost-sure results.
- The code is semantic and classical. It does not claim an executable or
  runtime-verified implementation.
- Lean uses zero-based prefixes: `Finset.range n` contains the first `n`
  indices. This is the usual reindexing of the paper's one-based notation.

The source comparison below was AI-assisted; no human statement- or
proof-correspondence audit is claimed.

## Source gaps and repair boundary

The pinned source has three distinct proof-level omissions.  They do not by
themselves show that a headline theorem is false, but the printed arguments
cannot be used literally without repair.

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
| Theorem 1 | **Partial core only** | [`Results/Overview.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Results/Overview.lean) exposes `theorems_1_2_pathwise_counting_core`, the finite-prefix inequality used by the impossibility proof. The existential hard family and the almost-sure diagonal argument are not formalized. |
| Theorem 2 | **Partial core only** | Reuses the same pathwise counting endpoint. The source's linear-deadline reduction and probabilistic universal quantification over randomized generators remain open. |
| Definition 2 (feasible profile) | **Partial, faithful natural-valued package** | [`FeasibleProfileDiagonal.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/FeasibleProfileDiagonal.lean), [`RateEnvelope.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/RateEnvelope.lean), and [`FlooredRateBudget.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/FlooredRateBudget.lean) construct a `NaturalFeasibleProfile` and prove the required diagonal/rate estimates. The literal real-valued source profile and discrete convexity of every composed prefix deadline are not packaged end to end. |
| Definition 3 (prefix-wise density) | **Full at the instance level** | `prefixWiseElements`, `prefixWiseDensity`, and `lowerPrefixWiseDensity` are in [`Definitions.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Definitions.lean). The paper's outer infima over targets, enumerations, and collections are not separately defined. |
| Lemma 2 | **Partial** | [`DensityReduction.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/DensityReduction.lean) proves the finite comparison and the vanishing-exception-ratio transfer; [`DeadlineDiagonal.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/DeadlineDiagonal.lean) constructs a simultaneous slowed deadline. The full source wrapper, including its feasible-profile and hallucination-rate obligations for a randomized generator, is open. |
| Lemma 3 (black-box reduction) | **Open** | The deterministic deadline/rate side conditions are available, but the randomized mixture, joint run semantics, expectations, concentration, and almost-sure lower-density conclusion are not formalized. |
| Theorem 3 | **Open as a headline theorem** | The deterministic infrastructure needed by the proof is checked, but the randomized SBG construction, Freedman/concentration argument, Borel--Cantelli step, and the final almost-sure `1/2` timely lower-density guarantee with vanishing hallucination are absent. |
| Definition 4 (upper timely density) | **Full at the instance level** | [`Definitions.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Definitions.lean) defines `upperTimelyDensity` using `limsup`. The paper's worst-case algorithm-level aggregation is not separately packaged. |
| Theorem 4 / Appendix Theorem 12 | **Full for the repaired GCG at the explicit indexed-family, instance-level worst-case interface** | [`GCGCommon.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/GCGCommon.lean) holds the infrastructure shared by both variants, while [`Diagnostics/PrintedStrictRiseGCG.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Diagnostics/PrintedStrictRiseGCG.lean) preserves the printed strict-rise skeleton and its documented defect outside the repaired proof path. [`TotalizedGCGMachine.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/TotalizedGCGMachine.lean), [`TotalizedGCGProgress.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/TotalizedGCGProgress.lean), and [`TotalizedGCGMain.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/TotalizedGCGMain.lean) implement the queue-all-guesses repair and prove stage termination, eventual consistency, cofinal checkpoints, and `upperTimelyDensity >= 1/2` on every exact presentation. [`AccurateCausality.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/AccurateCausality.lean) and [`OnlineTotalizedGCG.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/OnlineTotalizedGCG.lean) give the finite-history online realization. [`TurnTakingUpperBound.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/TurnTakingUpperBound.lean), [`AdaptivePresentation.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/AdaptivePresentation.lean), [`AdaptivePresentationExact.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/AdaptivePresentationExact.lean), and [`AdaptiveUpperBound.lean`](../GenLimit/Paper30_TimeSensitiveLanguageGeneration/AdaptiveUpperBound.lean) construct an adaptive exact presentation, bound catch-up exceptions by `Nat.log2 i`, and prove `<= 1/2`. The headline wrapper states the universal lower guarantee together with a concrete exact-presentation equality witness, with no certificate premise. A separately named `sInf` scalar for the logically equivalent outer aggregation is not required by downstream code. |

## Appendix result map

- Appendix C's Definition 5 and Lemma 4 restate/extend the measure-zero-chain
  obstruction. The structural chain and deterministic counting core are
  formalized; the randomized impossibility theorem is not.
- Appendix Theorems 5--6 are source-level consequences on the impossibility
  side and remain open for the same probabilistic reason as Theorems 1--2.
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
- Appendix Theorem 12 restates Theorem 4. The Overview therefore exposes an
  alias of the same unconditional repaired theorem instead of duplicating a
  proof.

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

## Remaining substantive roadmap

1. Define a history-dependent randomized generator/run interface backed by
   Mathlib probability spaces, with measurable hallucination and density
   events.
2. Formalize Lemma 3's speculative/black-box mixture and connect a reusable
   deterministic `1/2` generator (preferably P39) through an explicit bridge.
3. Add concentration, martingale/Freedman, summability, and Borel--Cantelli
   interfaces, then close Theorem 3 and the Appendix D extensions.
4. Formalize the measure-zero-chain adversarial randomized construction and
   close Lemma 1 and Theorems 1--2.
5. Optionally package the already-proved universal-lower-plus-equality-witness
   characterization as a separately named real-valued `sInf` aggregate if a
   later paper needs to calculate with that scalar. This is API packaging,
   not a remaining Theorem 4 proof obligation.

No declaration in the current P30 development uses `sorry` or `admit`.
