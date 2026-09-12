# Paper 18: Safe Language Generation in the Limit

This map records the correspondence between Anastasopoulos, Ateniese, and
Kornaropoulos, *Safe Language Generation in the Limit*, and the Lean
development under `GenLimit.Paper18_SafeLanguageGeneration`.

## Source edition and scope

- Formalization source: arXiv:2601.08648v2 (26 June 2026).
- Audited PDF SHA-256:
  `c978aaa43d875597f3a349660efaf87b1307a717007138d4edd2d8847f96bcb0`.
- Lean umbrella: `GenLimit.Paper18_SafeLanguageGeneration`.
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean).
- Status: **all five numbered theorems have kernel-checked semantic content,
  but four require explicit source qualifications**. Theorems 3.1, 5.1, and
  6.2 use documented repairs; Theorem 6.1 is proved for the conventional
  representation by pairs of partial-recursive program codes, with validity
  restricted to total Boolean deciders for infinite languages; Theorem 6.3 is
  fully represented. The printed Corollary 6.1 reduction is defective and the
  corollary remains open as stated.
- The development is deterministic semantic mathematics plus a concrete
  Mathlib partial-recursive reduction for Theorem 6.1. It does not claim a
  general extracted implementation, membership-oracle program, or runtime
  bound.

The source represents countable collections as indexed lists. Lean uses the
corresponding explicit interface `ℕ → Set α`, preserving index order and
repetitions. The source's countable-universe assumption appears as
`[Countable α]` where a canonical presentation must be chosen.

## Claim-to-Lean correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definition 1 (safe identification) | `SafeIdentifier`, `DifferenceRepresented`, and `SafelyIdentifiesFrom` in [`SafeIdentification.lean`](../GenLimit/Paper18_SafeLanguageGeneration/SafeIdentification.lean) | Source repair | The instruction to insert `K \ H` at a "random location" supplies no probability distribution, quantifier over positions, or information model. Lean fixes the candidate family before quantifying over the deterministic identifier and requires the difference to be extensionally represented. |
| Theorem 3.1 | `GenLimit.SafeGeneration.Results.theorem_3_1` in [`Results/Overview.lean`](../GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean) | Source repair | One explicit pair of indexed families of infinite languages defeats every deterministic semantic identifier. All relevant differences already occur in the fixed candidate family. The append-only diagonal stream has exactly the claimed target and harmful tagged ranges. |
| Definition 2 (safe generation) | `SafeGenerator`, `SafeCorrectAt`, `BottomCorrectAt`, `SafelyGenerates`, and `SafelyGeneratesFamilies` in [`Definitions.lean`](../GenLimit/Paper18_SafeLanguageGeneration/Definitions.lean) | Full semantic interface | A labeled presentation enumerates target and harmful occurrences separately, so an element in their intersection may occur with both tags. Every finite difference, including the empty case, requires eventual `none`, exactly as printed. |
| Algorithm 1 / Theorem 5.1 | `GenLimit.SafeGeneration.Results.theorem_5_1` in [`Results/Overview.lean`](../GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean), supported by [`IdentificationReduction.lean`](../GenLimit/Paper18_SafeLanguageGeneration/IdentificationReduction.lean) | Source repair; full semantic reduction | The pseudocode rebuilds finite inputs at each outer time, whereas a limit guarantee applies only along prefixes of one fixed infinite run. Lean gives every candidate one fixed padded labeled run and proves that each replayed call is its exact prefix. Duplicate family indices converge to the first extensionally equivalent language. The theorem is classical/semantic rather than a membership-oracle implementation. |
| Theorem 6.1 | `GenLimit.SafeGeneration.Results.theorem_6_1`, `theorem_6_1_restricted`, and `theorem_6_1_of_hard_embedding` in [`Results/Overview.lean`](../GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean), with the concrete representation in [`MachineEncoding.lean`](../GenLimit/Paper18_SafeLanguageGeneration/MachineEncoding.lean) and reduction core in [`DiffEmpty.lean`](../GenLimit/Paper18_SafeLanguageGeneration/DiffEmpty.lean) | Full under an explicit conventional encoding | The source does not choose a finite encoding for arbitrary decidable-language pairs. Lean makes that boundary explicit: an input is a pair of Mathlib partial-recursive codes, and validity promises that both halt everywhere with Boolean outputs and accept infinite languages. `computablePred_has_totalBooleanDeciderCode` proves that every computable predicate is represented. Using `Code.curry`/S-m-n, the hard instances are computably compiled into valid pairs, so no computable predicate is correct on the entire promise domain. The restricted hard subclass and generic representation-transport theorem remain exposed separately. |
| Corollary 6.1 | `GenLimit.SafeGeneration.Results.corollary_6_1_printed_reduction_collapses` in [`Results/Overview.lean`](../GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean), with the exact printed reduction in [`CorollarySixOneDiagnostic.lean`](../GenLimit/Paper18_SafeLanguageGeneration/CorollarySixOneDiagnostic.lean) | Open; source diagnostic | The printed halting reduction gives an empty difference for nonhalting and a singleton for halting. Definition 2 requires eventual bottom in both finite cases, so the safe generator's promised asymptotic behavior cannot distinguish them. Eventual convergence also gives no computable stabilization time. Lean proves this collapse and does not claim the corollary. |
| Theorem 6.2 | `GenLimit.SafeGeneration.Results.theorem_6_2` in [`Results/Overview.lean`](../GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean), proved in [`Impossibility.lean`](../GenLimit/Paper18_SafeLanguageGeneration/Impossibility.lean) | Source repair | The printed proof assumes, but does not construct, families satisfying Property `P*`; it also describes the absence of a future successful output as observable. Lean instead combines repaired Theorem 5.1 with an explicit non-identifiable family. The oracle-facing wrapper quantifies over every correct extensional set-difference oracle and every oracle algorithm. |
| Definition 3 (`SG∞`) | `AllCrossDifferencesInfinite` and `SafelyGeneratesInfiniteDifferences` in [`Definitions.lean`](../GenLimit/Paper18_SafeLanguageGeneration/Definitions.lean) | Full semantic interface | Every target--harmful cross-difference is explicitly assumed infinite. |
| Theorem 6.3 | `GenLimit.SafeGeneration.Results.theorem_6_3` in [`Results/Overview.lean`](../GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean), proved in [`InfiniteDifference.lean`](../GenLimit/Paper18_SafeLanguageGeneration/InfiniteDifference.lean) | Full | The finite-history construction chooses a highest critical target candidate and a least consistent harmful candidate, proves their eventual containment directions, and emits a fresh point from their infinite difference. |
| Section 7 finite-intersection observation | `theorem_6_3_of_finite_cross_intersections` in [`InfiniteDifference.lean`](../GenLimit/Paper18_SafeLanguageGeneration/InfiniteDifference.lean) | Full semantic corollary | Infinite targets with finite target--harmful intersections satisfy Theorem 6.3's infinite cross-difference hypothesis. |

## Reuse and dependency audit

- [`Core/GenericGeneration.lean`](../GenLimit/Core/GenericGeneration.lean)
  supplies languages, indexed families, presentations, finite samples, and
  the countable-universe interface.
- [`Core/Identification.lean`](../GenLimit/Core/Identification.lean) supplies
  the shared ordered-list learner and the finite-history adapter used by the
  Theorem 5.1 reduction.
- [`Support/FiniteCandidateRace.lean`](../GenLimit/Support/FiniteCandidateRace.lean)
  supplies the repetition-free enumeration of an infinite countable set.
  P18 now uses this reusable support API directly rather than depending on a
  P06-local compatibility wrapper.
- [`Support/LeastCandidate.lean`](../GenLimit/Support/LeastCandidate.lean)
  supplies both the totalized least-candidate selector used by Theorems 5.1
  and 6.3 and the generic least equivalent family index.  The latter is the
  same duplicate-name convention used by P00 identification by enumeration;
  the P00 `leastEqualName` and P18 `firstEquivalentIndex` names are retained
  as compatibility aliases.
- [`Support/Fresh.lean`](../GenLimit/Support/Fresh.lean) supplies the generic
  fresh choice from an infinite set used by Theorem 6.3.
- P18 reuses the semantic positive-data identification interface from
  [`Paper00A_PositiveDataInference`](../GenLimit/Paper00A_PositiveDataInference.lean).
- The repaired Theorem 6.2 reuses P28's explicit punctured family and its
  non-identifiability theorem from
  [`Paper28_ContrastiveGeneration/Hierarchy.lean`](../GenLimit/Paper28_ContrastiveGeneration/Hierarchy.lean).
  This exposes a mathematical relationship not stated in the source: the
  repaired Theorem 5.1 turns any explicit positive-data non-identifiability
  witness into a safe-generation impossibility witness after vertical padding.
- P18's tagged critical-candidate construction is analogous to the KM
  critical-language method, but its two-label containment argument is
  paper-specific; no duplicate foundational definition was moved into Core.

## Remaining gaps

1. The literal probabilistic meaning of Definition 1's "random location" is
   undefined in the source and therefore is not formalized.
2. The printed Corollary 6.1 remains unproved; its displayed reduction is
   kernel-checked to be insufficient under Definition 2.
3. Theorem 6.1 has no source-specified finite encoding type for arbitrary
   decidable-language pairs. Lean therefore records its conventional choice
   of pairs of total Boolean partial-recursive codes explicitly. Other
   representations are covered when they admit the generic computable hard
   embedding required by the transport theorem.
4. The repaired Theorem 5.1 is semantic and classical. A concrete executable
   membership-oracle implementation and complexity analysis are outside the
   current development.
5. The source repairs and statement correspondence have been reviewed with
   AI assistance against the pinned PDF; no independent human audit is
   claimed.
