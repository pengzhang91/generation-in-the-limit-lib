# #03 On the Limits of Language Generation map

Lean module: `GenLimit.Paper03_HallucinationAndModeCollapse`.
Declaration namespace: `GenLimit.HallucinationModeCollapse`.

## Pinned source

- Alkis Kalavasis, Anay Mehrotra, and Grigoris Velegkas, *On the Limits of
  Language Generation: Trade-Offs Between Hallucination and Mode Collapse*.
- Formalization source: [arXiv:2411.09642v3](https://arxiv.org/abs/2411.09642v3).
- The source correspondence has not yet received a named human audit or a
  checksum-pinned external statement-faithfulness audit.

## Scope and status

The present development deliberately formalizes the probability-free
semantic fragment.  Its main completed results are the support-valued online
cores of Theorems 3.5, 3.7, and 3.9.  The generator exposes an exact Boolean
membership oracle for its support, but Lean does not assert that the oracle,
the generator, or the induced identifier has a Turing-machine implementation.

The statistical universal-rate theorems are not claimed.  Several files
record only the deterministic or qualitative facts used inside their proofs;
their declaration names end in `_core` or `_online_core` for that reason.

## Paper-to-Lean correspondence

| Paper item | Lean declaration | Module | Status |
|---|---|---|---|
| Definitions 5--6, support membership oracle | `SupportGenerator` | `Definitions` | Complete semantic oracle interface; computability is not certified. |
| Definition 7, stability | `Stable` | `Definitions` | Complete support-stabilization predicate. |
| Definition 8, unambiguous generation | `UnambiguousAt`, `UnambiguousInLimit` | `Definitions` | Complete semantic support predicate using extended cardinality. |
| Definition 9, approximate breadth | `ApproximateBreadthAt`, `ApproximateBreadthInLimit` | `Definitions` | Complete probability-free online predicate. |
| Theorem 3.1 | `theorem_3_1_qualitative_core` | `RateCores` | Qualitative Angluin characterization only; universal rates and effective-oracle claims are not formalized. |
| Theorem 3.2 | `theorem_3_2_online_engine` | `RateCores` | Reuses the KM semantic online engine; the statistical `e^{-n}` theorem is not formalized. |
| Theorem 3.3 | -- | -- | Statistical breadth theorem not formalized; its probability-free online reduction is represented by Theorem 3.5. |
| Theorem 3.4 and Proposition A.1 | -- | -- | Not formalized; these require the randomized Turing-machine support-membership argument. |
| Theorem 3.5 | `Results.theorem_3_5`; supporting `theorem_3_5_fresh_negative_core`, `theorem_3_5_repeating_negative_core` | `Results.Overview`, `PositiveBreadth`, `OnlineReductions` | Complete semantic online biconditional under the paper's uniform family-membership oracle. |
| Theorem 3.6 | `theorem_3_6_stability_core` | `RateCores` | Deterministic post-stabilization persistence only; the probability/rate argument is absent. |
| Theorem 3.7 | `Results.theorem_3_7`; supporting `theorem_3_7`, `theorem_3_7_impossibility` | `Results.Overview`, `OnlineReductions` | Complete semantic online reduction and paper-facing impossibility statement. |
| Theorem 3.8 | `theorem_3_8_stability_core` | `RateCores` | Deterministic post-stabilization persistence only; the probability/rate argument is absent. |
| Theorem 3.9 | `Results.theorem_3_9`; supporting `theorem_3_9`, `theorem_3_9_impossibility` | `Results.Overview`, `OnlineReductions` | Complete semantic online reduction and paper-facing impossibility statement. |
| Theorem 3.10 | -- | -- | Statistical theorem not formalized. |
| Proposition 3.11 | `proposition_3_11_online_core` | `FurtherIdentification` | Qualitative finite-range identification core only. |
| Proposition 3.12 | `proposition_3_12_online_core` | `FurtherIdentification` | Qualitative finite-language identification core only. |
| Theorem 3.13 | `theorem_3_13_online_core` | `PositiveNegative` | Qualitative upper-bound ingredient only; the two-sided exponential-rate theorem is not formalized. |
| Background Theorem 2.1 | -- | -- | The exact paper-facing nested-chain statement is absent. |
| Background Theorem 2.2 | `theorem_3_1_qualitative_core` | `RateCores` | Reused through the canonical #0A Angluin characterization. |
| Background Theorem 2.3 | `theorem_3_13_online_core` | `PositiveNegative` | Reused through the canonical #0 Gold informant learner. |
| Background Theorem 2.4 | `theorem_3_2_online_engine` | `RateCores` | Reuses the #01 KM semantic theorem. |
| Appendix Theorem B.1 and Corollary B.2 | -- | -- | Not formalized.  The explicit last-critical support-valued construction remains future work. |

## Reuse and ownership

- `IdentifiableInLimit` is only a paper-facing abbreviation for
  `GenLimit.Angluin.SemanticallyInferrable`.
- Theorem 3.1 directly reuses
  `GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo`; P03 does not
  depend on the later #08 Hallucination Detection development.
- Theorem 3.13 is a thin existential wrapper around
  `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily`.
  No labeled-stream or least-consistent-learner implementation is duplicated
  inside P03.
- Theorem 3.2 directly reuses
  `GenLimit.KM.Semantic.kleinbergMullainathan_main`.
- `SupportGenerator`, stability, unambiguity, and approximate breadth remain
  paper-local.  None was moved into the lightweight Core.
- The explicit #03/#04 comparison lives in
  `GenLimit.Bridges.Paper03ToPaper04`, so the two native paper umbrellas remain
  independent.

## Source qualifications exposed by Lean

- The online discussion around Theorem 3.5 alternates between a fresh-output
  support `K \ S_t` and a proof sentence treating the support as `K`.  Lean
  distinguishes `FreshBreadthInLimit` from `RepeatingBreadthInLimit` and uses
  `completedSupport = support ∪ sample` to validate both reductions.
- The unambiguous-error indicator printed in arXiv v3 assigns `1` to the
  success condition, while the surrounding loss/rate convention requires
  success to have value `0`.  `printedUnambiguousError_eq_zero_iff` and
  `correctedUnambiguousError_eq_zero_iff` record the polarity difference.

These are Codex-assisted formalization findings and have not yet been
confirmed by a named human audit.

## Formalization boundaries

- The support oracle is extensionally correct but not accompanied by a
  computability certificate.
- The semantic identifier may use classical choice.  Consequently the online
  results should be described as complete semantic cores, not as full
  Turing-machine formalizations of the source theorems.
- Probability distributions, IID sampling, universal rates, exponential
  upper/lower bounds, and randomized computation are outside the current
  scope.
- The source commonly works with infinite targets.  The semantic reductions
  state only the assumptions used by their proofs; they do not silently add a
  global infinite-language premise.

## Suggested reading order

1. `Definitions.lean`
2. `OnlineReductions.lean`
3. `PositiveBreadth.lean`
4. `Results/Overview.lean`
5. `PositiveNegative.lean`
6. `RateCores.lean`
7. `FurtherIdentification.lean`
8. `GenLimit.Bridges.Paper03ToPaper04`

## Verification

```text
lake build GenLimit.Paper03_HallucinationAndModeCollapse
lake build GenLimit.Bridges.Paper03ToPaper04
```

No `sorry`, `admit`, or project-defined axiom occurs in the P03 modules.
