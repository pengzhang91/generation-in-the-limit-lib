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

The statistical universal-rate theorems are not claimed.  Two supporting
lemmas record finite-tell-tale consequences motivated by the proofs of
Propositions 3.11--3.12, but they are not presented as formalizations of those
numbered statistical propositions.

## Paper-to-Lean correspondence

| Paper item | Lean declaration | Module | Status |
|---|---|---|---|
| Definitions 5--6, support membership oracle | `SupportGenerator` | `Definitions` | Complete semantic oracle interface; computability is not certified. |
| Definition 7, stability | `Stable` | `Definitions` | Complete support-stabilization predicate. |
| Definition 8, unambiguous generation | `UnambiguousAt`, `UnambiguousInLimit` | `Definitions` | Complete semantic support predicate using extended cardinality. |
| Definition 9, approximate breadth | `ApproximateBreadthAt`, `ApproximateBreadthInLimit` | `Definitions` | Complete probability-free online predicate. |
| Theorem 3.1 | -- | -- | Not formalized: the universal-rate dichotomy and its exponential upper and lower bounds are absent.  The Angluin characterization used in its proof is Background Theorem 2.2, not a core formalization of Theorem 3.1. |
| Theorem 3.2 | -- | -- | Not formalized: the statistical `e^{-n}` upper and lower bounds are absent.  The KM semantic engine used in its proof is Background Theorem 2.4, formalized separately in #01. |
| Theorem 3.3 | -- | -- | Statistical breadth theorem not formalized; its probability-free online reduction is represented by Theorem 3.5. |
| Theorem 3.4 and Proposition A.1 | -- | -- | Not formalized; these require the randomized Turing-machine support-membership argument. |
| Theorem 3.5 | `Results.theorem_3_5_semantic`; supporting `identifiableInLimit_iff_freshBreadthInLimit`, `freshBreadthInLimit_implies_identifiableInLimit`, `repeatingBreadthInLimit_implies_identifiableInLimit` | `Results.Overview`, `PositiveBreadth`, `OnlineReductions` | Complete semantic online biconditional under the paper's uniform family-membership oracle; the name explicitly does not claim the paper's Turing-computability layer. |
| Theorem 3.6 | -- | -- | Statistical unambiguous-generation theorem not formalized. |
| Theorem 3.7 | `Results.theorem_3_7_semantic`; supporting `stable_unambiguousInLimit_implies_identifiableInLimit`, `not_exists_stable_unambiguousInLimit_of_not_identifiableInLimit` | `Results.Overview`, `OnlineReductions` | Complete semantic support-oracle reduction and impossibility statement; Turing computability is not claimed. |
| Theorem 3.8 | -- | -- | Statistical approximate-breadth theorem not formalized. |
| Theorem 3.9 | `Results.theorem_3_9_semantic`; supporting `stable_approximateBreadthInLimit_implies_identifiableInLimit`, `not_exists_stable_approximateBreadthInLimit_of_not_identifiableInLimit` | `Results.Overview`, `OnlineReductions` | Complete semantic support-oracle reduction and impossibility statement; Turing computability is not claimed. |
| Proposition 3.10 | -- | -- | Statistical subset-oracle theorem not formalized. |
| Proposition 3.11 | `finiteCollection_conditionTwo` (supporting lemma only) | `FurtherIdentification` | The exponential-rate proposition is not formalized.  Lean proves only that a finite-range family satisfies Angluin's condition. |
| Proposition 3.12 | `finiteLanguages_conditionTwo` (supporting lemma only) | `FurtherIdentification` | The exponential-rate proposition is not formalized.  Lean proves only that a family of finite languages satisfies Angluin's condition. |
| Theorem 3.13 | -- | -- | The positive/negative exponential-rate theorem is not formalized.  Its qualitative Gold ingredient is Background Theorem 2.3, formalized separately in #0. |
| Background Theorem 2.1 | -- | -- | The exact paper-facing nested-chain statement is absent. |
| Background Theorem 2.2 | `GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo` | `Paper00A_PositiveDataInference.Semantic.Characterization` | Already formalized in the canonical #0A Angluin development; P03 introduces no duplicate wrapper. |
| Background Theorem 2.3 | `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily` | `Paper00_LanguageIdentification.Informant.Enumeration` | Already formalized in the canonical #0 Gold development; P03 introduces no duplicate wrapper. |
| Background Theorem 2.4 | `GenLimit.KM.Semantic.kleinbergMullainathan_main` | `Paper01_LanguageGeneration.Semantic` | Already formalized in the canonical #01 KM development; P03 introduces no duplicate wrapper. |
| Appendix Theorem B.1 and Corollary B.2 | -- | -- | Not formalized.  The explicit last-critical support-valued construction remains future work. |

## Reuse and ownership

- `IdentifiableInLimit` is only a paper-facing abbreviation for
  `GenLimit.Angluin.SemanticallyInferrable`.
- The proof of source Theorem 3.1 invokes Background Theorem 2.2,
  `GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo`.  That background
  result is owned by #0A and is not presented as a P03 Theorem 3.1 core; the
  universal-rate dichotomy itself remains unformalized.  P03 does not depend
  on the later #08 Hallucination Detection development.
- The proofs of source Theorems 3.2 and 3.13 use the canonical #01 KM semantic
  engine and #0 Gold informant learner, respectively.  P03 does not wrap those
  background results as numbered P03 theorem cores because the corresponding
  statistical-rate conclusions remain unformalized.
- `finiteCollection_conditionTwo` and `finiteLanguages_conditionTwo` are
  complete standalone structural lemmas motivated by Propositions 3.11 and
  3.12; they do not claim either statistical proposition.
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
  success to have value `0`.  This source-level polarity finding is recorded
  here rather than represented by dedicated Lean declarations.

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
5. `FurtherIdentification.lean`
6. `GenLimit.Bridges.Paper03ToPaper04`

## Verification

```text
lake build GenLimit.Paper03_HallucinationAndModeCollapse
lake build GenLimit.Bridges.Paper03ToPaper04
```

No `sorry`, `admit`, or project-defined axiom occurs in the P03 modules.
