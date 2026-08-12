# Union-Closedness of Language Generation map

Lean module: `GenLimit.Paper11_UnionClosednessOfLanguageGeneration`.
Declaration namespace: `GenLimit.UnionClosedness`.

## Pinned source

- Steve Hanneke, Amin Karbasi, Anay Mehrotra, and Grigoris Velegkas,
  *On Union-Closedness of Language Generation*;
- arXiv:2506.18642v1, dated 23 June 2025;
- local PDF SHA-256:
  `9e788a45543e67a80ab81880efe848da9b7ba1ed464bb696e2f462178dc5f089`;
- source statements were checked during integration by visually inspecting
  rendered PDF pp. 8--9, 13, 15, and 17 and by text extraction on pp. 20 and
  22.

This map uses the repository folder name as its identifier. It does not rely
on numbering in the research knowledge graph.

## Public entry points

The main paper-facing import is
`GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Main`. Its overview
facade exposes:

- `GenLimit.UnionClosedness.theorem_3_1`;
- `GenLimit.UnionClosedness.theorem_3_2`; and
- `GenLimit.UnionClosedness.theorem_3_3`.

The corresponding concrete classes and detailed results are exposed by:

- `theorem_3_1_witness`, `theorem_4_1`;
- `theorem_3_2_witness`, `theorem_4_3`; and
- `theorem_3_3_witness`, `theorem_4_4`.

For the union lower bounds, the numbered results follow the source's
duplicate-free enumeration convention. Explicit declarations suffixed
`_all_presentations` give the corollaries for the library convention that a
generator must work for all exact presentations, including repetitions.

## Main-result correspondence

| Paper item | Lean declaration | Status |
|---|---|---|
| Definition 2.1, generation on duplicate-free enumerations | `IsLimitGeneratorOnInjectivePresentations`, `GeneratableInLimitOnInjectivePresentations` | Complete, universe-generic, Paper-local API |
| Definitions 2.4--2.5, uniform and non-uniform generation | `GenLimit.Generic.UniformlyGeneratable`, `GenLimit.Generic.NonuniformlyGeneratable` | Reused from Core |
| Definitions 2.6--2.7, version space and EUC | `GenLimit.Generic.versionSpace`, `GenLimit.Generic.commonCore`, `GenLimit.LiRamanTewari.EventuallyUnboundedClosure` | Reused from Core and the #02 Learning Theory development; not duplicated in this paper |
| Theorem 3.1 | `theorem_3_1` | Complete existential wrapper |
| Detailed Theorem 4.1 | `theorem_4_1` | Complete concrete witnesses and injective-presentation lower bound |
| Theorem 3.2 | `theorem_3_2` | Complete for the standard uniform/non-uniform predicates, with countable class first as in the source; the separate “without requiring examples” prose strengthening is not encoded |
| Detailed Theorem 4.3 | `theorem_4_3` | Complete concrete witnesses and injective-presentation lower bound |
| Theorem 3.3 | `theorem_3_3` | Complete existential wrapper using the uncountable Theorem 3.1 class |
| Detailed Theorem 4.4 | `theorem_4_4` | Complete for its displayed countable cofinite-negative class |
| Proposition A.1 | `proposition_A_1` | Complete deterministic result under the source presentation convention |
| Proposition A.2 | none | Not formalized; randomized generators are outside the current deterministic model |
| Appendix A.2 prefix-realizability principle | `appendix_A_2_deterministic_prefix_realizability_core`, `appendix_A_2_not_generatableInLimit` | Generic deterministic principle, conditional on the explicit infinite-limit membership obligation |
| Appendix A.2 concrete families and Remark A.3 | none | Not formalized |

## Reuse and theorem relationships

The development deliberately adds no Paper11-specific material to
`GenLimit.Core`.

- The canonical language, stream, sample, generator, uniform, non-uniform,
  and limit-generation definitions come from `GenLimit.Generic`.
- Eventually Unbounded Closure is the existing
  `GenLimit.LiRamanTewari.EventuallyUnboundedClosure`; Paper11 does not define
  a second copy.
- Countable component classes use the #02 theorem
  `countable_classes_are_nonuniformly_generatable`.
- The relationship between overview Theorems 3.1 and 3.3 is recorded through
  the #02 finite-EUC-union theorem: if both Theorem 3.1 components had EUC,
  their union would be generatable, contradicting the union lower bound.
- Detailed Theorems 4.1 and 4.3 share one cursor-zero alternating recursion.
  The recursion runs on a common hard subfamily of both displayed pairs, and
  each paper-facing lower bound follows by restriction. This is stronger and
  clearer than maintaining two nearly identical recursions.

The injective-presentation convention, signed-integer witnesses, sweep
generators, Cantor helper, alternating recursion, and prefix-realizability
scheme remain Paper11-local. They should move to Core only after a second
independent development needs the same interface.

## Module organization

```text
Definitions.lean                  duplicate-free presentation semantics
SignedIntegers.lean               strictly negative/positive encodings
SweepGenerators.lean              fresh one-sided sweeps
Cardinality.lean                  Paper-local Cantor helper
MainClasses.lean                  detailed Theorem 4.1 classes
MinimalPairClasses.lean           detailed Theorem 4.3 classes
EventuallyUnboundedClosure.lean   detailed Theorem 4.4 and source diagnostics
Internal/AlternatingEngine.lean   shared hard subfamily and phase recursion
AlternatingPhaseRecursion.lean    Theorem 4.1 lower-bound wrapper
MinimalPairRecursion.lean         Theorem 4.3 lower-bound wrapper
Theorem41Cardinality.lean         Theorem 3.1 cardinalities and witness
Theorem43.lean                    detailed Theorem 4.3 facade
Theorem33UncountableEUC.lean      direct concrete EUC witness
Results/Detailed.lean             public detailed-results facade
Results/Overview.lean             public overview-results facade
Results/Appendix.lean             appendix status and entry point
Main.lean                         main-results import
```

## Source qualifications

### Presentation convention

The source describes enumerations without repetitions. The shared Core
definition permits repetitions and therefore asks a generator to satisfy a
strictly stronger success condition. Lean keeps the two notions separate and
provides only the valid direction from all presentations to injective
presentations.

### Theorem 3.3 versus detailed Theorem 4.4

Overview Theorem 3.3 asks for an uncountable class and explicitly points to
the first class from Theorem 3.1. The class displayed in detailed Theorem 4.4
is countable. Lean proves Theorem 4.4 for that literal class, proves its
countability, and packages overview Theorem 3.3 using the uncountable class
named by the overview.

### Uniformity sentence in the proof of Theorem 4.4

The final sentence of the printed proof calls the displayed class uniformly
generatable. This is false for the standard uniform definition. Lean proves
`cofiniteNegativeClass_not_uniformlyGeneratable`; the displayed theorem only
claims non-uniform generation and remains valid.

### Theorem 4.3 negative sweep

The displayed recurrence in the source may skip a finite initial block of
negative integers, whereas the first Theorem 4.3 class requires all negative
integers. The formal recursion starts at `-1` and proves exact negative
coverage. That cursor-zero construction also suffices for Theorem 4.1.

### “Without requiring examples”

The paper emphasizes that the component generators can start without a
positive sample. The current shared `UniformlyGeneratable` and
`NonuniformlyGeneratable` propositions express distinct-sample thresholds,
not a separate history-independent or autoregressive predicate. The standard
generation claims are formalized; this prose strengthening is not advertised
as an additional theorem.

## Verification and audit status

On 12 August 2026, the Paper11 umbrella build completed successfully with 937
jobs, the full project build completed successfully with 2,118 jobs, and all
16 Paper11 probes in `Audit.lean` passed the project's axiom allowlist. A
source scan found no `sorry`, `admit`, declared project axiom, or `unsafe`
declaration in this development. The proofs are classical and make no
computability, oracle-complexity, runtime, or randomized guarantee.

The source comparison performed during integration is AI-assisted and is not
a checksum-verified ChatGPT Pro audit record or a named human audit. A complete
human paper-to-Lean audit remains pending.
