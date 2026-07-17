# GenLimit

`GenLimit` is a Lean 4 library for language generation in the limit. It
formalizes the foundational Kleinberg--Mullainathan theorem and the
DenseGeneration patient-scope result, while keeping shared mathematics,
paper-specific developments, and cross-paper comparisons separate.

The project uses Lean 4.24.0 and Mathlib 4.24.0. All current main theorem
paths compile without `sorry`, `admit`, or project-defined axioms.

## Main results

| Development | Main Lean declaration | Formalized result |
|---|---|---|
| KM semantic | `GenLimit.KM.Semantic.kleinbergMullainathan_main` | Short, classical proof of KM Theorem 2.1 |
| KM finite-query | `GenLimit.OracleFamily.kleinbergMullainathan_main` | Stateful endpoint-test algorithm from the NeurIPS proceedings |
| DenseGeneration | `GenLimit.PatientMachine.patientScope_lowerDensity_half` | Patient-scope lower density at least `1 / 2` for every exactly presented target |
| DenseGeneration joint conclusion | `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity` | Eventual validity, freshness, output novelty, and the same density bound |

Both KM developments eventually output target elements that are fresh relative
to the observed adversary sample. The semantic KM proof compares whole
infinite languages and is noncomputable; the finite-query development realizes
its tests through the Boolean membership oracle.

The DenseGeneration machine is also semantic and noncomputable because its
recursive criticality uses exact inclusion between infinite languages. Its
theorem proves the `1 / 2` achievability bound for arbitrary, possibly sparse,
targets. It does not claim finite-query execution or formalize the separate
upper bound needed for optimality.

## Library structure

```text
                         GenLimit.Core
                        /             \
               GenLimit.KM           GenLimit.DenseGeneration
                        \             /
                       GenLimit.Bridges
```

- `GenLimit.Core` contains paper-independent definitions and stabilization
  lemmas.
- `GenLimit.KM` contains the semantic and finite-query KM developments.
- `GenLimit.DenseGeneration` contains the abstract counting argument and the
  concrete patient-scope machine.
- `GenLimit.Bridges` contains explicit comparison theorems without making one
  paper development depend on the other.

The umbrella module [`GenLimit.lean`](GenLimit.lean) imports all four layers.
The paper-specific umbrellas [`GenLimit/KM.lean`](GenLimit/KM.lean) and
[`GenLimit/DenseGeneration.lean`](GenLimit/DenseGeneration.lean) can be used
independently.

## Build

From this directory:

```bash
lake exe cache get
lake build
lake env lean Audit.lean
```

Individual developments can also be built separately:

```bash
lake build GenLimit.KM
lake build GenLimit.KM.Semantic
lake build GenLimit.KM.FiniteQuery
lake build GenLimit.DenseGeneration
lake build GenLimit.Bridges
```

Opening this directory in VS Code with the Lean 4 extension provides
interactive theorem goals and diagnostics.

## Suggested reading order

| Goal | Start with |
|---|---|
| Shared model and exact presentations | [`GenLimit/Core/Basic.lean`](GenLimit/Core/Basic.lean) |
| Consistency stabilization | [`GenLimit/Core/TargetStability.lean`](GenLimit/Core/TargetStability.lean) |
| Indexed language family and membership oracle | [`GenLimit/Core/OracleFamily.lean`](GenLimit/Core/OracleFamily.lean) |
| Short semantic KM proof | [`GenLimit/KM/Critical.lean`](GenLimit/KM/Critical.lean), then [`GenLimit/KM/Semantic.lean`](GenLimit/KM/Semantic.lean) |
| Finite-query KM algorithm | [`GenLimit/KM/FiniteQuery.lean`](GenLimit/KM/FiniteQuery.lean) |
| DenseGeneration criticality and machine | [`GenLimit/DenseGeneration/Critical.lean`](GenLimit/DenseGeneration/Critical.lean), then [`GenLimit/DenseGeneration/Patient/Machine.lean`](GenLimit/DenseGeneration/Patient/Machine.lean) |
| DenseGeneration proof chain | `Patient/Validity.lean`, `Patient/Fact312.lean`, `Patient/Charging.lean`, then [`Patient/Main.lean`](GenLimit/DenseGeneration/Patient/Main.lean) |
| Cross-paper comparison | [`GenLimit/Bridges/KMToDenseGeneration.lean`](GenLimit/Bridges/KMToDenseGeneration.lean) |

## Paper maps and audits

- [`PAPER_MAP.md`](PAPER_MAP.md) is the repository-level paper registry.
- [`PaperMaps/KM.md`](PaperMaps/KM.md) maps the KM paper to Lean declarations.
- [`PaperMaps/DenseGeneration.md`](PaperMaps/DenseGeneration.md) maps the
  DenseGeneration manuscript to Lean declarations.
- [`PaperMaps/RELATIONSHIPS.md`](PaperMaps/RELATIONSHIPS.md) records shared
  foundations and explicit bridges.
- [`AUDIT.md`](AUDIT.md) records kernel, axiom, and access-model checks.
- [`HUMAN_AUDIT.md`](HUMAN_AUDIT.md) records the scoped KM semantic and
  DenseGeneration black-box audits.

Bibliographic metadata is collected in [`CITATION.bib`](CITATION.bib).
