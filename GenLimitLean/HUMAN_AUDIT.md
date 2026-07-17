# Human audit records

These are human semantic audits, separate from Lean's kernel checks in
[AUDIT.md](AUDIT.md). Each record is complete only at its stated level.

| Development | Audit level | Auditor | Recorded | Release |
|---|---|---|---|---|
| KM semantic | Theorem statement and semantic-construction correspondence | Peng Zhang | 17 July 2026 | `v0.3.0` |
| DenseGeneration | Black-box input/output specification | Peng Zhang | 16 July 2026 | `v0.3.0` |

## KM semantic construction

For a fixed family `O`, `KM.Semantic.generator O stream` does not receive the
hidden target index `z`. If `stream` exactly presents `O.language z`, the main
theorem says that every sufficiently late output belongs to the target and is
absent from `sample stream t`.

| Checked item | Audited meaning |
|---|---|
| Model | `OracleFamily` is an indexed family of infinite languages, and `Presents` means exact positive-data presentation. |
| Criticality | `Critical` is KM criticality; critical languages form the required inclusion chain and the target is eventually critical. |
| Construction | At round `t`, `focus` selects the greatest critical index below `t`, and `fresh` selects the least focused-language element outside `sample stream t`. |
| Uniformity | The generator depends on `O`, `stream`, and `t`, not on `z`. |
| Conclusion | Eventual target membership and freshness from the first `t` stream observations; generator outputs need not be mutually distinct. |
| Access model | Round `t` uses the current observation prefix, but whole-language inclusion makes this semantic construction noncomputable from the membership oracle. |

Code anchors are [`GenLimit/KM/Critical.lean`](GenLimit/KM/Critical.lean) and
[`GenLimit/KM/Semantic.lean`](GenLimit/KM/Semantic.lean), with the shared model
in [`GenLimit/Core/Basic.lean`](GenLimit/Core/Basic.lean). This audit does not
certify line-by-line correspondence between the Lean proof and the paper proof,
and it does not cover the separate finite-query development.

## DenseGeneration black-box specification

For a fixed family `O`, `PatientMachine.output O stream` does not receive the
hidden target index `z`. For every stream exactly presenting `O.language z`,
the joint theorem gives eventual target validity, novelty, and target-relative
lower density at least `1 / 2`.

| Checked item | Audited meaning |
|---|---|
| Inputs | `OracleFamily` is an indexed family of infinite languages; `Presents stream (O.language z)` means that the stream presents exactly the target. |
| Uniformity | The generator depends on `O` and the observed stream, not on `z`. |
| Validity | Every sufficiently late output belongs to `O.language z`. |
| Novelty | Every sufficiently late output differs from all stream values through that round and from all earlier generator outputs. |
| Density | The numerator counts target elements below `n` first announced by the generator; the denominator is `|O.language z ∩ Finset.range n|`, not `n`. |
| Strength | The result proves achievability of target-relative lower density at least `1 / 2`. |

Code anchors are
[`GenLimit/DenseGeneration/Patient/Machine.lean`](GenLimit/DenseGeneration/Patient/Machine.lean)
and [`GenLimit/DenseGeneration/Patient/Main.lean`](GenLimit/DenseGeneration/Patient/Main.lean),
with `Presents` and `OracleFamily` in `GenLimit.Core`. This audit does not
certify manuscript-algorithm correspondence, paper-to-Lean proof
correspondence, finite-query executability, computational complexity, or the
separate upper bound needed for optimality. The current machine is semantic
and noncomputable because recursive criticality compares whole infinite
languages.

## Re-audit condition

These records apply to `v0.3.0` and descendants in which their code anchors are
unchanged. Re-audit is required if an anchor changes or a stronger
correspondence claim is made.
