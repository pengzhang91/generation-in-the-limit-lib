# Kernel audit

This record is anchored to release `v0.3.0` (17 July 2026). The following
checks were run with Lean 4.24.0 and Mathlib 4.24.0.

```text
lake build
Build completed successfully.
```

The umbrella module `GenLimit.lean` imports the shared core, both paper
developments, and the explicit bridge layer.  The paper paths can also be
built independently:

```text
lake build GenLimit.KM
lake build GenLimit.KM.Semantic
lake build GenLimit.KM.FiniteQuery
lake build GenLimit.DenseGeneration
lake build GenLimit.Bridges
```

An import-boundary scan confirms that the modules under `GenLimit/KM/` do not
import anything under `GenLimit/DenseGeneration/`, and the modules under
`GenLimit/DenseGeneration/` do not import anything under `GenLimit/KM/`. The
theorem `critical_recursiveCritical` is isolated in
`GenLimit.Bridges.KMToDenseGeneration`.

A source scan found no `sorry`, `admit`, or declared project axiom in any Lean
module. `Audit.lean` checks that every main declaration uses exactly the
allowlisted axiom set below and fails to compile if the set changes:

```text
GenLimit.KM.Semantic.kleinbergMullainathan_main
  [propext, Classical.choice, Quot.sound]

GenLimit.OracleFamily.kleinbergMullainathan_main
  [propext, Classical.choice, Quot.sound]

GenLimit.PatientMachine.patient_validity
  [propext, Classical.choice, Quot.sound]

GenLimit.PatientMachine.settledChargingCertificate
  [propext, Classical.choice, Quot.sound]

GenLimit.PatientMachine.patientScope_lowerDensity_half
  [propext, Classical.choice, Quot.sound]

GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
  [propext, Classical.choice, Quot.sound]
```

These are Lean/Mathlib's standard classical and quotient axioms. The project
adds no axiom.

## Access-model audit

The shared `OracleFamily` record is declared in
`GenLimit.Core.OracleFamily`.  The semantic KM generator uses its languages
and infinitude proofs; KM criticality asks for exact inclusion between whole
languages, so this short construction is classical and noncomputable from the
pointwise oracle in general.  The finite-query KM machine additionally uses
the `query` field and realizes its tests as finite Boolean computations.

The DenseGeneration machine receives the same family object for direct
comparison, but its semantic transition also uses only the languages and
their infinitude; recursive criticality asks for exact inclusion between whole
languages.  Its decisions are therefore classical and noncomputable.  The
DenseGeneration theorem does not state that this machine can be run using
finitely many membership queries.

## Theorem scope

Both KM main theorems prove the current Lean specification: eventually every
output lies in the target and is absent from the adversary sample observed by
that time.  They do not require outputs from different generator rounds to be
distinct.

`patientScope_lowerDensity_half` proves the operational achievability bound
`1/2 ≤ lower density` for every exact presentation of every indexed target.
`patientScope_generation_and_lowerDensity` adds eventual target validity and
novelty. The separate adversarial upper bound used to call `1/2` optimal is
not included in this version.

## Human audit status

The KM semantic theorem and construction correspondence have been
human-audited; line-by-line proof correspondence and the finite-query path are
outside that audit. The DenseGeneration input/output specification has been
audited with its algorithm treated as a black box. See
[HUMAN_AUDIT.md](HUMAN_AUDIT.md) for the dated scopes and exclusions.
