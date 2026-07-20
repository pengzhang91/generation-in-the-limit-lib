# Kernel audit

This record describes the current revision, checked on 20 July 2026 with Lean
4.24.0 and Mathlib 4.24.0.

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
lake build GenLimit.DenseGeneration.Partial
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

GenLimit.PartialEnumeration.Counterexample.output_not_mem_trueLanguage
  [propext, Classical.choice, Quot.sound]

GenLimit.PartialEnumeration.lemma_3_16_generation
  [propext, Classical.choice, Quot.sound]

GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17
  [propext, Classical.choice, Quot.sound]

GenLimit.PartialEnumeration.theorem_3_17_lowerDensity
  [propext, Classical.choice, Quot.sound]

GenLimit.PartialEnumeration.theorem_3_17
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

For partial enumeration, `closure` keeps exactly the infinite nonempty finite
intersections, ordered by their binary subset codes. Membership in a selected
intersection is a finite conjunction of original queries, but deciding which
intersections are infinite is classical and noncomputable. Thus the filtered
indexing is part of the semantic access-model boundary.

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

`lemma_3_16_generation` assumes `Presents stream E`, `E.Infinite`, and
`E ⊆ O.language z`; it proves eventual target validity, freshness from the
stream, and output novelty for patient-scope on the finite-intersection
closure. `theorem_3_17_lowerDensity` proves the lower bound
`(1/2) * relativeLowerDensity E K ≤ generator lower density`. It does not
claim a full `1/2` bound unless the relative lower density of `E` in `K` is
one.

The formalization of Example 3.15 fixes the otherwise unspecified order of
the partial enumeration to `4, 8, 12, ...`. For that exact stream, the direct
untransformed machine outputs `1, 3, 5, ...` and never outputs an element of
the true positive-even language.

## Human audit status

The KM semantic development has a Level 3 human audit covering its theorem,
construction, and proof correspondence; the finite-query path is outside that
audit. The DenseGeneration exact-presentation result has a Level 2 end-to-end
audit covering its main theorem statement and patient-scope construction, but
not its intermediate proof correspondence. The Section 3.3
finite-intersection transformation and the paper-to-Lean statements of Lemma
3.16 and Theorem 3.17 have a Level 2 audit; their intermediate proof
correspondence and Example 3.15 have not been human-audited. See
[HUMAN_AUDIT.md](HUMAN_AUDIT.md) for the dated scopes and exclusions.
