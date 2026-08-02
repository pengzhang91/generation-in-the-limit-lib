# Kernel audit

This record describes the current revision, checked on 2 August 2026 with Lean
4.24.0 and Mathlib 4.24.0.

```text
lake build
Build completed successfully (1982 jobs).

lake env lean Audit.lean
All asserted declarations have exactly
[propext, Classical.choice, Quot.sound].
```

The umbrella module `GenLimit.lean` imports the shared core, all three paper
developments, and the explicit bridge layer.  The paper paths can also be
built independently:

```text
lake build GenLimit.Gold
lake build GenLimit.Gold.Abstract
lake build GenLimit.Gold.Text
lake build GenLimit.Gold.Informant
lake build GenLimit.KM
lake build GenLimit.KM.Semantic
lake build GenLimit.KM.FiniteQuery
lake build GenLimit.KM.FiniteQuery.ArxivV1
lake build GenLimit.KM.SetInterface
lake build GenLimit.DenseGeneration
lake build GenLimit.DenseGeneration.Partial
lake build GenLimit.Bridges
lake build GenLimit.Bridges.GoldToKM
lake build GenLimit.Bridges.GoldToDenseGeneration
```

An import-boundary scan confirms that the modules under `GenLimit/Gold/`,
`GenLimit/KM/`, and `GenLimit/DenseGeneration/` do not import either of the
other paper developments. Cross-paper results are isolated in the bridge
layer: `critical_recursiveCritical` is in
`GenLimit.Bridges.KMToDenseGeneration`, while the identification-to-generation
implication and the co-singleton separation are in
`GenLimit.Bridges.GoldToKM`; the quantitative PatientScope strengthening is
in `GenLimit.Bridges.GoldToDenseGeneration`.

A source scan found no `sorry`, `admit`, or declared project axiom in any Lean
module. `Audit.lean` checks that every main declaration uses exactly the
allowlisted axiom set below and fails to compile if the set changes:

```text
GenLimit.KM.Semantic.kleinbergMullainathan_main
  [propext, Classical.choice, Quot.sound]

GenLimit.OracleFamily.kleinbergMullainathan_main
  [propext, Classical.choice, Quot.sound]

GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main
  [propext, Classical.choice, Quot.sound]

GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface
  [propext, Classical.choice, Quot.sound]

GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions
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

GenLimit.Gold.Abstract.gold_theorem_7_1
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Text.finiteLanguages_identifiableWith
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Text.finiteLanguages_maximal_semanticallyIdentifiable
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Text.enumerationLearner_identifiesFamily_of_isInclusionAntichain
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Text.exists_locking_of_identifiesLanguage
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Text.superfinite_not_semanticallyIdentifiable
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.identifier_implies_fresh_generation
  [propext, Classical.choice, Quot.sound]

GenLimit.GoldKMSeparation.generation_without_identification
  [propext, Classical.choice, Quot.sound]

GenLimit.GoldDenseSeparation.dense_generation_without_identification
  [propext, Classical.choice, Quot.sound]
```

These are Lean/Mathlib's standard classical and quotient axioms. The project
adds no axiom.

## Access-model audit

The shared `OracleFamily` record is declared in
`GenLimit.Core.OracleFamily`.  The semantic KM generator uses its languages
and infinitude proofs; KM criticality asks for exact inclusion between whole
languages, so this short construction is classical and noncomputable from the
pointwise oracle in general. The finite-set interface is semantic as well: it
uses whole-language inclusion and classical fresh-element choice, while its
candidate scope is determined solely by the number of distinct observations.
Both finite-query KM machines additionally use the `query` field and realize
their tests as finite Boolean computations. The Proceedings machine tests the
new endpoint; the separate arXiv-v1 machine searches the whole selected prefix
and returns its least fresh eligible element.

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

The Gold layer is semantic. Its abstract identification-situation model
formalizes all three clauses of Theorem 7.1: necessity of distinguishability,
sufficiency of collapsing uncertainty via every enumeration, and sufficiency
of distinguishability when each object's allowable-sequence set is countable.
The theorem does not claim that its learners or enumerations are computable.

The language-specific layer uses arbitrary exact positive texts and complete
correct informants. `finiteLanguages_identifiableWith` formalizes
the accumulated-sample learner; its empty-language case is vacuous because no
function `ℕ → ℕ` has empty range.
`enumerationLearner_identifiesFamily_of_isInclusionAntichain` proves
positive-text identification only under the stated inclusion-antichain
condition. `informantEnumerationLearner_identifiesFamily` identifies every
indexed family from complete informants, resolving duplicate names by the
least equal index.

`exists_locking_of_identifiesLanguage` is the arbitrary-text semantic locking
lemma for nonempty targets. The superfinite theorem derives finite tell-tale
necessity and rules out any class containing all finite languages and at
least one infinite language. It does not formalize Gold's stronger effective
construction of a recursive bad text.

`identifier_implies_fresh_generation` converts exact-name identification of
an infinite oracle family into the KM trace-level freshness guarantee using a
classical fresh-element selector. The co-singleton separation instead uses
the existing finite-query KM generator on the uniformly decidable family
`ℕ, ℕ \ {0}, ℕ \ {1}, ...`; that family is KM-generatable from every exact
text but is not Gold-identifiable from all arbitrary positive texts.
`dense_generation_without_identification` strengthens the same-family
separation with PatientScope output novelty and target-relative lower density
at least `1 / 2`.

All four KM paths prove the current Lean specification on their stated
interfaces: eventually every output lies in the target and is absent from the
adversary sample observed by that time. The finite-set path remains correct
under repeated observations by using distinct-observation cardinality as its
candidate scope. The two finite-query paths formalize different published
Section 5 algorithms: the NeurIPS proceedings endpoint test and the arXiv-v1
least-fresh whole-prefix search. None requires outputs from different
generator rounds to be distinct.

The current KM scope does not include finite-family uniform Theorem 2.2,
robust-prompt Theorem 7.1, arXiv-v1's stronger regular-subset-query prompted
results, or the associated context-free and impossibility claims. The universe
is fixed to `ℕ`; no arbitrary-countable-universe transport theorem is claimed.

## External statement-audit evidence

The KM additions were reviewed through an AI-assisted code-only reconstruction
followed by a comparison against pinned NeurIPS and arXiv-v1 PDFs at Lean
snapshot `dfcd13534f9d51642a9f88904268e95454c88f7f`. Immutable artifact links,
PDF hashes, report hashes, findings, and the exact formalization boundary are
recorded in [the KM paper map](PaperMaps/KM.md). This is external review input,
not a kernel result or human correspondence audit.

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
construction, and proof correspondence; both finite-query paths and the
finite-set interface are outside that audit. The DenseGeneration
exact-presentation result has a Level 2 end-to-end
audit covering its main theorem statement and patient-scope construction, but
not its intermediate proof correspondence. The Section 3.3
finite-intersection transformation and the paper-to-Lean statements of Lemma
3.16 and Theorem 3.17 have a Level 2 audit; their intermediate proof
correspondence and Example 3.15 have not been human-audited. See
[HUMAN_AUDIT.md](HUMAN_AUDIT.md) for the dated scopes and exclusions. The
shared Core prerequisites and Gold Text have a recorded human audit at Level
2, covering the concrete arbitrary-text semantic chain from the model
and finite learner through locking and the superfinite obstruction. Gold's Abstract
Theorem 7.1 path, concrete text enumeration, abstract/text specialization,
informant development, and Gold-to-generation bridges remain outside the
recorded human audit.
