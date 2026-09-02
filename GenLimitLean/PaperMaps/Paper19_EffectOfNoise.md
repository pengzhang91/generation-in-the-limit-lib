# Paper 19: Characterizing the Effect of Noise in Language Generation in the Limit

This map records the correspondence between Aaron Li and Ian Zhang,
*Characterizing the Effect of Noise in Language Generation in the Limit*,
and the Lean development under `GenLimit.Paper19_EffectOfNoise`.

## Source edition and scope

- Formalization source: arXiv:2601.21237v2, dated 1 June 2026; the PDF is
  dated 2 June 2026.
- Lean umbrella: `GenLimit.Paper19_EffectOfNoise`.
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper19_EffectOfNoise/Results/Overview.lean).
- Status: **all four headline results, Theorems 2.16--2.19, are fully
  formalized**.  Their supporting Section 3 and Section 4 results are also
  represented, subject to the noisy-closure-dimension packaging described
  below.
- The development formalizes semantic mathematics.  It uses classical choice
  and does not claim an extracted executable algorithm or running-time bound.
- The source's global assumptions that the universe is countable and every
  language is infinite are explicit in the generic Lean statements as
  `[Countable α]`, `[Nonempty α]`, and `AllLanguagesInfinite C`.

## Claim-to-Lean correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definitions 2.1--2.7 and 2.14--2.15 | `MissingAtMost`, `EnumerationWithNoiseAtMost`, `CorrectAt`, and the fixed-level and noise-dependent generation predicates in [`Definitions.lean`](../GenLimit/Paper19_EffectOfNoise/Definitions.lean) | Full semantic interface | Definition 2.5 is an injective stream whose range covers the target and contains at most `i` distinct extraneous values. `observed stream t` contains `x₀,...,xₜ`, matching the source's inclusive time convention. |
| Definitions 2.8--2.12 | `consistentLanguages`, `noisyCommonCore`, `noisyClosure`, `NoisyClosureWitnessAt`, and `FiniteNoisyClosureDimensionAt` in [`Closure.lean`](../GenLimit/Paper19_EffectOfNoise/Closure.lean) | Full for the finiteness-based interface | Lean preserves the source's empty-version-space convention. It represents `NCᵢ(C) < ∞` by eventual absence of arbitrarily large witnesses instead of assigning an artificial extended-natural value to `NCᵢ(C)`. |
| Lemma 2.10 | `lemma_2_10` in [`Closure.lean`](../GenLimit/Paper19_EffectOfNoise/Closure.lean) | Full | Includes the source's alternative that the lower-noise closure is empty. |
| Lemma 2.11 | `lemma_2_11` in [`Closure.lean`](../GenLimit/Paper19_EffectOfNoise/Closure.lean) | Full | The noisy closure is contained in every consistent target language. |
| Lemma 2.13 | `noisyClosureWitnessAt_mono`, `finiteNoisyClosureDimensionAt_anti` in [`Closure.lean`](../GenLimit/Paper19_EffectOfNoise/Closure.lean) | Full for downstream uses | The witness monotonicity and corresponding finiteness implication are proved; there is no separate literal inequality between extended-natural-valued dimensions. |
| Lemma 3.1 | `lemma_3_1` in [`FixedLevel.lean`](../GenLimit/Paper19_EffectOfNoise/FixedLevel.lean) | Full | Exact characterization in P19's injective, distinct-value-noise and inclusive-time model. Both the closure generator and the finite-prefix adversary are constructed. |
| Lemma 3.2 | `lemma_3_2_squareRootWitnessTransfer`, `lemma_3_2_infinite_dimension_descends` in [`SquareRoot.lean`](../GenLimit/Paper19_EffectOfNoise/SquareRoot.lean) | Full proof content in witness form | Lean proves the exact `k²`-witness to `k`-witness transfer and the infinite-dimension consequence. This is the content needed for the paper's square-root inequality, without defining a numerical extended-natural `NCᵢ`. |
| Theorem 3.3 / uniform half of Theorem 2.16 | `theorem_3_3_uniform_finite_noise_collapse`, `theorem_2_16_uniform` in [`SquareRoot.lean`](../GenLimit/Paper19_EffectOfNoise/SquareRoot.lean) | Full | Every fixed positive finite noise level is equivalent to level one. |
| Theorem 3.4, recalled from Raman--Raman | `GenLimit.NoisyExamples.theorem_3_3` in [`Paper06_NoisyExamples/NoisyClosure.lean`](../GenLimit/Paper06_NoisyExamples/NoisyClosure.lean), transported through [`Bridges.lean`](../GenLimit/Paper19_EffectOfNoise/Bridges.lean) | Reused | The canonical proof remains with P06. P19 proves the required bridges from injective distinct-value noise and its finite-sample closure interface to the Raman--Raman interfaces. |
| Theorem 3.5 | `theorem_3_5_uniform_noise_dependent_iff_level_one` in [`SquareRoot.lean`](../GenLimit/Paper19_EffectOfNoise/SquareRoot.lean) | Full | Uniform noise-dependent generation is equivalent to fixed level one. |
| Theorem 2.16 | `Results.theorem_2_16` in [`Results/Overview.lean`](../GenLimit/Paper19_EffectOfNoise/Results/Overview.lean), delegating to `theorem_2_16` in [`Nonuniform.lean`](../GenLimit/Paper19_EffectOfNoise/Nonuniform.lean) | Full | One declaration combines the uniform and non-uniform collapse statements for every `i ≥ 1`. |
| Theorem 2.17 / Algorithm 1 | `Results.theorem_2_17` in [`Results/Overview.lean`](../GenLimit/Paper19_EffectOfNoise/Results/Overview.lean); canonical proofs in [`Separation.lean`](../GenLimit/Paper19_EffectOfNoise/Separation.lean), [`RejectedScan.lean`](../GenLimit/Paper19_EffectOfNoise/RejectedScan.lean), and [`EquivTransport.lean`](../GenLimit/Paper19_EffectOfNoise/EquivTransport.lean) | Full | The final wrapper uses the paper's literal universe `ℕ × ℕ`, exact class of nonempty column unions, and a lower-bound path retaining every rejected Algorithm 1 iteration. `Separation.lean` also provides an equivalent accepted-update compression. |
| Theorem 2.18 | `Results.theorem_2_18` in [`Results/Overview.lean`](../GenLimit/Paper19_EffectOfNoise/Results/Overview.lean); canonical equivalences in [`SquareRoot.lean`](../GenLimit/Paper19_EffectOfNoise/SquareRoot.lean) and separation in [`EquivTransport.lean`](../GenLimit/Paper19_EffectOfNoise/EquivTransport.lean) | Full | The wrapper combines the three generic uniform equivalences with an existential noiseless/noise-one separation on the exact source universe. |
| Lemma 4.1 | `lemma_4_1` in [`Nonuniform.lean`](../GenLimit/Paper19_EffectOfNoise/Nonuniform.lean) | Full | Both directions are proved. Sufficiency implements the paper's largest-eligible-layer dovetail with `Nat.findGreatest`. |
| Theorem 4.2 / non-uniform half of Theorem 2.16 | `theorem_4_2_nonuniform_finite_noise_collapse`, `theorem_2_16_nonuniform` in [`Nonuniform.lean`](../GenLimit/Paper19_EffectOfNoise/Nonuniform.lean) | Full | Every fixed positive finite noise level is equivalent to level one. |
| Lemmas 4.3--4.4, recalled from Raman--Raman | `GenLimit.NoisyExamples.lemma_3_6`, `GenLimit.NoisyExamples.lemma_3_8` in [`Paper06_NoisyExamples/Nonuniform.lean`](../GenLimit/Paper06_NoisyExamples/Nonuniform.lean), used through [`Bridges.lean`](../GenLimit/Paper19_EffectOfNoise/Bridges.lean) | Reused | The canonical earlier results are not duplicated under P19-local paper-numbered names. P19's stronger injective presentation assumptions are connected by explicit bridge theorems. |
| Lemmas 4.5--4.6 | `lemma_4_5`, `lemma_4_6` in [`Nonuniform.lean`](../GenLimit/Paper19_EffectOfNoise/Nonuniform.lean) | Full | Sufficiency reuses the stronger Raman--Raman diagonal generator; necessity follows from the level-one component and P19 Lemma 4.1. |
| Theorem 4.7 | `theorem_4_7` in [`Nonuniform.lean`](../GenLimit/Paper19_EffectOfNoise/Nonuniform.lean) | Full | Exact level-one increasing-exhaustion characterization of non-uniform noise-dependent generation. |
| Theorem 2.19 | `Results.theorem_2_19` in [`Results/Overview.lean`](../GenLimit/Paper19_EffectOfNoise/Results/Overview.lean); canonical equivalences in [`Nonuniform.lean`](../GenLimit/Paper19_EffectOfNoise/Nonuniform.lean) and separation in [`EquivTransport.lean`](../GenLimit/Paper19_EffectOfNoise/EquivTransport.lean) | Full | The wrapper combines the three generic non-uniform equivalences with an existential noiseless/noise-one separation on the exact source universe. |

## Shared infrastructure and cross-paper reuse

- Occurrence-counted and distinct-value finite contamination are kept
  separate in
  [`Core/FiniteContamination.lean`](../GenLimit/Core/FiniteContamination.lean).
  They are equivalent for injective streams, which justifies the bridge from
  P19 Definition 2.5 to P06's occurrence-counted interface.
- [`Support/FiniteContamination.lean`](../GenLimit/Support/FiniteContamination.lean)
  supplies the neutral `MissingAtMost` and injective noisy-enumeration
  packaging used by P19.
- [`Support/PrefixCompletion.lean`](../GenLimit/Support/PrefixCompletion.lean)
  supplies the finite-prefix extension used by the Lemma 3.1 adversary and
  the Theorem 2.17 separation.
- [`Support/Renaming.lean`](../GenLimit/Support/Renaming.lean) supplies the
  generic language, class, stream, and generator transport used to present
  Theorem 2.17 on the paper's literal `ℕ × ℕ` universe.
- [`Bridges.lean`](../GenLimit/Paper19_EffectOfNoise/Bridges.lean) proves exact
  finite-sample equality with the P06/Raman--Raman noisy version space and
  noisy common core, plus equivalence of the finite-dimension predicates.
- P19 depends directly on P06 for the Raman--Raman results explicitly recalled
  by the source. It has no dependency on P12.

## Remaining qualifications

There is no known mathematical gap in the conclusions of Theorems
2.16--2.19.  The remaining qualifications are representational:

1. The library does not define `NCᵢ(C)` as a literal extended-natural-valued
   maximum. Lemmas 2.13 and 3.2 instead expose exact witness-transfer and
   finiteness statements, which suffice for every downstream theorem.
2. The formalization is semantic and classical. Algorithm 1 is represented
   faithfully as a semantic scan, including rejected iterations, but is not
   packaged as extracted executable code.
3. Recalled Raman--Raman Theorem 3.4 and Lemmas 4.3--4.4 retain their
   canonical P06 declarations rather than receiving duplicate P19-local
   wrappers.

Every P19 declaration listed above is kernel-checked, and the development
contains no `sorry`, `admit`, or paper-local axioms.
