# #06 Noisy Examples map

Lean module: `GenLimit.Paper06_NoisyExamples`.
Declaration namespace retained for API compatibility: `GenLimit.NoisyExamples`.

## Pinned source

- Ananth Raman and Vinod Raman, *Generation from Noisy Examples*, ICML 2025,
  PMLR 267, pp. 51079--51093
  ([proceedings page](https://proceedings.mlr.press/v267/raman25a.html)).
- Formalization source: arXiv:2501.04179v2, dated 10 June 2025.
- Audited PDF SHA-256:
  `95c02ce2bd069b4fdf9a6b70d81763d9f9a49d65063f5141017b4474a71ad059`.
- The audited PDF is 374168 bytes and 15 pages. The source archive used in
  the audit (not redistributed here) has SHA-256
  `31d10cc890729b363a360a6d81875b587e7a8ce1a069edaab2d090328356c408`.
- The main text and Appendices A--G were checked from extracted PDF text.
  The displayed statements and proof passages newly covered here were also
  checked visually on PDF pages 6--8 and 11--13.
- audit evidence and provenance:
  [#06 audit record](../AuditRecords/Paper06_NoisyExamples/).

## Completion status

All paper-owned numbered definitions and mathematical results in the pinned
version have kernel-checked Lean counterparts. Appendix A's three noiseless
definitions and Appendix B's closure vocabulary use the neutral
`GenLimit.Generic` Core API. Appendix B's recalled learning-theory theorems
remain mapped to #02 Learning Theory rather than being duplicated; the #06
implementation itself does not import the #02 paper layer.

The paper is **COMPLETE AT THE KERNEL-CHECKED SEMANTIC LEVEL**, subject to the
source qualifications below.  The qualification is important: several
printed statements silently require an infinite or at least nonempty example
universe, and Definition D.1 conflicts with nearby prose.  Lean records the
displayed mathematics and exposes those assumptions rather than silently
strengthening the shared API.

The immutable evidence records the audited input snapshot's numbered #06 paths
and its then-current #02 aliases. For this public paper-by-paper integration,
the declarations retain the `GenLimit.NoisyExamples` namespace under the
`GenLimit.Paper06_NoisyExamples` module, while paper-independent generation, closure,
and cover definitions are owned by `GenLimit.Generic` in Core. The audit files
remain byte-for-byte unchanged so their checksums continue to identify the
actual review input; the adaptation is recorded separately in
[`record.json`](../AuditRecords/Paper06_NoisyExamples/record.json).

## Main-text correspondence

| Paper item | Lean declaration | Status |
|---|---|---|
| Assumption 2.1, UUS | `GenLimit.Generic.UUS` | Kernel checked shared definition in `GenLimit.Core.ClassGeneration`. |
| Definition 2.3, generator | `GenLimit.Generic.Generator` | Kernel checked shared definition; a length-`t` history is `Fin t -> α`. |
| Definition 2.4, finite noise | `HasFiniteNoise` | Exact finiteness of the set of negative occurrence indices. |
| Definition 2.4, fixed threshold | `IsUniformNoiseIndependentGeneratorAt` | Exact quantifier order. |
| Definition 2.4, class property | `UniformNoiseIndependentGeneratable` | Kernel checked. |
| Definition 2.5, bounded noise | `HasNoiseAtMost` | The finset records exactly the negative occurrence indices and has cardinality at most `n`. |
| Definition 2.5, uniform noise-dependent generation | `IsUniformNoiseDependentGenerator`, `UniformNoiseDependentGeneratable` | Exact order `exists G, forall n, exists d, ...`. |
| Definition 2.6, non-uniform noise-dependent generation | `IsNonuniformNoiseDependentGenerator`, `NonuniformNoiseDependentGeneratable` | The threshold may depend on noise level and target, but not the stream. |
| Definition 2.7, noisy enumeration | `NoisyPresentation` | Every positive point occurs and only finitely many stream positions are negative. |
| Definition 2.7, generation in the limit | `IsNoisyLimitGenerator`, `NoisilyGeneratableInLimit` | Kernel checked. |
| Remark 2.8, fifth setting | `IsNonuniformNoiseIndependentGenerator`, `NonuniformNoiseIndependentGeneratable` | Formalized with Appendix D. |
| Theorem 3.1, sufficiency | `infinite_commonIntersection_implies_uniform_noiseIndependent` | Fresh output from the infinite class intersection. |
| Theorem 3.1, adversary | `finite_commonIntersection_defeats_threshold` | Finite-core padding construction. |
| Theorem 3.1, necessity | `uniform_noiseIndependent_implies_infinite_commonIntersection` | Kernel checked. |
| Theorem 3.1, equivalence | `theorem_3_1` | Adds the proof's implicit `[Infinite α]`. |
| Definition 3.2, noisy version space and closure | `noisyVersionSpace`, `noisyCommonCore`, `noisyClosure` | `none` is the paper's bottom closure. |
| Definition 3.2, noisy Closure dimension | `NoisyClosureWitnessAt`, `FiniteNoisyClosureDimensionAt` | Proposition-level encoding of `NC_n(H) < ∞`. |
| Definition 3.2, distinct-sequence form | `noisyClosureWitnessAt_iff_injective_sequence` | Equivalence between finsets and injective `Fin d -> α` sequences. |
| Theorem 3.3, sufficiency | `finite_noisyClosureDimensions_imply_uniform_noiseDependent` | Largest eligible noise-level strategy. |
| Theorem 3.3, adversary | `nonfinite_noisyClosureDimension_defeats_threshold` | Pads a finite noisy core without increasing the noise budget. |
| Theorem 3.3, necessity | `uniform_noiseDependent_implies_finite_noisyClosureDimensions` | Kernel checked. |
| Theorem 3.3, equivalence | `theorem_3_3` | Adds `[Nonempty α]` to totalize the generator. |
| Corollary 3.4 | `corollary_3_4` | Includes the paper's counting bound via `noisy_witness_card_le_for_finite_class`. |
| Lemma 3.5 | `lemma_3_5` | Complete on the concrete countably infinite tagged universe used by the proof. |
| Lemma 3.5, ordinary dimension | `separation_hasClosureDimension_zero` | Proves `C(H)=0`. |
| Lemma 3.5, noisy dimension | `separation_oneNoisyWitness_every_card`, `InfiniteNoisyClosureDimensionAt` | Proves an exact witness at every cardinality, hence `NC_1(H)=∞`. |
| Lemma 3.6 | `lemma_3_6` | Nested-cover sufficiency. |
| Corollary 3.7 | `corollary_3_7` | Proves both non-uniform noisy generation and noisy generation in the limit. |
| Lemma 3.8 | `lemma_3_8` | Preserves the printed order: the cover may depend on fixed `n`. |
| Algorithm 1, exact suffix | `paperBalancedSuffixStart` | Uses the literal cardinality `⌊d_t/2⌋`; the value is zero-based, so the paper's `r_t` is one larger. |
| Algorithm 1, repeated calls | `iteratedGeneratorHistory`, `generatedCandidateSet` | Kernel checked. |
| Algorithm 1, one-history correctness | `paperRobustifiedNoiselessGenerator_correct` | Produces a positive point absent from the entire observed history. |
| Theorem 3.9, global invariant | `eventually_paperBalanced_suffix_positive_and_large` | The exact-floor suffix eventually starts after all noise and passes the noiseless threshold. |
| Theorem 3.9 | `theorem_3_9` | Full kernel-checked implication from noiseless non-uniform generation to noisy generation in the limit. |
| Theorem 3.10 | `theorem_3_10` | Finite union of uniformly noise-independent classes; adds the proof's implicit `[Infinite α]`. |

## Appendix correspondence

| Paper item | Lean declaration | Status |
|---|---|---|
| Definition A.1 | `GenLimit.Generic.IsUniformGeneratorAt`, `UniformlyGeneratable` | Shared neutral Core definition. |
| Definition A.2 | `GenLimit.Generic.IsNonuniformGenerator`, `NonuniformlyGeneratable` | Shared neutral Core definition. |
| Definition A.3 | `GenLimit.Generic.IsLimitGenerator`, `GeneratableInLimit` | Shared neutral Core definition. |
| Definition B.1 | `GenLimit.Generic.IsClosureWitness`, `HasClosureDimension`, `HasFiniteClosureDimension` | Shared neutral Core definition. |
| Theorem B.2 | `GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension` | Recalled #02 Theorem 3.3, available in the separate #02 development and not imported by #06. |
| Theorem B.3 | `GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover` | Recalled #02 Theorem 3.5, available separately and not imported by #06. |
| Theorem B.4 | `GenLimit.LiRamanTewari.finite_closure_dimension_cover_implies_generatable_in_limit` | Recalled #02 Theorem 3.10, available separately and not imported by #06. |
| Definition C.1 | `IsAlternateUniformNoiseIndependentGeneratorAt`, `AlternateUniformNoiseIndependentGeneratable` | Exact positive-distinct-sample threshold. |
| Lemma C.2 | `lemma_C_2` | Complete.  The formal proof constructs unbounded noisy-closure excess and avoids the source proof's malformed uniqueness sentence. |
| Theorem C.3, supremum condition | `BoundedNoisyClosureExcess` | Exact proposition-level meaning of `sup_n (NC_n(H)-n)<∞`. |
| Theorem C.3, sufficiency | `boundedNoisyClosureExcess_implies_alternateUniform` | Uses threshold one larger than the excess bound. |
| Theorem C.3, adversary | `noisyExcessWitness_defeats_alternate_threshold` | Finite-core padding plus an exact positive-count crossing time. |
| Theorem C.3, equivalence | `theorem_C_3` | Complete; adds `[Nonempty α]` for a total generator. |
| Definition D.1 | `IsNonuniformNoiseIndependentGenerator`, `NonuniformNoiseIndependentGeneratable` | Follows the displayed formula, which counts positive distinct examples. |
| Lemma D.2, concrete class | `evenLanguage`, `oddLanguage`, `parityClass` | The paper's even/odd class on `ℕ`. |
| Lemma D.2 | `lemma_D_2` | Complete concrete existential counterexample. |

## Source qualifications exposed by Lean

### Ambient-universe assumptions

The paper repeatedly says only that `X` is countable, while several proofs
use arbitrarily many distinct examples.  In particular:

- Theorem 3.1 is false for the empty class over a finite universe.
  `theorem_3_1` adds `[Infinite α]`.
- Theorem 3.3 and Theorem C.3 need `[Nonempty α]` because a generator is a
  total map into `α`, even when the class is empty.
- Lemma 3.5 and Lemma D.2 are not true as existential statements on every
  finite countable universe.  Their proofs respectively set `X` to a
  prime/power universe and to `ℕ`.  Lean states both results on concrete
  countably infinite universes.  The tagged `SeparationPoint` construction is
  isomorphic to the prime/negative-prime-power construction and avoids
  irrelevant unique-factorization obligations.
- Theorem 3.10 similarly exposes `[Infinite α]`.

### Definition D.1 conflict

The displayed Definition D.1 uses
`|{x_1,...,x_t} ∩ supp(h)| = d*`, so it counts distinct positive examples.
The sentence at the bottom of PDF page 11 says instead that D.1 measures all
distinct examples.  The displayed formula and the proof of Lemma D.2 agree
with each other; Lean follows them and records the prose sentence as false.

The sentence introducing Theorem C.3 also calls its target “Definition D.1.”
The theorem is in Appendix C and characterizes the uniform property in
Definition C.1; Lean uses C.1.

### Proof details completed formally

- Algorithm 1's proof chooses one time `s*` and then immediately treats its
  suffix conditions as valid for every `s ≥ s*`.  Lean proves the missing
  persistence argument: prefix cardinality is monotone, the latest
  exact-floor suffix starts after the last noisy occurrence, and its
  cardinality remains at least the noiseless threshold.
- Theorem 3.3's displayed algorithm uses zero both as a genuine noise level
  and as the sentinel “no eligible level.”  Lean branches on emptiness before
  taking the maximum.
- Lemma C.2's prose claims there is “exactly one time point” while displaying
  a fixed final-prefix set rather than the varying prefix.  The Lean proof
  uses a general one-step crossing lemma for positive-sample cardinality, so
  no uniqueness claim is needed.
- Theorem C.3's extended-natural supremum is not represented by assigning a
  fake natural value to `NC_n`.  `BoundedNoisyClosureExcess` quantifies over
  every finite-core witness and is exactly the bound the proof uses.
- Theorem 3.10's formal proof passes beyond the finite set of negative values
  before concluding that a winning component emits a positive point.

## Verification

The paper-facing entry point imports:

```text
GenLimit.Paper06_NoisyExamples.UniformIndependent
GenLimit.Paper06_NoisyExamples.NoisyClosure
GenLimit.Paper06_NoisyExamples.NonuniformDefinitions
GenLimit.Paper06_NoisyExamples.FiniteClasses
GenLimit.Paper06_NoisyExamples.Nonuniform
GenLimit.Paper06_NoisyExamples.NoiselessRobustification
GenLimit.Paper06_NoisyExamples.FiniteUnionLimit
GenLimit.Paper06_NoisyExamples.Separation
GenLimit.Paper06_NoisyExamples.AlternatePositive
GenLimit.Paper06_NoisyExamples.NonuniformIndependent
```

Focused verification:

- `lake build GenLimit.Paper06_NoisyExamples` checks the paper-facing umbrella.
- No `sorry`, `admit`, or project-defined axioms occur in the noisy-example
  modules.
- The new public theorems use only the project's accepted logical
  dependencies (`propext`, `Classical.choice`, and `Quot.sound`).

The preserved ChatGPT Pro check and pending human-review status live in the
[#06 audit record](../AuditRecords/Paper06_NoisyExamples/) and the
[authoritative human-audit ledger](../AuditRecords/Human/README.md).
