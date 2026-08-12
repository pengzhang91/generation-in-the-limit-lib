# #02 Learning Theory map

Lean module: `GenLimit.Paper02_LearningTheory`.
Declaration namespace retained for API compatibility:
`GenLimit.LiRamanTewari`.

Source: Jiaxun Li, Vinod Raman, and Ambuj Tewari, *Generation through the
Lens of Learning Theory*.

- arXiv source pin: [`arXiv:2410.13714v5`](https://arxiv.org/abs/2410.13714v5),
  dated 27 December 2024;
- conference version: *Proceedings of the 38th Conference on Learning Theory*
  (COLT 2025), PMLR 291, pp. 4740--4776;
- rendered arXiv-v5 PDF used for the page-level review: SHA-256
  `acaf59abdb4542173cb20dd05e874f7fa5b505bf7b2c5c561529d5e387502482`;
- audit-workspace source archive used for the initial correspondence review
  (not redistributed here): `2410.13714.tar.gz`, SHA-256
  `c825451f916189107db7dfc917cd28832720b5a5bb97e9b217317958343a655b`;
- principal file inside that archive: `main.tex`, SHA-256
  `a516d186a55e4ecb1b518fdd02f93df771354c0e5fde998c0e9ff4b86e58ab98`;
- prompted-section file inside that archive: `extensions.tex`,
  SHA-256
  `fcb16c9ddd8b7870b4d179ade52ae90ebecb8ce9031b2434daaf66d27881ced6`.
- audit evidence and provenance:
  [#02 audit record](../AuditRecords/Paper02_LearningTheory/).

The native #02 development currently formalizes the paper-facing generation notions,
their implication hierarchy, the closure-dimension definitions, both
necessity and sufficiency lemmas, and the full uniform-generation
characterization in Theorem 3.3. Definition 2.3's generator-specific sample
complexity is represented literally in `WithTop Nat`, with its least-value
API; the quantitative argument following Theorem 3.3 proves that the optimal
value lies between `C(H)` and `C(H) + 1`. It also formalizes the non-decreasing-cover
characterization of non-uniform generation in Theorem 3.5, including Lemmas
3.7--3.8 and the countable-class consequence in Corollary 3.6. The Section 3
results now also expose `proposition_2_1`, `theorem_2_4`, and `theorem_2_5`:
the first packages the two strict hierarchy separations proved later in
Section 3, while the other two are the source-facing countable-class and
finite-class conclusions obtained from the stronger Section 3
characterizations. Other Section 3 examples in Lemmas 3.4,
3.9, and 3.12, the finite-cone Corollary 3.11, the
finite-closure-dimension cover condition in Theorem 3.10, and the finite-union
counterexample in Lemma 4.2 now compile as well. The staged
countable-union lower bound in Lemma 4.3 is complete on an isomorphic tagged
version of the source's prime-ratio incidence structure. Section 5's prompted
definitions, Theorems 5.1--5.2, Corollary 5.3, Lemma 5.4, and Corollary 5.5
compile. In Appendix C, Definition C.1, Lemma C.1, and Theorems C.2 and C.4
compile. A separate diagnostic disproves the false arbitrary-stream
"equivalent representation" asserted in the prose before C.2; the repaired
C.2 proof does not use it, and the C.4 proof applies literal EUC only to a
target-containing cover component. Theorem 4.1's six Appendix A constructions also
compile at the exact VC/Littlestone combinatorial-characterization boundary.
They are deliberately named `..._combinatorial_core`: the literal
probability-space/PAC-algorithm and online-regret definitions, and the
external theorems equating them with finite VC/Littlestone dimension, remain
outside the current Lean boundary.

The cross-paper layer now additionally reuses the existing Gold, Angluin, and
KM developments instead of restating their mathematics inside #02. It gives
the literal language-valued identifier interface of Definitions 2.6--2.7,
Theorem 2.2, and Theorem 2.3 with Angluin's indexed-family/countability
hypothesis restored, together with adapters between the original `Nat` API,
generic classes, and indexed families. A separate bridge diagnostic proves
that P02's printed arbitrary-class version of Theorem 2.3 is false: an
uncountable UUS inclusion antichain has empty tell-tales but cannot be the
range identified by a language-valued finite-history identifier over a
countable example space.

## Current theorem entry points

- `GenLimit.LiRamanTewari.uniform_implies_nonuniform`;
- `GenLimit.LiRamanTewari.nonuniform_implies_limit`;
- `GenLimit.LiRamanTewari.uniform_implies_limit`;
- `GenLimit.LiRamanTewari.GenerationHierarchyStrictOn`;
- `GenLimit.LiRamanTewari.proposition_2_1`;
- `GenLimit.LiRamanTewari.closure_dimension_necessity`;
- `GenLimit.LiRamanTewari.closure_dimension_sufficiency`;
- `GenLimit.LiRamanTewari.finite_closure_dimension_implies_uniform`;
- `GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension`;
- `GenLimit.LiRamanTewari.uniformGenerationSampleComplexity`;
- `GenLimit.LiRamanTewari.optimalUniformGenerationSampleComplexity`;
- `GenLimit.LiRamanTewari.closure_dimension_le_uniformGenerationSampleComplexity`;
- `GenLimit.LiRamanTewari.optimal_uniform_generation_sample_complexity_bounds`;
- `GenLimit.LiRamanTewari.nonuniform_characterization_necessity`;
- `GenLimit.LiRamanTewari.nonuniform_characterization_sufficiency`;
- `GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover`;
- `GenLimit.LiRamanTewari.countable_classes_are_nonuniformly_generatable`;
- `GenLimit.LiRamanTewari.theorem_2_4`;
- `GenLimit.LiRamanTewari.theorem_2_5`;
- `GenLimit.LiRamanTewari.finite_closure_dimension_cover_implies_generatable_in_limit`;
- `GenLimit.LiRamanTewari.exists_uncountable_uniformly_generatable_class`;
- `GenLimit.LiRamanTewari.exists_countable_nonuniform_not_uniform_class`;
- `GenLimit.LiRamanTewari.finite_union_of_paper_cone_classes_generatable_in_limit`;
- `GenLimit.LiRamanTewari.exists_generatable_in_limit_not_nonuniformly_generatable`;
- `GenLimit.LiRamanTewari.exists_two_zero_closure_classes_union_not_nonuniform`;
- `GenLimit.LiRamanTewari.exists_countable_sequence_zero_closure_union_not_limit`;
- `GenLimit.LiRamanTewari.theorem_4_1_i_combinatorial_core`;
- `GenLimit.LiRamanTewari.theorem_4_1_ii_combinatorial_core`;
- `GenLimit.LiRamanTewari.theorem_4_1_iii_combinatorial_core`;
- `GenLimit.LiRamanTewari.theorem_4_1_iv_combinatorial_core`;
- `GenLimit.LiRamanTewari.theorem_4_1_v_combinatorial_core`;
- `GenLimit.LiRamanTewari.theorem_4_1_vi_combinatorial_core`;
- `GenLimit.LiRamanTewari.theorem_4_1_combinatorial_core`;
- `GenLimit.LiRamanTewari.prompted_uniform_generatability_iff_finite_prompted_closure_dimension`;
- `GenLimit.LiRamanTewari.prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover`;
- `GenLimit.LiRamanTewari.finite_prompt_classes_are_uniformly_generatable`;
- `GenLimit.LiRamanTewari.countable_prompt_classes_are_nonuniformly_generatable`;
- `GenLimit.LiRamanTewari.countable_prompt_classes_are_generatable_in_limit`;
- `GenLimit.LiRamanTewari.exists_finite_prompt_class_not_uniformly_generatable`;
- `GenLimit.LiRamanTewari.exists_finite_prompt_class_not_nonuniformly_generatable`;
- `GenLimit.LiRamanTewari.EventuallyUnboundedClosure`;
- `GenLimit.LiRamanTewari.exists_nonuniformly_generatable_not_eventuallyUnboundedClosure`;
- `GenLimit.LiRamanTewari.theorem_C2_finite_eventually_unbounded_closure_cover`;
- `GenLimit.LiRamanTewari.theorem_C4_eventually_unbounded_closure`.

Cross-paper entry points are kept out of the independent #02 umbrella:

- `GenLimit.GoldP02Separation.theorem_2_2_countable_uus_not_identifiable`;
- `GenLimit.Angluin.theorem_2_3_countable`;
- `GenLimit.Angluin.extensionallyIdentifiable_implies_countable`;
- `GenLimit.Paper02IdentificationDiagnostics.printed_theorem_2_3_is_false`;
- `GenLimit.Gold.semanticallyIdentifiable_iff_paper02ExtensionallyIdentifiable`;
- `GenLimit.KM.SetInterface.range_generatableInLimit`;
- `GenLimit.KM.SetInterface.range_nonuniformlyGeneratable_via_paper02`;
- `GenLimit.LiRamanTewari.finite_closure_dimension_cover_implies_generatable_via_euc`.

`uniform_generatability_iff_finite_closure_dimension` is the paper-level
equivalence in Theorem 3.3. Its two directions are retained as separately
named Lean declarations matching Lemmas 3.1 and 3.2. The corresponding
non-uniform equivalence in Theorem 3.5 and its two supporting lemmas are also
separately exposed.

## Representation and indexing conventions

The paper presents a binary hypothesis `h : X -> {0,1}` through its positive
support. Lean therefore represents a hypothesis extensionally by a language
`Set alpha` and a hypothesis class by a possibly uncountable set of such
languages:

| Paper object | Lean representation |
|---|---|
| Example space `X` | A type `alpha` |
| Positive support `supp(h)` | `GenLimit.Generic.Language alpha`, definitionally `Set alpha` |
| Binary hypothesis class `H` | `GenLimit.Generic.LanguageClass alpha`, definitionally `Set (Set alpha)` |
| Infinite positive stream | `GenLimit.Generic.Stream alpha`, definitionally `Nat -> alpha` |
| Finite sequence in `X*` | `Fin t -> alpha` for its length `t` |
| Generator `G : X* -> X` | `GenLimit.Generic.Generator alpha := forall t, (Fin t -> alpha) -> alpha` |
| Distinct observations in a history | `GenLimit.Generic.sequenceSample` or `GenLimit.Generic.sample` |
| Exact enumeration of a support | `GenLimit.Generic.Presents stream L` |
| Arbitrary positive sequence | `GenLimit.Generic.StreamIn stream L` |

Lean time is zero-based. A Lean history of length `t` contains positions
`i : Fin t`, corresponding to the paper values `x_1, ..., x_t`. Thus
`Generic.sample stream t` contains exactly `stream i` for `i < t`, and
`Generic.output G stream t` runs `G` after those `t` observations. Lean also
defines the harmless empty-history round `t = 0`; the paper writes its rounds
starting at one.

The use of supports rather than Boolean-valued functions is extensional: all
generation, shattering, and closure statements in the formalized portion
depend only on positive supports. `Prediction.lean` encodes the exact
sequence-shattering and complete-binary-tree combinatorics of Definitions
2.9 and 2.11--2.12. Its explicitly named PAC/online proxies do not encode
Definition 2.8's probability distributions or Definition 2.10's algorithms,
losses, and sublinear regret.

## Definition and theorem correspondence

The table uses the stable source labels from arXiv v5 where possible, rather
than relying only on displayed numbering. Here “Complete” is scoped to the
stated deterministic, extensional Lean interface. It does not promote the
VC/Littlestone proxies to literal PAC or online-learning algorithms or supply
computational efficiency. Identification items live in `GenLimit.Bridges`, so
importing the native #02 umbrella does not pull in Gold or Angluin.

| Paper item | Lean declaration | Module | Status |
|---|---|---|---|
| Uniformly Unbounded Support assumption | `UUS` | `GenLimit.Paper02_LearningTheory.Definitions` | Complete |
| Positive version space `H(x_1,...,x_t)` | `versionSpace` | `GenLimit.Paper02_LearningTheory.Definitions` | Complete |
| Closure `\langle x_1,...,x_t\rangle_H`, including the `bottom` case | `commonCore`, `closure` | `GenLimit.Paper02_LearningTheory.Definitions` | Complete; `Option.none` represents `bottom` |
| Generator, `def:generator` | `GenLimit.Generic.Generator` | `GenLimit.Core.GenericGeneration` | Complete |
| Generatability in the limit, `def:geninlim` | `IsLimitGenerator`, `GeneratableInLimit` | `GenLimit.Paper02_LearningTheory.Definitions` | Complete |
| Identifier, Definition 2.6 | `GenLimit.Angluin.ExtensionalIdentifier` | `GenLimit.Bridges.AngluinToPaper02` | Complete as the literal language-valued finite-history interface |
| Identifiability in the limit, Definition 2.7 | `ExtensionalIdentifies`, `ExtensionallyIdentifiable` | `GenLimit.Bridges.AngluinToPaper02` | Complete as exact extensional stabilization on every positive presentation |
| Theorem 2.2 | `GenLimit.GoldP02Separation.theorem_2_2_countable_uus_not_identifiable` | `GenLimit.Bridges.GoldToPaper02` | Complete; reuses the existing co-singleton Gold/KM separation witness |
| Theorem 2.3 with Angluin's indexed-family/countability hypothesis restored | `theorem_2_3_countable` | `GenLimit.Bridges.AngluinToPaper02` | Complete at the paper's semantic, language-valued identifier interface |
| Printed arbitrary-class Theorem 2.3 | `printed_theorem_2_3_is_false` | `GenLimit.Bridges.Paper02IdentificationDiagnostics` | Refuted: an uncountable UUS selector antichain has empty tell-tales but is not extensionally identifiable |
| Uniform generatability, `def:unifgen` | `IsUniformGeneratorAt`, `UniformlyGeneratable` | `GenLimit.Paper02_LearningTheory.Definitions` | Complete |
| Uniform generation sample complexity, Definition 2.3 | `uniformGenerationSampleComplexity`, `uniformGenerationSampleComplexity_eq_top_iff`, `uniformGenerationSampleComplexity_le_coe_iff`, `uniformGenerationSampleComplexity_eq_coe_iff` | `GenLimit.Paper02_LearningTheory.UniformSampleComplexity` | Complete as the literal least value in `WithTop Nat` |
| Optimal uniform generation sample complexity | `optimalUniformGenerationSampleComplexity`, `optimalUniformGenerationSampleComplexity_eq_top_iff`, `optimalUniformGenerationSampleComplexity_le_coe_iff` | `GenLimit.Paper02_LearningTheory.UniformSampleComplexity` | Complete as the least threshold attained by any generator, or `top` |
| Non-uniform generatability, `def:generability` | `IsNonuniformGenerator`, `NonuniformlyGeneratable` | `GenLimit.Paper02_LearningTheory.Definitions` | Complete |
| Displayed hierarchy `uniform => non-uniform => in-limit` | `uniform_implies_nonuniform`, `nonuniform_implies_limit`, `uniform_implies_limit` | `GenLimit.Paper02_LearningTheory.Hierarchy` | Complete |
| Proposition 2.1, strictness of both hierarchy implications | `GenerationHierarchyStrictOn`, `proposition_2_1` | `GenLimit.Paper02_LearningTheory.Hierarchy`, `GenLimit.Paper02_LearningTheory` | Complete on one existentially quantified countably infinite example type; the tagged `BlockUniverse` implementation is hidden in the proof, and the second clause instantiates the generic Lemma 3.12 construction on its two infinite tails |
| Closure witness in Definition `def:gem` | `IsClosureWitness` | `GenLimit.Paper02_LearningTheory.Closure` | Complete |
| Finite closure dimension `C(H) = d` | `ClosureDimensionAtMost`, `HasClosureDimension` | `GenLimit.Paper02_LearningTheory.Closure` | Complete as a relational encoding |
| Statement `C(H) < infinity` | `HasFiniteClosureDimension` | `GenLimit.Paper02_LearningTheory.Closure` | Complete |
| Statement `C(H) = infinity` | `HasInfiniteClosureDimension` | `GenLimit.Paper02_LearningTheory.Closure` | Complete as arbitrarily large finite closure witnesses |
| Restriction of an arbitrarily large witness to exact size `d` | `closure_witness_mono`, `exists_closure_witness_card_eq` | `GenLimit.Paper02_LearningTheory.Closure` | Complete |
| Quantitative witness obstruction underlying Lemma 3.1 | `closure_witness_defeats_uniform_threshold`, `closure_dimension_le_uniform_threshold`, `closure_dimension_le_uniformGenerationSampleComplexity` | `GenLimit.Paper02_LearningTheory.Closure`, `GenLimit.Paper02_LearningTheory.UniformSampleComplexity` | Complete; every generator-specific complexity is at least `C(H)` |
| Necessity Lemma 3.1, `lem:closnec` | `closure_dimension_necessity` | `GenLimit.Paper02_LearningTheory.Closure` | Complete |
| Infinite common core after more than `d` distinct consistent observations | `core_diff_sample_infinite` | `GenLimit.Paper02_LearningTheory.Closure` | Complete |
| Generator in Lemma 3.2, `lem:clossuff` | `closureGenerator`, `closureGenerator_spec` | `GenLimit.Paper02_LearningTheory.Closure` | Complete, with the construction choice documented below |
| Sufficiency Lemma 3.2, `lem:clossuff` | `closureGenerator_isUniformGeneratorAt`, `closure_dimension_sufficiency` | `GenLimit.Paper02_LearningTheory.Closure` | Complete; the named generator and existential wrapper are both exposed |
| `(C(H) < infinity) => uniformly generatable`, forward direction of Theorem 3.3, `thm:unifgen` | `finite_closure_dimension_implies_uniform` | `GenLimit.Paper02_LearningTheory.Closure` | Complete |
| Complementarity of finite and infinite dimension | `finite_closure_dimension_iff_not_infinite` | `GenLimit.Paper02_LearningTheory.Closure` | Complete; internal bridge between the relational encodings |
| Theorem 3.3, `thm:unifgen` | `uniform_generatability_iff_finite_closure_dimension` | `GenLimit.Paper02_LearningTheory.Closure` | Complete |
| Quantitative conclusion following Theorem 3.3 | `closureGenerator_uniformGenerationSampleComplexity_le`, `optimal_uniform_generation_sample_complexity_bounds` | `GenLimit.Paper02_LearningTheory.UniformSampleComplexity` | Complete; if `C(H) = d`, the optimal value lies in the exact interval `[d, d + 1]` |
| Non-decreasing union cover `H_1 subset H_2 subset ...`, `H = union_n H_n` | `IsNondecreasingCover` | `GenLimit.Core.ClassCovers` (paper-facing alias in `GenLimit.Paper02_LearningTheory.Definitions`) | Complete |
| Necessity Lemma 3.7 in Theorem 3.5 | `nonuniform_characterization_necessity` | `GenLimit.Paper02_LearningTheory.NonuniformCharacterization` | Complete; the least language-dependent threshold is selected with `Nat.find` |
| Sufficiency Lemma 3.8 in Theorem 3.5 | `nonuniform_characterization_sufficiency` | `GenLimit.Paper02_LearningTheory.NonuniformCharacterization` | Complete; finite maximum normalization documented below |
| Theorem 3.5, `thm:nonunifgen` | `nonuniform_generatability_iff_nondecreasing_finite_closure_cover` | `GenLimit.Paper02_LearningTheory.NonuniformCharacterization` | Complete |
| Finite classes have finite closure dimension | `finite_language_class_has_finite_closure_dimension` | `GenLimit.Paper02_LearningTheory.NonuniformCharacterization` | Complete; supporting fact for Corollary 3.6 |
| Corollary 3.6, countable classes are non-uniformly generatable | `countable_classes_are_nonuniformly_generatable` | `GenLimit.Paper02_LearningTheory.NonuniformCharacterization` | Complete, including empty and finite classes |
| Theorem 2.4, every countable UUS class is generatable in the limit | `theorem_2_4` | `GenLimit.Paper02_LearningTheory` | Source-facing wrapper; derived from the stronger Corollary 3.6 conclusion and `nonuniform_implies_limit` |
| Theorem 2.5, every finite UUS class is uniformly generatable | `theorem_2_5` | `GenLimit.Paper02_LearningTheory` | Source-facing wrapper; factors through the finite-class closure bound and Theorem 3.3 |
| Finite cover by finite-closure-dimension classes | `IsFiniteCover` | `GenLimit.Core.ClassCovers` (paper-facing alias in `GenLimit.Paper02_LearningTheory.Definitions`) | Complete |
| Theorem 3.10, `thm:geninlim` | `finite_closure_dimension_cover_implies_generatable_in_limit` | `GenLimit.Paper02_LearningTheory.GenerationInLimitCharacterization` | Complete; frozen common cores and maximal-prefix progress follow the source proof |
| Theorem 3.10 factored through Appendix C.2 | `finite_closure_dimension_cover_implies_generatable_via_euc` | `GenLimit.Paper02_LearningTheory.Relationships` | Complete; records the implication between the two sufficient conditions while retaining both source-facing proofs |
| Lemma 3.4, `lem:uncountunifgen` | `exists_uncountable_uniformly_generatable_class` | `GenLimit.Paper02_LearningTheory.EarlierSectionThreeExamples` | Complete at statement and construction level; uses the paper's integer upward cone and proves genuine set-theoretic uncountability |
| Lemma 3.9, `lem:nonunifvsunifgen` | `exists_countable_nonuniform_not_uniform_class` | `GenLimit.Paper02_LearningTheory.EarlierSectionThreeExamples` | Complete at theorem-statement level; uses the source's stated disjoint-block abstraction rather than its literal triangular-integer encoding |
| Upward cone `{S union A : A subseteq X}` | `upwardCone`, `upwardCone_eq_union_class` | `GenLimit.Paper02_LearningTheory.FiniteConeCover` | Complete |
| Corollary 3.11, finite unions of infinite upward cones | `finite_union_of_paper_cone_classes_generatable_in_limit` | `GenLimit.Paper02_LearningTheory.FiniteConeCover` | Complete; exact `Nat`-universe wrapper for the displayed class |
| Lemma 3.12, `lem:notnonunifgen` | `exists_generatable_in_limit_not_nonuniformly_generatable` | `GenLimit.Paper02_LearningTheory.LimitVsNonuniformSeparation` | Complete; same positive/nonpositive integer class and paper-level conclusion |
| Lemma 4.2, `lem:nonunifclos` | `exists_two_zero_closure_classes_union_not_nonuniform` | `GenLimit.Paper02_LearningTheory.LimitVsNonuniformSeparation` | Complete; the two component classes have closure dimension zero and their union is the Lemma 3.12 class |
| Lemma 4.3, `lem:hardgeninlim` | `exists_countable_sequence_zero_closure_union_not_limit` | `GenLimit.Paper02_LearningTheory.CountableUnionSeparation` | Complete; explicit staged exact-presentation diagonal on a tagged countable incidence structure isomorphic to the source's prime-ratio construction |
| Definition 2.9, sequence VC shattering and finite/infinite VC dimension | `VCShatters`, `HasFiniteVCDimension`, `HasInfiniteVCDimension` | `GenLimit.Paper02_LearningTheory.Prediction` | Complete combinatorial definitions |
| Definitions 2.11--2.12, complete binary Littlestone trees and finite/infinite dimension | `LittlestoneTree`, `LittlestoneShattered`, `HasFiniteLittlestoneDimension`, `HasInfiniteLittlestoneDimension` | `GenLimit.Paper02_LearningTheory.Prediction` | Complete combinatorial definitions |
| Definition 2.8 characterization proxy | `PACLearnableViaVC` | `GenLimit.Paper02_LearningTheory.Prediction` | Explicitly a finite-VC proxy, not the literal probabilistic learner definition |
| Definition 2.10 characterization proxy | `OnlineLearnableViaLittlestone` | `GenLimit.Paper02_LearningTheory.Prediction` | Explicitly a finite-Littlestone proxy, not the literal algorithm/regret definition |
| Theorem 4.1(i)--(vi), Appendix A constructions | `theorem_4_1_i_combinatorial_core` through `theorem_4_1_vi_combinatorial_core` | `GenLimit.Paper02_LearningTheory.Prediction` | All six existential regions complete at the cited VC/Littlestone characterization boundary |
| Six-way Theorem 4.1 package | `theorem_4_1_combinatorial_core` | `GenLimit.Paper02_LearningTheory.Prediction` | Complete combinatorial package; intentionally not named as the literal PAC/online theorem |
| Multiclass hypotheses and prompt supports | `MulticlassHypothesis`, `MulticlassHypothesisClass`, `promptSupport` | `GenLimit.Paper02_LearningTheory.PromptedDefinitions` | Complete |
| Prompted UUS assumption (PUUS), Assumption 2 | `PUUS` | `GenLimit.Paper02_LearningTheory.PromptedDefinitions` | Complete |
| Prompted generator and current-tuple history, Definition 5.1 | `PromptedObservation`, `PromptedGenerator`, `promptedHistory` | `GenLimit.Paper02_LearningTheory.PromptedDefinitions` | Complete; the generator sees the current tuple exactly as printed |
| Prompted uniform generation, Definition 5.2 | `PromptedCorrectAt`, `IsPromptedUniformGeneratorAt`, `PromptedUniformlyGeneratable` | `GenLimit.Paper02_LearningTheory.PromptedDefinitions` | Complete |
| Prompted non-uniform generation, Definition 5.3 | `IsPromptedNonuniformGenerator`, `PromptedNonuniformlyGeneratable` | `GenLimit.Paper02_LearningTheory.PromptedDefinitions` | Complete |
| Prompted generation in the limit, Definition 5.4 | `PromptSupportPresented`, `IsPromptedLimitGenerator`, `PromptedGeneratableInLimit` | `GenLimit.Paper02_LearningTheory.PromptedDefinitions` | Complete |
| Prompted version space, closure, and closure dimension, Definition 5.5 | `promptedVersionSpace`, `promptedCommonCore`, `promptedClosure`, `HasPromptedClosureDimension` | `GenLimit.Paper02_LearningTheory.PromptedDefinitions`, `GenLimit.Paper02_LearningTheory.PromptedClosure` | Complete; `Option.none` represents bottom |
| Theorem 5.1 | `prompted_uniform_generatability_iff_finite_prompted_closure_dimension` | `GenLimit.Paper02_LearningTheory.PromptedClosure` | Complete; necessity and sufficiency are separately exposed and preserve the `PC(H)+1` upper threshold |
| Theorem 5.2 | `prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover` | `GenLimit.Paper02_LearningTheory.PromptedNonuniform` | Complete; necessity and sufficiency are separately exposed |
| Prompted hierarchy | `prompted_uniform_implies_nonuniform`, `prompted_nonuniform_implies_limit`, `prompted_uniform_implies_limit` | `GenLimit.Paper02_LearningTheory.PromptedNonuniform` | Complete |
| Corollary 5.3(i) | `finite_prompt_classes_are_uniformly_generatable` | `GenLimit.Paper02_LearningTheory.PromptedNonuniform` | Complete; proved directly from finite prompt space, without the source's unjustified equality of thresholds |
| Corollary 5.3(ii)--(iii) | `countable_prompt_classes_are_nonuniformly_generatable`, `countable_prompt_classes_are_generatable_in_limit` | `GenLimit.Paper02_LearningTheory.PromptedNonuniform` | Complete |
| Lemma 5.4 | `exists_finite_prompt_class_not_uniformly_generatable` | `GenLimit.Paper02_LearningTheory.PromptedInfinitePromptExample` | Complete; tagged realization of the source's finite two-hypothesis construction |
| Corollary 5.5 | `exists_finite_prompt_class_not_nonuniformly_generatable` | `GenLimit.Paper02_LearningTheory.PromptedInfinitePromptExample` | Complete |
| Eventually Unbounded Closure, Definition C.1 | `EventuallyUnboundedClosure` | `GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosure` | Complete; quantifies over every target language and each exact presentation as in the source |
| Lemma C.1, `lem:stillnotnec` | `exists_nonuniformly_generatable_not_eventuallyUnboundedClosure` | `GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosure` | Complete at existential-statement level; uses an alternate cofinite-language witness rather than the source's prime-power finite-bit-string witness |
| False streamwise "equivalent representation" before C.2 | `printed_EUC_equivalence_is_false` | `GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosureDiagnostics` | Disproved by an explicit spine/tails class satisfying Definition C.1 |
| Repaired generator for Theorem C.2 | `finiteEUCUnionGenerator` | `GenLimit.Paper02_LearningTheory.FiniteEUCUnion` | Complete; freezes the first actually infinite core of each activated component |
| Theorem C.2, `thm:weaksuff` | `theorem_C2_finite_eventually_unbounded_closure_cover` | `GenLimit.Paper02_LearningTheory.FiniteEUCUnion` | Complete with the literal finite-cover, EUC, countability, and UUS hypotheses; does not use the false prose equivalence |
| Algorithm 1 / maximum eligible cover index in Theorem C.4 | `eventuallyUnboundedCoverGenerator` | `GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosure` | Complete as a classical Lean construction |
| Theorem C.4, `thm:altweaksuff` | `theorem_C4_eventually_unbounded_closure` | `GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosure` | Complete; preserves the paper-facing countability, UUS, non-decreasing-cover, and EUC hypotheses |

## Quantifier correspondence

The three main predicates preserve the paper's change in threshold
dependence:

```text
in-limit:   exists G, forall L, forall enumeration, exists T, ...
non-uniform: exists G, forall L, exists d, forall positive stream, ...
uniform:     exists G, exists d, forall L, forall positive stream, ...
```

For uniform and non-uniform generation, the paper says that if a time
`t*` with exactly `d` distinct observations exists, generation must be
correct thereafter. `IsUniformGeneratorAt` and `IsNonuniformGenerator`
quantify over every time `t` at which the sample cardinality equals `d`.
This is the universal reading used by the paper's own negation argument. It
also removes any ambiguity when a repeated stream leaves the cardinality
equal to `d` over several consecutive times.

`nonuniform_implies_limit` uses UUS to show that an exact enumeration reaches
every prescribed finite number of distinct observations. This is isolated in
the paper-independent theorem
`GenLimit.Generic.exists_sample_card_eq_of_presents_infinite`.

## Closure-dimension encoding

The paper treats `C(H)` as an element of `Nat union {infinity}`. Lean avoids a
separate extended-natural-valued definition:

- `ClosureDimensionAtMost H d` says that every consistent finite sample with
  cardinality strictly greater than `d` has infinite common core;
- `HasClosureDimension H d` adds a witness of cardinality `d`, except when
  `d = 0`;
- in the zero case, `ClosureDimensionAtMost H 0` implements the paper's
  convention that no singleton sample has finite non-bottom closure;
- `HasFiniteClosureDimension H` existentially packages the finite value.

This relational interface is sufficient for closure-dimension theorem
statements and avoids choosing an arbitrary value when the dimension is
infinite. The extended numeric closure dimension itself is not defined.
Generator sample complexity, by contrast, is represented literally:
`uniformGenerationSampleComplexity G H : WithTop Nat` is the least valid
threshold for `G`, and `optimalUniformGenerationSampleComplexity H` is the
least threshold attained by any generator. Their `eq_top`, `le_coe`, and
exact-minimum theorems expose the expected extended-natural semantics.

If `HasClosureDimension H d`, the finite witness adversary proves

```text
d <= uniformGenerationSampleComplexity G H
```

for every generator `G`. The closure generator supplies the matching
one-step upper bound, so

```text
d <= optimalUniformGenerationSampleComplexity H <= d + 1.
```

This is the exact result behind the paper's asymptotic prose. Lean does not
assert the generally stronger equality with `d`, and it leaves the
zero-dimension edge case explicit.

## Construction and access-model boundary

`closureGenerator` is classical and noncomputable. After more than `d`
distinct observations with a nonempty version space, it chooses a fresh point
from the current infinite common core. Otherwise it returns an arbitrary
fallback point.

The prose proof of Lemma 3.2 (`lem:clossuff`) first describes freezing the
common core seen when the `(d + 1)`st distinct point arrives. Lean instead
recomputes the current closure on every later history. This is the equivalent
per-round variant described in the paper's subsequent max-min-oracle remark:
each later consistent sample still has cardinality greater than `d`, so its
common core is infinite and is contained in the selected target.

The paper assumes a countable example space. The main Lean sufficiency
theorems retain `[Countable alpha]`, although the set-theoretic construction
does not use countability. Lean also states `[Nonempty alpha]` to make the
arbitrary fallback output well-defined. This makes explicit the paper's
implicit nonempty-example-space convention.

No ERM oracle, max-min oracle, finite-query implementation, or complexity
claim is included. The current construction uses `Classical.choice` directly.

## Non-uniform cover construction and finite maximum

Lemma 3.7 is formalized in the paper's order. From a non-uniform generator
`G`, Lean selects the least valid threshold `d_L` for each `L in H` and sets
`H_n = {L in H | d_L <= n}`. These classes are non-decreasing and their union
is `H`. Showing that the same `G` is uniform on `H_n` requires one detail that
is implicit in the prose proof: if a finite history contains `n` distinct
examples and `d_L <= n`, then an earlier prefix contained exactly `d_L`
distinct examples. The shared lemma
`GenLimit.Generic.eventualAtExactSize_mono` proves this even for streams with
repetitions.

Lemma 3.8 follows the paper's maximum-eligible-index reduction, with a
normalization needed to make the displayed maximum formally well-defined.
After choosing a uniform generator `G_n` and a valid threshold `d_n` for each
class `H_n`, Lean replaces `d_n` by the still-valid upper bound

```text
tilde d_n = max(n, d_n).
```

After `k` distinct examples, it considers

```text
E_k = {n <= k | tilde d_n <= k}
```

and, when nonempty, runs `G_q` for `q = max E_k`. This set is a `Finset`, so
the maximum genuinely exists. If the target lies in `H_n` and at least
`tilde d_n` distinct examples have appeared, then `n in E_k`, hence `q >= n`.
Monotonicity puts the target in `H_q`, while `d_q <= tilde d_q <= k` lets the
finite-prefix intermediate-value lemma invoke the uniform guarantee for
`G_q`.

This padding addresses a gap in the displayed first case of the prose proof:
`sup_n d_n = infinity` alone does not imply that every sublevel set
`{n | d_n <= k}` is finite. For example, an unbounded sequence can alternate
the value `1` with an increasing sequence. The paper's Remark 3.3 permits
replacing sample complexities by upper bounds; `max(n,d_n)` is such an upper
bound and makes all sublevel sets finite. The Lean construction therefore
gives one rigorous reduction covering both cases in the prose proof without
changing the statement of Lemma 3.8 or Theorem 3.5.

For Corollary 3.6, a countable class is covered by its finite enumeration
prefixes, intersected back with `H`. This formulation automatically handles
an empty class and a finite class whose ambient enumeration repeats or
contains irrelevant values. Each prefix is finite. The supporting finite-class
lemma bounds closure-witness sizes by taking the finite collection of common
cores arising from all subfamilies of a finite class.

## Theorem 3.10 finite-cover construction

`IsFiniteCover H classes` is the literal finite-union hypothesis
`H = ⋃ i, classes i`, with `i : Fin n`. After selecting a finite closure
dimension for each component, the proof takes their finite maximum `d` and
freezes, for every consistent component, the common core at the first prefix
containing `d + 1` distinct examples. Each active core is infinite.

The construction fixes a repetition-free enumeration of each active core and
selects a core whose longest observed initial enumeration segment is maximal.
A core contained in the target makes unbounded progress along an exact target
presentation. Every core not contained in the target has a first enumerated
obstruction outside the target, so its progress is eventually bounded. The
finite cover supplies a common bound for all bad cores, after which the chosen
core is contained in the target and its next enumerated point is both valid
and fresh. This is the frozen-core/maximal-progress proof in lines 763--773 of
the pinned TeX.

The public theorem exposes `[Nonempty alpha]`. The source assumes a generator
can always return an example before its eventual threshold. Without that
implicit convention, the empty example universe and empty class make UUS and
the finite-cover hypothesis vacuous but admit no function-valued generator.

The repetition-free enumeration, progress score, finite argmax race, and
finite-history-to-stream conversion are shared with the repaired C.2 proof in
the paper-local `GenLimit.Paper02_LearningTheory.Common` layer. They were not
moved into `GenLimit.Core`: these are concrete proof devices for #02, not part
of the library's small semantic interface. The relationship theorem
`finite_closure_dimension_cover_implies_generatable_via_euc` also records that
finite closure dimension implies EUC componentwise, so Theorem 3.10 can be
factored through C.2. The direct source-order proof remains intact.

## Section 3 and 4 examples

Lemma 3.4 is formalized with the paper's concrete class over the integers:
all languages containing the nonpositive integers. The proof uses the
infinite positive complement to give an explicit Cantor diagonal showing that
this upward cone is not countable, and then obtains uniform generation from
closure dimension zero.

The source proof incorrectly claims that the singleton closure is exactly the
nonpositive integers for every observed integer. For a positive observation
`x`, the closure must also contain `x`. Lean uses the correct inclusion of the
infinite nonpositive base, which is all the closure-dimension-zero argument
needs. This repair is documented here and beside
`exists_uncountable_uniformly_generatable_class`.

For Lemma 3.9, the source comments that its triangular arithmetic and
even/odd split are only a realization of disjoint finite blocks of unbounded
size together with two disjoint infinite tails. Lean uses that stated
abstraction directly. It proves countability, UUS, non-uniform generation via
Corollary 3.6, and failure of uniform generation via infinite closure
dimension. Thus the theorem statement and dependency structure are present,
but the particular integer coding has not been reproduced literally; that
construction-level correspondence remains a human-audit item.

Corollary 3.11 is exposed both as a universe-generic finite union of infinite
upward cones and as `finite_union_of_paper_cone_classes_generatable_in_limit`,
whose `Nat` formulation matches the displayed source class. Each component
has closure dimension zero, so the result invokes Theorem 3.10 exactly as in
the paper.

Lemma 3.12 uses the paper's positive and nonpositive subsets of `Int`. The
limit generator emits a fresh positive integer until a nonpositive example
appears, and fresh nonpositive integers thereafter. The non-uniform lower
bound recursively forms a subset of the positive integers that permanently
excludes the candidate generator's outputs, then defeats it on the target
formed by adjoining the nonpositive integers. This is the same class and
diagonal content as the source, although the Lean presentation packages the
recursion differently. The isolated occurrence of "USS" in the prose is
read as the intended UUS assumption.

Lemma 4.2 reuses this separation class. Lean proves separately that its two
component classes each have closure dimension zero and that their union is
not non-uniformly generatable.

Lemma 4.3 is formalized on `CountableUnionUniverse = Nat ⊕ (Nat × Nat)`.
This replaces prime ratios by their exact incidence structure: component zero
has an infinite shared row of anchors, while component `n + 1` has anchor `n`
and an infinite private tail. Each component is an upward cone above an
infinite core and therefore has UUS and closure dimension zero. The proof
implements the source's staged diagonal. At stage `n`, it extends the existing
history to a sufficiently late prefix of an exact presentation in component
`n + 1`, records the generator's fresh private-tail output, and withholds that
output. The nested limit history contains all anchors, hence belongs to
component zero, while disjointness of the tails keeps every recorded output
outside the final language. The generator therefore fails at arbitrarily late
stage endpoints.

## Appendix C: Eventually Unbounded Closure

`EventuallyUnboundedClosure` is the literal quantifier structure of
Definition C.1: for every target in the class and every exact presentation of
that target, some finite prefix has infinite non-bottom common core. The
formalization also proves that finite closure dimension, and hence uniform
generation, implies EUC.

Lemma C.1 is complete at the theorem-statement level. The source uses a
prime-power construction on finite bit strings; Lean instead uses the class
of cofinite subsets of `Nat`. This class is countable and UUS, hence
non-uniformly generatable by Corollary 3.6, while every finite consistent
sample has exactly that finite sample as its common core. The existential
separation is therefore kernel-checked, but the source's chosen witness and
its internal construction have not been formalized.

The cofinite class and its generic countability, UUS, common-core, and
infinite-closure facts now have one canonical definition in
`Examples.Cofinite`. Appendix A's `cofiniteClass` is a compatibility wrapper,
while Appendix C adds only its EUC-specific argument.

Theorem C.4 is represented by
`theorem_C4_eventually_unbounded_closure`. Its underlying generator chooses
the maximum eligible class among the first `t + 1` cover components whose
version space is nonempty and whose current common core is infinite. EUC is
needed only for a component containing the target; the non-decreasing cover
then ensures that the selected component also contains the target. The
paper-facing wrapper retains `[Countable alpha]` and UUS even though this
set-theoretic proof does not use them.

The printed C.4 proof initially assigns a bottom-or-infinite stopping time to
every component along the target stream, which again overuses the false
arbitrary-stream reformulation. Lean only invokes Definition C.1 for a cover
component containing the target. Non-decreasingness then ensures that every
later selected component also contains the target, so the theorem and
Algorithm 1's rightmost-eligible-index idea remain valid.

The prose immediately before Theorem C.2 invokes the following purported
equivalent form of Definition C.1: every arbitrary stream has a finite prefix
whose closure is bottom or infinite. That equivalence is false. The
kernel-checked diagnostic uses spine points `a_0, a_1, ...`, pairwise disjoint
infinite tails `T_n`, and languages

```text
L_n = {a_0, ..., a_n} union T_n.
```

The class `{L_n}` satisfies Definition C.1 because any exact presentation of
`L_n` eventually reveals a point in its unique tail, after which the version
space is the singleton `{L_n}` and its core is infinite. On the arbitrary
spine stream `a_0, a_1, ...`, however, every finite prefix is consistent with
all sufficiently large `L_n`, and its common core is exactly that finite
prefix: it is never bottom or infinite. The C.2 argument uses the false
equivalence to assign a stopping time to every cover component, including a
component for which the target stream presents no member.

The theorem itself is nevertheless valid. `FiniteEUCUnion` supplies the
missing proof. At any finite history, a component activates only when an
infinite common core has actually appeared; that first core is then frozen.
Along a fixed target presentation, only finitely many cover components exist,
so all components that ever activate have stabilized after a finite time. A
component containing the target activates by literal Definition C.1 and has a
frozen core contained in the target. Every bad frozen core has a first
enumerated point outside the target and therefore bounded enumeration
progress. The good core has unbounded progress. Maximizing progress over the
finite stabilized active set eventually selects only good cores. This proves
the exact finite-cover conclusion without the false arbitrary-stream
equivalence.

## Prompted generation

Section 5 is formalized in four modules. The API makes the source's timing
literal: at positive round `s`, the prompted generator receives the entire
current observation tuple, including current prompt `y_s`; the auxiliary
round `s = 0` is vacuous. The following source issues are recorded explicitly:

- Definition 5.1 lists `(x_2, h(x_1), y_2)`; the second label appears to be a
  typographical error for `h(x_2)`.
- Definition 5.5 writes a condition of the form `|closure| != bottom`.
  Cardinality cannot equal `bottom`; the intended condition appears to be
  `closure != bottom`.
- The necessity proof of Theorem 5.1 says MUUS where the theorem and prompted
  uniform setting require PUUS.
- The proof of Corollary 5.3 claims `PC(H) = max_y d_y`, although each `d_y`
  is introduced only as a valid generation threshold, not a least threshold.
  Lean proves the corollary directly from finiteness of the prompt space and
  does not assert this unjustified equality.
- Definition 5.1 gives a prompted generator the current tuple, including the
  current prompt `y_s`. In Lean this is the last element, at index `s - 1`,
  of the length-`s` history. `PromptedCorrectAt` and `promptedHistory`
  implement that printed current-tuple convention; comparisons with the
  zero-based unprompted API must use the same paper-facing reindexing.

Theorems 5.1 and 5.2 preserve the paper's necessity/sufficiency structure.
The sufficiency direction of Theorem 5.2 uses the same harmless threshold
padding as the unprompted theorem: a valid threshold for cover component `n`
is replaced by `max n d_n`, ensuring the set of eligible indices is finite.
Corollary 5.3 includes the empty-class edge case. Lemma 5.4 and Corollary 5.5
use a tagged two-hypothesis construction with the same finite blocks and
disjoint infinite tails as the source's prime-power realization.

## Completed scope

The following path is present in Lean:

1. a reusable arbitrary countable-universe generator interface;
2. support classes, positive streams, UUS, version spaces, and closure;
3. in-limit, uniform, and non-uniform generation predicates;
4. the implication chain among those predicates and the source-facing
   Proposition 2.1 package witnessing strictness of both implications;
5. closure witnesses and finite closure dimension;
6. the exact-witness and finite-core adversarial construction from
   `lem:closnec`;
7. the closure-based generator from `lem:clossuff`;
8. both directions and the equivalence in Theorem 3.3;
9. Definition 2.3's literal extended-natural least threshold for each
   generator, the class-level optimum, and the exact post-Theorem-3.3
   interval `C(H) <= d_opt <= C(H) + 1`;
10. the non-decreasing uniform-cover necessity reduction in Lemma 3.7;
11. the finite maximum-eligible-index sufficiency reduction in Lemma 3.8;
12. the finite-closure-cover equivalence in Theorem 3.5;
13. the countable-class result in Corollary 3.6, including its finite-prefix
    cover and finite-class closure bound, and the exact source-facing
    `theorem_2_4` limit-generation wrapper;
14. the finite-cover sufficient condition for generation in the limit,
    including the frozen-core/maximal-progress construction in Theorem 3.10;
15. the uncountable uniformly generatable upward-cone example in Lemma 3.4;
16. the countable non-uniform-but-not-uniform example in Lemma 3.9;
17. the finite-union-of-cones consequence in Corollary 3.11;
18. the in-limit-but-not-non-uniform integer class in Lemma 3.12;
19. the failure of finite-union closure for non-uniform generation in
    Lemma 4.2;
20. the staged countable-union lower bound for generation in the limit in
    Lemma 4.3;
21. Definitions 2.9 and 2.11--2.12 and all six Appendix A constructions for
    Theorem 4.1 at the finite-VC/finite-Littlestone characterization boundary;
22. prompted hypotheses, PUUS, prompted generators, prompted generation
    notions, version spaces, closure, and prompted closure dimension;
23. both directions and the equivalence in prompted Theorem 5.1;
24. both directions and the equivalence in prompted Theorem 5.2;
25. all three conclusions of prompted Corollary 5.3;
26. the infinite-prompt finite-class separations in Lemma 5.4 and Corollary
    5.5;
27. Eventually Unbounded Closure in Definition C.1 and the non-necessity
    separation in Lemma C.1;
28. the repaired finite EUC-cover construction in Theorem C.2;
29. a concrete counterexample to the false streamwise EUC equivalence printed
    before C.2; and
30. the non-decreasing EUC-cover sufficiency construction in Theorem C.4;
31. Definitions 2.6--2.7 and Theorem 2.2 through explicit Gold/P02 bridges;
32. Theorem 2.3 with Angluin's indexed-family/countability hypothesis
    restored, plus a concrete counterexample to the printed arbitrary-class
    formulation;
33. the source-facing finite-class conclusion in Theorem 2.5; and
34. explicit Basic/Generic, indexed-family/extensional-class, and KM/#02
    adapters, plus the factorization of Theorem 3.10 through C.2.

The operational conclusion has the paper's quantitative threshold `d + 1`:

```lean
theorem closure_dimension_sufficiency [Nonempty alpha] [Countable alpha]
    {H : GenLimit.Generic.LanguageClass alpha} (hUUS : UUS H) {d : Nat}
    (hC : HasClosureDimension H d) :
    exists gen : GenLimit.Generic.Generator alpha,
      IsUniformGeneratorAt gen H (d + 1)
```

The packaged quantitative conclusion is:

```lean
theorem optimal_uniform_generation_sample_complexity_bounds
    [Nonempty alpha] [Countable alpha]
    {H : GenLimit.Generic.LanguageClass alpha} (hUUS : UUS H) {d : Nat}
    (hC : HasClosureDimension H d) :
    (d : WithTop Nat) <= optimalUniformGenerationSampleComplexity H ∧
      optimalUniformGenerationSampleComplexity H <=
        ((d + 1 : Nat) : WithTop Nat)
```

## Theorem 2.3 source repair

Angluin's original Theorem 1 is stated for an indexed family
`L_0, L_1, ...`; its extensional range is therefore countable (and the
original effective theorem carries additional computability assumptions).
P02 retains a countable example space but quantifies over an arbitrary
hypothesis class. This loses a necessary cardinality hypothesis for its
language-valued finite-history identifier: every identifiable UUS class over
a countable example space is countable. The selector-class diagnostic proves
that the printed arbitrary-class equivalence is false, while
`theorem_2_3_countable` proves the corrected semantic statement.

## Outstanding paper items

The principal current omissions from arXiv v5 / COLT 2025 are:

- Definition 2.8's literal PAC probability/sample/algorithm model and
  Definition 2.10's literal online algorithm, loss, and sublinear-regret
  model;
- the external VC/PAC and Littlestone/online characterization theorems needed
  to promote `theorem_4_1_combinatorial_core` to the literal wording of
  Theorem 4.1;
- ERM/max-min/membership-oracle implementations and efficiency statements;
- prompted quantitative sample complexity and the Section 5.1 / Remark 5.3
  transport theorems; and
- a public strict-separation theorem witnessing `EUC` without uniform
  generatability.

`GenLimit.Bridges.BasicToGeneric`, `IndexedFamilyToClass`,
`AngluinToPaper02`, `GoldToPaper02`, `Paper01ToPaper02`, and
`Paper02IdentificationDiagnostics` now make those comparison and diagnostic
theorems literal. They remain outside the native paper path so
`GenLimit.Paper02_LearningTheory` stays independently importable.

## Verification

Kernel status: **checked for the current individual modules**. The following
modules compile with Lean 4.24.0 and Mathlib 4.24.0:

```text
GenLimit.Core.GenericGeneration
GenLimit.Core.ClassGeneration
GenLimit.Core.VersionSpace
GenLimit.Core.ClosureDimension
GenLimit.Core.ClassCovers
GenLimit.Paper02_LearningTheory.Common
GenLimit.Paper02_LearningTheory.Definitions
GenLimit.Paper02_LearningTheory.Hierarchy
GenLimit.Paper02_LearningTheory.Closure
GenLimit.Paper02_LearningTheory.UniformSampleComplexity
GenLimit.Paper02_LearningTheory.NonuniformCharacterization
GenLimit.Paper02_LearningTheory.GenerationInLimitCharacterization
GenLimit.Paper02_LearningTheory.FiniteConeCover
GenLimit.Paper02_LearningTheory.LimitVsNonuniformSeparation
GenLimit.Paper02_LearningTheory.CountableUnionSeparation
GenLimit.Paper02_LearningTheory.EarlierSectionThreeExamples
GenLimit.Paper02_LearningTheory.Prediction
GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosure
GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosureDiagnostics
GenLimit.Paper02_LearningTheory.FiniteEUCUnion
GenLimit.Paper02_LearningTheory.Examples.Cofinite
GenLimit.Paper02_LearningTheory.Relationships
GenLimit.Paper02_LearningTheory.PromptedDefinitions
GenLimit.Paper02_LearningTheory.PromptedClosure
GenLimit.Paper02_LearningTheory.PromptedNonuniform
GenLimit.Paper02_LearningTheory.PromptedInfinitePromptExample
GenLimit.Bridges.BasicToGeneric
GenLimit.Bridges.IndexedFamilyToClass
GenLimit.Bridges.AngluinToPaper02
GenLimit.Bridges.GoldToPaper02
GenLimit.Bridges.Paper01ToPaper02
GenLimit.Bridges.Paper02IdentificationDiagnostics
```

The focused umbrella target passes. The generation declarations
and all seven prediction clause/package theorems in the shared audit report
only `propext`, `Classical.choice`, and `Quot.sound`. The checked files contain no
`sorry`, `admit`, or project-defined axiom. Repository-wide integration is
recorded in [`../AUDIT.md`](../AUDIT.md) and executable checks in
[`../Audit.lean`](../Audit.lean).

The ChatGPT Pro statement-faithfulness check, completed scope-limited human
audit, remaining human-review scope, and immutable evidence are tracked in the
[#02 audit record](../AuditRecords/Paper02_LearningTheory/) and the
[authoritative human-audit ledger](../AuditRecords/Human/README.md). The
statuses “complete” above mean kernel-checked against the stated
correspondence boundary; this map does not assign a human audit level. The
immutable audit evidence predates the new cross-paper bridges, so the bridge
status reported here comes from the current kernel build and executable axiom
audit rather than a retroactive change to that evidence bundle.
