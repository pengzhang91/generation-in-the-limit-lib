# Stage 1: code-only reconstruction of 13 Lean statements

## Scope, inputs, and evidence boundary

This is a reconstruction of the mathematical specifications of the 13 roots in `stage1/targets.txt`. It uses only the frozen files in `audit-packages/P03_Overview_2026-11-09_6062058/stage1/`. It makes no claim about correspondence to a paper, proof correctness, compilation, or human review. No paper, repository description, PaperMap, registry, prior audit, Stage 2 material, or source file outside that directory was consulted. Names and source paths below identify declarations; their spelling is not evidence for their meaning.

The complete `PROMPT.md`, `START_HERE.md`, `01-target-statements.md`, and `02-definition-dependencies.md` were read. The `declarations.jsonl` records were parsed for declaration kinds, universes, dependency closure, and source metadata. The toolchain, manifest, Lake configuration, target list, external boundary, and snapshot identity were inspected. The five optional batches were not used. All 11 non-optional files enumerated by `SHA256SUMS` matched their supplied SHA-256 hashes. `SHA256SUMS` itself was read and its current hash is recorded in the run metadata; it has no self-hash in that manifest.

There are 220 exported project declarations: 13 target theorems and 207 background declarations, comprising 168 definitions, 9 inductives, 9 constructors, and 34 theorem interfaces in total. All 13 roots have no universe parameters and specialize the mathematical domain to `Nat`. Generic background declarations retain their displayed universe parameters; they are instantiated at universe zero here. No target has an unreported typeclass assumption. The recursive project edge check found no referenced `GenLimit.*` constant outside the 220-record export. This checks the supplied expression graph, not completeness of the exporter or repository. Supporting theorem types were used only as interfaces, especially termination and computability certificates inside definitions; their proofs were neither supplied nor independently audited.

The snapshot describes a dirty working-tree byte snapshot captured at `2026-11-10T01:29:42.007354+00:00`, with recorded HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`, scope module `GenLimit.Paper03_HallucinationAndModeCollapse.Results.Overview`, and 96 recorded source/configuration files. These are identity facts, not additional mathematical premises. The toolchain is `leanprover/lean4:v4.24.0`; the Lake manifest pins Mathlib to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (input revision `v4.24.0`) and pins its transitive packages.

`external-constant-boundary.txt` declares the external Lean/Mathlib boundary. I use the usual semantics of sets, finite sets, natural-number lists, Boolean functions, option/sum/product types, encodings, total computability (`Computable`, `Computable₂`), primitive recursion, partial search (`Part`, `Nat.rfindOpt`), probability mass functions (`PMF` and `pure`, `map`, `bind`, `support`, `toOuterMeasure`), fair Bernoulli and geometric laws, extended cardinality (`Set.encard` into `ENat`), symmetric difference, real exponentiation, and filters (`atTop`, `Frequently`, `Tendsto`, `limsup`, and `IsLittleO`). In particular, support means positive mass; a PMF has total mass one; `Frequently` at natural-number `atTop` means arbitrarily large indices; and `Set.encard` assigns infinity to an infinite set. These external bodies are not bundled or re-audited. None of these standard meanings was sufficiently uncertain to require extra context for a target reconstruction. Embedded `⋯` are suppressed proof terms, not omitted data or missing mathematical assumptions.

## Common notation and glossary

In explanatory formulas, `H` abbreviates the exact namespace `GenLimit.HallucinationModeCollapse`, `S` abbreviates `GenLimit.Support`, and `Cᵢ` means `C i`. A displayed source locator abbreviates paths only: `P3/F.lean:k` expands to `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/F.lean:k`; `Core/F.lean:k` and `Support/F.lean:k` expand with the same `GenLimitLean/GenLimit/` prefix. These locators come from the export, not from opening the source files. The generated glossary locator index below supplies the fully qualified identifiers and exact source locations for all objects discussed here.

### Families, information, and semantic identification

`GenLimit.Generic.Language α = Set α`, `GenLimit.Generic.LanguageFamily α = Nat → Set α`; their `GenLimit.Language`/`GenLimit.LanguageFamily` versions use `Nat`. Thus every family is an indexed countable list of sets, with repeated indices/languages allowed. No effectiveness, distinctness, nonemptiness, infinitude, or finite-range condition is implicit in a bare family.

A `Generic.Stream α` is `Nat → α`, and `Generic.Presents stream L` means `range stream = L`: every stream item lies in the target, and every target item occurs at least once. Repetitions are allowed. `textPrefix stream t` is the ordered length-`t` list of stream values at indices `< t`; `Generic.sample stream t` is its finite set of distinct values. A stream of natural numbers cannot present the empty language.

A `Learner Info Name` is an arbitrary function `List Info → Name`. `StabilizesTo guess name` is `∃ T, ∀ t ≥ T, guess t = name`. `IdentifiesInLimit denote learner stream target` means there is one name denoting the target to which all sufficiently late prefix guesses are equal. `Angluin.SemanticallyIdentifies M C` requires this for every index and every presenting stream; `SemanticallyInferrable C` existentially chooses one such `M`. `H.IdentifiableInLimit C` is exactly this semantic existence assertion. It has no computability requirement. The eventual name may depend on the index and stream, but `M` is selected before either; the name denotes the right set, not necessarily the target index.

`Angluin.IsTellTale C i T`, for a finite set `T`, says `T ⊆ Cᵢ` and, for every `j`, `T ⊆ Cⱼ ⊆ Cᵢ` implies `Cᵢ ⊆ Cⱼ`. Equivalently, no proper sublanguage of `Cᵢ` in the indexed family contains `T`. It does not exclude strict superlanguages or incomparable languages containing `T`. `Angluin.ConditionTwo C` is `∀ i, ∃ T : Finset Nat, IsTellTale C i T`, without an effective way to choose those finite sets. `Angluin.IsEnumeratedTellTale C i T` makes the same assertion for a set `T`, additionally stating `Set.Finite T`. `S.enumeratedSet emit i = {x | ∃ s, emit i s = some x}`, and `Angluin.enumeratedSet` aliases it. An enumeration can repeat elements, emit `none`, and continue forever; finiteness of its range supplies neither a stopping stage known to a computation nor computability of `emit : Nat → Nat → Option Nat`.

`H.NontrivialCollection C` means `∃ i j x, Cᵢ ≠ Cⱼ ∧ x ∈ Cᵢ ∧ x ∈ Cⱼ`: two extensionally distinct languages overlap. `H.GenerationNontrivial C` instead says there is a nonempty finite set of indices whose intersection is finite and nonempty. These conditions are different. In an `OracleFamily`, every member is infinite, so the latter witness cannot be a single language, or merely repetitions of the same language.

### Oracles and procedures

`MembershipOracle C` contains `query : Nat → Nat → Bool` with `query i x = true ↔ x ∈ Cᵢ`. It need not be ordinarily computable. `SubsetOracle C` contains `query i j = true ↔ Cᵢ ⊆ Cⱼ`, with the orientation exactly as written. `OracleFamily` bundles a family, a proof that every member is infinite, and a correct Boolean membership query; it contains no computability certificate. `H.familyMembership O` exposes that same query as a `MembershipOracle`. `H.generationOracle O` encodes a pair `(i,x)` as one natural and answers 1 or 0 for membership.

`S.TruthTableProgram` bundles a primitive-recursive finite list of oracle queries for each input list and a computable postprocessor. `run P oracle xs` maps the oracle over those queries, then postprocesses `(xs, answers)`. Queries at this level are determined from the input before answers are received. `S.tableLookup` uses the first index of a code in the query list and defaults to 0 if no corresponding answer is present. Duplicate queries cause no semantic ambiguity for actual oracle answers.

`S.OracleSearchProgram` instead has a primitive-recursive finite query list for each `(xs,q)` and a computable `Option Nat` postprocessor. `stage P oracle xs q` obtains that finite answer table and returns an option. `partialRun` searches the stages using `Nat.rfindOpt`; `Terminates P oracle` asserts `∀ xs, ∃ q y, stage ... q = some y`; `run` extracts the resulting natural using that termination certificate. This permits an unbounded search across stages, not a fixed truth table for the whole computation. When an oracle is arbitrary, this is an oracle-relative procedure. A theorem conditionally asserting `Computable` after assuming computability of the query establishes ordinary total computability of the specialized function. It does not assert that the oracle supplied to every theorem is computable, or provide an input parameter consisting of an index for an oracle implementation.

`S.boundedAll p a n` tests all `k < n`; `S.firstTrue p a n` returns the least satisfying `k < n`, or `none`; `S.lastTrue p a n` returns the greatest, or `none`. These strict bounds matter at `n = 0` and distinguish `n` from `n+1` in the named constructions.

### Probability, outputs, errors, and rates

`DiscreteIID.samples p n` is the PMF of an ordered list of exactly `n` independent draws from `p`: the base law is `pure []`, and the successor law draws a new head and independently samples the tail. `DiscreteIID.probability p E` is the real value of the PMF's outer measure of `E`; all events here are discrete. `H.ValidDistribution C i p` means `support p = Cᵢ`, not just containment: every target element has positive probability and every nontarget element probability zero. No lower bound on positive masses is assumed. Empty `Cᵢ` admits no valid PMF, so the corresponding positive-data statistical obligations are vacuous.

Both `H.StatisticalIdentifier` and `H.StatisticalGenerator` are definitionally `List Nat → PMF Nat`, but their output interpretations and losses differ. A generator emits an element; an identifier emits an index. Neither type asserts computability, finite support, rational probabilities, or a sampler. `H.deterministicIdentifier A xs = pure (A xs)` is used for either interpretation when the target type allows it.

Write `e_id(C,A,p,i,n)` for `H.identificationError`: first draw `xs ~ samples p n`, then `j ~ A xs`; failure is `Cⱼ ≠ Cᵢ`. Any duplicate index for the same set is successful. Write `e_gen(C,G,p,i,n)` for `H.generationError`: draw `xs` and then `y ~ G xs`; failure is `y ∉ Cᵢ ∨ y ∈ xs`. Success requires membership and freshness relative to the observed list, not freshness relative to earlier outputs. Both errors average over training randomness and output randomness.

`H.breadthError` is instead the probability over training samples alone that `support (G xs) ≠ Cᵢ \ {x | x ∈ xs}`. It asks for exact equality of the support with all unobserved target elements, without requiring equal or specified output weights. `H.approximateBreadthError` and `H.unambiguousError` likewise take the indicator of failure of their respective support predicates and average only over the sample. They do not measure the fraction of target mass omitted, total-variation error, or the probability of one erroneous generated element.

For any of these errors, “exponential” means `∀ i p, Valid... → ∃ c > 0, ∃ D > 0, ∀ n : Nat, e(n) ≤ D exp(-c n)`. `H.ExponentialIdentifies`, `ExponentialGenerates`, `ExponentialBreadth`, and `ExponentialLabeledIdentifies` differ only in the law/error they apply to. The constants may depend on the fixed family, algorithm, target index, and full distribution, and must work for all `n`, including zero. This is not one common exponent across all distributions and not merely an eventual bound.

`H.AchievesIdentificationRate C A R` and `AchievesBreadthRate C G R` mean `∀ i p, Valid... → ∃ D > 0, ∀ n, e(n) ≤ D R(n)`, with the same dependency pattern. `H.AdmissibleSublinearExponent g` contains exactly three conditions: `∀ n, 0 ≤ g(n)`; `g = o(n)` at natural-number infinity; and `g(n) → +∞`. It requires neither monotonicity nor computability of `g`. `H.AlmostExponentialIdentifiable C` is `∀ admissible g, ∃ A : List Nat → Nat, AchievesIdentificationRate C (deterministicIdentifier A) (n ↦ exp(-g(n)))`. The deterministic semantic learner may depend on `g`; it is not declared computable and need not be one learner for all `g`.

`H.NoIdentificationRate C` is `∀ A : StatisticalIdentifier, ∃ i p, ValidDistribution C i p ∧ limsup_n e_id(C,A,p,i,n) > 0`. `H.NoBreadthRate C G`, `NoUnambiguousRate C G`, and `NoApproximateBreadthRate C G` fix `G` first and then assert the analogous existence of one bad target/distribution with strictly positive limsup of their particular errors. These are persistent nonvanishing-error claims, stronger than failure of one proposed numerical convergence rate. A positive limsup need not be a positive lower bound at every late time; there can be good subsequences. An infinitely-often bound by a decaying exponential also need not have positive limsup.

### Supports, online predicates, and effectiveness of support membership

`H.SupportGenerator` has `support : (t : Nat) → (Fin t → Nat) → Set Nat`, a Boolean membership query on the same data, and a proof relating them. The Boolean query is not automatically computable. `supportAt G stream t` evaluates the support on the first `t` stream items. `H.statisticalSupportView G` supplies `support (G xs)` and a classically chosen Boolean decider; it asserts no computation from the history.

For a support generator, all the following limit predicates quantify `∀ z stream, Presents stream C_z → ∃ T, ∀ t ≥ T, ...`. The threshold may depend on the target and the complete stream, and need not be known or computable. `FreshBreadthInLimit` requires support exactly `C_z \ sample(stream,t)`; `RepeatingBreadthInLimit` requires support exactly `C_z`. `ApproximateBreadthAt S K` means `S ⊆ K ∧ Set.Finite (K \ S)`; `ApproximateBreadthInLimit` eventually requires this predicate, with no common finite omitted set required across times and no bound on its size. It permits omitting any finite number of target elements, including none. It requires no outside elements at all.

`H.UnambiguousAt C z S` says that, for every `i` with `Cᵢ ≠ C_z`, `encard (S △ C_z) < encard (S △ Cᵢ)`. The target is strictly closer than every extensionally different family member in extended-cardinality symmetric-difference distance. Duplicate languages are excluded from the comparisons. Infinite distances use the value infinity; two infinite distances tie and cannot satisfy the strict inequality. With any distinct competitor the target distance must be finite. With no distinct language in the family the predicate is vacuous for every `S`. `UnambiguousInLimit` eventually requires this comparison on every presenting stream; it does not require the support to equal or be contained in the target.

`H.Stable G C` says `∀ z stream, Presents stream C_z → ∃ T, ∀ s t ≥ T, supportAt G stream s = supportAt G stream t`. `StatisticalStable G C` applies this to `statisticalSupportView G`. It is stabilization of the support sets along each stream, not convergence or stabilization of probabilities, not identification of the target, and not one common support across different streams. Fresh breadth for infinite targets changes as new elements appear and should not be silently combined with this stability assumption.

`H.DecidableMOP G` is pointwise: `∀ xs, ∃ query : Nat → Bool, Computable query ∧ ∀ x, query x = true ↔ x ∈ support (G xs)`. There is no effective operation selecting `query` from `xs`. `H.UniformDecidableMOP G` is `∃ query : List Nat → Nat → Bool, Computable₂ query ∧ ∀ xs x, ...`, one joint procedure. `H.OracleMOP oracle G` is again pointwise: for every fixed history there exists a `TruthTableProgram P` deciding support by whether `run P oracle [x] = 1`. The program may depend non-effectively on the history, and the definition imposes no 0-or-1 range condition away from the accepted value 1.

`H.HasComputableSampler G` means there is one computable total `sample : (List Nat × Nat) → Nat` with `G xs = PMF.map (seed ↦ sample (xs,seed)) DiscreteIID.positiveGeometric` for every history. The seed law is Mathlib's geometric PMF at parameter `1/2`, on the naturals, as fixed by the supplied proof types. This is a joint computable sampler with a specified seed source, not a computable table of probabilities. It is a separate assertion from either support-membership property.

### Named generation and breadth constructions

`H.certifiedKM O` is exactly `OracleSearchProgram.run generationProgram (generationOracle O)` with its supplied termination certificate. To make the named function concrete, let `n = length xs` and decode stage `q` as `(m,j) = Nat.unpair q`. `generationQueries (xs,q)` asks membership of each `C_k`, `k < n`, on every observed item and every natural `< m`. `generationConsistent data k` checks all observed items. `generationSubset data (pair j k)` tests the inclusion `C_j ∩ [0,m) ⊆ C_k ∩ [0,m)` from that table. `generationCritical data j` requires consistency and those finite inclusions into every consistent `k ≤ j`. `generationAccept` requires `m > 0`, `j < n`, criticality of `j`, maximality of `j` among all critical indices `< n`, membership of `m-1` in `C_j`, and every observed item strictly below `m-1`. `generationPost` immediately returns 0 if no candidate `< n` is consistent; otherwise it returns `m-1` only at an accepting stage and continues searching on `none`. Natural subtraction is truncated, but the accepting branch requires `m > 0`. In particular, at `xs=[]`, no candidate exists and the output is 0. No global correctness-at-every-history assertion follows from the exponential statistical conclusion.

`H.seededFreshSample O xs j seed` runs `samplerProgram` on the encoded input `j :: seed :: xs`. The helper projections `samplerIndex`, `samplerSeed`, and `samplerSample` read the first entry, second entry, and remaining tail, with zero defaults for absent entries. At search stage `q`, `samplerQueries` asks whether `seed+q ∈ C_j`; `samplerPost` returns that value precisely when membership is affirmative and it is not in `xs`. Thus the semantic search returns the first member of `C_j \ xs` at or above the seed. Termination relies on the infinitude stored in `OracleFamily`. `H.exactFreshSampler O xs j` maps this seeded function over `positiveGeometric`; its support is all of `C_j \ xs` (each fresh `x` is reached by seed `x`, which has positive mass), and nothing outside it. This support description is derived from the supplied search definition and the declared standard geometric/support meanings, not from an unexported support theorem.

`H.identifiedBreadth O A xs = exactFreshSampler O xs (A xs)`; `H.identifiedRepeatingBreadth O A xs = exactFreshSampler O [] (A xs)`. The former removes the current observed set; the latter samples over the selected whole language. Neither receives the true index or data distribution.

For `H.tellTaleBreadthGenerator O emit`, the learner `A` is the run of `identificationProgram` with `identificationOracle (familyMembership O) emit`. `emissionCode j s` tags an enumeration query with 0; `memberCode j x` tags membership with 1. At length `n`, `identificationQueries` requests emissions for all `j ≤ n`, `s < n`, and membership of all sample items in all those candidate languages. `answerAt` reads the table; `decodedTell data j` collects successful decoded `some x` emissions at stages `< n`. `tableEligible` means every such emitted item has been observed and every observed item lies in the candidate. `identificationPost` chooses the least eligible `j ≤ n`, or 0 if none. `identificationOracle` returns the encoded optional emission or the 0/1 membership answer, with 0 for unrecognized tags. The enumeration is a separate information source from family membership; the existence of suitable `emit` does not imply it is computable.

`H.CertifiedBreadthPositiveBranch O` and `H.CertifiedOnlineBreadthPositiveBranch O` are conjunction-rich existential certificates, fully expanded in dossiers 3 and 5 below. They assert properties of these named constructions, not just an unspecified successful generator.

### Named positive-data and labeled learners

For `H.subsetIdentifier O S`, the truth-table oracle has tag 0 for membership and tag 1 for inclusion. At length `n`, `subsetIdentificationQueries` asks all sample membership questions for candidates `j < n`, and for each such `j` all inclusions `C_j ⊆ C_k` with `k < j`. `subsetTableConsistent` checks sample containment; `subsetTableCritical` additionally requires inclusion into every earlier consistent `k < j`. `subsetIdentificationPost` uses `lastTrue` to choose the largest critical `j < n`, or 0 if absent. `subsetMemberCode`, `subsetInclusionCode`, `subsetAnswerAt`, and `subsetIdentificationOracle` supply exactly these encodings and answers. This construction receives the family membership and subset oracles, not finite tell-tales as inputs.

`H.sampleConsistent O xs j` checks that all observed items belong to `C_j`. `H.prefixMinimal O xs j` also checks, for every sample-consistent `k ≤ n`, that `C_j ∩ [0,n) ⊆ C_k ∩ [0,n)`, where `n = length xs`. `H.finiteVersionSpaceLearner O xs` selects the least prefix-minimal `j ≤ n`, or 0 if there is none. It uses only finite membership tests; it is not supplied a list of the distinct family languages or a bound on their sizes.

`H.LabeledDatum = Gold.Informant.InformantDatum = Nat × Bool`. `H.CorrectLabel C i (x,b)` means `b = true ↔ x ∈ Cᵢ`. `H.ValidLabeledDistribution C i p` requires support exactly `{(x,b) | CorrectLabel C i (x,b)}`: for each natural `x`, its one correct label has positive mass; the incorrect label has zero mass. It includes positive and negative data wherever the target and its complement are nonempty. It is not merely a law on a selection of correctly labeled points.

`H.LabeledIdentifier = List LabeledDatum → PMF Nat`; `deterministicLabeledIdentifier` wraps a deterministic list-to-index learner in a point mass. `labeledIdentificationError` draws an i.i.d. labeled list and a hypothesis index and fails exactly when its language differs from the target. `labeledConsistent O xs j` compares the oracle label for every observed item against its supplied Boolean. `labeledEnumerationLearner O xs` selects the least consistent `j < length xs`, or 0 if none; the strict bound is not `≤ length xs`. It needs no subset oracle.

### Token generation and its machine model

`S.RandomBitMachine.Machine` contains computable initial-state and action functions on natural numbers. `Action = Nat ⊕ (Nat ⊕ (Nat × Nat))` encodes halt with output, deterministic transition, and a Boolean-branch transition; `Configuration = Nat ⊕ Nat` distinguishes running state and halted output. `advance` preserves halted outputs; deterministic transitions ignore the current bit; branching chooses the first next state for false and the second for true. `evaluate` folds one step per bit in a finite list, and `run M input tape n` uses the first `n` bits of the tape. Thus unused random bits can be consumed at deterministic steps without altering their transition.

`Machine.AlwaysHalts M` is `∀ input tape, ∃ n output, run ... n = inr output`. It requires termination on every infinite bit tape, not just with probability one. `binaryWords n` enumerates all length-`n` Boolean words, including `[[]]` at zero. `boundedResults` evaluates all of them; `halted` tests the halted constructor; `allFinished` tests that all results have halted. `boundProgram` has no oracle queries and searches for a time satisfying `allFinished`. Its supplied `boundProgram_terminates` interface uses `AlwaysHalts`. `executionBound` is the resulting search value. `fairCoin` is Bernoulli `1/2`; `boundedLaw` evaluates under independent fair bits; `outputOrZero` extracts a halted output and defaults to 0 on a running configuration; `outputLaw` uses `boundedLaw` at the execution bound. The defaults do not license an assumption of termination without the explicit hypothesis.

`H.TokenGenerator` bundles such a machine, a computable decoder `readOutput : Nat → (Option Nat × Nat)`, and `initialAux : Nat`. `inputCode stem aux` encodes the pair. `nextLaw G hG stem aux` maps the decoder over `machine.outputLaw` at that input. The optional value is either one next token (`some token`) or a stop marker (`none`); the second coordinate updates the auxiliary state.

`wordExperiment G hG stem aux word` is a finite recursive Boolean experiment. For `word=[]`, it succeeds precisely when the next call produces `none`, irrespective of the returned auxiliary value. For `token::rest`, it calls `nextLaw`, rejects unless the emitted option is exactly `some token`, and on a match recurses with `stem ++ [token]`, the returned auxiliary state, and `rest`. `wordProbability G hG word` is the real probability of success from empty stem and `initialAux`. It is the probability of emitting exactly that finite word followed immediately by stop; the empty word asks for immediate stop. `AlwaysHalts` is per machine call: it does not require the overall token process to stop after finitely many emitted tokens. The total mass of the finite-word probabilities need not be one.

### Fully qualified project dependency locator index

This index locates all 207 background records. Mathematical readings are given in the glossary above; ordinary projections and generated case-eliminator definitions only unpack the displayed fields or constructors. Nonroot theorem records are explicitly labeled **interface only**. Their presence is not a claim of an independent proof audit. Source positions marked `generated` are exported that way.

| Exact Lean identifier | Kind | Source anchor from export |
|---|---|---|
| [`GenLimit.IdentifiesInLimit`](../stage1/02-definition-dependencies.md#genlimitidentifiesinlimit) | definition | `GenLimitLean/GenLimit/Core/Identification.lean:53` |
| [`GenLimit.Language`](../stage1/02-definition-dependencies.md#genlimitlanguage) | definition | `GenLimitLean/GenLimit/Core/Basic.lean:20` |
| [`GenLimit.LanguageFamily`](../stage1/02-definition-dependencies.md#genlimitlanguagefamily) | definition | `GenLimitLean/GenLimit/Core/Basic.lean:23` |
| [`GenLimit.Learner`](../stage1/02-definition-dependencies.md#genlimitlearner) | definition | `GenLimitLean/GenLimit/Core/Identification.lean:18` |
| [`GenLimit.MembershipOracle`](../stage1/02-definition-dependencies.md#genlimitmembershiporacle) | inductive | `GenLimitLean/GenLimit/Core/Basic.lean:38` |
| [`GenLimit.OracleFamily`](../stage1/02-definition-dependencies.md#genlimitoraclefamily) | inductive | `GenLimitLean/GenLimit/Core/OracleFamily.lean:17` |
| [`GenLimit.StabilizesTo`](../stage1/02-definition-dependencies.md#genlimitstabilizesto) | definition | `GenLimitLean/GenLimit/Core/Identification.lean:47` |
| [`GenLimit.SubsetOracle`](../stage1/02-definition-dependencies.md#genlimitsubsetoracle) | inductive | `GenLimitLean/GenLimit/Core/SubsetOracle.lean:13` |
| [`GenLimit.textPrefix`](../stage1/02-definition-dependencies.md#genlimittextprefix) | definition | `GenLimitLean/GenLimit/Core/Text.lean:16` |
| [`GenLimit.Angluin.ConditionTwo`](../stage1/02-definition-dependencies.md#genlimitangluinconditiontwo) | definition | `GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Semantic/Definitions.lean:52` |
| [`GenLimit.Angluin.IsEnumeratedTellTale`](../stage1/02-definition-dependencies.md#genlimitangluinisenumeratedtelltale) | definition | `GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Effective/Definitions.lean:42` |
| [`GenLimit.Angluin.IsTellTale`](../stage1/02-definition-dependencies.md#genlimitangluinistelltale) | definition | `GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Semantic/Definitions.lean:39` |
| [`GenLimit.Angluin.SemanticIdentifier`](../stage1/02-definition-dependencies.md#genlimitangluinsemanticidentifier) | definition | `GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Semantic/Definitions.lean:18` |
| [`GenLimit.Angluin.SemanticallyIdentifies`](../stage1/02-definition-dependencies.md#genlimitangluinsemanticallyidentifies) | definition | `GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Semantic/Definitions.lean:24` |
| [`GenLimit.Angluin.SemanticallyInferrable`](../stage1/02-definition-dependencies.md#genlimitangluinsemanticallyinferrable) | definition | `GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Semantic/Definitions.lean:30` |
| [`GenLimit.Angluin.enumeratedSet`](../stage1/02-definition-dependencies.md#genlimitangluinenumeratedset) | definition | `GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Effective/Definitions.lean:38` |
| [`GenLimit.DiscreteIID.positiveGeometric`](../stage1/02-definition-dependencies.md#genlimitdiscreteiidpositivegeometric) | definition | `GenLimitLean/GenLimit/Support/FullSupportDistribution.lean:20` |
| [`GenLimit.DiscreteIID.probability`](../stage1/02-definition-dependencies.md#genlimitdiscreteiidprobability) | definition | `GenLimitLean/GenLimit/Support/DiscreteIID.lean:25` |
| [`GenLimit.DiscreteIID.samples`](../stage1/02-definition-dependencies.md#genlimitdiscreteiidsamples) | definition | `GenLimitLean/GenLimit/Support/DiscreteIID.lean:20` |
| [`GenLimit.Generic.Language`](../stage1/02-definition-dependencies.md#genlimitgenericlanguage) | definition | `GenLimitLean/GenLimit/Core/GenericGeneration.lean:21` |
| [`GenLimit.Generic.LanguageFamily`](../stage1/02-definition-dependencies.md#genlimitgenericlanguagefamily) | definition | `GenLimitLean/GenLimit/Core/GenericGeneration.lean:28` |
| [`GenLimit.Generic.Presents`](../stage1/02-definition-dependencies.md#genlimitgenericpresents) | definition | `GenLimitLean/GenLimit/Core/GenericGeneration.lean:50` |
| [`GenLimit.Generic.Stream`](../stage1/02-definition-dependencies.md#genlimitgenericstream) | definition | `GenLimitLean/GenLimit/Core/GenericGeneration.lean:31` |
| [`GenLimit.Generic.sample`](../stage1/02-definition-dependencies.md#genlimitgenericsample) | definition | `GenLimitLean/GenLimit/Core/GenericGeneration.lean:63` |
| [`GenLimit.HallucinationModeCollapse.AchievesBreadthRate`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseachievesbreadthrate) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/BreadthModel.lean:27` |
| [`GenLimit.HallucinationModeCollapse.AchievesIdentificationRate`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseachievesidentificationrate) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/UniversalRates.lean:34` |
| [`GenLimit.HallucinationModeCollapse.AdmissibleSublinearExponent`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseadmissiblesublinearexponent) | inductive | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/UniversalRates.lean:26` |
| [`GenLimit.HallucinationModeCollapse.AlmostExponentialIdentifiable`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsealmostexponentialidentifiable) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/UniversalRates.lean:39` |
| [`GenLimit.HallucinationModeCollapse.ApproximateBreadthAt`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseapproximatebreadthat) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:82` |
| [`GenLimit.HallucinationModeCollapse.ApproximateBreadthInLimit`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseapproximatebreadthinlimit) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:86` |
| [`GenLimit.HallucinationModeCollapse.CertifiedBreadthPositiveBranch`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsecertifiedbreadthpositivebranch) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/StatisticalBreadth.lean:32` |
| [`GenLimit.HallucinationModeCollapse.CertifiedOnlineBreadthPositiveBranch`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsecertifiedonlinebreadthpositivebranch) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OnlineBreadthConstruction.lean:90` |
| [`GenLimit.HallucinationModeCollapse.CorrectLabel`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsecorrectlabel) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/LabeledIdentificationModel.lean:20` |
| [`GenLimit.HallucinationModeCollapse.DecidableMOP`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsedecidablemop) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/BreadthModel.lean:41` |
| [`GenLimit.HallucinationModeCollapse.ExponentialBreadth`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseexponentialbreadth) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/BreadthModel.lean:36` |
| [`GenLimit.HallucinationModeCollapse.ExponentialGenerates`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseexponentialgenerates) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/GenerationModel.lean:41` |
| [`GenLimit.HallucinationModeCollapse.ExponentialIdentifies`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseexponentialidentifies) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/StatisticalModel.lean:46` |
| [`GenLimit.HallucinationModeCollapse.ExponentialLabeledIdentifies`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseexponentiallabeledidentifies) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/LabeledIdentificationModel.lean:69` |
| [`GenLimit.HallucinationModeCollapse.FreshBreadthInLimit`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsefreshbreadthinlimit) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:53` |
| [`GenLimit.HallucinationModeCollapse.GenerationNontrivial`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationnontrivial) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/GenerationModel.lean:52` |
| [`GenLimit.HallucinationModeCollapse.GenerationTable`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationtable) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:25` |
| [`GenLimit.HallucinationModeCollapse.HasComputableSampler`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsehascomputablesampler) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SupportMembership.lean:27` |
| [`GenLimit.HallucinationModeCollapse.IdentifiableInLimit`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseidentifiableinlimit) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:104` |
| [`GenLimit.HallucinationModeCollapse.LabeledDatum`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapselabeleddatum) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/LabeledIdentificationModel.lean:17` |
| [`GenLimit.HallucinationModeCollapse.LabeledIdentifier`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapselabeledidentifier) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/LabeledIdentificationModel.lean:18` |
| [`GenLimit.HallucinationModeCollapse.NoApproximateBreadthRate`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsenoapproximatebreadthrate) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ApproximateBreadthModel.lean:44` |
| [`GenLimit.HallucinationModeCollapse.NoBreadthRate`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsenobreadthrate) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/BreadthModel.lean:32` |
| [`GenLimit.HallucinationModeCollapse.NoIdentificationRate`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsenoidentificationrate) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/UniversalRates.lean:45` |
| [`GenLimit.HallucinationModeCollapse.NoUnambiguousRate`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsenounambiguousrate) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/UnambiguousModel.lean:79` |
| [`GenLimit.HallucinationModeCollapse.NontrivialCollection`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsenontrivialcollection) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/StatisticalModel.lean:52` |
| [`GenLimit.HallucinationModeCollapse.OracleMOP`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseoraclemop) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SupportMembership.lean:23` |
| [`GenLimit.HallucinationModeCollapse.RepeatingBreadthInLimit`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapserepeatingbreadthinlimit) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:61` |
| [`GenLimit.HallucinationModeCollapse.Stable`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsestable) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:45` |
| [`GenLimit.HallucinationModeCollapse.StatisticalGenerator`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsestatisticalgenerator) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/GenerationModel.lean:17` |
| [`GenLimit.HallucinationModeCollapse.StatisticalIdentifier`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsestatisticalidentifier) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/StatisticalModel.lean:33` |
| [`GenLimit.HallucinationModeCollapse.StatisticalStable`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsestatisticalstable) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/UnambiguousModel.lean:39` |
| [`GenLimit.HallucinationModeCollapse.SupportGenerator`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesupportgenerator) | inductive | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:27` |
| [`GenLimit.HallucinationModeCollapse.TokenGenerator`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetokengenerator) | inductive | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/TokenGeneration.lean:19` |
| [`GenLimit.HallucinationModeCollapse.UnambiguousAt`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseunambiguousat) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:69` |
| [`GenLimit.HallucinationModeCollapse.UnambiguousInLimit`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseunambiguousinlimit) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:75` |
| [`GenLimit.HallucinationModeCollapse.UniformDecidableMOP`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseuniformdecidablemop) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/BreadthModel.lean:45` |
| [`GenLimit.HallucinationModeCollapse.ValidDistribution`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsevaliddistribution) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/StatisticalModel.lean:29` |
| [`GenLimit.HallucinationModeCollapse.ValidLabeledDistribution`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsevalidlabeleddistribution) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/LabeledIdentificationModel.lean:23` |
| [`GenLimit.HallucinationModeCollapse.answerAt`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseanswerat) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:45` |
| [`GenLimit.HallucinationModeCollapse.approximateBreadthError`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseapproximatebreadtherror) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ApproximateBreadthModel.lean:20` |
| [`GenLimit.HallucinationModeCollapse.breadthError`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsebreadtherror) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/BreadthModel.lean:23` |
| [`GenLimit.HallucinationModeCollapse.certifiedKM`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsecertifiedkm) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:283` |
| [`GenLimit.HallucinationModeCollapse.decodedTell`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsedecodedtell) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:57` |
| [`GenLimit.HallucinationModeCollapse.deterministicIdentifier`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsedeterministicidentifier) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/StatisticalModel.lean:36` |
| [`GenLimit.HallucinationModeCollapse.deterministicLabeledIdentifier`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsedeterministiclabeledidentifier) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/LabeledIdentificationModel.lean:62` |
| [`GenLimit.HallucinationModeCollapse.emissionCode`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseemissioncode) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:22` |
| [`GenLimit.HallucinationModeCollapse.exactFreshSampler`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseexactfreshsampler) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:111` |
| [`GenLimit.HallucinationModeCollapse.familyMembership`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsefamilymembership) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/BreadthConstruction.lean:19` |
| [`GenLimit.HallucinationModeCollapse.finiteVersionSpaceLearner`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsefiniteversionspacelearner) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/FiniteIdentification.lean:36` |
| [`GenLimit.HallucinationModeCollapse.generationAccept`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationaccept) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:120` |
| [`GenLimit.HallucinationModeCollapse.generationAnswer`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationanswer) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:40` |
| [`GenLimit.HallucinationModeCollapse.generationConsistent`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationconsistent) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:51` |
| [`GenLimit.HallucinationModeCollapse.generationCritical`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationcritical) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:86` |
| [`GenLimit.HallucinationModeCollapse.generationError`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationerror) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/GenerationModel.lean:36` |
| [`GenLimit.HallucinationModeCollapse.generationHasConsistent`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationhasconsistent) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:106` |
| [`GenLimit.HallucinationModeCollapse.generationOracle`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationoracle) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:170` |
| [`GenLimit.HallucinationModeCollapse.generationPost`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationpost) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:152` |
| [`GenLimit.HallucinationModeCollapse.generationPost_computable`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationpost_computable) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:157` |
| [`GenLimit.HallucinationModeCollapse.generationProgram`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationprogram) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:164` |
| [`GenLimit.HallucinationModeCollapse.generationProgram_terminates`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationprogram_terminates) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:247` |
| [`GenLimit.HallucinationModeCollapse.generationQueries`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationqueries) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:27` |
| [`GenLimit.HallucinationModeCollapse.generationQueries_primrec`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationqueries_primrec) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:31` |
| [`GenLimit.HallucinationModeCollapse.generationSubset`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsegenerationsubset) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:63` |
| [`GenLimit.HallucinationModeCollapse.identificationError`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseidentificationerror) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/StatisticalModel.lean:40` |
| [`GenLimit.HallucinationModeCollapse.identificationOracle`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseidentificationoracle) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:111` |
| [`GenLimit.HallucinationModeCollapse.identificationPost`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseidentificationpost) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:97` |
| [`GenLimit.HallucinationModeCollapse.identificationPost_computable`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseidentificationpost_computable) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:100` |
| [`GenLimit.HallucinationModeCollapse.identificationProgram`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseidentificationprogram) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:105` |
| [`GenLimit.HallucinationModeCollapse.identificationQueries`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseidentificationqueries) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:25` |
| [`GenLimit.HallucinationModeCollapse.identificationQueries_primrec`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseidentificationqueries_primrec) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:29` |
| [`GenLimit.HallucinationModeCollapse.identifiedBreadth`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseidentifiedbreadth) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/BreadthConstruction.lean:22` |
| [`GenLimit.HallucinationModeCollapse.identifiedRepeatingBreadth`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseidentifiedrepeatingbreadth) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OnlineBreadthConstruction.lean:30` |
| [`GenLimit.HallucinationModeCollapse.instDecidableGenerationAccept`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseinstdecidablegenerationaccept) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:128` |
| [`GenLimit.HallucinationModeCollapse.instDecidableGenerationHasConsistent`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseinstdecidablegenerationhasconsistent) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleGeneration.lean:109` |
| [`GenLimit.HallucinationModeCollapse.labeledConsistent`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapselabeledconsistent) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/LabeledEnumeration.lean:19` |
| [`GenLimit.HallucinationModeCollapse.labeledEnumerationLearner`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapselabeledenumerationlearner) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/LabeledEnumeration.lean:34` |
| [`GenLimit.HallucinationModeCollapse.labeledIdentificationError`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapselabeledidentificationerror) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/LabeledIdentificationModel.lean:65` |
| [`GenLimit.HallucinationModeCollapse.memberCode`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsemembercode) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:23` |
| [`GenLimit.HallucinationModeCollapse.prefixMinimal`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseprefixminimal) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/FiniteIdentification.lean:29` |
| [`GenLimit.HallucinationModeCollapse.sampleConsistent`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesampleconsistent) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/FiniteIdentification.lean:24` |
| [`GenLimit.HallucinationModeCollapse.samplerIndex`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesamplerindex) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:21` |
| [`GenLimit.HallucinationModeCollapse.samplerPost`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesamplerpost) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:42` |
| [`GenLimit.HallucinationModeCollapse.samplerPost_computable`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesamplerpost_computable) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:46` |
| [`GenLimit.HallucinationModeCollapse.samplerProgram`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesamplerprogram) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:62` |
| [`GenLimit.HallucinationModeCollapse.samplerProgram_terminates`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesamplerprogram_terminates) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:78` |
| [`GenLimit.HallucinationModeCollapse.samplerQueries`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesamplerqueries) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:33` |
| [`GenLimit.HallucinationModeCollapse.samplerQueries_primrec`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesamplerqueries_primrec) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:36` |
| [`GenLimit.HallucinationModeCollapse.samplerSample`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesamplersample) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:23` |
| [`GenLimit.HallucinationModeCollapse.samplerSeed`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesamplerseed) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:22` |
| [`GenLimit.HallucinationModeCollapse.seededFreshSample`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseseededfreshsample) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/ExactSampler.lean:88` |
| [`GenLimit.HallucinationModeCollapse.statisticalSupportView`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsestatisticalsupportview) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/UnambiguousModel.lean:26` |
| [`GenLimit.HallucinationModeCollapse.subsetAnswerAt`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsetanswerat) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:48` |
| [`GenLimit.HallucinationModeCollapse.subsetIdentificationOracle`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsetidentificationoracle) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:108` |
| [`GenLimit.HallucinationModeCollapse.subsetIdentificationPost`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsetidentificationpost) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:94` |
| [`GenLimit.HallucinationModeCollapse.subsetIdentificationPost_computable`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsetidentificationpost_computable) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:97` |
| [`GenLimit.HallucinationModeCollapse.subsetIdentificationProgram`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsetidentificationprogram) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:102` |
| [`GenLimit.HallucinationModeCollapse.subsetIdentificationQueries`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsetidentificationqueries) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:31` |
| [`GenLimit.HallucinationModeCollapse.subsetIdentificationQueries_primrec`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsetidentificationqueries_primrec) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:35` |
| [`GenLimit.HallucinationModeCollapse.subsetIdentifier`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsetidentifier) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:138` |
| [`GenLimit.HallucinationModeCollapse.subsetInclusionCode`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsetinclusioncode) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:29` |
| [`GenLimit.HallucinationModeCollapse.subsetMemberCode`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsetmembercode) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:28` |
| [`GenLimit.HallucinationModeCollapse.subsetTableConsistent`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsettableconsistent) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:59` |
| [`GenLimit.HallucinationModeCollapse.subsetTableCritical`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesubsettablecritical) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/SubsetIdentification.lean:73` |
| [`GenLimit.HallucinationModeCollapse.supportAt`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesupportat) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:34` |
| [`GenLimit.HallucinationModeCollapse.tableEligible`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetableeligible) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OracleIdentification.lean:71` |
| [`GenLimit.HallucinationModeCollapse.tellTaleBreadthGenerator`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetelltalebreadthgenerator) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/StatisticalBreadth.lean:23` |
| [`GenLimit.HallucinationModeCollapse.unambiguousError`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseunambiguouserror) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/UnambiguousModel.lean:50` |
| [`GenLimit.MembershipOracle.mk`](../stage1/02-definition-dependencies.md#genlimitmembershiporaclemk) | constructor | `GenLimitLean/GenLimit/Core/Basic.lean:38` |
| [`GenLimit.MembershipOracle.query`](../stage1/02-definition-dependencies.md#genlimitmembershiporaclequery) | definition | `GenLimitLean/GenLimit/Core/Basic.lean:39` |
| [`GenLimit.OracleFamily.language`](../stage1/02-definition-dependencies.md#genlimitoraclefamilylanguage) | definition | `GenLimitLean/GenLimit/Core/OracleFamily.lean:18` |
| [`GenLimit.OracleFamily.mk`](../stage1/02-definition-dependencies.md#genlimitoraclefamilymk) | constructor | `GenLimitLean/GenLimit/Core/OracleFamily.lean:17` |
| [`GenLimit.OracleFamily.query`](../stage1/02-definition-dependencies.md#genlimitoraclefamilyquery) | definition | `GenLimitLean/GenLimit/Core/OracleFamily.lean:20` |
| [`GenLimit.OracleFamily.query_spec`](../stage1/02-definition-dependencies.md#genlimitoraclefamilyquery_spec) | theorem: interface only | `GenLimitLean/GenLimit/Core/OracleFamily.lean:21` |
| [`GenLimit.SubsetOracle.mk`](../stage1/02-definition-dependencies.md#genlimitsubsetoraclemk) | constructor | `GenLimitLean/GenLimit/Core/SubsetOracle.lean:13` |
| [`GenLimit.SubsetOracle.query`](../stage1/02-definition-dependencies.md#genlimitsubsetoraclequery) | definition | `GenLimitLean/GenLimit/Core/SubsetOracle.lean:14` |
| [`GenLimit.Support.OracleSearchProgram`](../stage1/02-definition-dependencies.md#genlimitsupportoraclesearchprogram) | inductive | `GenLimitLean/GenLimit/Support/OracleSearchProgram.lean:45` |
| [`GenLimit.Support.TruthTableProgram`](../stage1/02-definition-dependencies.md#genlimitsupporttruthtableprogram) | inductive | `GenLimitLean/GenLimit/Support/OracleTruthTable.lean:14` |
| [`GenLimit.Support.binaryWords`](../stage1/02-definition-dependencies.md#genlimitsupportbinarywords) | definition | `GenLimitLean/GenLimit/Support/BinaryWords.lean:7` |
| [`GenLimit.Support.boundedAll`](../stage1/02-definition-dependencies.md#genlimitsupportboundedall) | definition | `GenLimitLean/GenLimit/Support/ComputableSearch.lean:13` |
| [`GenLimit.Support.enumeratedSet`](../stage1/02-definition-dependencies.md#genlimitsupportenumeratedset) | definition | `GenLimitLean/GenLimit/Support/FiniteEnumeration.lean:15` |
| [`GenLimit.Support.firstTrue`](../stage1/02-definition-dependencies.md#genlimitsupportfirsttrue) | definition | `GenLimitLean/GenLimit/Support/ComputableSearch.lean:67` |
| [`GenLimit.Support.lastTrue`](../stage1/02-definition-dependencies.md#genlimitsupportlasttrue) | definition | `GenLimitLean/GenLimit/Support/ComputableLastSearch.lean:7` |
| [`GenLimit.Support.tableLookup`](../stage1/02-definition-dependencies.md#genlimitsupporttablelookup) | definition | `GenLimitLean/GenLimit/Support/OracleTruthTable.lean:24` |
| [`GenLimit.DiscreteIID.positiveGeometric._proof_1`](../stage1/02-definition-dependencies.md#genlimitdiscreteiidpositivegeometric_proof_1) | theorem: interface only | `GenLimitLean/GenLimit/Support/FullSupportDistribution.lean:generated` |
| [`GenLimit.DiscreteIID.positiveGeometric._proof_2`](../stage1/02-definition-dependencies.md#genlimitdiscreteiidpositivegeometric_proof_2) | theorem: interface only | `GenLimitLean/GenLimit/Support/FullSupportDistribution.lean:generated` |
| [`GenLimit.DiscreteIID.positiveGeometric._proof_3`](../stage1/02-definition-dependencies.md#genlimitdiscreteiidpositivegeometric_proof_3) | theorem: interface only | `GenLimitLean/GenLimit/Support/FullSupportDistribution.lean:generated` |
| [`GenLimit.DiscreteIID.samples.match_1`](../stage1/02-definition-dependencies.md#genlimitdiscreteiidsamplesmatch_1) | definition | `GenLimitLean/GenLimit/Support/DiscreteIID.lean:generated` |
| [`GenLimit.Gold.Informant.InformantDatum`](../stage1/02-definition-dependencies.md#genlimitgoldinformantinformantdatum) | definition | `GenLimitLean/GenLimit/Paper00_LanguageIdentification/Informant/Model.lean:25` |
| [`GenLimit.HallucinationModeCollapse.AdmissibleSublinearExponent.mk`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapseadmissiblesublinearexponentmk) | constructor | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/UniversalRates.lean:26` |
| [`GenLimit.HallucinationModeCollapse.SupportGenerator.mk`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesupportgeneratormk) | constructor | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:27` |
| [`GenLimit.HallucinationModeCollapse.SupportGenerator.support`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsesupportgeneratorsupport) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean:28` |
| [`GenLimit.HallucinationModeCollapse.TokenGenerator.initialAux`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetokengeneratorinitialaux) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/TokenGeneration.lean:23` |
| [`GenLimit.HallucinationModeCollapse.TokenGenerator.inputCode`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetokengeneratorinputcode) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/TokenGeneration.lean:27` |
| [`GenLimit.HallucinationModeCollapse.TokenGenerator.machine`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetokengeneratormachine) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/TokenGeneration.lean:20` |
| [`GenLimit.HallucinationModeCollapse.TokenGenerator.mk`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetokengeneratormk) | constructor | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/TokenGeneration.lean:19` |
| [`GenLimit.HallucinationModeCollapse.TokenGenerator.nextLaw`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetokengeneratornextlaw) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/TokenGeneration.lean:29` |
| [`GenLimit.HallucinationModeCollapse.TokenGenerator.readOutput`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetokengeneratorreadoutput) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/TokenGeneration.lean:21` |
| [`GenLimit.HallucinationModeCollapse.TokenGenerator.wordExperiment`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetokengeneratorwordexperiment) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/TokenGeneration.lean:62` |
| [`GenLimit.HallucinationModeCollapse.TokenGenerator.wordProbability`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetokengeneratorwordprobability) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/TokenGeneration.lean:92` |
| [`GenLimit.HallucinationModeCollapse.statisticalSupportView._proof_1`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsestatisticalsupportview_proof_1) | theorem: interface only | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/UnambiguousModel.lean:generated` |
| [`GenLimit.Support.OracleSearchProgram.Terminates`](../stage1/02-definition-dependencies.md#genlimitsupportoraclesearchprogramterminates) | definition | `GenLimitLean/GenLimit/Support/OracleSearchProgram.lean:59` |
| [`GenLimit.Support.OracleSearchProgram.mk`](../stage1/02-definition-dependencies.md#genlimitsupportoraclesearchprogrammk) | constructor | `GenLimitLean/GenLimit/Support/OracleSearchProgram.lean:45` |
| [`GenLimit.Support.OracleSearchProgram.output`](../stage1/02-definition-dependencies.md#genlimitsupportoraclesearchprogramoutput) | definition | `GenLimitLean/GenLimit/Support/OracleSearchProgram.lean:48` |
| [`GenLimit.Support.OracleSearchProgram.partialRun`](../stage1/02-definition-dependencies.md#genlimitsupportoraclesearchprogrampartialrun) | definition | `GenLimitLean/GenLimit/Support/OracleSearchProgram.lean:56` |
| [`GenLimit.Support.OracleSearchProgram.queries`](../stage1/02-definition-dependencies.md#genlimitsupportoraclesearchprogramqueries) | definition | `GenLimitLean/GenLimit/Support/OracleSearchProgram.lean:46` |
| [`GenLimit.Support.OracleSearchProgram.run`](../stage1/02-definition-dependencies.md#genlimitsupportoraclesearchprogramrun) | definition | `GenLimitLean/GenLimit/Support/OracleSearchProgram.lean:68` |
| [`GenLimit.Support.OracleSearchProgram.run_dom`](../stage1/02-definition-dependencies.md#genlimitsupportoraclesearchprogramrun_dom) | theorem: interface only | `GenLimitLean/GenLimit/Support/OracleSearchProgram.lean:62` |
| [`GenLimit.Support.OracleSearchProgram.stage`](../stage1/02-definition-dependencies.md#genlimitsupportoraclesearchprogramstage) | definition | `GenLimitLean/GenLimit/Support/OracleSearchProgram.lean:53` |
| [`GenLimit.Support.RandomBitMachine.Action`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachineaction) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:21` |
| [`GenLimit.Support.RandomBitMachine.Configuration`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachineconfiguration) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:23` |
| [`GenLimit.Support.RandomBitMachine.Machine`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachine) | inductive | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:25` |
| [`GenLimit.Support.TruthTableProgram.mk`](../stage1/02-definition-dependencies.md#genlimitsupporttruthtableprogrammk) | constructor | `GenLimitLean/GenLimit/Support/OracleTruthTable.lean:14` |
| [`GenLimit.Support.TruthTableProgram.output`](../stage1/02-definition-dependencies.md#genlimitsupporttruthtableprogramoutput) | definition | `GenLimitLean/GenLimit/Support/OracleTruthTable.lean:17` |
| [`GenLimit.Support.TruthTableProgram.queries`](../stage1/02-definition-dependencies.md#genlimitsupporttruthtableprogramqueries) | definition | `GenLimitLean/GenLimit/Support/OracleTruthTable.lean:15` |
| [`GenLimit.Support.TruthTableProgram.run`](../stage1/02-definition-dependencies.md#genlimitsupporttruthtableprogramrun) | definition | `GenLimitLean/GenLimit/Support/OracleTruthTable.lean:20` |
| [`GenLimit.Support.binaryWords.match_1`](../stage1/02-definition-dependencies.md#genlimitsupportbinarywordsmatch_1) | definition | `GenLimitLean/GenLimit/Support/BinaryWords.lean:generated` |
| [`GenLimit.Support.firstTrue.match_1`](../stage1/02-definition-dependencies.md#genlimitsupportfirsttruematch_1) | definition | `GenLimitLean/GenLimit/Support/ComputableSearch.lean:generated` |
| [`GenLimit.HallucinationModeCollapse.TokenGenerator.Produces.match_1`](../stage1/02-definition-dependencies.md#genlimithallucinationmodecollapsetokengeneratorproducesmatch_1) | definition | `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/TokenGeneration.lean:generated` |
| [`GenLimit.Support.RandomBitMachine.Machine.AlwaysHalts`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachinealwayshalts) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:49` |
| [`GenLimit.Support.RandomBitMachine.Machine.action`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineaction) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:27` |
| [`GenLimit.Support.RandomBitMachine.Machine.advance`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineadvance) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:33` |
| [`GenLimit.Support.RandomBitMachine.Machine.allFinished`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineallfinished) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Effective.lean:82` |
| [`GenLimit.Support.RandomBitMachine.Machine.boundProgram`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineboundprogram) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Effective.lean:109` |
| [`GenLimit.Support.RandomBitMachine.Machine.boundProgram_terminates`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineboundprogram_terminates) | theorem: interface only | `GenLimitLean/GenLimit/Support/RandomBitMachine/Effective.lean:121` |
| [`GenLimit.Support.RandomBitMachine.Machine.boundedLaw`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineboundedlaw) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Probability.lean:22` |
| [`GenLimit.Support.RandomBitMachine.Machine.boundedResults`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineboundedresults) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Effective.lean:60` |
| [`GenLimit.Support.RandomBitMachine.Machine.evaluate`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineevaluate) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:41` |
| [`GenLimit.Support.RandomBitMachine.Machine.executionBound`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineexecutionbound) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Effective.lean:127` |
| [`GenLimit.Support.RandomBitMachine.Machine.fairCoin`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachinefaircoin) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Probability.lean:17` |
| [`GenLimit.Support.RandomBitMachine.Machine.halted`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachinehalted) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Effective.lean:71` |
| [`GenLimit.Support.RandomBitMachine.Machine.initial`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineinitial) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:26` |
| [`GenLimit.Support.RandomBitMachine.Machine.mk`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachinemk) | constructor | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:25` |
| [`GenLimit.Support.RandomBitMachine.Machine.outputLaw`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineoutputlaw) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Probability.lean:54` |
| [`GenLimit.Support.RandomBitMachine.Machine.outputOrZero`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineoutputorzero) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Probability.lean:52` |
| [`GenLimit.Support.RandomBitMachine.Machine.run`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachinerun) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:46` |
| [`GenLimit.Support.RandomBitMachine.Machine.tapePrefix`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachinetapeprefix) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:44` |
| [`GenLimit.Support.RandomBitMachine.Machine.advance.match_1`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineadvancematch_1) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:generated` |
| [`GenLimit.Support.RandomBitMachine.Machine.advance.match_3`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineadvancematch_3) | definition | `GenLimitLean/GenLimit/Support/RandomBitMachine/Basic.lean:generated` |
| [`GenLimit.Support.RandomBitMachine.Machine.boundProgram._proof_1`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineboundprogram_proof_1) | theorem: interface only | `GenLimitLean/GenLimit/Support/RandomBitMachine/Effective.lean:generated` |
| [`GenLimit.Support.RandomBitMachine.Machine.boundProgram._proof_2`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachineboundprogram_proof_2) | theorem: interface only | `GenLimitLean/GenLimit/Support/RandomBitMachine/Effective.lean:generated` |
| [`GenLimit.Support.RandomBitMachine.Machine.fairCoin._proof_1`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachinefaircoin_proof_1) | theorem: interface only | `GenLimitLean/GenLimit/Support/RandomBitMachine/Probability.lean:generated` |
| [`GenLimit.Support.RandomBitMachine.Machine.fairCoin._proof_2`](../stage1/02-definition-dependencies.md#genlimitsupportrandombitmachinemachinefaircoin_proof_2) | theorem: interface only | `GenLimitLean/GenLimit/Support/RandomBitMachine/Probability.lean:generated` |

## Target dossiers

Each dossier's exact type is copied programmatically from `01-target-statements.md`; the prose expands definition values from the supplied dependency closure. Logical conjunctions are listed as separate obligations, not treated as alternative claims. In every skeleton, family and algorithm parameters already written to the left are permitted dependencies of witnesses on the right. No statistical learner receives `p`, the target index, or a future stream as runtime input.

### 1. GenLimit.HallucinationModeCollapse.Results.theorem_3_1

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:60`.

**Exact exported type**

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat),
  GenLimit.HallucinationModeCollapse.NontrivialCollection C →
    And
      (Or
        (And (GenLimit.HallucinationModeCollapse.AlmostExponentialIdentifiable C)
          (Not (GenLimit.HallucinationModeCollapse.NoIdentificationRate C)))
        (And (Not (GenLimit.HallucinationModeCollapse.AlmostExponentialIdentifiable C))
          (GenLimit.HallucinationModeCollapse.NoIdentificationRate C)))
      (And
        (Iff (GenLimit.HallucinationModeCollapse.AlmostExponentialIdentifiable C) (GenLimit.Angluin.ConditionTwo.{0} C))
        (∀ (A : GenLimit.HallucinationModeCollapse.StatisticalIdentifier),
          ∃ i p,
            And (GenLimit.HallucinationModeCollapse.ValidDistribution C i p)
              (∃ᶠ (n : Nat) in Filter.atTop.{0},
                LE.le.{0} (Real.exp (HMul.hMul.{0, 0, 0} (-2) ↑n))
                  (GenLimit.HallucinationModeCollapse.identificationError C A p i n))))
```

For every indexed family `C` of subsets of the naturals, if two distinct family languages overlap, the theorem asserts three components together.

1. Exactly one of two explicitly paired branches holds: `(AlmostExponentialIdentifiable C ∧ ¬ NoIdentificationRate C)` or `(¬ AlmostExponentialIdentifiable C ∧ NoIdentificationRate C)`. The negative clauses are part of the stated result; the disjunction is not merely an unqualified excluded middle.
2. `AlmostExponentialIdentifiable C ↔ Angluin.ConditionTwo C`.
3. For every randomized semantic identifier `A`, there are one index `i` and one full-support law `p` for `Cᵢ` such that `e_id(C,A,p,i,n) ≥ exp(-2n)` at arbitrarily large natural `n`.

Quantifier/dependency skeleton:

- `∀ C, NontrivialCollection C → [(P ∧ ¬Q) ∨ (¬P ∧ Q)] ∧ [P ↔ ∀i∃T IsTellTale C i T] ∧ [∀A∃i,p (Valid C i p ∧ ∀N∃n≥N, exp(-2n) ≤ e_id(...,n))]`.
- Inside `P`: `∀g, [g≥0 ∧ g=o(n) ∧ g→∞] → ∃A_g, ∀i,p, Valid → ∃D_{g,A_g,i,p}>0, ∀n, e_id(C,pure∘A_g,p,i,n) ≤ D exp(-g(n))`.
- Inside `Q`: `∀A, ∃i,p, Valid ∧ limsup e_id > 0`.

The almost-exponential learner is deterministic but need not be computable, and may depend on the requested `g`. The lower bound ranges over all PMF-valued identifiers, including arbitrary noncomputable ones. Its `i,p` may depend on `A`, but not on `n`; its exponent 2 is fixed, with no free prefactor. It does not say every sample size has that error. It coexists with convergence to zero in the positive branch. The nontriviality condition supplies no membership oracle or infinitude assumption. Repeated indices are allowed and do not count as identification mistakes. Empty languages have no valid positive-data distribution or presenting stream. There is no named successful learner in this theorem, no oracle-relative or ordinary computability assertion, and no uniform rate over target laws. Interpretation uncertainties: none beyond the declared external boundary.

### 2. GenLimit.HallucinationModeCollapse.Results.theorem_3_2

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:88`.

**Exact exported type**

```lean
∀ (O : GenLimit.OracleFamily),
  And
    (GenLimit.HallucinationModeCollapse.ExponentialGenerates (GenLimit.OracleFamily.language O)
      (GenLimit.HallucinationModeCollapse.deterministicIdentifier (GenLimit.HallucinationModeCollapse.certifiedKM O)))
    (And
      (Computable₂.{0, 0, 0} (GenLimit.OracleFamily.query O) →
        Computable.{0, 0} (GenLimit.HallucinationModeCollapse.certifiedKM O))
      (GenLimit.HallucinationModeCollapse.GenerationNontrivial (GenLimit.OracleFamily.language O) →
        ∀ (G : GenLimit.HallucinationModeCollapse.StatisticalGenerator),
          ∃ i p,
            And (GenLimit.HallucinationModeCollapse.ValidDistribution (GenLimit.OracleFamily.language O) i p)
              (∃ c,
                And (LT.lt.{0} 0 c)
                  (∃ D,
                    And (LT.lt.{0} 0 D)
                      (∃ᶠ (n : Nat) in Filter.atTop.{0},
                        LE.le.{0} (HMul.hMul.{0, 0, 0} D (Real.exp (HMul.hMul.{0, 0, 0} (Neg.neg.{0} c) ↑n)))
                          (GenLimit.HallucinationModeCollapse.generationError (GenLimit.OracleFamily.language O) G p i
                            n))))))
```

For every `OracleFamily O`, put `C = O.language` and `F = certifiedKM O`. The family already has infinitely many elements in each language, and `F` is the specific total oracle-search construction described in the glossary. Three conjuncts hold.

1. Its deterministic output law `G xs = pure (F xs)` has exponentially decreasing fresh-generation failure for every target and full-support law.
2. If `O.query` is jointly computable in index and item, `F : List Nat → Nat` is ordinarily computable.
3. If `GenerationNontrivial C`, every semantic randomized generator `G` has a target/full-support law and positive constants `c,D` with `e_gen(C,G,p,i,n) ≥ D exp(-c n)` infinitely often.

Skeleton: `∀O, [∀i,p, Valid→∃c>0∃D>0∀n, e_gen(C,pure∘F,p,i,n)≤D exp(-cn)] ∧ [Computable₂ O.query→Computable F] ∧ [GenerationNontrivial C→∀G∃i,p, Valid∧∃c>0∃D>0∀N∃n≥N, D exp(-cn)≤e_gen(C,G,p,i,n)]`.

The upper-bound constants depend on `O,i,p` and the fixed construction. In the lower bound, the adversarial `i,p,c,D` may depend on `O` and `G`, but are chosen before the infinitely-often indices. No computability or support-decision condition restricts the lower-bound `G`. The upper claim holds without `GenerationNontrivial`; that hypothesis is confined to the lower-bound conjunct. The oracle is family membership, not target membership supplied with the true target index; the input list is the sole data argument to `F`. The named output at an empty sample is 0 and need not be successful; the positive prefactor absorbs small sample sizes in the upper bound. Infinitude ensures that a finite observed list never exhausts the target. The error counts both hallucinations and repeats from the training sample; it says nothing about covering the entire unseen target or avoiding prior generated outputs. The exponential lower bound is infinitely often, not all time, and permits an error tending to zero. Interpretation uncertainties: none beyond the declared boundary.

### 3. GenLimit.HallucinationModeCollapse.Results.theorem_3_3

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:104`.

**Exact exported type**

```lean
∀ (O : GenLimit.OracleFamily),
  GenLimit.HallucinationModeCollapse.GenerationNontrivial (GenLimit.OracleFamily.language O) →
    And
      (Not (GenLimit.HallucinationModeCollapse.IdentifiableInLimit (GenLimit.OracleFamily.language O)) →
        ∀ (G : GenLimit.HallucinationModeCollapse.StatisticalGenerator),
          GenLimit.HallucinationModeCollapse.DecidableMOP G →
            GenLimit.HallucinationModeCollapse.NoBreadthRate (GenLimit.OracleFamily.language O) G)
      (And
        (∃ G,
          And (GenLimit.HallucinationModeCollapse.DecidableMOP G)
            (And
              (GenLimit.HallucinationModeCollapse.OracleMOP (GenLimit.HallucinationModeCollapse.generationOracle O) G)
              (And (GenLimit.HallucinationModeCollapse.ExponentialGenerates (GenLimit.OracleFamily.language O) G)
                (Computable₂.{0, 0, 0} (GenLimit.OracleFamily.query O) →
                  GenLimit.HallucinationModeCollapse.HasComputableSampler G))))
        (And
          (GenLimit.HallucinationModeCollapse.IdentifiableInLimit (GenLimit.OracleFamily.language O) →
            GenLimit.HallucinationModeCollapse.CertifiedBreadthPositiveBranch O)
          (∀ (G : GenLimit.HallucinationModeCollapse.StatisticalGenerator),
            ∃ i p,
              And (GenLimit.HallucinationModeCollapse.ValidDistribution (GenLimit.OracleFamily.language O) i p)
                (∃ c,
                  And (LT.lt.{0} 0 c)
                    (∃ D,
                      And (LT.lt.{0} 0 D)
                        (∃ᶠ (n : Nat) in Filter.atTop.{0},
                          LE.le.{0} (HMul.hMul.{0, 0, 0} D (Real.exp (HMul.hMul.{0, 0, 0} (Neg.neg.{0} c) ↑n)))
                            (GenLimit.HallucinationModeCollapse.generationError (GenLimit.OracleFamily.language O) G p i
                              n)))))))
```

Fix `OracleFamily O`, set `C=O.language`, and assume `GenerationNontrivial C`. Four components hold simultaneously.

1. If `¬IdentifiableInLimit C`, every `G` with pointwise `DecidableMOP G` satisfies `NoBreadthRate C G`: some fixed valid `i,p` has `limsup_n breadthError C G p i n > 0`. The assumption is semantic nonidentifiability, not merely absence of a computable identifier.
2. There exists one generator `G` with all four properties: `DecidableMOP G`; `OracleMOP (generationOracle O) G`; `ExponentialGenerates C G`; and `Computable₂ O.query → HasComputableSampler G`. Its support is pointwise decidable even when the family query is not computable. This is an unnamed existential witness in this target type; the theorem does not equate it with the positive-breadth construction in the next component.
3. If `IdentifiableInLimit C`, `CertifiedBreadthPositiveBranch O` holds, with the full expansion immediately below.
4. For every generator `G`, there are valid `i,p` and positive `c,D` such that `e_gen(C,G,p,i,n) ≥ D exp(-cn)` infinitely often. No MOP, sampler, stability, or computability premise restricts this last quantifier.

Top-level skeleton: `∀O, GenerationNontrivial C → [(¬I→∀G, DM G→NB C G) ∧ (∃G, DM G∧OM O G∧EG C G∧(CQ O→Sampler G)) ∧ (I→CBPB O) ∧ (∀G∃i,p,c,D, Valid∧c>0∧D>0∧∀N∃n≥N, D exp(-cn)≤e_gen(...,n))]`. The existential in component 2 is before any target/law in its rate guarantee; the distribution-dependent constants inside `EG` are after `i,p`.

Full positive branch: there exists **one** `emit : Nat → Nat → Option Nat` such that, for every index, its enumerated set is a finite tell-tale. Define `A_emit` by the membership-and-emission truth-table program and `B = tellTaleBreadthGenerator O emit`. This same `emit` and same `B` satisfy all of:

- `OracleMOP (generationOracle O) B` (pointwise programs; the oracle here is family membership, not the combined emission oracle).
- `ExponentialBreadth C B`: `∀i,p, Valid→∃c>0∃D>0∀n, breadthError≤D exp(-cn)`.
- `∀g, AdmissibleSublinearExponent g → AchievesBreadthRate C B (n↦exp(-g(n)))`: the generator is chosen **before** `g`, unlike the learner quantifier in `AlmostExponentialIdentifiable`.
- `Computable₂ O.query → DecidableMOP B`.
- `Computable₂ O.query → Computable₂ emit → [HasComputableSampler B ∧ UniformDecidableMOP B]`.

The enumerator's computability is conditional and not part of its initial existential guarantee. Ordinary computability of family membership alone gives only the stated pointwise support decision property, not automatically a joint sampler or uniform support decider. The named breadth construction is defined using both membership and tell-tale emissions to identify an index and then exact sampling from the selected unseen language. No learner receives the target or the sample law. Its statistical loss is failure of exact support equality, distinct from one-output generation loss. Component 2 and the breadth-positive certificate need not use the same witness. All statistical upper bounds are for every `n`; limsup failure and infinitely-often exponential lower bounds are different claims and can have different bad distributions. Every language is infinite, so the desired fresh support is nonempty at every finite history consistent with that target. The finite-intersection hypothesis applies to the whole theorem as written, even where a component might logically need less. Interpretation uncertainties: none beyond the declared boundary.

### 4. GenLimit.HallucinationModeCollapse.Results.theorem_3_4

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:119`.

**Exact exported type**

```lean
∀ (G : GenLimit.HallucinationModeCollapse.TokenGenerator)
  (hG :
    GenLimit.Support.RandomBitMachine.Machine.AlwaysHalts
      (GenLimit.HallucinationModeCollapse.TokenGenerator.machine G)),
  ∃ query,
    And (Computable.{0, 0} query)
      (∀ (word : List.{0} Nat),
        Iff (Eq.{1} (query word) Bool.true)
          (LT.lt.{0} 0 (GenLimit.HallucinationModeCollapse.TokenGenerator.wordProbability G hG word)))
```

For every bundled token generator `G` and proof `hG` that its machine halts on every input and every bit tape, there exists a single ordinarily computable Boolean function on finite natural-number words deciding whether that generator emits exactly the word and then stops with positive probability.

Skeleton: `∀G : TokenGenerator, ∀hG : G.machine.AlwaysHalts, ∃query : List Nat → Bool, Computable query ∧ ∀word, [query word=true ↔ 0 < wordProbability G hG word]`.

The witness depends on the fixed generator and may use the supplied total-halting premise; it precedes and works jointly for every word. This is uniform in the word for each fixed `G`, but the type does not assert a computable operation taking a code for arbitrary `G` and a proof of halting to a decider. There is no external oracle here. The machine's initial/action functions and the output decoder are already computable by their constructors. The hypothesis means every tape terminates for each machine invocation, stronger than almost-sure termination, with the halting time existentially after `input,tape`. The supplied definitions turn this into a searchable finite-time bound per input using all finite bit strings. Neither a globally fixed time bound across inputs nor an expected-time complexity bound is claimed.

For an empty word, success means the first decoded output is `none`. For a nonempty word, each token must match in order, the stem is extended after each token, auxiliary state changes are honored, and a final stop is required. Tokens are naturals; no finite token alphabet is imposed. There are no training samples, target language, validity/support-of-training-law assumptions, loss rates, asymptotic thresholds, or family identification claims. The machine may always emit another token on successive calls, so all finite words can have probability zero even though each invocation always halts; then the constant-false query satisfies the conclusion. This result decides positivity, not exact real probabilities, and does not assert that the finite-word weights sum to one. Interpretation uncertainties: none beyond the declared boundary.

### 5. GenLimit.HallucinationModeCollapse.Results.theorem_3_5

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:129`.

**Exact exported type**

```lean
∀ (O : GenLimit.OracleFamily),
  And
    (Not (GenLimit.HallucinationModeCollapse.IdentifiableInLimit (GenLimit.OracleFamily.language O)) →
      ∀ (G : GenLimit.HallucinationModeCollapse.StatisticalGenerator),
        GenLimit.HallucinationModeCollapse.DecidableMOP G →
          And
            (Not
              (GenLimit.HallucinationModeCollapse.FreshBreadthInLimit
                (GenLimit.HallucinationModeCollapse.statisticalSupportView G) (GenLimit.OracleFamily.language O)))
            (Not
              (GenLimit.HallucinationModeCollapse.RepeatingBreadthInLimit
                (GenLimit.HallucinationModeCollapse.statisticalSupportView G) (GenLimit.OracleFamily.language O))))
    (And
      (GenLimit.HallucinationModeCollapse.IdentifiableInLimit (GenLimit.OracleFamily.language O) →
        GenLimit.HallucinationModeCollapse.CertifiedOnlineBreadthPositiveBranch O)
      (Computable₂.{0, 0, 0} (GenLimit.OracleFamily.query O) →
        And
          (Iff (GenLimit.HallucinationModeCollapse.IdentifiableInLimit (GenLimit.OracleFamily.language O))
            (∃ G,
              And (GenLimit.HallucinationModeCollapse.DecidableMOP G)
                (GenLimit.HallucinationModeCollapse.FreshBreadthInLimit
                  (GenLimit.HallucinationModeCollapse.statisticalSupportView G) (GenLimit.OracleFamily.language O))))
          (Iff (GenLimit.HallucinationModeCollapse.IdentifiableInLimit (GenLimit.OracleFamily.language O))
            (∃ G,
              And (GenLimit.HallucinationModeCollapse.DecidableMOP G)
                (GenLimit.HallucinationModeCollapse.RepeatingBreadthInLimit
                  (GenLimit.HallucinationModeCollapse.statisticalSupportView G) (GenLimit.OracleFamily.language O))))))
```

For every `OracleFamily O`, set `C=O.language` and `I=IdentifiableInLimit C`. There are three main conjuncts, with no `GenerationNontrivial` premise.

1. If `¬I`, then for every `G` with pointwise `DecidableMOP G`, **both** `¬FreshBreadthInLimit (statisticalSupportView G) C` and `¬RepeatingBreadthInLimit (statisticalSupportView G) C` hold.
2. If `I`, the full named certificate `CertifiedOnlineBreadthPositiveBranch O` holds.
3. If `O.query` is jointly computable, `I` is equivalent to the existence of a pointwise support-decidable statistical generator with fresh breadth in the limit, and separately equivalent to the existence of one with repeating breadth in the limit. Those two existential witnesses are not required to coincide. Their existential conditions in this conjunct do not include `HasComputableSampler` or `UniformDecidableMOP`.

Top-level skeleton: `∀O, [(¬I→∀G, DM G→(¬Fresh G C∧¬Repeat G C)) ∧ (I→COBPB O) ∧ (CQ O→[(I↔∃G,DM G∧Fresh G C)∧(I↔∃G,DM G∧Repeat G C)])]`.

Full online positive certificate: there is one enumerator `emit` such that every `enumeratedSet emit i` is a finite tell-tale. Define `A` as `TruthTableProgram.run identificationProgram (identificationOracle (familyMembership O) emit)`, `F = identifiedBreadth O A`, and `R = identifiedRepeatingBreadth O A`. For those same choices all the following hold:

- `FreshBreadthInLimit (statisticalSupportView F) C`.
- `RepeatingBreadthInLimit (statisticalSupportView R) C`.
- `OracleMOP (generationOracle O) F` and, separately, `OracleMOP (generationOracle O) R`.
- If `Computable₂ O.query`, then `DecidableMOP F ∧ DecidableMOP R`.
- If `Computable₂ O.query` and `Computable₂ emit`, then `HasComputableSampler F ∧ UniformDecidableMOP F ∧ HasComputableSampler R ∧ UniformDecidableMOP R`.

The enumerator is not asserted computable. The common `A` uses both membership and tell-tale emissions, while `F` removes observed elements and `R` uses an empty removal list. These two generators have different support requirements and are not declared equal. The oracle-support assertions remain pointwise in history. The condition on `emit` is necessary for the stated effective sampling/uniform-support consequences; a semantic identifying learner alone has no effectiveness certificate.

For each success predicate, `∀z stream, range stream=C_z → ∃T_{z,stream}∀t≥T, support = required set`. There is no common time bound, no probability law, and no statistical rate in this target. Negating one predicate yields some presenting stream with failures at arbitrarily large times; the bad stream for fresh breadth may differ from the one for repeating breadth. The theorem does not assert failure at every time or one history witnessing both failures. Every target is infinite by the family bundle, so fresh-support equality never asks a PMF to have empty support at finite time. Duplicates in indices or stream values are allowed and handled extensionally. Interpretation uncertainties: none beyond the declared boundary.

### 6. GenLimit.HallucinationModeCollapse.Results.theorem_3_6

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:147`.

**Exact exported type**

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat),
  Not (GenLimit.HallucinationModeCollapse.IdentifiableInLimit C) →
    ∀ (G : GenLimit.HallucinationModeCollapse.StatisticalGenerator),
      GenLimit.HallucinationModeCollapse.StatisticalStable G C →
        GenLimit.HallucinationModeCollapse.DecidableMOP G → GenLimit.HallucinationModeCollapse.NoUnambiguousRate C G
```

For every indexed family `C`, if it is not semantically identifiable from positive presenting streams, every statistical generator whose support stabilizes on each such stream and whose support at each fixed history is ordinarily decidable has nonvanishing statistical unambiguity failure on some full-support target distribution.

Skeleton: `∀C, ¬I(C) → ∀G, StatisticalStable G C → DecidableMOP G → ∃i,p, [support p=Cᵢ ∧ 0<limsup_n P_{xs~p^n}(¬UnambiguousAt C i (support(G xs)))]`.

`i,p` may depend on `C,G` and are fixed across the limsup. There is no membership oracle, computable sampler, joint support decider, or computability premise on the generator. The support-stability premise is universal over **all** presenting streams: on each one, some threshold makes all later supports equal to one another. It imposes no direct bound on samplewise probabilities or relation between the stabilized support and the true language. The conclusion uses strict extended-cardinality comparisons with each extensionally different family language. Ties, including two infinite distances, count as failure; duplicate target indices do not create comparisons. A positive limsup supplies persistent error along a subsequence, with no claimed numerical rate and no guarantee of an eventual positive lower bound at all times. The probability is over the observed i.i.d. list only, not a sampled output token. There is no distinctness, infinitude, or nontriviality condition beyond `¬I(C)`. Empty-target statistical obligations have no valid PMF; the existential conclusion selects a valid, hence nonempty, target. A family with one distinct language makes unambiguity vacuous, but it is also semantically identifiable and cannot meet the leading premise. Interpretation uncertainties: none beyond the declared boundary.

### 7. GenLimit.HallucinationModeCollapse.Results.theorem_3_7

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:155`.

**Exact exported type**

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat),
  Not (GenLimit.HallucinationModeCollapse.IdentifiableInLimit C) →
    ∀ (G : GenLimit.HallucinationModeCollapse.StatisticalGenerator),
      GenLimit.HallucinationModeCollapse.StatisticalStable G C →
        GenLimit.HallucinationModeCollapse.DecidableMOP G →
          Not
            (GenLimit.HallucinationModeCollapse.UnambiguousInLimit
              (GenLimit.HallucinationModeCollapse.statisticalSupportView G) C)
```

Under the same family nonidentifiability, streamwise support stability, and pointwise support-decision assumptions as dossier 6, the generator fails eventual unambiguity on all presenting streams.

Skeleton: `∀C, ¬I(C) → ∀G, StatisticalStable G C → DecidableMOP G → ¬[∀z stream, Presents stream C_z → ∃T∀t≥T, UnambiguousAt C z (support(G(textPrefix stream t)))]`.

In classical quantifier form, the conclusion supplies `∃z stream, Presents stream C_z ∧ ∀T∃t≥T, ¬UnambiguousAt C z (support(G(prefix_t)))`. The index and stream depend on `C,G` and are selected once; each later failing time may depend on the proposed threshold. It asserts arbitrarily late failures, not all-time failure. It does not state a distributional lower bound or a rate; the support-stability premise is still about every presenting stream, and not about equality of probabilities. The learner sees only the length-`t` prefix at time `t`, and no target index or future stream is an argument of `G`. There is no oracle or sampler requirement. Support distances, duplicate-language exclusions, and infinite-distance ties have exactly the meanings in the glossary and dossier 6. A presenting stream cannot have an empty target, so any witness to this negation has a nonempty target. No named construction, common threshold over streams, or effective extraction of the bad stream is asserted. Interpretation uncertainties: none beyond the declared boundary.

### 8. GenLimit.HallucinationModeCollapse.Results.theorem_3_8

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:165`.

**Exact exported type**

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat),
  Not (GenLimit.HallucinationModeCollapse.IdentifiableInLimit C) →
    ∀ (G : GenLimit.HallucinationModeCollapse.StatisticalGenerator),
      GenLimit.HallucinationModeCollapse.StatisticalStable G C →
        GenLimit.HallucinationModeCollapse.DecidableMOP G →
          GenLimit.HallucinationModeCollapse.NoApproximateBreadthRate C G
```

For a semantically nonidentifiable indexed family, any generator with support stability on every presenting stream and pointwise decidable supports has nonvanishing statistical failure of approximate breadth for some full-support target law.

Skeleton: `∀C, ¬I(C) → ∀G, StatisticalStable G C → DecidableMOP G → ∃i,p, [support p=Cᵢ ∧ 0<limsup_n P_{xs~p^n}(¬[support(G xs)⊆Cᵢ ∧ Set.Finite(Cᵢ \ support(G xs))]) ]`.

The fixed `i,p` may depend on `C,G`, but not on `n`. Failure means either some support element lies outside the target or infinitely many target elements are omitted. This is a Boolean event over sample histories, not the chance that a single generated output is wrong or a small missing-mass guarantee. The approximate-breadth success predicate includes neither freshness nor a bound on the number of omitted elements. In a finite target, finiteness of omissions is automatic and the predicate reduces to support containment. A PMF's support is nonempty, although an abstract set satisfying `ApproximateBreadthAt` could be empty for finite targets. The theorem does not assume infinite languages or a membership oracle. Pointwise computable support queries may vary non-effectively with the history; no ordinary computability of the generator or a common sampler is implied. Positive limsup is kept distinct from a limit or all-late-time lower bound. Empty targets admit no valid law, so the existential bad target is nonempty. Duplicates among family members are permitted. Interpretation uncertainties: none beyond the declared boundary.

### 9. GenLimit.HallucinationModeCollapse.Results.theorem_3_9

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:173`.

**Exact exported type**

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat),
  Not (GenLimit.HallucinationModeCollapse.IdentifiableInLimit C) →
    ∀ (G : GenLimit.HallucinationModeCollapse.StatisticalGenerator),
      GenLimit.HallucinationModeCollapse.StatisticalStable G C →
        GenLimit.HallucinationModeCollapse.DecidableMOP G →
          Not
            (GenLimit.HallucinationModeCollapse.ApproximateBreadthInLimit
              (GenLimit.HallucinationModeCollapse.statisticalSupportView G) C)
```

Under the same premises as dossier 8, the generator cannot eventually have support contained in the target with only finitely many target omissions on every presenting stream.

Skeleton: `∀C, ¬I(C) → ∀G, StatisticalStable G C → DecidableMOP G → ¬[∀z stream, Presents stream C_z → ∃T∀t≥T, support(G(prefix_t))⊆C_z ∧ Set.Finite(C_z \ support(G(prefix_t)))]`.

Equivalently, there is an index and a presenting stream such that for every proposed threshold there is a later time when support containment fails or infinitely many target elements are missing. The failure alternative can vary with time. The conclusion is not that one particular target element remains forever missing, that infinitely many target elements are missing at every time, or that the generator produces an invalid element on every late invocation. The finite omission sets allowed in the positive predicate may vary across times; only the separate stability assumption forces eventual equality of the actual supports on each stream. The threshold and bad-stream witnesses are semantic and need not be effectively obtainable. There is no sample distribution, rate, oracle, or computable-sampling claim in this statement. The observed list is the only data input, and repeated observations cause no issue because omissions are set differences. Empty languages have no presenting stream and cannot be witnesses to the negated universal property. For finite targets, the omitted-set condition is automatic; for infinite targets, cofinite support within the target is required. Interpretation uncertainties: none beyond the declared boundary.

### 10. GenLimit.HallucinationModeCollapse.Results.proposition_3_10

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:183`.

**Exact exported type**

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat) (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle.{0} C),
  GenLimit.Angluin.ConditionTwo.{0} C →
    And
      (GenLimit.HallucinationModeCollapse.ExponentialIdentifies C
        (GenLimit.HallucinationModeCollapse.deterministicIdentifier
          (GenLimit.HallucinationModeCollapse.subsetIdentifier O S)))
      (Computable₂.{0, 0, 0} (GenLimit.MembershipOracle.query O) →
        Computable₂.{0, 0, 0} (GenLimit.SubsetOracle.query.{0} S) →
          Computable.{0, 0} (GenLimit.HallucinationModeCollapse.subsetIdentifier O S))
```

For every family `C`, a correct membership oracle `O`, and a correct subset oracle `S`, if each indexed language has a finite tell-tale in the sense of `Angluin.ConditionTwo`, the specific learner `subsetIdentifier O S` has exponential statistical identification error. Additionally, if both oracles are jointly ordinarily computable, that same learner is ordinarily computable.

Skeleton: `∀C, ∀O : MembershipOracle C, ∀S : SubsetOracle C, ConditionTwo C → [(∀i,p, Valid C i p→∃c>0∃D>0∀n, e_id(C,pure∘subsetIdentifier O S,p,i,n)≤D exp(-cn)) ∧ (Computable₂ O.query→Computable₂ S.query→Computable (subsetIdentifier O S))]`.

The rate constants may depend on `C,O,S,i,p`, but not on `n`. The learner itself is fixed before the target distribution is chosen. Its only data argument is the observed ordered list. At length `n`, it uses membership for candidate indices `< n` and inclusion queries `C_j⊆C_k` for `k<j<n`, then selects the largest consistent candidate included in every earlier consistent candidate. The questions form a finite truth table known from the list; their answers need not be computable until the two explicit hypotheses are supplied. The target index, distribution, and tell-tales are not runtime inputs. A proof of the tell-tale condition is a hypothesis of the guarantee, not a finite tell-tale enumeration passed to this named function.

The claim does not require infinite languages, finitely many distinct languages, finite targets, computable tell-tales, or a computable membership/subset oracle without the stated conditional. The family can contain empty languages and repeated indices. Identifying any equal language is success, and an empty target has no valid positive-data distribution. At `n=0` the candidate search is empty and defaults to 0; the theorem's all-time error bound still includes that case with a distribution-dependent prefactor. The two computability implications are nested hypotheses inside a conjunct, not assumptions needed for the statistical rate. This theorem concerns identification, not freshness or support breadth. Interpretation uncertainties: none beyond the declared boundary.

### 11. GenLimit.HallucinationModeCollapse.Results.proposition_3_11

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:193`.

**Exact exported type**

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat) (O : GenLimit.MembershipOracle C),
  Set.Finite.{0} (Set.range.{0, 1} C) →
    And
      (GenLimit.HallucinationModeCollapse.ExponentialIdentifies C
        (GenLimit.HallucinationModeCollapse.deterministicIdentifier
          (GenLimit.HallucinationModeCollapse.finiteVersionSpaceLearner O)))
      (Computable₂.{0, 0, 0} (GenLimit.MembershipOracle.query O) →
        Computable.{0, 0} (GenLimit.HallucinationModeCollapse.finiteVersionSpaceLearner O))
```

For every family `C` and membership oracle `O`, if the set of distinct family languages `Set.range C` is finite, the named `finiteVersionSpaceLearner O`, wrapped as a deterministic statistical identifier, has exponential identification error. If the membership query is jointly computable, the named learner is ordinarily computable.

Skeleton: `∀C, ∀O : MembershipOracle C, Set.Finite (Set.range C) → [(∀i,p, Valid→∃c>0∃D>0∀n, e_id(C,pure∘finiteVersionSpaceLearner O,p,i,n)≤D exp(-cn)) ∧ (Computable₂ O.query→Computable (finiteVersionSpaceLearner O))]`.

Finite range concerns how many **sets** occur; it does not restrict the natural index set or require the individual languages to be finite. Arbitrarily many duplicate indices can name each set, and the learner need not identify the same numerical index as the target. At list length `n`, the learner checks candidates `j≤n`, tests containment of the sample, and compares finite restrictions `C_j∩[0,n)` against those of every sample-consistent `k≤n`. It selects the least candidate passing those tests, or 0 if none. It is not handed the finite range, its cardinality, a complete list of representatives, a target index, or the unknown law.

All `i,p` with exact target support are covered by one fixed named learner, and constants are allowed to depend on the full law and target; no common exponent or threshold is asserted. The ordinary computability consequence is conditional only on computability of membership and makes no computable choice of a finite-range witness necessary. The family may contain empty or infinite languages; the empty-target statistical obligation is vacuous. A family consisting of one set satisfies the structural premise even if all indices duplicate it. The loss concerns equality of languages, not generated strings or support equality. There is no lower bound or claim about finite-time recognition of a last mind change. Interpretation uncertainties: none beyond the declared boundary.

### 12. GenLimit.HallucinationModeCollapse.Results.proposition_3_12

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:201`.

**Exact exported type**

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat) (O : GenLimit.MembershipOracle C),
  (∀ (i : Nat), Set.Finite.{0} (C i)) →
    And
      (GenLimit.HallucinationModeCollapse.ExponentialIdentifies C
        (GenLimit.HallucinationModeCollapse.deterministicIdentifier
          (GenLimit.HallucinationModeCollapse.finiteVersionSpaceLearner O)))
      (Computable₂.{0, 0, 0} (GenLimit.MembershipOracle.query O) →
        Computable.{0, 0} (GenLimit.HallucinationModeCollapse.finiteVersionSpaceLearner O))
```

For every family `C` and membership oracle `O`, if each `C i` is finite, the **same** `finiteVersionSpaceLearner O` used in proposition 3_11 has exponential statistical identification error. If the membership query is jointly computable, that named learner is ordinarily computable.

Skeleton: `∀C, ∀O : MembershipOracle C, (∀i, Set.Finite Cᵢ) → [(∀i,p, Valid→∃c>0∃D>0∀n, e_id(C,pure∘finiteVersionSpaceLearner O,p,i,n)≤D exp(-cn)) ∧ (Computable₂ O.query→Computable (finiteVersionSpaceLearner O))]`.

Here finiteness is pointwise over languages, not finiteness of the family range. There may be infinitely many distinct finite languages, and there is no uniform bound on their cardinalities or on the magnitudes of their elements. No cardinality, finite enumeration of a language, or bound is supplied to the learner. The named learner uses only the finite membership comparisons described in dossier 11, with candidates `≤ n` and item values `< n`, then the same least-choice/default-0 rule. This is distinct from receiving a presentation of a finite target's entire contents at once.

For a valid nonempty finite target, the unknown sample law gives every one of its elements positive mass; no common minimum mass is assumed across all targets/laws. The exponential constants are chosen after `i,p` and can reflect those masses. The all-natural-`n` bound includes zero, with the prefactor handling initial errors. Empty languages are allowed by the structural premise and have no valid positive-data law, so their rate clauses are vacuous. Duplicate indices are allowed and counted extensionally. The bare membership oracle can be noncomputable; the conditional conclusion supplies ordinary computability when it is computable. No subset oracle, effective tell-tale enumeration, randomized support decision, freshness property, or common rate over the whole family is asserted. Interpretation uncertainties: none beyond the declared boundary.

### 13. GenLimit.HallucinationModeCollapse.Results.theorem_3_13

Source: `GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean:211`.

**Exact exported type**

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat) (O : GenLimit.MembershipOracle C),
  And
    (GenLimit.HallucinationModeCollapse.ExponentialLabeledIdentifies C
      (GenLimit.HallucinationModeCollapse.deterministicLabeledIdentifier
        (GenLimit.HallucinationModeCollapse.labeledEnumerationLearner O)))
    (And
      (Computable₂.{0, 0, 0} (GenLimit.MembershipOracle.query O) →
        Computable.{0, 0} (GenLimit.HallucinationModeCollapse.labeledEnumerationLearner O))
      (GenLimit.HallucinationModeCollapse.NontrivialCollection C →
        ∀ (A : GenLimit.HallucinationModeCollapse.LabeledIdentifier),
          ∃ i p,
            And (GenLimit.HallucinationModeCollapse.ValidLabeledDistribution C i p)
              (∃ᶠ (n : Nat) in Filter.atTop.{0},
                LE.le.{0} (Real.exp (HMul.hMul.{0, 0, 0} (-2) ↑n))
                  (GenLimit.HallucinationModeCollapse.labeledIdentificationError C A p i n))))
```

For every indexed family `C` and correct membership oracle `O`, three components hold.

1. The named `labeledEnumerationLearner O`, wrapped in `deterministicLabeledIdentifier`, has exponentially decreasing identification error for every target and every i.i.d. distribution with full support on **all** correctly labeled natural-number items for that target.
2. If the family membership query is jointly ordinarily computable, the named learner on labeled lists is ordinarily computable.
3. If `NontrivialCollection C`, then every randomized semantic labeled identifier `A` has a target and valid labeled law for which its identification error is at least `exp(-2n)` infinitely often.

Skeleton: `∀C, ∀O : MembershipOracle C, [∀i,p, ValidLabeled C i p→∃c>0∃D>0∀n, e_lab(C,pure∘labeledEnumerationLearner O,p,i,n)≤D exp(-cn)] ∧ [Computable₂ O.query→Computable (labeledEnumerationLearner O)] ∧ [NontrivialCollection C→∀A : LabeledIdentifier, ∃i,p, ValidLabeled C i p∧∀N∃n≥N, exp(-2n)≤e_lab(C,A,p,i,n)]`.

The upper bound needs no tell-tale condition, finite-range assumption, pointwise finiteness, infinitude, or nontriviality. At sample size `n`, the learner compares every observed Boolean label with the membership oracle for each candidate `j<n`, chooses the least fully consistent index, and defaults to 0 if none. The strict bound `<n` includes an empty search at zero. It sees the labeled sample and family membership oracle, not `p` or the target index. Correctly labeled negative items rule out candidates containing an observed nontarget item; correctly labeled positives rule out candidates omitting an observed target item.

`ValidLabeledDistribution` requires support equality with the graph of the true Boolean membership function: each natural appears with its correct label at positive mass, including every negative item when there are any. This is stronger than saying all sampled labels are correct. Empty and universal targets still have valid labeled laws, respectively on all `(x,false)` and all `(x,true)`; their statistical obligations are not vacuous as they are for empty targets under positive-only data. Every correct-label graph is infinite, regardless of target cardinality.

The positive rate constants depend on `C,O,i,p` and are fixed for all `n`; the lower-bound `i,p` depend on `C,A` and are fixed before the infinitely-often times. Its exponent 2 is fixed with no free prefactor. The lower bound is restricted only by the overlap-based `NontrivialCollection`, exactly as written; no broader necessity claim is inferred. Its `A` need not be computable or use the oracle. Index duplicates are not mistakes when the denoted language is right. The lower bound is compatible with convergence to zero, and it is not an all-time inequality. No support-membership or token-generation claim is included. Interpretation uncertainties: none beyond the declared boundary.

## Coverage and limitations

All targets have been reconstructed from their exported types and the relevant project definition values. No decisive missing project or external definition was identified. The status `reconstructed` concerns the meaning of the supplied specification only. It does not certify theorem proofs, run a Lean build, or compare with any paper. No library source or frozen input was modified; this report and its run record are the only requested audit outputs.

| Target (prefix `GenLimit.HallucinationModeCollapse.Results.`) | Source line | Status | Scope of reconstruction |
|---|---:|---|---|
| `theorem_3_1` | 60 | reconstructed | Identification dichotomy, tell-tale equivalence, and fixed-exponent infinitely-often lower bound |
| `theorem_3_2` | 88 | reconstructed | Named fresh generator, conditional computability, and generation lower bound |
| `theorem_3_3` | 104 | reconstructed | Breadth failure branch, existential generator, full named positive certificate, and lower bound |
| `theorem_3_4` | 119 | reconstructed | Computable positivity decider for exact stopped finite words under total per-call halting |
| `theorem_3_5` | 129 | reconstructed | Both online impossibilities, full named positive certificate, and two conditional equivalences |
| `theorem_3_6` | 147 | reconstructed | Positive limsup of statistical unambiguity failure under stability and pointwise MOP |
| `theorem_3_7` | 155 | reconstructed | Failure of eventual streamwise unambiguity under the same assumptions |
| `theorem_3_8` | 165 | reconstructed | Positive limsup of statistical approximate-breadth failure under the same assumptions |
| `theorem_3_9` | 173 | reconstructed | Failure of eventual streamwise approximate breadth under the same assumptions |
| `proposition_3_10` | 183 | reconstructed | Named membership/subset learner under the finite tell-tale condition |
| `proposition_3_11` | 193 | reconstructed | Named finite-restriction learner under finite family range |
| `proposition_3_12` | 201 | reconstructed | Same named learner under pointwise finite languages |
| `theorem_3_13` | 211 | reconstructed | Named full labeled-data learner, conditional computability, and overlap-restricted lower bound |

Checks for this report were textual/data checks only: supplied-file hash agreement, exported project-edge closure, exact signature insertion, and one coverage row per target. No Lean compilation or proof checking was performed, and there are no build warnings or build failures to report because no build was run. The absence of omitted project edges is not an independent audit of each background theorem. Standard external definitions remain the declared library boundary; no follow-up definitions were requested or supplied. Stage 2 was not begun.
