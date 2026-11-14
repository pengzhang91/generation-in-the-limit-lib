# P05 Stage 3: discrepancy adjudication

## Executive disposition and provenance

The semantic exact, approximate-sufficiency, and Nat stable-approximate results remain accepted within their stated scope. The literal stability obstructions are mathematically justified and deliberately documented, so they are not unexplained Lean errors. They do not formalize the source's positive stable-generation claims. The whole-target theorem matches an explicitly discussed local source convention, but the conversion to fresh output does not preserve raw stability. The registry's dismissal of imported exhaustive-generation coverage is too strong: the supplied P04 predicate matches P05 Definition 4.2 semantically, subject to an innocuous initial-round boundary explained below.

This is the continuing Stage 2 reviewer, configured as `gpt-6.1-sol` / `xhigh`, originally isolated with `fork_turns=none`; it is not an independent third blind review. I retain the source-first inventory, six target comparisons, and full 34-module inspection from Stage 2. After Stage 2 froze at 2026-11-10T05:27:11.703976Z, the coordinator authorized the three Stage 3 context files and existing raw-source comments. The coordinator supplied methodological checks, not a mathematical verdict or counterexample. A previous coordinator wording clarification merely made the sufficiency arrow explicit.

The pinned source remains arXiv:2412.18530v2, 3 July 2025, 46 PDF pages, SHA-256 `ba5c0de2215a156ea45791e2399487aed75e08715176d57c24e6238ce4fdd7dd`. All source pages below are both printed and one-based PDF numbers. Page 15 was newly rendered; pages 17, 38, 39, and 41 were visually reinspected using the unchanged Stage 2 renders.

The frozen inputs remain unchanged:

| Artifact | SHA-256 |
|---|---|
| Stage 1 reconstruction | `8eed8dcb9c22ca48c5c355759acecd288120ad889db3d3e63b5762510f0f579f` |
| Stage 1 run | `8b2f026804e72c8ccf46de1ffc54e116ffcd076be192ea9803f34ccce09e9eec` |
| Stage 2 comparison | `46a729d5f3594b372595df83cab5015088ddabd5503cb7ea6f56078e94effeea` |
| Stage 2 run | `c1c960d8dd7e01ad1ef0dd68b19627ae3050ac8858e20b72e756ace6622be3f7` |

## Existing explanations and evidence status

The newly opened `stage3-context/PaperMap.md` has hash `58047c20e067b57c79f8b1373272e32006abc27f2c3b7b68a14acb1b0114ef67`; `registry.json` has hash `04621796b1eca3ed8e6d3fcebc09b0eed5ae431f5f59333c0b36486bd2ddced7`; `provenance.json` has hash `88b69cb1cce3dd01352ce7ebf8a66d1911eaec9f1210156e8d286ebb8e7f6629`. Their recorded hashes agree. The registry contains 19 custom-scope cards, not an inventory of every source claim. Exact input hashes, access order, comments consulted, and QA hashes are in `adjudication-run.json`.

The PaperMap's “Scope and status,” correspondence table, reuse section, and source qualifications disclose semantic-only scope, missing approximate necessity, the Nat restriction, classical P03 adaptation, stability conflicts, and a separate whole-target repair. Registry cards `exact-breadth-characterization`, `approximate-breadth-characterization`, and `stable-approximate-characterization` retain effective-realization limitations. These explanations agree with actual types and defining values.

Raw comments also disclose these choices: P05 Definitions.lean:5,90 distinguishes unseen from whole-target support; CorrectedStability.lean:3,26,66 describes the repair; Relationships.lean:4,23 disclaims computability; Overview.lean:7,34,54,65,77 marks partial results and countertheorems; StabilityGap.lean:4,70,130 states the literal obstruction. SemanticBoundary.lean:3,36 documents empty output. Comments establish disclosure, not truth. In particular, their claims of prior kernel checking or absence of axioms were not independently re-audited here.

Evidence levels are kept separate: the six exported theorem types and relevant existing raw Lean theorem interfaces are statement evidence; fresh/seen conversions, counterexample hypothesis checks, and exhaustive-interface translation below are informal mathematical arguments, not newly Lean-checked proofs. There was no new compilation, proof audit, outside mathematical source, author endorsement, or human certification.

## Final disposition for every target

Write B for `GenLimit.BreadthCharacterizations`; Overview means the pinned P05 `Results/Overview.lean`.

| Target | Exact compared content and final disposition |
|---|---|
| `GenLimit.BreadthCharacterizations.Results.theorem_3_3_semantic` (Overview:27) | On nonempty countable domains and infinite-member families, exact fresh support exists iff strong tell-tales exist. **Matches source context semantically** (Theorem 3.3, p. 9); arbitrary countable domain is a faithful generalization. Effective sampler/enumerator/membership implementation remains a separate coverage gap. |
| `GenLimit.BreadthCharacterizations.Results.theorem_3_8_sufficiency_semantic` (Overview:37) | Weak tell-tales imply existence of approximate support, on countable domains and infinite-member families. **Matches the sufficiency component**, with a **substantive coverage gap** for necessity and effective realization. “Constructive direction” in the notes does not turn the noncomputable semantic construction into an ordinary program. |
| `GenLimit.BreadthCharacterizations.Results.theorem_3_15_approximate_semantic` (Overview:46) | Over Nat, a single stable approximate generator exists iff strong tell-tales exist. **Matches source context as a faithful specialization** of Theorem 3.15's approximate arm, p. 12. Arbitrary-domain transport and effectivity remain missing. The classical Boolean adapter does not supply uniform computational MOP access. |
| `GenLimit.BreadthCharacterizations.Results.theorem_3_15_literal_exact_inconsistent` (Overview:57) | Every countable infinite-member family lacks a generator jointly raw-stable and literally exact/fresh. **Justified literal-specification correction/diagnostic**, materially different from the positive arm of Theorem 3.15. It contributes no positive stable-exact coverage; local seen-support context must remain visible. |
| `GenLimit.BreadthCharacterizations.Results.theorem_3_15_corrected_wholeTarget_semantic` (Overview:68) | Stable whole-target support exists iff strong tell-tales exist, on nonempty countable domains and infinite-member families. **Matches the locally stated seen-support convention and is a qualified representation choice**; it is not literal Definition 3.1. It implements a coherent semantic repair without resolving effective realization. |
| `GenLimit.BreadthCharacterizations.Results.proposition_8_10_literal_specification_inconsistent` (Overview:80) | Every countable infinite-member family lacks jointly raw-stable, valid, fresh, infinite support. **Justified correction of the literal positive specification**, including genuinely nonvacuous finite-dimension cases. A repaired positive dimension/VSI theorem, its distinct-example bound, and effective oracle implementation remain **substantive coverage gaps**. |

All six retain `∃G` before target/presentation quantifiers and presentation-dependent eventual thresholds. The two negative targets quantify over arbitrary semantic functions, so no computational qualification weakens their obstruction. None supplies rates, distributions, a named counterpresentation, or a bound on convergence time.

## Fresh/seen conversions: what survives stability

Stage 2 found tension between exact support `K\S_t` (Definition 3.1, p. 9) and eventual raw-support equality (Definition 3.14, p. 12). The notes explicitly distinguish them. Actual definitions give `removeObserved G(h)=G(h)\historySet(h)` and `restoreObserved G(h)=G(h)∪historySet(h)`. ExactBreadth.lean:109,117,125 states their correctness conversions and existential generatability equivalence. CorrectedStability.lean:27 instead defines stability *of the restored generator*, and line 47 supplies precisely that changed property.

Here is a nonvacuous informal check. Take the singleton collection {N}, encoded as a constant indexed family. Its language is infinite; it has a computable membership oracle and strong tell-tales (the empty set suffices). The whole-target generator `G(h)=N` is raw-stable and whole-target correct. Removing observations yields `N\S_t`. On the complete presentation 0,1,2,... this support changes at every step, so raw stability is destroyed. Conversely, restoring observations to this fresh generator gives constant N. Thus the conversions establish ordinary semantic existence equivalence, not equivalence after conjoining raw stability. Infinitude, presentation completeness, strong-condition sufficiency, and oracle availability are all satisfied in this example.

More generally, after stability and correctness thresholds, choose an element of the fixed nonempty support A⊆K. Completeness eventually puts it in S_t, contradicting later sample-disjointness. Exact fresh support is nonempty for infinite K and finite S_t; infinite coverage is explicitly infinite. This informal argument agrees with existing StabilityGap theorem interfaces; it does not audit their proofs.

Footnote 3 on p. 17 explicitly says “Here” the exact-support convention permits training examples. It supports whole-target interpretation in that local discussion and Theorem 4.5's exact arm. It does not prove that raw stability survives conversion, or retrospectively make the literal p. 12 conjunction equivalent. T5 therefore earns local semantic correspondence; T4 remains a valid diagnostic of the literal definitions. No global rewrite is inferred from the footnote.

The smallest coherent repair for stable exact breadth is either whole-target support with raw stability, or fresh exact support with stability measured after restoring observations. Lean explicitly represents these alternatives. The positive theorem's effective access requirements still require independent formalization.

## Proposition 8.10: all hypotheses checked

Stage 2 left the source-convention adjudication open. The notes say the obstruction is independent of dimension and oracles. A universal obstruction alone does not show that a conditional positive theorem has an inhabited antecedent; the following explicit informal example supplies that missing check.

Let X=N and let the two languages be

`L0 = {0,2,4,6,...}` and `L1 = {0,1,3,5,...}`.

They are distinct, infinite, countable, and computably decidable; the domain can also be computably encoded as finite strings. Their intersection is {0}. The one-element sample {0} has nonempty version space containing both languages, with finite intersection. Any consistent sample of at least two distinct elements contains a positive element; its parity selects exactly one language, so its version-space intersection is that infinite language. Consequently Definition 8.8, p. 38, gives closure dimension exactly **1**, avoiding any empty-witness or dimension-zero convention.

The dimension value is known. A VSI query is computable by checking both candidate languages: keep those containing the finite sample, then test the query point in each retained language. This implements Definition 8.9 on all queries, including the conventional universal intersection when no candidate remains. Thus the family satisfies the finite-dimension and oracle premises of Proposition 8.10, p. 39. It is also finite, satisfying Corollary 8.11(2). Complete target presentations exist and eventually contain two distinct observations. There is no nonidentifiability or stochastic-distribution premise to satisfy here.

The literal positive conclusion is still impossible by the fixed-support argument. Hence its failure is not vacuous or caused by unavailable oracles. All new family/dimension/oracle calculations are informal, not Lean-checked. The existing T6 type supplies the universal obstruction; it does not itself contain this dimension calculation.

The source's pp. 39-40 construction freezes support to the infinite VSI intersection after d+1 distinct examples. It supports a nearby positive theorem permitting observed strings. The smallest repair is to remove freshness from the stable infinite-coverage conclusion while retaining target containment and infinite support. Lean has no positive theorem for that repaired specification, dimension, VSI, or sample bound.

Footnote 17 on p. 41 applies to the *subsequent* increasing-coverage discussion; it cannot silently repair the preceding Proposition 8.10 or Example 8.12. Nor does the exact-breadth restoration trick automatically repair infinite coverage: for a frozen proper subset A⊂K, removing observations and then restoring them gives `A∪S_t`, which can keep changing when K\A is infinite.

## Imported exhaustive generation: registry correction accepted

The PaperMap table marks Theorems 4.3/4.5 unformalized as general tables. Registry card `exhaustive-generation-characterization` goes further: it calls the P04 interface materially different and withholds all coverage pending interface equivalence. That mathematical reason is not supported by the actual definitions.

P05 Definition 4.2 and Equation (2), visually verified on p. 15, use a current enumeration, finitely many current hallucinations, and coverage by training observations, earlier first outputs, and the current range. P04 Exhaustive.lean:33-79 has exactly those components: `ExhaustiveAlgorithm`, `generateOnly`, `generatedBefore`, and

`Finite(currentRange\K) ∧ K⊆sample ∪ pastFirstOutputs ∪ currentRange`.

The source expressly switches to an enumeration-valued object for exhaustive generation. It need not share P05's support-only generator type. Source enumeration position 1 corresponds to Lean position 0; ordered finite history and complete presentation semantics agree.

There is a minor initial-round boundary: Lean permits an empty-history round 0, whose first output can enter past outputs, while the source starts at round 1. Restricting a Lean generator to positive rounds can lose this one past element. If that element belongs to K, completeness eventually includes it in the sample; otherwise it is irrelevant to covering K. After that finite delay the exhaustive guarantees agree. Conversely a source generator can be extended arbitrarily at round 0 without damaging eventual correctness. This is an informal translation of eventual specifications, not a newly compiled equivalence theorem.

P04 ExhaustiveCharacterization.lean:712 already states, under Countable α and infinite family members,

`ExhaustivelyGeneratable (Set.range F) ↔ WeakAngluinExistence (Set.range F)`.

The weak condition at Exhaustive.lean:252 is the same finite-tell-tale/proper-subset finite-difference condition as P05, with class membership replacing indices. Passing between `Set.range F` and indexed quantifiers preserves the semantic condition, including duplicates.

Therefore the nonstable exhaustive arm of Theorem 4.3 has **native imported semantic coverage**, with a missing P05 facade wrapper rather than an absent mathematical formalization. A compiled explicit P05 comparison theorem would improve traceability, but its absence is not evidence of material interface difference. The registry's separate bridge lies outside the supplied raw closure and was not opened; the conclusion above uses the actual imported native theorem, not that documentary link.

This correction does not establish the full four-way or stable tables. It also does not supply Lemmas 7.5/7.7's effective access refinements or eventual zero hallucinations. P04's classical subset/finiteness tests and noncomputable enumeration are not ordinary relative programs merely because its comments say “strong-oracle.”

## Remaining source and coverage limitations

The semantic/effective boundaries disclosed by the notes are accepted. Classical tell-tale selection and classical Boolean support queries do not prove uniform computable selection, membership access from descriptions, or ordinary sampling. Approximate necessity, generic uniqueness/finite-non-uniqueness frameworks, statistical laws/losses/rates, stable exhaustive characterization, increasing coverage, and most hallucination-grid components remain absent. Imported stable-unambiguous reductions and co-singleton examples are partial supporting coverage, not complete P05 characterizations. The 19 registry cards cannot replace Stage 2's full 57-item inventory.

The empty-support diagnostic matches literal Definition 2.1 and the disclosed support-validity model; it does not model productive single-string generation. Theorem 5.3's p. 22 final “exact breadth” clause remains a suspected wording issue, correctly preserved by the registry; no statistical repair is implemented. Example 8.12's p. 40 fixed support `N\S1` fails target containment for a sufficiently high positive integer tail even if seen strings are allowed. Replacing it by a tail above the first observation gives a plausible seen-support witness, but is a separate informal repair and is not native Lean coverage. The literal infinite-hallucination column for whole-domain targets, Remark 3.11's broad metric wording, and p. 41's growth inference from a size cap remain unresolved source qualifications, without effect on accepted facade semantics.

Several registry Section 8 page locators are offset from this pinned PDF: Proposition 8.10 is on pp. 39-40, Corollary 8.11 on p. 39, and Proposition 8.14 on p. 41. These are documentation follow-ups, not source changes made here.

Minimal follow-up is to distinguish local seen-support conventions from literal countertheorems, credit the imported exhaustive semantic arm while retaining effective gaps, and add explicit comparison/transport or repaired-positive declarations where desired. No repository, registry, or documentation source was edited. Completion of adjudication does not certify all paper proofs, Lean proofs, ordinary computation, or human review.
