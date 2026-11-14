# P29 source-to-Lean statement comparison

## Identity, isolation and result

This compares four claim slots and all five registered targets against *Mistake-Bounded Language Generation*, Kleinberg–Peale–Reingold, arXiv:2605.10809v1 (margin date 11 May 2026; title date May 12). Original PDF SHA-256: `c79335d8c0fec7e3960c141c034a34144e4928d118f27311c8d661f81ba61365`. Printed and PDF pages coincide. The supplied kernel-interface snapshot records source digest `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc`; this is metadata, not an independently hashed source checkout.

The source inventory was completed and coordinator-frozen before any Stage 1 access (freeze 07:53:52 UTC, inventory JSON hash `5fe0d7f89f4d3747f36a5ec5373403521f399ec7b18a8fd90ef6c1205693cef8`). Stage 1 was separately frozen at 07:44:24 UTC. Both freezes and every listed artifact hash were rechecked. No developer explanations, owner material, raw Lean, proof bodies, PaperMaps, registry interpretations, Git or old audits were accessed.

| Slot | Statement correspondence | Main finding |
|---|---|---|
| C01 | Faithful specialization of the meaningful finite-bound case | The same weighted algorithm and sharp bound, with explicit positive target prior and finite activation; broader semantic universe. |
| C02 | Substantively different from the literal printed numbers; supported source correction | Same-witness joint theorem uses d+1 for count/time under generator-first play. The disjoint-pair diagnostic is static. |
| C03 | Faithful generalization | Registered integer bound is sharper; native public endpoint explicitly proves the paper's displayed real bound for the same stream. |
| C04 | Partial | Arithmetic proof fragment only. The hard-class and rate-tradeoff lower bound are not represented in the supplied census. |

No genuine algorithm/statement translation error was established in the represented positive results. The C02 literal difference, C04 incomplete coverage, and independent source issues are separate findings.

## Independent source inventory and common translation

The frozen source-only inventory remains the authoritative pre-comparison record; it contains the full assumptions, source contexts and visual checks for every slot. Its core source claims are: C01, total mistakes ≤d_i+floor(log2(W/w0(i))) (pp.5,15–16); C02, one generator with total ≤min{floor(log2 N),Cdim} and last error ≤Cdim (pp.6–7); C03, the reciprocal-square/exponential instance has total ≤3log2 i+log2(π²/6) (pp.9–10); C04, one fixed class forces ≥i−1 mistakes at each i≥2 for every generator with the stipulated O(max{i,m_i}) time rate (pp.11–12).

Source Section 3 assumes a countably infinite universe, infinite languages, and distinct adversarial outputs realized by the target, without full target coverage. The generator moves first and must avoid only the adversary's prior outputs. There is no correctness feedback. Lean uses any `Infinite α` and indexed arbitrary sets; target infinitude follows from the injective realized stream. Non-target languages need not be infinite, and duplicate indexed sets are allowed. These are domain/representation generalizations, not a change in the source instance when faithfully enumerated.

Use paper language i=k+1 and paper round r=t+1. `sample observed t` contains precisely observations at indices s<t. `mistakeCount trace T` counts errors at s<T; `TotalMistakesAtMost` bounds all such counts. The source's supremum over realized streams of total errors is thus the same bound after universal quantification over streams and horizons. The native `worstCaseMistakes` supremum and its iff bridge support this interpretation. None of these results concern a probability law, distribution, support loss or expected error.

The checked definitions use exact real scores and `Classical.choose` of a maximizer over all unseen points. The state uses only earlier observations; target and analysis budgets do not enter the selection. They define named semantic online streams, not effective implementations. The source also leaves membership, infinite-domain optimization and exact arithmetic access unspecified, despite its finite-active-prefix discussion. No computational runtime guarantee is inferred on either side.

## Full component comparison

| Slot/component | Source location | Lean evidence and result |
|---|---|---|
| C01 argmax/freshness | Algorithm 1, p.5 | `countableSemanticGenerated`, `weightedScore`, `freshWeightedMaximizer` and freshness/maximality interfaces: same finite-active score and unseen domain. |
| C01 update | Algorithm 1, p.5 | `countableSemanticWeight`, `updateWeight`: inconsistency first, otherwise keep/double, exactly as source. |
| C01 delayed admission | Algorithm 1, p.5 | Newly admitted weight is its prior iff every observation through the current one belongs to that language. |
| C01 activation/budget | Theorem 4.1, pp.5,15–16 | `FirstActivated`, `DyadicUpperBudget`, `Results.theorem_4_1`: positive-prior finite-entry bound, numerically equivalent after translation below. |
| C01 potential/doubling | Lemma A.1 and proof, pp.15–16 | Native active-weight step/total-bound and target-weight power-of-two interfaces are present. Proof steps are not certified. |
| C01 LfD provenance | Appendix B, pp.17–22 | Context was read; no standalone reward-context reduction is represented in the supplied census. This is contextual derivation, not an extra C01 theorem conclusion. |
| C02 floor-log guarantee | Theorem 5.1, pp.6–7 | Uniform-prior `finiteSemanticGenerated` and registered joint endpoint retain floor(log2 N). |
| C02 critical common-intersection choice | Algorithm 2 and proof, p.7 | Native `finiteAlgorithm_critical_choice` plus `finiteSemanticGenerated_isFiniteWeightedArgmax` apply to the same named stream; condition is any nonempty unseen intersection. |
| C02 joint count/time | Theorem 5.1, p.6 | Same stream in one conjunction; count min{Nat.log 2 N,d+1}, correctness at zero-based t≥d+1. Literal source Cdim terms change by one. |
| C02 order diagnostic | Example 1/Remark 1, pp.2,4 | Registered disjoint infinite pair has dimension bound 0 and every point misses a member. Static obstruction only, no online adversary theorem. |
| C02 cardinality lower-bound context | Section 5.2, pp.7–9 | Outside Theorem 5.1/Section 5.1 slot; no claim here that this separate lower-bound construction is formalized. |
| C03 parameters/mass | Section 6.1, pp.9–10 | Exact shifted schedule/prior; native `polynomialPrior_hasSum` has mass π²/6. |
| C03 integer and displayed bounds | Theorem 6.1, p.10 | Registered exact activation+floor bound; native `Results.theorem_6_1_displayed_bound` and underlying real-bound theorem explicitly give the source RHS. |
| C03 timing scope | Section 6.1, pp.9–10 | Count only, without a target-uniform last-error deadline on either side. |
| C04 positive comparison | Algorithm 3; Lemmas 6.2–6.3, pp.10–11 | Native Modified-Greedy definitions, count and time interfaces exist for the same named generator. |
| C04 hard family and m/tail sizes | Proof, p.12 | Not represented by the arithmetic endpoint or another inspected native interface. |
| C04 boundary arithmetic | Proof, p.12 | `geometricPrefix` and diagnostic equality represent a numerical rewrite only. |
| C04 stopping branches and valid stream | Proof, p.12 | Not covered in supplied census. |
| C04 O-constant/time contradiction | Theorem/proof, pp.11–12 | Not covered; the source's fixed-n asymptotic reasoning independently needs clarification. |
| C04 all-index i−1 lower bound | Theorem 6.4, p.11 | Not covered. Neither positive Modified-Greedy bounds nor generic supremum interfaces supply this conclusion. |

## Five target dossiers

### 1. C01 — `GenLimit.MistakeBounded.Results.theorem_4_1`

Anchor: `Results.Overview:42`; exact type in `stage1/01-target-statements.md`, recursive definition values in `02-definition-dependencies.md`. Let A be monotone, w nonnegative, o injective, and every prefix Σ(j<n)w(j)≤B. For any target k, first active round a, and natural b, assume all o(t)∈L(k), w(k)>0 and `B < 2^(b+1) w(k)`. Then the fixed stream `countableSemanticGenerated A w L o` has at most a+b errors in every prefix. The generated stream is independent of k,a,b,B and all analysis premises.

Set A(t)=f(t+1). The first-activation predicate means precisely that source Li, i=k+1, first appears at paper round a+1; hence a=d_i. For a nonnegative sequence, bounding all finite prefix sums expresses the source finite total mass bound. Since B≥w(k)>0, the dyadic strict inequality is equivalent to `floor(log2(B/w(k)))≤b`; choosing the smallest b recovers the source sharp floor. At a dyadic equality B/w(k)=2^m, b=m works and b=m−1 does not. The generator's state and admission rules match Algorithm 1 after this shift.

The literal source permits zero priors and never-reached targets, whereas this finite theorem requires positive target weight and an activation witness. Those are meaningful-domain restrictions/source qualifications, not evidence of a lost valid finite guarantee. Other zero weights and bounded schedules remain allowed. A target never activated receives no conclusion; the source supplies only infinite delay there. Native zero-weight, potential and target-doubling interfaces were checked, rather than assuming this endpoint was an abstract potential-only result.

### 2. C02 — `GenLimit.MistakeBounded.Results.theorem_5_1`

Anchor: `Results.Overview:71`. For any injective stream o realized by k:Fin N, and any natural d bounding every finite subfamily intersection size, one named `finiteSemanticGenerated L o` has both count ≤min{Nat.log 2 N,d+1} and no errors at any zero-based t≥d+1. The generator does not take k or d. With N≥1, Nat.log is the source floor logarithm. N=0 has no target; N=1 gives zero mistakes.

The dimension predicate bounds finite intersection cardinalities and does not constrain infinite ones. A faithful finite enumeration permits d=Cdim when that source maximum exists; arbitrary larger d is also allowed. It handles classes with no finite intersections without inventing an empty maximum. Native closure and critical-choice interfaces were inspected, and both registered conjuncts refer to the same stream.

Translating t to paper r=t+1, the Lean theorem permits a last error at paper round d+1 and guarantees correctness from d+2. The printed source says last error ≤d and total ≤min{floor(log2 N),d}. This is a literal numerical difference, supported as a source correction by the source's own Example 1: after n common elements are exhausted, generator-first play can force an error at n+1. In the disjoint case d=0, zero errors cannot be guaranteed. The count correction cannot be explained away as just relabeling a clock.

### 3. C02 — `GenLimit.MistakeBounded.Results.theorem_5_1_order_diagnostic`

Anchor: `Results.Overview:94`. For arbitrary infinite disjoint sets L₀,L₁, every x satisfies both `FiniteClassClosureDimensionAtMost(pair,0)` and `(x∉L₀ or x∉L₁)`. There is no explicit Infinite-α instance because the sets themselves are assumed infinite. The union need not cover α.

This faithfully records the static obstruction at the source's boundary case: a first prediction misses a possible target in a class of dimension 0. Its type has no observation sequence, target-selection algorithm, round, or mistake-count conclusion. It does not itself formalize the full adversary or prove a lower-bound theorem about all online generators.

### 4. C03 — `GenLimit.MistakeBounded.Results.theorem_6_1`

Anchor: `Results.Overview:106`. For any injective realized stream and target k, use A(t)=2^(t+1), p(k)=1/(k+1)². The registered theorem bounds every prefix by

`pred(Nat.clog 2 (k+1)) + floor_nat(log2((π²/6)/p(k)))`.

With source i=k+1, the first term is max{ceil(log2 i)−1,0}, the exact source entry delay, including zero at i=1,2. The second is the source nonnegative real-log floor. This bound is sharper than the source display. Native census records 236 and 285 respectively give `theorem_6_1_displayed_real_bound_concrete_semantic_algorithm` (`PolynomialPrior:532`) and `Results.theorem_6_1_displayed_bound` (`Results.Overview:125`): every prefix count cast to Real is ≤`3log2(k+1)+log2(π²/6)` for the identical stream. Native Basel-mass, first-activation, valid-budget and budget-cast interfaces were also read. Thus the full source numerical bound is represented, and O(log i) follows mathematically. Absence of that coarse display from the five registered targets is not a native-result gap.

The source proof's final equality drops a floor; replacing that equality by ≤ proves the advertised bound. No error-location guarantee is claimed. No effective algorithm follows from its semantic definition.

### 5. C04 — `GenLimit.MistakeBounded.Results.theorem_6_4_proof_diagnostic`

Anchor: `Results.Overview:181`. The exact claim is, for every natural base and i>0,

`G(base,i)+base^i+1 = G(base,i+1)+1`,

where G sums base^j over positive j<i. Bases 0 and 1 are allowed. At i=0 the identity would fail, so the positivity premise matters. The native counterpart (`TradeoffDiagnostic:32`) has the same arithmetic type. Neither statement asserts any language family or rate.

This is a legitimate numerical fragment of the source boundary formula. It does not assert that G equals the structural complexity of any formalized language, that a stream/adversary is valid, that a late error contradicts an O bound, or that every target i≥2 incurs i−1 errors. The supplied 389-declaration census was used before declaring this gap: all TradeoffDiagnostic types, existential theorem interfaces, geometricPrefix/worstCaseMistakes/NonuniformComplexityAtMost use sites, and relevant Modified-Greedy definition bodies and bounds were inspected. No full hard-class lower-bound statement was found. This absence finding is limited to that frozen census.

The positive comparator is present: native `lemma_6_2_modifiedGreedy_complete` and `lemma_6_3_modifiedGreedy_last_mistake` concern the same `modifiedGreedyGenerated`. With k=i−1, the count is min{2k,max{k,m+1}} and the zero-based inclusive cutoff is max{k,m+1}; the latter means paper last error ≤max{i−1,m+1}. Its definition scans the first t+1 indexed languages, exactly the paper's first r languages at round r=t+1. These results do not provide the separate tradeoff lower bound.

## Discrepancies, source questions and Stage 1 corrections

The following distinctions remain explicit:

- **Literal difference/source correction:** C02 adds one in the closure-dimension count/time guarantee. Source Example 1 and generator-first play support this correction; it is not an established Lean bug.
- **Source qualification:** C01 spells out positive target prior and finite activation. Its finite formula otherwise has the same sharp content.
- **Faithful sharpening/model generalization:** C03 uses an exact integer bound and a broader universe, with the source real display also natively present. All positive algorithms remain semantic classical choices.
- **Partial formalization:** C04 covers only boundary arithmetic, while the class, adversary and lower bound are absent from the inspected interface. A theorem name or an arithmetic identity cannot establish those omitted claims.
- **Independent source issue:** For fixed n>1, `(m_i+n^i)/m_i` tends to n as i grows. The source proof's ω expression therefore needs a different variable or construction. Taking n arbitrarily large leaves the O constant's dependence on n and the theorem's one-class-before-all-generators quantifier order unresolved. The diagnostic identity neither resolves nor formally refutes that issue.

Additional source questions are the undefined empty maxima for Cdim/m, the C04 introduction's i*−2 versus its final i*−1 count, and the distinction between an inclusive convergence cutoff and a last erroneous round. The source-only inventory already recorded these before Lean access. No source correction is silently substituted for the pinned theorem.

No factual correction to Stage 1's five target reconstructions was required after direct type/definition checks. The additional native real-bound theorem and Modified-Greedy context are scope supplements, not errors in Stage 1's code-only report; Stage 1 expressly did not audit all census declarations.

## Coverage and limits

All four slots and five registered targets are accounted for. Both C02 conjuncts and its diagnostic conjuncts were checked. C01 update/admission/potential/target doubling, C02 critical choice and same witness, C03 constants/rounding/schedule, and every C04 hard-family/branch/lower-bound component are explicitly classified above. Contextual LfD and cardinality-lower-bound derivations were distinguished from the scoped theorem conclusions.

All relevant paper context and appendices were read during the independently frozen inventory. Thirteen source pages were visually inspected there; pages 6 and 12 were re-viewed for the decisive comparison. The original and annotation-removed PDFs have separate recorded hashes. Source/inventory/Stage 1 freezes are preserved. No Lean build or mathematical edit was performed, and neither proof correctness nor human review is certified.

Stop for coordinator comparison freeze before developer explanations or adjudication.
