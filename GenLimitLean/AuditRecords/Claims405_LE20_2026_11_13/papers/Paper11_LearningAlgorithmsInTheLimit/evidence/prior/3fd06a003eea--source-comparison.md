# P11 Stage 2 — independent source comparison

The native snapshot proves useful elimination, observation, tagging, finite-cover and conditional greedy-merging results. It also contains a concrete tape interpreter and an assembled time-bound learner for its finite-program representation. It does **not** represent the complete source paper: several facade targets are conditional mathematical cores, not the named source theorem. In particular, the source's abstract-model time-class results, full recursive-to-rational learner reduction, halting-based noncomputability conclusions, and concrete MSM learning theorem remain unassembled or require mathematics absent from the complete native census. These are statement-correspondence findings, not proof failures.

## Identity, scope and method

The source is Hristo Papazov and Nicolas Flammarion, *Learning Algorithms in the Limit*, COLT 2025 proceedings, PMLR 291, edition dated 2025-07-02. Mathematical source evidence is the supplied official 25-page PDF and its full extracted base text. PDF SHA-256: `83aef91acf3b06c6dbbe6432fa5c1084cc7396c206684a5ebf0d4f62c0e61d57`; text: `513017d89246ac9a6ef20ad87da7eb562c0f916cd4ba39a05fc14e66a321f77e`. The identity file explains why the historical expected PDF hash differs: the historical copy was annotated and its normalized base text matches every official page. I did not access that copy or any annotations. I make no independent claim about its annotation payload.

I read the paper before Stage 1 or Lean and serialized the independent inventory to `qa/source-first-inventory.md`, SHA-256 `6bc1b95ed96ccd50aab43f4761d420b08e0fd442ace52a4efd46ae8158c2bfea`. Its freeze record confirms that order. Ghostscript rendered the official PDF; I visually inspected printed/PDF pages 8, 12, 13, 14, 18, 21, 23, 24 and 25. Printed labels equal one-based PDF pages on those inspected pages. Page references below use that numbering. Decisive formulas and source defects discussed below were checked in these images. Poppler was unavailable; pypdf independently reported 25 pages.

The selected scope is exactly the 16 entries in `stage2/lean-interface/targets.txt`. Native coverage uses the **full-umbrella-census-supplement**, available in the initial handoff: 516 records; all 15 expected modules loaded, comprising 14 nonempty modules and the import-only umbrella. Its manifest hash is `0ff77fa1d7d097c34cc50e61b98f7ef38afc846cc2521c2c3295497eafc0a674`; declarations hash is `7c01961f69a818e7a10215cf4e7df01a4bd463937af1623e794136cf4e7387df`. Every root flag is true because every declaration was an export seed; roots do not identify the selected targets. I checked all names, substantive theorem types and relevant defining values, including supporting modules outside the facade. Generated constructors, matchers, projections and equation signatures were distinguished from additional mathematical results.

All 59 checks across the supplied Stage 2, interface, explicit-type and full-supplement manifests matched. This includes 18 snapshot entries verified **only by hashing bytes**, without displaying or interpreting raw source. No raw Lean text, comments, theorem proof values, owner material, Stage 3 explanations, registry, PaperMaps, sibling reports, other audits, later editions or external mathematical sources were used. The 16 explicit target types equal the canonical census types byte-for-byte. All 144 interface names occur in that census; compact versus explicit printers change some other type/value strings, so I do not call those strings byte-identical or infer a semantic discrepancy from their formatting.

The frozen Stage 1 report and run record were opened only after the inventory was written, and their supplied hashes matched. Standard Lean/Mathlib meanings and exporter fidelity are trusted. I performed no build, proof-body audit, axiom audit, repository edit, Git operation or network request. The coordinator supplied model `gpt-6.1-sol`, effort `xhigh`, fresh context `fork_turns=none`; backend revision and sampling identity are not observable. No reviewer delegation occurred.

## Independent inventory of the entire source

The longer, source-only inventory was frozen separately before comparison. This condensed inventory preserves its independent boundaries and explicitly includes claims outside the 16 targets.

Pages 1–4 introduce learning **algorithms** for partial general-recursive functions on enumerable domains, outputting descriptions from a computable representation set. Observations exhaust a restricted source of defined inputs. The abstract promises IOO learning under time restrictions, TBO learning under q-ECTT, PTO reduction to rational functions, and negative characteristic-set results. There is no probability distribution, risk, loss, confidence parameter or statistical rate.

Definition 1 (p5) gives finite-state, finite-alphabet total Mealy FSTs, distinguishing final-symbol semantics on nonempty words from full output sequences. Finite generalized Nerode index defines rational maps. Definition 2 (p5) permits nondeterministic partition quotients and defines apartness through distinguishing words. Definition 3 and the convention below it (pp5–6) specify finite-state bidirectional-tape TMs with left/right/stay moves, designated start/halt states, a finite problem alphabet distinct from blank, contiguous initial input, and valid contiguous final output. State count is representation size, with fixed-alphabet description length O(n log n).

Assumption 4 (p6) is q-ECTT: one computable monotone overhead q, with a model-dependent constant and TM giving source-wide simulation bounds through reasonable encodings. The source additionally assumes all natural encodings have that property. Definitions 5–6 (p7) introduce finite-support symbolic worlds and finite-state computable agents with perception-local transitions. These motivate PTOs but do not themselves identify every external history with a finite-state policy.

Definition 7 (p8) requires **one eventual representation**, for every model, every allowed source and every exhaustive order. Correctness is on that source's defined inputs. Definition 8 (pp8–9) gives a characteristic core forcing whole-source correctness for every containing sample. Mass sums full observation lengths, whereas size counts examples. RIPTD quantifies one polynomial-time learner and characteristic sets of polynomial mass in representation size for every source. Unlike the intended finite-data use, the printed definition does not explicitly qualify all sets as finite; this ambiguity is retained below. Lemma 9 (p9), repeated as Lemma 25 (p20), claims distinguishability in the union of two characteristic sets, including a different-domain branch.

Theorem 10 (p9) states Gold's impossibility for learning all total recursive functions from IOOs. Definition 11 (p9) defines the union over a parameter c of partial functions having an O(Q(c,n)) bound on every halting input, with computable monotone Q and known input size. Theorem 12 (p10; Appendix B, pp20–21) learns this class under q-ECTT. Its displayed algorithm enumerates machines, increases a shared budget parameter, and selects the first finite-sample-valid representation at the first feasible budget. The appendix additionally claims minimum-state output, consistency at every stage, an alternative computable-order optimization, a polynomial-in-data-size capped variant sacrificing consistency, and incremental execution. Corollary 13 (p10) specializes to TMs without ECTT. The narration includes super-exponential enumeration effort in representation size.

TBOs (pp3,10) expose one natural bound per observation, with one model-dependent multiplicative slack valid across inputs. Theorem 14 (pp10–11; Appendix C, pp21–22) learns all general recursive functions from arbitrary-model TBOs under q-ECTT; it repeats the consistency, minimal-state, incremental and polynomial-time-variant claims. Corollary 15 (p11) removes ECTT for TMs.

PTOs (pp11–12) expose read/write/move trajectories and omit internal state. The scanned-symbol history is a word; a trajectory contains actions for **all its prefixes**, not only the last action. Theorem 16 (p12; Appendix D, pp22–23) gives a learner reduction from rational IOO learning under restricted sources to TM PTO learning and also an enumeration learner for all rational functions. Its appendix claims first-source-correct representation, size-order minimality, polynomial-time capping and incrementality. Page 23 explicitly says the learned function need not reproduce the teacher's full behavior.

Theorem 17 (p12; Appendix D, pp23–24) excludes every computable representation-dependent bound on characteristic **mass** and separately excludes computable characteristic-set assignments, already for linear-time total halting TMs on the full input source. The proof uses an effective halting-instance-dependent pair whose full behaviors agree until a sufficiently long input. Corollary 18 (p13) excludes IPTD for PTO, TBO and IOO. Narration also excludes restricted-source polynomial-data learning of rational functions through the reduction.

Definition 19 (p13) constructs partial observation trees; Definition 20 (p13) defines valid mergers as deterministic quotients, including cascading successor mergers. Pages 13–14 claim O(n|A|) merge and validity work, O(n) similarity scoring for fixed alphabet, and O(n^4) naive MSM. MSM chooses maximum positive similarity until terminal. The text says unrestricted greedy MSM is not universally correct, conjectures favorable-order correctness, and leaves its characterization open. Theorem 21 (p14; Appendix D, pp24–25) asserts that every total computable function has an expanded-alphabet tagged TM from whose PTOs actual MSM learns under every source, with polynomially many characteristic samples. It claims a two-step simulation, score-induced ordering of true-state mergers, and at most m examples to cover m used transitions.

Appendix A.1, Theorem 22 (p18), gives rational/FST equivalence, the canonical Nerode quotient, exact state count, minimality and uniqueness up to isomorphism. Theorem 23 (p18) includes O(n log n) minimization, length ≤n−1 state distinguishers, two-machine equivalence and length ≤n+n′−1 distinguishers in O((n+n′)log(n+n′)), and partial-FST apartness. Proposition 24 (p18) includes an effective **bijection** enumerating TMs in monotone state-count order, state count o(log n), and a polynomial-time binary decoder. Appendix A.3 (p19) discusses reasonable encodings via fixed FOL descriptions; A.4 (pp19–20) applies the framework to tasks. Sections 6 and D (pp14,24) leave polynomial-cardinality RIPTS/RIPS, favorable MSM orderings and reactive environments open. References pp15–17 add no paper claims.

## Common semantic and computational boundaries

In Lean, `Learner Info Rep` is a function `List Info → Rep`, and stabilization means `∃ r, correct r ∧ ∃ T, ∀ t≥T, learner(prefix t)=r`. This accurately preserves representation stabilization, rather than merely eventual function agreement. `Covers` is range equality: repeated inputs and finite sources are allowed; a covering stream excludes the empty source. The paper's surjection convention has the same empty-source vacuity. No statement supplies an arrival-time rate.

There are two different learner interfaces. Enumeration consumes finite lists, preserving order and multiplicity. Characteristic-set results consume arbitrary mathematical sets of `(input,observation)` pairs; neither the core nor intermediate sets are required finite. There is no assembled equivalence between these two interfaces. An arbitrary set learner is not an algorithm on finite encodings. The source itself slides between the interfaces, so their equivalence must not be assumed on either side.

`CorrectOn` and `AgreeOn` compare entire `Option` values on a **common source**, including `none`. The paper normally supplies only halting inputs and asks correctness on each model's own intersection with I. Positive data about a partial function do not reveal all negative halting facts. An abstract optional-label theorem therefore needs an explicit defined-source specialization before it models those observations.

`BoundedEnumeration` contains only `decode : Nat → Nat×Nat` and `runWithin : Nat → Nat → Input → Option Output`. It does not contain a Q-family, an overhead q, model simulations, a coding law, monotonicity or effectiveness. Its semantic candidate is an already bounded optional function. The finite elimination learner checks indices ≤ history length and falls back to 0 if none fits. This differs from the paper's unbounded search to the first feasible simulation budget, including its all-stage consistency behavior.

The complete census adds real tape configurations, finite instruction lists, default instructions, encoded program decoding, and a bounded interpreter. This supports Corollary 15, and must not be dismissed because other targets are abstract. Nevertheless, `TuringIO` supplies arbitrary initialization and output-reading functions over arbitrary input/output types. No ordinary computability law for those interfaces is asserted. There is no source-permitted oracle here and no conclusion that arbitrary supplied functions are uncomputable: the precise limit is that ordinary computability of the whole pipeline is **conditional on effective choices of those functions**.

`Mealy` and `PolicyMachine` have start and total step fields over arbitrary state types, with no finite-state or finite-alphabet assumptions. `PolicyMachine.tapeBehavior` consumes a prescribed scanned word; it does not execute the separate tape interpreter. Its equality to a converted Mealy output is definitional. Whole output lists are mathematically useful, but differ from the paper's final-symbol rational semantics on a restricted word source unless prefix expansion is justified.

## Component comparison matrix

“Core” below credits a genuine represented mathematical component while withholding the complete named source conclusion.

| Source unit | Native anchors | Classification and unrepresented components |
| --- | --- | --- |
| Definition 7, p8 | `SolvesLearningProblem`, `LearnsByCriterion`, `Covers` | Faithful semantic framework on defined sources; no ordinary algorithm predicate |
| Definition 8; Lemmas 9/25 | `IsCharacteristicSet`, target 1 | Common-source theorem generalized; original partial-domain formulation differs |
| Theorem 10, p9 | No substantive census theorem | Not represented; no Gold diagonalization or negative IOO conclusion |
| Definition 11; Theorem 12 | targets 2–3; enumeration module | Conditional elimination core; Q/q/model-to-clocked-enumeration assembly absent |
| Corollary 13 | target 4; concrete interpreter available | Same core as target 2; time-class representation and coverage still absent |
| Theorem 14 | target 5 | Conditional TBO-fitting core; arbitrary-model q-ECTT translation absent |
| Corollary 15 | target 6; program decoding and interpreter | Assembled semantic specialization; canonical effective I/O specialization remains implicit |
| Theorem 16 transition diagram | target 7; behavior length | Exact prescribed-word identity; no actual TM scanned-history bridge |
| Theorem 16 rational learning | target 8; least-consistency lemmas | Given countable-family convergence; all finite FST enumeration/representation absent |
| Theorem 16 learner reduction | targets 7–8 separately | Missing assembly and tape/prefix/source bridge mathematics |
| Theorem 17 late distinction | targets 9–10 | Abstract two-Boolean lower-bound core only |
| Theorem 17 computable bounds and sets | No halting reduction in census | Genuinely missing native mathematics, not merely a missing facade theorem |
| Corollary 18 | targets 11–12 | Equality/characteristic transfer core; no concrete IPTD impossibility |
| Definitions 19–20; MSM pp13–14 | abstract MSM relation | No observation-tree or quotient/cascade implementation, validity or cost theorem |
| Theorem 21 tagged conversion | targets 13–14; scanned length | Prescribed-word simulation generalization; actual tape/function preservation absent |
| Theorem 21 cover remark | target 15 | Finite image, coverage and eventual appearance; no learning implication |
| Theorem 21 greedy correctness | target 16 | Conditional score-gap/termination theorem; concrete hypotheses not discharged |
| Theorems 22–23 | Mealy basics only | Nerode, minimality, isomorphism, distinguishers, Hopcroft and all costs absent |
| Proposition 24 | program decode/encode identities | Enumeration infrastructure only; bijection, size order, little-o and polynomial cost absent |

## Sixteen target dossiers

Identifiers below are the actual selected declarations. Anchors `Overview:n` abbreviate `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:n`; supporting module names refer to that same frozen paper directory. Exact types are the supplied explicit export, independently compared to the canonical census. These dossiers state all conclusion components; they do not substitute source labels for their types.

### 1. `GenLimit.LearningAlgorithmsLimit.Results.lemma_9_distinguishability`

Anchor Overview:27; native `CharacteristicSets:26,52`; source Lemma 9 p9/Lemma 25 p20. For arbitrary observation/semantic maps, one common source, one set learner and two supplied characteristic cores, semantic `Option` disagreement implies a point in their union with unequal observations. There is no finite-core, computability, learning-in-the-limit or witness-finding premise/conclusion. The witness depends on both cores and all interfaces. Empty source makes disagreement impossible; two empty cores cannot meet the three hypotheses.

On a source where both source models are defined, this is a faithful generalization of the source's observational argument, permitting independent representation semantics and arbitrary observation types. For differing partial domains it is materially different: Lean demands correctness on the same source including divergence, whereas the source asks only each model's own defined restriction and allows an outside-common-domain alternative. This difference cannot be erased by identifying `none` with an observed undefined answer. The printed source has a separate problem described below.

### 2. `GenLimit.LearningAlgorithmsLimit.Results.theorem_12_timeRestrictedIOO_core`

Anchor Overview:45; native `TimeBounds:22,37`, `Enumeration:95,246`; source Theorem 12 pp10,20–21. Given arbitrary bounded enumeration E, optional target f, stream and source, exact coverage and **one** source-correct candidate imply eventual stabilization of `labeledEnumerationLearner E.semantics` to a source-correct natural index. The stabilized index need not equal the supplied witness. Data include exact optional labels. No conclusion says minimum states, all-stage consistency, polynomial runtime or an identified convergence time.

This is a useful general elimination theorem, but materially different from the complete source theorem: candidate existence is assumed instead of obtained from the Q-class and q-ECTT, and algorithmic access to E is unqualified. Removing source assumptions here does not make the source theorem stronger; it changes what is assumed. For positive defined labels and a uniformly effective clocked enumeration, this is the convergence core of a possible implementation. The Q class, size map, encoded simulation and their coverage assembly are absent throughout the census, not just the facade.

### 3. `GenLimit.LearningAlgorithmsLimit.Results.theorem_12_minIndex_claim_not_justified`

Anchor Overview:62; native `Enumeration:263,271,275`; source p21 minimum-state discussion. This closed proposition has four conjuncts: representation 0 returns `some false` at some budget; representation 1 does likewise at some separately chosen budget; at budget 2 representation 0 returns `none`; at that same budget representation 1 returns `some false`. The definition uses thresholds 10 and 2, respectively, and ignores its Unit input. There is no learner, source, history or minimization operator in the type.

It is a materially different diagnostic, not a formal negation of Theorem 12 or a complete source-algorithm counterexample. It illustrates why the first feasible budget need not select the least representation that would work at a larger budget. For a repeated singleton source, a budget-first strategy can retain the first feasible budget forever. The source's minimum-state proof therefore needs additional justification, but the four facts alone neither refute learnability nor certify an error in a particular concrete TM construction.

### 4. `GenLimit.LearningAlgorithmsLimit.Results.corollary_13_parametrizedTMClass_core`

Anchor Overview:70; native `TimeBounds:55`; source Corollary 13 p10. Its type is exactly the type of target 2: for every E,f,stream,source, coverage and a source-correct index imply stabilization of the specified labeled elimination learner. Every optional-output, witness-order, finite-source and absence-of-rate qualification from target 2 applies. It introduces no TM-specific Q class or new hypothesis.

The concrete interpreter elsewhere supplies genuine material for a future specialization, so this is not a claim that all machine foundations are missing. What is missing is the uniform clocked-enumeration construction for arbitrary computable monotone Q, the membership-to-candidate theorem and the effective canonical input/output interpretation. Thus this is a conditional convergence core, not an assembled formalization of the source's assertion that every such TM complexity class is algorithmically learnable. Neither the named complexity examples nor their functional interpretations are represented.

### 5. `GenLimit.LearningAlgorithmsLimit.Results.theorem_14_universalTBO_core`

Anchor Overview:86; native `TimeBounds:72,97,128`; source Theorem 14 pp10–11,21–22. Fix a simulator `Nat → Input → Nat → Option Output`, observation assignment, stream and source. Coverage, source-wise input-field coherence, and `∃ c, ∀x∈source, simulate c x (bound x)=some(value x)` imply stabilization to an index satisfying exactly that whole-source criterion. One candidate must work for all inputs; unrelated input-wise candidates do not suffice. Repeated input occurrences have the same supplied observation record.

This faithfully generalizes the elimination step once a suitable simulator/candidate is supplied. It does not translate approximate arbitrary-model runtimes through q-ECTT: q, a model, encoding and multiplicative slack are absent, and the simulator need not be monotone or effective. No actual task function outside the observed labels is identified. Zero bounds are syntactically permitted subject to candidate existence. Native Corollary 15 supplies a concrete TM case, but no complete arbitrary-model Theorem 14 wrapper or simulation premise exists elsewhere.

### 6. `GenLimit.LearningAlgorithmsLimit.Results.corollary_15_turingTBO`

Anchor Overview:103; native `TimeBounds:157–215`, `TuringMachines:30–173`; source Corollary 15 p11. For every finite encodable symbol type, decidable output equality and I/O interface, **the one specified learner** works for every finite target program, source, covering stream and coherent observation assignment satisfying a common-scale execution bound. Candidate naturals encode a scale and program. The learner runs each decoded candidate for its scale times the observed budget. The common scale is existential before all source inputs, and may depend on program, source and observations.

The conclusion supplies one stabilized candidate whose decoded program computes the observed value on each source input, with `∀x∈source, ∃budget`; it does not state recovery of the teacher or the final candidate's scale bound. This is substantial assembled native coverage, a faithful semantic specialization under conventional effective I/O. The arbitrary supplied I/O functions generalize representation while leaving an ordinary algorithm interpretation conditional. State 1 starts, state 0 halts; a zero execution budget cannot produce a value, so nonempty feasible source data exclude zero bounds/scales here. No rate or off-source behavior is asserted.

### 7. `GenLimit.LearningAlgorithmsLimit.Results.theorem_16_recursiveToRational_behavior`

Anchor Overview:113; native `Transducers:80–104`; source transition-diagram discussion p12. For every policy machine and finite prescribed scanned-symbol list, `tapeBehavior` equals the complete action-list component of the converted Mealy run. This is exact for those defined objects: `tapeBehavior` is defined by that expression. The empty list yields an empty action list; final state is not part of this equality.

It is only the local diagram correspondence within Theorem 16, not the learner reduction. No finite State, tape configuration, halting computation, scanned-source construction, learner or transformed observation stream occurs. Even infinite-state policy functions satisfy it. The separate real-tape interpreter is not connected to `PolicyMachine` by any exported theorem. To obtain the paper's claim requires constructing actual scanned histories and labels from PTOs, establishing source/prefix coverage, converting learner representations back to TMs, and proving source task correctness and stabilization. Those are missing assembly and bridge mathematics, rather than a false local equality.

### 8. `GenLimit.LearningAlgorithmsLimit.Results.theorem_16_rationalEnumeration_core`

Anchor Overview:120; native `Transducers:110–115`, `Enumeration:160,182`; source Theorem 16 pp12,22–23. For **any given** family `machines : Nat → Mealy State A B`, target index k, word stream and covered word source, the family-parametrized learner stabilizes to some index whose **whole List B output** agrees with machine k on every source word. The target index generates observations but is not a learner argument. Input is List A, semantic output is List B, and empty words have `some []`.

This faithfully generalizes convergence within a supplied countable family. It does not enumerate all finite FSTs: State/A/B need not be finite, family coverage and ordinary computability are not required, and the target is promised to occur in the family. No canonical state coding, all-size finite-machine enumeration or binary time guarantee appears elsewhere. Whole-sequence labels provide more information than final-symbol χ labels on an unchanged restricted source; prefix expansion can reconcile that difference, but is not assembled here. Native least-consistency lemmas do exist, so minimum-index elimination is not wholly absent; minimum-state FST enumeration remains absent.

### 9. `GenLimit.LearningAlgorithmsLimit.Results.theorem_17_lateSplit_characteristic_obstruction`

Anchor Overview:140; native `CharacteristicSets:85–116`; source late-distinction argument pp23–24. For a fixed natural threshold k, two Boolean models agree below k and differ at/above k. Their optional semantics is always defined. If a supplied set learner has characteristic cores for false and true, their union contains some n≥k. Cores may be infinite. At k=0 this still requires a union member. It does not force a late member in each core or specifically at k.

This is a faithful abstract specialization of the necessary-distinction component. It contains no halting instance, TM encoding, linear-time family, full PTO trace, computable bound β or computable core assignment. The learner returns a Boolean representation in this fixed two-model family. Thus the theorem is entirely compatible with computable threshold-dependent characteristic sets; it does not itself show uncomputability. The native census has no halting reduction connecting thresholds to representation-dependent bounds. That is genuinely missing negative-result mathematics, not merely omitted notation around this theorem.

### 10. `GenLimit.LearningAlgorithmsLimit.Results.theorem_17_mass_lower_bound_core`

Anchor Overview:158; native `CharacteristicSets:140–151`; source Theorem 17 pp12,23–24. With the same fixed-threshold Boolean models and two **finite** characteristic cores, the conclusion is `k+1 ≤ inputMass coreFalse + inputMass coreTrue`, where `inputMass S = ∑n∈S (n+1)`. The two masses are summed separately; overlap counts twice. No claim bounds each core individually, the union's mass, cardinality or sample-arrival time.

The distinction between numeric input n and length of a string is not represented by an encoding theorem. Nor is this source mass: source mass includes encoded outputs and full trajectories. A concrete lower bound could use input lengths, but the conversion is absent. This is a faithful auxiliary lower-bound pattern, not Theorem 17's quantification over every computable β on actual representations. It proves neither nonexistence of computable core assignments nor the linear-time strengthening. At k=0 the lower bound is one, so both empty cores cannot satisfy the hypotheses.

### 11. `GenLimit.LearningAlgorithmsLimit.Results.corollary_18_forgetting_preserves_indistinguishability`

Anchor Overview:178; native `ObservationForgetting:177`; source informational argument pp9,13. For arbitrary model/input/observation sorts and one fixed forgetting function, pointwise rich-observation equality on an input set implies pointwise forgotten-observation equality there. The map is the same for both models and independent of input. Empty input sets are vacuous; constant forget maps and infinite sets are allowed. There is no converse.

This exactly represents a generic equality-preservation fact used in an indistinguishability argument. It proves no learning or polynomial-data impossibility. Actual PTO/TBO/IOO types and projection maps are not instantiated. In particular, an arbitrary source TBO may be an approximate model-dependent runtime bound, rather than the exact trajectory length; its relationship to PTO data must be specified. The source can use the exact-runtime TBO case for a lower bound, but that specialization is absent. No computational complexity for forgetting is asserted.

### 12. `GenLimit.LearningAlgorithmsLimit.Results.corollary_18_characteristic_bound_lifts_to_richer_observations`

Anchor Overview:188; native `ObservationForgetting:25–83`; source Corollary 18 p13 and p9 monotonicity. Fix one poor-observation set learner, rich observations, a forgetting map, semantic maps, source, an arbitrary input-set mass and model bound. If each model has a poor characteristic core satisfying that bound, each has such a rich core for the fixed learner that first forgets. The same core and numerical mass can be reused. Model-wise existence does not produce a computable core-finding program.

This is a faithful generalization of characteristic correctness transfer. It has no finiteness, polynomial growth, ordinary learner algorithm or runtime requirement. Crucially, mass is **the same function of the input set** on both sides. Actual source observation mass changes when rich traces are retained; the theorem supplies no bound relating those masses. Together with a concrete input-length obstruction it could contribute to Corollary 18, but that obstruction is not instantiated for TMs. No complete IPTD conclusion occurs elsewhere in the census. Empty sources are permitted and correctness is vacuous.

### 13. `GenLimit.LearningAlgorithmsLimit.Results.theorem_21_tagged_two_step`

Anchor Overview:213; native `TaggedSimulation:19–93`; source tagged path p24. For arbitrary decidable State/Tape, machine M, state q and symbol a, the tagged Mealy machine on `[inl a,inr(q,a)]` returns the original next state as a normal state and **both** actions: write the unique `(q,a)` tag/stay, then the lifted original write/move. Tagged states and symbols use disjoint sums, so tags cannot equal ordinary symbols. The identity does not depend on starting at M's initial state.

This faithfully generalizes the local two-transition mechanism, including final state and complete output list. It does not construct a finite TM for each total computable f, establish tape output or halting preservation, or discharge the paper's no-stay starting-machine assumption. Native tagging can lift even a stay action; that generalization is valid for prescribed words but not an assembled source construction. Mismatched tags are handled by other defined cases, not by this equality. No sample bound or MSM result follows from the identity alone.

### 14. `GenLimit.LearningAlgorithmsLimit.Results.taggedMachine_runFrom`

Anchor Overview:223; native `TaggedSimulation:104–138`; source two-step simulation p24. For every finite untagged scanned word w and state q, running the tagged machine on the recursively generated tagged word returns the original final state lifted into normal states and exactly the recursively generated tagged action list. The word encoding threads M's true state: each original symbol a at q contributes the matching `(q,a)` tag. It is not a fixed model-independent map of input symbols. The empty word gives zero steps and empty actions.

This is substantial full-word simulation infrastructure. Native `taggedScannedFrom_length` also states precisely twice the original word length. However, a doubled synthetic scanned-word length is not yet twice an actual TM halting time: no theorem connects those words to runs of the real tape interpreter. No finite alphabets/states are required, and the source's task-output preservation, representation-size cost, learning behavior and observation-tree correctness remain outside this theorem. Its correspondence is faithful at the transition-system level, incomplete for Theorem 21.

### 15. `GenLimit.LearningAlgorithmsLimit.Results.theorem_21_transition_cover_core`

Anchor Overview:233; native `TaggedSimulation:148–209`; source p25 cover argument/remark. Given a finite used-transition set U, exercise relation and **supplied** witness sample W(e) for each e∈U, every covered source containing those witnesses satisfies three conjuncts: the image cover has cardinality ≤|U|; every used transition is exercised by a member of that cover; and one finite stream prefix contains every cover sample. The witness map precedes stream/source; appearance time follows them and can depend on the entire stream.

This faithfully generalizes finite transition coverage and exhaustion. Duplicate witnesses can shrink the cover. Empty U yields empty cover, vacuous exercise obligations and possible prefix length zero. Coverage allows arbitrarily late appearances, so |cover|≤|U| is neither a uniform time nor arbitrary-stream sample-count bound. More importantly, no learner appears: coverage has not been proved sufficient for MSM correctness, characteristic status or representation stabilization. The used transitions and witnesses are not constructed from a tagged TM/source. The source's polynomial characteristic-curriculum interpretation cannot be obtained by dropping those missing links.

### 16. `GenLimit.LearningAlgorithmsLimit.Results.theorem_21_msm_merge_order_core`

Anchor Overview:251; native `MSMMergeOrder:34–249`; source claimed merge order p25. Fix finite candidates per configuration, natural scores, merge, remaining measure, intended relation, Sound/Complete predicates and initial configuration. Its six premises are: initial soundness; at every sound incomplete configuration an intended candidate of score ≥2; every unintended candidate there has score ≤1; intended merges preserve soundness; sound complete configurations are terminal; and **all** maximum-positive choices strictly decrease remaining, even off the sound region. The conclusion has four parts: some final configuration is finitely reachable, sound, complete and terminal.

This is a useful conditional greedy argument, with ties among maxima allowed and zero-step reachability possible. It asserts existence of a reachable terminal configuration, not a specified executable learner or unique representation. Supporting native results additionally preserve soundness along runs and establish well-foundedness under descent; they are credited. But score separation, actual observation-tree similarity, quotient validity, concrete intended-state soundness and learning completeness are supplied as assumptions, not proved for the tagged construction. Complete-to-terminal can also be stronger than the source's statement that later harmless merges may occur. Theorem 21 therefore still lacks central native mathematics, not merely a wrapper joining already proved facts.

## Complete source-to-native coverage beyond the facade

The module census supports the following closure assessment. `Definitions` has nine framework declarations; `Enumeration` has the generic finite-consistency algorithm and rejection/stabilization results; `TimeBounds` supplies the abstract cores and assembled TM TBO result; `TuringMachines` supplies the real interpreter and encoding identities; `Transducers` supplies total Mealy runs, policy conversion, output lengths and given-family enumeration. `CharacteristicSets`, `ObservationForgetting`, `TaggedSimulation` and `MSMMergeOrder` supply precisely the local results described above. The four shared Core modules supply lists, finite samples, presentations and stabilization; their language-generation/sample lemmas do not establish any missing P11 lower bound or automata algorithm. The facade has the 16 selected theorem types; the umbrella adds no declarations.

| Inventory component | Full-census disposition |
| --- | --- |
| Finite FST definition; seq2seq execution | Mealy start/step/run represented, generalized beyond finite state; no certified finite representation family |
| Nerode relation/rational finite-index definition | Not represented; `rationalSemantics` is just optional whole-list execution |
| Partial FSTs, quotients, apartness | Not represented concretely; arbitrary merge functions are not quotient transducers |
| TM tape action and finite program execution | Represented with different explicit finite-list representation and supplied I/O |
| State count and O(n log n) representation bound | Not represented; no state-size complexity theorem |
| Reasonable encodings, CTT/q-ECTT assumptions | Not represented as native predicates/assumptions; no FOL encoding framework |
| Symbolic universe and perception-local agents | Not represented; policy start/step is a narrower interface with a different semantic task |
| Restricted-source exact representation stabilization | Represented semantically; ordinary algorithm qualification absent in generic definitions |
| Characteristic sets, mass, RIPTD/IPTD/RIPTS | Set correctness represented; source full-observation mass and polynomial/time predicates absent |
| Lemmas 9/25 | Common-source optional-semantics variant represented; partial-domain source gap remains |
| Gold Theorem 10 | No native diagonalization or nonlearnability theorem |
| Theorem 12/Corollary 13 class coverage | Conditional elimination only; actual Q class and clocking assembly absent |
| Minimum-index convergence for generic elimination | `enumeration_stabilizes_to_least` represented; this does not validate budget-first minimum-state claim |
| All-stage consistency of paper's search | Not represented for that algorithm; finite index cap can fall back to inconsistent 0 initially |
| Polynomial-time capped/incremental learner variants | Not represented; no cost model or incremental implementation theorem |
| Universal arbitrary-model TBO under q-ECTT | Candidate-fitting core only; simulation/encoding assembly absent |
| TM TBO learning | Assembled semantic finite-program theorem represented; effective conventional I/O specialization needed |
| Actual PTO→FST source/prefix reduction | Local prescribed-word equality only; no learner or source transformation |
| Enumeration of all rational maps | Given-family convergence only; finite variable-state machine enumeration absent |
| Halting-derived linear-time machine pairs | Not represented; Boolean threshold family is not such an implementation |
| No computable mass bound / no computable cores | Neither conclusion represented; required reduction and representation dependencies absent |
| IOO/TBO/PTO non-IPTD | Generic forgetting infrastructure only; no concrete impossibility assembly |
| Rational restricted-source non-RIPTD | Not represented; depends on unassembled reduction and negative-result transfer |
| Observation trees, cascading merger, score | No concrete representation or implementation; abstract score relation only |
| O(n|A|), O(n), O(n^4) guarantees | Not represented anywhere in native types |
| MSM failure for unrestricted rational sources | No concrete counterexample/native impossibility theorem |
| Theorem 21 existence of total-function teacher | Tagged policy constructor only; no total-recursive f or actual teacher-program bridge |
| Exact factor-two simulation | Word-length doubling and state/action identities present; actual tape/time/output preservation absent |
| ≤m covering examples | Finite-cover cardinality and eventual appearance present; characteristic/learning implication absent |
| Tagged data imply greedy score gap | Not proved; quantified premise in target 16 |
| Actual MSM convergence and stable representation | Not represented; conditional finite abstract run is insufficient |
| Theorem 22 canonical/minimum/isomorphic FST | Not represented, despite basic Mealy execution being present |
| Theorem 23 all algorithm/time/distinguisher clauses | Not represented; none follows from run-output-length identities |
| Proposition 24 decoder existence and coverage | Decode-encode identities present; bare code enumeration repeats invalid/default codes |
| Proposition 24 bijection/order/o(log n)/poly decoder | All four quantitative/structural guarantees absent |
| A.3–A.4 interpretations; open questions | No native theorem expected for narrative/open problems; not counted as solved claims |

This separates missing wrappers from missing mathematics. One could add wrappers specializing some abstract elimination results after defining clocked families and effective interfaces; the census already supplies the relevant elimination lemma. For Theorem 16, more substantive tape/source/prefix and representation-conversion bridges are needed as well. For Theorem 17 the halting reduction and its linear-time/full-behavior construction are genuinely absent. For Theorem 21 the concrete tree/quotient framework and the score-separation proof are genuinely absent. No absence conclusion relies on the historical facade-only loading boundary.

## Source questions and discrepancies requiring Stage 3 discussion

1. **Partial domains in Lemmas 9/25.** On the literal Definitions 7–8 interpretation, take I=N, M the total zero function and N the zero function defined only at 0. A learner always outputting M is correct on every allowed source for either model. Empty characteristic cores satisfy the stated correctness requirement for both, yet their union has no distinguishing input. The functions differ in domain. Thus the printed lemma needs a restriction on what “distinct” means, a common defined source, or a stronger correctness requirement. Lean's full common-source Option equality changes this issue; it does not silently prove the printed partial-domain statement. This is a source-level counterexample analysis, not a proof-body audit.

2. **Minimum-state/budget-first argument, p21.** The paper moves from the first feasible budget to a larger bound sufficient for its preferred index without proving the learner reaches that larger bound. Repeated finite sources make the gap visible. The native diagnostic illustrates the budget phenomenon, but is not itself a complete actual-TM counterexample. This challenges the named proof/minimality refinement, not the main existence-of-learning theorem. Native least-consistent-index convergence applies to a different fixed-candidate semantics.

3. **Mass versus information, pp9,13.** A characteristic input set can be reused after forgetting, but full observation mass can change when trajectories are added. Source claims of mass monotonicity or Corollary 18 need an input-length obstruction or an explicit mass comparison, not equality preservation alone. The halting-pair proof may supply the needed stronger obstruction; it has not been formalized here. Target 12 only transfers a fixed input-set measure.

4. **MSM proof, pp24–25.** The official PDF prints an incomplete dummy-state clause and asserts that correct computing-state merges have greater similarity without a complete argument covering tree occurrences, ties and all restricted sources. Target 16 assumes precisely a sufficient gap rather than deriving it. I do not conclude that Theorem 21 is false. Its sample remark is a bound on a chosen covering curriculum, not on the number of observations in every adversarial order. Exact representation stabilization also needs a stated representation convention if only source behavior stabilizes.

5. **Other literal boundaries.** Page 23 concludes containment in Σ^B from a ≤B length bound, which requires clarification as bounded-length notation or an extra argument. It references “Theorem 9” and contains an `NT,x` typo. Page 24 uses a union where the earlier reduction uses a product output alphabet. These are confirmed source text, not extraction mistakes. Theorem 10's finite-alphabet wording also leaves the empty-alphabet case: Σ* is then a singleton and its unique total self-map is trivially learnable. Definitions 7–8 do not reconcile finite ordered histories with arbitrary containing sets. The source-only inventory called characteristic data finite in its intended interpretation; the literal definition does not explicitly impose that qualification, and this report corrects that phrasing rather than silently adding it.

Proposition 24's little-o and polynomial binary decoder were visually confirmed; I found no source contradiction there. They require separate formal guarantees and cannot be inferred from `Encodable` or a defaulting decoder. Likewise source proofs are context, not certified derivations. No conclusion about those proofs' correctness has been imported from diagnostic theorem names.

## Stage 1 corrections and remaining limits

The frozen Stage 1 report accurately reconstructed the 16 target types, especially complete output lists in target 8, the final configuration witness in target 16, one source-wide scale in target 6, both masses in target 10 and all four diagnostic conjuncts in target 3. I found no binder or conjunct error requiring a textual correction to its code-only reconstruction. Its warnings about arbitrary functions, lack of finite-state assumptions, set/list interfaces and empty-source coverage are retained.

Stage 1 is not the native coverage boundary. This report adds the full census, the actual tape interpreter, program decoding, generic least-index stabilization, soundness-along-runs, well-foundedness, and word-length doubling. Conversely, names such as “universal,” “rational,” “mass lower bound” and “MSM” do not expand those types into the source's complete claims. Stage 1's absence of source correspondence was intentional; it neither established nor denied the paper coverage assessed here.

No decisive missing interface request was necessary: the full census supplies the project definitions needed to interpret every selected statement and determine the claimed native gaps. Remaining questions concern source interpretation and unproved source-to-native assembly, not inaccessible proof bodies. The finding is limited to the supplied frozen package and trusted exporter/standard-library boundary. It certifies neither proofs nor compilation nor human review. Stage 3 material stayed closed through report freeze.
