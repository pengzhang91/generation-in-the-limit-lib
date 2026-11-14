# P39 Stage 2 source comparison

The deterministic recursive patient-scope construction and its partial-enumeration extension are represented at the semantic statement level. Literal v1 uses a different criticality predicate; generic v1 algorithm correctness cannot be identified with the recursive machine. Deterministic optimality upper bounds and the randomized, multi-order, q-output and infinitely-often-accuracy extensions are not represented in this supplied snapshot.

Completed 2026-11-14T07:04:45.893065+00:00. This is a statement/definition correspondence review, with no proof certification, implementation change, or human-review credit.

## Identity, freeze and scope

Package: `REMAINING8_2026-11-14_ca97f2b/P39`. The exported Lean snapshot reports source SHA-256 `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc`; this is frozen package provenance, not an independently inspected source tree. All six frozen inventory/Stage 1 artifact hashes match their freeze manifests. The source inventory was frozen at 2026-11-14T06:48:30.614921+00:00 before this comparison was authorized; Stage 1 was independently frozen at 2026-11-14T06:42:14.572059+00:00.

There are 44 current source slots, 32 distinct registered Lean targets, 166 recursive interface declarations and 1,257 native census declarations. Every slot is compared below, and all 32 registered targets have a reverse-mapping dossier. Native declaration names were locators; decisive types and definition values were checked directly.

| Edition | Source date | Expected PDF SHA-256 | Verification |
|---|---|---|---|
| earlier-supplied-manuscript | Manuscript PDF creation metadata 2026-07-10; no publication date asserted | `1a9a81a7aa02719f5cfe852746f3db853d47d42f699e8f62cc78f451ef7cb23e` | Raw hash and local decisive images verified |
| arxiv-2608-01320-v1 | 2026-08-02 (v1 author version) | `295b7ea54afd3859c4ff3baef4cf8e1e655824f3efd240699d7df429cf68b676` | Exact remote edition text verified; raw bytes and usable images unavailable |
| arxiv-2608-01320-v2 | v2 exact identity; version date not supplied in manifest | `8dfc7ada39b62bb79d380331deeb4377035ec35d26b8334c2c6c6a91cb711b08` | Raw hash and local decisive images verified |

The exact v1 [PDF](https://arxiv.org/pdf/2608.01320v1) and supplementary [author HTML](https://arxiv.org/html/2608.01320v1) were read during the source-first phase. Their formulas were not silently replaced by v2. Printed and one-based PDF locations for every slot are retained below and in the frozen inventory.

## Independent source inventory and shared comparison rules

The complete 44-item independent inventory is preserved in [source-inventory.md](source-inventory.md) and [source-inventory.json](source-inventory.json). Its standing assumptions and per-edition definitions are incorporated into each object in [stage2-claims.json](stage2-claims.json).

**representation:** Lean uses Nat, zero-based candidate indices and rounds, scope [0,s), and ambient counting below n. Source candidate i corresponds to Lean i−1; source round t corresponds to Lean t−1. Source positive values embed unchanged in Nat with 0 omitted from those languages. General Nat languages add a harmless lower-end generality. Inclusive source prefixes correspond to a one-unit ambient cutoff shift. Target-rank density avoids sparse-target normalization loss.

**model:** OracleFamily stores infinitely many indexed semantic languages, infinitude proofs and a Boolean membership query with its specification. Presents is equality between stream range and target, without injectivity. Thus v2’s repetition-free streams form a subclass; earlier/v1 do not explicitly prohibit repetitions.

**computation:** The named machine output O stream is independent of target index z and of an enumerated subset E. Its round decision reads the observed prefix; exact recursive criticality uses set inclusion and Classical.propDecidable, and fallback selection tests unbounded existence. No effective subset oracle, executable finite-query implementation, complexity bound or computable stabilization rate is established. Partial closure additionally selects intersections by the semantic infinitude predicate.

**quantifiers:** The construction is a fixed named function g_O(stream,t), followed by ∀ target z and ∀ presenting streams. Each existential validity threshold follows O, stream and target and may depend on them. Density is outside that time existential. The threshold/certificate can use future-dependent classical choices without being an input to the generator.

**ownership:** AdversaryFirst uses absence from generator outputs at s<t; GeneratorFirst uses absence from adversary announcements at s≤t. This represents adversary-first turn order and distinct values, not multisets of rounds or output probability supports.

**rates:** Represented numerical guarantees are target-relative liminf density ≥1/2, partial density ≥α/2 and settled switch-loss count ≤Nat.log2(target prefix count). Nat.log2 is the integer floor version when the target count is positive. No uniform time-to-validity bound follows from exponential waiting.

**limits:** Comparison concerns the supplied frozen statement/definition snapshot only. Theorem proof bodies, raw Lean comments, owner explanations, PaperMaps, old audits and Stage 3 context remain excluded. No proof certification or human-review credit is assigned.

The earlier manuscript and v2 use recursive criticality. V1 instead requires inclusion in every earlier consistent language. Lean has both predicates, but `PatientMachine.criticalIndices`, `IsFocus` and the actual state machine use only `RecursiveCritical`.

The full source deterministic theorems say the ratio is optimal. Their positive half guarantee is represented; no native upper-bound theorem on arbitrary generators was found. This grouped difference is scored partial even where achievability is a faithful generalization.

## Full comparison matrix

| Slot | Edition; printed / PDF pages | Correspondence | Component result |
|---|---|---|
| C01 | earlier-supplied-manuscript; 13 / 15 | equivalent | The semantic round machine matches the earlier recursive patient-scope/backtracking procedure after index/time translation. |
| C02 | earlier-supplied-manuscript; 7 / 9 | equivalent | Target-rank liminf is equivalent to the source ambient-prefix target-relative ratio. |
| C03 | earlier-supplied-manuscript; 7 / 9 | not-covered | No universal deterministic half-density upper bound or legal catch-up adversary is represented in the supplied native census. |
| C04 | earlier-supplied-manuscript; 9–10 / 11,12 | faithful-generalization | RecursiveCritical is the literal recursive condition, extended to arbitrary semantic candidate sets and streams. |
| C05 | arxiv-2608-01320-v1; 10 / 12 | faithful-generalization | Critical matches the literal v1 all-earlier-consistent definition; including the equal index adds only reflexive containment. |
| C06 | earlier-supplied-manuscript; 14 / 16 | equivalent | The same named recursive generator has eventual target membership and global novelty. |
| C07 | arxiv-2608-01320-v1; 14–15 / 16,17 | substantively-different | The closest native validity result is for the recursive machine, while literal v1 defines its focus using all earlier consistent languages. |
| C08 | earlier-supplied-manuscript; 14–16 / 16,17,18 | equivalent | Native types recover old-focus membership, strict predecessor comparison, target support and injective predecessor pairing for the recursive machine. |
| C09 | arxiv-2608-01320-v1; 15 / 17 | partial | The nonswitch local relation is represented for the recursive machine; the literal v1 machine is not the witness of that theorem. |
| C10 | earlier-supplied-manuscript; 15–16 / 17,18 | faithful-specialization | The logarithmic loss bound is recovered at the explicit settled criticality-and-scope cutoff, resolving the earlier loose generation-start language. |
| C11 | arxiv-2608-01320-v1; 15–16 / 17,18 | substantively-different | The native logarithmic charging bound concerns recursive-machine switch losses, not the literal v1 all-consistent procedure. |
| C12 | earlier-supplied-manuscript; 16; upper bound 7 / 18,9 | partial | The full earlier deterministic achievability and validity are represented, but its grouped worst-case optimality claim is not. |
| C13 | arxiv-2608-01320-v1; 16–17; upper bound 8 / 18,19,10 | partial | Recursive-machine half-density existence and validity are available; literal v1 algorithm identity and the upper-bound half of optimality are not. |
| C14 | earlier-supplied-manuscript; 16–17 / 18,19 | faithful-specialization | The exact source family and target have a concrete increasing-4-multiples witness with output 2t+1, zero density and failed validity. |
| C15 | arxiv-2608-01320-v1; 17–18 / 19,20 | faithful-specialization | An unlinked native counterexample realizes the v1 example with the explicit increasing enumeration of multiples of 4. |
| C16 | earlier-supplied-manuscript; 17–18 / 19,20 | equivalent | The closure-based named generator eventually produces fresh elements of the original target, with no requirement to stay in the enumerated subset. |
| C17 | arxiv-2608-01320-v1; 18–19 / 20,21 | substantively-different | The native closure-validity theorem uses a recursively critical machine; literal v1 has the all-consistent criticality definition. |
| C18 | earlier-supplied-manuscript; 18–19 / 20,21 | equivalent | The same closure-based generator has full eventual validity and density at least half the lower density of the infinite enumerated subset. |
| C19 | arxiv-2608-01320-v1; 19 / 21 | partial | The α/2 existence guarantee and validity are available for a recursive closure generator, not the literal v1 construction. |
| C20 | arxiv-2608-01320-v1; 20–27; 39–43 / 22,23,24,25,26,27,28,29,41,42,43,44,45 | not-covered | v1 randomized 1−1/e achievability is not represented in the supplied census. |
| C21 | arxiv-2608-01320-v1; 20; 26–28 / 22,28,29,30 | not-covered | v1 randomized 1−1/e upper bound is not represented in the supplied census. |
| C22 | arxiv-2608-01320-v1; 28–34; 43–47 / 30,31,32,33,34,35,36,45,46,47,48,49 | not-covered | v1 simultaneous finite-order half-density construction is not represented in the supplied census. |
| C23 | arxiv-2608-01320-v1; 35; 47–52 / 37,49,50,51,52,53,54 | not-covered | v1 simultaneous finite-order randomized 1−1/e construction is not represented in the supplied census. |
| C24 | arxiv-2608-01320-v2; 13–14 / 15,16 | faithful-generalization | The source v2 recursive machine is represented, with total off-model behavior and support for repeated presenting streams. |
| C25 | arxiv-2608-01320-v2; 7 / 9 | equivalent | The target-rank definition and native ambient-ratio equality recover v2 lower density. |
| C26 | arxiv-2608-01320-v2; 7–8 / 9,10 | not-covered | No native arbitrary-generator half-density impossibility theorem or sparse catch-up adversary construction was found. |
| C27 | arxiv-2608-01320-v2; 10 / 12 | faithful-generalization | The recursive predicate is literal v2 criticality, with arbitrary candidate sets and streams permitted. |
| C28 | arxiv-2608-01320-v2; 10 / 12 | faithful-generalization | All three source chain-dynamics clauses are represented, and the transition lemmas hold over arbitrary t≤u. |
| C29 | arxiv-2608-01320-v2; 10 / 12 | faithful-generalization | Every target presented as the stream range is eventually permanently recursively critical. |
| C30 | arxiv-2608-01320-v2; 10–11 / 12,13 | faithful-generalization | Fixed-scope survival preserves the focus and all in-scope criticality statuses. |
| C31 | arxiv-2608-01320-v2; 12 / 14 | faithful-generalization | SwitchRound is precisely current announcement outside the pre-round focus. |
| C32 | arxiv-2608-01320-v2; 15 / 17 | faithful-generalization | Full eventual target validity and novelty hold for the same named recursive generator, also for repeated legal presentations. |
| C33 | arxiv-2608-01320-v2; 15–17 / 17,18,19 | faithful-generalization | The local nonswitch theorem states both old-focus membership and a strict predecessor inequality; supporting native types provide the target-owned injection used later. |
| C34 | arxiv-2608-01320-v2; 15–16 / 17,18 | faithful-generalization | The same settled machine loses at most log2 of the actual target-prefix count in every ambient prefix, with repeated presentations permitted. |
| C35 | arxiv-2608-01320-v2; 16–17; 7–8 / 18,19,9,10 | partial | Deterministic half-density achievability and full validity are represented for the same v2 recursive machine; the grouped optimality upper bound is absent. |
| C36 | arxiv-2608-01320-v2; 17 / 19 | not-covered | The q-output extension is not represented beyond the single-output q=1 case. |
| C37 | arxiv-2608-01320-v2; 17 / 19 | not-covered | No statement that the named patient-scope focus equals K infinitely often was found in the native census. |
| C38 | arxiv-2608-01320-v2; 18; 39–40 / 20,41,42 | equivalent | The complete v2 counterexample bundle and its focus arithmetic are present natively. |
| C39 | arxiv-2608-01320-v2; 40–41 / 42,43 | faithful-generalization | The retained-infinite-intersection generator is valid in the original target for any repeated or unrepeated presentation of an infinite partial subset. |
| C40 | arxiv-2608-01320-v2; 41 / 43 | faithful-generalization | The full α/2 partial-enumeration statement, including same-generator validity, holds under the broader repeated-stream model. |
| C41 | arxiv-2608-01320-v2; 18–26; 41–46 / 20,21,22,23,24,25,26,27,28,43,44,45,46,47,48 | not-covered | v2 exact randomized single-order theorem is not represented in the provided native snapshot. |
| C42 | arxiv-2608-01320-v2; 19; 25–26 / 21,27,28 | not-covered | v2 randomized upper bound is not represented in the provided native snapshot. |
| C43 | arxiv-2608-01320-v2; 27–34; 47–52 / 29,30,31,32,33,34,35,36,49,50,51,52,53,54 | not-covered | v2 simultaneous deterministic finite-order theorem is not represented in the provided native snapshot. |
| C44 | arxiv-2608-01320-v2; 35; 52–58 / 37,54,55,56,57,58,59,60 | not-covered | v2 simultaneous randomized finite-order theorem is not represented in the provided native snapshot. |

Counts: equivalent: 8, faithful-generalization: 13, faithful-specialization: 3, not-covered: 12, partial: 5, substantively-different: 3. These are correspondence categories, not proof-validity verdicts.


## Per-slot component and discrepancy notes

Source statements, standing assumptions and complete direct-anchor lists are preserved per slot in [stage2-claims.json](stage2-claims.json); the frozen inventory supplies source wording and proof context. T01–T32 refer to the shared reverse dossiers below. Additional native anchors are named only when they add evidence beyond those targets.

### C01

Initialization and exponential waiting: represented. All on-model backtracking branches and minimum fresh output: represented. Off-model total fallback: additional Lean behavior outside source plays.

The age field makes the source prose timing precise; initial age=0, and a focus-changing round resets age to 1. This is a scoped definition comparison, not a trace-by-trace proof audit. A membership query field does not make the classical inclusion-based machine effective.

Evidence: T15, T23, T27; native `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.processRound`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C01.

### C02

Definition of density and target intersection: represented. Ambient/target-rank bridge: native equality theorem inspected.

The definition accepts arbitrary A and counts its intersection with K implicitly; source applications use D∩K. Empty early prefixes use Lean real division/zero conventions, with no asymptotic change.

Evidence: T26; native `GenLimit.PatientScope.relativeLowerDensity_eq_liminf`, `GenLimit.KleinbergWei.OrderedLanguage.increasing_lowerDensity_eq_liminf`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C02.

### C03

Worst-case upper bound: not covered. The available half theorem is achievability; upperDensity_le_one only bounds density by 1.

The earlier source least-free adversary paragraph omits catch-up enumeration details. This source issue does not turn the lower-bound theorem into an upper bound.

Evidence: T17; native `GenLimit.KleinbergWei.OrderedLanguage.upperDensity_le_one`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C03.

### C04

Least-consistent base and recursive earlier-critical inclusion: represented.

Lean imposes no infinitude or presentation assumption on this predicate itself; source applications restrict those inputs.

Evidence: T27; native `GenLimit.RecursiveCritical.match_1`, `GenLimit.Consistent`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C04.

### C05

All earlier consistent candidates: represented. This definition is separate from the recursive predicate used by the machine.

Its presence does not establish correctness of a v1-criticality patient-scope machine.

Evidence: T01; native `GenLimit.Consistent`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C05.

### C06

Eventual membership: patient_validity. Freshness against current/prior adversary values and all prior outputs: combined theorem and native freshness types. Density is an additional conjunct for that same generator.

patient_validity alone asserts membership only; the combined endpoint is needed for full source validity.

Evidence: T16, T18; native `GenLimit.PatientMachine.stream_ne_output`, `GenLimit.PatientMachine.output_ne_of_lt`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C06.

### C07

Eventual-validity shape: available for a recursive machine. Validity of the literal v1 all-consistent machine: not established.

The witness changes at the criticality definition, before any proof question arises. This is a possible intended source correction, not evidence of a Lean bug.

Evidence: T16, T18, T01; native `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.stream_ne_output`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C07.

### C08

Local nonswitch membership and comparison: represented by fact_3_13. Late target-owned predecessor support, strict inequality and injectivity: represented by the three partner theorems.

The registered endpoints omit the direct old-focus membership theorem, but it is in the native census. Fresh first occurrence and an existing preceding round are explicit; the target-support theorems require a supplied validity threshold. These match the source’s late counting use.

Evidence: T19, T20, T21, T22, T13; native `GenLimit.PatientMachine.gameTrace`, `GenLimit.PatientMachine.lateSwitchLoss`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C08.

### C09

Old-focus membership plus comparison: covered for recursive output. Same statement for literal v1 output: not linked or supplied.

The minimum-output reasoning is common, but no equality between the two generic algorithms is available. The missing registered endpoint alone was not treated as absence.

Evidence: T13, T22, T01; native `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.previous_output_le`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C09.

### C10

Bound on settled fresh switch-loss values: represented, with actual target-prefix count inside log2. Named concrete tau/charge certificate: represented. Pairwise disjointness of charge sets, asserted in the source proof: not a certificate field or native theorem found.

The selected cutoff can be later than an arbitrary earliest output-validity time. The abstract certificate uses positive injective tau labels and individual exponential charges; it does not assert the source proof’s stronger disjointness/sum claim. The lemma conclusion remains represented without that proof-payload assertion.

Evidence: T24, T25, T14; native `GenLimit.PatientMachine.StableTargetRun.charge_card`, `GenLimit.PatientMachine.settledThreshold`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C10.

### C11

Numerical logarithmic statement: represented for the recursive witness. Literal v1 witness and its claimed history mechanism: not established.

Criticality substitution and a precisely settled cutoff are material changes. They should be adjudicated as source-correction questions.

Evidence: T14, T24, T25, T01; native `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.StableTargetRun.charge_card`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C11.

### C12

Named recursive generator achieves density ≥1/2: represented. Same generator is valid: represented. No deterministic generator can guarantee more: not covered.

A lower-bound theorem does not certify optimality. The bound is a guaranteed minimum, not equality on every play.

Evidence: T17, T16, T26; native `GenLimit.PatientScope.relativeLowerDensity_eq_liminf`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C12.

### C13

Existence of a semantic deterministic half-density generator: covered. Correctness of the literal v1 algorithm: changed witness. Optimality upper bound: not covered.

The numeric existential result survives use of a different named witness; the source’s named-algorithm claim must retain the criticality difference.

Evidence: T17, T16, T01; native `GenLimit.PatientMachine.criticalIndices`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C13.

### C14

Family and target arithmetic: represented after index shift. Presentation, odd outputs, invalidity and zero density: represented, including native bundle and empty target-owned output set. Unique recursive focus: represented.

The earlier example leaves the enumeration order unspecified. Lean supplies the increasing order. It proves the intended counterexample witness, not an all-orders assertion that outputs are always odd.

Evidence: T05, T06, T07, T04; native `GenLimit.PartialEnumeration.Counterexample.run_focus_eq_zero`, `GenLimit.PartialEnumeration.Counterexample.family`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C14.

### C15

Same source arithmetic family, target, partial set and increasing witness: represented. Zero density, invalidity and fixed focus for recursive machine: represented.

For this particular family both criticality predicates select only the first language by direct inspection: that first language stays consistent, and every later tail contains a value 2 mod 4 absent from it. Thus the example transfers without identifying the generic v1 and recursive algorithms. No native theorem specifically names an all-consistent machine; this source-specific transfer is a definition-level mathematical comparison.

Evidence: T04, T05, T06, T07, T01; native `GenLimit.PartialEnumeration.Counterexample.run_focus_eq_zero`, `GenLimit.PartialEnumeration.Counterexample.family`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C15.

### C16

Infinite partial subset and target containment hypotheses: represented. Removal of finite intersections and increasing enumeration of retained binary codes: represented semantically. Persistent critical subset and full eventual validity: represented.

The source binary code is distinct from the Lean reindexed closure index. closureCode translates between them. Infinitude filtering is classical and is not computable from the membership-query interface alone.

Evidence: T08; native `GenLimit.PartialEnumeration.exists_eventually_critical_subset_target`, `GenLimit.PartialEnumeration.closureCode`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C16.

### C17

Intersection preprocessing and eventual validity shape: represented for the recursive construction. The literal v1 closure-machine witness: not established.

The source proof’s original binary index is replaced by a retained-code enumeration in Lean, which is a faithful implementation of discarding finite intersections; the criticality change is the material difference.

Evidence: T08, T01; native `GenLimit.PartialEnumeration.exists_eventually_critical_subset_target`, `GenLimit.PartialEnumeration.closureCode`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C17.

### C18

α is tied by equality to the lower density of K′ in K: represented. α/2 inequality and full validity for the same named output: represented. No need to supply α, E or target z to the generator: confirmed in definitions.

The registered density endpoint alone omits validity; theorem_B_3_with_generation supplies it for the same witness.

Evidence: T09, T08, T10, T11; native `GenLimit.PartialEnumeration.exists_eventually_critical_subset_target`, `GenLimit.PartialEnumeration.closureCode`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C18.

### C19

Semantic existence of a valid generator with the stated α/2 coverage: covered. Literal v1 named-algorithm identity: not covered.

No inequality permits replacing the actual α by an arbitrary free requested performance value; the equality premise fixes it. Criticality changes the named witness, even though the numerical existential conclusion is recovered.

Evidence: T08, T09, T10, T11, T01; native `GenLimit.PartialEnumeration.exists_eventually_critical_subset_target`, `GenLimit.PartialEnumeration.closureCode`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C19.

### C20

Source full theorem and associated appendix algorithm: not covered. Generic single-order deterministic density definitions/results are support only.

Census type/value search found no probability/expectation, finite random-permutation algorithms, or single-generator simultaneous finite-order guarantee. A fixed single-order half result does not realize these claims.

Evidence: T17; native `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C20.

### C21

Source full theorem and associated appendix algorithm: not covered. Generic single-order deterministic density definitions/results are support only.

Census type/value search found no probability/expectation, finite random-permutation algorithms, or single-generator simultaneous finite-order guarantee. A fixed single-order half result does not realize these claims.

Evidence: T17; native `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C21.

### C22

Source full theorem and associated appendix algorithm: not covered. Generic single-order deterministic density definitions/results are support only.

Census type/value search found no probability/expectation, finite random-permutation algorithms, or single-generator simultaneous finite-order guarantee. A fixed single-order half result does not realize these claims.

Evidence: T17; native `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C22.

### C23

Source full theorem and associated appendix algorithm: not covered. Generic single-order deterministic density definitions/results are support only.

Census type/value search found no probability/expectation, finite random-permutation algorithms, or single-generator simultaneous finite-order guarantee. A fixed single-order half result does not realize these claims.

Evidence: T17; native `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C23.

### C24

Source initialization, waiting, backtracking and minimum fresh output: represented. No-repetition source setting is included among Lean streams.

Presents does not require injectivity. This broadens the legal-input class; it does not weaken source conclusions. Exact inclusion and code selection remain semantic rather than executable oracle operations.

Evidence: T15, T23, T27; native `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.processRound`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C24.

### C25

Target intersection, liminf and first-ownership convention: represented. Rank/ambient equivalence: represented.

A single-order semantic density definition is not a randomized or simultaneous multi-order theorem.

Evidence: T26; native `GenLimit.PatientScope.relativeLowerDensity_eq_liminf`, `GenLimit.KleinbergWei.OrderedLanguage.increasing_lowerDensity_eq_liminf`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C25.

### C26

Worst-case deterministic upper bound and full enumeration catch-up: not covered.

The source makes catch-up explicit in v2; Lean achievability does not formalize that argument.

Evidence: T17; native `GenLimit.KleinbergWei.OrderedLanguage.upperDensity_le_one`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C26.

### C27

Recursive base and earlier-critical inclusion condition: represented. Difference from v1 all-consistent predicate: explicit in distinct definition bodies.

The predicate itself does not assume languages infinite or stream legal; those conditions enter later machine/result statements.

Evidence: T27; native `GenLimit.RecursiveCritical.match_1`, `GenLimit.Consistent`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C27.

### C28

Descending inclusion: represented. Removal of an old suffix: represented. Every new critical index is above each survivor: represented.

No legal-presentation or infinitude hypothesis is required for these purely semantic structural lemmas.

Evidence: T29, T30, T31. Complete types/definition anchors and strength axes: `stage2-claims.json`, C28.

### C29

Exists finite T, then all t≥T criticality: represented.

Lean allows repeated presentations and does not require other candidates to be infinite for this lemma. The threshold is pointwise and has no uniform effective rate.

Evidence: T32, T27; native `GenLimit.Presents`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C29.

### C30

Fixed-scope clause: represented directly. Expanded scope changes focus only through newly included critical indices: follows from maximal focus definition plus the fixed-scope clause.

The direct theorem additionally states criticality equivalence for every index below scope. It does not assert stability when scope shrinks.

Evidence: T28; native `GenLimit.IsFocus`, `GenLimit.PatientMachine.focus_next_of_consistent`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C30.

### C31

Bare switch event: represented. First-ownership/fresh-value restrictions are added only for lateSwitchLoss.

The definition is total off-model too. This does not identify scope-expansion focus changes with switch losses.

Evidence: T12, T23; native `GenLimit.PatientMachine.lateSwitchLoss`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C31.

### C32

Eventual target membership: represented. Current/prior-adversary and prior-generator novelty: represented. Explicit settled focus regime is supported by criticality/scope/focus subset native types.

The combined theorem additionally gives density ≥1/2 for that same output, not an independently chosen witness.

Evidence: T16, T18; native `GenLimit.PatientMachine.stream_ne_output`, `GenLimit.PatientMachine.output_ne_of_lt`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C32.

### C33

Local membership and comparison: represented. Late target support and injectivity: represented by separate native theorems for the same predecessorPartner.

Source ≥ becomes strict < on fresh adversary-first announcements. This is a valid strengthening because the values are distinct. The three pairing conclusions need the explicit late-domain/validity assumptions; the bare fact does not itself assert target membership.

Evidence: T13, T22, T21, T20, T19; native `GenLimit.PatientMachine.gameTrace`, `GenLimit.PatientScope.ordinaryAttacker`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C33.

### C34

Post-settlement logarithmic bound: represented, including target-relative sparse-target accounting. Concrete tau/charge payload and individual exponential-size/support properties: represented. Source-proof pairwise-disjoint charging assertion: no matching certificate field/native assertion found.

The abstract conclusion does not require pairwise disjoint charges. That is a source-proof-payload distinction, not a missing lemma conclusion or a proof failure. At target count 0 or 1, Nat.log2=0; positive-count cases match the integer version of the real log bound.

Evidence: T14, T24, T25; native `GenLimit.PatientMachine.StableTargetRun.charge_card`, `GenLimit.PatientMachine.settledThreshold`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C34.

### C35

Achievability: represented. Same-witness validity and novelty: represented. Optimality against all deterministic algorithms: not covered.

The Overview density-only facade should be read with the native combined theorem. Repeated streams generalize the positive v2 result but do not supply the missing adversarial upper bound.

Evidence: T02, T16, T17. Complete types/definition anchors and strength axes: `stage2-claims.json`, C35.

### C36

q-element output procedure and disjoint q-partner accounting: not covered. General inverse counting lemma: support only, with its counting premise assumed.

The parameter q in the generic inverse-counting theorem yields 1/q from N≤qD+error; it does not construct the source q-output algorithm or prove q/(q+1).

Evidence: T15; native `GenLimit.lowerDensity_inv_of_eventual_counting_atTop`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C36.

### C37

Eventual target criticality and scope inclusion: represented support. Unboundedly many times of focus-language equality: not represented as a supplied native theorem.

Eventual focus containment in K and validity do not by themselves state infinitely-often equality. The result may be derivable with further mathematics, but no new theorem/proof is inferred here.

Evidence: T32; native `GenLimit.PatientMachine.target_eventually_in_scope`, `GenLimit.focus_subset_target`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C37.

### C38

Exact family, target and increasing 4-multiple stream: represented. Output 2t+1 at every round, failed validity and zero target density: represented. Unique critical language and fixed machine focus: represented by native supporting theorems.

The standalone facade bundle omits explicit focus equality, but the native census supplies it.

Evidence: T04, T05, T06, T07; native `GenLimit.PartialEnumeration.Counterexample.run_focus_eq_zero`, `GenLimit.PartialEnumeration.Counterexample.family`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C38.

### C39

Partial subset model and original-target validity: represented. Semantic discard/reindex preprocessing: represented. Persistent critical subset witness and eventual scope: supplied by native types.

The output is not required to lie in K′. GoodCode filtering selects only infinite nonempty intersections; it is not an effective infinitude oracle.

Evidence: T08; native `GenLimit.PartialEnumeration.exists_eventually_critical_subset_target`, `GenLimit.PartialEnumeration.closureCode`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C39.

### C40

Density premise and α/2 conclusion: represented. Validity and density for exactly output(closure O): represented in combined theorem. Native direct density-value and α-equality versions: equivalent presentations.

α follows O,stream,E,z and is constrained to the actual lower density. The generator itself takes neither α, E nor target z.

Evidence: T03, T10, T11, T08, T09; native `GenLimit.PartialEnumeration.exists_eventually_critical_subset_target`, `GenLimit.PartialEnumeration.closureCode`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C40.

### C41

Full theorem, corresponding variable-block/grouped algorithm and needed stochastic/simultaneous scope: not covered.

All declaration type/value records were searched for stochastic and multi-order ingredients; relevant density and focus candidates were inspected. No matching probability/expectation model or one-generator finite-order construction occurs in this package. Generic single-order density lemmas do not fill this gap.

Evidence: T17; native `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C41.

### C42

Full theorem, corresponding variable-block/grouped algorithm and needed stochastic/simultaneous scope: not covered.

All declaration type/value records were searched for stochastic and multi-order ingredients; relevant density and focus candidates were inspected. No matching probability/expectation model or one-generator finite-order construction occurs in this package. Generic single-order density lemmas do not fill this gap.

Evidence: T17; native `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C42.

### C43

Full theorem, corresponding variable-block/grouped algorithm and needed stochastic/simultaneous scope: not covered.

All declaration type/value records were searched for stochastic and multi-order ingredients; relevant density and focus candidates were inspected. No matching probability/expectation model or one-generator finite-order construction occurs in this package. Generic single-order density lemmas do not fill this gap.

Evidence: T17; native `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C43.

### C44

Full theorem, corresponding variable-block/grouped algorithm and needed stochastic/simultaneous scope: not covered.

All declaration type/value records were searched for stochastic and multi-order ingredients; relevant density and focus candidates were inspected. No matching probability/expectation model or one-generator finite-order construction occurs in this package. Generic single-order density lemmas do not fill this gap.

Evidence: T17; native `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`. Complete types/definition anchors and strength axes: `stage2-claims.json`, C44.
## Reverse mapping: all 32 registered Lean targets

The following dossiers map each checked target back to the source slots. An anchor listed under a v1 slot can be adjacent corrected mathematics rather than a literal counterpart; the per-slot verdict controls that distinction.

### T01 — `GenLimit.Critical`

Anchor `GenLimit.Paper01_LanguageGeneration.Critical:16`; kind `definition`. Source slots: C05, C07, C09, C11, C13, C15, C17, C19.

At time t, candidate n is consistent and contained in every consistent i≤n. This is literal v1 criticality, not the predicate used to choose machine focus.

### T02 — `GenLimit.DenseGeneration.Results.theorem_3_15`

Anchor `GenLimit.Paper39_DenseGeneration.Results.Overview:27`; kind `theorem`. Source slots: C35.

For every O, stream and target index z, range(stream)=O.language(z) implies density of the named machine output in that target is at least 1/2. No optimality upper bound occurs.

### T03 — `GenLimit.DenseGeneration.Results.theorem_B_3`

Anchor `GenLimit.Paper39_DenseGeneration.Results.Overview:36`; kind `theorem`. Source slots: C40.

For infinite E⊆O.language(z) presented by stream and α equal to its target-relative density, α/2 bounds the closure machine’s target density below. The generator is fixed independently of E,z,α.

### T04 — `GenLimit.PartialEnumeration.Counterexample.example_B_1`

Anchor `GenLimit.Paper39_DenseGeneration.Partial.ExampleB1:35`; kind `theorem`. Source slots: C14, C15, C38.

Closed conjunction for the fixed increasing-multiple-of-4 example: presentation, infinite enumerated subset, subset of target, output 2t+1 at every t, no eventual target membership, and zero target-relative density.

### T05 — `GenLimit.PartialEnumeration.Counterexample.output_eq_odd`

Anchor `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:183`; kind `theorem`. Source slots: C14, C15, C38.

The original untransformed machine output on the fixed counterexample is exactly 2t+1 at every zero-based round.

### T06 — `GenLimit.PartialEnumeration.Counterexample.output_not_mem_trueLanguage`

Anchor `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:247`; kind `theorem`. Source slots: C14, C15, C38.

Every fixed-example output is outside the positive-even target.

### T07 — `GenLimit.PartialEnumeration.Counterexample.presents_enumeratedLanguage`

Anchor `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:93`; kind `theorem`. Source slots: C14, C15, C38.

The concrete stream has range equal to the concrete enumerated subset. Its injectivity and arithmetic shape follow from the inspected stream definition, not this proposition alone.

### T08 — `GenLimit.PartialEnumeration.lemma_B_2_generation`

Anchor `GenLimit.Paper39_DenseGeneration.Partial.Validity:47`; kind `theorem`. Source slots: C16, C17, C18, C19, C39, C40.

For infinite E presented by stream and contained in K=O.language(z), there exists a pointwise T after which output(closure O) lies in K and differs from every adversary value through that round and every prior output.

### T09 — `GenLimit.PartialEnumeration.theorem_B_3`

Anchor `GenLimit.Paper39_DenseGeneration.Partial.Main:63`; kind `theorem`. Source slots: C18, C19, C40.

Same α-equality partial-density statement as its Overview facade. It uses the original target as density denominator and the named closure output.

### T10 — `GenLimit.PartialEnumeration.theorem_B_3_lowerDensity`

Anchor `GenLimit.Paper39_DenseGeneration.Partial.Main:42`; kind `theorem`. Source slots: C18, C19, C40.

For infinite presented E⊆K, density(output(closure O),K) is at least (1/2) density(E,K), without introducing a separate α-equality binder.

### T11 — `GenLimit.PartialEnumeration.theorem_B_3_with_generation`

Anchor `GenLimit.Paper39_DenseGeneration.Partial.Main:78`; kind `theorem`. Source slots: C18, C19, C40.

Conjoins eventual full validity with the half-density-of-E bound for exactly the same closure output. The density conjunct lies outside the existential time.

### T12 — `GenLimit.PatientMachine.SwitchRound`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Pairing:40`; kind `definition`. Source slots: C31.

At pre-round state run(t), stream(t) is outside its focus language. No freshness/first-ownership hypothesis is built into this predicate.

### T13 — `GenLimit.PatientMachine.fact_3_13`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Fact313:16`; kind `theorem`. Source slots: C08, C09, C33.

For t>0, a fresh adversary-first stream(t) and no switch, the value lies in the pre-round focus and is strictly larger than output(t−1). No target presentation or validity assumption is required by this local statement.

### T14 — `GenLimit.PatientMachine.lemma_3_14`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Charging:44`; kind `theorem`. Source slots: C10, C11, C34.

For every full presenting stream and target z, each ambient cutoff has at most Nat.log2(target values below cutoff) settled fresh switch-loss values below cutoff.

### T15 — `GenLimit.PatientMachine.output`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Machine:387`; kind `definition`. Source slots: C01, C24, C36.

Reads lastOutput from run(t+1), defaulting to 0 syntactically. The inspected successor transition always writes some least fresh focus element, so no no-output branch is introduced.

### T16 — `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Main:53`; kind `theorem`. Source slots: C06, C07, C12, C13, C32, C35.

For a full presenting stream, one named recursive machine has eventual target membership plus freshness against all current/prior adversary values and prior generator outputs, and target-relative density ≥1/2.

### T17 — `GenLimit.PatientMachine.patientScope_lowerDensity_half`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Main:36`; kind `theorem`. Source slots: C03, C12, C13, C20, C21, C22, C23, C26, C35, C41, C42, C43, C44.

Target-relative lower density of the named recursive machine is ≥1/2 whenever stream presents the selected target. It has no arbitrary-generator upper-bound conclusion.

### T18 — `GenLimit.PatientMachine.patient_validity`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Validity:233`; kind `theorem`. Source slots: C06, C07, C32.

There exists T after which every named machine output lies in K for every presenting stream. This target alone omits novelty; other native types provide novelty for the same machine.

### T19 — `GenLimit.PatientMachine.predecessorPartner_injective_machine`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Pairing:173`; kind `theorem`. Source slots: C08, C33.

With a presented target and supplied validity cutoff, the fixed previous-output partner is injective on late ordinary adversary-owned target values outside early announcements and late switch losses.

### T20 — `GenLimit.PatientMachine.predecessorPartner_lt_machine`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Pairing:163`; kind `theorem`. Source slots: C08, C33.

On that same late ordinary domain, predecessorPartner(x)<x in the value order.

### T21 — `GenLimit.PatientMachine.predecessorPartner_mem_machine`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Pairing:154`; kind `theorem`. Source slots: C08, C33.

On that same domain, predecessorPartner(x) belongs to GeneratorFirst∩K. Target support is a conclusion, using the supplied eventual validity of the same output.

### T22 — `GenLimit.PatientMachine.previous_output_lt_of_not_lateSwitch`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Pairing:108`; kind `theorem`. Source slots: C08, C09, C33.

For a fresh adversary-first value at t>validFrom that is outside lateSwitchLoss, output(t−1)<stream(t). The cutoff need not itself be certified valid by this local statement.

### T23 — `GenLimit.PatientMachine.run`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Machine:380`; kind `definition`. Source slots: C01, C24, C31.

A primitive recursive state sequence from the fixed initial state using processRound with observed prefix updates. No target index is a parameter.

### T24 — `GenLimit.PatientMachine.settledChargingCertificate`

Anchor `GenLimit.Paper39_DenseGeneration.Patient.Charging:33`; kind `definition`. Source slots: C10, C11, C34.

For every full presented target it returns a named certificate with concrete tau/charge functions from a stable target run. The definition body fixes witness z and the settled criticality/scope threshold.

### T25 — `GenLimit.PatientScope.TargetSwitchChargingCertificate.prefixCount_le_log2_targetCount`

Anchor `GenLimit.Paper39_DenseGeneration.Abstract.TargetSwitchCharging:62`; kind `theorem`. Source slots: C10, C11, C34.

For any certificate satisfying its six obligations, switch-loss values below n number at most Nat.log2(target values below n). Pairwise charge disjointness is not a hypothesis.

### T26 — `GenLimit.PatientScope.relativeLowerDensity`

Anchor `GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity:24`; kind `definition`. Source slots: C02, C12, C25.

For any A and infinite K, the liminf fraction of its first n increasing elements of K lying in A. The ambient-ratio equivalence was rechecked in the native census.

### T27 — `GenLimit.RecursiveCritical`

Anchor `GenLimit.Paper39_DenseGeneration.Critical:20`; kind `definition`. Source slots: C01, C04, C24, C27, C29.

Index recursion: consistency at 0; at n+1 consistency plus containment in every recursively critical j≤n. Exact language inclusion is semantic.

### T28 — `GenLimit.fixed_scope_one_step`

Anchor `GenLimit.Paper39_DenseGeneration.Dynamics:143`; kind `theorem`. Source slots: C30.

An old maximal in-scope recursive focus surviving the next observation remains the focus at fixed scope, and all in-scope recursive criticality statuses agree before/after.

### T29 — `GenLimit.lost_recursiveCritical_suffix`

Anchor `GenLimit.Paper39_DenseGeneration.Dynamics:168`; kind `theorem`. Source slots: C28.

At any t≤u, if i≤j were both critical at t and i is lost at u, j is lost too.

### T30 — `GenLimit.new_recursiveCritical_above_survivor`

Anchor `GenLimit.Paper39_DenseGeneration.Dynamics:183`; kind `theorem`. Source slots: C28.

At any t≤u, an index newly critical at u exceeds every old critical index surviving to u.

### T31 — `GenLimit.recursiveCritical_subset_of_le`

Anchor `GenLimit.Paper39_DenseGeneration.Critical:38`; kind `theorem`. Source slots: C28.

For i≤j critical at the same time, C(j)⊆C(i).

### T32 — `GenLimit.target_eventually_recursiveCritical`

Anchor `GenLimit.Paper39_DenseGeneration.Critical:56`; kind `theorem`. Source slots: C29, C37.

Any target whose set is the range of stream is recursively critical from some pointwise finite T onward. No other candidate-infinitude or computability assumption occurs.

## Native census search and recovered coverage

All 1,257 declaration records were searched in name, type and exported definition value for stochastic/probability/expectation ingredients, permutations/multiple orders, upper/impossibility bounds, q-output extension, target/focus recurrence and density conclusions. Candidate native types were then inspected. The complete input modules are listed in the frozen snapshot; this coverage finding is confined to that supplied census.

The search recovered these useful unlinked components:

- `Counterexample.example_B_1`, `lowerDensity_eq_zero`, `generatorFirst_inter_target_eq_empty`, `recursiveCritical_iff_eq_zero` and `run_focus_eq_zero` complete the arithmetic example and recover C15’s concrete witness.
- `fact_3_13` recovers the direct old-focus clause for C08; predecessor partner lemmas complete C33’s late target-owned injection.
- `lemma_3_14` directly instantiates the earlier abstract registered charging interface for the machine.
- `theorem_B_3_with_generation` joins validity and density for the same closure output; `exists_eventually_critical_subset_target` supplies the persistent subset witness behind partial validity.

The remaining unrepresented slots are C03, C20–C23, C26, C36–C37 and C41–C44. Generic upperDensity≤1, a single-order half lower bound, arbitrary OrderedLanguage definitions, and an inverse-counting lemma with a parameter named q do not establish the missing source statements.

## Discrepancies and suspected source issues for Stage 3

### SQ1 — C07, C09, C11, C13, C17, C19

Is literal v1 all-earlier-consistent criticality intended for its patient-scope correctness claims, or should those claims be treated as corrected to the recursive earlier/v2 construction?

Evidence: v1 Definition 3.2 is all-consistent; Lean criticalIndices and IsFocus use RecursiveCritical. A fixed-scope all-consistent focus can change when an earlier noncritical blocker is falsified, even while the old focus survives. Example semantic configuration: L1=N+\{2}, L2=N+\{3}, L3=N+\{2,4}, initially observing only 1; announcing 3 removes L2 and makes L3 newly critical under all-consistent criticality. Recursive criticality already included L3.

Assessment: Material named-witness change, not an automatically diagnosed Lean error.

### SQ2 — C03, C26, C12, C13, C35

Which exact legal catch-up schedule establishes the universal deterministic half upper bound?

Evidence: Earlier/v1 describe taking the least unused target value without stating catch-up; v2 adds sparse catch-up prose. The provided Lean census has no matching arbitrary-generator adversarial theorem.

Assessment: Source-detail question and real coverage gap; positive achievability alone does not establish optimality.

### SQ3 — C10, C11, C34

How should the earlier generation-start boundary and source proof’s pairwise-disjoint charge assertion be stated precisely?

Evidence: Lean uses a fixed settled threshold after permanent target criticality and scope inclusion, and its certificate does not assert charge disjointness. It still has the intended logarithmic conclusion via positive injective tau labels and individual exponential support.

Assessment: Separate lemma-statement coverage from proof-payload identity. No proof defect is concluded.

### SQ4 — C14, C15, C38

Should earlier/v1 counterexamples explicitly specify increasing enumeration of multiples of 4, as v2 does?

Evidence: The native stream is 4(t+1). The earlier/v1 only-odd-output assertion with an unspecified permutation of multiples of 4 is stronger than this concrete witness.

Assessment: Faithful concrete specialization/clarification rather than an all-orders result.

### SQ5 — C16, C17, C18, C19, C39, C40

Should binary intersection codes and retained closure indices be distinguished explicitly after finite intersections are discarded?

Evidence: Lean closureCode is Nat.nth of nonzero codes with infinite coded intersection, and membership is a finite query conjunction only after that semantic code choice.

Assessment: Semantic source preprocessing is represented; effective filtering does not follow.

### SQ6 — C01, C16, C20, C22, C23, C24, C39, C41, C43, C44

What computational guarantee, if any, is intended by full family access or the earlier membership oracle?

Evidence: Source and Lean require exact language-inclusion decisions; Lean additionally uses classical unbounded existence and infinitude filtering. OracleFamily.query alone supplies no such algorithm.

Assessment: Report semantic existence separately from effective oracle computation; do not infer a finite-query implementation.

### SQ7 — C20, C22, C23

Are the literal v1 ambient-value/rank variable blocks invariant under target relabeling in the appendix proof?

Evidence: v1 uses ambient smallest available value or ambient rho_i, then identifies K with N+. V2 uses focus-relative rank and adds detailed conditional-history/Fatou accounting.

Assessment: Source proof/context question only; none of these randomized/multi-order algorithms is formalized in this snapshot.

## Stage 1 corrections and coverage extensions

- No substantive error was found in the decisive Stage 1 type/definition reconstructions rechecked here. Stage 1 correctly distinguished the two criticality predicates, semantic computation, and the absence of pairwise disjointness in the charging certificate.
- Stage 1 deliberately reported 19 unlinked slots as evidence boundaries. Native comparison now recovers the full example bundle and supporting zero-density/focus facts for C14/C15, rather than marking them absent.
- Native fact_3_13 supplies old-focus membership for C08 despite that slot’s narrower registered anchor set. Native partner types supplement C33 with target-supported injective pairing.
- The native combined partial theorem supplies validity and density for exactly the same closure output in C18/C40; density-only facades must not be mistaken for the entire available native conclusion.
- For C07/C09/C11/C13/C17/C19, native recursive results are adjacent mathematics, but their existence does not erase the literal v1 witness change.
- After a dedicated native search, deterministic optimality upper bounds and randomized, multi-order, q-output and infinitely-often-accuracy statements remain uncovered in the supplied package. This is a Stage 2 coverage finding rather than a correction to Stage 1’s cautious no-endpoint wording.

## Coverage checklist and unresolved boundaries

- Exactly one comparison object for each of C01–C44, with all three editions kept separate.
- All 32 registered declarations directly rechecked and reverse mapped; native support inspected before declaring an unlinked slot uncovered.
- Full validity distinguished from membership-only facades; same-witness density/validity properties tracked explicitly.
- Source-wide infinite-language, turn-order, enumeration, deterministic/adaptive and randomized/oblivious assumptions retained. V2 no-repetition versus Lean repeated presentation is an explicit generalization.
- Semantic full-language access, Boolean oracle interface, infinitude filtering and ordinary effective computation kept separate.
- Source proof disjoint-charge prose separated from the actual certificate obligations and from proof certification.
- Source v1 hash/visual limitations remain unresolved; local earlier/v2 source visuals were checked during the frozen inventory.
- No raw Lean comments or theorem proof bodies, owner/developer explanations, PaperMaps, old audits or Stage 3 context were read. No Git/library changes or new proof compilation was performed.

Stop here for coordinator validation and freeze. Source-correction intent, computational interpretation and the listed source-proof questions await Stage 3 authorization; no human-credit status changes follow from this review.
