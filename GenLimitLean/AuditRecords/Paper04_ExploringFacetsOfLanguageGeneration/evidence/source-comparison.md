# P04 Stage 2: independent source comparison

## Identity, scope, and evidence boundary

This is a statement correspondence audit of seven declarations, not a proof audit, build, or human certification. The source is Moses Charikar and Chirag Pabbaraju, *Exploring Facets of Language Generation in the Limit*, arXiv:2411.15364v2. The banner says 24 December 2024; the title date is December 25, 2024. All 31 PDF pages were inventoried before consulting frozen Stage 1 text or inspecting Lean declarations. Printed pages equal one-based PDF pages throughout: every “p. n” reference below means printed n / PDF n.

The supplied official versioned PDF has SHA256 52e1f0d2111d73a2a248e7b8bdc113ee4f331e0c0478a3e5c7826b0417b7ab8b (419020 bytes). Its title, version banner, date, page count and relevant formulas were checked. The identity file records a different historical expected hash, cea686c86617749044c31e89fd212b29a32ad91a88c088326b30f7991b785381. This review pins the actual official-download bytes and does not establish equality to that unavailable historical artifact. No annotated copy or alternate edition was opened. The identity file's account of an earlier comparison with an annotated copy is supplied provenance, not evidence independently reproduced here.

Allowed mathematical inputs were stage2/, frozen results/code-only-reconstruction.md (SHA256 329effb8d0dc0bd0be2e97e2b5dc8a7e527bf1df2d790ee3a4dd64993a59a761), and frozen results/stage1-run.json (41e409d2baca1baed44765a3791d41050771ff9aed25e000fe55b7da2392634d). Both frozen hashes were checked. The coverage index lists 55 project source files, including seven supplements beyond the original 48-file target closure; all 55 hashes match. The supplied interface has 88 declarations and seven target roots. Actual target signatures and decisive definition bodies were rechecked in the source snapshot. Automated extraction stripped comments and theorem proof bodies before displaying declarations. Names locate evidence; neither names, Lean comments, proof scripts, compilation nor developer interpretations establish correspondence.

Only GenLimit.CharikarPabbaraju.Results.theorem_1 through theorem_7 are headline targets. Supporting native statements are inventoried separately to avoid mistaking a missing facade wrapper for missing mathematics. Unqualified P04 identifiers below have namespace GenLimit.CharikarPabbaraju; Results.* adds the final namespace. P04 file anchors are relative to GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/ in the supplied snapshots. Other anchors name their module paths explicitly.

## Independent full-paper inventory

This inventory was fixed source-first in session state before Stage 1 consultation. It covers all numbered claims and substantive surrounding conventions, distinguishing cited prior results from new contributions.

| Source unit and location | Independently inventoried content |
|---|---|
| Abstract and introduction, pp. 1-4 | Countable-family non-uniform generation; membership-only impossibility; validity/breadth tradeoff; exhaustive and feedback characterizations. Introductory claims restate later theorems rather than add targets. |
| Related work, pp. 5-6; Appendix A, p. 31 | Concurrent-work comparisons; statistical i.i.d. rates belong to cited work. Appendix A maps Propositions 5.3 and 6.1-6.3 to that work, without a new independent theorem. |
| Section 2, p. 6 | Finite alphabet; finite-string universe; countable indexed collection; every language infinite. Positive input completely enumerates the target, with repetitions allowed. |
| Definition 1 and Remark 1, p. 6 | Eventual output in K minus observed inputs; cutoff may depend on target and complete text. Following paragraph literally calls the baseline map computable, then discusses oracle resources. |
| Definitions 2-3, p. 7 | Non-uniform threshold depends on target but precedes enumeration; uniform threshold precedes target and enumeration. Both count distinct inputs. |
| Definition 4, p. 7 | Closure dimension: largest size of finite input set whose containing-language intersection is finite; unbounded case allowed. Empty-version-space and zero conventions are incompletely explicit. |
| Definition 5, pp. 7-8, footnotes 1-2 | Each prefix yields a generate-only sequence. Eventually its range has finite error outside target, and input plus earlier distinguished outputs plus current range cover target. Cutoff depends on text. This v2 condition relaxes the previous edition's no-tail-error condition. |
| Theorem 1, p. 3; algorithm, p. 8 | Every countable family admits non-uniform generation. Greedily retain consistent languages only while intersection remains infinite. Footnote 3 sets empty intersection to the universe; footnote 4 permits avoiding prior generated outputs. |
| Definition 6 / equation (1), p. 9; Theorem 6 / equation (2), p. 9 | Maximum finite intersection size among initial subcollections containing target index. Correctness at distinct-input count at least max(i*,m+1), with one-based indices. Membership plus an oracle deciding finiteness of finite intersections implements the construction. |
| Theorem 2, p. 3; Theorem 7, p. 10 | No single deterministic membership-only algorithm works across all two-language collections without collection-specific advice. Pair/target bounds precede all texts; every round must finish finitely many adaptive queries, even below threshold. |
| Section 4 discussion, pp. 12-13 | Finite-family uniform/non-uniform equivalence. Intersection-finiteness advice or a maximum finite intersection bound explains contrast with the cited closure algorithm. Not impossibility for each fixed pair. |
| Theorem 3, pp. 4,13 | Some countable collection of regular infinite languages cannot be exhaustively generated. Source construction uses Z and integer upper rays, with an informal regular-encoding observation. |
| Corollary 5.1, pp. 14-15 | Randomized exhaustive lower bound: the two exhaustive properties cannot hold with probability strictly greater than one half at every sufficiently late stage, for every target/text. |
| Definition 7, equation (3), Theorem 8, p. 15 | Identification eventually outputs correct language indices. Cited Angluin characterization uses a computable procedure enumerating finite telltales, not pointwise existence. Discussion says identification implies exhaustive generation. |
| Example 9, pp. 15-16 | Z and all one-point deletions: not identifiable but exhaustively generatable by a fixed integer sweep. |
| Definition 8 and Remark 2, p. 16 | Exact breadth is eventual equality of current range and target. Distribution support is translated to sequence range. Approximate breadth and unambiguous generation are discussed without new characterizations here. |
| Section 5.3.1, p. 16 | Exact breadth implies exhaustive generation; Theorem 3 rules out breadth plus consistency for all countable collections, answering the quoted open question. |
| MOP discussion and Claim 5.2, pp. 17-18 | Example 9's generator has decidable support but lacks exact breadth; its collection in fact has no exact-breadth generator. The cited MOP theorem concerns a restricted effective generator class. |
| Equation (4), p. 18; Proposition 5.3, pp. 19-20; Remark 3, p. 20 | Strong Angluin telltale existence is necessary for exact breadth. Computation distinguishes enumeration from existence; their effective equivalence is not asserted. |
| Equation (7), p. 20; Theorem 4, p. 4; Propositions 6.1-6.2, pp. 20-23 | Weak existence permits proper sublanguages containing a telltale only when target deficit is finite. It characterizes exhaustive generation; sufficiency explicitly uses a finite-difference oracle. Remark 5 discusses an additional subset oracle and its elimination. |
| Remark 4, pp. 21-22 | Finite symmetric difference is a relaxation. Exhaustive implies relaxed, converse fails; weak existence remains necessary for relaxed generation. |
| Equation (12), p. 23; Proposition 6.3, pp. 23-24 | A single computable enumerator of finite weak telltales suffices for exhaustive generation with membership oracle access only. |
| Example 10, p. 24 | Growing disjoint finite blocks with negative even/odd integers: infinite closure dimension, but uniform generation using one target query. |
| Definition 9 / equation (13), p. 25; Proposition 7.1, pp. 25-26 | No-feedback game and effective intersection (consistent-language intersection minus inputs); GnF obstruction dimension equals closure dimension. |
| Definition 10, p. 27 | Feedback has one query and truthful answer per round, before output; adversary fully enumerates a fixed target. A shared threshold handles every consistent adaptive adversary. |
| Definition 11, p. 28; Theorem 5, p. 5; Lemmas 7.2-7.3, pp. 28-29 | GF is supremum of scales where every generator has a target/adversary play reaching a large sample with empty effective intersection. Finite GF iff uniform feedback generation. |
| Example 11, pp. 29-30 | One- and two-point deletions of Z: neither ordinary nor feedback uniform generation, but non-uniform generation. Direct sweep argument additionally gives order bounds in excluded integers' magnitudes. |

## Shared semantics and full component matrix

Write S_t = {s(0),...,s(t-1)} for Lean samples, E_t for current generate-only range, and B_t for earlier distinguished single outputs. Ordinary Lean stage t has read t inputs, matching source stage t, with only prefix positions reindexed. Feedback and membership-dialogue round t has already read t+1 inputs, so source round r corresponds to Lean t=r-1.

Classifications are componentwise: E = exact/equivalent after explicit notation/index changes; S = faithful specialization; G = faithful generalization; D = materially different; N = not represented; I = indeterminate. An extensional guarantee can be exact while an implementation assertion is unrepresented.

| Component / targets | Source | Actual Lean content and classification |
|---|---|---|
| Universe, 1,4 | Finite strings, countable family | Arbitrary countable types and total Nat families; G semantically. No effective encoding supplied. |
| Universe, 6 | Finite strings, countable family | Arbitrary infinite type without countability; G semantically. |
| Universe, 2,7 | Strings in effective fixed universe | Natural-number words/queries; S. No generic effective transport theorem asserted. |
| Universe, 3 | Some finite-alphabet regular collection | List Bool, two-letter finite alphabet; E for advertised existential properties. |
| Collection, 5 | Section 7 restricts to countable collections | Arbitrary class on countable type; G, class itself need not be countable. |
| Infinitude, all | Every language infinite | UUS premise, pair infinitude, or existential UUS; E. Finite targets excluded. |
| Texts, 1,4 | Complete enumerations, repetitions allowed | Presents means range s = K; E. No distribution or enumeration deadline. |
| Texts, 6 | Complete target enumeration | Only StreamIn, range s subset of K; G in hypothesis, stronger pointwise conclusion. |
| Prefix information, 1,3,4,6 | Source abbreviates inputs by S_t; exhaustive algorithm “maps S_t” | Full ordered prefix and length retained. E on history reading; I on literal set-only reading. No symmetrization assumed. |
| Non-uniform order, 1,6 | Common generator; target bound before text | Exists G, forall i, exists d, forall text; E. Repeated family indices allowed. |
| Uniform order, 5 | Generator/bound before target/adversary | Exists G,d, forall K,A; E. |
| MQ order, 2,7 | Program before pair; pair/target bounds before texts | Not exists A, Computable A and forall pair ... exists d0,d1 ...; E. Distinctness matches size two. |
| Novelty, 1,2,5,6,7 | Output in K minus inputs | Membership and input freshness; E. Generated-output repetition not automatically forbidden. |
| Exact bound, 6 | max(i*,m+1) | max(i+1,(nonuniformComplexity C i)+1); E under i*=i+1. |
| Scale, 6 | Initial finite intersections containing target | Powerset of indices through i, finiteness guard, cardinal maximum; E when maximum candidates exist. Zero default is I at source's unstated empty maximum. |
| Semantic/effective, 1,4,6 | Algorithm; p. 6 says computable map | Arbitrary total generator functions. D if literal effective existence demanded; I if source oracle conventions unresolved. Extensional content remains faithful. |
| Implementation, 1,6 | Membership plus intersection-finiteness oracle, p. 9 | Semantic subset/infinitude tests and choice; N for certified oracle realization or one executable procedure taking family access. |
| MQ access, 2,7 | Either candidate, adaptive finite queries | Finite valid traces, history, current input, Boolean answers, query/output action; E. Hidden target absent from runtime inputs. |
| MQ computation, 2,7 | Deterministic, no pair advice | Computable total local action; arbitrary candidate oracles; E within dialogue model. Ordinary computability of memberships not assumed. |
| MQ program representation, 2,7 | Informal deterministic oracle algorithm | Total finite-data next-action function is a concrete specialization; S. Equivalence with every partial oracle-machine representation is not established here. |
| MQ termination, 2,7 | Finishes every round, including early rounds | Output execution exists at every time; all executions conditionally correct; E. Negation can witness divergence. |
| Exhaustive errors, 3,4 | Finite distinct tail range error | Finite(E_t minus K); E. Not finiteness of erroneous positions. |
| Exhaustive coverage, 3,4 | Target subset of inputs/history/current range | K subset S_t union B_t union E_t; E. B_t uses earlier position-zero outputs, not earlier whole ranges. |
| Exhaustive time, 3,4 | Eventual target/text-specific cutoff | Forall K,text, exists T, forall t>=T; E. No uniform bound or single-output freshness. |
| Regularity, 3 | All witness languages regular | Standard Language.IsRegular on Boolean lists; native DFA; E. No uniform automaton compiler. |
| Weak telltales, 4 | Each L has finite T, constraining proper sublanguages | Same witness order and finite deficit; E. Empty T allowed; no uniform size/deficit bound. |
| Exhaustive implementation, 4 | Prop. 6.2 finite-difference oracle; Remark 5 subset issue | Semantic characterization and oracle-set construction; N for relative computability/interface theorem. |
| Feedback order, 5 | Input, query, answer, output | Same order and current answer available to output; E. Exactly one query each round. |
| Feedback consistency, 5 | Fixed target, complete enumeration, truthful answers | Same along actual play with G; E. No constraint on unreachable counterfactual histories. |
| Residual, 5 | Intersect languages consistent with inputs/answers, remove sample | Same through current round; E. “Effective” names residual set, not computation. |
| GF order, 5 | Forall G, exists K,A,r obstruction | Same order; both d<=t+1 and d<=sample cardinal retained; E. |
| Finite GF, 5 | Obstruction supremum finite | Exists d, not GFDimensionAtLeast C d; E for boundedness. Numerical supremum/optimal constant N. |
| Probability/loss, all | Targets deterministic; Cor. 5.1 separately randomized | No target probability law, loss, expectation or i.i.d. rate; E for seven targets, N for randomized corollary. |

## Seven target dossiers

### 1. GenLimit.CharikarPabbaraju.Results.theorem_1

**Source:** Theorem 1, p. 3; Definitions 1-2, pp. 6-7; construction and oracle discussion pp. 8-9. **Lean:** Results/Overview.lean:22; Definitions.lean:21,27; Core/GenericGeneration.lean:37,50,63,87,367.

The type is: for an infinite countable type and any family C, UUS(range C) implies NonuniformlyGeneratable C. Expanded: one generator precedes forall i, exists d, forall s presenting C i, forall t; d<=|S_t| implies target membership and freshness. Threshold dependence and all-stage success exactly match Definition 2. A difficult enumeration cannot receive a separately chosen bound. Repetition can arbitrarily delay threshold attainment.

The theorem generalizes the semantic universe while retaining an indexed countable family and infinite languages. It does not name the greedy witness; native support and target 6 do. It does not assert computation of thresholds or a common effective procedure accepting a representation of C. Repeated indices can receive different threshold witnesses without changing extensional existence for their common language.

**Correspondence/strength:** faithful semantic generalization of the non-uniform guarantee. Literal effective or oracle-implementation correspondence is indeterminate, with that component unrepresented. Dropping computability weakens a positive conclusion while enlarging the domain broadens scope; these opposing changes do not support a blanket “stronger” verdict. The source's p. 6 wording remains an unresolved issue, not silently replaced by arbitrary-function language.

### 2. GenLimit.CharikarPabbaraju.Results.theorem_2

**Source:** Theorem 2, p. 3, sharpened by Theorem 7, p. 10; discussion pp. 12-13. **Lean:** Results/Overview.lean:31; MembershipQueryLowerBoundStatement.lean:53,116,132,140; Support/AdaptiveMembershipDialogue.lean:38,45,57,68,83.

Its closed type is TheoremSevenStatement. Expansion negates one computable action rule which, for every distinct infinite natural-number pair, has two target-specific distinct-input bounds and terminates correctly on every complete text. Inputs are completed prior rounds, current input and answered-query list. Either candidate can be queried repeatedly and adaptively. No fixed query budget, pair description/advice input, or unknown-target Boolean is available to the rule.

Two clauses are essential: a completed execution output exists at every round; every valid execution output is fresh and belongs to the selected target once its sample bound is reached. This matches the source's every-round finite-query requirement, including below threshold. Failure may be nontermination, not infinitely many incorrect outputs. Bad pair/text can depend on the program. The statement does not exclude a specialized program for a fixed pair.

**Correspondence/strength:** exact computational lower-bound structure on a natural-number presentation, faithfully specializing the string universe. Like the paper's detailed theorem, this is sharper than the overview's all-countable-collections impossibility: size two suffices. Excluding equal pairs matches “two languages.” No negative result about all noncomputable rules, or a named adverse pair, is inferred. The total computable next-action representation is a concrete dialogue model; this review does not establish a machine-model equivalence theorem for arbitrary partial oracle programs.

### 3. GenLimit.CharikarPabbaraju.Results.theorem_3

**Source:** Theorem 3, pp. 4,13; Definition 5, p. 8. **Lean:** Results/Overview.lean:35; Exhaustive.lean:33-79; RegularRayEncoding.lean:35,78,188,197,242,310,319.

One existential Boolean-word class is countable, has infinite languages, has individually regular members, and has no exhaustive prefix operator. Its negated requirement retains eventual finite range error and exact coverage with finite input/history allowance. This is neither just no exact breadth nor a requirement of zero errors.

All advertised existential properties match. A two-symbol alphabet validly instantiates regular languages. Native signedUnaryRayClass contains the whole word universe and languages accepting the empty word, all words beginning false, and words beginning true whose remaining length is below an index. A native DFA supplies regularity. This alternative witness need not be transported from the source proof's specific integer rays to establish the existential statement. Identity with its exact binary/integer construction is not claimed.

**Correspondence/strength:** faithful generalization of impossibility to arbitrary semantic prefix operators, excluding computable ones as a subclass. If the source map from S_t were literally set-only, access to full prefixes makes the negative result stronger too. Neither difference loses an advertised existential property. Corollary 5.1's randomized guarantee is not covered.

### 4. GenLimit.CharikarPabbaraju.Results.theorem_4

**Source:** Theorem 4, p. 4; equation (7), p. 20; Propositions 6.1-6.2, pp. 20-23. **Lean:** Results/Overview.lean:44; Exhaustive.lean:252; ExhaustiveCharacterization.lean:301,684,712.

For an indexed family on a countable universe with infinite languages, semantic exhaustive generation of its range is equivalent to WeakAngluinExistence of the range. On the right: forall L in range F, exists finite T subset L, such that each proper sublanguage competitor containing T has finite L minus L'. Witness T precedes the competitor. Equals, supersets, incomparable languages, and sublanguages missing T impose no condition. Neither T's size nor the finite deficit is uniformly bounded.

The left has a common algorithm and target/text-specific eventual cutoffs, retaining both Definition 5 range conditions. Family repetitions disappear on taking the range. Nonempty indexed range plus infinite languages ensures the universe is infinite without an explicit Infinite instance in this signature.

**Correspondence/strength:** exact semantic characterization with faithful domain generalization. It is not an effective characterization: pointwise finite-witness existence has not become a computable assignment. Native sufficiency gives a semantic set construction, without a machine-realization theorem for finite-difference/subset oracle computation. That access-qualified sufficiency is partially represented. The semantic positive direction is weaker than an effective realization; semantic necessity excludes more generators. A single total strength ordering for the iff would conceal this difference.

### 5. GenLimit.CharikarPabbaraju.Results.theorem_5

**Source:** Theorem 5, p. 5; Definitions 10-11 and Lemmas 7.2-7.3, pp. 27-29. **Lean:** Results/Overview.lean:53; Feedback.lean:31-61,118,131,139,151,394,404,412,431,608,938.

For any UUS class on a countable universe, UniformlyGeneratableWithFeedback C iff HasFiniteGFDimension C. Strategies are semantic functions. A round uses completed history, current input, query, truthful answer, then output. Consistency means actual input enumerates the fixed target and actual replies match membership. It is consistency along the interaction, not across every counterfactual play against another generator.

Both dependency patterns match. Uniform generation has exists G,d before all targets/adversaries. Obstruction has forall G, exists K,A,t; target and adversary may depend on G. Consistent languages account for positive inputs and answers through the current round. The actual target witnesses nonemptiness, so empty residual means no common fresh word, not inconsistent evidence.

**Correspondence/strength:** faithful generalization of the abstract strategy characterization. The class may be uncountable, beyond source's standing collection scope. The finite-scale predicate represents boundedness, not a numerical GF supremum, optimal threshold or computable strategy. Empty classes are allowed and both sides are vacuously satisfiable; nonempty actual classes still have infinite targets. Section 7 explicitly uses abstract strategy maps, making its semantic reading clearer than p. 6's algorithm wording.

### 6. GenLimit.CharikarPabbaraju.Results.theorem_6

**Source:** Theorem 6 / equations (1)-(2), p. 9; algorithm p. 8. **Lean:** Results/Detailed.lean:22; Nonuniform.lean:23,47,72,84,179,200.

This target names greedyGenerator C and the exact bound max(i+1,(nonuniformComplexity C i)+1)<=|S_t|. Source L_1 corresponds to C 0, so the first additive one correctly reindexes, rather than creating an off-by-one discrepancy. The second puts the sample strictly above the maximum finite intersection. The scale uses subsets of indices through i containing i; repeated indices do not create new intersections.

The recurrence begins with no selected indices and scans 0 through t-1. It adds an index if the sample is contained in its language and intersecting it with retained languages stays infinite. Output is chosen from this infinite core minus sample. Extensionally this matches the source tests and arbitrary unseen output. Empty intersection is the whole universe. Lean explicitly defaults the complexity to zero if no finite candidate contributes; source leaves its empty maximum unspecified.

**Correspondence/strength:** faithful semantic generalization. No countability is required; remaining within target replaces complete enumeration. This hypothesis relaxation gives correctness at every qualifying stage even on incomplete streams. It promises no eventual threshold attainment on a repeatedly small sample. Stronger-oracle implementation and effective computation of the threshold remain unrepresented; bodies use semantic tests and choice. Output repetition is allowed here; a native no-repetition strengthening separately covers footnote 4.

### 7. GenLimit.CharikarPabbaraju.Results.theorem_7

**Source:** Theorem 7, p. 10; advice/oracle discussion pp. 12-13. **Lean:** Results/Detailed.lean:36; same expanded definitions as target 2.

This target was separately rechecked: its closed type TheoremSevenStatement is exactly target 2's type. It is not a differently strengthened variant. Expansion excludes a computable adaptive rule shared across every distinct infinite pair, with pair-dependent thresholds preceding texts, every round complete, and qualifying outputs in the selected target minus sample.

**Correspondence/strength:** exact detailed lower-bound content on natural numbers, with target 2's faithful domain specialization. Query counts can be unbounded across rounds but each completed trace is finite. Computability of the local action does not decide arbitrary membership without oracle access. It does not assert failure on every pair, termination required only beyond threshold, or randomized impossibility. The duplicate legitimately covers overview and detailed source statements, not two independent mathematical results.

## Broader native coverage and actual gaps

This census uses all 55 indexed umbrella files; the entries are supporting coverage, not extra headline targets.

| Source claim | Native anchors and assessed coverage |
|---|---|
| Definitions 1-3; p. 6 computation wording | Core/ClassGeneration.lean:17 supplies semantic limit generation; P04 Definitions.lean:21,31 supplies source-style non-uniform/uniform predicates. Supplemental Preliminaries.lean:23-60 defines Computable limit generators and a semantic bridge. This distinguishes the notions, without making targets 1/4/6 effective. |
| Closure characterization cited p. 7 | Core/ClosureDimension.lean:16,20,25,30,34 and Paper02_LearningTheory/Closure.lean:152,237,258 give semantic necessity/sufficiency and finite-closure iff uniform generation. Version-space nonemptiness is explicit. Native imported coverage, not an omitted result. |
| No repetition, p. 8 footnote 4 | NonuniformNoRepetition.lean:174,179,212,248 gives injective output streams, same distinct-input bound and non-uniform existence. Represented semantically; no oracle-realization theorem. |
| Finite-family observation, pp. 12-13 | Finite class has finite closure dimension (Core/ClosureDimension.lean:119), with imported uniform sufficiency. Membership implementation with intersection advice is not certified by the inspected statements. |
| Corollary 5.1, pp. 14-15 | Actual omission from this umbrella: no probability law or randomized exhaustive lower-bound statement. Deterministic semantic impossibility does not substitute for its probability strictly above one half. |
| Cited Theorem 8 / effective Angluin iff, p. 15 | Imported GenLimit.Angluin.ConditionOne.effective_sufficiency (Paper00A_PositiveDataInference/Effective/Sufficiency.lean:422) proves sufficiency for uniformly computable-membership families. Imported semantic iff (Semantic/Characterization.lean:266) uses mere existence. Effective iff is defined as a proposition (Effective/Definitions.lean:73), but its full necessity is not a theorem in this closure. A proposition definition is not proof of the cited iff. |
| Example 9, pp. 15-16 | Exhaustive.lean:121,153,230,259 defines the actual integer all/one-hole class, proves no finite telltale for universe, exhaustive generation and weak existence. Nonidentifiability is supported by imported finite-telltale necessity. No single facade combining the separation is required. |
| Exact breadth / universal impossibility, p. 16 | Breadth.lean:30-42 means exact range equality, directly implying exhaustive conditions; target 3 supplies counterexample. Separate wrapper absent, mathematical implication supported by existing statements/definitions. No measure/support conversion theorem supplied. |
| Claim 5.2, pp. 17-18 | BreadthClaim52.lean:30,35,89 proves no breadth for all/one-hole family on Nat, the same deletion pattern under natural-number presentation. Common/IntegerSweep.lean:13-18 supplies Nat-Int bijection. No displayed breadth transport theorem unites it with the exact integer class of Example 9. Record domain adaptation rather than silently asserting such a library theorem. |
| Proposition 5.3 / equation (4), pp. 18-20 | Breadth.lean:157 gives strong finite telltales for indexed natural-number families with nonempty languages: faithful specialization. breadthGenerator_semanticallyIdentifies at line 117 is semantic identification, not effective identification under MOP. |
| Remark 4, pp. 21-22 | Exhaustive.lean:97,104 gives finite symmetric difference and exhaustive-implies-relaxed. The inspected native statements do not supply converse-failure example or relaxed-generation necessity. Those additional remark assertions are unrepresented as results. |
| Propositions 6.1-6.2, pp. 20-23 | ExhaustiveCharacterization.lean:684,301 gives semantic necessity/sufficiency. Augmentation definitions at lines 167-232 mirror the set construction. Finite-difference/subset-oracle realizability is not established by those signatures. |
| Proposition 6.3 / equation (12), pp. 23-24 | MembershipExhaustive.lean:40,49 requires one Computable₂ emitter of finite weak telltales; line 328 concludes existence of an exhaustive generator with OracleFamily supplied. Lines 99-204 define query-based stage tests and least-member search. Substantial native coverage. However query is a supplied arbitrary function, output theorem is semantic, and no relative-machine computability or finite-query realization predicate is concluded. Effective access claim is partially represented. |
| Example 10, p. 24 | Supplemental FeedbackSeparation.lean:21,158,217,240,289,358-370 models growing partition blocks, negative parity, infinite closure, no uniform generation without feedback, and uniform generation with feedback. Strategy queries -2 and chooses a fresh value of the indicated negative parity. Headline separation present; canonical block sizes d+1 faithfully instantiate the example. |
| Proposition 7.1, pp. 25-26 | NoFeedbackDimension.lean:93,257 gives GnFDimensionAtLeast C d iff ClosureDimensionAtLeast C d for positive d, on nonempty countable universes. Faithful finite-scale specialization; no numerical extended-natural dimensions or zero/empty conventions settled. |
| Lemmas 7.2-7.3, pp. 28-29 | Feedback.lean:938,608 separately gives finite-GF sufficiency and infinite-GF impossibility. Both directions exist in the stated abstract model. |
| Example 11, pp. 29-30 | Supplemental FeedbackExample.lean:34,124,191,202,684,733 defines the actual integer one/two-hole class and proves all three headline properties plus infinite GF. Named direct sweep specification at line 94. No theorem states magnitude-based big-O bounds; that quantitative addendum remains unrepresented. |
| MOP, other breadth notions, related-work rates | Cited context, outside the seven targets. No effective MOP theorem, measure-theoretic support equivalence, alternative-breadth characterization, statistical loss or i.i.d. rate is claimed. Appendix A comparisons are not new mathematical results. |

## Discrepancies, source questions, and Stage 1 corrections

The principal unrepresented dimension is effective realization, not the extensional non-uniform/exhaustive quantifiers. Arbitrary Boolean queries and choice do not themselves state one computable procedure relative to specified oracles. WeakAngluinEnumeration includes uniform effective telltale emission; WeakAngluinExistence does not. Semantic negative results can exclude more generators than computable-only negatives. Each characterization direction needs its own assessment.

Source questions are preserved for later adjudication, not silently corrected or offered as proof verdicts:

1. **Computation:** p. 6 says computable map, while p. 9 and Proposition 6.2 explicitly invoke stronger oracles, and Section 7 uses abstract strategy maps. What effective/relative-computation convention governs each headline?
2. **Observation:** pp. 7-8 write maps from S_t, whereas examples use time and enumeration histories. Is this literal set-only restriction or shorthand? No equivalence to more informative ordered prefixes is assumed.
3. **Range versus time errors:** Definition 5 permits one wrong value to recur forever in generate-only mode, while following prose describes eventually stopping hallucinations. Lean follows the set formula, without adding injectivity.
4. **Boundaries:** Definition 6 leaves empty maximum unspecified; Definition 4 and dimension suprema leave zero/empty cases implicit. Lean's defaults and nonempty version space are stated conventions, not textual equalities established at every boundary.
5. **Source proof discussion only:** Lemma 7.2, p. 28, moves from a strategy ensuring nonempty residuals to saying this generator can generate from them. Choosing core outputs may change future adversary behavior. Do not assume identity of original and selected-output strategies; this is a source exposition question, not a theorem-refutation claim.
6. **Source proof discussion only:** Proposition 6.3's displayed cutoff, pp. 23-24, omits explicit waiting for target index to enter scope and target telltale to appear. Its “precisely” description of all consistent near-supersets is stronger than needed. Preserve these issues without rewriting the theorem.
7. **Timing notation:** Example 11, p. 29, writes x_t=y_t although input precedes current query; case conditions refer to the preceding query, and first-round convention is needed. Native separation is present; exact literal construction identity is unclaimed.
8. **Cross-references:** Corollary 5.1's proof cites Theorem 8 rather than its local predecessor Theorem 3. Appendix A calls membership-query sufficiency Proposition 6.2 rather than 6.3. Neither changes the inventory.

No factual correction to Stage 1's seven expanded signatures was necessary. Quantifier order, all-round query termination, range semantics, index shift, semantic/effective distinction and duplicate types survived direct rechecking. Its evidential scope must be extended: Stage 1 could not establish correspondence or full-paper coverage, and seven targets do not exhaust native support. In particular, missing facade wrappers for Claim 5.2, Propositions 5.3/6.3/7.1 and Examples 10-11 are not library omissions. The present report supplies their supporting mapping.

## Coverage and limitations checklist

- All 31 pages, including preliminaries, footnotes, remarks, examples and Appendix A, were inventoried before Stage 1.
- Seven target types were rechecked independently; targets 2 and 7 were each checked despite identical types.
- Every numbered theorem, proposition, lemma, corollary, example and definition is accounted for; cited Theorem 8 and randomized Corollary 5.1 are separate from target coverage.
- Hypotheses, conclusions, quantifier/witness order, access/computation, rates, boundaries, alphabet representation and domain changes were checked componentwise.
- All 55 indexed native files were hashed and declaration-censused. Relevant supporting signatures and decisive definitions were inspected, without proof inspection claims.
- Poppler was unavailable; Ghostscript rendered official-PDF pages under results/qa/. Full-page visual checks covered pp. 6,8,9,10,13,20,22,23,25,27,28,29, confirming formulas, labels, oracle wording and timing notation. Additional rendered pp. 21,24,26 were retained but unnecessary for formula adjudication.
- No library source changed, no build run, no Git tracking/staging/commit performed, and no prohibited stage/developer/old-audit material opened. Coordinator methodological guidance distinguished existential statement correspondence from identity of a particular witness; it supplied no mathematical evidence or alteration of the independent inventory.
- Standard Lean/Mathlib meanings of Computable, sets, finite sets, countability, infinitude and Language.IsRegular are the disclosed external boundary. External bodies and general oracle-machine representation adequacy were not recursively audited.
- Official-v2 identity is verified at the actual supplied hash, without identity to unavailable historical bytes. Backend revision is not exposed; requested model configuration is recorded without independent runtime introspection.
- Remaining questions concern effective realizability, source conventions and listed omitted addenda. Neither proofs nor authors' intended resolution is certified. Both report files are frozen after mechanical validation.
