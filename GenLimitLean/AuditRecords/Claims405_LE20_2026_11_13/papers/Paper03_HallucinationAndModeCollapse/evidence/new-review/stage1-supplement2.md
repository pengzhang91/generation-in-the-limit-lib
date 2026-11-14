# P03 Stage 1 supplement 2 — paper-withheld reconstruction

This separate supplement reconstructs exactly four native targets under opaque label C16. It uses only the new code-only interface as mathematical evidence. The original Stage 1 and first supplement remain frozen; their six report artifacts were binary-hashed solely to confirm preservation.

## Inputs and scope

`stage1-supplement2-input/targets.txt` and `targets-by-slot.json` agree on four targets. The package contains 17 unique native records: 13 definitions, 2 theorem signatures, 1 structure/inductive declaration and 1 constructor. The four target dossiers and 13-entry shared glossary below account for every record. All six manifest entries match actual SHA-256 values. There are no unresolved GenLimit dependency references within the export. This is a syntactic interface check, not certification of the exporter or proof bodies. Complete input hashes and preservation checks are in `stage1-supplement2-run.json`.

Exact raw target types and definition values remain in the hashed `target-statements.md` and `declarations.jsonl`; recursive types/values remain in `definition-dependencies.md`. The descriptions below preserve their bounds and quantifier order without duplicating the raw export. Module/line anchors are supplied export locators, not source files read in this run.

## Shared operational meaning

For n = length(xs), the defining equations mean:

```text
match(xs,j) = for every natural x<n:
                O.query(j,x) equals [Q(xs,x) OR (x occurs in xs)]
identifier(xs) = least j<=n with match(xs,j)=true, if any;
                 otherwise 0
```

The candidate bound is inclusive through n because `firstTrue` receives n+1. The numeric value window is strictly below n because `boundedAll` receives n. These are distinct roles for the same list length. Q is an arbitrary Bool function of the full list and a natural value; its type does not provide a support interpretation, a generator, correctness or computability. A finite match compares both positive and negative membership bits only inside that numeric window.

`MatchesInitialSegment C S t i` is a separate proposition saying that C i and S agree on every natural x<t. `IsLeastTargetIndex C z` says that no smaller index has exactly the same set as C z. The eventual-exclusion theorem supplies a cutoff common to every i<z; it does not itself mention the named identifier or Q.

## Four target dossiers

### GenLimit.HallucinationModeCollapse.breadthIdentifier

**Kind:** Bool/function-valued definition, not an identification theorem. **Opaque slot:** C16. **Export locator:** `GenLimit.Paper03_HallucinationAndModeCollapse.BreadthIdentification:24`. **Exact input:** `declarations.jsonl` line 5 and the same-name heading in `target-statements.md`.

**Reconstruction.** For a family C, correct membership oracle O, arbitrary Bool-valued function Q of a finite list and a natural value, and input list xs, return the least candidate j at most length xs for which breadthMatches O Q xs j is true; if there is no such candidate, return 0. This is a named total finite-search function, not a theorem that it identifies C.

**Assumptions.** C : Nat -> Set Nat is implicit and arbitrary. O.query j x=true iff x belongs to C j, as required by MembershipOracle. Q : List Nat -> Nat -> Bool is arbitrary. No support interpretation, correctness, computability or convergence premise for Q is present. xs : List Nat is arbitrary; no consistency, presentation or witness condition is assumed.

**Quantifiers, witnesses and bounds.** implicit C, then O, then Q, then xs, produce one Nat. With n=length(xs), choose firstTrue(breadthMatches O Q,xs,n+1) and apply Option.getD 0. Candidate range is j<n+1, equivalently j<=n; each match tests values x<n. There are no existential success witnesses in the declaration type.

**Operation and effectiveness.** Finite ascending candidate search; firstTrue preserves the earliest successful index. breadthMatches compares O.query j x against Q xs x OR listContains xs x for all natural x<n. The full list is passed to Q at every tested value; no persistent learner state appears. The code is given as finite recursion, not as a TruthTableProgram with a separately supplied fixed query batch. Totality as a mathematical definition does not imply ordinary computability of O.query or Q. Conditional ordinary computability is a separate supplied theorem. No semantic identification or stabilization conclusion is included in this definition.

**Edge cases.** For xs=[], n=0, every breadthMatches result is vacuously true, and the only tested candidate is 0, so the output is 0. If no candidate matches, output 0 can itself fail the match test; the output value does not distinguish failure from a genuine successful index 0. The returned value is always at most n, but no full-language equality follows merely from a finite match. A repeated observation can increase n and therefore expand both the numeric value-test window and candidate range, even without adding a distinct observed value.

Relevant native dependency names are enumerated in this target's JSON row. No theorem proof body was reviewed.

### GenLimit.HallucinationModeCollapse.breadthIdentifier_computable

**Kind:** theorem signature, proof not reviewed. **Opaque slot:** C16. **Export locator:** `GenLimit.Paper03_HallucinationAndModeCollapse.BreadthIdentification:41`. **Exact input:** `declarations.jsonl` line 6 and the same-name heading in `target-statements.md`.

**Reconstruction.** For each implicit family C and correct membership oracle O, computability of the two-argument membership query implies that, for every Q whose two-argument function on finite lists and natural values is computable, the particular named function breadthIdentifier O Q is an ordinary computable map List Nat -> Nat.

**Assumptions.** O : MembershipOracle C, including its exact semantic membership specification. Computable2 O.query on Nat,Nat -> Bool. Q : List Nat -> Nat -> Bool, quantified after the membership-query computability premise. Computable2 Q under the standard List Nat, Nat and Bool encodings. No correctness or support specification for Q is assumed.

**Quantifiers, witnesses and bounds.** forall {C} O, Computable2(O.query) -> forall Q, Computable2(Q) -> Computable(breadthIdentifier O Q). This preserves the displayed binder/implication order. Canonical Nat encodings, the list encoding and Bool encoding are those explicitly shown in the exported type.

**Operation and effectiveness.** The conclusion is effectiveness of the same bounded first-match function above, using finite membership, boundedAll and firstTrue. It has no additional success check and no semantic target-language premise. Both query-computability hypotheses are required by the signature. The result does not supply an effective Q, prove that an arbitrary support predicate is computable, or provide a mapping that extracts a single code uniformly from representations of all families. No runtime/rate bound or identification guarantee is stated.

**Edge cases.** No infinitude, family injectivity, least-index, tell-tale, subset-oracle or data-validity premise appears. Q may be computable but have no relation to any generator or target; the theorem still concerns computation of the defined output, not correctness of that output.

Relevant native dependency names are enumerated in this target's JSON row. No theorem proof body was reviewed.

### GenLimit.HallucinationModeCollapse.breadthMatches

**Kind:** Bool/function-valued definition, not an identification theorem. **Opaque slot:** C16. **Export locator:** `GenLimit.Paper03_HallucinationAndModeCollapse.BreadthIdentification:19`. **Exact input:** `declarations.jsonl` line 7 and the same-name heading in `target-statements.md`.

**Reconstruction.** For any candidate j, returns true exactly when, for every natural number x strictly below length xs, membership in C j agrees with the disjunction of Q xs x and occurrence of x in the finite list xs. It compares a bounded initial segment of Boolean characteristic data; it does not compare entire languages.

**Assumptions.** Implicit family C and correct membership oracle O. Q : List Nat -> Nat -> Bool, input xs : List Nat and candidate j : Nat are arbitrary. There is no hypothesis that Q is a support oracle, computes true fresh target membership, or satisfies a probability-law specification.

**Quantifiers, witnesses and bounds.** implicit C, O, Q, xs, j -> Bool. Let n=length xs. Result=true iff forall x : Nat, x<n -> [O.query j x = (Q xs x OR (x occurs in xs))]. This Bool equality compares both true and false membership cases. There is no restriction on j in this definition.

**Operation and effectiveness.** boundedAll over x=0,...,n-1; each step compares a membership-query Bool to Q(xs,x).or(listContains xs x). listContains uses finite Nat equality. The observed-list membership term makes the right side true for any tested value already in xs, irrespective of Q at that value. This definition uses oracle/function values without requiring them to be computable. It returns a Bool but has no separate effectiveness certificate in its type. The supplied breadthIdentifier_computable theorem assumes computability of both O.query and Q for the final learner.

**Edge cases.** At n=0 the bounded conjunction is true for every j and every Q. Natural values x>=n are unconstrained, including observed values outside this numeric window. Consequently a match need not imply that all entries of xs lie in C j. The OR does not require Q xs x to be false on observed values; Q may overlap the observed set. List duplicates do not change the listContains bit, but can increase n; Q may also depend on order and duplicates because it receives the entire list.

Relevant native dependency names are enumerated in this target's JSON row. No theorem proof body was reviewed.

### GenLimit.HallucinationModeCollapse.eventually_leastMatching_of_target

**Kind:** theorem signature, proof not reviewed. **Opaque slot:** C16. **Export locator:** `GenLimit.Paper03_HallucinationAndModeCollapse.OnlineReductions:82`. **Exact input:** `declarations.jsonl` line 8 and the same-name heading in `target-statements.md`.

**Reconstruction.** For any family C and index z with no earlier index denoting the same set C z, there exists one natural cutoff T such that at every t>=T, every earlier i<z fails to agree with C z on all natural values below t. Equivalently, each earlier index has some membership disagreement below every sufficiently large t, with one cutoff simultaneous for all those indices.

**Assumptions.** C : Nat -> Set Nat and z : Nat are implicit. IsLeastTargetIndex C z means forall i<z, C i != C z. It is a condition on equality of denoted sets, not an inclusion-minimality condition. No oracle, Q, learner, stream, observation list, computability or infinitude premise appears.

**Quantifiers, witnesses and bounds.** forall {C} {z}, [forall i<z, C i != C z] -> exists T : Nat, forall t : Nat, T<=t -> forall i : Nat, i<z -> not [forall x : Nat, x<t -> (x in C i iff x in C z)]. T is chosen before t and i, so it is common to all smaller indices and all subsequent cutoffs; T may depend on C,z. The type gives no numeric bound or effective method for T.

**Operation and effectiveness.** A semantic finite-initial-segment separation statement. The parameter t bounds natural-number values, not sampled positions. No algorithm or update procedure is defined by this theorem; its proof body is absent. No computability of family membership, no effective distinguishing value, no effective cutoff and no rate are supplied. In particular, this target has no breadthIdentifier or Q argument and states no equality or stabilization of learner outputs.

**Edge cases.** For z=0 there are no earlier indices; the conclusion is vacuous for that index range and a cutoff of 0 is compatible with it. For t=0, MatchesInitialSegment is true for all i because there are no x<0; when smaller indices exist, the asserted eventual exclusion must occur at later cutoffs. An earlier duplicate language would violate the premise. Duplicate languages at later indices are allowed. Finite or empty target languages are permitted. The conclusion excludes earlier matches; it does not impose a uniform cutoff independent of C,z.

Relevant native dependency names are enumerated in this target's JSON row. No theorem proof body was reviewed.

## Shared definition glossary

The following 13 non-target records supply the entire native recursive interface. Proposition-valued definitions state meanings; they are not additional proved results.

| Native declaration | Meaning or interface |
| --- | --- |
| `GenLimit.Generic.Language` | Alias Set alpha. At alpha=Nat, a language is a set of natural numbers. |
| `GenLimit.Generic.LanguageFamily` | Alias Nat -> Set alpha. Indices need not be injective, and no infinitude or nonemptiness assumption is included. |
| `GenLimit.HallucinationModeCollapse.IsLeastTargetIndex` | Predicate definition: for every i<z, C i is not equal to C z. It says z has no earlier equal-language index, not that C z is minimal under inclusion; later duplicates are allowed. This definition is not itself a proved theorem. |
| `GenLimit.HallucinationModeCollapse.MatchesInitialSegment` | Predicate definition: for every natural x<t, x belongs to C i iff x belongs to S. The cutoff t bounds natural-number values, not a sampled history. At t=0 it is vacuously true. This definition is not a proved equivalence between full languages. |
| `GenLimit.Language` | Alias Set Nat. |
| `GenLimit.LanguageFamily` | Alias Nat -> Language, hence Nat -> Set Nat. |
| `GenLimit.MembershipOracle` | Structure over C with Bool query on index and natural value, plus exact membership correctness; no computability, infinitude or nonemptiness field. |
| `GenLimit.MembershipOracle.mk` | Constructor takes query : Nat -> Nat -> Bool, then a proof that query i u=true iff u is in C i for every i,u. |
| `GenLimit.MembershipOracle.query` | Projection of the Bool membership-query field. C and the oracle correctness certificate give its semantic interpretation. |
| `GenLimit.Support.boundedAll` | Natural recursion: at bound 0 return true; at k+1 return previous.and(p a k). It tests every k strictly below the bound and is vacuously true at 0. |
| `GenLimit.Support.firstTrue` | Natural recursion with initial none. At step k, keep an existing some i; otherwise return some k if p a k=true and none if false. Thus it returns the least successful index strictly below its supplied bound, or none. |
| `GenLimit.Support.firstTrue.match_1` | Generated Option eliminator used by firstTrue: a some i runs the some branch at i; none runs the none branch on Unit.unit. No additional mathematical assumption is hidden here. |
| `GenLimit.Support.listContains` | Decides membership of a Nat in a finite Nat list using the ordinary decidable Nat equality instance; returns true exactly for values occurring in the list. Duplicates do not change this membership bit. |

## Exhaustive coverage

| Exact target | Native kind | Reconstruction status |
| --- | --- | --- |
| `GenLimit.HallucinationModeCollapse.breadthIdentifier` | definition | Complete input-scope type/definition reconstruction; no source/proof certification |
| `GenLimit.HallucinationModeCollapse.breadthIdentifier_computable` | theorem | Complete input-scope type/definition reconstruction; no source/proof certification |
| `GenLimit.HallucinationModeCollapse.breadthMatches` | definition | Complete input-scope type/definition reconstruction; no source/proof certification |
| `GenLimit.HallucinationModeCollapse.eventually_leastMatching_of_target` | theorem | Complete input-scope type/definition reconstruction; no source/proof certification |

## Context and limitations

Requested configuration remains `gpt-6.1-sol` / `xhigh`; the actual model setting, reasoning setting and backend revision are not exposed to the reviewer and are not invented. This is continued retained paper-withheld context, not a new context reset. Earlier exposure consisted of the original zero-target Stage 1 package and authored reports, plus the source-free first supplement with seven targets and 86 native interface records. The original broader census was only hashed and counted; its declarations were not semantically reviewed. No source-informed stages were consulted.

The mathematical evidence for this second supplement was read only from `stage1-supplement2-input/`. Earlier reports were accessed only as bytes for preservation hashes. All six original/first-supplement hashes match their recorded frozen values. Only `stage1-supplement2.md`, `stage1-supplement2.json` and `stage1-supplement2-run.json` were written.

Source papers, Stage 2/3 findings or reports, owner notes, registry, PaperMap, developer comments, older audits and raw Lean proof/source files were not accessed. No external browsing, compilation, Git/library/input changes, source comparison or proof/construction certification occurred. Standard Lean/Mathlib operations and encodings form the external trust boundary. The prompt states common frozen-environment provenance; this run checks supplied bytes and references without independently rebuilding the environment. No source-coverage or library-absence conclusion follows. Work ends after these four reconstructed targets.
