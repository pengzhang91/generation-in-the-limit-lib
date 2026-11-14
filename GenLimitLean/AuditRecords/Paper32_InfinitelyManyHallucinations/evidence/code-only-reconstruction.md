# P32 Stage 1: code-only reconstruction

This report reconstructs the supplied Lean interface only. All 10 opaque slots and all 18 exact targets are covered below. The paper and other audit stages were withheld; declaration names are locators, not evidence of source meaning. No proof body, raw Lean source comment, registry/PaperMap, prior audit, human record, Git state, or external source was consulted. There was no compilation or proof certification and no mathematical edit.

## Input census and limits

The allowed stage1 directory contains 11 files, all read and hashed in this run. Its recursive declaration export contains 83 rows (50 definitions, 7 inductives, 7 constructors, 19 type-only theorems). The 18 requested targets comprise 3 definitions and 15 theorems. The native census contains 1,807 code-only declaration rows (545 definitions, 27 inductives, 28 constructors, 27 recursors, 1,180 theorems); it was parsed for inventory and aggregate support, not individually reviewed helper by helper. Every supplied target occurs in the recursive export; every slot has an endpoint. There are no unresolved GenLimit.* references among the recursive type/value dependency lists after following the supplied constructor interfaces.

The machine-exported type of each target is reproduced verbatim in its dossier, together with its original exported module/line anchor and stage1 text/JSONL locations. Glossary equations unfold the recursively necessary definition values and constructor fields. Pretty-printer proof suppression is not treated as a proof hole or as proof evidence.

Lean/Mathlib standard meanings listed in external-boundary.txt are trusted, including finite sets, filters, real liminf/limsup, real sSup, and classical proposition decidability; no recursive library audit was performed. No decisive unresolved custom definition was found. The source snapshot hash in snapshot.json is an opaque supplied provenance value, not independently verified against source files. Model/configuration observations and exact hashes are recorded in stage1-run.json.

### Input SHA-256 census

| stage1 input | SHA-256 |
|---|---|
| START_HERE.md | 52dbb6f80b47a22d94f222fd499cc75c3e793e710b44d74dd69922866c1c02d7 |
| PROMPT.md | c63aad9d119a37687071a9dd61f3139f0f318647c5237a6cfd05e4ecd3e38de3 |
| claim-slots.json | 0f74d5a9c1594fd184c79b084c52a00af2e1bcabdd2b62c4351a979ab6b4ac7a |
| 01-target-statements.md | dedbe971f2bd82a61da4a97808da3c18967997d3fbd4870f19fe7a7e82d4ef58 |
| 02-definition-dependencies.md | e5a8241d41dbd09b68bd2d2a135bb7169fb7052b8593383e202f03c1904767e7 |
| declarations.jsonl | 7856f9540e6cde9e7c57d844866a8ca517f4f5ffd39f640f734362ea4f01ac52 |
| native-declaration-census.jsonl | 36206209fd335aadcdc49fd2c9f47e6f1286e11737edc0b6b041f47a1aac7b71 |
| targets.txt | dab6d4f18e05acb2d47ea33258a5a48d753d74109bc2b12ab8229be4caa64c23 |
| snapshot.json | 2aecd06dab4066a58207184705eeafb5b8dd843ed9e336da2c82b6d62e76cb45 |
| external-boundary.txt | a5d2bb8041d0fb64a5442d2ea3466a882e1a36a4187086c46d8e5babaa85c9b5 |
| SHA256SUMS | 7a7b9c011d45dcc59bd4e67cda0114acb1ae3f863fa96e3888d6ec5363f4e7e7 |

## Shared definition glossary

All symbols below abbreviate the supplied definition values, not names inferred from a paper. Let I stand for GenLimit.InfinitelyManyHallucinations and K for an OrderedLanguage. When A and Q are exhaustions, write A_n = A.stage n and Q_n = Q.stage n. All cardinalities are of finite sets, casts and divisions in displayed ratios are real, and every liminf/limsup and eventual statement uses the natural-number atTop filter.

### G01 — carriers, exhaustions, and positive-step bounds

GenLimit.Language = Set Nat; I.Language = GenLimit.Generic.Language Nat = Set Nat. An Exhaustion is a function stage : Nat → Finset Nat together with stage(0) = ∅ and monotonicity under inclusion. Its limit is {x | ∃ n, x ∈ stage(n)}. Its increment ΔE_0 is ∅, and ΔE_(n+1) = E_(n+1) ∖ E_n. Exhausts E L means exactly E.limit = L. BoundedBy f E means ∀ n, |ΔE_(n+1)| ≤ f(n+1), and IsSingleStep means BoundedBy (fun _ => 1). Thus zero-index capacity is unused; stages can stop growing, new increments can be empty, and previously present elements are never counted again as new.

Exact dependency interfaces/values: Definitions:35,39,40,54,68,121,130,134, GenericGeneration:21, Basic:20. The exported Exhaustion.mk type supplies both structural constraints. Exhaustion.increment.match_1 is ordinary case analysis on Nat (zero versus successor), with its defining Nat.casesOn body supplied; no extra mathematical assumption is hidden in that matcher.

### G02 — cumulative precision, increment precision, and ordered recall

GenLimit.Generic.acceptedCount P S = |{x ∈ S | P x}|, rejectedCount P S = |{x ∈ S | ¬P x}|. acceptedFraction P S is zero if |S| = 0, otherwise acceptedCount P S / |S|. Accordingly countIn L S counts membership, invalidCount L S counts nonmembership, and membershipFraction L S is that accepted fraction. These finite filters use Classical.propDecidable; the separate I.instDecidable_genLimit is also Classical.propDecidable. They provide mathematical definitions, not an effective membership-oracle contract.

Write MP(L,Q) = lowerMembershipPrecision L Q = liminf_n membershipFraction L Q_n. Write TP_n(L,Q) = stepTailPrecision L Q n: it is one if ΔQ_n is empty, otherwise countIn L ΔQ_n / |ΔQ_n|. Then lowerTailPrecision L Q = liminf_n TP_n(L,Q). The two empty conventions differ: an empty cumulative sample scores zero; an empty increment scores one.

An OrderedLanguage consists of carrier : Set Nat, enumeration e : Nat → Nat, injectivity of e, and Set.range e = carrier. Hence its carrier is infinite and enumeration positions do not repeat. prefixCount K B n = |{i ∈ Finset.range n | e(i) ∈ B}|. prefixRatio K B 0 = 0; for n > 0 it is prefixCount/n. lowerDensity K B is the liminf of these ratios and upperDensity K B their limsup. lowerRecall K B = lowerDensity K B and upperRecall K B = upperDensity K B. These concern B's membership in the entire ordered target, not a simultaneous guessed stage unless that stage is explicitly supplied. The enumeration order is part of K, with no computability condition.

Exact dependency values: FiniteContamination:23,29,77; Definitions:32,140,155,172,183,187,192,197; Precision:21; OrderedDensity:24–26,33,197,233,237. No probability measure, support, random draw, almost-sure event, confidence level, or distributional full-support condition occurs in these targets: the fractions are deterministic finite counts and the asymptotic statistics are densities/liminfs.

### G03 — synchronous exhaustions and supremum domains

For exhaustions T,Q:
- exhaustionLowerPrecision T Q = liminf_n membershipFraction (T_n as a set) Q_n.
- exhaustionLowerRecall T Q = liminf_n membershipFraction (Q_n as a set) T_n.
- coverageLowerRecall T B = liminf_n membershipFraction B T_n.
- lowerRecallValues T B = {r | ∃ Q, Q.limit = B ∧ r = exhaustionLowerRecall T Q}.
- bestExhaustionLowerRecall T B = sSup (lowerRecallValues T B).
- boundedLowerPrecisionValues f L Q = {r | ∃ T, T.limit = L ∧ BoundedBy f T ∧ r = exhaustionLowerPrecision T Q}.
- bestBoundedLowerPrecision f L Q = sSup (boundedLowerPrecisionValues f L Q).

The existential T or Q is inside the value-set definition and may depend on its fixed arguments. Real sSup is the standard Lean/Mathlib real supremum operation, not a selected maximum or program. These definitions do not assert nonemptiness or attainment. Exact values: SupremumCharacterizations:37,45,52,185,192,249,256.

### G04 — eventual validity and exact attainment

EventuallyValid L Q = ∃ N, ∀ n, N ≤ n → (ΔQ_n as a set) ⊆ L.
TailPrecisionOneFromFiniteTime L Q = ∃ N, ∀ n, N ≤ n → TP_n(L,Q) = 1.
LowerTailPrecisionAttained L Q = ∃ N, TP_N(L,Q) = lowerTailPrecision L Q ∧ ∀ n, N ≤ n → lowerTailPrecision L Q ≤ TP_n(L,Q).

The same N serves both clauses in the attainment predicate. The first two predicates have existential cutoffs and universal tails; they are not definitions of a liminf equality. Exact values: Definitions:206,211; TailPrecision:333.

### G05 — generator access, recurrence, raw outputs, and the named copy rule

BatchGenerator = (t : Nat) → (Fin(t+1) → Finset Nat) → Finset Nat → Finset Nat. A generator is an arbitrary total mathematical function. Its arguments are an index t, adversary cumulative stages indexed zero through t, and previous cumulative generated guesses. Its type supplies no membership oracle, code index, running-time restriction, randomness, additional persistent state, or computability evidence. Fixed external parameters may be captured when a generator is chosen.

Let S_0 = ∅ and R_(n+1) = G (n+1) (fun i : Fin(n+2) => A.stage i.val) S_n. The exact recursive definition of generatedStages gives S_(n+1) = S_n ∪ R_(n+1). generatedExhaustion G A packages stage = S with zero-stage and monotonicity evidence. Thus ΔS_(n+1) removes earlier outputs even if R repeats them. The previous recursive value x.1 in the Nat.brecOn export is S_n. The G(0) branch is never called by this recurrence.

GeneratorNovel G A = ∀ n, Disjoint R_(n+1) (A_(n+1) ∪ S_n). By contrast, Novel A Q = ∀ n, Disjoint ΔQ_n A_n. The former constrains raw batches on this generated run, including avoiding all previous guesses; the latter constrains only new increments against current adversary stages.

parrotGenerator t history previousGuess = history ⟨t,t<t+1⟩. It ignores previousGuess. In the generated recurrence it returns A_(n+1); union and adversary monotonicity give S_n = A_n at every n. This observation follows from the supplied update equations, not a review or certification of a theorem proof. It is the named witness only in D16; the existential G of D09 is not identified with it.

Exact values/interfaces: Definitions:224,231,249,258,269; NoNovelty:20. generatedStages_mono and generatedExhaustion._proof_1 are supplied type-only auxiliary declarations; proof bodies are absent and are not assessed.

### G06 — the complete BatchedPodsCertificate premise

BatchedPodsCertificate target L A Q k is Type-valued. Its sole constructor, Certificates:177, takes:
1. overhead : Nat → Real;
2. Tendsto overhead atTop (nhds 0);
3. eventually in n, target.prefixRatio A.limit n ≤ (k+1 : Real) * target.prefixRatio Q.limit n + overhead n;
4. Novel A Q;
5. lowerMembershipPrecision L Q = 1;
6. lowerTailPrecision L Q = 1.

All six components, including the last three conclusions of D10, are premises of constructing this certificate. The eventual threshold may depend on these fixed parameters and overhead; no sign condition or convergence rate for overhead is specified. k is natural. The type is a certificate of an existing trace pair, not a generator definition or a claim that every run admits such a certificate.

### G07 — exploration objects and sparse-error subcertificates

explorationCount E m = |{n ∈ Finset.Icc 1 m | n ∈ E}|. ExplorationSet.mk takes a carrier E ⊆ Nat, infinitude, 1 ∉ E, ∀ n ∈ E, n+1 ∉ E, and Tendsto (fun m => (explorationCount E m : Real)/(m : Real)) atTop (nhds 0). The count uses positions 1 through m inclusively; at m = 0 the interval is empty and real division by zero has Lean's standard value zero. Zero is not prohibited in E by this interface and is never counted.

E.GammaAdmissible γ means ∀ m, (explorationCount E.carrier m : Real) ≤ (1−γ)*(m : Real), an all-prefix inequality in addition to the object's asymptotic zero density. A SparseExplorationCertificate E L Q (a Prop) has exactly two constructor premises: Tendsto (fun n => |Q_n|) atTop atTop, and ∀ n, invalidCount L Q_n ≤ explorationCount E.carrier |Q_n|. Both are required, including divergence of cumulative output size.

Exact values/interfaces: Definitions:315,321,322,333; Certificates:26.

### G08 — the complete StrictNoveltyCertificate premise

StrictNoveltyCertificate E target L A Q is a Prop. Its sole constructor at Certificates:221 requires:
1. SparseExplorationCertificate E L Q (fully expanded in G07);
2. Novel A Q;
3. target.carrier ∖ A.limit ⊆ Q.limit;
4. lowerRecall target A.limit / 3 ≤ lowerRecall target Q.limit.

Consequently novelty and the one-third bound are already assumptions inside this certificate. Complement coverage is a semantic inclusion. There is no trace-construction algorithm, adversary validity premise, or bounded-increment hypothesis in this interface.

### G09 — historical novelty and the complete GammaNoveltyCertificate premise

novelHistory A Q 0 = ∅.
novelHistory A Q (n+1) = novelHistory A Q n ∪ (ΔQ_(n+1) ∖ A_(n+1)).
Write H_n for this historical set. An item is classified when newly generated; subsequent arrival in the adversary does not remove it from H_n.

GammaNovel γ A Q means ∀ n, 0 < |Q_n| → γ ≤ (|H_n| : Real)/(|Q_n| : Real). It is an every-stage proportion conditioned on positive cumulative size, not a liminf, and H_n is not the instantaneous Q_n ∖ A_n.

GammaNoveltyCertificate E γ L A Q is a Prop with sole constructor at Certificates:250 requiring:
1. SparseExplorationCertificate E L Q (both G07 premises);
2. E.GammaAdmissible γ;
3. ∀ n, |Q_n ∖ H_n| ≤ explorationCount E.carrier |Q_n|;
4. Set.univ ⊆ Q.limit.

The last premise means Q.limit = all natural numbers, and is much stronger than recall one for one target. No OrderedLanguage occurs in this certificate's parameters. No γ interval restriction is a separate constructor field. Exact historical/GammaNovel values: Definitions:302,310.

### G10 — concrete finite trace

oneShotInvalidExhaustion has stage(0) = ∅ and stage(n) = {0} for every positive n. Its limit is {0}; its increment at one is {0}, and all other increments are empty. Definition: Diagnostics:18. The supplied _proof_2 and _proof_3 declarations have only their types exported (zero-stage equality and monotonicity); their bodies are not evidence reviewed here.

## Per-target dossiers

The exact types below retain the exported implicit binders, dependent let-bindings, and conjunction nesting. The shorter skeletons use G01–G10 notation; no binder or premise is added by that notation.

### D01 — GenLimit.InfinitelyManyHallucinations.Results.lemma_2_2

Slot: C01. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:49. Exact input: stage1/01-target-statements.md:82; stage1/declarations.jsonl:32.

Exact exported type:

~~~lean
∀ (target : GenLimit.InfinitelyManyHallucinations.Exhaustion) (guess : GenLimit.InfinitelyManyHallucinations.Language),
  @Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.bestExhaustionLowerRecall target guess)
    (GenLimit.InfinitelyManyHallucinations.coverageLowerRecall target guess)
~~~

**Quantifier skeleton.** ∀ target : Exhaustion, ∀ guess : Language, bestExhaustionLowerRecall target guess = coverageLowerRecall target guess.

**Reconstruction.** For each fixed target exhaustion T and guessed set B, the supremum over all exhaustions Q with Q.limit = B of liminf_n membershipFraction(Q_n,T_n) equals liminf_n membershipFraction(B,T_n). In the left expression the numerator counts target-stage elements already in the simultaneous guessed stage; the right counts target-stage elements in the entire guessed set. The outer result is equality of real numbers, with no maximizer or procedure named.

**Available information and algorithm scope.** No learner is quantified. T is a whole mathematical exhaustion and B an arbitrary set. The supremum ranges over semantic exhaustions of that same B, without a bound or effectiveness requirement.

**Edge cases and limits.** No infinitude assumption on T or B. Empty T_n contributes zero under the cumulative fraction convention; an empty or eventually exhausted target is allowed. This is a liminf identity, not an all-time, attained-maximum, or rate statement.

**Definitions.** G01–G03. The exact supporting definition/interface locations are indexed below.

### D02 — GenLimit.InfinitelyManyHallucinations.Results.theorem_2_1

Slot: C01. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:44. Exact input: stage1/01-target-statements.md:188; stage1/declarations.jsonl:39.

Exact exported type:

~~~lean
∀ (f : Nat → Nat) (L : GenLimit.InfinitelyManyHallucinations.Language)
  (guess : GenLimit.InfinitelyManyHallucinations.Exhaustion),
  @Set.Infinite.{0} Nat guess.limit →
    GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f guess →
      @Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.bestBoundedLowerPrecision f L guess)
        (GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision L guess)
~~~

**Quantifier skeleton.** ∀ f : Nat → Nat, ∀ L : Language, ∀ Q : Exhaustion, Infinite(Q.limit) → BoundedBy f Q → bestBoundedLowerPrecision f L Q = lowerMembershipPrecision L Q.

**Reconstruction.** For every f, set L, and fixed infinite-limit guessed exhaustion Q satisfying |ΔQ_(n+1)| ≤ f(n+1) for every n, the supremum over target exhaustions T of L that satisfy the same bound f of liminf_n membershipFraction(T_n,Q_n) equals liminf_n membershipFraction(L,Q_n). Both the target and guessed bounds use positive step indices. This is a supremum equality for the fixed Q, not an existential learner theorem.

**Available information and algorithm scope.** The alternatives T in the supremum may depend on f, L, and the fixed entire Q. Their existence/effectiveness and an attaining witness are not separately asserted by this type. Sets are predicates with classical finite filtering.

**Edge cases and limits.** The guessed limit must be infinite. f need not be monotone or everywhere positive; f(0) is unused. With f identically zero there is no admissible infinite Q, so the implication is vacuous. No ordered target, novelty, tail precision, convergence rate, or oracle program is asserted.

**Definitions.** G01–G03. The exact supporting definition/interface locations are indexed below.

### D03 — GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision

Slot: C01. Kind: definition. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:172. Exact input: stage1/01-target-statements.md:288; stage1/declarations.jsonl:63.

Exact exported type:

~~~lean
GenLimit.InfinitelyManyHallucinations.Language → GenLimit.InfinitelyManyHallucinations.Exhaustion → Real
~~~

**Quantifier skeleton.** lowerMembershipPrecision : Language → Exhaustion → Real; lowerMembershipPrecision L Q := liminf_(n→∞) membershipFraction L Q_n.

**Reconstruction.** The value is the atTop liminf of the fraction of distinct cumulative guessed-stage elements belonging to L. For a nonempty Q_n it is |{x ∈ Q_n : x ∈ L}| / |Q_n|; for an empty stage the fraction is defined to be zero.

**Available information and algorithm scope.** This is a statistic of the whole exhaustion and set, with no learner or computation interface. Membership filtering uses classical proposition decidability.

**Edge cases and limits.** It measures cumulative-stage membership precision, not the newest increment and not a probability law. Empty exhaustion has value zero. Repeated proposals do not multiply counts because stages are finite sets; no convergence beyond a liminf is built into the definition.

**Definitions.** G01–G02. The exact supporting definition/interface locations are indexed below.

### D04 — GenLimit.InfinitelyManyHallucinations.lowerRecall

Slot: C01. Kind: definition. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:183. Exact input: stage1/01-target-statements.md:306; stage1/declarations.jsonl:64.

Exact exported type:

~~~lean
GenLimit.KleinbergWei.OrderedLanguage → GenLimit.InfinitelyManyHallucinations.Language → Real
~~~

**Quantifier skeleton.** lowerRecall : OrderedLanguage → Language → Real; lowerRecall K B := K.lowerDensity B = liminf_(n→∞) K.prefixRatio B n.

**Reconstruction.** Relative to a fixed injective enumeration e of K.carrier, this is the liminf of the fraction of the first n enumerated target positions whose values lie in B. The n = 0 prefix ratio is zero; for n > 0 it is |{i < n : e(i) ∈ B}| / n.

**Available information and algorithm scope.** The target contains its full mathematical enumeration, injectivity, and range-equals-carrier evidence. No representation or effective access to that enumeration or to membership in B is specified.

**Edge cases and limits.** The enumeration cannot repeat values and forces an infinite target carrier. B may be empty or arbitrary and need not be a subset of the carrier. Recall depends on the supplied order, concerns the entire set B, and is a deterministic lower density rather than time-indexed prediction accuracy or a probability.

**Definitions.** G01–G02. The exact supporting definition/interface locations are indexed below.

### D05 — GenLimit.InfinitelyManyHallucinations.Results.proposition_2_4_constant_step

Slot: C02. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:55. Exact input: stage1/01-target-statements.md:131; stage1/declarations.jsonl:35.

Exact exported type:

~~~lean
∀ {L : GenLimit.InfinitelyManyHallucinations.Language} {guess : GenLimit.InfinitelyManyHallucinations.Exhaustion}
  {c : Nat},
  GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy (fun x => c) guess →
    GenLimit.InfinitelyManyHallucinations.LowerTailPrecisionAttained L guess
~~~

**Quantifier skeleton.** ∀ {L : Language} {Q : Exhaustion} {c : Nat}, BoundedBy (fun _ => c) Q → ∃ N, stepTailPrecision L Q N = lowerTailPrecision L Q ∧ ∀ n ≥ N, lowerTailPrecision L Q ≤ stepTailPrecision L Q n.

**Reconstruction.** Every exhaustion with at most c new distinct elements in each positive step has a time N at which its step tail precision equals its lower tail precision, and every subsequent step tail precision is at least that same lower value. The witness N can depend on L, Q, c, and the bound evidence.

**Available information and algorithm scope.** No generator or algorithm to find N is supplied. The conclusion is semantic finite-time attainment plus a permanent lower bound.

**Edge cases and limits.** c may be zero; then all increments are empty and their step precision is one. No infinite limit or nonempty-step assumption is imposed. Attainment does not say the sequence is eventually constant or converges, and no bound on N is provided.

**Definitions.** G01–G02, G04. The exact supporting definition/interface locations are indexed below.

### D06 — GenLimit.InfinitelyManyHallucinations.Results.proposition_2_4_single_step

Slot: C02. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:52. Exact input: stage1/01-target-statements.md:142; stage1/declarations.jsonl:36.

Exact exported type:

~~~lean
∀ {L : GenLimit.InfinitelyManyHallucinations.Language} {guess : GenLimit.InfinitelyManyHallucinations.Exhaustion},
  guess.IsSingleStep →
    And
      (Or
        (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerTailPrecision L guess)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerTailPrecision L guess)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (GenLimit.InfinitelyManyHallucinations.LowerTailPrecisionAttained L guess)
~~~

**Quantifier skeleton.** ∀ {L : Language} {Q : Exhaustion}, IsSingleStep Q → (lowerTailPrecision L Q = 0 ∨ lowerTailPrecision L Q = 1) ∧ LowerTailPrecisionAttained L Q.

**Reconstruction.** If every positive increment has at most one element, then the lower tail precision is either zero or one, and there is N with stepTailPrecision(N) equal to that lower value and all later step values at least it. These are two conjuncts; the attainment conjunct has both equality-at-N and the all-later lower bound.

**Available information and algorithm scope.** No learner or computable decision between the disjuncts, and no method for finding N, is quantified.

**Edge cases and limits.** Single-step means at most one new element, allowing empty increments, finite limits, and an empty exhaustion. Empty increments score one. In the zero branch the result does not force eventual constancy; in the one branch the all-later bound yields step values one. The claim is about liminf of increments, not cumulative membership precision.

**Definitions.** G01–G02, G04. The exact supporting definition/interface locations are indexed below.

### D07 — GenLimit.InfinitelyManyHallucinations.Results.proposition_3_3

Slot: C02. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:58. Exact input: stage1/01-target-statements.md:158; stage1/declarations.jsonl:37.

Exact exported type:

~~~lean
∀ (L : GenLimit.InfinitelyManyHallucinations.Language) (guess : GenLimit.InfinitelyManyHallucinations.Exhaustion),
  Iff (GenLimit.InfinitelyManyHallucinations.EventuallyValid L guess)
    (GenLimit.InfinitelyManyHallucinations.TailPrecisionOneFromFiniteTime L guess)
~~~

**Quantifier skeleton.** ∀ L : Language, ∀ Q : Exhaustion, (∃ N, ∀ n ≥ N, ΔQ_n ⊆ L) ↔ (∃ N, ∀ n ≥ N, stepTailPrecision L Q n = 1).

**Reconstruction.** For every L and exhaustion Q, eventual validity of every newly added element is equivalent to step tail precision being exactly one at every sufficiently late step. The existential cutoffs on the two sides are separate witnesses inside the equivalence.

**Available information and algorithm scope.** No learner, rate, or procedure for obtaining a cutoff is given. This is an equivalence of predicates of the fixed trace.

**Edge cases and limits.** Empty increments are valid subsets and have step precision one; finite or empty traces are included. The right side is eventual exact equality of the step statistic, not merely lowerTailPrecision = 1. Earlier invalid elements may remain in cumulative stages.

**Definitions.** G01–G02, G04. The exact supporting definition/interface locations are indexed below.

### D08 — GenLimit.InfinitelyManyHallucinations.Results.theorem_3_5_fixed_pod_endgame

Slot: C03. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:89. Exact input: stage1/01-target-statements.md:201; stage1/declarations.jsonl:40.

Exact exported type:

~~~lean
∀ (K : GenLimit.KleinbergWei.OrderedLanguage) (output : GenLimit.Language) (α : Real),
  (∀ (s : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s →
        @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            α
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 4) (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast ⋯))
                (@Nat.cast.{0} Real Real.instNatCast s))))
          (K.lowerDensity output)) →
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) α
        (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
      (K.lowerDensity output)
~~~

**Quantifier skeleton.** ∀ K : OrderedLanguage, ∀ output : Language, ∀ α : Real, (∀ s : Nat, 2 ≤ s → α / (2 + 4 / (s : Real)) ≤ K.lowerDensity output) → α / 2 ≤ K.lowerDensity output.

**Reconstruction.** For a single fixed ordered target K, fixed output set, and real α, if its same lower density is at least α/(2 + 4/s) for every natural s ≥ 2, then it is at least α/2. The output is fixed before the universal s; no changing family of output sets is being compared.

**Available information and algorithm scope.** No generator, construction of output, or effective access is provided. All approximating bounds are hypotheses, not conclusions of an algorithm analysis in this type.

**Edge cases and limits.** There is no sign or interval restriction on α and no assertion that any output satisfying the premise exists. The scale parameter s is natural and at least two, not a sample-time-dependent choice. No rate is asserted.

**Definitions.** G01–G02. The exact supporting definition/interface locations are indexed below.

### D09 — GenLimit.InfinitelyManyHallucinations.Results.theorem_4_3

Slot: C04. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:68. Exact input: stage1/01-target-statements.md:225; stage1/declarations.jsonl:41.

Exact exported type:

~~~lean
∀ (target : GenLimit.KleinbergWei.OrderedLanguage) (L : GenLimit.InfinitelyManyHallucinations.Language) (f : Nat → Nat),
  ∃ G,
    ∀ (adversary : GenLimit.InfinitelyManyHallucinations.Exhaustion),
      @Set.Infinite.{0} Nat adversary.limit →
        @HasSubset.Subset.{0} GenLimit.InfinitelyManyHallucinations.Language (@Set.instHasSubset.{0} Nat)
            adversary.limit L →
          GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f adversary →
            have guess := GenLimit.InfinitelyManyHallucinations.generatedExhaustion G adversary;
            And (GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f guess)
              (And
                (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerRecall target guess.limit)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision L guess)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
~~~

**Quantifier skeleton.** ∀ target : OrderedLanguage, ∀ L : Language, ∀ f : Nat → Nat, ∃ G : BatchGenerator, ∀ A : Exhaustion, Infinite(A.limit) → A.limit ⊆ L → BoundedBy f A → let Q := generatedExhaustion G A; BoundedBy f Q ∧ lowerRecall target Q.limit = 1 ∧ lowerMembershipPrecision L Q = 1.

**Reconstruction.** For each ordered target, validity set L, and step bound f, there is one generator G that works for every subsequently chosen exhaustion A with infinite limit, limit contained in L, and positive increments bounded by f. For its specifically generated Q, all three conclusions hold: the same increment bound f, lower target recall exactly one, and cumulative lower membership precision in L exactly one.

**Available information and algorithm scope.** G is selected after target, L, and f and before A, so the existential can depend on all three fixed parameters but must be uniform over admissible A. Its online arguments are exactly those in G05: current index, cumulative adversary history through the current stage, and previous cumulative guess. The existential names no witness and supplies no computability or restricted membership-oracle contract; parameters may be captured in the chosen mathematical function.

**Edge cases and limits.** No target.carrier ⊆ L assumption, novelty conclusion, tail-precision conclusion, exact all-time precision, or rate appears. If L is finite, or if f permits no infinite bounded A (for example f identically zero), the universal implication is vacuous. G(0) is unused by the generated trace; output bounds concern new increments after union, not necessarily raw proposal cardinality.

**Definitions.** G01–G03, G05. The exact supporting definition/interface locations are indexed below.

### D10 — GenLimit.InfinitelyManyHallucinations.Results.lemma_4_5_of_trace_certificate

Slot: C05. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:73. Exact input: stage1/01-target-statements.md:92; stage1/declarations.jsonl:33.

Exact exported type:

~~~lean
∀ {target : GenLimit.KleinbergWei.OrderedLanguage} {L : GenLimit.InfinitelyManyHallucinations.Language}
  {adversary guess : GenLimit.InfinitelyManyHallucinations.Exhaustion} {k : Nat}
  (hcert : GenLimit.InfinitelyManyHallucinations.BatchedPodsCertificate target L adversary guess k) {α : Real},
  @LE.le.{0} Real Real.instLE α (GenLimit.InfinitelyManyHallucinations.lowerRecall target adversary.limit) →
    And
      (@LE.le.{0} Real Real.instLE
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) α
          (@Nat.cast.{0} Real Real.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (GenLimit.InfinitelyManyHallucinations.lowerRecall target guess.limit))
      (And (GenLimit.InfinitelyManyHallucinations.Novel adversary guess)
        (And
          (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision L guess)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerTailPrecision L guess)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
~~~

**Quantifier skeleton.** ∀ {target L A Q k}, (hcert : BatchedPodsCertificate target L A Q k) → ∀ {α : Real}, α ≤ lowerRecall target A.limit → α / (k + 1 : Real) ≤ lowerRecall target Q.limit ∧ Novel A Q ∧ lowerMembershipPrecision L Q = 1 ∧ lowerTailPrecision L Q = 1.

**Reconstruction.** Given the fixed target, L, traces A and Q, natural k, and a certificate as expanded in G06, every real α below the adversary limit recall yields guessed limit recall at least α/(k+1). The result also returns strict trace novelty, lower membership precision one, and lower tail precision one. The certificate already supplies the last three properties; its additional quantitative content is a vanishing-overhead eventual prefix-ratio inequality.

**Available information and algorithm scope.** The certificate is a Type-valued object carrying a real overhead sequence, its convergence, and the other fields. It is supplied for the already fixed traces, before α; there is no existential G, new Q, procedure, or proof that an arbitrary run has such a certificate.

**Edge cases and limits.** No independent infinitude, f-bound, admissibility of A, or sign condition on α is assumed outside the certificate. k is natural, so k+1 is positive. The prefix inequality is eventual, not all-time; overhead has limit zero with no sign or rate condition. Both precision conjuncts and novelty must be retained.

**Definitions.** G01–G02, G06. The exact supporting definition/interface locations are indexed below.

### D11 — GenLimit.InfinitelyManyHallucinations.Results.lemma_4_7

Slot: C06. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:61. Exact input: stage1/01-target-statements.md:116; stage1/declarations.jsonl:34.

Exact exported type:

~~~lean
∀ (target : GenLimit.KleinbergWei.OrderedLanguage) (adversary guess : GenLimit.InfinitelyManyHallucinations.Language),
  @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat)
      (@SDiff.sdiff.{0} GenLimit.Language (@Set.instSDiff.{0} Nat) target.carrier adversary) guess →
    @LE.le.{0} Real Real.instLE
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (GenLimit.InfinitelyManyHallucinations.upperRecall target adversary))
      (GenLimit.InfinitelyManyHallucinations.lowerRecall target guess)
~~~

**Quantifier skeleton.** ∀ target : OrderedLanguage, ∀ A B : Language, target.carrier ∖ A ⊆ B → 1 - upperRecall target A ≤ lowerRecall target B.

**Reconstruction.** If B contains every target-carrier element absent from A, its lower density in the target order is at least one minus the upper density of A in that same order. The upper statistic is limsup and the lower statistic is liminf.

**Available information and algorithm scope.** A and B are whole sets; there is no exhaustion, generator, computable inclusion test, or constructed B. The condition is a semantic set inclusion.

**Edge cases and limits.** No requirement A ⊆ target.carrier, B ⊆ target.carrier, A ⊆ L, or disjointness is imposed; off-target elements do not enter the position count. Empty B is permitted when the inclusion holds. The conclusion is an asymptotic bound, not an exact complement identity or an all-prefix inequality.

**Definitions.** G01–G02. The exact supporting definition/interface locations are indexed below.

### D12 — GenLimit.InfinitelyManyHallucinations.GeneratorNovel

Slot: C07. Kind: definition. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:258. Exact input: stage1/01-target-statements.md:3; stage1/declarations.jsonl:25.

Exact exported type:

~~~lean
GenLimit.InfinitelyManyHallucinations.BatchGenerator → GenLimit.InfinitelyManyHallucinations.Exhaustion → Prop
~~~

**Quantifier skeleton.** GeneratorNovel : BatchGenerator → Exhaustion → Prop; GeneratorNovel G A := ∀ n : Nat, Disjoint (G (n+1) (fun i : Fin(n+2) => A.stage i.val) (generatedStages G A n)) (A.stage (n+1) ∪ generatedStages G A n).

**Reconstruction.** On the particular run determined by G and A, every raw proposal at step n+1 is disjoint from the current adversary cumulative stage and from all previous cumulative generated guesses. It therefore prohibits repetitions of already generated elements in the raw batch, not merely repetitions that disappear when cumulative stages are formed by union.

**Available information and algorithm scope.** G05 supplies the exact history and state interface and recurrence. This predicate is for one G,A pair and quantifies n only; it does not require novelty on every possible adversary or every hypothetical history, and does not construct or certify any G.

**Edge cases and limits.** The n = 0 check concerns the proposal at step one and history stages zero and one; G at index zero is never tested. Empty proposals satisfy disjointness and progress is not required. A previously guessed element proposed again would violate this predicate even if the new increment is empty; the separate Novel predicate only tests increments against the current adversary.

**Definitions.** G01, G05. The exact supporting definition/interface locations are indexed below.

### D13 — GenLimit.InfinitelyManyHallucinations.Results.theorem_4_8_of_trace_certificate

Slot: C07. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:78. Exact input: stage1/01-target-statements.md:246; stage1/declarations.jsonl:42.

Exact exported type:

~~~lean
∀ (E : GenLimit.InfinitelyManyHallucinations.ExplorationSet) (target : GenLimit.KleinbergWei.OrderedLanguage)
  (L : GenLimit.InfinitelyManyHallucinations.Language)
  (adversary guess : GenLimit.InfinitelyManyHallucinations.Exhaustion),
  GenLimit.InfinitelyManyHallucinations.StrictNoveltyCertificate E target L adversary guess →
    And (GenLimit.InfinitelyManyHallucinations.Novel adversary guess)
      (And
        (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision L guess)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@LE.le.{0} Real Real.instLE
          (@Max.max.{0} Real Real.instMax
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (GenLimit.InfinitelyManyHallucinations.upperRecall target adversary.limit))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (GenLimit.InfinitelyManyHallucinations.lowerRecall target adversary.limit)
              (@OfNat.ofNat.{0} Real (nat_lit 3) (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast ⋯))))
          (GenLimit.InfinitelyManyHallucinations.lowerRecall target guess.limit)))
~~~

**Quantifier skeleton.** ∀ E : ExplorationSet, ∀ target : OrderedLanguage, ∀ L : Language, ∀ A Q : Exhaustion, StrictNoveltyCertificate E target L A Q → Novel A Q ∧ lowerMembershipPrecision L Q = 1 ∧ max (1 - upperRecall target A.limit) (lowerRecall target A.limit / 3) ≤ lowerRecall target Q.limit.

**Reconstruction.** A supplied strict certificate for E, target, L, A, and Q implies strict trace novelty, cumulative lower membership precision one, and the lower recall bound given by the maximum of one minus adversary upper recall and one third of adversary lower recall. G08 expands every certificate premise: sparse-exploration precision accounting, already-supplied novelty, target-complement coverage, and already-supplied one-third recall bound.

**Available information and algorithm scope.** E and both traces are universal parameters; a certificate is an additional hypothesis. This type gives no learner, algorithm producing traces, certificate constructor for arbitrary traces, or oracle/computability claim.

**Edge cases and limits.** The sparse subcertificate forces cumulative size to tend to infinity. No f-bound, adversary subset/infinite assumption, lower tail precision conclusion, or generation-rate claim appears. Novelty and the one-third lower bound are certificate premises. Upper recall is a limsup and the final recall a liminf; the max conjunct must not be reduced to either bound alone.

**Definitions.** G01–G02, G07–G08. The exact supporting definition/interface locations are indexed below.

### D14 — GenLimit.InfinitelyManyHallucinations.Results.theorem_4_9_of_trace_certificate

Slot: C07. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:83. Exact input: stage1/01-target-statements.md:271; stage1/declarations.jsonl:43.

Exact exported type:

~~~lean
∀ (E : GenLimit.InfinitelyManyHallucinations.ExplorationSet) (γ : Real) (target : GenLimit.KleinbergWei.OrderedLanguage)
  (L : GenLimit.InfinitelyManyHallucinations.Language)
  (adversary guess : GenLimit.InfinitelyManyHallucinations.Exhaustion),
  GenLimit.InfinitelyManyHallucinations.GammaNoveltyCertificate E γ L adversary guess →
    And (GenLimit.InfinitelyManyHallucinations.GammaNovel γ adversary guess)
      (And
        (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerRecall target guess.limit)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision L guess)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
~~~

**Quantifier skeleton.** ∀ E : ExplorationSet, ∀ γ : Real, ∀ target : OrderedLanguage, ∀ L : Language, ∀ A Q : Exhaustion, GammaNoveltyCertificate E γ L A Q → GammaNovel γ A Q ∧ lowerRecall target Q.limit = 1 ∧ lowerMembershipPrecision L Q = 1.

**Reconstruction.** For every exploration set, real γ, ordered target, validity set, and pair of traces, a supplied gamma certificate implies the at-every-n historical novelty fraction bound GammaNovel, lower target recall exactly one, and lower cumulative membership precision exactly one. The certificate does not mention target: it requires, in particular, Set.univ ⊆ Q.limit, so the same certificate supports recall one for every ordered target.

**Available information and algorithm scope.** This is conditional on a certificate for existing traces. G09 spells out the sparse-growth and invalid-count bounds, E.GammaAdmissible γ, the every-stage count bound for nonhistorically-novel output, and universal-set coverage. No G, computable procedure, or existence of such a certificate is asserted.

**Edge cases and limits.** There is no explicit γ < 1 or γ ≥ 0 hypothesis; whatever restrictions are necessary are inherited from the certificate. GammaNovel only tests stages with positive cumulative size, and uses historical novelty, not Q_n ∖ A_n. No strict Novel or lower-tail-precision conclusion, step-size bound, or rate is included.

**Definitions.** G01–G02, G07, G09. The exact supporting definition/interface locations are indexed below.

### D15 — GenLimit.InfinitelyManyHallucinations.Results.gamma_admissible_exploration_exists

Slot: C08. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:98. Exact input: stage1/01-target-statements.md:72; stage1/declarations.jsonl:31.

Exact exported type:

~~~lean
∀ {γ : Real},
  @LT.lt.{0} Real Real.instLT γ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    ∃ E, E.GammaAdmissible γ
~~~

**Quantifier skeleton.** ∀ {γ : Real}, γ < 1 → ∃ E : ExplorationSet, ∀ m : Nat, (explorationCount E.carrier m : Real) ≤ (1 - γ) * (m : Real).

**Reconstruction.** For every real γ strictly below one, some exploration-set object E has its count in positions 1 through m bounded by (1−γ)m for every natural m. Because E is an ExplorationSet, its carrier is infinite, excludes one, has no consecutive members, and its same prefix-count ratio tends to zero.

**Available information and algorithm scope.** The existential E may depend on γ. Its identity is unspecified by the type; there is no explicit construction, representation of γ, decidable membership, or uniform computable map γ ↦ E. This does not construct a generator or a gamma-certified trace.

**Edge cases and limits.** γ need not be nonnegative. The count bound is all-prefix, including m = 0, where the interval is empty. The constructor does not exclude zero from the carrier, and zero is not counted by explorationCount. No quantitative decay rate is given and no admissibility result at γ = 1 is asserted.

**Definitions.** G07. The exact supporting definition/interface locations are indexed below.

### D16 — GenLimit.InfinitelyManyHallucinations.Results.appendix_valid_generation_without_novelty

Slot: C09. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:94. Exact input: stage1/01-target-statements.md:48; stage1/declarations.jsonl:30.

Exact exported type:

~~~lean
∀ (target : GenLimit.KleinbergWei.OrderedLanguage) (L : GenLimit.InfinitelyManyHallucinations.Language) (f : Nat → Nat)
  (α : Real) (adversary : GenLimit.InfinitelyManyHallucinations.Exhaustion),
  @Set.Infinite.{0} Nat adversary.limit →
    @HasSubset.Subset.{0} GenLimit.InfinitelyManyHallucinations.Language (@Set.instHasSubset.{0} Nat) adversary.limit
        L →
      GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f adversary →
        @LE.le.{0} Real Real.instLE α (GenLimit.InfinitelyManyHallucinations.lowerRecall target adversary.limit) →
          have guess :=
            GenLimit.InfinitelyManyHallucinations.generatedExhaustion
              GenLimit.InfinitelyManyHallucinations.parrotGenerator adversary;
          And (GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f guess)
            (And (@LE.le.{0} Real Real.instLE α (GenLimit.InfinitelyManyHallucinations.lowerRecall target guess.limit))
              (And
                (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision L guess)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                (@Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerTailPrecision L guess)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
~~~

**Quantifier skeleton.** ∀ target : OrderedLanguage, ∀ L : Language, ∀ f : Nat → Nat, ∀ α : Real, ∀ A : Exhaustion, Infinite(A.limit) → A.limit ⊆ L → BoundedBy f A → α ≤ lowerRecall target A.limit → let Q := generatedExhaustion parrotGenerator A; BoundedBy f Q ∧ α ≤ lowerRecall target Q.limit ∧ lowerMembershipPrecision L Q = 1 ∧ lowerTailPrecision L Q = 1.

**Reconstruction.** For the specifically named copying generator and every target, L, f, α, and admissible infinite A with lower recall at least α, its generated Q retains the bound f and the recall lower bound α, and has both lower membership precision and lower tail precision equal to one. G05 shows directly that this generator returns the current adversary cumulative stage and hence its generated cumulative stages equal those of A.

**Available information and algorithm scope.** The witness is exactly parrotGenerator, not an existential choice. At index t it uses the history entry t and ignores previous guessed state; generated execution supplies adversary stages through t. It requires no membership test in L or target at runtime. All four conclusion components concern this fixed named generated trace.

**Edge cases and limits.** There is no novelty conclusion; copied new elements already lie in the current adversary stage. Raw cumulative proposals may be large, while the new increments satisfy f. No sign restriction on α, no target-carrier subset assumption, and no rate appear. Infinitude is an explicit premise and must not be omitted.

**Definitions.** G01–G02, G05. The exact supporting definition/interface locations are indexed below.

### D17 — GenLimit.InfinitelyManyHallucinations.Results.appendix_lemma_D_1_of_limit_infinite

Slot: C10. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:108. Exact input: stage1/01-target-statements.md:35; stage1/declarations.jsonl:29.

Exact exported type:

~~~lean
∀ {L : GenLimit.InfinitelyManyHallucinations.Language} {guess : GenLimit.InfinitelyManyHallucinations.Exhaustion},
  @Set.Infinite.{0} Nat guess.limit →
    @Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerTailPrecision L guess)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @Eq.{1} Real (GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision L guess)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
~~~

**Quantifier skeleton.** ∀ {L : Language} {Q : Exhaustion}, Infinite(Q.limit) → lowerTailPrecision L Q = 1 → lowerMembershipPrecision L Q = 1.

**Reconstruction.** For an arbitrary validity set and a fixed guessed exhaustion whose limit is infinite, lower tail precision one implies cumulative lower membership precision one. Both premises concern the same Q; no named witness or construction occurs.

**Available information and algorithm scope.** No learner, computation, or cutoff-finding procedure is specified. The premise is equality of the liminf of per-increment fractions to one, not eventual exact per-step precision one.

**Edge cases and limits.** The infinite-limit hypothesis is essential to the stated scope; the concrete next dossier has a finite limit and satisfies the tail premise while its cumulative precision is zero. No converse, eventual validity, novelty, step-size bound, or rate is asserted.

**Definitions.** G01–G02. The exact supporting definition/interface locations are indexed below.

### D18 — GenLimit.InfinitelyManyHallucinations.Results.tail_precision_one_finite_guess_counterexample

Slot: C10. Kind: theorem. Source anchor: GenLimit.Paper32_InfinitelyManyHallucinations.Results.Overview:102. Exact input: stage1/01-target-statements.md:168; stage1/declarations.jsonl:38.

Exact exported type:

~~~lean
And
  (@Eq.{1} Real
    (GenLimit.InfinitelyManyHallucinations.lowerTailPrecision
      (@EmptyCollection.emptyCollection.{0} GenLimit.InfinitelyManyHallucinations.Language
        (@Set.instEmptyCollection.{0} Nat))
      GenLimit.InfinitelyManyHallucinations.oneShotInvalidExhaustion)
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (@Eq.{1} Real
    (GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision
      (@EmptyCollection.emptyCollection.{0} GenLimit.InfinitelyManyHallucinations.Language
        (@Set.instEmptyCollection.{0} Nat))
      GenLimit.InfinitelyManyHallucinations.oneShotInvalidExhaustion)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
~~~

**Quantifier skeleton.** lowerTailPrecision ∅ oneShotInvalidExhaustion = 1 ∧ lowerMembershipPrecision ∅ oneShotInvalidExhaustion = 0.

**Reconstruction.** For the fixed exhaustion with stage zero empty and every positive stage {0}, against the empty validity set, lower tail precision is exactly one and cumulative lower membership precision is exactly zero. This is a closed conjunction about the specified object, not an existential over an unspecified counterexample.

**Available information and algorithm scope.** The witness definition is fully supplied: the sole new element zero is added at step one, and every later increment is empty. There is no learner or oracle.

**Edge cases and limits.** Its limit is the finite singleton {0}. The invalid first increment scores zero and every later empty increment scores one, while every positive cumulative stage contains one invalid element. It therefore lies outside the preceding infinite-limit hypothesis. Both equalities are retained.

**Definitions.** G01–G02, G10. The exact supporting definition/interface locations are indexed below.

## Supporting declaration index

The following are the definition values and inductive/constructor interfaces used for the shared glossary. Locations refer to the allowed stage1 export, with original source anchors copied as metadata. The remaining four non-target theorem rows are type-only structural support, not additional target dossiers or certified proofs.

| Exact declaration | Kind | stage1/02-definition-dependencies.md line | Exported source anchor |
|---|---|---:|---|
| GenLimit.Generic.Language | definition | 3 | GenLimit.Core.GenericGeneration:21 |
| GenLimit.Generic.acceptedCount | definition | 16 | GenLimit.Core.FiniteContamination:23 |
| GenLimit.Generic.acceptedFraction | definition | 30 | GenLimit.Core.FiniteContamination:77 |
| GenLimit.Generic.rejectedCount | definition | 50 | GenLimit.Core.FiniteContamination:29 |
| GenLimit.InfinitelyManyHallucinations.BatchGenerator | definition | 63 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:224 |
| GenLimit.InfinitelyManyHallucinations.BatchedPodsCertificate | inductive | 81 | GenLimit.Paper32_InfinitelyManyHallucinations.Certificates:177 |
| GenLimit.InfinitelyManyHallucinations.BatchedPodsCertificate.mk | constructor | 93 | GenLimit.Paper32_InfinitelyManyHallucinations.Certificates:177 |
| GenLimit.InfinitelyManyHallucinations.EventuallyValid | definition | 127 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:206 |
| GenLimit.InfinitelyManyHallucinations.Exhaustion | inductive | 144 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:39 |
| GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy | definition | 154 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:130 |
| GenLimit.InfinitelyManyHallucinations.Exhaustion.Exhausts | definition | 176 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:121 |
| GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep | definition | 189 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:134 |
| GenLimit.InfinitelyManyHallucinations.Exhaustion.increment | definition | 204 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:68 |
| GenLimit.InfinitelyManyHallucinations.Exhaustion.increment.match_1 | definition | 224 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:None |
| GenLimit.InfinitelyManyHallucinations.Exhaustion.limit | definition | 240 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:54 |
| GenLimit.InfinitelyManyHallucinations.Exhaustion.mk | constructor | 255 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:39 |
| GenLimit.InfinitelyManyHallucinations.Exhaustion.stage | definition | 268 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:40 |
| GenLimit.InfinitelyManyHallucinations.ExplorationSet | inductive | 281 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:321 |
| GenLimit.InfinitelyManyHallucinations.ExplorationSet.GammaAdmissible | definition | 291 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:333 |
| GenLimit.InfinitelyManyHallucinations.ExplorationSet.carrier | definition | 311 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:322 |
| GenLimit.InfinitelyManyHallucinations.ExplorationSet.mk | constructor | 324 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:321 |
| GenLimit.InfinitelyManyHallucinations.GammaNovel | definition | 351 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:310 |
| GenLimit.InfinitelyManyHallucinations.GammaNoveltyCertificate | inductive | 372 | GenLimit.Paper32_InfinitelyManyHallucinations.Certificates:250 |
| GenLimit.InfinitelyManyHallucinations.GammaNoveltyCertificate.mk | constructor | 385 | GenLimit.Paper32_InfinitelyManyHallucinations.Certificates:250 |
| GenLimit.InfinitelyManyHallucinations.GeneratorNovel | definition | 01-target-statements.md:3 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:258 |
| GenLimit.InfinitelyManyHallucinations.Language | definition | 405 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:35 |
| GenLimit.InfinitelyManyHallucinations.LowerTailPrecisionAttained | definition | 418 | GenLimit.Paper32_InfinitelyManyHallucinations.TailPrecision:333 |
| GenLimit.InfinitelyManyHallucinations.Novel | definition | 439 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:269 |
| GenLimit.InfinitelyManyHallucinations.SparseExplorationCertificate | inductive | 455 | GenLimit.Paper32_InfinitelyManyHallucinations.Certificates:26 |
| GenLimit.InfinitelyManyHallucinations.SparseExplorationCertificate.mk | constructor | 466 | GenLimit.Paper32_InfinitelyManyHallucinations.Certificates:26 |
| GenLimit.InfinitelyManyHallucinations.StrictNoveltyCertificate | inductive | 481 | GenLimit.Paper32_InfinitelyManyHallucinations.Certificates:221 |
| GenLimit.InfinitelyManyHallucinations.StrictNoveltyCertificate.mk | constructor | 494 | GenLimit.Paper32_InfinitelyManyHallucinations.Certificates:221 |
| GenLimit.InfinitelyManyHallucinations.TailPrecisionOneFromFiniteTime | definition | 515 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:211 |
| GenLimit.InfinitelyManyHallucinations.bestBoundedLowerPrecision | definition | 533 | GenLimit.Paper32_InfinitelyManyHallucinations.SupremumCharacterizations:256 |
| GenLimit.InfinitelyManyHallucinations.bestExhaustionLowerRecall | definition | 547 | GenLimit.Paper32_InfinitelyManyHallucinations.SupremumCharacterizations:192 |
| GenLimit.InfinitelyManyHallucinations.boundedLowerPrecisionValues | definition | 561 | GenLimit.Paper32_InfinitelyManyHallucinations.SupremumCharacterizations:249 |
| GenLimit.InfinitelyManyHallucinations.countIn | definition | 580 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:140 |
| GenLimit.InfinitelyManyHallucinations.coverageLowerRecall | definition | 597 | GenLimit.Paper32_InfinitelyManyHallucinations.SupremumCharacterizations:52 |
| GenLimit.InfinitelyManyHallucinations.exhaustionLowerPrecision | definition | 615 | GenLimit.Paper32_InfinitelyManyHallucinations.SupremumCharacterizations:37 |
| GenLimit.InfinitelyManyHallucinations.exhaustionLowerRecall | definition | 634 | GenLimit.Paper32_InfinitelyManyHallucinations.SupremumCharacterizations:45 |
| GenLimit.InfinitelyManyHallucinations.explorationCount | definition | 653 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:315 |
| GenLimit.InfinitelyManyHallucinations.generatedExhaustion | definition | 671 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:249 |
| GenLimit.InfinitelyManyHallucinations.generatedStages | definition | 700 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:231 |
| GenLimit.InfinitelyManyHallucinations.instDecidable_genLimit | definition | 745 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:32 |
| GenLimit.InfinitelyManyHallucinations.invalidCount | definition | 758 | GenLimit.Paper32_InfinitelyManyHallucinations.Precision:21 |
| GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision | definition | 01-target-statements.md:288 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:172 |
| GenLimit.InfinitelyManyHallucinations.lowerRecall | definition | 01-target-statements.md:306 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:183 |
| GenLimit.InfinitelyManyHallucinations.lowerRecallValues | definition | 775 | GenLimit.Paper32_InfinitelyManyHallucinations.SupremumCharacterizations:185 |
| GenLimit.InfinitelyManyHallucinations.lowerTailPrecision | definition | 792 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:197 |
| GenLimit.InfinitelyManyHallucinations.membershipFraction | definition | 809 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:155 |
| GenLimit.InfinitelyManyHallucinations.novelHistory | definition | 826 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:302 |
| GenLimit.InfinitelyManyHallucinations.oneShotInvalidExhaustion | definition | 854 | GenLimit.Paper32_InfinitelyManyHallucinations.Diagnostics:18 |
| GenLimit.InfinitelyManyHallucinations.parrotGenerator | definition | 914 | GenLimit.Paper32_InfinitelyManyHallucinations.NoNovelty:20 |
| GenLimit.InfinitelyManyHallucinations.stepTailPrecision | definition | 932 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:192 |
| GenLimit.InfinitelyManyHallucinations.upperRecall | definition | 954 | GenLimit.Paper32_InfinitelyManyHallucinations.Definitions:187 |
| GenLimit.KleinbergWei.OrderedLanguage | inductive | 967 | GenLimit.Core.OrderedDensity:24 |
| GenLimit.KleinbergWei.OrderedLanguage.carrier | definition | 977 | GenLimit.Core.OrderedDensity:25 |
| GenLimit.KleinbergWei.OrderedLanguage.enumeration | definition | 990 | GenLimit.Core.OrderedDensity:26 |
| GenLimit.KleinbergWei.OrderedLanguage.lowerDensity | definition | 1003 | GenLimit.Core.OrderedDensity:237 |
| GenLimit.KleinbergWei.OrderedLanguage.mk | constructor | 1020 | GenLimit.Core.OrderedDensity:24 |
| GenLimit.KleinbergWei.OrderedLanguage.prefixCount | definition | 1031 | GenLimit.Core.OrderedDensity:33 |
| GenLimit.KleinbergWei.OrderedLanguage.prefixRatio | definition | 1047 | GenLimit.Core.OrderedDensity:197 |
| GenLimit.KleinbergWei.OrderedLanguage.upperDensity | definition | 1065 | GenLimit.Core.OrderedDensity:233 |
| GenLimit.Language | definition | 1082 | GenLimit.Core.Basic:20 |

## Exhaustive coverage

| Slot | Exact supplied declarations and dossiers | Status |
|---|---|---|
| C01 | D01 — GenLimit.InfinitelyManyHallucinations.Results.lemma_2_2<br>D02 — GenLimit.InfinitelyManyHallucinations.Results.theorem_2_1<br>D03 — GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision<br>D04 — GenLimit.InfinitelyManyHallucinations.lowerRecall | All 4 supplied targets reconstructed; none absent |
| C02 | D05 — GenLimit.InfinitelyManyHallucinations.Results.proposition_2_4_constant_step<br>D06 — GenLimit.InfinitelyManyHallucinations.Results.proposition_2_4_single_step<br>D07 — GenLimit.InfinitelyManyHallucinations.Results.proposition_3_3 | All 3 supplied targets reconstructed; none absent |
| C03 | D08 — GenLimit.InfinitelyManyHallucinations.Results.theorem_3_5_fixed_pod_endgame | All 1 supplied targets reconstructed; none absent |
| C04 | D09 — GenLimit.InfinitelyManyHallucinations.Results.theorem_4_3 | All 1 supplied targets reconstructed; none absent |
| C05 | D10 — GenLimit.InfinitelyManyHallucinations.Results.lemma_4_5_of_trace_certificate | All 1 supplied targets reconstructed; none absent |
| C06 | D11 — GenLimit.InfinitelyManyHallucinations.Results.lemma_4_7 | All 1 supplied targets reconstructed; none absent |
| C07 | D12 — GenLimit.InfinitelyManyHallucinations.GeneratorNovel<br>D13 — GenLimit.InfinitelyManyHallucinations.Results.theorem_4_8_of_trace_certificate<br>D14 — GenLimit.InfinitelyManyHallucinations.Results.theorem_4_9_of_trace_certificate | All 3 supplied targets reconstructed; none absent |
| C08 | D15 — GenLimit.InfinitelyManyHallucinations.Results.gamma_admissible_exploration_exists | All 1 supplied targets reconstructed; none absent |
| C09 | D16 — GenLimit.InfinitelyManyHallucinations.Results.appendix_valid_generation_without_novelty | All 1 supplied targets reconstructed; none absent |
| C10 | D17 — GenLimit.InfinitelyManyHallucinations.Results.appendix_lemma_D_1_of_limit_infinite<br>D18 — GenLimit.InfinitelyManyHallucinations.Results.tail_precision_one_finite_guess_counterexample | All 2 supplied targets reconstructed; none absent |

## Boundary and validation record

Coverage checks matched the 18 unique targets in targets.txt exactly to the slot declarations, the recursive export, and the 18 dossiers. The slot JSON has one object per slot and preserves each slot's exact declarations. All 10 hashes in the supplied SHA256SUMS match the actual corresponding input bytes; that manifest's own SHA-256 is separately recorded above. The recursive custom-dependency check found no absent GenLimit.* constant. Validation concerns artifact structure, hashes, and exhaustive semantic reconstruction only.

The existential G and E targets do not expose named witnesses or an effective representation; the only named generator used in a target is parrotGenerator, whose history access and recurrence are unfolded in G05/D16. Certificate-conditioned targets do not establish that an algorithm constructs their certificates. No source correspondence or correctness verdict is made. No Stage 2 material was accessed; this report stops at Stage 1.
