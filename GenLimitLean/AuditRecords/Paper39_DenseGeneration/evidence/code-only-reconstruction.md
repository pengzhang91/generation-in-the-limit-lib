# P39 Stage 1: paper-withheld code reconstruction

This report reconstructs the supplied Lean interfaces. Declaration names and source anchors are locators only; no paper claim is inferred from them. The evidence boundary is the eleven files in `P39/stage1`. The coordinator assignment and runtime instructions supplied the task, not source interpretations. No paper, web, source package, owner material, later stage, registry/PaperMap, prior audit or other directory was consulted as input. No Lean proof body was supplied or inspected, and no compilation was run.

The request specified `gpt-6.1-sol` with `xhigh` reasoning and isolated fresh review. The actual serving backend/revision and effective model configuration are not observable here; no independent backend attestation is claimed. This reviewer performed the Stage 1 work without subagents. All output is a reconstruction, not human certification or proof verification.

## Input census

The slot file has 44 slots: 25 slots with endpoints and 19 without endpoints. There are 32 distinct supplied target declarations and 166 exported recursive declarations (including those targets); the native census has 1,257 declarations. Every supplied target has a dossier below. The full native census was parsed and inventoried; selected decisive helper types were inspected, not all 1,257 helpers individually. Exact source types and definition values in the report's closure appendix preserve the supplied boundaries and pretty-printer proof suppression. All ten listed checksums in SHA256SUMS match actual bytes. SHA256SUMS itself is also hashed below.

| Input | Bytes | Actual SHA-256 |
|---|---:|---|
| `stage1/01-target-statements.md` | 25970 | `c7ed9750f7d87f27d00a6a6038adc5fb85641b23f134efc66709a7b803d29664` |
| `stage1/02-definition-dependencies.md` | 63798 | `870bfbbfdd5d219f5f6ccfc0299c2022d4e2a530d3bb940e6f9f0556cdc0f757` |
| `stage1/PROMPT.md` | 3356 | `c63aad9d119a37687071a9dd61f3139f0f318647c5237a6cfd05e4ecd3e38de3` |
| `stage1/SHA256SUMS` | 854 | `e9ea03f5d588fb2b7aee5ea32f5597861ec8ae5f16e821134b032b658cace7fc` |
| `stage1/START_HERE.md` | 217 | `52dbb6f80b47a22d94f222fd499cc75c3e793e710b44d74dd69922866c1c02d7` |
| `stage1/claim-slots.json` | 8779 | `267e49602d03ab61e0889268bfe12b48f27fba9e47d1ca4a77b057764d0a23cf` |
| `stage1/declarations.jsonl` | 150473 | `90fbd2743c33ea123479a129152cd993a26cabf56a38f8484f4c866657f7e032` |
| `stage1/external-boundary.txt` | 1712 | `3bb59775d1cbc0439e5875186abe2591efa6f51934b5bd0f34efa1d4ebbbe072` |
| `stage1/native-declaration-census.jsonl` | 1496652 | `a1e2a8b4f84a06b9e4825c33a58b6b58a2881d7934ea1fec3af4b71d7a9633a7` |
| `stage1/snapshot.json` | 3489 | `5e1100a9acfad848a68a099075568188b3280aaf40eaed9c8682c74be6dd5e7a` |
| `stage1/targets.txt` | 1524 | `e4cc238efd8e9b4b82b523e805e2fe5d55f315e854ad610a8bfab70ab0221906` |

The snapshot reports source snapshot SHA-256 `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc`; that is supplied provenance metadata, not an independently inspected source tree. Inputs use standard Lean/Mathlib meanings at the external boundary. No decisive project definition was missing.

## Definition glossary and algorithm reconstruction

### Sets, observations, criticality and focus

`Language = Set Nat`; `LanguageFamily = Nat -> Language`. `sample stream t` is the finite set `{stream(s) | s<t}`. `Presents stream L` means `Set.range stream = L`, without injectivity, speed, or repetition restrictions. `Consistent C stream t i` means `sample stream t` is a subset of `C(i)`. `Critical` compares a consistent candidate with every consistent index up to it; `RecursiveCritical` instead recursively compares with earlier recursively critical indices, as detailed in their dossiers. `IsFocus C stream t s f` is the conjunction `f<s`, recursive criticality of `f`, and maximality: every recursively critical `j<s` satisfies `j<=f`. A family is indexed by naturals, so the index set is nonempty; equal languages at distinct indices are allowed.

`OracleFamily` contains a language family, a proof each member is infinite, `query : Nat -> Nat -> Bool`, and the law `query i x=true iff x in language i`. Infinitude is a logical field, not an effective enumeration. No subset or infinitude decision oracle occurs in this structure.

### Complete state transition for run/output

A `State` has fields `(scope,tau,age,focus,used,lastOutput,move)`, with types `(Nat,Nat,Nat,Nat,Finset Nat,Option Nat,MoveKind)`. `MoveKind` has `initial`, `stay`, `expand`, `backtrack`. A `Decision` consists of `(scope,tau,focus,move)`. Initial state is `(1,1,0,0,empty,none,initial)`.

For a family C, `consistentIndices C stream a s` filters `[0,s)` by consistency at a. `criticalIndices` filters the same interval by recursive criticality. `survivingCriticalIndices C stream t s` keeps indices recursively critical at both t and t+1. The greatest/least finite candidate helpers return max/min on nonempty candidate sets and the supplied fallback on empty ones. `highestCritical` and `highestSurvivor` use the greatest candidate; `lowestConsistentInScope` uses the least. `lowestConsistent C stream a fallback` tests existence of any consistent index, returns the least if one exists, and otherwise returns fallback. The existence test is classical and ranges over all naturals.

At round t with old state, `decide` checks whether old.focus is consistent at t+1, thus including stream(t).

1. If it is consistent, `stableDecision` checks whether `2^old.tau <= old.age`. If false, decision keeps scope, tau and focus and tags stay. If true, scope becomes old.scope+1; newFocus is highest recursively critical index at time t+1 below new scope, with old.focus as fallback. Tau stays old.tau if focus is unchanged and becomes old.tau+1 otherwise. Move is expand even when focus is unchanged.
2. If old.focus is inconsistent, `backtrackDecision` first computes indices consistent at t+1 below old.scope. If nonempty, it chooses highest surviving critical index below old.scope if survivors are nonempty, otherwise the least consistent index in scope (fallback old.focus). If this chooses i, decision is `(i+1,old.tau+1,i,backtrack)`.
3. If no in-scope consistent index exists, it computes `i=lowestConsistent C stream (t+1) old.focus`. If any consistent index exists anywhere, decision is again `(i+1,old.tau+1,i,backtrack)`. If none exists anywhere, it keeps focus, sets scope to max(old.scope,1), increments tau, and tags backtrack. This fallback makes the semantic transition total even off-model.

After decision d, `processRound` chooses the least natural x such that `x in C(d.focus)`, `x notin sample stream (t+1)`, and `x notin old.used`. Each language is infinite and both forbidden sets are finite, so the supplied `available_exists` helper type provides existence for `Nat.find`; its minimality and membership helper types were inspected. It sets scope=d.scope, tau=d.tau, focus=d.focus, used=insert x old.used, lastOutput=some x and move=d.move. Age becomes old.age+1 when focus is unchanged, and 1 when it changes, independently of move tag. There is no output suspension while waiting.

`run 0=initialState`; `run (t+1)=processRound O stream t (run t)`. Thus state run t precedes announcement stream(t). `output t=(run (t+1)).lastOutput.getD 0`. The default is in the literal definition; the successor transition actually puts some x in that field. The native helper types explicitly identify output with leastAvailable, show membership in the post-round focus language, and show its availability after excluding the current announcement.

This is a single named semantic state machine, uniform in target index z. Its observations are the stream prefix through the current t. The semantic predicates inspect full languages: recursive criticality contains universal set containment; finite filters use `Classical.propDecidable`; lowestConsistent tests an unbounded existence proposition before Nat.find. The definition does not invoke O.query to implement these predicates. Having a total Lean function, or a law for Boolean membership queries, does not supply ordinary computability, a finite-query implementation, or a time bound. The number `2^tau` is a transition waiting threshold, not a proved computational complexity rate or stabilization bound.

### Turn order, pairing and losses

`AdversaryFirst a g = {x | exists t, a(t)=x and forall s<t, g(s)!=x}`. `GeneratorFirst a g = {x | exists t, g(t)=x and forall s<=t, a(s)!=x}`. The asymmetry encodes that an announcement at round t precedes output at round t. These are sets of natural values, not multisets of rounds, output supports or probability laws.

`firstAnnouncementTime a x` is the least t with a(t)=x if such a t exists, otherwise 0. `predecessorPartner a g x = g(firstAnnouncementTime a x - 1)`, using truncated Nat subtraction. A GameTrace packages target K, adversary a, generator g, presentation of K, freshness against every announcement through the output's round, distinctness from previous outputs, validFrom, and eventual target membership from validFrom. The machine's gameTrace instantiates a=stream, g=output O stream, K=O.language(z), with validFrom, presentation and validity explicitly supplied. Its attacker and defender are the two sets above. Its earlyAttacker is the subset of attacker in sample a (validFrom+1), a finite set including the announcement at validFrom. `ordinaryAttacker` is `(attacker intersect target) minus (earlyAttacker union switchLoss)`.

`SwitchRound O stream t` means the current announcement is outside the pre-round focus language. `lateSwitchLoss O stream v` consists of x in AdversaryFirst for which there exists a time t>v with stream(t)=x, x notin sample stream t, and SwitchRound t. It is a set of distinct announced values with a fresh switch witness, not the set of all switch times. No validity guarantee is built into the bare cutoff v.

### Settlement and every field of the charging certificate

`criticalStart O stream z hP` is the least n such that every t>=n makes z recursively critical. `scopeStart` is the least n such that every t>=n has z<(run t).scope. Both use Nat.find with classical universal-future predicates and supplied existence theorems. `settledThreshold=max(criticalStart,scopeStart)`; `settledSwitchLoss=lateSwitchLoss` at that threshold.

A StableTargetRun O stream K packages witness, threshold, OnModel (`forall t, exists i, Consistent(t,i)`), recursive criticality of witness for every t>=threshold, witness in scope at every such t, O.language(witness) subset K, and every stream(t) in K. The private stable-target run used by settledChargingCertificate chooses witness z, threshold settledThreshold and K=O.language(z).

For S and value x, `IsSwitchTime S x t` requires threshold<t, stream(t)=x, freshness against sample t, and SwitchRound t. `switchTime S x` is the least such t if any, otherwise 0. `landingFocus S x` is focus of run(switchTime+1). `UpwardDeparture O stream i d` requires run(d).focus=i, run(d+1).move=expand, and i<run(d+1).focus. `departureTimes O stream t i` is the finite set of such d<t. `latestDeparture` is its maximum or 0 if empty. `departure S x` applies that maximum search before switchTime x for landingFocus x. `tau S x=(run(departure S x)).tau`. `charge S x` is the finite image of k in `[0,2^(tau S x))` under `k -> output O stream ((departure S x - 1) - k)`. The subtractions are truncated, and no properties for arbitrary x follow merely from this formula.

`TargetSwitchChargingCertificate target switchLoss` stores `tau:Nat->Nat` and `charge:Nat->Finset Nat`, together with exactly these six obligations: switchLoss subset target; tau(ell)>0 on switchLoss; tau is injective on switchLoss; `2^(tau ell)<=card(charge ell)` on switchLoss; every charge element is in target on switchLoss; charge ell is a subset of Finset.range ell on switchLoss. It does not require charges for different losses to be disjoint. `StableTargetRun.chargingCertificate` returns these specific tau and charge functions with obligations supplied as proof fields. `settledChargingCertificate` returns that object for the private settled stable run, rather than merely asserting existence of an unnamed certificate.

`PatientScope.prefixFinset S n={x<n | x in S}` and `prefixCount` is its cardinality. Certificate counting conclusions use this ambient value cutoff n and natural `log2`, including its standard 0 and 1 conventions. They are distinct from target-rank density ratios.

### Density and partial-closure preprocessing

An OrderedLanguage packages carrier, enumeration, injectivity, and range equal to carrier; its type itself does not require increasing order. `OrderedLanguage.increasing K hK` specifically uses Nat.nth of membership in infinite K. `prefixCount K A n` counts i<n with K.enumeration(i) in A; prefixRatio is 0 at n=0 and real count/n otherwise; lowerDensity is Filter.liminf at Nat.atTop. `relativeLowerDensity A K hK` uses this particular increasing enumeration. No stochastic laws or full-support assumptions occur in any target.

`patientLowerDensity O stream z` is relativeLowerDensity of `GeneratorFirst stream (output O stream) intersect O.language(z)` inside O.language(z). This measures distinct target values won before the stream announced them, not output accuracy over time. It does not require convergence, only a liminf.

For the partial variant, `codeSupport q` uses Finset.equivBitIndices, the finite set of positions of 1 bits. `codedIntersection C q={x | forall i in codeSupport q, x in C(i)}`. Code 0 has empty support and a vacuous intersection, but `GoodCode O q` explicitly excludes q=0 and requires the coded intersection infinite. `closureCode O n=Nat.nth (GoodCode O) n`. The inspected native helper `closureCode_good` asserts each selected code is good. `closure O` has n-th language codedIntersection O.language (closureCode O n), its infinity proof, and query `List.all (closureCode O n).bitIndices (fun i -> O.query i x)`, with a query-spec proof. These languages are the selected infinite nonempty finite intersections. The code-selection condition tests infinitude of an intersection, which is not supplied as an effective oracle; its use of Nat.nth is semantic. This distinction remains even though the finite membership conjunction for a fixed selected code is explicit.

`partialPatientLowerDensity O stream z` uses GeneratorFirst of `output (closure O) stream`, intersected with the original target O.language(z), and takes relativeLowerDensity inside that original target. The generator takes neither E nor z. The theorems assume E infinite, presented by stream and included in that target, even when E is not itself a family member. They do not require any lower bound on E's relative density.

### Fixed arithmetic constants

For the Counterexample constants, stream(t)=4*(t+1); enumeratedLanguage is its range. firstLanguage contains odd naturals and positive multiples of 4. family(0)=firstLanguage; family(i+1)={2*j | i+1<=j}. trueLanguage=family(1), the positive evens. oracle's query is the classical membership indicator for that family, with supplied correctness and infinitude proof types. The target declarations give original machine output 2*t+1, exclusion from trueLanguage, and the bundled properties specified in their dossiers. They make no universal impossibility claim for all generators.

## Target dossiers

The code blocks below are exact exported types, including implicit binders, ordering, conjunction nesting and suppressed proof arguments. Definitions also include exact exported values. Natural-language shorthand g, g*, K, RC and partner has the meanings fixed above. Each dossier lists the recursively relevant project definitions; the appendix retains their exact supplied types and values.

### T01: `GenLimit.Critical`

Kind: definition. Exact source anchor: `GenLimit.Paper01_LanguageGeneration.Critical:16`. Input anchor: `declarations.jsonl` record 3, duplicated in `01-target-statements.md`.

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Prop
```

Exact definition value:

```lean
fun C stream t n =>
  And (GenLimit.Consistent C stream t n)
    (∀ (i : Nat),
      @LE.le.{0} Nat instLENat i n →
        GenLimit.Consistent C stream t i →
          @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) (C n) (C i))
```

**Reconstruction.** Critical C stream t n holds exactly when every value announced strictly before time t belongs to C(n), and for every natural i<=n that also contains all those observations, C(n) is a subset of C(i). The comparison is with every consistent earlier-or-equal index, rather than only recursively selected ones.

**Quantifier skeleton and dependencies.** forall C:Nat->Set Nat, stream:Nat->Nat, t,n:Nat; Critical iff Consistent(t,n) and forall i:Nat, i<=n -> Consistent(t,i) -> forall x, x in C(n) -> x in C(i).

**Information available.** Predicate arguments are C, stream, t and n; all membership and full-language subset relations are semantically available. No Boolean query parameter is used.

**Edge cases.** At t=0 every index is consistent. At n=0 the sole subset comparison is reflexive, so Critical reduces to consistency. Empty family members are allowed by LanguageFamily; positive samples may exclude them. No infinite-language hypothesis.

**Algorithm scope.** This is a predicate/set/counting statement, not a construction of an executable learner. All quantified languages are semantic subsets of Nat unless an OracleFamily is explicitly present.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Critical`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.sample`.

### T02: `GenLimit.DenseGeneration.Results.theorem_3_15`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Results.Overview:27`. Input anchor: `declarations.jsonl` record 4, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {z : Nat},
  GenLimit.Presents stream (O.language z) →
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
      (GenLimit.PatientMachine.patientLowerDensity O stream z)
```

**Reconstruction.** For every O and stream presenting K=O.language(z), the liminf of the proportion of the first n increasing elements of K that belong to GeneratorFirst(stream,output O stream) intersect K is at least 1/2.

**Quantifier skeleton and dependencies.** forall O,stream,{z}; Presents(stream,K) -> 1/2 <= patientLowerDensity O stream z. No existential program or threshold appears in this type.

**Information available.** Same fixed named semantic generator as output; z selects the set against which density is evaluated.

**Edge cases.** This type contains no generation/freshness conjunction and no quantitative convergence rate. K is infinite via O. The ratio at n=0 is defined as 0, without affecting this asymptotic liminf.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.GeneratorFirst`, `GenLimit.KleinbergWei.OrderedLanguage.enumeration`, `GenLimit.KleinbergWei.OrderedLanguage.increasing`, `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`, `GenLimit.KleinbergWei.OrderedLanguage.prefixCount`, `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.patientLowerDensity`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T03: `GenLimit.DenseGeneration.Results.theorem_B_3`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Results.Overview:36`. Input anchor: `declarations.jsonl` record 5, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  GenLimit.Presents stream E →
    @Set.Infinite.{0} Nat E →
      @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) E (O.language z) →
        ∀ (α : Real),
          @Eq.{1} Real (GenLimit.PatientScope.relativeLowerDensity E (O.language z) ⋯) α →
            @LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) α
                (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
              (GenLimit.PartialEnumeration.partialPatientLowerDensity O stream z)
```

**Reconstruction.** For every O, stream, infinite E, and index z, assume range(stream)=E and E subset K=O.language(z). For every real alpha equal to relativeLowerDensity E K, alpha/2 is at most the liminf target-relative density of GeneratorFirst(stream,g*) intersect K, along the increasing enumeration of K. The equality fixes alpha to that lower density; it is not an unrestricted free performance parameter.

**Quantifier skeleton and dependencies.** forall (O:OracleFamily), {stream:Nat->Nat}, {E:Language}, {z:Nat}; Presents(stream,E) -> Set.Infinite E -> E subset K -> forall alpha:Real, relativeLowerDensity(E,K)=alpha -> alpha/2 <= partialPatientLowerDensity O stream z.

**Information available.** alpha is a theorem parameter after the presentation, infinitude and subset hypotheses; it is not input to g*. Output is the same semantic function for all compatible E,z.

**Edge cases.** E must be infinite, so empty/finite observed languages are outside these theorems; K is infinite by O. E need not be a family member. Repetitions and any enumeration speed are allowed. The density may be zero, yielding a zero lower bound; no positive-density assumption or rate is present. This type contains no generation conjunct, finite-prefix bound, limit-existence statement, or convergence rate.

**Algorithm scope.** The named generator is g*(t)=GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t. It is fixed for O and stream, without E, z, alpha or a density witness as generator inputs. closureCode enumerates codes selected by infinitude of finite intersections using Nat.nth; this preprocessing is semantic and is not established computable from O.query. Conditional on a selected code, the closure query is the finite conjunction of original membership queries. The machine also retains the classical set-inclusion and existence tests described in the glossary.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.GeneratorFirst`, `GenLimit.KleinbergWei.OrderedLanguage.enumeration`, `GenLimit.KleinbergWei.OrderedLanguage.increasing`, `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`, `GenLimit.KleinbergWei.OrderedLanguage.prefixCount`, `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.OracleFamily.query`, `GenLimit.PartialEnumeration.GoodCode`, `GenLimit.PartialEnumeration.closure`, `GenLimit.PartialEnumeration.closureCode`, `GenLimit.PartialEnumeration.codeSupport`, `GenLimit.PartialEnumeration.codedIntersection`, `GenLimit.PartialEnumeration.partialPatientLowerDensity`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T04: `GenLimit.PartialEnumeration.Counterexample.example_B_1`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Partial.ExampleB1:35`. Input anchor: `declarations.jsonl` record 25, duplicated in `01-target-statements.md`.

```lean
And
  (GenLimit.Presents GenLimit.PartialEnumeration.Counterexample.stream
    GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage)
  (And (@Set.Infinite.{0} Nat GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage)
    (And
      (@HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat)
        GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage
        GenLimit.PartialEnumeration.Counterexample.trueLanguage)
      (And
        (∀ (t : Nat),
          @Eq.{1} Nat
            (GenLimit.PatientMachine.output GenLimit.PartialEnumeration.Counterexample.oracle
              GenLimit.PartialEnumeration.Counterexample.stream t)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (And
          (Not
            (∃ T,
              ∀ (t : Nat),
                @LE.le.{0} Nat instLENat T t →
                  @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
                    GenLimit.PartialEnumeration.Counterexample.trueLanguage
                    (GenLimit.PatientMachine.output GenLimit.PartialEnumeration.Counterexample.oracle
                      GenLimit.PartialEnumeration.Counterexample.stream t)))
          (@Eq.{1} Real
            (GenLimit.PatientMachine.patientLowerDensity GenLimit.PartialEnumeration.Counterexample.oracle
              GenLimit.PartialEnumeration.Counterexample.stream
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))))
```

**Reconstruction.** The constants are fully fixed: stream(t)=4*(t+1); E=range(stream) is the positive multiples of 4; family(0)={x | x mod 2=1 or (x!=0 and x mod 4=0)}; family(i+1)={x | exists j>=i+1, x=2*j}; K=trueLanguage=family(1), the positive even naturals. oracle has this family and query equal to classical membership indicator. This is the original machine output for that oracle, without applying closure. The closed proposition conjoins all six components: (1) stream presents E; (2) E is infinite; (3) E subset K; (4) forall t, the output is 2*t+1; (5) there is no T such that every t>=T has output in K; (6) patientLowerDensity oracle stream 1=0. No conjunct is an unspecified existential construction: all sets, stream, oracle and target index 1 are fixed constants.

**Quantifier skeleton and dependencies.** Presents(stream,E) and Infinite(E) and E subset K and (forall t,g(t)=2*t+1) and not(exists T,forall t,T<=t->g(t) in K) and patientLowerDensity(oracle,stream,1)=0.

**Information available.** The constants are fully fixed: stream(t)=4*(t+1); E=range(stream) is the positive multiples of 4; family(0)={x | x mod 2=1 or (x!=0 and x mod 4=0)}; family(i+1)={x | exists j>=i+1, x=2*j}; K=trueLanguage=family(1), the positive even naturals. oracle has this family and query equal to classical membership indicator. This is the original machine output for that oracle, without applying closure.

**Edge cases.** The final density concerns GeneratorFirst of the original machine intersect family(1). It is not a claim of zero density for E in K. The negation is not merely failure at one early time; it excludes any eventual-membership threshold. This is a counterexample for this one semantic machine under these inputs.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.GeneratorFirst`, `GenLimit.KleinbergWei.OrderedLanguage.enumeration`, `GenLimit.KleinbergWei.OrderedLanguage.increasing`, `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`, `GenLimit.KleinbergWei.OrderedLanguage.prefixCount`, `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage`, `GenLimit.PartialEnumeration.Counterexample.family`, `GenLimit.PartialEnumeration.Counterexample.family.match_1`, `GenLimit.PartialEnumeration.Counterexample.firstLanguage`, `GenLimit.PartialEnumeration.Counterexample.oracle`, `GenLimit.PartialEnumeration.Counterexample.stream`, `GenLimit.PartialEnumeration.Counterexample.trueLanguage`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.patientLowerDensity`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T05: `GenLimit.PartialEnumeration.Counterexample.output_eq_odd`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:183`. Input anchor: `declarations.jsonl` record 32, duplicated in `01-target-statements.md`.

```lean
∀ (t : Nat),
  @Eq.{1} Nat
    (GenLimit.PatientMachine.output GenLimit.PartialEnumeration.Counterexample.oracle
      GenLimit.PartialEnumeration.Counterexample.stream t)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

**Reconstruction.** The constants are fully fixed: stream(t)=4*(t+1); E=range(stream) is the positive multiples of 4; family(0)={x | x mod 2=1 or (x!=0 and x mod 4=0)}; family(i+1)={x | exists j>=i+1, x=2*j}; K=trueLanguage=family(1), the positive even naturals. oracle has this family and query equal to classical membership indicator. This is the original machine output for that oracle, without applying closure. For every t, the output is exactly 2*t+1.

**Quantifier skeleton and dependencies.** forall t:Nat, output counterexample.oracle counterexample.stream t=2*t+1. There are no external assumptions or target quantifiers.

**Information available.** The constants are fully fixed: stream(t)=4*(t+1); E=range(stream) is the positive multiples of 4; family(0)={x | x mod 2=1 or (x!=0 and x mod 4=0)}; family(i+1)={x | exists j>=i+1, x=2*j}; K=trueLanguage=family(1), the positive even naturals. oracle has this family and query equal to classical membership indicator. This is the original machine output for that oracle, without applying closure.

**Edge cases.** Includes t=0, where output=1 while stream(0)=4. This is a fixed example, not a statement that every generator fails on these sets.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PartialEnumeration.Counterexample.family`, `GenLimit.PartialEnumeration.Counterexample.family.match_1`, `GenLimit.PartialEnumeration.Counterexample.firstLanguage`, `GenLimit.PartialEnumeration.Counterexample.oracle`, `GenLimit.PartialEnumeration.Counterexample.stream`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T06: `GenLimit.PartialEnumeration.Counterexample.output_not_mem_trueLanguage`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:247`. Input anchor: `declarations.jsonl` record 33, duplicated in `01-target-statements.md`.

```lean
∀ (t : Nat),
  GenLimit.PatientMachine.output GenLimit.PartialEnumeration.Counterexample.oracle
      GenLimit.PartialEnumeration.Counterexample.stream t ∉
    GenLimit.PartialEnumeration.Counterexample.trueLanguage
```

**Reconstruction.** The constants are fully fixed: stream(t)=4*(t+1); E=range(stream) is the positive multiples of 4; family(0)={x | x mod 2=1 or (x!=0 and x mod 4=0)}; family(i+1)={x | exists j>=i+1, x=2*j}; K=trueLanguage=family(1), the positive even naturals. oracle has this family and query equal to classical membership indicator. This is the original machine output for that oracle, without applying closure. Every output, at every t, is outside K.

**Quantifier skeleton and dependencies.** forall t:Nat, output counterexample.oracle counterexample.stream t notin counterexample.trueLanguage.

**Information available.** The constants are fully fixed: stream(t)=4*(t+1); E=range(stream) is the positive multiples of 4; family(0)={x | x mod 2=1 or (x!=0 and x mod 4=0)}; family(i+1)={x | exists j>=i+1, x=2*j}; K=trueLanguage=family(1), the positive even naturals. oracle has this family and query equal to classical membership indicator. This is the original machine output for that oracle, without applying closure.

**Edge cases.** All-time failure for this named unmodified machine on this stream; no claim about arbitrary algorithms or the closure-based generator.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PartialEnumeration.Counterexample.family`, `GenLimit.PartialEnumeration.Counterexample.family.match_1`, `GenLimit.PartialEnumeration.Counterexample.firstLanguage`, `GenLimit.PartialEnumeration.Counterexample.oracle`, `GenLimit.PartialEnumeration.Counterexample.stream`, `GenLimit.PartialEnumeration.Counterexample.trueLanguage`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T07: `GenLimit.PartialEnumeration.Counterexample.presents_enumeratedLanguage`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:93`. Input anchor: `declarations.jsonl` record 34, duplicated in `01-target-statements.md`.

```lean
GenLimit.Presents GenLimit.PartialEnumeration.Counterexample.stream
  GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage
```

**Reconstruction.** The constants are fully fixed: stream(t)=4*(t+1); E=range(stream) is the positive multiples of 4; family(0)={x | x mod 2=1 or (x!=0 and x mod 4=0)}; family(i+1)={x | exists j>=i+1, x=2*j}; K=trueLanguage=family(1), the positive even naturals. oracle has this family and query equal to classical membership indicator. This is the original machine output for that oracle, without applying closure. The range of the fixed stream is exactly enumeratedLanguage, which itself is defined as that range.

**Quantifier skeleton and dependencies.** Presents counterexample.stream counterexample.enumeratedLanguage; equivalently Set.range(stream)=enumeratedLanguage. Closed proposition.

**Information available.** The constants are fully fixed: stream(t)=4*(t+1); E=range(stream) is the positive multiples of 4; family(0)={x | x mod 2=1 or (x!=0 and x mod 4=0)}; family(i+1)={x | exists j>=i+1, x=2*j}; K=trueLanguage=family(1), the positive even naturals. oracle has this family and query equal to classical membership indicator. This is the original machine output for that oracle, without applying closure.

**Edge cases.** The statement alone does not contain infinitude, inclusion in K, or an output guarantee; those occur elsewhere. stream is an injective arithmetic enumeration, but injectivity is not part of this target type.

**Algorithm scope.** This is a predicate/set/counting statement, not a construction of an executable learner. All quantified languages are semantic subsets of Nat unless an OracleFamily is explicitly present.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Language`, `GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage`, `GenLimit.PartialEnumeration.Counterexample.stream`, `GenLimit.Presents`.

### T08: `GenLimit.PartialEnumeration.lemma_B_2_generation`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Partial.Validity:47`. Input anchor: `declarations.jsonl` record 44, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  GenLimit.Presents stream E →
    @Set.Infinite.{0} Nat E →
      @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) E (O.language z) →
        ∃ T,
          ∀ (t : Nat),
            @LE.le.{0} Nat instLENat T t →
              And
                (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
                  (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t))
                (And
                  (∀ (s : Nat),
                    @LE.le.{0} Nat instLENat s t →
                      @Ne.{1} Nat (stream s)
                        (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t))
                  (∀ (s : Nat),
                    @LT.lt.{0} Nat instLTNat s t →
                      @Ne.{1} Nat (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream s)
                        (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t)))
```

**Reconstruction.** For every O, stream, infinite E, and index z, assume range(stream)=E and E subset K=O.language(z). For the fixed closure-based generator g*, there exists T such that every t>=T has g*(t) in K, g*(t) different from every stream(s) with s<=t, and g*(t) different from every g*(s) with s<t. Target membership is in K, with no assertion that g*(t) belongs to E.

**Quantifier skeleton and dependencies.** forall (O:OracleFamily), {stream:Nat->Nat}, {E:Language}, {z:Nat}; Presents(stream,E) -> Set.Infinite E -> E subset K -> exists T, forall t>=T, g*(t) in K and (forall s<=t, stream(s)!=g*(t)) and (forall s<t, g*(s)!=g*(t)). T may depend on O,stream,E,z and the hypotheses, with no rate.

**Information available.** The generator receives O through closure and stream only. E,z and the infinitude/subset hypotheses are analysis parameters.

**Edge cases.** E must be infinite, so empty/finite observed languages are outside these theorems; K is infinite by O. E need not be a family member. Repetitions and any enumeration speed are allowed. The density may be zero, yielding a zero lower bound; no positive-density assumption or rate is present. The earlier-output and observation comparisons include all earlier rounds, not only t>=T.

**Algorithm scope.** The named generator is g*(t)=GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t. It is fixed for O and stream, without E, z, alpha or a density witness as generator inputs. closureCode enumerates codes selected by infinitude of finite intersections using Nat.nth; this preprocessing is semantic and is not established computable from O.query. Conditional on a selected code, the closure query is the finite conjunction of original membership queries. The machine also retains the classical set-inclusion and existence tests described in the glossary.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.OracleFamily.query`, `GenLimit.PartialEnumeration.GoodCode`, `GenLimit.PartialEnumeration.closure`, `GenLimit.PartialEnumeration.closureCode`, `GenLimit.PartialEnumeration.codeSupport`, `GenLimit.PartialEnumeration.codedIntersection`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T09: `GenLimit.PartialEnumeration.theorem_B_3`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Partial.Main:63`. Input anchor: `declarations.jsonl` record 46, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  GenLimit.Presents stream E →
    @Set.Infinite.{0} Nat E →
      @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) E (O.language z) →
        ∀ (α : Real),
          @Eq.{1} Real (GenLimit.PatientScope.relativeLowerDensity E (O.language z) ⋯) α →
            @LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) α
                (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
              (GenLimit.PartialEnumeration.partialPatientLowerDensity O stream z)
```

**Reconstruction.** For every O, stream, infinite E, and index z, assume range(stream)=E and E subset K=O.language(z). For every real alpha equal to relativeLowerDensity E K, alpha/2 is at most the liminf target-relative density of GeneratorFirst(stream,g*) intersect K, along the increasing enumeration of K. The equality fixes alpha to that lower density; it is not an unrestricted free performance parameter.

**Quantifier skeleton and dependencies.** forall (O:OracleFamily), {stream:Nat->Nat}, {E:Language}, {z:Nat}; Presents(stream,E) -> Set.Infinite E -> E subset K -> forall alpha:Real, relativeLowerDensity(E,K)=alpha -> alpha/2 <= partialPatientLowerDensity O stream z.

**Information available.** alpha is a theorem parameter after the presentation, infinitude and subset hypotheses; it is not input to g*. Output is the same semantic function for all compatible E,z.

**Edge cases.** E must be infinite, so empty/finite observed languages are outside these theorems; K is infinite by O. E need not be a family member. Repetitions and any enumeration speed are allowed. The density may be zero, yielding a zero lower bound; no positive-density assumption or rate is present. This type contains no generation conjunct, finite-prefix bound, limit-existence statement, or convergence rate.

**Algorithm scope.** The named generator is g*(t)=GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t. It is fixed for O and stream, without E, z, alpha or a density witness as generator inputs. closureCode enumerates codes selected by infinitude of finite intersections using Nat.nth; this preprocessing is semantic and is not established computable from O.query. Conditional on a selected code, the closure query is the finite conjunction of original membership queries. The machine also retains the classical set-inclusion and existence tests described in the glossary.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.GeneratorFirst`, `GenLimit.KleinbergWei.OrderedLanguage.enumeration`, `GenLimit.KleinbergWei.OrderedLanguage.increasing`, `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`, `GenLimit.KleinbergWei.OrderedLanguage.prefixCount`, `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.OracleFamily.query`, `GenLimit.PartialEnumeration.GoodCode`, `GenLimit.PartialEnumeration.closure`, `GenLimit.PartialEnumeration.closureCode`, `GenLimit.PartialEnumeration.codeSupport`, `GenLimit.PartialEnumeration.codedIntersection`, `GenLimit.PartialEnumeration.partialPatientLowerDensity`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T10: `GenLimit.PartialEnumeration.theorem_B_3_lowerDensity`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Partial.Main:42`. Input anchor: `declarations.jsonl` record 47, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  GenLimit.Presents stream E →
    @Set.Infinite.{0} Nat E →
      @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) E (O.language z) →
        @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
            (GenLimit.PatientScope.relativeLowerDensity E (O.language z) ⋯))
          (GenLimit.PartialEnumeration.partialPatientLowerDensity O stream z)
```

**Reconstruction.** For every O, stream, infinite E, and index z, assume range(stream)=E and E subset K=O.language(z). (1/2)*relativeLowerDensity E K is at most the liminf target-relative density of GeneratorFirst(stream,g*) intersect K, along the increasing enumeration of K. This version directly uses the density value rather than separately quantifying a real alpha and an equality.

**Quantifier skeleton and dependencies.** forall (O:OracleFamily), {stream:Nat->Nat}, {E:Language}, {z:Nat}; Presents(stream,E) -> Set.Infinite E -> E subset K -> (1/2)*relativeLowerDensity(E,K)<=partialPatientLowerDensity O stream z.

**Information available.** E and K determine the two sets against which densities are evaluated; neither z nor E is provided to g*.

**Edge cases.** E must be infinite, so empty/finite observed languages are outside these theorems; K is infinite by O. E need not be a family member. Repetitions and any enumeration speed are allowed. The density may be zero, yielding a zero lower bound; no positive-density assumption or rate is present. There is no validity or freshness conjunct in this target.

**Algorithm scope.** The named generator is g*(t)=GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t. It is fixed for O and stream, without E, z, alpha or a density witness as generator inputs. closureCode enumerates codes selected by infinitude of finite intersections using Nat.nth; this preprocessing is semantic and is not established computable from O.query. Conditional on a selected code, the closure query is the finite conjunction of original membership queries. The machine also retains the classical set-inclusion and existence tests described in the glossary.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.GeneratorFirst`, `GenLimit.KleinbergWei.OrderedLanguage.enumeration`, `GenLimit.KleinbergWei.OrderedLanguage.increasing`, `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`, `GenLimit.KleinbergWei.OrderedLanguage.prefixCount`, `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.OracleFamily.query`, `GenLimit.PartialEnumeration.GoodCode`, `GenLimit.PartialEnumeration.closure`, `GenLimit.PartialEnumeration.closureCode`, `GenLimit.PartialEnumeration.codeSupport`, `GenLimit.PartialEnumeration.codedIntersection`, `GenLimit.PartialEnumeration.partialPatientLowerDensity`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T11: `GenLimit.PartialEnumeration.theorem_B_3_with_generation`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Partial.Main:78`. Input anchor: `declarations.jsonl` record 48, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  GenLimit.Presents stream E →
    @Set.Infinite.{0} Nat E →
      @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) E (O.language z) →
        And
          (∃ T,
            ∀ (t : Nat),
              @LE.le.{0} Nat instLENat T t →
                And
                  (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
                    (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t))
                  (And
                    (∀ (s : Nat),
                      @LE.le.{0} Nat instLENat s t →
                        @Ne.{1} Nat (stream s)
                          (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t))
                    (∀ (s : Nat),
                      @LT.lt.{0} Nat instLTNat s t →
                        @Ne.{1} Nat (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream s)
                          (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t))))
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
              (GenLimit.PatientScope.relativeLowerDensity E (O.language z) ⋯))
            (GenLimit.PartialEnumeration.partialPatientLowerDensity O stream z))
```

**Reconstruction.** For every O, stream, infinite E, and index z, assume range(stream)=E and E subset K=O.language(z). The conclusion conjoins: (i) there exists T such that every t>=T has g*(t) in K, differs from every stream(s) for s<=t, and differs from every earlier g*(s) for s<t; (ii) (1/2)*relativeLowerDensity E K is at most the liminf target-relative density of GeneratorFirst(stream,g*) intersect K, along the increasing enumeration of K. The density conjunct is outside the existential T.

**Quantifier skeleton and dependencies.** forall (O:OracleFamily), {stream:Nat->Nat}, {E:Language}, {z:Nat}; Presents(stream,E) -> Set.Infinite E -> E subset K -> ((exists T, forall t>=T, g*(t) in K and (forall s<=t, stream(s)!=g*(t)) and (forall s<t, g*(s)!=g*(t))) and ((1/2)*relativeLowerDensity(E,K)<=partialPatientLowerDensity O stream z)).

**Information available.** g* is fixed without E,z or a density value as inputs. Existence of T is pointwise for the fixed theorem data.

**Edge cases.** E must be infinite, so empty/finite observed languages are outside these theorems; K is infinite by O. E need not be a family member. Repetitions and any enumeration speed are allowed. The density may be zero, yielding a zero lower bound; no positive-density assumption or rate is present. Both all-earlier freshness clauses are preserved; generation is eventually in K, not asserted eventually in E.

**Algorithm scope.** The named generator is g*(t)=GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t. It is fixed for O and stream, without E, z, alpha or a density witness as generator inputs. closureCode enumerates codes selected by infinitude of finite intersections using Nat.nth; this preprocessing is semantic and is not established computable from O.query. Conditional on a selected code, the closure query is the finite conjunction of original membership queries. The machine also retains the classical set-inclusion and existence tests described in the glossary.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.GeneratorFirst`, `GenLimit.KleinbergWei.OrderedLanguage.enumeration`, `GenLimit.KleinbergWei.OrderedLanguage.increasing`, `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`, `GenLimit.KleinbergWei.OrderedLanguage.prefixCount`, `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.OracleFamily.query`, `GenLimit.PartialEnumeration.GoodCode`, `GenLimit.PartialEnumeration.closure`, `GenLimit.PartialEnumeration.closureCode`, `GenLimit.PartialEnumeration.codeSupport`, `GenLimit.PartialEnumeration.codedIntersection`, `GenLimit.PartialEnumeration.partialPatientLowerDensity`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T12: `GenLimit.PatientMachine.SwitchRound`

Kind: definition. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Pairing:40`. Input anchor: `declarations.jsonl` record 87, duplicated in `01-target-statements.md`.

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → Prop
```

Exact definition value:

```lean
fun O stream t => stream t ∉ O.language (GenLimit.PatientMachine.run O stream t).focus
```

**Reconstruction.** SwitchRound O stream t means stream(t) is not a member of the language indexed by the focus of run O stream t, the state before processing that announcement. It is a membership failure predicate, with no explicit requirement that the focus index changes after the transition.

**Quantifier skeleton and dependencies.** forall O,stream,t; SwitchRound iff stream(t) notin O.language((run O stream t).focus).

**Information available.** Uses the current announcement and the pre-round focus's semantic language.

**Edge cases.** Defined also at t=0 and off-model; a move tag, scope change or index inequality is not part of this definition.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.SwitchRound`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T13: `GenLimit.PatientMachine.fact_3_13`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Fact313:16`. Input anchor: `declarations.jsonl` record 97, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {t : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t →
    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
        (GenLimit.AdversaryFirst stream (GenLimit.PatientMachine.output O stream)) (stream t) →
      stream t ∉ GenLimit.sample stream t →
        Not (GenLimit.PatientMachine.SwitchRound O stream t) →
          And
            (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
              (O.language (GenLimit.PatientMachine.run O stream t).focus) (stream t))
            (@LT.lt.{0} Nat instLTNat
              (GenLimit.PatientMachine.output O stream
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) t
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (stream t))
```

**Reconstruction.** If t>0, stream(t) belongs to AdversaryFirst(stream,g), is absent from sample stream t, and round t is not SwitchRound, then both stream(t) belongs to the pre-round focus language O.language((run O stream t).focus) and g(t-1)<stream(t). The result contains both membership and strict numerical inequality.

**Quantifier skeleton and dependencies.** forall O,stream,{t}; 0<t -> stream(t) in AdversaryFirst(stream,g) -> stream(t) notin sample(stream,t) -> not SwitchRound(O,stream,t) -> (stream(t) in O.language((run t).focus) and g(t-1)<stream(t)).

**Information available.** No target z, presentation, validity threshold or stabilization assumption.

**Edge cases.** Excluded t=0 avoids truncated predecessor ambiguity; prior stream repetitions are excluded by the sample premise. Numerical value inequality does not assert increasing outputs at all rounds.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.AdversaryFirst`, `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.SwitchRound`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T14: `GenLimit.PatientMachine.lemma_3_14`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Charging:44`. Input anchor: `declarations.jsonl` record 105, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z : Nat) (hP : GenLimit.Presents stream (O.language z)) (n : Nat),
  @LE.le.{0} Nat instLENat
    (GenLimit.PatientScope.prefixCount (GenLimit.PatientMachine.settledSwitchLoss O stream z hP) n)
    (GenLimit.PatientScope.prefixCount (O.language z) n).log2
```

**Reconstruction.** For every O,stream,z,hP presenting K=O.language(z) and every ambient cutoff n, prefixCount(settledSwitchLoss O stream z hP,n) is at most Nat.log2(prefixCount(K,n)). This is an all-cutoff finite counting bound for the specifically settled loss set.

**Quantifier skeleton and dependencies.** forall O,stream,z,hP:Presents stream K,n:Nat; prefixCount(settledSwitchLoss O stream z hP,n)<=Nat.log2(prefixCount(K,n)). The set depends on the presentation proof through its defined threshold.

**Information available.** z and hP locate the settled loss analysis; they are absent from the generator interface.

**Edge cases.** No asymptotic-only qualifier: it holds also at n=0 and when target prefix count is 0 or 1. It counts distinct values, not switch times or round frequencies. No computable bound on the settlement threshold is supplied.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.AdversaryFirst`, `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.SwitchRound`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.criticalStart`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.lateSwitchLoss`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.scopeStart`, `GenLimit.PatientMachine.settledSwitchLoss`, `GenLimit.PatientMachine.settledThreshold`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.prefixCount`, `GenLimit.PatientScope.prefixFinset`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T15: `GenLimit.PatientMachine.output`

Kind: definition. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Machine:387`. Input anchor: `declarations.jsonl` record 109, duplicated in `01-target-statements.md`.

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → Nat
```

Exact definition value:

```lean
fun O stream t =>
  @Option.getD.{0} Nat
    (GenLimit.PatientMachine.run O stream
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).lastOutput
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```

**Reconstruction.** At time t, output O stream t is the lastOutput field of run O stream (t+1), with default 0 if that Option is none. Since processRound always stores some x, the successor-state field supplies the least natural x in the newly chosen focus language, absent from observations through time t and absent from the previous used set. The initial state's none is not directly output at t=0.

**Quantifier skeleton and dependencies.** forall O,stream,t:Nat, output O stream t:Nat = (run O stream (t+1)).lastOutput.getD 0. No target or presentation binder.

**Information available.** Same semantic family access as run; stream(t) is observed before this round's choice. z, a target identity, stabilization times and future stream values are absent from the rule.

**Edge cases.** Exactly one natural number is output per round. This is not a support-valued or distribution-valued generator. Output need not lie in an arbitrary true target before eventual validity, or off-model; freshness itself holds for every O and stream by supplied native helper types. Infinitude prevents exhausting a focus language with the two finite forbidden sets.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T16: `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Main:53`. Input anchor: `declarations.jsonl` record 112, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {z : Nat},
  GenLimit.Presents stream (O.language z) →
    And
      (∃ T,
        ∀ (t : Nat),
          @LE.le.{0} Nat instLENat T t →
            And
              (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
                (GenLimit.PatientMachine.output O stream t))
              (And
                (∀ (s : Nat),
                  @LE.le.{0} Nat instLENat s t → @Ne.{1} Nat (stream s) (GenLimit.PatientMachine.output O stream t))
                (∀ (s : Nat),
                  @LT.lt.{0} Nat instLTNat s t →
                    @Ne.{1} Nat (GenLimit.PatientMachine.output O stream s)
                      (GenLimit.PatientMachine.output O stream t))))
      (@LE.le.{0} Real Real.instLE
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
        (GenLimit.PatientMachine.patientLowerDensity O stream z))
```

**Reconstruction.** For every O and stream with range K=O.language(z), a time T exists after which each g(t) lies in K, differs from every observation stream(s) with s<=t, and differs from every prior output g(s) with s<t. In the same conclusion, the target-relative lower density of GeneratorFirst(stream,g) intersect K is at least 1/2. The density is a liminf of set proportions along the increasing enumeration of K, not a fraction of successful time rounds.

**Quantifier skeleton and dependencies.** forall O,stream,{z}; Presents(stream,K) -> ((exists T, forall t>=T, g(t) in K and (forall s<=t, stream(s)!=g(t)) and (forall s<t, g(s)!=g(t))) and (1/2 <= relativeLowerDensity(GeneratorFirst(stream,g) intersect K,K))). The density conjunct is outside the existential T.

**Information available.** Uniform named semantic generator g=output O stream; it is not chosen separately for z. Analysis uses z and presentation. The eventual T may depend on O,stream,z.

**Edge cases.** The quantified earlier s in both freshness clauses include all earlier times, including s<T; no claim of target validity at those early times. No rate, finite-prefix ratio lower bound or ordinary density limit is asserted. Stream may repeat and family indices may denote equal languages.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.GeneratorFirst`, `GenLimit.KleinbergWei.OrderedLanguage.enumeration`, `GenLimit.KleinbergWei.OrderedLanguage.increasing`, `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`, `GenLimit.KleinbergWei.OrderedLanguage.prefixCount`, `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.patientLowerDensity`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T17: `GenLimit.PatientMachine.patientScope_lowerDensity_half`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Main:36`. Input anchor: `declarations.jsonl` record 113, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {z : Nat},
  GenLimit.Presents stream (O.language z) →
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
      (GenLimit.PatientMachine.patientLowerDensity O stream z)
```

**Reconstruction.** For every O and stream presenting K=O.language(z), the liminf of the proportion of the first n increasing elements of K that belong to GeneratorFirst(stream,output O stream) intersect K is at least 1/2.

**Quantifier skeleton and dependencies.** forall O,stream,{z}; Presents(stream,K) -> 1/2 <= patientLowerDensity O stream z. No existential program or threshold appears in this type.

**Information available.** Same fixed named semantic generator as output; z selects the set against which density is evaluated.

**Edge cases.** This type contains no generation/freshness conjunction and no quantitative convergence rate. K is infinite via O. The ratio at n=0 is defined as 0, without affecting this asymptotic liminf.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.GeneratorFirst`, `GenLimit.KleinbergWei.OrderedLanguage.enumeration`, `GenLimit.KleinbergWei.OrderedLanguage.increasing`, `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`, `GenLimit.KleinbergWei.OrderedLanguage.prefixCount`, `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.patientLowerDensity`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T18: `GenLimit.PatientMachine.patient_validity`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Validity:233`. Input anchor: `declarations.jsonl` record 114, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {z : Nat},
  GenLimit.Presents stream (O.language z) →
    ∃ T,
      ∀ (t : Nat),
        @LE.le.{0} Nat instLENat T t →
          @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
            (GenLimit.PatientMachine.output O stream t)
```

**Reconstruction.** For every oracle family O and stream presenting its language at index z, there exists T such that for every t>=T, output O stream t belongs to O.language(z). This target asserts eventual membership only.

**Quantifier skeleton and dependencies.** forall O,stream,{z}; Presents(stream,O.language z) -> exists T, forall t, T<=t -> g(t) in O.language z. T follows O,stream,z and may depend on them; no uniform rate.

**Information available.** The generator is the fixed output function; z and presentation are theorem parameters, not generator inputs.

**Edge cases.** All family languages are infinite by OracleFamily. Repetitions in a presenting stream are allowed. No statement of membership before T. Freshness and density are not conjuncts of this particular target.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T19: `GenLimit.PatientMachine.predecessorPartner_injective_machine`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Pairing:173`. Input anchor: `declarations.jsonl` record 115, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z validFrom : Nat) (hP : GenLimit.Presents stream (O.language z))
  (hvalid :
    ∀ (t : Nat),
      @LE.le.{0} Nat instLENat validFrom t →
        @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
          (GenLimit.PatientMachine.output O stream t)),
  @Set.InjOn.{0, 0} Nat Nat (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).predecessorPartner
    (GenLimit.PatientScope.ordinaryAttacker (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).target
      (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).attacker
      (GenLimit.PatientMachine.lateSwitchLoss O stream validFrom)
      (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).earlyAttacker)
```

**Reconstruction.** Fix O,stream,z,validFrom, hP:range(stream)=K=O.language(z), and hvalid:forall t>=validFrom, g(t) in K. gameTrace has target K, adversary stream, generator g, validFrom as supplied; attacker=AdversaryFirst(stream,g), defender=GeneratorFirst(stream,g); earlyAttacker is attacker filtered from sample stream (validFrom+1). ordinaryAttacker=(attacker intersect K) minus (earlyAttacker union lateSwitchLoss O stream validFrom). predecessorPartner is injective on that domain: if x and y are both in it and their partners coincide, x=y.

**Quantifier skeleton and dependencies.** forall O,stream,z,validFrom,hP,hvalid; Set.InjOn partner ordinaryAttacker, meaning forall x,y in domain, partner(x)=partner(y) -> x=y.

**Information available.** Fix O,stream,z,validFrom, hP:range(stream)=K=O.language(z), and hvalid:forall t>=validFrom, g(t) in K. gameTrace has target K, adversary stream, generator g, validFrom as supplied; attacker=AdversaryFirst(stream,g), defender=GeneratorFirst(stream,g); earlyAttacker is attacker filtered from sample stream (validFrom+1). ordinaryAttacker=(attacker intersect K) minus (earlyAttacker union lateSwitchLoss O stream validFrom).

**Edge cases.** The domain may be empty, making InjOn and pointwise properties vacuous. validFrom=0 is allowed; earlyAttacker uses observations through that index (sample at validFrom+1). No distinctness of stream announcements is assumed; partner uses first announcement time. The partner function is total with default first-time 0 and truncated subtraction, but these theorems apply only on ordinaryAttacker.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.AdversaryFirst`, `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.SwitchRound`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.gameTrace`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.lateSwitchLoss`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.GameTrace.adversary`, `GenLimit.PatientScope.GameTrace.attacker`, `GenLimit.PatientScope.GameTrace.earlyAttacker`, `GenLimit.PatientScope.GameTrace.generator`, `GenLimit.PatientScope.GameTrace.predecessorPartner`, `GenLimit.PatientScope.GameTrace.target`, `GenLimit.PatientScope.GameTrace.validFrom`, `GenLimit.PatientScope.ordinaryAttacker`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.firstAnnouncementTime`, `GenLimit.predecessorPartner`, `GenLimit.sample`.

### T20: `GenLimit.PatientMachine.predecessorPartner_lt_machine`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Pairing:163`. Input anchor: `declarations.jsonl` record 116, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z validFrom : Nat) (hP : GenLimit.Presents stream (O.language z))
  (hvalid :
    ∀ (t : Nat),
      @LE.le.{0} Nat instLENat validFrom t →
        @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
          (GenLimit.PatientMachine.output O stream t))
  {x : Nat},
  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (GenLimit.PatientScope.ordinaryAttacker (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).target
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).attacker
        (GenLimit.PatientMachine.lateSwitchLoss O stream validFrom)
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).earlyAttacker)
      x →
    @LT.lt.{0} Nat instLTNat ((GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).predecessorPartner x) x
```

**Reconstruction.** Fix O,stream,z,validFrom, hP:range(stream)=K=O.language(z), and hvalid:forall t>=validFrom, g(t) in K. gameTrace has target K, adversary stream, generator g, validFrom as supplied; attacker=AdversaryFirst(stream,g), defender=GeneratorFirst(stream,g); earlyAttacker is attacker filtered from sample stream (validFrom+1). ordinaryAttacker=(attacker intersect K) minus (earlyAttacker union lateSwitchLoss O stream validFrom). Every x in that domain has predecessorPartner(x)<x in the numerical order on natural values, not in announcement time.

**Quantifier skeleton and dependencies.** forall O,stream,z,validFrom,hP,hvalid, {x}; x in ordinaryAttacker -> partner(x)<x.

**Information available.** Fix O,stream,z,validFrom, hP:range(stream)=K=O.language(z), and hvalid:forall t>=validFrom, g(t) in K. gameTrace has target K, adversary stream, generator g, validFrom as supplied; attacker=AdversaryFirst(stream,g), defender=GeneratorFirst(stream,g); earlyAttacker is attacker filtered from sample stream (validFrom+1). ordinaryAttacker=(attacker intersect K) minus (earlyAttacker union lateSwitchLoss O stream validFrom).

**Edge cases.** The domain may be empty, making InjOn and pointwise properties vacuous. validFrom=0 is allowed; earlyAttacker uses observations through that index (sample at validFrom+1). No distinctness of stream announcements is assumed; partner uses first announcement time. The partner function is total with default first-time 0 and truncated subtraction, but these theorems apply only on ordinaryAttacker.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.AdversaryFirst`, `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.SwitchRound`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.gameTrace`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.lateSwitchLoss`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.GameTrace.adversary`, `GenLimit.PatientScope.GameTrace.attacker`, `GenLimit.PatientScope.GameTrace.earlyAttacker`, `GenLimit.PatientScope.GameTrace.generator`, `GenLimit.PatientScope.GameTrace.predecessorPartner`, `GenLimit.PatientScope.GameTrace.target`, `GenLimit.PatientScope.GameTrace.validFrom`, `GenLimit.PatientScope.ordinaryAttacker`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.firstAnnouncementTime`, `GenLimit.predecessorPartner`, `GenLimit.sample`.

### T21: `GenLimit.PatientMachine.predecessorPartner_mem_machine`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Pairing:154`. Input anchor: `declarations.jsonl` record 117, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z validFrom : Nat) (hP : GenLimit.Presents stream (O.language z))
  (hvalid :
    ∀ (t : Nat),
      @LE.le.{0} Nat instLENat validFrom t →
        @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
          (GenLimit.PatientMachine.output O stream t))
  {x : Nat},
  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (GenLimit.PatientScope.ordinaryAttacker (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).target
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).attacker
        (GenLimit.PatientMachine.lateSwitchLoss O stream validFrom)
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).earlyAttacker)
      x →
    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (@Inter.inter.{0} (Set.{0} Nat) (@Set.instInter.{0} Nat)
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).defender
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).target)
      ((GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).predecessorPartner x)
```

**Reconstruction.** Fix O,stream,z,validFrom, hP:range(stream)=K=O.language(z), and hvalid:forall t>=validFrom, g(t) in K. gameTrace has target K, adversary stream, generator g, validFrom as supplied; attacker=AdversaryFirst(stream,g), defender=GeneratorFirst(stream,g); earlyAttacker is attacker filtered from sample stream (validFrom+1). ordinaryAttacker=(attacker intersect K) minus (earlyAttacker union lateSwitchLoss O stream validFrom). For every x in that ordinaryAttacker domain, its predecessorPartner lies in defender intersect target. Partner is g(firstAnnouncementTime(stream,x)-1), where firstAnnouncementTime is the least occurrence time if one exists and 0 otherwise.

**Quantifier skeleton and dependencies.** forall O,stream,z,validFrom,hP,hvalid, {x}; x in ordinaryAttacker -> partner(x) in (defender intersect target). hvalid is an explicit universal hypothesis following hP.

**Information available.** Fix O,stream,z,validFrom, hP:range(stream)=K=O.language(z), and hvalid:forall t>=validFrom, g(t) in K. gameTrace has target K, adversary stream, generator g, validFrom as supplied; attacker=AdversaryFirst(stream,g), defender=GeneratorFirst(stream,g); earlyAttacker is attacker filtered from sample stream (validFrom+1). ordinaryAttacker=(attacker intersect K) minus (earlyAttacker union lateSwitchLoss O stream validFrom).

**Edge cases.** The domain may be empty, making InjOn and pointwise properties vacuous. validFrom=0 is allowed; earlyAttacker uses observations through that index (sample at validFrom+1). No distinctness of stream announcements is assumed; partner uses first announcement time. The partner function is total with default first-time 0 and truncated subtraction, but these theorems apply only on ordinaryAttacker.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.AdversaryFirst`, `GenLimit.Consistent`, `GenLimit.GeneratorFirst`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.SwitchRound`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.gameTrace`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.lateSwitchLoss`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.PatientScope.GameTrace.adversary`, `GenLimit.PatientScope.GameTrace.attacker`, `GenLimit.PatientScope.GameTrace.defender`, `GenLimit.PatientScope.GameTrace.earlyAttacker`, `GenLimit.PatientScope.GameTrace.generator`, `GenLimit.PatientScope.GameTrace.predecessorPartner`, `GenLimit.PatientScope.GameTrace.target`, `GenLimit.PatientScope.GameTrace.validFrom`, `GenLimit.PatientScope.ordinaryAttacker`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.firstAnnouncementTime`, `GenLimit.predecessorPartner`, `GenLimit.sample`.

### T22: `GenLimit.PatientMachine.previous_output_lt_of_not_lateSwitch`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Pairing:108`. Input anchor: `declarations.jsonl` record 118, duplicated in `01-target-statements.md`.

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {validFrom t : Nat},
  @LT.lt.{0} Nat instLTNat validFrom t →
    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
        (GenLimit.AdversaryFirst stream (GenLimit.PatientMachine.output O stream)) (stream t) →
      stream t ∉ GenLimit.sample stream t →
        stream t ∉ GenLimit.PatientMachine.lateSwitchLoss O stream validFrom →
          @LT.lt.{0} Nat instLTNat
            (GenLimit.PatientMachine.output O stream
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) t
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (stream t)
```

**Reconstruction.** For any O and stream, if validFrom<t, stream(t) belongs to AdversaryFirst(stream,g), stream(t) was absent from the earlier sample, and stream(t) is not in lateSwitchLoss O stream validFrom, then g(t-1)<stream(t). This does not assume that validFrom is actually a validity threshold or that stream presents a target.

**Quantifier skeleton and dependencies.** forall O,stream,{validFrom,t}; validFrom<t -> stream(t) in AdversaryFirst(stream,g) -> stream(t) notin sample(stream,t) -> stream(t) notin lateSwitchLoss(O,stream,validFrom) -> g(t-1)<stream(t).

**Information available.** The cutoff is a supplied natural; the loss predicate and the two first-announcement premises restrict which rounds qualify.

**Edge cases.** validFrom<t ensures t>0, so t-1 is the preceding round. Repeated stream values fail the new-announcement premise. No conclusion on switch-loss or early values.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.AdversaryFirst`, `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.SwitchRound`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.lateSwitchLoss`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T23: `GenLimit.PatientMachine.run`

Kind: definition. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Machine:380`. Input anchor: `declarations.jsonl` record 120, duplicated in `01-target-statements.md`.

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → GenLimit.PatientMachine.State
```

Exact definition value:

```lean
fun O stream x =>
  @Nat.brecOn.{1} (fun x => GenLimit.PatientMachine.State) x fun x f =>
    GenLimit.PatientMachine.run.match_1.{1}
      (fun x => @Nat.below.{1} (fun x => GenLimit.PatientMachine.State) x → GenLimit.PatientMachine.State) x
      (fun a x => GenLimit.PatientMachine.initialState) (fun t x => GenLimit.PatientMachine.processRound O stream t x.1)
      f
```

**Reconstruction.** run O stream 0 is initialState. run O stream (t+1) is processRound O stream t (run O stream t). It returns the complete State after processing stream values at rounds 0 through t-1. State has scope, tau, age, focus, used, lastOutput and move fields. The glossary below specifies every decision branch, fallback, state update and output search used by processRound.

**Quantifier skeleton and dependencies.** forall O:OracleFamily, stream:Nat->Nat, t:Nat, run O stream t:State. This is a definition, with no presentation or target hypothesis and no existential learner witness. The recursion is on t.

**Information available.** O includes an infinite semantic language at each natural index, Boolean membership queries and their correctness law. run uses O.language and infinitude, plus the stream prefix. The full semantic family, rather than merely finite query answers, enters branch tests.

**Edge cases.** At t=0 there is no last output. Off-model prefixes with no consistent language use the explicit backtrack fallback; totality of output search still uses infinitude of every focus language. No target z is required. Natural subtraction in helper definitions is truncated.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`.

### T24: `GenLimit.PatientMachine.settledChargingCertificate`

Kind: definition. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Patient.Charging:33`. Input anchor: `declarations.jsonl` record 123, duplicated in `01-target-statements.md`.

```lean
(O : GenLimit.OracleFamily) →
  (stream : Nat → Nat) →
    (z : Nat) →
      (hP : GenLimit.Presents stream (O.language z)) →
        GenLimit.PatientScope.TargetSwitchChargingCertificate (O.language z)
          (GenLimit.PatientMachine.settledSwitchLoss O stream z hP)
```

Exact definition value:

```lean
fun O stream z hP =>
  @id.{1}
    (GenLimit.PatientScope.TargetSwitchChargingCertificate (O.language z)
      (GenLimit.PatientMachine.settledSwitchLoss O stream z hP))
    (@GenLimit.PatientMachine.StableTargetRun.chargingCertificate O stream (O.language z)
      (GenLimit.PatientMachine.settledStableTargetRun✝ O stream z hP))
```

**Reconstruction.** For any O,stream,z and hP presenting K=O.language(z), this definition returns a TargetSwitchChargingCertificate for K and settledSwitchLoss O stream z hP. The latter is lateSwitchLoss at settledThreshold=max(criticalStart,scopeStart); these starts are the least times whose universal future conditions keep z recursively critical and in scope. The returned certificate is the chargingCertificate of the named stable-target run with witness z and that threshold. Its tau and charge are concretely defined as described in the glossary.

**Quantifier skeleton and dependencies.** (O)->(stream)->(z)->(hP:Presents stream K)-> TargetSwitchChargingCertificate K (settledSwitchLoss O stream z hP). All listed inputs precede the returned data; there is no exists Q choosing an unspecified certificate.

**Information available.** The certificate is an analysis construction using z, hP and future-stability predicates, not extra information supplied to output. It includes all six constructor obligations, including positivity and injectivity of tau.

**Edge cases.** Natural labels are positive only on loss elements; charge and tau are total functions with fallbacks elsewhere. If losses are empty, the obligations are vacuous. The threshold has no rate and is not established computable from a finite prefix.

**Algorithm scope.** The named generator is g(t)=GenLimit.PatientMachine.output O stream t, fixed uniformly as a semantic function of O and stream; target index z is absent from its arguments. Its state transition uses only stream values through the current round, but inspects the semantic family using classical decisions, including universal set inclusion in RecursiveCritical and an existence test over all indices. O supplies a Boolean membership query and its specification, not an effective subset or infinitude decision procedure. The exported definitions do not establish ordinary computability, runtime, or an executable oracle implementation.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.AdversaryFirst`, `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.OracleFamily.language`, `GenLimit.PatientMachine.Available`, `GenLimit.PatientMachine.Decision.focus`, `GenLimit.PatientMachine.Decision.move`, `GenLimit.PatientMachine.Decision.scope`, `GenLimit.PatientMachine.Decision.tau`, `GenLimit.PatientMachine.OnModel`, `GenLimit.PatientMachine.StableTargetRun.IsSwitchTime`, `GenLimit.PatientMachine.StableTargetRun.charge`, `GenLimit.PatientMachine.StableTargetRun.chargingCertificate`, `GenLimit.PatientMachine.StableTargetRun.departure`, `GenLimit.PatientMachine.StableTargetRun.landingFocus`, `GenLimit.PatientMachine.StableTargetRun.switchTime`, `GenLimit.PatientMachine.StableTargetRun.tau`, `GenLimit.PatientMachine.StableTargetRun.threshold`, `GenLimit.PatientMachine.State.age`, `GenLimit.PatientMachine.State.focus`, `GenLimit.PatientMachine.State.lastOutput`, `GenLimit.PatientMachine.State.move`, `GenLimit.PatientMachine.State.scope`, `GenLimit.PatientMachine.State.tau`, `GenLimit.PatientMachine.State.used`, `GenLimit.PatientMachine.SwitchRound`, `GenLimit.PatientMachine.UpwardDeparture`, `GenLimit.PatientMachine.backtrackDecision`, `GenLimit.PatientMachine.consistentIndices`, `GenLimit.PatientMachine.criticalIndices`, `GenLimit.PatientMachine.criticalStart`, `GenLimit.PatientMachine.decide`, `GenLimit.PatientMachine.departureTimes`, `GenLimit.PatientMachine.highestCritical`, `GenLimit.PatientMachine.highestSurvivor`, `GenLimit.PatientMachine.initialState`, `GenLimit.PatientMachine.lateSwitchLoss`, `GenLimit.PatientMachine.latestDeparture`, `GenLimit.PatientMachine.leastAvailable`, `GenLimit.PatientMachine.lowestConsistent`, `GenLimit.PatientMachine.lowestConsistentInScope`, `GenLimit.PatientMachine.output`, `GenLimit.PatientMachine.processRound`, `GenLimit.PatientMachine.run`, `GenLimit.PatientMachine.run.match_1`, `GenLimit.PatientMachine.scopeStart`, `GenLimit.PatientMachine.settledChargingCertificate`, `GenLimit.PatientMachine.settledSwitchLoss`, `GenLimit.PatientMachine.settledThreshold`, `GenLimit.PatientMachine.stableDecision`, `GenLimit.PatientMachine.survivingCriticalIndices`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.Support.greatestCandidateWithFallback`, `GenLimit.Support.leastCandidateWithFallback`, `GenLimit.sample`, `_private.GenLimit.Paper39_DenseGeneration.Patient.Charging.0.GenLimit.PatientMachine.settledStableTargetRun`.

### T25: `GenLimit.PatientScope.TargetSwitchChargingCertificate.prefixCount_le_log2_targetCount`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Abstract.TargetSwitchCharging:62`. Input anchor: `declarations.jsonl` record 144, duplicated in `01-target-statements.md`.

```lean
∀ {target switchLoss : Set.{0} Nat} (Q : GenLimit.PatientScope.TargetSwitchChargingCertificate target switchLoss)
  (n : Nat),
  @LE.le.{0} Nat instLENat (GenLimit.PatientScope.prefixCount switchLoss n)
    (GenLimit.PatientScope.prefixCount target n).log2
```

**Reconstruction.** For any semantic target and switchLoss sets, any supplied TargetSwitchChargingCertificate Q and every natural cutoff n, the number of switchLoss values below n is at most Nat.log2 of the number of target values below n. Q supplies switchLoss subset target, a tau label positive and injective on switchLoss, and for every loss value ell a finite charge with at least 2^(tau ell) elements, all in target and strictly below ell.

**Quantifier skeleton and dependencies.** forall {target,switchLoss:Set Nat}, (Q:TargetSwitchChargingCertificate target switchLoss), n:Nat; prefixCount(switchLoss,n)<=Nat.log2(prefixCount(target,n)). No infinitude assumption.

**Information available.** Q is input evidence, not inferred merely from naming a set switchLoss. The prefix is the ambient numeric interval [0,n), rather than the first n target ranks.

**Edge cases.** n=0 or zero target count forces loss count 0; standard Nat.log2(0)=0 and Nat.log2(1)=0 are in force. Empty losses allow vacuous certificate conditions. No algorithm producing Q or computational complexity is asserted.

**Algorithm scope.** This is a predicate/set/counting statement, not a construction of an executable learner. All quantified languages are semantic subsets of Nat unless an OracleFamily is explicitly present.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.PatientScope.prefixCount`, `GenLimit.PatientScope.prefixFinset`.

### T26: `GenLimit.PatientScope.relativeLowerDensity`

Kind: definition. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity:24`. Input anchor: `declarations.jsonl` record 148, duplicated in `01-target-statements.md`.

```lean
GenLimit.Language → (K : GenLimit.Language) → @Set.Infinite.{0} Nat K → Real
```

Exact definition value:

```lean
fun A K hK => (GenLimit.KleinbergWei.OrderedLanguage.increasing K hK).lowerDensity A
```

**Reconstruction.** Given arbitrary A subset Nat, infinite K subset Nat and proof hK of infinitude, form the OrderedLanguage whose enumeration is Nat.nth of membership in K. For each n, count indices i<n for which the i-th increasing element of K lies in A. Use ratio 0 at n=0 and the real count/n otherwise. relativeLowerDensity A K hK is the Filter.liminf of these ratios as n tends to infinity.

**Quantifier skeleton and dependencies.** forall A:Language, (K:Language), (hK:Set.Infinite K), result:Real. A need not be a subset of K. Enumeration is fixed by K, not by an arbitrary presentation stream.

**Information available.** Full semantic sets A,K and an infinitude proof; no finite data learner, distribution or membership-oracle computation is specified.

**Edge cases.** Finite or empty K has no admissible hK. A may be empty, disjoint, or all of K. The numerator counts distinct target elements through injective enumeration. No convergence of ratios is demanded; the selected quantity is a liminf.

**Algorithm scope.** This is a predicate/set/counting statement, not a construction of an executable learner. All quantified languages are semantic subsets of Nat unless an OracleFamily is explicitly present.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.KleinbergWei.OrderedLanguage.enumeration`, `GenLimit.KleinbergWei.OrderedLanguage.increasing`, `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`, `GenLimit.KleinbergWei.OrderedLanguage.prefixCount`, `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio`, `GenLimit.Language`, `GenLimit.PatientScope.relativeLowerDensity`.

### T27: `GenLimit.RecursiveCritical`

Kind: definition. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Critical:20`. Input anchor: `declarations.jsonl` record 150, duplicated in `01-target-statements.md`.

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Prop
```

Exact definition value:

```lean
fun C stream t =>
  @WellFounded.fix.{1, 1} Nat (fun a => Prop)
    (@invImage.{1, 1} Nat Nat (fun x => x) (@sizeOfWFRel.{1} Nat instSizeOfNat)).1 GenLimit.RecursiveCritical._proof_1
    fun a a_1 =>
    GenLimit.RecursiveCritical.match_1.{1}
      (fun x =>
        ((y : Nat) → (@invImage.{1, 1} Nat Nat (fun x => x) (@sizeOfWFRel.{1} Nat instSizeOfNat)).1 y x → Prop) → Prop)
      a (fun a x => GenLimit.Consistent C stream t (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (fun n x =>
        And
          (GenLimit.Consistent C stream t
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (∀ (j : Nat) (a : @LE.le.{0} Nat instLENat j n),
            x j ⋯ →
              @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat)
                (C
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (C j)))
      a_1
```

**Reconstruction.** At index 0, RecursiveCritical C stream t 0 is Consistent C stream t 0. At index n+1 it means consistency of C(n+1), together with C(n+1) subset C(j) for every j<=n that is recursively critical at the same time t. The recursion is on the candidate index, and compares complete language sets; it does not require containment in every consistent earlier language.

**Quantifier skeleton and dependencies.** forall C,stream,t; RC(t,0)=Consistent(t,0); forall n, RC(t,n+1) iff Consistent(t,n+1) and forall j<=n, RC(t,j) -> C(n+1) subset C(j).

**Information available.** C and a finite observed prefix enter consistency, while full semantic language containment enters the recursive comparison.

**Edge cases.** The universal clause is empty at index 0. At t=0 all candidates are consistent, but higher recursive criticality still depends on inclusions. No relation to Critical is asserted by this definition alone.

**Algorithm scope.** This is a predicate/set/counting statement, not a construction of an executable learner. All quantified languages are semantic subsets of Nat unless an OracleFamily is explicitly present.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.sample`.

### T28: `GenLimit.fixed_scope_one_step`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Dynamics:143`. Input anchor: `declarations.jsonl` record 157, duplicated in `01-target-statements.md`.

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {t s f : Nat},
  GenLimit.IsFocus C stream t s f →
    GenLimit.Consistent C stream
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        f →
      And
        (∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i s →
            Iff
              (GenLimit.RecursiveCritical C stream
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i)
              (GenLimit.RecursiveCritical C stream t i))
        (GenLimit.IsFocus C stream
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          s f)
```

**Reconstruction.** Suppose f is the largest recursively critical index strictly below s at time t, and C(f) remains consistent after also observing stream(t). Then for every i<s, recursive criticality at t+1 is equivalent to criticality at t, and the same f remains the largest critical index below the same s at t+1. Both the pointwise equivalence and the focus conclusion are asserted.

**Quantifier skeleton and dependencies.** forall {C,stream,t,s,f}; IsFocus(t,s,f) -> Consistent(t+1,f) -> ((forall i, i<s -> (RC(t+1,i) iff RC(t,i))) and IsFocus(t+1,s,f)). IsFocus includes f<s, RC(t,f), and forall j<s, RC(t,j)->j<=f.

**Information available.** A fixed scope and focus are hypotheses; no machine state or bound on how they are obtained is required.

**Edge cases.** s=0 cannot satisfy IsFocus. The equivalence is only below s, not at s or beyond. No conclusion across more than one step without iteration.

**Algorithm scope.** This is a predicate/set/counting statement, not a construction of an executable learner. All quantified languages are semantic subsets of Nat unless an OracleFamily is explicitly present.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.IsFocus`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.sample`.

### T29: `GenLimit.lost_recursiveCritical_suffix`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Dynamics:168`. Input anchor: `declarations.jsonl` record 158, duplicated in `01-target-statements.md`.

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {t u i j : Nat},
  @LE.le.{0} Nat instLENat t u →
    @LE.le.{0} Nat instLENat i j →
      GenLimit.RecursiveCritical C stream t i →
        GenLimit.RecursiveCritical C stream t j →
          Not (GenLimit.RecursiveCritical C stream u i) → Not (GenLimit.RecursiveCritical C stream u j)
```

**Reconstruction.** Between times t<=u, if i<=j were both recursively critical at t and i is not recursively critical at u, then j is not recursively critical at u either.

**Quantifier skeleton and dependencies.** forall {C,stream,t,u,i,j}; t<=u -> i<=j -> RC(t,i) -> RC(t,j) -> not RC(u,i) -> not RC(u,j).

**Information available.** Only the family, stream and indicated time/index comparisons are involved.

**Edge cases.** Only j that was critical at t is covered; it says nothing about all larger indices. i=j is allowed. t=u makes the loss premise incompatible with RC(t,i).

**Algorithm scope.** This is a predicate/set/counting statement, not a construction of an executable learner. All quantified languages are semantic subsets of Nat unless an OracleFamily is explicitly present.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.sample`.

### T30: `GenLimit.new_recursiveCritical_above_survivor`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Dynamics:183`. Input anchor: `declarations.jsonl` record 159, duplicated in `01-target-statements.md`.

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {t u i j : Nat},
  @LE.le.{0} Nat instLENat t u →
    GenLimit.RecursiveCritical C stream u i →
      Not (GenLimit.RecursiveCritical C stream t i) →
        GenLimit.RecursiveCritical C stream t j → GenLimit.RecursiveCritical C stream u j → @LT.lt.{0} Nat instLTNat j i
```

**Reconstruction.** If t<=u, i is critical at u but was not at t, and j is critical at both t and u, then j<i. Thus each surviving old critical index lies strictly below the newly critical i.

**Quantifier skeleton and dependencies.** forall {C,stream,t,u,i,j}; t<=u -> RC(u,i) -> not RC(t,i) -> RC(t,j) -> RC(u,j) -> j<i.

**Information available.** No existence of a newcomer or survivor is asserted; each is supplied as a hypothesis.

**Edge cases.** The hypotheses rule out i=j and t=u. There is no numerical bound on i or duration u-t.

**Algorithm scope.** This is a predicate/set/counting statement, not a construction of an executable learner. All quantified languages are semantic subsets of Nat unless an OracleFamily is explicitly present.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.sample`.

### T31: `GenLimit.recursiveCritical_subset_of_le`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Critical:38`. Input anchor: `declarations.jsonl` record 161, duplicated in `01-target-statements.md`.

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {t i j : Nat},
  @LE.le.{0} Nat instLENat i j →
    GenLimit.RecursiveCritical C stream t i →
      GenLimit.RecursiveCritical C stream t j →
        @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) (C j) (C i)
```

**Reconstruction.** For any fixed family, stream and time, if i<=j and both indices are recursively critical, then C(j) is a subset of C(i).

**Quantifier skeleton and dependencies.** forall {C,stream,t,i,j}; i<=j -> RC(t,i) -> RC(t,j) -> C(j) subset C(i). All implicit binders are universal.

**Information available.** This is a relation among two supplied criticality hypotheses; it gives no learner or witness search.

**Edge cases.** Allows i=j, giving reflexive inclusion; allows t=0 and arbitrary finite or empty languages.

**Algorithm scope.** This is a predicate/set/counting statement, not a construction of an executable learner. All quantified languages are semantic subsets of Nat unless an OracleFamily is explicitly present.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.sample`.

### T32: `GenLimit.target_eventually_recursiveCritical`

Kind: theorem. Exact source anchor: `GenLimit.Paper39_DenseGeneration.Critical:56`. Input anchor: `declarations.jsonl` record 163, duplicated in `01-target-statements.md`.

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {z : Nat},
  GenLimit.Presents stream (C z) →
    ∃ T, ∀ (t : Nat), @LE.le.{0} Nat instLENat T t → GenLimit.RecursiveCritical C stream t z
```

**Reconstruction.** If the range of stream equals C(z), there exists a time T after which z is recursively critical at every time t>=T.

**Quantifier skeleton and dependencies.** forall {C,stream,z}; Presents(stream,C(z)) -> exists T:Nat, forall t:Nat, T<=t -> RC(t,z). T may depend on C,stream,z and the presentation hypothesis.

**Information available.** z is an analysis parameter, not a supplied algorithm. Presentation means exact set equality of the range, with no speed or no-repetition condition.

**Edge cases.** No infinitude assumption and no rate for T. C(z) must be nonempty because stream is total on Nat; finite targets and repeated announcements are permitted.

**Algorithm scope.** This is a predicate/set/counting statement, not a construction of an executable learner. All quantified languages are semantic subsets of Nat unless an OracleFamily is explicitly present.

**Limits.** Reconstruction from exported types and definition values only. No proof correctness, fresh compilation, source correspondence, runtime, or effective computability is certified. Repeated stream values and repeated/equal family languages are not excluded.

**Definitions reviewed in the supplied recursive closure.** `GenLimit.Consistent`, `GenLimit.Language`, `GenLimit.LanguageFamily`, `GenLimit.Presents`, `GenLimit.RecursiveCritical`, `GenLimit.RecursiveCritical.match_1`, `GenLimit.sample`.

## Exhaustive slot coverage

A repeated endpoint points to the same dossier; repetition is not independent source correspondence. “No supplied reconstruction target” records the exact endpoint boundary and is not a claim that the withheld source has no claim or that no other code counterpart exists. No slot contains a linked name reported absent from the frozen environment.

| Slot | Reviewed target dossiers | Status |
|---|---|---|
| C01 | T15, T23 | All supplied endpoints reconstructed |
| C02 | T26 | All supplied endpoints reconstructed |
| C03 | None | No supplied reconstruction target |
| C04 | T27 | All supplied endpoints reconstructed |
| C05 | T01 | All supplied endpoints reconstructed |
| C06 | T16, T18 | All supplied endpoints reconstructed |
| C07 | None | No supplied reconstruction target |
| C08 | T19, T20, T21, T22 | All supplied endpoints reconstructed |
| C09 | None | No supplied reconstruction target |
| C10 | T24, T25 | All supplied endpoints reconstructed |
| C11 | None | No supplied reconstruction target |
| C12 | T17 | All supplied endpoints reconstructed |
| C13 | None | No supplied reconstruction target |
| C14 | T05, T06, T07 | All supplied endpoints reconstructed |
| C15 | None | No supplied reconstruction target |
| C16 | T08 | All supplied endpoints reconstructed |
| C17 | None | No supplied reconstruction target |
| C18 | T09 | All supplied endpoints reconstructed |
| C19 | None | No supplied reconstruction target |
| C20 | None | No supplied reconstruction target |
| C21 | None | No supplied reconstruction target |
| C22 | None | No supplied reconstruction target |
| C23 | None | No supplied reconstruction target |
| C24 | T15, T23 | All supplied endpoints reconstructed |
| C25 | T26 | All supplied endpoints reconstructed |
| C26 | None | No supplied reconstruction target |
| C27 | T27 | All supplied endpoints reconstructed |
| C28 | T29, T30, T31 | All supplied endpoints reconstructed |
| C29 | T32 | All supplied endpoints reconstructed |
| C30 | T28 | All supplied endpoints reconstructed |
| C31 | T12 | All supplied endpoints reconstructed |
| C32 | T16 | All supplied endpoints reconstructed |
| C33 | T13 | All supplied endpoints reconstructed |
| C34 | T14 | All supplied endpoints reconstructed |
| C35 | T02, T16 | All supplied endpoints reconstructed |
| C36 | None | No supplied reconstruction target |
| C37 | None | No supplied reconstruction target |
| C38 | T04 | All supplied endpoints reconstructed |
| C39 | T08 | All supplied endpoints reconstructed |
| C40 | T03, T10, T11 | All supplied endpoints reconstructed |
| C41 | None | No supplied reconstruction target |
| C42 | None | No supplied reconstruction target |
| C43 | None | No supplied reconstruction target |
| C44 | None | No supplied reconstruction target |

## Selected native helper types actually inspected

The native census was inventoried as code-only supporting evidence. The following exact helper types were individually inspected to settle recursion equations, output access/selection, and selected closure-code goodness. They are not extra target slots. Their proof bodies were neither available nor checked. Other closure helper types are retained in the next appendix; the census as a whole is not represented as an individual review of every helper.

### `GenLimit.PatientMachine.available_exists`

`GenLimit.Paper39_DenseGeneration.Patient.Machine:329`

```lean
∀ (C : GenLimit.LanguageFamily),
  (∀ (i : Nat), @Set.Infinite.{0} Nat (C i)) →
    ∀ (stream : Nat → Nat) (t : Nat) (used : Finset.{0} Nat) (focus : Nat),
      ∃ x, GenLimit.PatientMachine.Available C stream t used focus x
```

### `GenLimit.PatientMachine.leastAvailable_minimal`

`GenLimit.Paper39_DenseGeneration.Patient.Machine:354`

```lean
∀ (C : GenLimit.LanguageFamily) (hInfinite : ∀ (i : Nat), @Set.Infinite.{0} Nat (C i)) (stream : Nat → Nat) (t : Nat)
  (used : Finset.{0} Nat) (focus x : Nat),
  GenLimit.PatientMachine.Available C stream t used focus x →
    @LE.le.{0} Nat instLENat (GenLimit.PatientMachine.leastAvailable C hInfinite stream t used focus) x
```

### `GenLimit.PatientMachine.leastAvailable_spec`

`GenLimit.Paper39_DenseGeneration.Patient.Machine:346`

```lean
∀ (C : GenLimit.LanguageFamily) (hInfinite : ∀ (i : Nat), @Set.Infinite.{0} Nat (C i)) (stream : Nat → Nat) (t : Nat)
  (used : Finset.{0} Nat) (focus : Nat),
  GenLimit.PatientMachine.Available C stream t used focus
    (GenLimit.PatientMachine.leastAvailable C hInfinite stream t used focus)
```

### `GenLimit.PatientMachine.output_available_post_focus`

`GenLimit.Paper39_DenseGeneration.Patient.Output:14`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (t : Nat),
  GenLimit.PatientMachine.Available O.language stream
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (GenLimit.PatientMachine.run O stream t).used
    (GenLimit.PatientMachine.run O stream
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).focus
    (GenLimit.PatientMachine.output O stream t)
```

### `GenLimit.PatientMachine.output_eq_leastAvailable`

`GenLimit.Paper39_DenseGeneration.Patient.Machine:411`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (t : Nat),
  @Eq.{1} Nat (GenLimit.PatientMachine.output O stream t)
    (GenLimit.PatientMachine.leastAvailable O.language ⋯ stream
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (GenLimit.PatientMachine.run O stream t).used
      (GenLimit.PatientMachine.decide O.language stream t (GenLimit.PatientMachine.run O stream t)).focus)
```

### `GenLimit.PatientMachine.output_mem_run_succ_focus`

`GenLimit.Paper39_DenseGeneration.Patient.Validity:34`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (t : Nat),
  @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
    (O.language
      (GenLimit.PatientMachine.run O stream
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).focus)
    (GenLimit.PatientMachine.output O stream t)
```

### `GenLimit.PatientMachine.run_focus_isFocus`

`GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant:475`

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {z : Nat},
  GenLimit.Presents stream (O.language z) →
    ∀ (t : Nat),
      GenLimit.IsFocus O.language stream t (GenLimit.PatientMachine.run O stream t).scope
        (GenLimit.PatientMachine.run O stream t).focus
```

### `GenLimit.PatientMachine.run_focus_isFocus_of_onModel`

`GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant:452`

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat},
  GenLimit.PatientMachine.OnModel O stream →
    ∀ (t : Nat),
      GenLimit.IsFocus O.language stream t (GenLimit.PatientMachine.run O stream t).scope
        (GenLimit.PatientMachine.run O stream t).focus
```

### `GenLimit.PatientMachine.run_succ`

`GenLimit.Paper39_DenseGeneration.Patient.Machine:397`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (t : Nat),
  @Eq.{1} GenLimit.PatientMachine.State
    (GenLimit.PatientMachine.run O stream
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (GenLimit.PatientMachine.processRound O stream t (GenLimit.PatientMachine.run O stream t))
```

### `GenLimit.PatientMachine.run_zero`

`GenLimit.Paper39_DenseGeneration.Patient.Machine:392`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat),
  @Eq.{1} GenLimit.PatientMachine.State
    (GenLimit.PatientMachine.run O stream (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    GenLimit.PatientMachine.initialState
```

### `GenLimit.PartialEnumeration.closureCode_good`

`GenLimit.Paper39_DenseGeneration.Partial.Closure:99`

```lean
∀ (O : GenLimit.OracleFamily) (n : Nat),
  GenLimit.PartialEnumeration.GoodCode O (GenLimit.PartialEnumeration.closureCode O n)
```

## Supplied recursive closure: exact supporting evidence

This appendix records all 166 exported declarations, including targets and generated/private helpers. Definition values and constructor types specify the necessary semantic content. Theorem entries contain types only. `source_line=null` is represented as `None` and means the export did not give a line for that generated declaration. Pretty-printer `⋯` suppresses embedded proof terms; it is not a reported hole. This appendix is an exact evidence ledger; the semantic analysis is the glossary and target dossiers, not an assertion that every theorem in the native census was independently audited.

### `GenLimit.AdversaryFirst`

definition; `GenLimit.Support.TurnTaking.Announcements:19`

```lean
(Nat → Nat) → (Nat → Nat) → Set.{0} Nat
```

```lean
fun adversary generator =>
  @setOf.{0} Nat fun x =>
    ∃ t, And (@Eq.{1} Nat (adversary t) x) (∀ (s : Nat), @LT.lt.{0} Nat instLTNat s t → @Ne.{1} Nat (generator s) x)
```

### `GenLimit.Consistent`

definition; `GenLimit.Core.Basic:34`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Prop
```

```lean
fun C stream t i =>
  @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat)
    (@Finset.toSet.{0} Nat (GenLimit.sample stream t)) (C i)
```

### `GenLimit.Critical`

definition; `GenLimit.Paper01_LanguageGeneration.Critical:16`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Prop
```

```lean
fun C stream t n =>
  And (GenLimit.Consistent C stream t n)
    (∀ (i : Nat),
      @LE.le.{0} Nat instLENat i n →
        GenLimit.Consistent C stream t i →
          @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) (C n) (C i))
```

### `GenLimit.DenseGeneration.Results.theorem_3_15`

theorem; `GenLimit.Paper39_DenseGeneration.Results.Overview:27`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {z : Nat},
  GenLimit.Presents stream (O.language z) →
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
      (GenLimit.PatientMachine.patientLowerDensity O stream z)
```

### `GenLimit.DenseGeneration.Results.theorem_B_3`

theorem; `GenLimit.Paper39_DenseGeneration.Results.Overview:36`

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  GenLimit.Presents stream E →
    @Set.Infinite.{0} Nat E →
      @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) E (O.language z) →
        ∀ (α : Real),
          @Eq.{1} Real (GenLimit.PatientScope.relativeLowerDensity E (O.language z) ⋯) α →
            @LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) α
                (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
              (GenLimit.PartialEnumeration.partialPatientLowerDensity O stream z)
```

### `GenLimit.GeneratorFirst`

definition; `GenLimit.Support.TurnTaking.Announcements:24`

```lean
(Nat → Nat) → (Nat → Nat) → Set.{0} Nat
```

```lean
fun adversary generator =>
  @setOf.{0} Nat fun x =>
    ∃ t, And (@Eq.{1} Nat (generator t) x) (∀ (s : Nat), @LE.le.{0} Nat instLENat s t → @Ne.{1} Nat (adversary s) x)
```

### `GenLimit.IsFocus`

definition; `GenLimit.Paper39_DenseGeneration.Critical:75`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Nat → Prop
```

```lean
fun C stream t s f =>
  And (@LT.lt.{0} Nat instLTNat f s)
    (And (GenLimit.RecursiveCritical C stream t f)
      (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat j s → GenLimit.RecursiveCritical C stream t j → @LE.le.{0} Nat instLENat j f))
```

### `GenLimit.KleinbergWei.OrderedLanguage`

inductive; `GenLimit.Core.OrderedDensity:24`

```lean
Type
```

Constructors: `GenLimit.KleinbergWei.OrderedLanguage.mk`.

### `GenLimit.KleinbergWei.OrderedLanguage.enumeration`

definition; `GenLimit.Core.OrderedDensity:26`

```lean
GenLimit.KleinbergWei.OrderedLanguage → Nat → Nat
```

```lean
fun self => self.2
```

### `GenLimit.KleinbergWei.OrderedLanguage.increasing`

definition; `GenLimit.Core.NaturalDensity:19`

```lean
(K : GenLimit.Language) → @Set.Infinite.{0} Nat K → GenLimit.KleinbergWei.OrderedLanguage
```

```lean
fun K hK =>
  { carrier := K,
    enumeration := Nat.nth fun x => @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) K x,
    enumeration_injective := ⋯, range_enumeration := ⋯ }
```

### `GenLimit.KleinbergWei.OrderedLanguage.increasing._proof_1`

theorem; `GenLimit.Core.NaturalDensity:None`

```lean
∀ (K : GenLimit.Language),
  @Set.Infinite.{0} Nat K →
    @Function.Injective.{1, 1} Nat Nat
      (Nat.nth fun x => @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) K x)
```

### `GenLimit.KleinbergWei.OrderedLanguage.increasing._proof_2`

theorem; `GenLimit.Core.NaturalDensity:None`

```lean
∀ (K : GenLimit.Language),
  @Set.Infinite.{0} Nat K →
    @Eq.{1} (Set.{0} Nat)
      (@Set.range.{0, 1} Nat Nat
        (Nat.nth fun x => @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) K x))
      (@setOf.{0} Nat fun x => @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) K x)
```

### `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`

definition; `GenLimit.Core.OrderedDensity:237`

```lean
GenLimit.KleinbergWei.OrderedLanguage → GenLimit.Language → Real
```

```lean
fun K A =>
  @Filter.liminf.{0, 0} Real Nat
    (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Real
      Real.instConditionallyCompleteLinearOrder)
    (K.prefixRatio A) (@Filter.atTop.{0} Nat Nat.instPreorder)
```

### `GenLimit.KleinbergWei.OrderedLanguage.mk`

constructor; `GenLimit.Core.OrderedDensity:24`

```lean
(carrier : GenLimit.Language) →
  (enumeration : Nat → Nat) →
    @Function.Injective.{1, 1} Nat Nat enumeration →
      @Eq.{1} (Set.{0} Nat) (@Set.range.{0, 1} Nat Nat enumeration) carrier → GenLimit.KleinbergWei.OrderedLanguage
```

### `GenLimit.KleinbergWei.OrderedLanguage.prefixCount`

definition; `GenLimit.Core.OrderedDensity:33`

```lean
GenLimit.KleinbergWei.OrderedLanguage → GenLimit.Language → Nat → Nat
```

```lean
fun K A n =>
  @Finset.card.{0} Nat
    ({i ∈ Finset.range n |
      @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) A (K.enumeration i)})
```

### `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio`

definition; `GenLimit.Core.OrderedDensity:197`

```lean
GenLimit.KleinbergWei.OrderedLanguage → GenLimit.Language → Nat → Real
```

```lean
fun K A n =>
  @ite.{1} Real (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (instDecidableEqNat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (K.prefixCount A n)) (@Nat.cast.{0} Real Real.instNatCast n))
```

### `GenLimit.Language`

definition; `GenLimit.Core.Basic:20`

```lean
Type
```

```lean
Set.{0} Nat
```

### `GenLimit.LanguageFamily`

definition; `GenLimit.Core.Basic:23`

```lean
Type
```

```lean
Nat → GenLimit.Language
```

### `GenLimit.OracleFamily`

inductive; `GenLimit.Core.OracleFamily:17`

```lean
Type
```

Constructors: `GenLimit.OracleFamily.mk`.

### `GenLimit.OracleFamily.infinite'`

theorem; `GenLimit.Core.OracleFamily:19`

```lean
∀ (self : GenLimit.OracleFamily) (i : Nat), @Set.Infinite.{0} Nat (self.language i)
```

### `GenLimit.OracleFamily.language`

definition; `GenLimit.Core.OracleFamily:18`

```lean
GenLimit.OracleFamily → GenLimit.LanguageFamily
```

```lean
fun self => self.1
```

### `GenLimit.OracleFamily.mk`

constructor; `GenLimit.Core.OracleFamily:17`

```lean
(language : GenLimit.LanguageFamily) →
  (∀ (i : Nat), @Set.Infinite.{0} Nat (language i)) →
    (query : Nat → Nat → Bool) →
      (∀ (i u : Nat),
          Iff (@Eq.{1} Bool (query i u) Bool.true)
            (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (language i) u)) →
        GenLimit.OracleFamily
```

### `GenLimit.OracleFamily.query`

definition; `GenLimit.Core.OracleFamily:20`

```lean
GenLimit.OracleFamily → Nat → Nat → Bool
```

```lean
fun self => self.3
```

### `GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:68`

```lean
GenLimit.Language
```

```lean
@Set.range.{0, 1} Nat Nat GenLimit.PartialEnumeration.Counterexample.stream
```

### `GenLimit.PartialEnumeration.Counterexample.example_B_1`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.ExampleB1:35`

```lean
And
  (GenLimit.Presents GenLimit.PartialEnumeration.Counterexample.stream
    GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage)
  (And (@Set.Infinite.{0} Nat GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage)
    (And
      (@HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat)
        GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage
        GenLimit.PartialEnumeration.Counterexample.trueLanguage)
      (And
        (∀ (t : Nat),
          @Eq.{1} Nat
            (GenLimit.PatientMachine.output GenLimit.PartialEnumeration.Counterexample.oracle
              GenLimit.PartialEnumeration.Counterexample.stream t)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (And
          (Not
            (∃ T,
              ∀ (t : Nat),
                @LE.le.{0} Nat instLENat T t →
                  @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
                    GenLimit.PartialEnumeration.Counterexample.trueLanguage
                    (GenLimit.PatientMachine.output GenLimit.PartialEnumeration.Counterexample.oracle
                      GenLimit.PartialEnumeration.Counterexample.stream t)))
          (@Eq.{1} Real
            (GenLimit.PatientMachine.patientLowerDensity GenLimit.PartialEnumeration.Counterexample.oracle
              GenLimit.PartialEnumeration.Counterexample.stream
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))))
```

### `GenLimit.PartialEnumeration.Counterexample.family`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:31`

```lean
GenLimit.LanguageFamily
```

```lean
fun x =>
  GenLimit.PartialEnumeration.Counterexample.family.match_1.{1} (fun x => GenLimit.Language) x
    (fun _ => GenLimit.PartialEnumeration.Counterexample.firstLanguage) fun i =>
    @setOf.{0} Nat fun x =>
      ∃ j,
        And
          (@LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            j)
          (@Eq.{1} Nat x
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))
```

### `GenLimit.PartialEnumeration.Counterexample.family.match_1`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:None`

```lean
(motive : Nat → Sort u_1) →
  (x : Nat) →
    (Unit → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      ((i : Nat) → motive i.succ) → motive x
```

```lean
fun motive x h_1 h_2 => @Nat.casesOn.{u_1} (fun x => motive x) x (h_1 Unit.unit) fun n => h_2 n
```

### `GenLimit.PartialEnumeration.Counterexample.family_infinite`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:35`

```lean
∀ (i : Nat), @Set.Infinite.{0} Nat (GenLimit.PartialEnumeration.Counterexample.family i)
```

### `GenLimit.PartialEnumeration.Counterexample.firstLanguage`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:27`

```lean
GenLimit.Language
```

```lean
@setOf.{0} Nat fun x =>
  Or
    (@Eq.{1} Nat
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) x
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (And (@Ne.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) x
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
```

### `GenLimit.PartialEnumeration.Counterexample.oracle`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:52`

```lean
GenLimit.OracleFamily
```

```lean
{ language := GenLimit.PartialEnumeration.Counterexample.family,
  infinite' := GenLimit.PartialEnumeration.Counterexample.family_infinite,
  query := fun i x =>
    @ite.{1} Bool
      (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
        (GenLimit.PartialEnumeration.Counterexample.family i) x)
      (Classical.propDecidable
        (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
          (GenLimit.PartialEnumeration.Counterexample.family i) x))
      Bool.true Bool.false,
  query_spec := GenLimit.PartialEnumeration.Counterexample.oracle._proof_1 }
```

### `GenLimit.PartialEnumeration.Counterexample.oracle._proof_1`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:None`

```lean
∀ (i x : Nat),
  Iff
    (@Eq.{1} Bool
      (@ite.{1} Bool
        (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
          (GenLimit.PartialEnumeration.Counterexample.family i) x)
        (Classical.propDecidable
          (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
            (GenLimit.PartialEnumeration.Counterexample.family i) x))
        Bool.true Bool.false)
      Bool.true)
    (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
      (GenLimit.PartialEnumeration.Counterexample.family i) x)
```

### `GenLimit.PartialEnumeration.Counterexample.output_eq_odd`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:183`

```lean
∀ (t : Nat),
  @Eq.{1} Nat
    (GenLimit.PatientMachine.output GenLimit.PartialEnumeration.Counterexample.oracle
      GenLimit.PartialEnumeration.Counterexample.stream t)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### `GenLimit.PartialEnumeration.Counterexample.output_not_mem_trueLanguage`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:247`

```lean
∀ (t : Nat),
  GenLimit.PatientMachine.output GenLimit.PartialEnumeration.Counterexample.oracle
      GenLimit.PartialEnumeration.Counterexample.stream t ∉
    GenLimit.PartialEnumeration.Counterexample.trueLanguage
```

### `GenLimit.PartialEnumeration.Counterexample.presents_enumeratedLanguage`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:93`

```lean
GenLimit.Presents GenLimit.PartialEnumeration.Counterexample.stream
  GenLimit.PartialEnumeration.Counterexample.enumeratedLanguage
```

### `GenLimit.PartialEnumeration.Counterexample.stream`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:62`

```lean
Nat → Nat
```

```lean
fun t =>
  @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### `GenLimit.PartialEnumeration.Counterexample.trueLanguage`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Counterexample:65`

```lean
GenLimit.Language
```

```lean
GenLimit.PartialEnumeration.Counterexample.family (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
```

### `GenLimit.PartialEnumeration.GoodCode`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Closure:70`

```lean
GenLimit.OracleFamily → Nat → Prop
```

```lean
fun O q =>
  And (@Ne.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@Set.Infinite.{0} Nat (GenLimit.PartialEnumeration.codedIntersection O.language q))
```

### `GenLimit.PartialEnumeration.closure`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Closure:125`

```lean
GenLimit.OracleFamily → GenLimit.OracleFamily
```

```lean
fun O =>
  {
    language := fun n =>
      GenLimit.PartialEnumeration.codedIntersection O.language (GenLimit.PartialEnumeration.closureCode O n),
    infinite' := ⋯,
    query := fun n x => @List.all.{0} Nat (GenLimit.PartialEnumeration.closureCode O n).bitIndices fun i => O.query i x,
    query_spec := ⋯ }
```

### `GenLimit.PartialEnumeration.closure._proof_1`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Closure:None`

```lean
∀ (O : GenLimit.OracleFamily) (n : Nat),
  @Set.Infinite.{0} Nat
    (GenLimit.PartialEnumeration.codedIntersection O.language (GenLimit.PartialEnumeration.closureCode O n))
```

### `GenLimit.PartialEnumeration.closure._proof_2`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Closure:None`

```lean
∀ (O : GenLimit.OracleFamily) (n x : Nat),
  Iff
    (@Eq.{1} Bool (@List.all.{0} Nat (GenLimit.PartialEnumeration.closureCode O n).bitIndices fun i => O.query i x)
      Bool.true)
    (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
      (GenLimit.PartialEnumeration.codedIntersection O.language (GenLimit.PartialEnumeration.closureCode O n)) x)
```

### `GenLimit.PartialEnumeration.closureCode`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Closure:91`

```lean
GenLimit.OracleFamily → Nat → Nat
```

```lean
fun O n => Nat.nth (GenLimit.PartialEnumeration.GoodCode O) n
```

### `GenLimit.PartialEnumeration.codeSupport`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Closure:22`

```lean
Nat → Finset.{0} Nat
```

```lean
fun q =>
  @DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} Nat (Finset.{0} Nat)) Nat (fun x => Finset.{0} Nat)
    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} Nat (Finset.{0} Nat)) Nat (Finset.{0} Nat)
      (@Equiv.instEquivLike.{1, 1} Nat (Finset.{0} Nat)))
    Finset.equivBitIndices q
```

### `GenLimit.PartialEnumeration.codedIntersection`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Closure:26`

```lean
GenLimit.LanguageFamily → Nat → GenLimit.Language
```

```lean
fun C q =>
  @setOf.{0} Nat fun x =>
    ∀ (i : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
          (GenLimit.PartialEnumeration.codeSupport q) i →
        @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (C i) x
```

### `GenLimit.PartialEnumeration.lemma_B_2_generation`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Validity:47`

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  GenLimit.Presents stream E →
    @Set.Infinite.{0} Nat E →
      @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) E (O.language z) →
        ∃ T,
          ∀ (t : Nat),
            @LE.le.{0} Nat instLENat T t →
              And
                (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
                  (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t))
                (And
                  (∀ (s : Nat),
                    @LE.le.{0} Nat instLENat s t →
                      @Ne.{1} Nat (stream s)
                        (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t))
                  (∀ (s : Nat),
                    @LT.lt.{0} Nat instLTNat s t →
                      @Ne.{1} Nat (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream s)
                        (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t)))
```

### `GenLimit.PartialEnumeration.partialPatientLowerDensity`

definition; `GenLimit.Paper39_DenseGeneration.Partial.Main:23`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → Real
```

```lean
fun O stream z =>
  GenLimit.PatientScope.relativeLowerDensity
    (@Inter.inter.{0} GenLimit.Language (@Set.instInter.{0} Nat)
      (GenLimit.GeneratorFirst stream (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream))
      (O.language z))
    (O.language z) ⋯
```

### `GenLimit.PartialEnumeration.theorem_B_3`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Main:63`

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  GenLimit.Presents stream E →
    @Set.Infinite.{0} Nat E →
      @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) E (O.language z) →
        ∀ (α : Real),
          @Eq.{1} Real (GenLimit.PatientScope.relativeLowerDensity E (O.language z) ⋯) α →
            @LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) α
                (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
              (GenLimit.PartialEnumeration.partialPatientLowerDensity O stream z)
```

### `GenLimit.PartialEnumeration.theorem_B_3_lowerDensity`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Main:42`

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  GenLimit.Presents stream E →
    @Set.Infinite.{0} Nat E →
      @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) E (O.language z) →
        @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
            (GenLimit.PatientScope.relativeLowerDensity E (O.language z) ⋯))
          (GenLimit.PartialEnumeration.partialPatientLowerDensity O stream z)
```

### `GenLimit.PartialEnumeration.theorem_B_3_with_generation`

theorem; `GenLimit.Paper39_DenseGeneration.Partial.Main:78`

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {E : GenLimit.Language} {z : Nat},
  GenLimit.Presents stream E →
    @Set.Infinite.{0} Nat E →
      @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) E (O.language z) →
        And
          (∃ T,
            ∀ (t : Nat),
              @LE.le.{0} Nat instLENat T t →
                And
                  (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
                    (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t))
                  (And
                    (∀ (s : Nat),
                      @LE.le.{0} Nat instLENat s t →
                        @Ne.{1} Nat (stream s)
                          (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t))
                    (∀ (s : Nat),
                      @LT.lt.{0} Nat instLTNat s t →
                        @Ne.{1} Nat (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream s)
                          (GenLimit.PatientMachine.output (GenLimit.PartialEnumeration.closure O) stream t))))
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
              (GenLimit.PatientScope.relativeLowerDensity E (O.language z) ⋯))
            (GenLimit.PartialEnumeration.partialPatientLowerDensity O stream z))
```

### `GenLimit.PatientMachine.Available`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:324`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Finset.{0} Nat → Nat → Nat → Prop
```

```lean
fun C stream t used focus x =>
  And (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (C focus) x)
    (And (x ∉ GenLimit.sample stream t) (x ∉ used))
```

### `GenLimit.PatientMachine.Decision`

inductive; `GenLimit.Paper39_DenseGeneration.Patient.Machine:267`

```lean
Type
```

Constructors: `GenLimit.PatientMachine.Decision.mk`.

### `GenLimit.PatientMachine.Decision.focus`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:270`

```lean
GenLimit.PatientMachine.Decision → Nat
```

```lean
fun self => self.3
```

### `GenLimit.PatientMachine.Decision.mk`

constructor; `GenLimit.Paper39_DenseGeneration.Patient.Machine:267`

```lean
Nat → Nat → Nat → GenLimit.PatientMachine.MoveKind → GenLimit.PatientMachine.Decision
```

### `GenLimit.PatientMachine.Decision.move`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:271`

```lean
GenLimit.PatientMachine.Decision → GenLimit.PatientMachine.MoveKind
```

```lean
fun self => self.4
```

### `GenLimit.PatientMachine.Decision.scope`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:268`

```lean
GenLimit.PatientMachine.Decision → Nat
```

```lean
fun self => self.1
```

### `GenLimit.PatientMachine.Decision.tau`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:269`

```lean
GenLimit.PatientMachine.Decision → Nat
```

```lean
fun self => self.2
```

### `GenLimit.PatientMachine.MoveKind`

inductive; `GenLimit.Paper39_DenseGeneration.Patient.Machine:30`

```lean
Type
```

Constructors: `GenLimit.PatientMachine.MoveKind.initial`, `GenLimit.PatientMachine.MoveKind.stay`, `GenLimit.PatientMachine.MoveKind.expand`, `GenLimit.PatientMachine.MoveKind.backtrack`.

### `GenLimit.PatientMachine.MoveKind.backtrack`

constructor; `GenLimit.Paper39_DenseGeneration.Patient.Machine:34`

```lean
GenLimit.PatientMachine.MoveKind
```

### `GenLimit.PatientMachine.MoveKind.expand`

constructor; `GenLimit.Paper39_DenseGeneration.Patient.Machine:33`

```lean
GenLimit.PatientMachine.MoveKind
```

### `GenLimit.PatientMachine.MoveKind.initial`

constructor; `GenLimit.Paper39_DenseGeneration.Patient.Machine:31`

```lean
GenLimit.PatientMachine.MoveKind
```

### `GenLimit.PatientMachine.MoveKind.stay`

constructor; `GenLimit.Paper39_DenseGeneration.Patient.Machine:32`

```lean
GenLimit.PatientMachine.MoveKind
```

### `GenLimit.PatientMachine.OnModel`

definition; `GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant:447`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Prop
```

```lean
fun O stream => ∀ (t : Nat), ∃ i, GenLimit.Consistent O.language stream t i
```

### `GenLimit.PatientMachine.StableTargetRun`

inductive; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:20`

```lean
GenLimit.OracleFamily → (Nat → Nat) → GenLimit.Language → Type
```

Constructors: `GenLimit.PatientMachine.StableTargetRun.mk`.

### `GenLimit.PatientMachine.StableTargetRun.IsSwitchTime`

definition; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:47`

```lean
{O : GenLimit.OracleFamily} →
  {stream : Nat → Nat} → {K : GenLimit.Language} → GenLimit.PatientMachine.StableTargetRun O stream K → Nat → Nat → Prop
```

```lean
fun {O} {stream} {K} S x t =>
  And (@LT.lt.{0} Nat instLTNat (@GenLimit.PatientMachine.StableTargetRun.threshold O stream K S) t)
    (And (@Eq.{1} Nat (stream t) x)
      (And (x ∉ GenLimit.sample stream t) (GenLimit.PatientMachine.SwitchRound O stream t)))
```

### `GenLimit.PatientMachine.StableTargetRun.charge`

definition; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:148`

```lean
{O : GenLimit.OracleFamily} →
  {stream : Nat → Nat} →
    {K : GenLimit.Language} → GenLimit.PatientMachine.StableTargetRun O stream K → Nat → Finset.{0} Nat
```

```lean
fun {O} {stream} {K} S x =>
  @Finset.image.{0, 0} Nat Nat instDecidableEqNat
    (fun k =>
      GenLimit.PatientMachine.output O stream
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@GenLimit.PatientMachine.StableTargetRun.departure O stream K S x)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          k))
    (Finset.range
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@GenLimit.PatientMachine.StableTargetRun.tau O stream K S x)))
```

### `GenLimit.PatientMachine.StableTargetRun.charge_mem_target`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:201`

```lean
∀ {O : GenLimit.OracleFamily} {stream : Nat → Nat} {K : GenLimit.Language}
  (S : GenLimit.PatientMachine.StableTargetRun O stream K) {x y : Nat},
  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (GenLimit.PatientMachine.lateSwitchLoss O stream
        (@GenLimit.PatientMachine.StableTargetRun.threshold O stream K S))
      x →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
        (@GenLimit.PatientMachine.StableTargetRun.charge O stream K S x) y →
      @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) K y
```

### `GenLimit.PatientMachine.StableTargetRun.chargingCertificate`

definition; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:287`

```lean
{O : GenLimit.OracleFamily} →
  {stream : Nat → Nat} →
    {K : GenLimit.Language} →
      (S : GenLimit.PatientMachine.StableTargetRun O stream K) →
        GenLimit.PatientScope.TargetSwitchChargingCertificate K
          (GenLimit.PatientMachine.lateSwitchLoss O stream
            (@GenLimit.PatientMachine.StableTargetRun.threshold O stream K S))
```

```lean
fun {O} {stream} {K} S =>
  @GenLimit.PatientScope.TargetSwitchChargingCertificate.mk K
    (GenLimit.PatientMachine.lateSwitchLoss O stream (@GenLimit.PatientMachine.StableTargetRun.threshold O stream K S))
    (@GenLimit.PatientMachine.StableTargetRun.tau O stream K S)
    (@GenLimit.PatientMachine.StableTargetRun.charge O stream K S) ⋯ ⋯ ⋯ ⋯ ⋯ ⋯
```

### `GenLimit.PatientMachine.StableTargetRun.chargingCertificate._proof_1`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:None`

```lean
∀ {O : GenLimit.OracleFamily} {stream : Nat → Nat} {K : GenLimit.Language}
  (S : GenLimit.PatientMachine.StableTargetRun O stream K) ⦃x : Nat⦄,
  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (GenLimit.PatientMachine.lateSwitchLoss O stream
        (@GenLimit.PatientMachine.StableTargetRun.threshold O stream K S))
      x →
    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) K x
```

### `GenLimit.PatientMachine.StableTargetRun.chargingCertificate._proof_2`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:None`

```lean
∀ {O : GenLimit.OracleFamily} {stream : Nat → Nat} {K : GenLimit.Language}
  (S : GenLimit.PatientMachine.StableTargetRun O stream K) (x : Nat),
  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (GenLimit.PatientMachine.lateSwitchLoss O stream
        (@GenLimit.PatientMachine.StableTargetRun.threshold O stream K S))
      x →
    @LE.le.{0} Nat instLENat
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@GenLimit.PatientMachine.StableTargetRun.tau O stream K S x))
      (@Finset.card.{0} Nat (@GenLimit.PatientMachine.StableTargetRun.charge O stream K S x))
```

### `GenLimit.PatientMachine.StableTargetRun.chargingCertificate._proof_3`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:None`

```lean
∀ {O : GenLimit.OracleFamily} {stream : Nat → Nat} {K : GenLimit.Language}
  (S : GenLimit.PatientMachine.StableTargetRun O stream K) (x : Nat),
  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (GenLimit.PatientMachine.lateSwitchLoss O stream
        (@GenLimit.PatientMachine.StableTargetRun.threshold O stream K S))
      x →
    ∀ ⦃y : Nat⦄,
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
          (@GenLimit.PatientMachine.StableTargetRun.charge O stream K S x) y →
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat) (Finset.range x) y
```

### `GenLimit.PatientMachine.StableTargetRun.departure`

definition; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:142`

```lean
{O : GenLimit.OracleFamily} →
  {stream : Nat → Nat} → {K : GenLimit.Language} → GenLimit.PatientMachine.StableTargetRun O stream K → Nat → Nat
```

```lean
fun {O} {stream} {K} S x =>
  GenLimit.PatientMachine.latestDeparture O stream (@GenLimit.PatientMachine.StableTargetRun.switchTime O stream K S x)
    (@GenLimit.PatientMachine.StableTargetRun.landingFocus O stream K S x)
```

### `GenLimit.PatientMachine.StableTargetRun.landingFocus`

definition; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:65`

```lean
{O : GenLimit.OracleFamily} →
  {stream : Nat → Nat} → {K : GenLimit.Language} → GenLimit.PatientMachine.StableTargetRun O stream K → Nat → Nat
```

```lean
fun {O} {stream} {K} S x =>
  (GenLimit.PatientMachine.run O stream
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@GenLimit.PatientMachine.StableTargetRun.switchTime O stream K S x)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).focus
```

### `GenLimit.PatientMachine.StableTargetRun.mk`

constructor; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:20`

```lean
{O : GenLimit.OracleFamily} →
  {stream : Nat → Nat} →
    {K : GenLimit.Language} →
      (witness threshold : Nat) →
        GenLimit.PatientMachine.OnModel O stream →
          (∀ (t : Nat), @LE.le.{0} Nat instLENat threshold t → GenLimit.RecursiveCritical O.language stream t witness) →
            (∀ (t : Nat),
                @LE.le.{0} Nat instLENat threshold t →
                  @LT.lt.{0} Nat instLTNat witness (GenLimit.PatientMachine.run O stream t).scope) →
              @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) (O.language witness) K →
                (∀ (t : Nat), @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) K (stream t)) →
                  GenLimit.PatientMachine.StableTargetRun O stream K
```

### `GenLimit.PatientMachine.StableTargetRun.switchTime`

definition; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:51`

```lean
{O : GenLimit.OracleFamily} →
  {stream : Nat → Nat} → {K : GenLimit.Language} → GenLimit.PatientMachine.StableTargetRun O stream K → Nat → Nat
```

```lean
fun {O} {stream} {K} S x =>
  @dite.{1} Nat (∃ t, @GenLimit.PatientMachine.StableTargetRun.IsSwitchTime O stream K S x t)
    (Classical.propDecidable (∃ t, @GenLimit.PatientMachine.StableTargetRun.IsSwitchTime O stream K S x t))
    (fun h =>
      @Nat.find (@GenLimit.PatientMachine.StableTargetRun.IsSwitchTime O stream K S x)
        (fun a => Classical.propDecidable (@GenLimit.PatientMachine.StableTargetRun.IsSwitchTime O stream K S x a)) h)
    fun h => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))
```

### `GenLimit.PatientMachine.StableTargetRun.tau`

definition; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:145`

```lean
{O : GenLimit.OracleFamily} →
  {stream : Nat → Nat} → {K : GenLimit.Language} → GenLimit.PatientMachine.StableTargetRun O stream K → Nat → Nat
```

```lean
fun {O} {stream} {K} S x =>
  (GenLimit.PatientMachine.run O stream (@GenLimit.PatientMachine.StableTargetRun.departure O stream K S x)).tau
```

### `GenLimit.PatientMachine.StableTargetRun.tau_injective`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:164`

```lean
∀ {O : GenLimit.OracleFamily} {stream : Nat → Nat} {K : GenLimit.Language}
  (S : GenLimit.PatientMachine.StableTargetRun O stream K),
  @Set.InjOn.{0, 0} Nat Nat (@GenLimit.PatientMachine.StableTargetRun.tau O stream K S)
    (GenLimit.PatientMachine.lateSwitchLoss O stream (@GenLimit.PatientMachine.StableTargetRun.threshold O stream K S))
```

### `GenLimit.PatientMachine.StableTargetRun.tau_pos`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:160`

```lean
∀ {O : GenLimit.OracleFamily} {stream : Nat → Nat} {K : GenLimit.Language}
  (S : GenLimit.PatientMachine.StableTargetRun O stream K) {x : Nat},
  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (GenLimit.PatientMachine.lateSwitchLoss O stream
        (@GenLimit.PatientMachine.StableTargetRun.threshold O stream K S))
      x →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@GenLimit.PatientMachine.StableTargetRun.tau O stream K S x)
```

### `GenLimit.PatientMachine.StableTargetRun.threshold`

definition; `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging:23`

```lean
{O : GenLimit.OracleFamily} →
  {stream : Nat → Nat} → {K : GenLimit.Language} → GenLimit.PatientMachine.StableTargetRun O stream K → Nat
```

```lean
fun O stream K self => self.2
```

### `GenLimit.PatientMachine.State`

inductive; `GenLimit.Paper39_DenseGeneration.Patient.Machine:38`

```lean
Type
```

Constructors: `GenLimit.PatientMachine.State.mk`.

### `GenLimit.PatientMachine.State.age`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:44`

```lean
GenLimit.PatientMachine.State → Nat
```

```lean
fun self => self.3
```

### `GenLimit.PatientMachine.State.focus`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:46`

```lean
GenLimit.PatientMachine.State → Nat
```

```lean
fun self => self.4
```

### `GenLimit.PatientMachine.State.lastOutput`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:50`

```lean
GenLimit.PatientMachine.State → Option.{0} Nat
```

```lean
fun self => self.6
```

### `GenLimit.PatientMachine.State.mk`

constructor; `GenLimit.Paper39_DenseGeneration.Patient.Machine:38`

```lean
Nat →
  Nat → Nat → Nat → Finset.{0} Nat → Option.{0} Nat → GenLimit.PatientMachine.MoveKind → GenLimit.PatientMachine.State
```

### `GenLimit.PatientMachine.State.move`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:52`

```lean
GenLimit.PatientMachine.State → GenLimit.PatientMachine.MoveKind
```

```lean
fun self => self.7
```

### `GenLimit.PatientMachine.State.scope`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:40`

```lean
GenLimit.PatientMachine.State → Nat
```

```lean
fun self => self.1
```

### `GenLimit.PatientMachine.State.tau`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:42`

```lean
GenLimit.PatientMachine.State → Nat
```

```lean
fun self => self.2
```

### `GenLimit.PatientMachine.State.used`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:48`

```lean
GenLimit.PatientMachine.State → Finset.{0} Nat
```

```lean
fun self => self.5
```

### `GenLimit.PatientMachine.SwitchRound`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Pairing:40`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → Prop
```

```lean
fun O stream t => stream t ∉ O.language (GenLimit.PatientMachine.run O stream t).focus
```

### `GenLimit.PatientMachine.UpwardDeparture`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Departure:21`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → Nat → Prop
```

```lean
fun O stream i d =>
  And (@Eq.{1} Nat (GenLimit.PatientMachine.run O stream d).focus i)
    (And
      (@Eq.{1} GenLimit.PatientMachine.MoveKind
        (GenLimit.PatientMachine.run O stream
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).move
        GenLimit.PatientMachine.MoveKind.expand)
      (@LT.lt.{0} Nat instLTNat i
        (GenLimit.PatientMachine.run O stream
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).focus))
```

### `GenLimit.PatientMachine.available_exists`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Machine:329`

```lean
∀ (C : GenLimit.LanguageFamily),
  (∀ (i : Nat), @Set.Infinite.{0} Nat (C i)) →
    ∀ (stream : Nat → Nat) (t : Nat) (used : Finset.{0} Nat) (focus : Nat),
      ∃ x, GenLimit.PatientMachine.Available C stream t used focus x
```

### `GenLimit.PatientMachine.backtrackDecision`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:281`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → GenLimit.PatientMachine.State → GenLimit.PatientMachine.Decision
```

```lean
fun C stream t old =>
  have consistent :=
    GenLimit.PatientMachine.consistentIndices C stream
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      old.scope;
  @dite.{1} GenLimit.PatientMachine.Decision (@Finset.Nonempty.{0} Nat consistent)
    (@Finset.decidableNonempty.{0} Nat consistent)
    (fun hcon =>
      have survivors := GenLimit.PatientMachine.survivingCriticalIndices C stream t old.scope;
      have i :=
        @ite.{1} Nat (@Finset.Nonempty.{0} Nat survivors) (@Finset.decidableNonempty.{0} Nat survivors)
          (GenLimit.PatientMachine.highestSurvivor C stream t old.scope old.focus)
          (GenLimit.PatientMachine.lowestConsistentInScope C stream
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            old.scope old.focus);
      {
        scope :=
          @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        tau :=
          @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old.tau
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        focus := i, move := GenLimit.PatientMachine.MoveKind.backtrack })
    fun hcon =>
    have i :=
      GenLimit.PatientMachine.lowestConsistent C stream
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        old.focus;
    @dite.{1} GenLimit.PatientMachine.Decision
      (∃ j,
        GenLimit.Consistent C stream
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          j)
      (Classical.propDecidable
        (∃ j,
          GenLimit.Consistent C stream
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            j))
      (fun hall =>
        {
          scope :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
          tau :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old.tau
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
          focus := i, move := GenLimit.PatientMachine.MoveKind.backtrack })
      fun hall =>
      { scope := @Max.max.{0} Nat Nat.instMax old.scope (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        tau :=
          @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old.tau
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        focus := old.focus, move := GenLimit.PatientMachine.MoveKind.backtrack }
```

### `GenLimit.PatientMachine.consistentIndices`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:65`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Finset.{0} Nat
```

```lean
fun C stream t scope =>
  @Finset.filter.{0} Nat (GenLimit.Consistent C stream t)
    (fun a => Classical.propDecidable (GenLimit.Consistent C stream t a)) (Finset.range scope)
```

### `GenLimit.PatientMachine.criticalIndices`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:71`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Finset.{0} Nat
```

```lean
fun C stream t scope =>
  @Finset.filter.{0} Nat (GenLimit.RecursiveCritical C stream t)
    (fun a => Classical.propDecidable (GenLimit.RecursiveCritical C stream t a)) (Finset.range scope)
```

### `GenLimit.PatientMachine.criticalStart`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Certificate:21`

```lean
(O : GenLimit.OracleFamily) → (stream : Nat → Nat) → (z : Nat) → GenLimit.Presents stream (O.language z) → Nat
```

```lean
fun O stream z hP =>
  @Nat.find (fun n => ∀ (t : Nat), @LE.le.{0} Nat instLENat n t → GenLimit.RecursiveCritical O.language stream t z)
    (fun a =>
      Classical.propDecidable
        (∀ (t : Nat), @LE.le.{0} Nat instLENat a t → GenLimit.RecursiveCritical O.language stream t z))
    ⋯
```

### `GenLimit.PatientMachine.criticalStart._proof_1`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Certificate:None`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z : Nat),
  GenLimit.Presents stream (O.language z) →
    ∃ T, ∀ (t : Nat), @LE.le.{0} Nat instLENat T t → GenLimit.RecursiveCritical O.language stream t z
```

### `GenLimit.PatientMachine.decide`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:314`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → GenLimit.PatientMachine.State → GenLimit.PatientMachine.Decision
```

```lean
fun C stream t old =>
  @ite.{1} GenLimit.PatientMachine.Decision
    (GenLimit.Consistent C stream
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      old.focus)
    (Classical.propDecidable
      (GenLimit.Consistent C stream
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        old.focus))
    (GenLimit.PatientMachine.stableDecision C stream t old) (GenLimit.PatientMachine.backtrackDecision C stream t old)
```

### `GenLimit.PatientMachine.departureTimes`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Departure:28`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → Nat → Finset.{0} Nat
```

```lean
fun O stream t i =>
  @Finset.filter.{0} Nat (GenLimit.PatientMachine.UpwardDeparture O stream i)
    (fun a => Classical.propDecidable (GenLimit.PatientMachine.UpwardDeparture O stream i a)) (Finset.range t)
```

### `GenLimit.PatientMachine.fact_3_13`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Fact313:16`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {t : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t →
    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
        (GenLimit.AdversaryFirst stream (GenLimit.PatientMachine.output O stream)) (stream t) →
      stream t ∉ GenLimit.sample stream t →
        Not (GenLimit.PatientMachine.SwitchRound O stream t) →
          And
            (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat)
              (O.language (GenLimit.PatientMachine.run O stream t).focus) (stream t))
            (@LT.lt.{0} Nat instLTNat
              (GenLimit.PatientMachine.output O stream
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) t
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (stream t))
```

### `GenLimit.PatientMachine.gameTrace`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Pairing:24`

```lean
(O : GenLimit.OracleFamily) →
  (stream : Nat → Nat) →
    (z validFrom : Nat) →
      GenLimit.Presents stream (O.language z) →
        (∀ (t : Nat),
            @LE.le.{0} Nat instLENat validFrom t →
              @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
                (GenLimit.PatientMachine.output O stream t)) →
          GenLimit.PatientScope.GameTrace
```

```lean
fun O stream z validFrom hP hvalid =>
  { target := O.language z, adversary := stream, generator := GenLimit.PatientMachine.output O stream, presents := hP,
    fresh_adversary := ⋯, fresh_generator := ⋯, validFrom := validFrom, eventual_target := hvalid }
```

### `GenLimit.PatientMachine.highestCritical`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:107`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Nat → Nat
```

```lean
fun C stream t scope fallback =>
  have candidates := GenLimit.PatientMachine.criticalIndices C stream t scope;
  @GenLimit.Support.greatestCandidateWithFallback.{0} Nat Nat.instLinearOrder candidates fallback
```

### `GenLimit.PatientMachine.highestSurvivor`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:115`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Nat → Nat
```

```lean
fun C stream t scope fallback =>
  have candidates := GenLimit.PatientMachine.survivingCriticalIndices C stream t scope;
  @GenLimit.Support.greatestCandidateWithFallback.{0} Nat Nat.instLinearOrder candidates fallback
```

### `GenLimit.PatientMachine.initialState`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:55`

```lean
GenLimit.PatientMachine.State
```

```lean
{ scope := @OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)),
  tau := @OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)),
  age := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
  focus := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
  used := @EmptyCollection.emptyCollection.{0} (Finset.{0} Nat) (@Finset.instEmptyCollection.{0} Nat),
  lastOutput := @Option.none.{0} Nat, move := GenLimit.PatientMachine.MoveKind.initial }
```

### `GenLimit.PatientMachine.lateSwitchLoss`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Pairing:47`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → Set.{0} Nat
```

```lean
fun O stream validFrom =>
  @setOf.{0} Nat fun x =>
    And
      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
        (GenLimit.AdversaryFirst stream (GenLimit.PatientMachine.output O stream)) x)
      (∃ t,
        And (@LT.lt.{0} Nat instLTNat validFrom t)
          (And (@Eq.{1} Nat (stream t) x)
            (And (x ∉ GenLimit.sample stream t) (GenLimit.PatientMachine.SwitchRound O stream t))))
```

### `GenLimit.PatientMachine.latestDeparture`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Departure:354`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → Nat → Nat
```

```lean
fun O stream t i =>
  have ds := GenLimit.PatientMachine.departureTimes O stream t i;
  @GenLimit.Support.greatestCandidateWithFallback.{0} Nat Nat.instLinearOrder ds
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```

### `GenLimit.PatientMachine.leastAvailable`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:340`

```lean
(C : GenLimit.LanguageFamily) →
  (∀ (i : Nat), @Set.Infinite.{0} Nat (C i)) → (Nat → Nat) → Nat → Finset.{0} Nat → Nat → Nat
```

```lean
fun C hInfinite stream t used focus =>
  @Nat.find (GenLimit.PatientMachine.Available C stream t used focus)
    (fun a => Classical.propDecidable (GenLimit.PatientMachine.Available C stream t used focus a)) ⋯
```

### `GenLimit.PatientMachine.lemma_3_14`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Charging:44`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z : Nat) (hP : GenLimit.Presents stream (O.language z)) (n : Nat),
  @LE.le.{0} Nat instLENat
    (GenLimit.PatientScope.prefixCount (GenLimit.PatientMachine.settledSwitchLoss O stream z hP) n)
    (GenLimit.PatientScope.prefixCount (O.language z) n).log2
```

### `GenLimit.PatientMachine.lowestConsistent`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:130`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Nat
```

```lean
fun C stream t fallback =>
  @dite.{1} Nat (∃ i, GenLimit.Consistent C stream t i)
    (Classical.propDecidable (∃ i, GenLimit.Consistent C stream t i))
    (fun h =>
      @Nat.find (GenLimit.Consistent C stream t) (fun a => Classical.propDecidable (GenLimit.Consistent C stream t a))
        h)
    fun h => fallback
```

### `GenLimit.PatientMachine.lowestConsistentInScope`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:122`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Nat → Nat
```

```lean
fun C stream t scope fallback =>
  have candidates := GenLimit.PatientMachine.consistentIndices C stream t scope;
  @GenLimit.Support.leastCandidateWithFallback.{0} Nat Nat.instLinearOrder candidates fallback
```

### `GenLimit.PatientMachine.onModel_of_presents`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant:467`

```lean
∀ (O : GenLimit.OracleFamily) {stream : Nat → Nat} {z : Nat},
  GenLimit.Presents stream (O.language z) → GenLimit.PatientMachine.OnModel O stream
```

### `GenLimit.PatientMachine.output`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:387`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → Nat
```

```lean
fun O stream t =>
  @Option.getD.{0} Nat
    (GenLimit.PatientMachine.run O stream
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).lastOutput
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```

### `GenLimit.PatientMachine.output_ne_of_lt`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant:576`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {s t : Nat},
  @LT.lt.{0} Nat instLTNat s t →
    @Ne.{1} Nat (GenLimit.PatientMachine.output O stream s) (GenLimit.PatientMachine.output O stream t)
```

### `GenLimit.PatientMachine.patientLowerDensity`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Main:17`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → Real
```

```lean
fun O stream z =>
  GenLimit.PatientScope.relativeLowerDensity
    (@Inter.inter.{0} GenLimit.Language (@Set.instInter.{0} Nat)
      (GenLimit.GeneratorFirst stream (GenLimit.PatientMachine.output O stream)) (O.language z))
    (O.language z) ⋯
```

### `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Main:53`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {z : Nat},
  GenLimit.Presents stream (O.language z) →
    And
      (∃ T,
        ∀ (t : Nat),
          @LE.le.{0} Nat instLENat T t →
            And
              (@Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
                (GenLimit.PatientMachine.output O stream t))
              (And
                (∀ (s : Nat),
                  @LE.le.{0} Nat instLENat s t → @Ne.{1} Nat (stream s) (GenLimit.PatientMachine.output O stream t))
                (∀ (s : Nat),
                  @LT.lt.{0} Nat instLTNat s t →
                    @Ne.{1} Nat (GenLimit.PatientMachine.output O stream s)
                      (GenLimit.PatientMachine.output O stream t))))
      (@LE.le.{0} Real Real.instLE
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
        (GenLimit.PatientMachine.patientLowerDensity O stream z))
```

### `GenLimit.PatientMachine.patientScope_lowerDensity_half`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Main:36`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {z : Nat},
  GenLimit.Presents stream (O.language z) →
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
      (GenLimit.PatientMachine.patientLowerDensity O stream z)
```

### `GenLimit.PatientMachine.patient_validity`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Validity:233`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {z : Nat},
  GenLimit.Presents stream (O.language z) →
    ∃ T,
      ∀ (t : Nat),
        @LE.le.{0} Nat instLENat T t →
          @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
            (GenLimit.PatientMachine.output O stream t)
```

### `GenLimit.PatientMachine.predecessorPartner_injective_machine`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Pairing:173`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z validFrom : Nat) (hP : GenLimit.Presents stream (O.language z))
  (hvalid :
    ∀ (t : Nat),
      @LE.le.{0} Nat instLENat validFrom t →
        @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
          (GenLimit.PatientMachine.output O stream t)),
  @Set.InjOn.{0, 0} Nat Nat (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).predecessorPartner
    (GenLimit.PatientScope.ordinaryAttacker (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).target
      (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).attacker
      (GenLimit.PatientMachine.lateSwitchLoss O stream validFrom)
      (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).earlyAttacker)
```

### `GenLimit.PatientMachine.predecessorPartner_lt_machine`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Pairing:163`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z validFrom : Nat) (hP : GenLimit.Presents stream (O.language z))
  (hvalid :
    ∀ (t : Nat),
      @LE.le.{0} Nat instLENat validFrom t →
        @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
          (GenLimit.PatientMachine.output O stream t))
  {x : Nat},
  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (GenLimit.PatientScope.ordinaryAttacker (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).target
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).attacker
        (GenLimit.PatientMachine.lateSwitchLoss O stream validFrom)
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).earlyAttacker)
      x →
    @LT.lt.{0} Nat instLTNat ((GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).predecessorPartner x) x
```

### `GenLimit.PatientMachine.predecessorPartner_mem_machine`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Pairing:154`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z validFrom : Nat) (hP : GenLimit.Presents stream (O.language z))
  (hvalid :
    ∀ (t : Nat),
      @LE.le.{0} Nat instLENat validFrom t →
        @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z)
          (GenLimit.PatientMachine.output O stream t))
  {x : Nat},
  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (GenLimit.PatientScope.ordinaryAttacker (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).target
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).attacker
        (GenLimit.PatientMachine.lateSwitchLoss O stream validFrom)
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).earlyAttacker)
      x →
    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
      (@Inter.inter.{0} (Set.{0} Nat) (@Set.instInter.{0} Nat)
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).defender
        (GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).target)
      ((GenLimit.PatientMachine.gameTrace O stream z validFrom hP hvalid).predecessorPartner x)
```

### `GenLimit.PatientMachine.previous_output_lt_of_not_lateSwitch`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Pairing:108`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {validFrom t : Nat},
  @LT.lt.{0} Nat instLTNat validFrom t →
    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
        (GenLimit.AdversaryFirst stream (GenLimit.PatientMachine.output O stream)) (stream t) →
      stream t ∉ GenLimit.sample stream t →
        stream t ∉ GenLimit.PatientMachine.lateSwitchLoss O stream validFrom →
          @LT.lt.{0} Nat instLTNat
            (GenLimit.PatientMachine.output O stream
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) t
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (stream t)
```

### `GenLimit.PatientMachine.processRound`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:364`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → GenLimit.PatientMachine.State → GenLimit.PatientMachine.State
```

```lean
fun O stream t old =>
  have d := GenLimit.PatientMachine.decide O.language stream t old;
  have x :=
    GenLimit.PatientMachine.leastAvailable O.language ⋯ stream
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      old.used d.focus;
  { scope := d.scope, tau := d.tau,
    age :=
      @ite.{1} Nat (@Eq.{1} Nat d.focus old.focus) (instDecidableEqNat d.focus old.focus)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old.age
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
    focus := d.focus,
    used := @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat) x old.used,
    lastOutput := @Option.some.{0} Nat x, move := d.move }
```

### `GenLimit.PatientMachine.run`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:380`

```lean
GenLimit.OracleFamily → (Nat → Nat) → Nat → GenLimit.PatientMachine.State
```

```lean
fun O stream x =>
  @Nat.brecOn.{1} (fun x => GenLimit.PatientMachine.State) x fun x f =>
    GenLimit.PatientMachine.run.match_1.{1}
      (fun x => @Nat.below.{1} (fun x => GenLimit.PatientMachine.State) x → GenLimit.PatientMachine.State) x
      (fun a x => GenLimit.PatientMachine.initialState) (fun t x => GenLimit.PatientMachine.processRound O stream t x.1)
      f
```

### `GenLimit.PatientMachine.run.match_1`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:None`

```lean
(motive : Nat → Sort u_1) →
  (x : Nat) →
    (Unit → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      ((t : Nat) → motive t.succ) → motive x
```

```lean
fun motive x h_1 h_2 => @Nat.casesOn.{u_1} (fun x => motive x) x (h_1 Unit.unit) fun n => h_2 n
```

### `GenLimit.PatientMachine.scopeStart`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Certificate:37`

```lean
(O : GenLimit.OracleFamily) → (stream : Nat → Nat) → (z : Nat) → GenLimit.Presents stream (O.language z) → Nat
```

```lean
fun O stream z hP =>
  @Nat.find
    (fun n =>
      ∀ (t : Nat),
        @LE.le.{0} Nat instLENat n t → @LT.lt.{0} Nat instLTNat z (GenLimit.PatientMachine.run O stream t).scope)
    (fun a =>
      Classical.propDecidable
        (∀ (t : Nat),
          @LE.le.{0} Nat instLENat a t → @LT.lt.{0} Nat instLTNat z (GenLimit.PatientMachine.run O stream t).scope))
    ⋯
```

### `GenLimit.PatientMachine.settledChargingCertificate`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Charging:33`

```lean
(O : GenLimit.OracleFamily) →
  (stream : Nat → Nat) →
    (z : Nat) →
      (hP : GenLimit.Presents stream (O.language z)) →
        GenLimit.PatientScope.TargetSwitchChargingCertificate (O.language z)
          (GenLimit.PatientMachine.settledSwitchLoss O stream z hP)
```

```lean
fun O stream z hP =>
  @id.{1}
    (GenLimit.PatientScope.TargetSwitchChargingCertificate (O.language z)
      (GenLimit.PatientMachine.settledSwitchLoss O stream z hP))
    (@GenLimit.PatientMachine.StableTargetRun.chargingCertificate O stream (O.language z)
      (GenLimit.PatientMachine.settledStableTargetRun✝ O stream z hP))
```

### `GenLimit.PatientMachine.settledSwitchLoss`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Certificate:95`

```lean
(O : GenLimit.OracleFamily) → (stream : Nat → Nat) → (z : Nat) → GenLimit.Presents stream (O.language z) → Set.{0} Nat
```

```lean
fun O stream z hP =>
  GenLimit.PatientMachine.lateSwitchLoss O stream (GenLimit.PatientMachine.settledThreshold O stream z hP)
```

### `GenLimit.PatientMachine.settledThreshold`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Certificate:52`

```lean
(O : GenLimit.OracleFamily) → (stream : Nat → Nat) → (z : Nat) → GenLimit.Presents stream (O.language z) → Nat
```

```lean
fun O stream z hP =>
  @Max.max.{0} Nat Nat.instMax (GenLimit.PatientMachine.criticalStart O stream z hP)
    (GenLimit.PatientMachine.scopeStart O stream z hP)
```

### `GenLimit.PatientMachine.settled_target_critical`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Certificate:57`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z : Nat) (hP : GenLimit.Presents stream (O.language z)) {t : Nat},
  @LE.le.{0} Nat instLENat (GenLimit.PatientMachine.settledThreshold O stream z hP) t →
    GenLimit.RecursiveCritical O.language stream t z
```

### `GenLimit.PatientMachine.settled_target_in_scope`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Certificate:65`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z : Nat) (hP : GenLimit.Presents stream (O.language z)) {t : Nat},
  @LE.le.{0} Nat instLENat (GenLimit.PatientMachine.settledThreshold O stream z hP) t →
    @LT.lt.{0} Nat instLTNat z (GenLimit.PatientMachine.run O stream t).scope
```

### `GenLimit.PatientMachine.stableDecision`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:302`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → GenLimit.PatientMachine.State → GenLimit.PatientMachine.Decision
```

```lean
fun C stream t old =>
  @dite.{1} GenLimit.PatientMachine.Decision
    (@LE.le.{0} Nat instLENat
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) old.tau)
      old.age)
    ((@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) old.tau).decLe
      old.age)
    (fun hwait =>
      have newScope :=
        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old.scope
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
      have newFocus :=
        GenLimit.PatientMachine.highestCritical C stream
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          newScope old.focus;
      have newTau :=
        @ite.{1} Nat (@Eq.{1} Nat newFocus old.focus) (instDecidableEqNat newFocus old.focus) old.tau
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old.tau
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))));
      { scope := newScope, tau := newTau, focus := newFocus, move := GenLimit.PatientMachine.MoveKind.expand })
    fun hwait =>
    { scope := old.scope, tau := old.tau, focus := old.focus, move := GenLimit.PatientMachine.MoveKind.stay }
```

### `GenLimit.PatientMachine.stream_ne_output`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant:586`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (t s : Nat),
  @LE.le.{0} Nat instLENat s t → @Ne.{1} Nat (stream s) (GenLimit.PatientMachine.output O stream t)
```

### `GenLimit.PatientMachine.survivingCriticalIndices`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Machine:77`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Finset.{0} Nat
```

```lean
fun C stream t scope =>
  {i ∈ Finset.range scope |
    And (GenLimit.RecursiveCritical C stream t i)
      (GenLimit.RecursiveCritical C stream
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        i)}
```

### `GenLimit.PatientMachine.target_eventually_in_scope`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Validity:222`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) {z : Nat},
  GenLimit.Presents stream (O.language z) →
    ∃ T,
      ∀ (t : Nat),
        @LE.le.{0} Nat instLENat T t → @LT.lt.{0} Nat instLTNat z (GenLimit.PatientMachine.run O stream t).scope
```

### `GenLimit.PatientScope.GameTrace`

inductive; `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace:19`

```lean
Type
```

Constructors: `GenLimit.PatientScope.GameTrace.mk`.

### `GenLimit.PatientScope.GameTrace.adversary`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace:21`

```lean
GenLimit.PatientScope.GameTrace → Nat → Nat
```

```lean
fun self => self.2
```

### `GenLimit.PatientScope.GameTrace.attacker`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace:37`

```lean
GenLimit.PatientScope.GameTrace → Set.{0} Nat
```

```lean
fun G => GenLimit.AdversaryFirst G.adversary G.generator
```

### `GenLimit.PatientScope.GameTrace.defender`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace:40`

```lean
GenLimit.PatientScope.GameTrace → Set.{0} Nat
```

```lean
fun G => GenLimit.GeneratorFirst G.adversary G.generator
```

### `GenLimit.PatientScope.GameTrace.earlyAttacker`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace:81`

```lean
GenLimit.PatientScope.GameTrace → Finset.{0} Nat
```

```lean
fun G =>
  {x ∈
      GenLimit.sample G.adversary
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) G.validFrom
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) |
    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) G.attacker x}
```

### `GenLimit.PatientScope.GameTrace.generator`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace:22`

```lean
GenLimit.PatientScope.GameTrace → Nat → Nat
```

```lean
fun self => self.3
```

### `GenLimit.PatientScope.GameTrace.mk`

constructor; `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace:19`

```lean
(target : GenLimit.Language) →
  (adversary generator : Nat → Nat) →
    GenLimit.Presents adversary target →
      (∀ (t s : Nat), @LE.le.{0} Nat instLENat s t → @Ne.{1} Nat (adversary s) (generator t)) →
        (∀ (t s : Nat), @LT.lt.{0} Nat instLTNat s t → @Ne.{1} Nat (generator s) (generator t)) →
          (validFrom : Nat) →
            (∀ (t : Nat),
                @LE.le.{0} Nat instLENat validFrom t →
                  @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) target (generator t)) →
              GenLimit.PatientScope.GameTrace
```

### `GenLimit.PatientScope.GameTrace.predecessorPartner`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.Pairing:71`

```lean
GenLimit.PatientScope.GameTrace → Nat → Nat
```

```lean
fun G x => GenLimit.predecessorPartner G.adversary G.generator x
```

### `GenLimit.PatientScope.GameTrace.target`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace:20`

```lean
GenLimit.PatientScope.GameTrace → GenLimit.Language
```

```lean
fun self => self.1
```

### `GenLimit.PatientScope.GameTrace.validFrom`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace:29`

```lean
GenLimit.PatientScope.GameTrace → Nat
```

```lean
fun self => self.7
```

### `GenLimit.PatientScope.TargetSwitchChargingCertificate`

inductive; `GenLimit.Paper39_DenseGeneration.Abstract.TargetSwitchCharging:16`

```lean
Set.{0} Nat → Set.{0} Nat → Type
```

Constructors: `GenLimit.PatientScope.TargetSwitchChargingCertificate.mk`.

### `GenLimit.PatientScope.TargetSwitchChargingCertificate.mk`

constructor; `GenLimit.Paper39_DenseGeneration.Abstract.TargetSwitchCharging:16`

```lean
{target switchLoss : Set.{0} Nat} →
  (tau : Nat → Nat) →
    (charge : Nat → Finset.{0} Nat) →
      @HasSubset.Subset.{0} (Set.{0} Nat) (@Set.instHasSubset.{0} Nat) switchLoss target →
        (∀ (ℓ : Nat),
            @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) switchLoss ℓ →
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (tau ℓ)) →
          @Set.InjOn.{0, 0} Nat Nat tau switchLoss →
            (∀ (ℓ : Nat),
                @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) switchLoss ℓ →
                  @LE.le.{0} Nat instLENat
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (tau ℓ))
                    (@Finset.card.{0} Nat (charge ℓ))) →
              (∀ (ℓ : Nat),
                  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) switchLoss ℓ →
                    @HasSubset.Subset.{0} (Set.{0} Nat) (@Set.instHasSubset.{0} Nat) (@Finset.toSet.{0} Nat (charge ℓ))
                      target) →
                (∀ (ℓ : Nat),
                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) switchLoss ℓ →
                      @HasSubset.Subset.{0} (Finset.{0} Nat) (@Finset.instHasSubset.{0} Nat) (charge ℓ)
                        (Finset.range ℓ)) →
                  GenLimit.PatientScope.TargetSwitchChargingCertificate target switchLoss
```

### `GenLimit.PatientScope.TargetSwitchChargingCertificate.prefixCount_le_log2_targetCount`

theorem; `GenLimit.Paper39_DenseGeneration.Abstract.TargetSwitchCharging:62`

```lean
∀ {target switchLoss : Set.{0} Nat} (Q : GenLimit.PatientScope.TargetSwitchChargingCertificate target switchLoss)
  (n : Nat),
  @LE.le.{0} Nat instLENat (GenLimit.PatientScope.prefixCount switchLoss n)
    (GenLimit.PatientScope.prefixCount target n).log2
```

### `GenLimit.PatientScope.ordinaryAttacker`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.PatientScope:49`

```lean
Set.{0} Nat → Set.{0} Nat → Set.{0} Nat → Finset.{0} Nat → Set.{0} Nat
```

```lean
fun target attacker switchLoss earlyAttacker =>
  @SDiff.sdiff.{0} (Set.{0} Nat) (@Set.instSDiff.{0} Nat)
    (@Inter.inter.{0} (Set.{0} Nat) (@Set.instInter.{0} Nat) attacker target)
    (@Union.union.{0} (Set.{0} Nat) (@Set.instUnion.{0} Nat) (@Finset.toSet.{0} Nat earlyAttacker) switchLoss)
```

### `GenLimit.PatientScope.prefixCount`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.PatientScope:43`

```lean
Set.{0} Nat → Nat → Nat
```

```lean
fun S n => @Finset.card.{0} Nat (GenLimit.PatientScope.prefixFinset S n)
```

### `GenLimit.PatientScope.prefixFinset`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.PatientScope:32`

```lean
Set.{0} Nat → Nat → Finset.{0} Nat
```

```lean
fun S n => {x ∈ Finset.range n | @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) S x}
```

### `GenLimit.PatientScope.relativeLowerDensity`

definition; `GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity:24`

```lean
GenLimit.Language → (K : GenLimit.Language) → @Set.Infinite.{0} Nat K → Real
```

```lean
fun A K hK => (GenLimit.KleinbergWei.OrderedLanguage.increasing K hK).lowerDensity A
```

### `GenLimit.Presents`

definition; `GenLimit.Core.Basic:26`

```lean
(Nat → Nat) → GenLimit.Language → Prop
```

```lean
fun stream L => @Eq.{1} (Set.{0} Nat) (@Set.range.{0, 1} Nat Nat stream) L
```

### `GenLimit.RecursiveCritical`

definition; `GenLimit.Paper39_DenseGeneration.Critical:20`

```lean
GenLimit.LanguageFamily → (Nat → Nat) → Nat → Nat → Prop
```

```lean
fun C stream t =>
  @WellFounded.fix.{1, 1} Nat (fun a => Prop)
    (@invImage.{1, 1} Nat Nat (fun x => x) (@sizeOfWFRel.{1} Nat instSizeOfNat)).1 GenLimit.RecursiveCritical._proof_1
    fun a a_1 =>
    GenLimit.RecursiveCritical.match_1.{1}
      (fun x =>
        ((y : Nat) → (@invImage.{1, 1} Nat Nat (fun x => x) (@sizeOfWFRel.{1} Nat instSizeOfNat)).1 y x → Prop) → Prop)
      a (fun a x => GenLimit.Consistent C stream t (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (fun n x =>
        And
          (GenLimit.Consistent C stream t
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (∀ (j : Nat) (a : @LE.le.{0} Nat instLENat j n),
            x j ⋯ →
              @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat)
                (C
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (C j)))
      a_1
```

### `GenLimit.RecursiveCritical._proof_1`

theorem; `GenLimit.Paper39_DenseGeneration.Critical:None`

```lean
@WellFounded.{1} Nat (@invImage.{1, 1} Nat Nat (fun x => x) (@sizeOfWFRel.{1} Nat instSizeOfNat)).1
```

### `GenLimit.RecursiveCritical._proof_2`

theorem; `GenLimit.Paper39_DenseGeneration.Critical:None`

```lean
∀ (n j : Nat),
  @LE.le.{0} Nat instLENat j n → (@invImage.{1, 1} Nat Nat (fun x => x) (@sizeOfWFRel.{1} Nat instSizeOfNat)).1 j n.succ
```

### `GenLimit.RecursiveCritical.match_1`

definition; `GenLimit.Paper39_DenseGeneration.Critical:None`

```lean
(motive : Nat → Sort u_1) →
  (x : Nat) →
    (Unit → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      ((n : Nat) → motive n.succ) → motive x
```

```lean
fun motive x h_1 h_2 => @Nat.casesOn.{u_1} (fun x => motive x) x (h_1 Unit.unit) fun n => h_2 n
```

### `GenLimit.Support.greatestCandidateWithFallback`

definition; `GenLimit.Support.LeastCandidate:49`

```lean
{α : Type u_1} → [LinearOrder.{u_1} α] → Finset.{u_1} α → α → α
```

```lean
fun {α} [inst : LinearOrder.{u_1} α] candidates fallback =>
  @dite.{u_1 + 1} α (@Finset.Nonempty.{u_1} α candidates) (@Finset.decidableNonempty.{u_1} α candidates)
    (fun h => @Finset.max'.{u_1} α inst candidates h) fun h => fallback
```

### `GenLimit.Support.leastCandidateWithFallback`

definition; `GenLimit.Support.LeastCandidate:20`

```lean
{α : Type u_1} → [LinearOrder.{u_1} α] → Finset.{u_1} α → α → α
```

```lean
fun {α} [inst : LinearOrder.{u_1} α] candidates fallback =>
  @dite.{u_1 + 1} α (@Finset.Nonempty.{u_1} α candidates) (@Finset.decidableNonempty.{u_1} α candidates)
    (fun h => @Finset.min'.{u_1} α inst candidates h) fun h => fallback
```

### `GenLimit.firstAnnouncementTime`

definition; `GenLimit.Support.TurnTaking.Announcements:30`

```lean
(Nat → Nat) → Nat → Nat
```

```lean
fun announcer x =>
  @dite.{1} Nat (∃ t, @Eq.{1} Nat (announcer t) x) (Classical.propDecidable (∃ t, @Eq.{1} Nat (announcer t) x))
    (fun h => @Nat.find (fun n => @Eq.{1} Nat (announcer n) x) (fun a => instDecidableEqNat (announcer a) x) h) fun h =>
    @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))
```

### `GenLimit.fixed_scope_one_step`

theorem; `GenLimit.Paper39_DenseGeneration.Dynamics:143`

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {t s f : Nat},
  GenLimit.IsFocus C stream t s f →
    GenLimit.Consistent C stream
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        f →
      And
        (∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i s →
            Iff
              (GenLimit.RecursiveCritical C stream
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i)
              (GenLimit.RecursiveCritical C stream t i))
        (GenLimit.IsFocus C stream
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          s f)
```

### `GenLimit.lost_recursiveCritical_suffix`

theorem; `GenLimit.Paper39_DenseGeneration.Dynamics:168`

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {t u i j : Nat},
  @LE.le.{0} Nat instLENat t u →
    @LE.le.{0} Nat instLENat i j →
      GenLimit.RecursiveCritical C stream t i →
        GenLimit.RecursiveCritical C stream t j →
          Not (GenLimit.RecursiveCritical C stream u i) → Not (GenLimit.RecursiveCritical C stream u j)
```

### `GenLimit.new_recursiveCritical_above_survivor`

theorem; `GenLimit.Paper39_DenseGeneration.Dynamics:183`

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {t u i j : Nat},
  @LE.le.{0} Nat instLENat t u →
    GenLimit.RecursiveCritical C stream u i →
      Not (GenLimit.RecursiveCritical C stream t i) →
        GenLimit.RecursiveCritical C stream t j → GenLimit.RecursiveCritical C stream u j → @LT.lt.{0} Nat instLTNat j i
```

### `GenLimit.predecessorPartner`

definition; `GenLimit.Support.TurnTaking.Announcements:64`

```lean
(Nat → Nat) → (Nat → Nat) → Nat → Nat
```

```lean
fun announcer generator x =>
  generator
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (GenLimit.firstAnnouncementTime announcer x)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### `GenLimit.recursiveCritical_subset_of_le`

theorem; `GenLimit.Paper39_DenseGeneration.Critical:38`

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {t i j : Nat},
  @LE.le.{0} Nat instLENat i j →
    GenLimit.RecursiveCritical C stream t i →
      GenLimit.RecursiveCritical C stream t j →
        @HasSubset.Subset.{0} GenLimit.Language (@Set.instHasSubset.{0} Nat) (C j) (C i)
```

### `GenLimit.sample`

definition; `GenLimit.Core.Basic:30`

```lean
(Nat → Nat) → Nat → Finset.{0} Nat
```

```lean
fun stream t => @Finset.image.{0, 0} Nat Nat instDecidableEqNat stream (Finset.range t)
```

### `GenLimit.target_eventually_recursiveCritical`

theorem; `GenLimit.Paper39_DenseGeneration.Critical:56`

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {z : Nat},
  GenLimit.Presents stream (C z) →
    ∃ T, ∀ (t : Nat), @LE.le.{0} Nat instLENat T t → GenLimit.RecursiveCritical C stream t z
```

### `_private.GenLimit.Paper39_DenseGeneration.Patient.Charging.0.GenLimit.PatientMachine.settledStableTargetRun`

definition; `GenLimit.Paper39_DenseGeneration.Patient.Charging:17`

```lean
(O : GenLimit.OracleFamily) →
  (stream : Nat → Nat) →
    (z : Nat) →
      GenLimit.Presents stream (O.language z) → GenLimit.PatientMachine.StableTargetRun O stream (O.language z)
```

```lean
fun O stream z hP =>
  @GenLimit.PatientMachine.StableTargetRun.mk O stream (O.language z) z
    (GenLimit.PatientMachine.settledThreshold O stream z hP) ⋯ ⋯ ⋯ ⋯ ⋯
```

### `_private.GenLimit.Paper39_DenseGeneration.Patient.Charging.0.GenLimit.PatientMachine.settledStableTargetRun._proof_1`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Charging:None`

```lean
∀ (O : GenLimit.OracleFamily) (z : Nat),
  @HasSubset.Subset.{0} (Set.{0} Nat) (@Set.instHasSubset.{0} Nat) (O.language z) (O.language z)
```

### `_private.GenLimit.Paper39_DenseGeneration.Patient.Charging.0.GenLimit.PatientMachine.settledStableTargetRun._proof_2`

theorem; `GenLimit.Paper39_DenseGeneration.Patient.Charging:None`

```lean
∀ (O : GenLimit.OracleFamily) (stream : Nat → Nat) (z : Nat),
  GenLimit.Presents stream (O.language z) →
    ∀ (t : Nat), @Membership.mem.{0, 0} Nat GenLimit.Language (@Set.instMembership.{0} Nat) (O.language z) (stream t)
```

## Scope, uncertainty and stopping point

All 32 supplied exact targets and all 44 slots are addressed. Missing decisive project definitions: none. Standard Lean/Mathlib meanings, including Nat.nth, Nat.find, Nat.log2, classical decisions and real liminf, are trusted at the expressly supplied external boundary; this is not a recursive library audit. The declared closure includes semantic proof-field obligations without their proofs. No conclusion here certifies those proofs, the source snapshot, source fidelity, effective algorithms, rates not stated in the types, or fresh compilation. The 19 no-endpoint slots remain explicit evidence gaps for later comparison. Stage 1 stops here; later-stage comparison was not performed.
