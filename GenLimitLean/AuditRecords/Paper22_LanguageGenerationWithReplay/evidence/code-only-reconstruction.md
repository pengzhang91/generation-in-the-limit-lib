# P22 — Stage1 code-only reconstruction

## Scope and input census

All six opaque slots and nine distinct targets are reconstructed below. There are no absent linked names and no slots without a supplied endpoint. Slots remain opaque identifiers; this report assigns no source-paper claims to them.

Semantic evidence was restricted to files in `P22/stage1`. An initial metadata-only command, `pwd && ls -la`, ran in `/Users/pengzhang/Documents/research/language generation lean` before the package inspection. It exposed that directory's file/directory names, not contents. This is an access-boundary deviation: this run cannot claim zero access outside the package. No paper text, source files, proof bodies, developer comments, Git data, PaperMap, registry, other reviews, or later stages were read. The directory listing was not used to infer any claim.

The packet contains 136 recursive declaration records: 104 definitions, 14 theorem types, ten constructors, seven inductives, and one recursor. Its native census contains 1,159 records: 386 definitions, 737 theorem types, 14 constructors, eleven inductives, and eleven recursors. Recursive records and target types were inspected; the native census was parsed and its P22 definition index inspected, with the selected records listed in the run manifest reviewed for supporting interface details. This does **not** assert individual semantic review of all 1,159 records. The native records add query-trace construction, countable transport, a constant querying procedure, and examples of named family definitions. None reveal theorem proof bodies or identify hidden existential witnesses automatically.

The packet's source-snapshot label is `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc`; this is supplied metadata, not an independently inspected source tree. All ten entries in the supplied `SHA256SUMS` matched. Actual input hashes, including the manifest itself, follow.

| Input file | Bytes | Actual SHA-256 |
|---|---:|---|
| `01-target-statements.md` | 3767 | `428c950e1d4816350b6975098bb7aeaa2715f8dbc4fa6d4bb6e75d76557985a6` |
| `02-definition-dependencies.md` | 80676 | `f03a31cd973352260b16de15a7ffee687ef351cd01624417c6ffda3d152b15a3` |
| `PROMPT.md` | 3356 | `c63aad9d119a37687071a9dd61f3139f0f318647c5237a6cfd05e4ecd3e38de3` |
| `SHA256SUMS` | 854 | `e5acd94ecafa0e6e3c8205a658f5afbcf6f388414a3c5692b6a9105fae7f1f01` |
| `START_HERE.md` | 217 | `52dbb6f80b47a22d94f222fd499cc75c3e793e710b44d74dd69922866c1c02d7` |
| `claim-slots.json` | 1379 | `5fcf2f68a44e1e3afcee903d038bfae59e2087a9b2e54185f2f45e64f1626090` |
| `declarations.jsonl` | 131399 | `29e76b6cf4f4dfe9cd5308f3e958704f4cc8e3395be9406287de863973c7263c` |
| `external-boundary.txt` | 1523 | `db8ae866667070962e4094c82ea5c0fe175df42996e8050340ed5397b2f71d2e` |
| `native-declaration-census.jsonl` | 1402128 | `a5ff4389863c596c5134a774dfd76c3ea81d2a0084cf7c972908d4936f2c2daf` |
| `snapshot.json` | 2199 | `dd043a318ae5202aa832d59074c599e58666049b9fa49c2e2de9ca88cc201113` |
| `targets.txt` | 383 | `a569817fe9a6b87c2a3c9fa4368acce06ac424659f302556fb3072c863e64c00` |

No Lean invocation, compilation, proof correctness review, theorem-proof certification, source correspondence judgment, or mathematical edit was performed. Requested configuration was `gpt-6.1-sol / xhigh`, with fresh, paper-withheld context requested. Backend revision and enforced context-isolation implementation are not observable; the manifest records the actual content-access boundary and the metadata deviation.

## Shared definition glossary

Unless otherwise stated, names below have prefix `GenLimit.Generic` or `GenLimit.Replay` as indicated. Their exact exported types and values are in the matching sections of [02-definition-dependencies.md](../stage1/02-definition-dependencies.md), also machine-readable in [declarations.jsonl](../stage1/declarations.jsonl). Abbreviations here are explanatory notation, not new Lean declarations.

### Scalar generation and replay

For `α : Type u`, `Language α = Set α`, `LanguageClass α = Set (Set α)`, `LanguageFamily α = Nat → Set α`, and `Stream α = Nat → α`. `FiniteHistoryOperator Input Output = (t : Nat) → (Fin t → Input) → Output`; a scalar `Generator α` has output type `α`. The generator receives the **ordered prefix** of length `t`, including repetitions, and its length. It has no future-input parameter or explicit membership-query argument.

Write `o_G(σ,t) = G t (fun i => σ i.val)` and `S_σ(t) = {σ n | n < t}` as a finite set. These are `output` and `sample`. `CorrectAt G L σ t`, abbreviated `C(G,L,σ,t)`, means **both** `o_G(σ,t) ∈ L` and `o_G(σ,t) ∉ S_σ(t)`. Freshness excludes observed inputs only. It does not by itself exclude earlier generator outputs, guarantee distinct outputs, or describe a probability law or support loss.

`StreamIn σ L` means `range σ ⊆ L`; it need not enumerate every element. `Presents σ L` means `range σ = L`; repetitions are allowed and no enumeration order is imposed. `UUS H` means `∀ L ∈ H, Set.Infinite L`.

Define `R(G,L,σ)` by the exact `IsReplaySequence` value:

```
∀ n : Nat, σ n ∈ L ∨ ∃ k : Nat, 0 < k ∧ k ≤ n ∧ o_G(σ,k) = σ n.
```

This is a condition on the **same generator G** being evaluated. At position `n`, an off-target input must equal an output at positive time `k ≤ n`; output time zero is excluded. `k = n` is allowed because output at `n` depends only on positions `< n`. `IsReplayEnumeration`, written `RE(G,L,σ)`, is `R(G,L,σ) ∧ ∀x∈L, ∃n, σ n = x`. It permits off-target values justified by replay; it is not the equality `range σ = L`. At `n=0` the input must belong to `L`.

The six relevant success predicates unfold as follows; all times, thresholds, and indices are natural numbers.

| Predicate | Full quantifier pattern after fixing G and H |
|---|---|
| `IsUniformGeneratorAt G H d` | `∀ L∈H, ∀σ, StreamIn σ L → ∀t, |S_σ(t)|=d → ∀s≥t, C(G,L,σ,s)` |
| `IsUniformReplayGeneratorAt G H d` | `∀ L∈H, ∀σ, R(G,L,σ) → ∀t, 0<t → |S_σ(t)|=d → ∀s≥t, C(G,L,σ,s)` |
| `IsNonuniformGenerator G H` | `∀ L∈H, ∃d, ∀σ, StreamIn σ L → ∀t, |S_σ(t)|=d → ∀s≥t, C(G,L,σ,s)` |
| `IsNonuniformReplayGenerator G H` | `∀ L∈H, ∃d, 0<d ∧ ∀σ, R(G,L,σ) → ∀t, 0<t → |S_σ(t)|=d → ∀s≥t, C(G,L,σ,s)` |
| `IsLimitGenerator G H` | `∀ L∈H, ∀σ, Presents σ L → ∃T, ∀s≥T, C(G,L,σ,s)` |
| `IsLimitReplayGenerator G H` | `∀ L∈H, ∀σ, RE(G,L,σ) → ∃T, ∀t≥T, C(G,L,σ,t)` |

`NonuniformlyGeneratable`, `NonuniformlyGeneratableWithReplay`, `GeneratableInLimit`, and `GeneratableInLimitWithReplay` respectively put a **single existential G outside** the corresponding class-wide predicate. Nonuniform ordinary thresholds may be zero; replay nonuniform thresholds must be positive. A threshold depends on `L`, not on its input stream. Limit onset `T` may depend on the stream as well as the language and generator. Every success conclusion is all-time-after-onset, not merely infinitely often. None of these scalar predicates demands computability.

### Oracle family and the named carried procedure

`GenLimit.Language = Set Nat` and `GenLimit.LanguageFamily = Nat → Set Nat`. `OracleFamily` stores a family `L_i`, proofs that every `L_i` is infinite, a Boolean map `q : Nat → Nat → Bool`, and `q(i,x)=true ↔ x∈L_i`. Its constructor imposes no `Computable` condition on `q`, no injectivity of indices, and no uniform bound on queries. `CountableDomainOracleFamily α` has the same fields with `x:α`. The existence of such a family implies that its domain is infinite, even though this consequence is not a separate target hypothesis.

The following reconstructs the exact values behind `O.carriedWitnessProtectionGenerator` (all names in this paragraph are under `GenLimit.OracleFamily`). Let a carried state be `(S,P,c,a)`: finite `sure` set `S`, finite `pastOutputs` set `P`, natural `cutoff c`, and scalar `output a`. The initial state is `(∅,∅,0,0)`. On a round with new input `x` and index bound `t`, set

```
S' = S                    if x ∈ P
     insert x S           otherwise
A  = {i < t | ∀y∈S', q(i,y)=true}.
```

These are `witnessProtectionSureUpdate`, `ReplayConsistentAt`, `replayActive`, and `HasReplayActive`. There is no assumption that an arbitrary input state was reached by an earlier run.

For `A≠∅` and cutoff candidate `m`, `ReplayFinitelyCriticalAt S' P m i` says that `i` is consistent with `S'` and

```
∀j<i, (j consistent with S') → ∀y<m,
       q(i,y)=true → y∉P → q(j,y)=true.
```

`replayCriticalCandidates` filters `i<t` by that property; `replaySelected` chooses its **maximum**. `finitePrefix i m` is `{y<m | q(i,y)=true}`. For each pair `i,j∈A` with `j<i`, `replayDifferencePrefix P i j m` is `finitePrefix i m \ (finitePrefix j m ∪ P)`. `replayWitnessValue` returns its minimum when nonempty, otherwise zero; `replayWitnesses` includes values only for nonempty differences, so the zero fallback does not add a witness from an empty difference. Define

```
D_m = finitePrefix (replaySelected S' P t m) m
      \ (S' ∪ P ∪ replayWitnesses S' P t m).
lower = max(c,x+1)+1.
```

`replayAdmissible` is `D_m`. `replayCarriedRoundCutoff` uses `Nat.find` to choose the **least** `m≥lower` with `D_m` nonempty, and `replayCarriedRoundOutput` chooses `min D_m`. `carriedWitnessProtectionProcessRound` returns `(S', insert out P, m, out)`. If `A=∅`, `witnessProtectionFallback` returns `min S'` when nonempty and zero otherwise, and the returned state is `(S', insert out P, c, out)` with the old cutoff. Active-round search termination and candidate nonemptiness are supplied through proposition arguments/theorem types; their proofs were not inspected. The procedure is a membership-oracle construction with an unbounded cutoff search, not a statement that an arbitrary oracle is ordinarily computable.

`carriedWitnessProtectionRun σ 0` is the initial state; its state at `n+1` is the process round on state `n`, input `σ n`, and bound `n+1`. The finite-history generator zero-extends a history after its length using `witnessProtectionPrefixStream`, runs exactly its length many rounds from the initial state, and returns the state's output. Hence it reads no part of that artificial future extension. At time zero it returns zero; the initial zero is not inserted into `pastOutputs` until an actual round inserts an output.

A replay membership query is `(i,y)`; an answered query is `((i,y),b)`; a trace is a **Finset** of answered queries. `ReplayMembershipTraceValid O Q` requires every recorded Boolean answer to equal `O.query i y`. Thus its cardinality counts distinct answered queries, without ordering or repeated-query costs. In the native census, `replayStageQueryPlan S' t m = range t × (S' ∪ range m)`; stage/round traces attach `O`'s answers to this finite rectangle. `carriedWitnessProtectionQueryTrace` uses the final found cutoff in the active branch, and zero in the inactive branch. These native definitions explain a concrete trace interface; the target itself existentially quantifies its trace.

`CarriedWitnessProtectionUsesFiniteQueries O` means: **for every state, x, t**, one trace `Q` simultaneously has all of these properties:

1. `Q` is valid for `O`.
2. For **every OracleFamily P0**, if that same `Q` is valid for `P0`, the entire next carried state under `P0` equals the next state under `O` on the same state, `x`, and `t`.
3. If the active set for the updated `S'` is nonempty, the next-state equality to `(S',insert out P,m,out)` holds with the cutoff and output above, `lower≤m`, `|Q|≤t*(|S'|+m)`, and
   `∀r, lower≤r → r≤m → ∀i<t, ∀y, (y∈S' ∨ y<r) → ((i,y),O.query i y)∈Q`.
4. Otherwise the next-state equality to the fallback state holds, `|Q|≤t*|S'|`, and
   `∀i<t, ∀y∈S', ((i,y),O.query i y)∈Q`.

The branch conditions are exhaustive; the same trace witnesses validity, agreement, update formula, bound, and coverage within its applicable branch. The active bound depends on the found cutoff, not solely on `t`; no ordinary time-complexity rate is claimed.

Native countable transport definitions map an `α↔Nat` equivalence across histories and family sets, run the natural-number procedure with query `q(i,e.symm n)`, and pull the output back by `e.symm`. The countable equivalence is obtained through `Classical.choice` of a `Denumerable α` witness. Neither `Countable α` nor this choice supplies a computable coding. The target existential result does not name this transport or assert its ordinary computability.

### Proper outputs and adaptive membership computation

`ProperGenerator ι α = (t:Nat) → (Fin t → α) → ι`. Its output is an **index**; write `h_g(σ,t)=g t (fun i=>σ i.val)`. `ProperCorrectAt family g target σ t` is exactly `family(h_g(σ,t)) ⊆ family target`. There is no point-output freshness clause, equality of hypotheses, eventual constant index, or sampling distribution.

`IsProperReplaySequence family g target σ` means

```
∀n, σ n ∈ family target ∨
     ∃k, 0<k ∧ k≤n ∧ σ n ∈ family(h_g(σ,k)).
```

Thus a replayed input can be **any member of an earlier output language**, not just an earlier scalar output. `IsProperReplayEnumeration` additionally covers every element of the target language at some stream position. `IsProperLimitReplayGenerator family g` means
`∀target, ∀σ, ProperReplayEnumeration → ∃T, ∀t≥T, family(h_g(σ,t)) ⊆ family target`.
`ProperlyGeneratableInLimitWithReplay family` is `∃g` with this property. No membership query parameter or computability restriction is part of that generator type.

The separate adaptive membership model has `ProperMembershipQuery = Nat × Nat`, answered queries `(query,Bool)`, `Round = (input,(finite list of answered queries,output index))`, and `Action = Sum Query Nat`. A `ProperMembershipAlgorithm A` is a **total step function** on `(finite list of completed rounds,(current Nat input, current finite query/answer list))`, returning either `Sum.inl` to ask a query or `Sum.inr` to emit an index. Totality of this step function does not imply that a round eventually emits an index.

`ProperMembershipAnswerCorrect family ((i,y),b)` is `b=true ↔ y∈family i`. For each position `k` of a finite within-round query list, `QueryTraceValid` requires that `A` on the completed history, current input, and the first `k` answers asks exactly that position's query, whose recorded answer is correct. `RoundValid` additionally equates the round's input to the current input and requires `A` on the entire finite answer list to emit exactly the round's output. `ExecutionValid` equates the numbers of rounds and inputs, and validates every round using precisely the preceding completed rounds and its corresponding input. Repeated queries and repetitions in lists are allowed. These are constraints on **ordered lists**, unlike the carried procedure's Finset traces.

`ProperMembershipExecutionOutputsAt A family σ t i`, abbreviated `E(A,family,σ,t,i)`, means that there exists a valid finite execution on inputs `σ 0,...,σ t` (length `t+1`) whose round at index `t` outputs `i`. This model sees the input `σ t` before its output at round `t`, whereas the scalar/proper finite-history `output` at `t` sees exactly positions `<t`. Every existential execution includes finite query lists and hence termination for its included rounds; the bare step-function type alone does not.

`IsRecursiveUUSFamily family` means `∃oracle : MembershipOracle family, Computable₂ oracle.query ∧ ∀i, Infinite(family i)`. `MembershipOracle` guarantees Boolean membership answers are correct. `Computable₂` is joint computability of one map on index and point, not merely a separate decidability claim for each language. `UniversalProperMembershipGenerator A`, abbreviated `U(A)`, is the conjunction

```
Computable A ∧ ∀family, IsRecursiveUUSFamily family →
  ∀target σ, Presents σ (family target) →
    (∀t, ∃i, E(A,family,σ,t,i)) ∧
    (∃T, ∀t≥T, ∀i, E(A,family,σ,t,i) → family i ⊆ family target).
```

This uses **ordinary target presentations**, not either replay-enumeration predicate. One `A` is fixed before all families and targets and receives the family through membership answers, not as a direct code argument. Its action function is ordinarily computable on the supplied encodings. The target-stream success clause separately supplies existence of terminating executions at every round and eventual subset correctness for **all** valid output indices. `T` may depend on the family, target, and stream. There is no target-stream rate or fixed query bound.

`Algorithm3Certificate A` is a data structure, not an algorithm function. Its constructor contains one family, a correct membership oracle with jointly computable query map, infinitude of every family member, a stream `σ`, one scalar output sequence `b:Nat→Nat`, `∀t E(A,family,σ,t,b t)`, and **one of** these branches for that same family, stream, and output sequence:

```
(Presents σ (family 0) ∧
 ∀T, ∃t, T≤t ∧ ¬(family(b t) ⊆ family 0))
∨
(∃trap start, Presents σ (family trap) ∧
 (∀t≥start, b t=0) ∧ ¬(family 0 ⊆ family trap)).
```

The first branch is failure at arbitrarily late times, not failure at every time. The second is eventual constant index zero with a non-subset witness relative to a possibly different target index `trap`. `trap` and `start` depend on the certificate; no separate bound or computation of them is specified. The stream and output sequence need not be computable. `Nonempty (Algorithm3Certificate A)` is semantic inhabitation, not a computable transformation constructing a certificate.

### Fixed domains and supplementary native families

`HardPoint = Nat ⊕ Nat`; `upperLanguage = {inl n | n:Nat}`; `cutoffLanguage a = {inl n | n<a} ∪ {inr n | n:Nat}`. `nonuniformHardClass` is `{upperLanguage} ∪ range cutoffLanguage`, including `a=0`. Each of these displayed languages is infinite.

`LimitReplayPoint = Int ⊕ Nat`. `HardHypothesis` has exactly the four nullary constructors `minusOne`, `minusTwo`, `plusOne`, and `plusTwo`; its explicit `Fintype` lists these four. Constructor names alone imply no integer membership rule.

For clarity about what was learned from the native census, two named candidates can be described independently of the anonymous existential witnesses in the targets. `properReplayHardFamily` assigns, in the four constructor positions just listed, `{z≤0}∪{1}`, `{z≤0}∪{2}`, `{z≥0}∪{-1}`, and `{z≥0}∪{-2}`. Its match helper fixes this ordering. `replayLimitHardClass` contains the language of all `inr n`, and, for each `a:Nat`, two subfamilies. The first has all languages with `inr n` iff `n<a` and `inl z` iff `z=a ∨ z∈B ∨ j<z`, for arbitrary `B⊆Int` and `j:Int` with `a<j`. The second has the same `inr` portion and `inl z` iff `z<a ∨ z∈B`, with `B⊆{z | z≠a}`. These definitions are supplemental code evidence. The theorem proof bodies that might select either named candidate as an existential witness remain withheld; neither target's exact type identifies its witness by name.

## Target dossiers

### T1 / C01 — uniform scalar existence equivalence

`GenLimit.Replay.Results.theorem_4_1` — theorem; exported source anchor `GenLimit.Paper22_LanguageGenerationWithReplay.Results.Overview:41`. Exact kernel type: [declarations.jsonl line 108](../stage1/declarations.jsonl#L108) and the same identifier's section in [01-target-statements.md](../stage1/01-target-statements.md).

**Reconstruction.** For every universe-polymorphic inhabited domain `α`, every language class `H`, and every natural `d` with `0<d`, there exists a scalar generator uniformly correct at distinct-sample threshold `d` on target-contained input streams iff there exists a scalar generator with the corresponding replay-uniform guarantee at the **same d**. Both success predicates expand in the glossary, including freshness, all future times, and the replay-side positive-time premise.

**Skeleton.** `∀{α:Type u} [Inhabited α] (H:Set(Set α)) (d:Nat), 0<d → ((∃G, Uniform(G,H,d)) ↔ (∃G', ReplayUniform(G',H,d)))`.

**Information and dependencies.** Each witness is one finite-history function shared across the class and all streams and may depend on `H,d` and the inhabited instance. The two witnesses are independently quantified; the exact type neither asserts their equality nor names a conversion procedure. There is no oracle or computability requirement.

**Edges.** Empty classes are vacuous. Empty target languages admit neither target-contained streams nor replay sequences, since position zero must be a target point. No infinitude condition is imposed on `H`. The condition is exact equality of distinct-input cardinality to `d`, not a supplied time or a sample-count-with-repetitions bound; streams that never hit it have no resulting success obligation. For `d>0`, a triggering time is automatically positive; `d=0` is outside the theorem. Exhaustion of a finite target after a trigger would conflict with freshness, rather than being silently excepted.

### T2 / C02 — one specified class separates nonuniform predicates

`GenLimit.Replay.Results.theorem_5_1` — theorem; exported source anchor `GenLimit.Paper22_LanguageGenerationWithReplay.Results.Overview:50`. Exact kernel type: [declarations.jsonl line 109](../stage1/declarations.jsonl#L109) and the same identifier's section in [01-target-statements.md](../stage1/01-target-statements.md).

**Reconstruction.** The particular `nonuniformHardClass` on `Nat⊕Nat` is nonuniformly generatable by one scalar finite-history function on target-contained streams, and there is no scalar finite-history function satisfying the replay nonuniform predicate for that same class.

**Skeleton.** With the fixed `H` above,
`(∃G, ∀L∈H, ∃d, ∀σ, StreamIn σ L → ∀t, |S_σ(t)|=d → ∀s≥t, C(G,L,σ,s)) ∧ ¬∃G', ∀L∈H, ∃d, 0<d ∧ ∀σ, R(G',L,σ) → ∀t, 0<t → |S_σ(t)|=d → ∀s≥t, C(G',L,σ,s)`.

**Information and dependencies.** Ordinary `d` is chosen after `L` and before every stream; `G` is chosen before `L`. The replay negation ranges over arbitrary functions, so it is not restricted to computable or named learners. The endpoint supplies no explicit positive generator, threshold formula, or oracle implementation.

**Edges.** The class includes the all-right `cutoffLanguage 0`; none of its languages is finite or empty. Repeated samples still count once. The ordinary and replay threshold positivity conditions differ exactly as displayed. The conclusion uses the specified same class in both conjuncts, not two independently chosen classes.

### T3 / C03 — limit replay existence on a countable domain

`GenLimit.Replay.Results.theorem_6_1` — theorem; exported source anchor `GenLimit.Paper22_LanguageGenerationWithReplay.Results.Overview:59`. Exact kernel type: [declarations.jsonl line 110](../stage1/declarations.jsonl#L110) and the same identifier's section in [01-target-statements.md](../stage1/01-target-statements.md).

**Reconstruction.** For every `CountableDomainOracleFamily F` on a countable type `α`, there exists one scalar finite-history generator that is eventually correct and fresh at every time on every replay enumeration of every language in `range F.language`.

**Skeleton.** `∀{α:Type u} (F:CountableDomainOracleFamily α) [Countable α], ∃G, ∀L∈range F.language, ∀σ, RE(G,L,σ) → ∃T, ∀t≥T, C(G,L,σ,t)`.

**Information and dependencies.** `F` supplies a countably indexed family of infinite languages plus a Boolean membership oracle with its correctness property. No computability of that oracle or computable countable coding is assumed. The existential `G` may depend on the whole `F` and countability evidence but works for all its languages; `T` may depend on `L,σ`. The theorem type names no `G` and asserts neither a `Computable` instance nor the finite-query property of T4. Native countable transport values reviewed above contain a classical choice of coding.

**Edges.** Distinct indices may denote the same language; range removes these duplicates. The family index set is all naturals, and every language must be infinite; on an empty or finite `α` such a family cannot exist, so that parameter case is vacuous. Coverage of every target element is required; merely target-contained or replay-compatible streams without coverage are insufficient. No onset rate, uniform threshold, or time-zero correctness is supplied.

### T4 / C03 — named carried generator and finite query agreement

`GenLimit.Replay.Results.theorem_6_1_finite_query` — theorem; exported source anchor `GenLimit.Paper22_LanguageGenerationWithReplay.Results.Overview:72`. Exact kernel type: [declarations.jsonl line 111](../stage1/declarations.jsonl#L111) and the same identifier's section in [01-target-statements.md](../stage1/01-target-statements.md).

**Reconstruction.** For every natural-number `OracleFamily O`, the **specific** `O.carriedWitnessProtectionGenerator` is a limit replay generator for `range O.language`, and `O.CarriedWitnessProtectionUsesFiniteQueries` holds. The whole machine, its precise per-round branch formulas, shared trace witness, query coverage, and bounds are given in the shared glossary; those clauses are all part of this endpoint through the second conjunct.

**Skeleton.** `∀O:OracleFamily, (∀L∈range O.language, ∀σ, RE(G_O,L,σ) → ∃T, ∀t≥T, C(G_O,L,σ,t)) ∧ (∀state x t, ∃Q, Valid_O(Q) ∧ (∀P0, Valid_P0(Q) → next_P0(state,x,t)=next_O(state,x,t)) ∧ BranchSpec_O(state,x,t,Q))`, where `G_O` is the named generator and `BranchSpec` is exactly the active/inactive four-clause expansion above.

**Information and dependencies.** The same `O` supplies languages, membership answers, generator, correctness guarantee, and trace property. The same `Q` works for all alternative oracle families agreeing on it, with equality of the whole next state. `Q` can depend on `O,state,x,t`; the active cutoff can be arbitrarily large. The query bounds are `t*(|S'|+cutoff)` and `t*|S'|`, not universal runtime bounds. This is finite oracle dependence with a concrete membership-based machine, without an ordinary computability assumption on the oracle.

**Edges.** The trace property quantifies arbitrary states and bounds, including `t=0`; there is no reachable-state premise. For `t=0` the active set is empty and the trace bound is zero. Inactive fallback on empty `S'` returns zero; on nonempty `S'` it returns its minimum and can repeat outputs. Such transient fallback behavior does not itself assert `CorrectAt`. The theorem only guarantees eventual correctness on replay enumerations. Active rounds exclude `S'`, all stored outputs, and protected witnesses from the chosen output. Finset traces do not certify a particular ordered query execution or an ordinary running-time bound.

### T5 / C04 — an uncountable class with and without limit replay

`GenLimit.Replay.Results.theorem_6_6` — theorem; exported source anchor `GenLimit.Paper22_LanguageGenerationWithReplay.Results.Overview:79`. Exact kernel type: [declarations.jsonl line 112](../stage1/declarations.jsonl#L112) and the same identifier's section in [01-target-statements.md](../stage1/01-target-statements.md).

**Reconstruction.** There exists one class `H` of languages on `Int⊕Nat` that is not countable, whose every member is infinite, that admits a scalar limit generator on ordinary presentations, and that admits no scalar limit replay generator. All four properties concern the same `H`.

**Skeleton.** `∃H:Set(Set(Int⊕Nat)), ¬Set.Countable H ∧ (∀L∈H, Infinite L) ∧ (∃G, ∀L∈H, ∀σ, Presents σ L → ∃T, ∀t≥T, C(G,L,σ,t)) ∧ ¬∃G', ∀L∈H, ∀σ, RE(G',L,σ) → ∃T, ∀t≥T, C(G',L,σ,t)`.

**Information and dependencies.** `H` and the positive `G` are semantic witnesses; no uniform membership oracle, indexed presentation of the class, computation, or positive generator is named by the type. The negative quantifier includes all scalar finite-history functions. A countable domain is compatible with an uncountable set of its subsets. Native class definitions were inspected separately and are not substituted for the unnamed witness based on proof-name inference.

**Edges.** Noncountability rules out the empty class; `UUS` rules out finite or empty members. Both sides require enumeration coverage, with replay allowing generator-dependent extra values. Eventual correctness is at every time after a stream-dependent onset, without threshold or rate. The statement is not a nonuniform-threshold characterization.

### T6 / C05 — a conditional implication to the defined lower-bound proposition

`GenLimit.Replay.Results.theorem_7_1_of_algorithm3` — theorem; exported source anchor `GenLimit.Paper22_LanguageGenerationWithReplay.Results.Overview:90`. Exact kernel type: [declarations.jsonl line 113](../stage1/declarations.jsonl#L113) and the same identifier's section in [01-target-statements.md](../stage1/01-target-statements.md).

**Reconstruction.** Assume that for **every** adaptive membership algorithm `A` satisfying `U(A)`, an `Algorithm3Certificate A` is inhabited. Under that assumption, the proposition named `Theorem71Statement` holds: no adaptive membership algorithm satisfies `U(A)`.

**Skeleton.** `[∀A:ProperMembershipAlgorithm, U(A) → Nonempty(Algorithm3Certificate A)] → [¬∃A:ProperMembershipAlgorithm, U(A)]`.

**Information and dependencies.** All definitions of `U` and of the certificate, including the same-family/oracle/stream/output dependencies and its two alternative failure patterns, are expanded above. The assumption ranges over universal successful algorithms, already requiring ordinary computability and terminating executions on every relevant ordinary target presentation. Certificate inhabitation alone is not an effective construction. The theorem gives an implication; it does not supply its premise.

**Edges.** The premise is vacuous if there are no `U` algorithms. It is narrower than requiring certificates for all computable step functions. The success and certificate predicates here concern ordinary presentations with adaptive membership access, not replay enumeration. The supplied result must not be reported as an unconditional proof of the lower-bound proposition, nor as certified implementation of a named construction.

### T7 / C05 — denial of the broader certificate demand

`GenLimit.Replay.Results.theorem_7_1_overstrong_construction_is_false` — theorem; exported source anchor `GenLimit.Paper22_LanguageGenerationWithReplay.Results.Overview:97`. Exact kernel type: [declarations.jsonl line 114](../stage1/declarations.jsonl#L114) and the same identifier's section in [01-target-statements.md](../stage1/01-target-statements.md).

**Reconstruction.** It is false that every ordinarily computable `ProperMembershipAlgorithm` step function has an inhabited `Algorithm3Certificate`.

**Skeleton.** `¬[∀A:ProperMembershipAlgorithm, Computable A → Nonempty(Algorithm3Certificate A)]`.

**Information and dependencies.** The computational encoding is the supplied composition of natural, Boolean, product, list, and sum `Primcodable` instances. There is no successful-generation or round-termination premise in this denied broad demand. The certificate would nevertheless require one output at **every** time on its chosen stream. No particular counterexample algorithm is named in this theorem's exact type.

**Edges.** Native `queryForeverAlgorithm` has value `fun _ => Sum.inl (0,0)`: it always asks the same membership question and never returns the output constructor. Native theorem types separately state its computability and absence of `E` outputs. These are code-only supporting observations, not inspection/certification of those proofs. A total computable next-action map can therefore have no completed round. The theorem does not negate the narrower universal-algorithm premise in T6, and does not establish or refute `Theorem71Statement` by itself.

### T8 / C06 — a four-index proper replay impossibility family

`GenLimit.Replay.Results.theorem_7_3` — theorem; exported source anchor `GenLimit.Paper22_LanguageGenerationWithReplay.Results.Overview:102`. Exact kernel type: [declarations.jsonl line 115](../stage1/declarations.jsonl#L115) and the same identifier's section in [01-target-statements.md](../stage1/01-target-statements.md).

**Reconstruction.** There exists a family of integer languages indexed by `HardHypothesis` such that its index type has cardinality four, every indexed language is infinite, and no proper finite-history generator is eventually subset-correct on every proper replay enumeration for that family.

**Skeleton.** `∃family:HardHypothesis→Set Int, Fintype.card HardHypothesis=4 ∧ (∀i:HardHypothesis, Infinite(family i)) ∧ ¬∃g:ProperGenerator HardHypothesis Int, ∀target:HardHypothesis, ∀σ:Nat→Int, IsProperReplayEnumeration family g target σ → ∃T, ∀t≥T, family(h_g(σ,t)) ⊆ family target`.

**Information and dependencies.** The existential family is shared by infinitude and impossibility. A single candidate `g` would be chosen before all target indices and streams. Its output is a hypothesis index; its interpreted whole language is used both for subset correctness and for permission to replay an input. There is no computability restriction or explicit membership oracle. The named native family in the glossary is separate supporting evidence, not a name supplied for this target's existential witness.

**Edges.** Four is the cardinality of the index type; the endpoint does not separately assert pairwise distinct indexed languages or range cardinality four. Infinitude rules out success by selecting an empty indexed language. Proper correctness requires subset inclusion only, not equality or eventual stabilization to one index. Replay can introduce any point in a previously output language at time `0<k≤n`; the initial input must still belong to the target. Coverage of the target remains mandatory. This is a support-inclusion impossibility, not failure of scalar point freshness.

### T9 / C05 — the proposition `Theorem71Statement` itself

`GenLimit.Replay.Theorem71Statement` — definition; exported source anchor `GenLimit.Paper22_LanguageGenerationWithReplay.ProperMembershipLowerBound:151`. Exact kernel type: [declarations.jsonl line 116](../stage1/declarations.jsonl#L116) and the same identifier's section in [01-target-statements.md](../stage1/01-target-statements.md).

**Exact definition value.** `Not (∃ A, GenLimit.Replay.UniversalProperMembershipGenerator A)`; its exact type is `Prop`.

**Reconstruction and skeleton.** This definition names the proposition
`¬∃A:ProperMembershipAlgorithm, Computable A ∧ ∀family, IsRecursiveUUSFamily family → ProperlyGeneratesInLimitUsingMembership A family`.
The full expansion of recursive infinitude, membership access, finite executions, all-time output existence, and eventual subset correctness is in the glossary.

**Information and dependencies.** The hypothetical `A` is one uniform ordinary computable step function before all uniformly recursive infinite families; each queried family answers index/point membership. Correctness is eventually universal over all valid output indices at a time; total execution at every time is a separate conjunct. The target is a **definition**, not a proof that its proposition is true. T6 establishes this proposition only conditional on its displayed construction premise.

**Edges.** The family oracle must be jointly computable, but no code for that oracle is passed directly to `A`. Ordinary presentations, not replay streams, are quantified. No runtime/query-count rate, no convergence rate, no hypothesis equality, and no fresh scalar output is part of the proposition.

## Exhaustive coverage

| Slot | Exact reviewed declarations | Dossiers | Status |
|---|---|---|---|
| C01 | `GenLimit.Replay.Results.theorem_4_1` | T1 | All supplied endpoints reconstructed |
| C02 | `GenLimit.Replay.Results.theorem_5_1` | T2 | All supplied endpoints reconstructed |
| C03 | `GenLimit.Replay.Results.theorem_6_1`<br>`GenLimit.Replay.Results.theorem_6_1_finite_query` | T3, T4 | All supplied endpoints reconstructed |
| C04 | `GenLimit.Replay.Results.theorem_6_6` | T5 | All supplied endpoints reconstructed |
| C05 | `GenLimit.Replay.Results.theorem_7_1_of_algorithm3`<br>`GenLimit.Replay.Results.theorem_7_1_overstrong_construction_is_false`<br>`GenLimit.Replay.Theorem71Statement` | T6, T7, T9 | All supplied endpoints reconstructed |
| C06 | `GenLimit.Replay.Results.theorem_7_3` | T8 | All supplied endpoints reconstructed |

Each input slot has exactly one corresponding object in `stage1-claims.json`; shared definitions are expanded once above. All supplied identifiers have individual dossiers, including the `Prop` definition. There are zero no-endpoint slots and zero frozen-environment-absent linked names; no missing endpoint was replaced by a guessed source claim.

## Boundaries and limitations

The external boundary is Lean/Mathlib standard types, logic, finite sets/lists, countability, `Computable`/`Computable₂`, and the standard encodings explicitly listed in `external-boundary.txt`. Supplemental native transport/family values also use ordinary `Equiv`, `Set.image`/indexed unions, `Classical.choice`, `Denumerable.eqv`, integer casts/order/negation, and standard product/sum instances; these are trusted at their standard meanings, not recursively audited. Every `GenLimit.*` dependency appearing in the recursive package resolves within its 136 records; no unresolved project-specific definition prevents reconstruction. Concrete classical choices and all suppressed proof terms are unexamined, so no effective encoding or proof-body property is inferred from them.

The initial external directory listing described in the scope section is a recorded metadata-only deviation. All mathematical/algorithmic interpretation is grounded in Stage1 contents. Source anchors are exporter-provided locators; no source file was opened to validate them. The run does not certify source fidelity, fresh kernel checking, proof correctness, code executability, or any paper statement. Stage1 ends with these three outputs for coordinator validation/freezing; no later-stage input was accessed.
