# Stage 1: paper-withheld statement reconstruction

## Scope, inputs, and evidential limits

This report reconstructs exactly the six declarations in `stage1/targets.txt` from exported types and definition values. Identifiers and source paths are locators; their wording supplies no mathematical premise. The 30 declarations comprise six theorem types and 24 definition bodies. The theorem proof values are absent. This is a statement reconstruction, not a proof audit, compilation report, correspondence assessment, or human certification.

The only existing files read were the twelve files below, inside this package's `stage1/` directory. `01-target-statements.md` supplies target types; `02-definition-dependencies.md` supplies project definition bodies; `declarations.jsonl` supplies the same declarations in structured form and their dependency lists. The prompt and start file set the boundary. `external-constant-boundary.txt` declares assumed standard meanings. Snapshot and Lake files supply recorded provenance/configuration. No referenced source, paper, other stage, prior result, registry, or PaperMap was opened. No web or library-source lookup occurred.

All eleven entries in `SHA256SUMS` matched freshly computed SHA-256 hashes; its own hash is also recorded. Snapshot source-file hashes are provenance claims within that input, not independent verification of source files. The declared Lean version is `leanprover/lean4:v4.24.0`; the manifest records Mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. No Lean process or build was run.

| Accessible input | Bytes | SHA-256 |
|---|---:|---|
| `01-target-statements.md` | 3471 | `5e84bbab2fcdf1b8b866e2305cd0981f756df0be580d19e6fe06c389e9970e40` |
| `02-definition-dependencies.md` | 11336 | `6d0f420317fa0aa29a80902b61a1d9b4a375cdbe7b4e443cb21e11225037295c` |
| `PROMPT.md` | 1827 | `d79a9f3221e3fdc6cdb3835026d91ba49ca51b6fade5f30a27d10c5aba9eed4e` |
| `SHA256SUMS` | 928 | `e8c1b28d3d51deca5025eed87a86206d2d4c26a5bbf66adbbc8268373028d05f` |
| `START_HERE.md` | 189 | `bcead4a7e60afaa8e08ddf513c4d5c0a33a6967ab4d2a537f1b3ca6c98322860` |
| `declarations.jsonl` | 24145 | `4feea776bd68626977e0455dfb4c987e18580b347a662872b209db038b827eb9` |
| `external-constant-boundary.txt` | 734 | `dfd463992b31c9cf2199c8ac85d80a9cadbedfa22c9be3ffe174af45eb582c3b` |
| `lake-manifest.json` | 3100 | `994d8b6a379cea0e626d27fe8fa2fc74a2d966197a6998ecde6bd419634991aa` |
| `lakefile.toml` | 379 | `0fef48c5e314b7476f09da4caa5615d58a50937752aea1b192c0921a05b6e3d0` |
| `lean-toolchain` | 25 | `42779d67b81608af8a12aa4328d2ab47ca201925b3b2bd68369587b5340bb434` |
| `snapshot.json` | 10473 | `589055727297b71883793c91ecf3a8c74dbd6778c2e6dd2104eb1d47f427ba38` |
| `targets.txt` | 476 | `aec98c57258c490716290dbfc809c8d5698eb7dc46098f5a3694015396a3d6a0` |

The invocation is identified to this reviewer as model/configuration alias `gpt-6.1-sol`, reasoning effort `xhigh`, isolated with `fork_turns=none`. These are invocation labels, not independently observed backend identifiers. The backend revision is unknown.

## Definition glossary and shared conventions

Write `B` for `GenLimit.BreadthCharacterizations`, `A` for `GenLimit.Angluin`, and `Q` for `GenLimit.Generic`. The notation below expands supplied bodies. Ordinary Lean/Mathlib meanings of sets, finite sets, lists, natural numbers, subset, proper subset, finiteness, equality, and logic are assumed at the disclosed boundary. Every project dependency named by the export is present.

### G1. Languages, histories, and presentations

`Q.Language α = Set α`; `Q.LanguageFamily α = Nat → Set α`; `Q.Stream α = Nat → α`. A family is indexed by every natural number, without injectivity or effective membership assumptions. `Q.Presents s K` is exactly `Set.range s = K`: every observation belongs to `K`, and every member eventually appears. Observations may repeat with arbitrary delays. No pause or blank symbol is included in the stream type.

`GenLimit.textPrefix s t` is `List.map s (List.range t)`, the ordered list `[s 0, …, s (t−1)]`. It has length `t`, and is empty at `t=0`. `Q.sample s t` is `Finset.image s (Finset.range t)`. Write its underlying set as `D_s(t) = {s k | k<t}`. The sample forgets order and multiplicity; the list does not. Neither includes observation `s t`.

### G2. Outputs and available information

`B.SupportAlgorithm α = List α → Set α`. `B.supportAt G s t = G (GenLimit.textPrefix s t)`; abbreviate this by `S_G(s,t)`. Sets are supplied directly as function values. No probability law, distribution, sampler, full-support law, single generated point, loss function, or numerical error measure occurs. “Support” here means this explicit output set.

At a call, `G` receives precisely the ordered finite history. The target index, target set, future observations, and presentation proof are not arguments. Identical lists give identical outputs. An existential `G` can nevertheless depend on the fixed family and ambient parameters: it is chosen outside the target/presentation quantifiers. It is one uniform semantic function for the whole family, not a function chosen separately for each target or stream. No ordinary computability, effective enumeration, membership oracle, or oracle procedure is required. Countability is an ambient proposition/class assumption, not a supplied executable listing.

### G3. Four predicates at a time

The four correctness bodies, for target `K`, are:

* `B.ExactBreadthCorrectAt G K s t`: `S_G(s,t) = K \ D_s(t)`. The set contains exactly the unobserved target elements, excluding observed elements and everything outside the target.
* `B.ApproximateBreadthCorrectAt G K s t`: `S_G(s,t) ⊆ K ∧ Set.Finite (K \ S_G(s,t))`. It excludes outside-target elements and omits only finitely many target elements at that time. Observations may be included or omitted; no disjointness conjunct occurs.
* `B.WholeTargetCorrectAt G K s t`: `S_G(s,t) = K`, including all observations and all other target members.
* `B.InfiniteCoverageCorrectAt G K s t`: `S_G(s,t) ⊆ K ∧ (Disjoint (S_G(s,t)) D_s(t) ∧ Set.Infinite (S_G(s,t)))`. The three conjuncts require target membership, exclusion of all observations so far, and an infinite current output set. There is no equality with the unobserved part or finite omitted-complement requirement.

### G4. Eventual guarantees and stability

For each adjective `P` among ExactBreadth, ApproximateBreadth, WholeTarget, and InfiniteCoverage, `B.IsPGenerator G F` expands to

```text
∀ z : Nat, ∀ s : Nat → α,
  range(s) = F z →
  ∃ T : Nat, ∀ t : Nat, T ≤ t → P-at(G,F z,s,t).
```

This covers all four exported `Is…Generator` definitions. A threshold may depend on the target and presenting stream, as well as fixed family/function. It is not uniform over presentations or indices, has no bound, and imposes nothing before it. `B.ExactBreadthGeneratable F` and `B.ApproximateBreadthGeneratable F` each add an outer `∃ G : List α → Set α` to the respective predicate.

`B.IsStableGenerator G F` expands separately to

```text
∀ z : Nat, ∀ s : Nat → α,
  range(s) = F z →
  ∃ T : Nat, ∀ n n' : Nat,
    T ≤ n → T ≤ n' → S_G(s,n) = S_G(s,n').
```

Every pair of sufficiently late outputs must be equal as sets on each presentation. The eventual set may depend on the presentation. Stability alone imposes no correctness, nonemptiness, coverage, or equality across streams. A conjunction of stability with another generator predicate uses the same `G`, but gives two independently quantified thresholds. Both properties hold after their maximum; no named common threshold occurs in the original type.

### G5. Finite witnesses

For `T : Finset α`, with its coercion to a set understood, `A.IsTellTale F i T` is

```text
T ⊆ F i ∧
  ∀ j : Nat, T ⊆ F j → F j ⊆ F i → F i ⊆ F j.
```

Any family member containing `T` and contained in `F i` must equal `F i`. `A.ConditionTwo F` is `∀ i : Nat, ∃ T : Finset α, A.IsTellTale F i T`. Each witness may depend on `F` and `i`; it precedes the universal competitor `j`. This is existence, without an effective selection procedure.

`B.IsWeakTellTale F i T` aliases `Q.IsWeakTellTale F i T`, whose body is

```text
T ⊆ F i ∧
  ∀ j : Nat, T ⊆ F j → F j ⊂ F i → Set.Finite (F i \ F j).
```

The strict-subset premise and finite-difference conclusion are essential. `B.WeakAngluinCondition F` is `∀ i : Nat, ∃ T : Finset α, B.IsWeakTellTale F i T`. Neither condition bounds witness size, difference size, or selection time. Empty witnesses are allowed if their remaining implications hold. Duplicate indices denoting equal sets are legal: equality satisfies the strong conclusion and makes the weak strict-subset premise false.

## T1. Exact unobserved-target output and finite witnesses

**Exact identifier:** `GenLimit.BreadthCharacterizations.Results.theorem_3_3_semantic`  
**Exported source anchor:** `GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean:27` (locator only; source not opened).

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] [Countable.{u_1 + 1} α] (F : GenLimit.Generic.LanguageFamily.{u_1} α),
  (∀ (i : Nat), Set.Infinite.{u_1} (F i)) →
    Iff (GenLimit.BreadthCharacterizations.ExactBreadthGeneratable.{u_1} F) (GenLimit.Angluin.ConditionTwo.{u_1} F)
```

For every universe level, every nonempty countable alphabet, and every natural-number-indexed family whose members are all infinite, existence of an exact-breadth function is equivalent to the strong finite-witness condition in G5.

After the ambient binders and infinitude premise, the expanded skeleton is

```text
(∃ G : List α → Set α,
   ∀ z s, range(s)=F z → ∃ T, ∀ t, T≤t →
     S_G(s,t)=F z \ D_s(t))
↔
(∀ i, ∃ W : Finset α,
   W⊆F i ∧ ∀ j, W⊆F j → F j⊆F i → F i⊆F j).
```

Both implications are asserted. One function is chosen before any target or presentation; each finite witness is chosen after its own index and before every competitor. Neither side supplies a named executable witness or a computable conversion. The function sees only the finite history in G2; the witness is not handed to it as a call argument.

Removing a finite sample cannot exhaust an infinite target, so the eventual exact output is infinite. As new distinct observations arrive, their membership in the required unobserved remainder changes; this statement itself imposes no stability. Repetitions can leave the sample unchanged while changing the input list. No rate bounds the onset of exact equality, and nonpresenting streams are unconstrained. The explicit `Nonempty` and `Countable` binders remain in the exact signature even though the infinitude premise also rules out an empty alphabet.

## T2. Weak finite witnesses suffice for approximate output

**Exact identifier:** `GenLimit.BreadthCharacterizations.Results.theorem_3_8_sufficiency_semantic`  
**Exported source anchor:** `GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean:37` (locator only; source not opened).

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] (F : GenLimit.Generic.LanguageFamily.{u_1} α),
  (∀ (i : Nat), Set.Infinite.{u_1} (F i)) →
    GenLimit.BreadthCharacterizations.WeakAngluinCondition.{u_1} F →
      GenLimit.BreadthCharacterizations.ApproximateBreadthGeneratable.{u_1} F
```

For any countable alphabet and family of infinite members, the weak witness condition implies existence of one approximate-breadth function. This is only the displayed directed implication; no necessity or equivalence is asserted.

```text
∀ {α} [Countable α], ∀ F,
  (∀ i, Infinite(F i)) →
  (∀ i, ∃ W : Finset α,
     W⊆F i ∧ ∀ j, W⊆F j → F j⊂F i → Finite(F i \ F j)) →
  ∃ G : List α → Set α,
    ∀ z s, range(s)=F z → ∃ T, ∀ t, T≤t →
      (S_G(s,t)⊆F z ∧ Finite(F z \ S_G(s,t))).
```

The existential function may depend on the family and weak-condition hypothesis, but is chosen before the actual target or presentation. The finite witnesses are not input fields; there is no oracle argument. Unlike T1, the outer type has no explicit `Nonempty α` instance. Every indexed member must still be infinite.

The omitted finite set may vary over time and presentations. No common finite exceptional set or cardinality bound is specified. Including observed target elements is permitted. The type does not promise freshness of a selected output point, stability of the output sets, or monotonic reduction of omissions. On an infinite target, a subset with finite omitted complement is infinite, but that follows from the two stated conjuncts rather than a probability law. Empty or finite members violate the premise, so the theorem makes no claim about them.

## T3. Stable approximate output over natural numbers

**Exact identifier:** `GenLimit.BreadthCharacterizations.Results.theorem_3_15_approximate_semantic`  
**Exported source anchor:** `GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean:46` (locator only; source not opened).

```lean
∀ (F : GenLimit.Generic.LanguageFamily.{0} Nat),
  (∀ (i : Nat), Set.Infinite.{0} (F i)) →
    Iff
      (∃ G,
        And (GenLimit.BreadthCharacterizations.IsStableGenerator.{0} G F)
          (GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator.{0} G F))
      (GenLimit.Angluin.ConditionTwo.{0} F)
```

For a family of subsets of `Nat`, each infinite, existence of one function satisfying stability and approximate breadth is equivalent to the strong finite-witness condition. This type is specialized to `Nat`; it does not quantify over arbitrary countable alphabets.

After `∀ F` and the infinitude premise:

```text
(∃ G : List Nat → Set Nat,
   (∀ z s, range(s)=F z → ∃ T_st,
      ∀ n n', T_st≤n → T_st≤n' → S_G(s,n)=S_G(s,n')) ∧
   (∀ z s, range(s)=F z → ∃ T_ap,
      ∀ t, T_ap≤t →
        S_G(s,t)⊆F z ∧ Finite(F z \ S_G(s,t))))
↔
(∀ i, ∃ W : Finset Nat,
   W⊆F i ∧ ∀ j, W⊆F j → F j⊆F i → F i⊆F j).
```

The separate universal blocks are conjuncts under the same existential function. No privileged target or presentation is selected. The eventual constant set on each presentation is a subset of the target omitting finitely many members. It may include observations. Neither absence of omissions nor equality of eventual sets across presentations follows from what is written.

Only histories are passed to the function. This is a semantic existence equivalence without a named generator, effective selector, stabilization-time detector, or time bound. Infinite targets prevent the eventual approximate set from being empty. Repeated observations and duplicate family indices remain allowed. Dropping either conjunct, replacing the strong condition by the weak one, or generalizing the alphabet would alter the statement.

## T4. Stability and exact unobserved-target output

**Exact identifier:** `GenLimit.BreadthCharacterizations.Results.theorem_3_15_literal_exact_inconsistent`  
**Exported source anchor:** `GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean:57` (locator only; source not opened).

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] (F : GenLimit.Generic.LanguageFamily.{u_1} α),
  (∀ (i : Nat), Set.Infinite.{u_1} (F i)) →
    Not
      (∃ G,
        And (GenLimit.BreadthCharacterizations.IsStableGenerator.{u_1} G F)
          (GenLimit.BreadthCharacterizations.IsExactBreadthGenerator.{u_1} G F))
```

For every countable alphabet and every family of infinite members, no single support function has both the stability and exact-breadth properties. The negation covers the whole existential conjunction, rather than denying either property separately.

```text
∀ {α} [Countable α], ∀ F, (∀ i, Infinite(F i)) →
¬ ∃ G : List α → Set α,
  (∀ z s, range(s)=F z → ∃ T_st,
     ∀ n n', T_st≤n → T_st≤n' → S_G(s,n)=S_G(s,n')) ∧
  (∀ z s, range(s)=F z → ∃ T_ex,
     ∀ t, T_ex≤t → S_G(s,t)=F z \ D_s(t)).
```

Exactness requires excluding everything currently observed; stability requires eventual equality of all output sets along the presentation. A complete presentation eventually observes every target element, including elements previously in the unobserved remainder. This describes the semantic incompatibility being asserted, without inspecting or certifying a proof.

There is no finite-witness assumption, no existentially chosen difficult family, and no restriction to computable functions. The claim is nonexistence over all functions of G2's type for each family satisfying the hypotheses. It supplies no particular counterpresentation, failure time, or frequency of failure. The precise conclusion is failure of the conjunction of the two eventual predicates.

Repetitions may postpone new observations but cannot exhaust an infinite target with a finite prefix. When an alphabet admits no infinite subset, the infinitude premise is impossible and the implication is vacuous. `Countable α` is explicit; a `Nonempty α` instance is not. Finite and empty targets are outside scope, so their possible behavior does not qualify this conclusion.

## T5. Stable whole-target output and finite witnesses

**Exact identifier:** `GenLimit.BreadthCharacterizations.Results.theorem_3_15_corrected_wholeTarget_semantic`  
**Exported source anchor:** `GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean:68` (locator only; source not opened).

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] [Countable.{u_1 + 1} α] (F : GenLimit.Generic.LanguageFamily.{u_1} α),
  (∀ (i : Nat), Set.Infinite.{u_1} (F i)) →
    Iff
      (∃ G,
        And (GenLimit.BreadthCharacterizations.IsWholeTargetGenerator.{u_1} G F)
          (GenLimit.BreadthCharacterizations.IsStableGenerator.{u_1} G F))
      (GenLimit.Angluin.ConditionTwo.{u_1} F)
```

For nonempty countable alphabets and families of infinite members, existence of one whole-target function that is also stable is equivalent to the strong finite-witness condition. The exact type places the whole-target conjunct first and stability second.

After the ambient binders and infinitude premise:

```text
(∃ G : List α → Set α,
   (∀ z s, range(s)=F z → ∃ T_wh,
      ∀ t, T_wh≤t → S_G(s,t)=F z) ∧
   (∀ z s, range(s)=F z → ∃ T_st,
      ∀ n n', T_st≤n → T_st≤n' → S_G(s,n)=S_G(s,n')))
↔
(∀ i, ∃ W : Finset α,
   W⊆F i ∧ ∀ j, W⊆F j → F j⊆F i → F i⊆F j).
```

The eventual output equals the entire target, including every observed member. No sample subtraction or disjointness occurs. Whole-target correctness gives equality at every sufficiently late time; stability nevertheless appears as a second explicit conjunct, with its own quantifiers and threshold, which must be retained.

One function must work on all presentations throughout the family from histories alone. Finite witnesses are existential per index, not an extra input channel. Both directions assert semantic existence without specifying an effective learner, oracle contract, or method for recognizing the convergence time. Indices may repeat; thresholds need not agree across presentations or targets. Equality is exact, not equality modulo a finite difference. Infinitude excludes exhausted finite targets, while the explicit nonempty/countable binders remain. Nothing about an external specification or correction is inferred from the identifier.

## T6. Stability and infinite fresh coverage

**Exact identifier:** `GenLimit.BreadthCharacterizations.Results.proposition_8_10_literal_specification_inconsistent`  
**Exported source anchor:** `GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean:80` (locator only; source not opened).

```lean
∀ {α : Type u_1} [Countable.{u_1 + 1} α] (F : GenLimit.Generic.LanguageFamily.{u_1} α),
  (∀ (i : Nat), Set.Infinite.{u_1} (F i)) →
    Not
      (∃ G,
        And (GenLimit.BreadthCharacterizations.IsStableGenerator.{u_1} G F)
          (GenLimit.BreadthCharacterizations.IsInfiniteCoverageGenerator.{u_1} G F))
```

For every countable alphabet and family of infinite members, no function is both stable and an infinite-coverage generator. Coverage has exactly G3's three-part set meaning, with no probability interpretation.

```text
∀ {α} [Countable α], ∀ F, (∀ i, Infinite(F i)) →
¬ ∃ G : List α → Set α,
  (∀ z s, range(s)=F z → ∃ T_st,
     ∀ n n', T_st≤n → T_st≤n' → S_G(s,n)=S_G(s,n')) ∧
  (∀ z s, range(s)=F z → ∃ T_cov,
     ∀ t, T_cov≤t →
       S_G(s,t)⊆F z ∧
       (Disjoint(S_G(s,t),D_s(t)) ∧ Infinite(S_G(s,t)))).
```

All three coverage conjuncts lie inside the eventual universal-time guarantee. A candidate must eventually output infinitely many target elements and exclude every observation so far. Stability would fix this set along the presentation; completeness eventually observes each of its target elements. This explains the claimed incompatibility, without validating its proof.

No equality with the full unobserved remainder, cofinite complement, or enumeration of outputs is required. Arbitrary semantic functions are ruled out when they satisfy the conjunction. No strong or weak witness condition is assumed. Stability and coverage have separate presentation-dependent thresholds but refer to the same function. An empty output cannot satisfy the infinitude conjunct; omitting that conjunct changes the specification. No named counterexample, quantitative lower bound, rate, failure frequency, or executable adversarial strategy is exported.

## Exhaustive declaration coverage and remaining limits

The table accounts for every exported project declaration. Glossary locations cover the role of each dependency's type and the supplied body's meaning. Dossiers give exact target types and quantifier dependencies.

| Exact declaration | Role | Reconstruction |
|---|---|---|
| `GenLimit.textPrefix` | Definition | G1 |
| `GenLimit.Angluin.ConditionTwo` | Definition | G5 |
| `GenLimit.Angluin.IsTellTale` | Definition | G5 |
| `GenLimit.BreadthCharacterizations.ApproximateBreadthCorrectAt` | Definition | G3 |
| `GenLimit.BreadthCharacterizations.ApproximateBreadthGeneratable` | Definition | G4 |
| `GenLimit.BreadthCharacterizations.ExactBreadthCorrectAt` | Definition | G3 |
| `GenLimit.BreadthCharacterizations.ExactBreadthGeneratable` | Definition | G4 |
| `GenLimit.BreadthCharacterizations.InfiniteCoverageCorrectAt` | Definition | G3 |
| `GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator` | Definition | G4 |
| `GenLimit.BreadthCharacterizations.IsExactBreadthGenerator` | Definition | G4 |
| `GenLimit.BreadthCharacterizations.IsInfiniteCoverageGenerator` | Definition | G4 |
| `GenLimit.BreadthCharacterizations.IsStableGenerator` | Definition | G4 |
| `GenLimit.BreadthCharacterizations.IsWeakTellTale` | Definition | G5 |
| `GenLimit.BreadthCharacterizations.IsWholeTargetGenerator` | Definition | G4 |
| `GenLimit.BreadthCharacterizations.SupportAlgorithm` | Definition | G2 |
| `GenLimit.BreadthCharacterizations.WeakAngluinCondition` | Definition | G5 |
| `GenLimit.BreadthCharacterizations.WholeTargetCorrectAt` | Definition | G3 |
| `GenLimit.BreadthCharacterizations.supportAt` | Definition | G2 |
| `GenLimit.Generic.IsWeakTellTale` | Definition | G5 |
| `GenLimit.Generic.Language` | Definition | G1 |
| `GenLimit.Generic.LanguageFamily` | Definition | G1 |
| `GenLimit.Generic.Presents` | Definition | G1 |
| `GenLimit.Generic.Stream` | Definition | G1 |
| `GenLimit.Generic.sample` | Definition | G1 |
| `GenLimit.BreadthCharacterizations.Results.proposition_8_10_literal_specification_inconsistent` | Target | T6 |
| `GenLimit.BreadthCharacterizations.Results.theorem_3_15_approximate_semantic` | Target | T3 |
| `GenLimit.BreadthCharacterizations.Results.theorem_3_15_corrected_wholeTarget_semantic` | Target | T5 |
| `GenLimit.BreadthCharacterizations.Results.theorem_3_15_literal_exact_inconsistent` | Target | T4 |
| `GenLimit.BreadthCharacterizations.Results.theorem_3_3_semantic` | Target | T1 |
| `GenLimit.BreadthCharacterizations.Results.theorem_3_8_sufficiency_semantic` | Target | T2 |

In every target, presenting streams alone trigger the guarantees. Behavior on other inputs is unconstrained by these predicates. The family is indexed by `Nat`, so the index domain is never empty. Under the premises, no target is empty or finite, and no finite sample exhausts one. Without such premises, a presentation implication can be vacuous when no stream has the specified range; the report does not extend any theorem to that setting.

Every temporal assertion is eventual and then universal over all later times, or eventual pairwise equality. None is merely frequent, a limsup claim, an all-time guarantee, or convergence in probability. No rates, scales, numerical constants, bounded omissions, common stabilization times, or effective witness selectors occur in the conclusions. The remaining semantic boundary is the explicitly assumed standard Lean/Mathlib interface; no decisive project body is missing. Proof correctness, source correspondence, fresh compilation, human certification, and backend identity remain unverified by design. Both output files are frozen after local coverage/hash validation; no prior results were consulted.
