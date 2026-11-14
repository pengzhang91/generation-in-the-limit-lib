# Stage 1: paper-withheld Lean reconstruction

## Input census and evidential boundary

This reconstructs exactly the 13 declarations listed in `stage1/targets.txt`. Mathematical evidence consists solely of the supplied Stage 1 interface: original exported types, recursively relevant project definition values and constructors, and the initial explicit-type supplement. Identifiers and source anchors below locate that evidence; their names do not establish mathematical meaning. No source paper, owner material, later stage, PaperMap, registry interpretation, old audit, other package, raw library source, or theorem proof body was consulted. No Lean/Lake build, Git action, proof audit, or external mathematical lookup was performed.

Both manifests were verified before substantive reconstruction: all 13 entries in `stage1/SHA256SUMS` and both entries in `explicit-target-types/SHA256SUMS` matched their actual SHA256 hashes. There are 15 supplied files counting the two manifests themselves. The declaration export contains 152 unique records: 13 target theorems and 139 dependencies; by kind, 121 definitions, 27 theorems, two inductive structures, and two constructors. All theorem values are omitted. Every referenced `GenLimit.*` dependency in the supplied records is present. The original 13 types agree literally with the corresponding JSON strings, and the explicit supplement has precisely the same target set. Actual hashes, access sequence, configuration visibility, and the report hash are in `stage1-run.json`.

The two Markdown exports are `01-target-statements.md` and `02-definition-dependencies.md`; `declarations.jsonl` additionally supplies dependency edges. `explicit-target-types/{README.md,types.jsonl}` exposes implicit applications but retains some notation. `external-constant-boundary.txt` authorizes standard Lean/Mathlib meanings for sets, finite sets, natural-number encodings, choice, floor, filters, liminf/limsup, and the other listed external constants. `snapshot.json` records a dirty working-tree byte snapshot at Git head `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`; this is metadata, not an independently verified source correspondence. The supplied toolchain is Lean 4.24.0 and the supplied Lake metadata selects Mathlib v4.24.0. Those metadata files were read, not executed.

The exact original target types are quoted below, including printed universes and proof ellipses. An ellipsis inside a definition denotes an omitted proof term, not a missing Lean proof. Relevant existential predicates are recovered from their exported theorem types and dependency edges. No decisive project definition remains missing. Standard boundary meanings are assumed, rather than recursively audited. The report interprets the exported interface; it does not certify proof correctness, consistency, compilation, source-paper fidelity, effectiveness, or human review.

## Definition glossary and dependency anchors

The following notation is only a shorthand for the supplied defining expressions. Write `L_i` for a family member, `s` for a stream, `S_t={s(0),…,s(t−1)}` for its distinct observed values, `g_t=g t (s|Fin t)` for an element output, and `A_t=G t (s|Fin t)` for a set output. All thresholds in eventual statements are natural numbers.

**D1 — Domains, finite information, and oracles.** `Generic.Language α=Set α`, `LanguageClass α=Set (Set α)`, and `Stream α=Nat→α`. A finite-history operator has type `(t:Nat)→(Fin t→Input)→Output`. Thus an element generator outputs one element and a set generator outputs a mathematical set, after receiving the ordered history of length exactly `t`. The current observation `s(t)` is not included. `sample` and `sequenceSample` discard repetitions by finite-set image. Anchors: `Core/GenericGeneration.lean:21,24,31,37,41,58,63,87`, `Core/SetGeneration.lean:19,30`, under `GenLimitLean/GenLimit/`. An infinite set generator outputs an infinite set on **every** finite history, including inadmissible histories and the empty one.

`GenLimit.Language=Set Nat` and `LanguageFamily=Nat→Set Nat` (`Core/Basic.lean:20,23`). The constructor `OracleFamily.mk` takes this family, a proof that every member is infinite, a function `query:Nat→Nat→Bool`, and a proof that `query i x=true ↔ x∈L_i` (`Core/OracleFamily.lean:17`). It supplies exact Boolean membership, but no machine program, recursive index, time bound, or formal reducibility certificate. The targets assert properties of functions; the word “generator,” even when named, does not add ordinary or relative computability. Arbitrary language predicates, infinitude tests, real densities, and classical choice occur in their values.

**D2 — Contamination and omissions.** `noiseCount(s,L,n)` counts **indices** `j<n` with `s(j)∉L`; `empiricalNoiseRate` is this count divided by `n`, with value zero at `n=0`. `NoNoise` means `range(s)⊆L`. `FiniteNoise` means the set of bad indices is finite. `VanishingNoise` means the real empirical rate tends to zero at infinity. `ConstantNoise(s,L,c)` means `∃N ∀n≥N, rate(n)≤c`; it is an eventual bound, not merely a limsup bound allowing persistent overshoot. `FiniteOmissions` means `Lange(s)` is finite. `ArbitraryOmissions` means `range(s)∩L` is infinite; it imposes no bound on how many target elements are absent. The vanishing/constant arbitrary-omission enumeration predicates conjoin stream injectivity, this infinite intersection, and their respective noise condition. The finite-noise finite-omission enumeration conjoins injectivity, finite bad indices, and finite omissions. Anchors: `Paper17_InfiniteContamination/Definitions.lean:36,54,100–147,206,214,234`; finite violations also unfold through `Core/FiniteContamination.lean:171,176`.

**D3 — Correctness and freshness.** Element correctness at time `t` conjoins `g_t∈L`, `g_t∉S_t`, and `g_t` unequal to **every** earlier output, including outputs from an erroneous initial period. `GeneratesElementInLimitOn` means `∃T ∀t≥T` this full conjunction. Set correctness conjoins `A_t⊆L` and `A_t∩S_t=∅`; it has no freshness condition relative to earlier output sets. Set generation in the limit is eventual set correctness. Infinite set generation additionally conjoins the global all-history infinitude from D1, not just eventual infinitude on the stream in question. Neither notion forbids an output from becoming a future observation. Anchors: `Definitions.lean:250,267,278,285,290,294,307`, `SetDensityObstruction.lean:27,36`.

**D4 — Two spatial densities and two temporal set densities.** `OrderedLanguage.mk` takes a carrier `K⊆Nat`, an injective enumeration `e:Nat→Nat`, and `range(e)=K` (`Core/OrderedDensity.lean:24`). Hence every such carrier is infinite. Set density uses this supplied enumeration, which need not increase in the ambient natural-number order. Its prefix count is `#{j<n:e(j)∈A}`; the prefix ratio is count/n, zero at zero. Write `d⁻_K(A)=liminf_n ratio` and `d⁺_K(A)=limsup_n ratio` (`:33,197,233,237`). These ratios lie between zero and one even for sets with elements outside the carrier.

`setBasedLowerDensity(G,K,s)=liminf_t d⁻_K(A_t)`; `setBasedUpperDensity(G,K,s)=limsup_t d⁻_K(A_t)`. In particular, the latter still uses **lower** spatial density inside its time limsup (`SetDensityObstruction.lean:83,90`). Element densities instead are `d⁻_K({g_t:t∈Nat})` and `d⁺_K({g_t:t∈Nat})`: density of the full output range, not a time-frequency ratio, and not a sum of per-round supports (`ElementDensity.lean:36–56`). `ElementDensityGuaranteeOn` asserts both `ρlow≤elementBasedLowerDensity` and `ρup≤elementBasedUpperDensity`; both parameters are **lower bounds**, not an upper cap (`:253`). `OmissionsAtMost(s,K,c)` is `1−c≤d⁻_K(range(s)∩K)` (`Definitions.lean:147`). No timing or coverage beyond that inequality is implicit.

**D5 — Finite intersections and expansion coding.** `finiteCommonCore(S)={x:∀L∈S,x∈L}` and `indexedLanguages(f,I)=image(f,I)` (`VanishingNoise.lean:80`, `PriorityStabilization.lean:366`). An empty intersection is the whole ambient type; repeated indices are disallowed by finite sets, while repeated language values are deduplicated without changing the intersection. Finite expansion is `(L∪add)emove`. Decode `j` by two `Nat.unpair` operations into `(base,(a,r))`; use `Finset.equivBitIndices` to obtain finite addition/removal sets. The expanded family at `j` is this expansion of `O.language base`; its oracle constructor includes an infinitude certificate and exact membership query. `finiteExpansionMeasure orders j` is the original order at that base index, not the expanded carrier's order. Anchors: `FiniteExpansionTransfer.lean:29`, `FiniteContaminationSufficiency.lean:27,31,46,50,57,69,138`.

**D6 — Named set generators.** Algorithm Five, at time `t`, considers indices `i<t` whose language contains all observations so far. For `k≤t`, take the active indices below `k`; require that activity below `k` agrees at times `t` and `t−1` (natural subtraction) and that their common core is infinite. Choose the greatest such `k`, intersect those languages, and delete the observed finite set. Its finite history is completed with zeros solely to evaluate the stream-based definitions. The `k=0` core on `Nat` is universal, so that empty prefix is available. Anchors: `AlgorithmFive.lean:29,46,64,72,85,170,236`. The generator value uses the family predicates; no implementation from oracle queries alone is asserted.

Algorithm Nine defines threshold `ε·(1/2)^(i+1)`. Its good-at test at prefix length `n` requires empirical noise at most that threshold and maximum canonical carrier rank among the first `n` observations at most `M·n`. A diagnostic is zero on success and one on failure. A penalty is `max(1,max{m+1:m≤n and diagnostic(m)>0})`, with empty finite supremum zero; priority score is `i+penalty`. Rank candidates `i<n` lexicographically by `(score(i),i)`. Choose the largest prefix size `k≤n` whose common core has lower density at least `(1−ε)/M` in every selected order. An empty prefix passes that test vacuously. Output that intersection minus the observed finite set. All history scores use completion by zeros. Anchors: `AlgorithmNine.lean:27,67,144,155,163,456,517,541,631,641`; ranking at `AlgorithmFour.lean:45,61,68,74,646`; maximal dense prefix at `AlgorithmSixSeven.lean:302,312,331`; penalty at `PriorityStabilization.lean:46`.

**D7 — Set-to-element conversion.** `SetCoreSelectionInvariant` quantifies over every finite history: its set output lies in the common core of all indices selected there, after deleting observed values (`AlgorithmEight.lean:686`). The selected finite set can be empty. `InheritsAmbientOrder(K)` means precisely `StrictMono K.enumeration`, an additional increasing-order condition (`Support/KleinbergWei/OrderedPositions.lean:18`). For stage `s`, slack is `δ_s=1+(1/2)^(s+1)`. A classically chosen density cutoff ensures `d⁻_K(A)/δ_s≤prefixRatio(K,A,m)` for every `m` beyond that cutoff (`AlgorithmEight.lean:38,59,87`); dependency edges identify this existential predicate despite the printed proof ellipsis. Take the finite supremum of these cutoffs across the stage's selected indices, with that stage's set output as `A` (`:100,119`).

At time `t`, an admissible stage is zero or satisfies `cutoff_s/δ_s≤2(t+1)/ρ`. Select the greatest admissible stage at most `t` (`:130,142,153`). With the current history completed by zeros, use that earlier stage's set output as the chosen infinite set (`:225,296`). The well-founded recursive output selects its least natural number outside both current observations and outputs recursively produced from all shorter restricted histories. The exported helper types certify infinitude and existence of such a number; no helper proof values were read (`:306,331`, generated `algorithmEightOutput._unary` and `_proof_1` through `_proof_5`). Thus this is a particular mathematically defined history operator, depending on the supplied set generator, infinitude proof, selection, orders, and `ρ`; its classical cutoff selection prevents an effectiveness claim from following just from its syntax.

**D8 — Rank, displacement, and empirical target ratios.** `canonicalIndex K x` is the least enumeration position of `x` if `x∈K`, and zero otherwise; the exported existence-helper type supplies its enumeration witness. `canonicalRank K L x` is zero if `x∉L`, and otherwise `prefixCount K L (canonicalIndex K x+1)`. If `x∈L` but lies outside `K`, this definition still counts the first enumeration position; it must not be replaced by an intended rank outside its domain. `BoundedDisplacement(K,s,L,M)` means `∃N ∀n≥N, rank(K,L,s(n))≤M·(n+1)` in the reals (`BoundedDisplacement.lean:38,57,95`). The empirical target count is `#(S_n∩L)`, counting distinct observed **values**, and its ratio is that count/n, zero at zero (`:125,680`). These definitions impose no injectivity unless the target type separately says so.

## Target dossiers

Each quantifier skeleton abbreviates the fully quoted original type using D1–D8. “Uniform” describes only quantifier order and shared function identity. Every eventual threshold can depend on the universally fixed data, the generator, target, and stream occurring before it; no explicit convergence rate or computable threshold is asserted.

### `GenLimit.InfiniteContamination.Results.theorem_5_1`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:117`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.theorem_5_1`.

Original target type, verbatim:

```lean
∀ {α : Type u_1} (family : Nat → GenLimit.Generic.Language.{u_1} α),
  (∀ (i : Nat), Set.Infinite.{u_1} (family i)) →
    ∃ gen,
      ∀ (target : Nat) (stream : GenLimit.Generic.Stream.{u_1} α),
        GenLimit.InfiniteContamination.VanishingNoiseArbitraryOmissionEnumeration.{u_1} stream (family target) →
          GenLimit.InfiniteContamination.GeneratesElementInLimitOn.{u_1} gen (family target) stream
```

**Reconstruction.** For every type `α` and every natural-number-indexed family of infinite subsets of `α`, there exists one element history operator that works for every target index and every injective stream having infinitely many distinct observed target values and vanishing empirical noise. On each such stream, from some time onward every output belongs to the target, is absent from the observed prefix, and differs from all earlier outputs.

**Quantifier skeleton.** `∀α ∀family, (∀i Infinite L_i) → ∃g ∀z ∀s, [Injective s ∧ Infinite(range s∩L_z) ∧ rate→0] → ∃T ∀t≥T, [g_t∈L_z ∧ g_t∉S_t ∧ g_t∉{g_r:r<t}]`.

**Dependencies, information, and edges.** D1–D3 expand every predicate. The witness can depend on the whole family; it is chosen before the target and stream and receives only finite history when applied. No oracle, countability of `α`, effective family enumeration, ordinary program, or named witness is required. Infinitely many omitted target elements are permitted, with no prescribed coverage rate. Repetitions in the family are permitted; stream repetitions are forbidden. Empty or finite targets, and finite ambient types supporting no infinite family, cannot satisfy the infinitude premise. Freshness concerns observed history, not future observations.


### `GenLimit.InfiniteContamination.Results.theorem_5_4`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:131`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.theorem_5_4`.

Original target type, verbatim:

```lean
∀ {α : Type u_1} (C : GenLimit.Generic.LanguageClass.{u_1} α) (c : Real),
  LT.lt.{0} 0 c →
    LT.lt.{0} c 1 →
      ∀ (family : Nat → GenLimit.Generic.Language.{u_1} α),
        (∀ (i : Nat), Set.Infinite.{u_1} (family i)) →
          (∀ (i : Nat), Membership.mem.{u_1, u_1} C (family i)) →
            (∀ (L : GenLimit.Generic.Language.{u_1} α),
                Membership.mem.{u_1, u_1} C L → ∃ i, Eq.{u_1 + 1} (family i) L) →
              Iff (∃ gen, GenLimit.InfiniteContamination.GeneratesUnderConstantNoise.{u_1} gen C c)
                (GenLimit.InfiniteContamination.ConstantNoiseGenerationProperty.{u_1} C c)
```

**Reconstruction.** Fix a class `C` of subsets of an arbitrary type and a real `0<c<1`. Supply a natural-number-indexed family of infinite members of `C` that covers every member of `C`. A single element generator handles every member and every constant-noise arbitrary-omission enumeration exactly when every nonempty finite collection of members admitting one shared such stream has infinite common intersection.

**Quantifier skeleton.** After `∀α,C,c,family` and the bounds, infinitude, membership, and surjectivity hypotheses: `[∃g ∀L∈C ∀s, admissible_c(s,L) → eventualFresh(g,L,s)] ↔ [∀S:Finset(Set α), S.Nonempty → S⊆C → ∀s, (∀L∈S admissible_c(s,L)) → Infinite(⋂S)]`.

**Dependencies, information, and edges.** `GeneratesUnderConstantNoise` and `ConstantNoiseGenerationProperty` at `ConstantNoiseNecessity.lean:108,117`, together with D1–D3 and D5, give precisely this equivalence. The finite collection is a set of languages, not of indices or samples. The stream is shared across all its members; if no shared stream exists, that instance is vacuous. The family need not be injective and can repeat a finite nonempty class. Its membership hypothesis rules out an empty class; all class members are infinite by coverage. The output witness precedes both language and stream, but its existence supplies neither a named construction nor a computable procedure. No density condition on the common intersection beyond infinitude is present.


### `GenLimit.InfiniteContamination.Results.theorem_6_1`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:148`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.theorem_6_1`.

Original target type, verbatim:

```lean
∀ (O : GenLimit.OracleFamily) (orders : Nat → GenLimit.KleinbergWei.OrderedLanguage),
  (∀ (i : Nat),
      Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders i)) (GenLimit.OracleFamily.language O i)) →
    ∀ (z : Nat) (c : Real) {stream : GenLimit.Generic.Stream.{0} Nat},
      Function.Injective.{1, 1} stream →
        GenLimit.InfiniteContamination.FiniteNoise.{0} stream (GenLimit.OracleFamily.language O z) →
          GenLimit.InfiniteContamination.OmissionsAtMost stream (orders z) c →
            And
              (GenLimit.InfiniteContamination.GeneratesInfiniteSetInLimitOn.{0}
                (GenLimit.InfiniteContamination.algorithmFiveGenerator
                  (GenLimit.OracleFamily.language (GenLimit.InfiniteContamination.finiteExpansionOracleFamily O)))
                (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders z)) stream)
              (LE.le.{0} (HSub.hSub.{0, 0, 0} 1 c)
                (GenLimit.InfiniteContamination.setBasedUpperDensity
                  (GenLimit.InfiniteContamination.algorithmFiveGenerator
                    (GenLimit.OracleFamily.language (GenLimit.InfiniteContamination.finiteExpansionOracleFamily O)))
                  (orders z) stream))
```

**Reconstruction.** Given an oracle family and matching ordered carriers, fix any target `z`, real `c`, and injective stream with finitely many bad indices and `d⁻` of its observed target portion at least `1−c`. Algorithm Five applied to the finitely expanded oracle family's languages is an infinite set generator, eventually outputs only unobserved target elements, and has time limsup of its outputs' lower spatial densities at least `1−c` in the original target order.

**Quantifier skeleton.** `∀O,orders, matching → ∀z,c,s, Injective s → FiniteNoise(s,L_z) → [1−c≤d⁻_z(range s∩L_z)] → [GlobalInfinite(G5) ∧ ∃T ∀t≥T SetCorrect(G5,L_z,s,t)] ∧ [1−c≤limsup_t d⁻_z(A_t)]`.

**Dependencies, information, and edges.** D1–D6 define the named witness `G5=algorithmFiveGenerator((finiteExpansionOracleFamily O).language)`. Its value depends on `O`'s languages, not on the target, `c`, or the orders used to assess it. Oracle-family membership correctness and infinitude are supplied structure data, not a computability theorem. There is no finite-omission or full-presentation assumption: infinitely many target values may be omitted. There is no `0<c<1` premise. Negative `c` makes the omission inequality infeasible; `c≥1` makes its numerical demand nonpositive. The global infinite-output conjunct remains substantive. The density conclusion is a time limsup, not an eventual per-time lower bound; set outputs may overlap earlier output sets.


### `GenLimit.InfiniteContamination.Results.theorem_6_4`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:170`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.theorem_6_4`.

Original target type, verbatim:

```lean
∀ (c : Real) (hc0 : LT.lt.{0} 0 c) (hc1 : LT.lt.{0} c 1) (ε : Real),
  LT.lt.{0} 0 ε →
    ∀ (gen : GenLimit.InfiniteContamination.SetGenerator.{0} Nat),
      Not
        (GenLimit.InfiniteContamination.GuaranteesSetBasedUpperDensityUnderOmissionsOn.{1} gen
          (GenLimit.InfiniteContamination.theoremSixFourFamily (HSub.hSub.{0, 0, 0} 1 c))
          (GenLimit.InfiniteContamination.theoremSixFourOrders (HSub.hSub.{0, 0, 0} 1 c) ⋯ ⋯) c
          (HAdd.hAdd.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 c) ε))
```

**Reconstruction.** For every `0<c<1`, every `ε>0`, and every set history operator, it fails to guarantee both eventual set correctness and time-upper set density at least `1−c+ε` on all eligible omission streams for a specific two-member family. Its index type is **Bool**, as the explicit application and exported family type confirm. At `true` the language is all naturals with identity enumeration. At `false` it is `F_p={n:floor(p(n+1))=floor(pn)+1}`, with `p=1−c` and enumeration `Nat.nth (·∈F_p)`.

**Quantifier skeleton.** `∀c hc0 hc1 ε, ε>0 → ∀G, ¬[∀b:Bool ∀s, Injective s → range(s)⊆L_b → 1−c≤d⁻_b(range s∩L_b) → (eventualSetCorrect ∧ 1−c+ε≤limsup_t d⁻_b(A_t))]`.

**Dependencies, information, and edges.** D2–D4, `GuaranteesSetBasedUpperDensityUnderOmissionsOn` (`SetDensityObstruction.lean:323`), the family/orders (`:337,341`), and floor construction (`:157,261,278`) resolve all domains. `hc0,hc1` support the order constructor's positive-`p`, `p≤1` proofs; these proof arguments add no new assumption. Streams here have **no** noise at any time, not merely finite or vanishing noise. The theorem is a negated universal guarantee; it supplies no named failing index or stream. It does not assume global infinite set outputs. Empty outputs can satisfy correctness but cannot meet this positive bound. No exact density formula for `F_p` is needed or silently imported to identify the constructed family.


### `GenLimit.InfiniteContamination.Results.theorem_6_5`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:183`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.theorem_6_5`.

Original target type, verbatim:

```lean
∀ (O : GenLimit.OracleFamily) (orders : Nat → GenLimit.KleinbergWei.OrderedLanguage),
  (∀ (i : Nat),
      Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders i)) (GenLimit.OracleFamily.language O i)) →
    ∀ (c : Real),
      Iff
        (∃ gen,
          And (GenLimit.InfiniteContamination.IsInfiniteSetGenerator.{0} gen)
            (∀ (z : Nat),
              And
                (GenLimit.InfiniteContamination.GeneratesSetUnderFiniteContaminationOn.{0} gen
                  (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders z)))
                (GenLimit.InfiniteContamination.GuaranteesSetBasedLowerDensityUnderFiniteContaminationOn gen (orders z)
                  c)))
        (∀ (i j : Nat),
          Set.Finite.{0} (SDiff.sdiff.{0} (GenLimit.OracleFamily.language O i) (GenLimit.OracleFamily.language O j)) →
            LE.le.{0} c
              (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity (orders j) (GenLimit.OracleFamily.language O i)))
```

**Reconstruction.** For any oracle family, matching orders, and unrestricted real `c`, there exists one globally infinite set generator that, for every target, generates eventually correct fresh sets under finite-noise finite-omission injective enumeration and guarantees time-lower set density at least `c`, if and only if every ordered pair `(i,j)` with `L_i\L_j` finite satisfies `c≤d⁻_{orders j}(L_i)`.

**Quantifier skeleton.** `∀O,orders, matching → ∀c, [∃G, GlobalInfinite(G) ∧ ∀z, (∀s admissible_fin(s,L_z) → eventualSetCorrect) ∧ (∀s admissible_fin(s,L_z) → c≤liminf_t d⁻_z(A_t))] ↔ [∀i,j, Finite(L_i\L_j) → c≤d⁻_j(L_i)]`.

**Dependencies, information, and edges.** `GeneratesSetUnderFiniteContaminationOn` and `GuaranteesSetBasedLowerDensityUnderFiniteContaminationOn` (`FiniteContaminationNecessity.lean:33,60`) unfold via D1–D5. The direction of the difference and the measuring order are essential: almost-containment is from `i` into `j`, and density is measured along `j`. The generator precedes all targets and both universal stream obligations. No effective construction is stated. No `c>0` is assumed; for nonpositive `c` the density inequality adds no positive requirement, but correctness and infinitude remain. Taking `i=j` forces `c≤1`, so a larger value cannot satisfy the right side. Oracle and order constructors exclude finite or empty target languages; repeated family values remain allowed.


### `GenLimit.InfiniteContamination.Results.theorem_6_11`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:203`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.theorem_6_11`.

Original target type, verbatim:

```lean
∀ (family : Nat → GenLimit.Generic.Language.{0} Nat),
  (∀ (i : Nat), Set.Infinite.{0} (family i)) →
    ∀ (orders : Nat → GenLimit.KleinbergWei.OrderedLanguage),
      (∀ (i : Nat), Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders i)) (family i)) →
        ∀ (ρ : Real),
          Iff (∃ gen, GenLimit.InfiniteContamination.GeneratesSetDensityUnderVanishingNoise gen family orders ρ)
            (GenLimit.InfiniteContamination.VanishingNoiseDenseSetCondition family orders ρ)
```

**Reconstruction.** For a natural-number family of infinite sets and matching orders, and any real `ρ`, uniform infinite set generation with time-lower density at least `ρ` on every vanishing-noise arbitrary-omission enumeration is equivalent to this finite-intersection condition: every nonempty finite set of indices whose common core is infinite has that core's lower density at least `ρ` in each selected index's order.

**Quantifier skeleton.** `∀family, infinite → ∀orders, matching → ∀ρ, [∃G, GlobalInfinite(G) ∧ ∀z,s, admissible_vanish(s,L_z) → (eventualSetCorrect ∧ ρ≤liminf_t d⁻_z(A_t))] ↔ [∀I:Finset Nat, I.Nonempty → Infinite(core(I)) → ∀i∈I, ρ≤d⁻_i(core(I))]`.

**Dependencies, information, and edges.** `GeneratesSetDensityUnderVanishingNoise` and `VanishingNoiseDenseSetCondition` (`AlgorithmSixSeven.lean:106,95`), D1–D5. The condition contains no stream quantifier: infinitude of the core is its explicit trigger. A finite or empty common intersection imposes no condition, although individual members are infinite. Empty index sets are excluded; duplicate language values do not change the core. No positivity assumption on `ρ` may be inserted. If `ρ≤0`, the density demands are numerically automatic; for `ρ>1`, singleton index sets obstruct the right side. The generator is one semantic witness chosen before all targets and streams; per-stream thresholds need not be uniform or computable. Its sets are infinite on invalid histories too.


### `GenLimit.InfiniteContamination.Results.theorem_6_14`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:218`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.theorem_6_14`.

Original target type, verbatim:

```lean
∀ (family : Nat → GenLimit.Generic.Language.{0} Nat),
  (∀ (i : Nat), Set.Infinite.{0} (family i)) →
    ∀ (orders : Nat → GenLimit.KleinbergWei.OrderedLanguage),
      (∀ (i : Nat), Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders i)) (family i)) →
        ∀ (c ρ : Real),
          LT.lt.{0} 0 c →
            LT.lt.{0} c 1 →
              LT.lt.{0} 0 ρ →
                Iff (∃ gen, GenLimit.InfiniteContamination.GeneratesSetDensityUnderConstantNoise gen family orders c ρ)
                  (GenLimit.InfiniteContamination.ConstantNoiseDenseSetCondition family orders c ρ)
```

**Reconstruction.** Given an infinite indexed family, matching orders, `0<c<1`, and `ρ>0`, one globally infinite set generator succeeds on every constant-noise arbitrary-omission enumeration with time-lower density at least `ρ` if and only if every nonempty finite index set and every stream simultaneously admissible for all of those indices has common-core lower density at least `ρ` in every selected order.

**Quantifier skeleton.** After the family/order hypotheses and real bounds: `[∃G, GlobalInfinite(G) ∧ ∀z,s, admissible_c(s,L_z) → (eventualSetCorrect ∧ ρ≤liminf_t d⁻_z(A_t))] ↔ [∀I, I.Nonempty → ∀s, (∀i∈I admissible_c(s,L_i)) → ∀i∈I, ρ≤d⁻_i(core(I))]`.

**Dependencies, information, and edges.** `GeneratesSetDensityUnderConstantNoise` and `ConstantNoiseDenseSetCondition` (`AlgorithmSixSeven.lean:385,372`), D1–D5. Unlike the preceding target's condition, this one quantifies over a shared stream and has no separate infinite-core premise. It may be vacuous for an index set admitting no such stream. Where applicable, the positive density demand excludes a finite core. Every admissible stream is injective, observes infinitely many values from each relevant target, and eventually has noise rate at most `c` relative to each one; neither full coverage nor finite omissions follows. The existential generator is uniform over targets and streams, with family/orders/`c`/`ρ` available as mathematical parameters. No upper restriction `ρ≤1` or computational certificate appears among the hypotheses.


### `GenLimit.InfiniteContamination.Results.theorem_6_15`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:236`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.theorem_6_15`.

Original target type, verbatim:

```lean
∀ (setGen : GenLimit.InfiniteContamination.SetGenerator.{0} Nat)
  (hinfinite : GenLimit.InfiniteContamination.IsInfiniteSetGenerator.{0} setGen) (family : Nat → Set.{0} Nat)
  (selection : (t : Nat) → (Fin t → Nat) → Finset.{0} Nat) (orders : Nat → GenLimit.KleinbergWei.OrderedLanguage)
  (ρ : Real),
  LT.lt.{0} 0 ρ →
    GenLimit.InfiniteContamination.SetCoreSelectionInvariant setGen family selection →
      (∀ (i : Nat), Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders i)) (family i)) →
        (∀ (i : Nat), GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.InheritsAmbientOrder (orders i)) →
          ∀ (target : Nat) (stream : GenLimit.Generic.Stream.{0} Nat),
            (∃ N, ∀ (t : Nat), LE.le.{0} N t → Membership.mem.{0, 0} (selection t fun i => stream ↑i) target) →
              (∃ N,
                  ∀ (t : Nat),
                    LE.le.{0} N t →
                      LE.le.{0} ρ
                        (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity (orders target)
                          (GenLimit.InfiniteContamination.setOutput.{0} setGen stream t))) →
                And
                  (GenLimit.InfiniteContamination.GeneratesElementInLimitOn.{0}
                    (GenLimit.InfiniteContamination.algorithmEightGenerator setGen hinfinite selection orders ρ)
                    (family target) stream)
                  (LE.le.{0} (HDiv.hDiv.{0, 0, 0} ρ 2)
                    (GenLimit.InfiniteContamination.elementBasedLowerDensity
                      (GenLimit.InfiniteContamination.algorithmEightGenerator setGen hinfinite selection orders ρ)
                      (orders target) stream))
```

**Reconstruction.** Supply a globally infinite set generator and its infinitude proof, a family, finite-index selection operator, orders, and `ρ>0`. Require the all-history core-selection invariant, matching carriers, and increasing ambient order for every enumeration. For every target and stream, if that target is selected eventually and its set outputs eventually each have lower density at least `ρ`, the particular Algorithm Eight element generator eventually outputs target elements fresh from both observations and prior outputs, and its entire output range has lower density at least `ρ/2`.

**Quantifier skeleton.** `∀G,h∞,family,selection,orders,ρ, ρ>0 → invariant → matching → increasing → ∀z,s, [∃N₁ ∀t≥N₁ z∈selection(t,s|t)] → [∃N₂ ∀t≥N₂ ρ≤d⁻_z(A_t)] → [∃T ∀t≥T FreshElementCorrect] ∧ [ρ/2≤d⁻_z(range(outputs))]`.

**Dependencies, information, and edges.** D1, D3–D5, D7 specify both hypotheses and the fixed named output. The two eventual witnesses can differ; no common initial threshold was assumed. There is no stream injectivity, noise, omission, or presentation hypothesis. The orders' constructors already force every family member infinite; a separate family-infinitude premise is absent. The element generator depends on the globally supplied data and `ρ`, preceding `z,s`, and receives finite history only. Positive density above one makes the eventual density premise infeasible. Empty selections are allowed on initial or unrelated histories, but eventual target selection rules them out eventually on this stream. Increasing enumeration is a real additional hypothesis here, not part of every ordered language.


### `GenLimit.InfiniteContamination.Results.corollary_6_16`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:265`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.corollary_6_16`.

Original target type, verbatim:

```lean
∀ (setGen : GenLimit.InfiniteContamination.SetGenerator.{0} Nat),
  GenLimit.InfiniteContamination.IsInfiniteSetGenerator.{0} setGen →
    ∀ (family : Nat → Set.{0} Nat) (selection : (t : Nat) → (Fin t → Nat) → Finset.{0} Nat)
      (orders : Nat → GenLimit.KleinbergWei.OrderedLanguage) (ρ ε : Real),
      LT.lt.{0} 0 ε →
        GenLimit.InfiniteContamination.SetCoreSelectionInvariant setGen family selection →
          (∀ (i : Nat), Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders i)) (family i)) →
            (∀ (i : Nat), GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.InheritsAmbientOrder (orders i)) →
              ∀ (target : Nat) (stream : GenLimit.Generic.Stream.{0} Nat),
                (∃ N, ∀ (t : Nat), LE.le.{0} N t → Membership.mem.{0, 0} (selection t fun i => stream ↑i) target) →
                  LE.le.{0} ρ (GenLimit.InfiniteContamination.setBasedLowerDensity setGen (orders target) stream) →
                    ∃ gen,
                      And (GenLimit.InfiniteContamination.GeneratesElementInLimitOn.{0} gen (family target) stream)
                        (LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} ρ ε) 2)
                          (GenLimit.InfiniteContamination.elementBasedLowerDensity gen (orders target) stream))
```

**Reconstruction.** With a globally infinite set generator, family, selection, matching increasing orders, arbitrary real `ρ`, and `ε>0`, assume the core invariant. For each particular target and stream eventually selecting that target, if the time-liminf of set-output lower densities is at least `ρ`, there exists an element generator that eventually produces fully fresh target elements and whose output-range lower density is at least `(ρ−ε)/2`.

**Quantifier skeleton.** `∀G,h∞,family,selection,orders,ρ,ε, ε>0 → invariant → matching → increasing → ∀z,s, eventualSelection → [ρ≤liminf_t d⁻_z(A_t)] → ∃g, eventualFresh(g,L_z,s) ∧ [(ρ−ε)/2≤d⁻_z(range(outputs_g))]`.

**Dependencies, information, and edges.** D1, D3–D5, D7 and `setBasedLowerDensity` fix the meanings. Crucially, `∃g` occurs **after** the target and stream; this type does not assert one shared witness for all of them. No named element witness is specified in the conclusion. The hypothesis is a time liminf, rather than the eventual exact per-time `ρ` bound of the preceding theorem. The loss is precisely subtract `ε`, then divide by two. There is no `ρ>0` or `ρ>ε` assumption: if `ρ−ε≤0`, the numerical conclusion is weak but eventual target correctness and both freshness conditions remain. No injectivity, noise, or coverage assumption is present. Infinitude and increasing order are supplied globally, including for histories unrelated to this stream.


### `GenLimit.InfiniteContamination.Results.theorem_6_18`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:290`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.theorem_6_18`.

Original target type, verbatim:

```lean
∀ (O : GenLimit.OracleFamily) (orders expansionOrders : Nat → GenLimit.KleinbergWei.OrderedLanguage),
  (∀ (i : Nat),
      Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders i)) (GenLimit.OracleFamily.language O i)) →
    (∀ (j : Nat),
        Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.carrier (expansionOrders j))
          (GenLimit.OracleFamily.language (GenLimit.InfiniteContamination.finiteExpansionOracleFamily O) j)) →
      (∀ (j : Nat) (A : GenLimit.Language),
          And
            (Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity (expansionOrders j) A)
              (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity
                (GenLimit.InfiniteContamination.finiteExpansionMeasure orders j) A))
            (Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.upperDensity (expansionOrders j) A)
              (GenLimit.KleinbergWei.OrderedLanguage.upperDensity
                (GenLimit.InfiniteContamination.finiteExpansionMeasure orders j) A))) →
        ∀ (gen : GenLimit.Generic.Generator.{0} Nat) (ρlow ρup : Real),
          (∀ (j : Nat) (stream : Nat → Nat),
              GenLimit.Presents stream
                  (GenLimit.OracleFamily.language (GenLimit.InfiniteContamination.finiteExpansionOracleFamily O) j) →
                And
                  (GenLimit.InfiniteContamination.GeneratesElementInLimitOn.{0} gen
                    (GenLimit.OracleFamily.language (GenLimit.InfiniteContamination.finiteExpansionOracleFamily O) j)
                    stream)
                  (GenLimit.InfiniteContamination.ElementDensityGuaranteeOn gen (expansionOrders j) stream ρlow ρup)) →
            ∀ (z : Nat) (stream : GenLimit.Generic.Stream.{0} Nat),
              GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration.{0} stream
                  (GenLimit.OracleFamily.language O z) →
                And
                  (GenLimit.InfiniteContamination.GeneratesElementInLimitOn.{0} gen (GenLimit.OracleFamily.language O z)
                    stream)
                  (GenLimit.InfiniteContamination.ElementDensityGuaranteeOn gen (orders z) stream ρlow ρup)
```

**Reconstruction.** Fix an oracle family, matching base orders, and orders on all encoded finite expansions with matching carriers. Require, for every expansion index and every set of naturals, equality of **both** its lower and upper densities under that expansion order and its original base-index order. For any given element generator and any real `ρlow,ρup`, suppose it generates fresh elements and meets the two density lower bounds on every exact presentation of every expansion. Then the same generator has those properties for every base target under injective enumeration with finite noise and finite omissions.

**Quantifier skeleton.** `∀O,orders,expansionOrders, matchingBase → matchingExpanded → [∀j,A, d⁻_expj(A)=d⁻_base(j)(A) ∧ d⁺_expj(A)=d⁺_base(j)(A)] → ∀g,ρlow,ρup, [∀j,s, range(s)=expanded(j) → (eventualFresh ∧ ρlow≤elementLower ∧ ρup≤elementUpper)] → ∀z,s, admissible_fin(s,L_z) → (eventualFresh ∧ ρlow≤elementLower_z ∧ ρup≤elementUpper_z)`.

**Dependencies, information, and edges.** D1–D5 and `Presents` (`Core/Basic.lean:26`) resolve the hypotheses. An exact presentation is range equality only: repetitions are allowed and there is no deadline for observing each element. In contrast, the conclusion's finite-contamination enumeration explicitly requires injectivity. The equality certificate ranges over **all** sets `A`; it is supplied as a hypothesis, not proved by a presumed invariance theorem in this reconstruction. `finiteExpansionMeasure` chooses the decoded base order even though its carrier differs from the expanded carrier. The result neither constructs a new generator nor asserts existence of the input one; it transfers its stipulated guarantees conditionally. `ρup` remains a lower bound on upper spatial density. No positivity, machine code, reduction, or treatment of infinite omissions is asserted.


### `GenLimit.InfiniteContamination.Results.proposition_7_4`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:324`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.proposition_7_4`.

Original target type, verbatim:

```lean
∀ (K : GenLimit.KleinbergWei.OrderedLanguage) (stream : GenLimit.Generic.Stream.{0} Nat) {L L' : Set.{0} Nat}
  {M : Real},
  HasSubset.Subset.{0} L' L →
    GenLimit.InfiniteContamination.BoundedDisplacement K stream L M →
      GenLimit.InfiniteContamination.BoundedDisplacement K stream L' M
```

**Reconstruction.** For every ordered language, arbitrary natural-number stream, sets `L,L'`, and real `M`, if `L'⊆L` and displacement relative to `L` is eventually bounded by `M(n+1)`, displacement relative to `L'` is eventually bounded by the same expression and constant.

**Quantifier skeleton.** `∀K,s,{L,L',M}, L'⊆L → [∃N ∀n≥N rank(K,L,s(n))≤M(n+1)] → [∃N' ∀n≥N' rank(K,L',s(n))≤M(n+1)]`.

**Dependencies, information, and edges.** D8 is decisive: this is monotonicity of the supplied rank predicate under restricting its set argument, not a statement about stream order or bounded waiting times. Neither set is required to lie in the carrier. In particular, the definition's zero canonical index outside the carrier must be retained. The type assumes no injection, coverage, noise bound, positivity of `M`, or infinitude of `L,L'`. Negative `M` makes the displacement premise impossible because ranks are nonnegative and `n+1` is positive. At `M=0` it can hold when eventual ranks vanish. Empty `L'` has rank zero everywhere; this is a valid edge case, not an excluded target. No learner or generator occurs.


### `GenLimit.InfiniteContamination.Results.lemma_7_5`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:336`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.lemma_7_5`.

Original target type, verbatim:

```lean
∀ (K : GenLimit.KleinbergWei.OrderedLanguage) (stream : GenLimit.Generic.Stream.{0} Nat) (L : Set.{0} Nat),
  HasSubset.Subset.{0} L (GenLimit.KleinbergWei.OrderedLanguage.carrier K) →
    ∀ (M : Real),
      LT.lt.{0} 0 M →
        GenLimit.InfiniteContamination.BoundedDisplacement K stream (GenLimit.KleinbergWei.OrderedLanguage.carrier K)
            M →
          And
            (LE.le.{0}
              (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 M)
                (Filter.liminf.{0, 0} (GenLimit.InfiniteContamination.empiricalTargetRatio stream L) Filter.atTop.{0}))
              (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K L))
            (LE.le.{0}
              (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 M)
                (Filter.limsup.{0, 0} (GenLimit.InfiniteContamination.empiricalTargetRatio stream L) Filter.atTop.{0}))
              (GenLimit.KleinbergWei.OrderedLanguage.upperDensity K L))
```

**Reconstruction.** For any ordered language `K`, stream, and set `L⊆K`, a positive real `M` and eventual displacement bound relative to the **whole carrier** imply two inequalities. The time liminf of the distinct-observed-target ratio, multiplied by `1/M`, is at most the lower ordered density of `L`; its time limsup multiplied by `1/M` is at most the upper ordered density of `L`.

**Quantifier skeleton.** `∀K,s,L, L⊆K → ∀M, M>0 → BD(K,s,K,M) → [(1/M)·liminf_n #(S_n∩L)/n≤d⁻_K(L)] ∧ [(1/M)·limsup_n #(S_n∩L)/n≤d⁺_K(L)]`, with both ratios defined as zero at zero.

**Dependencies, information, and edges.** D4 and D8 distinguish the spatial and temporal limits. The displacement hypothesis is on carrier ranks, not merely ranks within `L`. No injectivity is required: repeated target observations count once in `S_n`, while the denominator is the prefix length. Thus this is not generally a bound using the frequency of acceptable positions. Streams need not stay in the carrier or cover it, and no noise hypothesis is supplied. Finite `L`, including the empty set, is allowed and yields zero asymptotic distinct-value ratio; `K` itself is necessarily infinite by its constructor. Both conclusion conjuncts are required, with no replacement of lower by upper density. This target contains no generator or computational assertion.


### `GenLimit.InfiniteContamination.Results.theorem_7_8`

Original source anchor: `GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean:354`; original export: `stage1/01-target-statements.md`, section `GenLimit.InfiniteContamination.Results.theorem_7_8`.

Original target type, verbatim:

```lean
∀ (family : Nat → Set.{0} Nat),
  (∀ (i : Nat), Set.Infinite.{0} (family i)) →
    ∀ (orders : Nat → GenLimit.KleinbergWei.OrderedLanguage),
      (∀ (i : Nat), Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders i)) (family i)) →
        ∀ (ε M : Real),
          LT.lt.{0} 0 ε →
            LT.lt.{0} ε 1 →
              LT.lt.{0} 0 M →
                ∀ (target : Nat) (stream : GenLimit.Generic.Stream.{0} Nat),
                  Function.Injective.{1, 1} stream →
                    GenLimit.InfiniteContamination.VanishingNoise.{0} stream (family target) →
                      GenLimit.InfiniteContamination.BoundedDisplacement (orders target) stream
                          (GenLimit.KleinbergWei.OrderedLanguage.carrier (orders target)) M →
                        And
                          (GenLimit.InfiniteContamination.GeneratesInfiniteSetInLimitOn.{0}
                            (GenLimit.InfiniteContamination.algorithmNineSetGenerator family orders ε M) (family target)
                            stream)
                          (∃ T,
                            ∀ (t : Nat),
                              LE.le.{0} T t →
                                LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 ε) M)
                                  (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity (orders target)
                                    (GenLimit.InfiniteContamination.setOutput.{0}
                                      (GenLimit.InfiniteContamination.algorithmNineSetGenerator family orders ε M)
                                      stream t)))
```

**Reconstruction.** For an infinite indexed family and matching orders, fix real `0<ε<1` and `M>0`. On every injective stream with vanishing noise relative to a target and bounded displacement relative to that target's entire ordered carrier, Algorithm Nine is a globally infinite set generator and eventually outputs only unseen target elements. In addition, from some time onward **each** set output has lower ordered density at least `(1−ε)/M`.

**Quantifier skeleton.** `∀family, infinite → ∀orders, matching → ∀ε,M, 0<ε → ε<1 → M>0 → ∀z,s, Injective s → VanishingNoise(s,L_z) → BD(orders_z,s,carrier_z,M) → [GlobalInfinite(G9) ∧ eventualSetCorrect(G9,L_z,s)] ∧ [∃T ∀t≥T, (1−ε)/M≤d⁻_z(A_t)]`.

**Dependencies, information, and edges.** D1–D6 and D8 identify the named witness `algorithmNineSetGenerator family orders ε M`. It is fixed before the target and stream and has no extra order-monotonicity requirement. The eventual density lower bound is stronger than a mere time-limsup guarantee; it is not an element-output density statement. The correctness and density thresholds are separately existential and can depend on the stream. There is no full-presentation, finite-noise, finite-omission, or explicit omission-density premise. Injectivity and vanishing noise already ensure infinitely many observed target values, but the type states its actual assumptions directly. The expression `(1−ε)/M` is preserved without truncating at one; feasibility of the premises for particular constants is not an extra hypothesis. Infinitude excludes exhausted targets, while empty selected prefixes inside the named generator still have universal common core. No effectiveness or convergence-rate certificate is supplied.


## Exhaustive coverage and limitations

| Target | Main output and time scope | Essential distinct premises / dependencies |
|---|---|---|
| 5.1 | One existential element generator; eventual double freshness | Infinite family, injective stream, infinite target intersection, vanishing positional noise; D1–D3 |
| 5.4 | Uniform element existence iff infinite compatible finite cores | Class covered by infinite indexed members, `0<c<1`, shared admissible stream; D1–D3,D5 |
| 6.1 | Named G5; globally infinite sets, eventual correctness, time limsup ≥`1−c` | Oracle structure, matching orders, injectivity, finite bad indices, omission lower-density bound; D1–D6 |
| 6.4 | Negation for every set generator on Bool family | `0<c<1`, `ε>0`; noiseless injective omission streams; floor-increment definitions; D2–D4 |
| 6.5 | Uniform infinite-set existence iff directed almost-containment density | Finite bad indices and finite omissions; `L_i\L_j` finite; unrestricted real `c`; D1–D5 |
| 6.11 | Uniform infinite-set existence iff infinite finite-core density | Vanishing-noise arbitrary omissions; unrestricted `ρ`; D1–D5 |
| 6.14 | Uniform infinite-set existence iff shared-stream finite-core density | Constant-noise arbitrary omissions, `0<c<1`, `ρ>0`; D1–D5 |
| 6.15 | Named G8; eventual element correctness and output-range lower density ≥`ρ/2` | Global set infinitude, core invariant, increasing orders, eventual selection, eventual per-set density; D1,D3–D5,D7 |
| 6.16 | Per-target/per-stream existential element generator; ≥`(ρ−ε)/2` | Same invariant and orders, time-liminf set density, `ε>0`, no positivity for `ρ`; D1,D3–D5,D7 |
| 6.18 | Same supplied element generator, both density lower bounds retained | Exact expanded presentations, all-set lower/upper equality certificates, finite-contamination conclusion; D1–D5 |
| 7.4 | Restriction preserves displacement constant | Set inclusion only, no positivity or stream restriction; D8 |
| 7.5 | Two scaled empirical-ratio versus spatial-density inequalities | Subset of carrier, positive `M`, whole-carrier displacement, distinct-value count; D4,D8 |
| 7.8 | Named G9; globally infinite sets and eventual per-set density ≥`(1−ε)/M` | Infinite family, matching orders, `0<ε<1`, positive `M`, injectivity, vanishing noise, whole-carrier displacement; D1–D6,D8 |

All 13 original types, quantifier skeletons, witness dependencies, relevant definitions, stream restrictions, output distinctions, constants, limit directions, and vacuous/finite edges are covered. No law, probability distribution, support-loss notion, runtime bound, ordinary-computability premise, or formal oracle-relative program predicate occurs in these types. The membership-query field is recorded at its actual structural strength. Necessary supplied infinitude/existence helpers and the all-set density certificates were preserved as conditions rather than independently proved. Proof correctness, fresh compilation, source correspondence, and certification remain outside this stage.
