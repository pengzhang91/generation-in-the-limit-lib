# Stage 1: code-only statement reconstruction

## Scope, census, and method

This report reconstructs the 13 supplied target types, in `targets.txt` order, solely from the Stage 1 export. The source-paper meanings of labels such as “printed” and “corrected” are outside this report: those labels identify declarations, and do not establish what any paper says. No theorem proof body, raw project source, other stage, previous result, registry, PaperMap, owner material, or external mathematical source was consulted. No Lean invocation, build, Git inspection, source edit, or proof certification occurred.

There are 97 exported declarations: 13 target theorems and 84 statement-relevant dependencies, including constructors, projections, generated match definitions, and an auxiliary theorem type. The main SHA256SUMS has 13 entries; the supplement manifest has two. Every entry matched its actual bytes. The explicit-target-types supplement was already included in the initial main manifest, rather than requested after reconstruction. Its 13 names match target order. The declaration JSONL places roots in a different order; the root-name set still matches all 13 targets, and each original target type agrees byte-for-byte with its Markdown quotation. All recorded type/value dependency names resolve either to the 97 exported declarations or to the declared standard-library boundary. That is an interface-closure check, not a proof check.

The input hashes and actual access sequence are recorded in `stage1-run.json`, alongside the report digest. The first substantive reads were START_HERE, PROMPT, both manifest texts, the supplement README, snapshot, target list, and external boundary; hashing then traversed the main and supplement manifests. Original types, explicit types, definition export, machine declaration records, and pinned configuration were subsequently inspected. A large definition-display response was truncated; its missing middle was explicitly reread. The run used the coordinator-specified configuration `gpt-6.1-sol / xhigh / fork none`; the serving backend revision is unavailable. No reproducibility claim about hidden backend internals is made.

The supplied snapshot describes dirty working-tree bytes, branch `work/non-p38`, head `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`, and capture time `2026-11-10T14:23:54.018917+00:00`. These are supplied provenance, not independently inspected Git facts. The pinned interface configuration is Lean 4.24.0 and Mathlib v4.24.0, whose manifest revision is `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Snapshot hashes of raw source files were not compared against excluded source files.

For anchors below, **D** means `stage1/02-definition-dependencies.md`, **T** means `stage1/01-target-statements.md`, and **J row** means the one-based line of `stage1/declarations.jsonl`. Original source paths and line numbers are locators supplied by these exports. Standard meanings of sets, finite sets, sums, ENNReal, real absolute value, countability, and `Computable₂` are assumed only at `external-constant-boundary.txt`. No decisive missing project interface remained; the explicitly printed target supplement plus exported predicate signatures resolve notation-hidden domains.

## Definition glossary and common quantifier conventions

**Objects and observations.** A language is a set of elements of the ambient type A; a class is a set of languages; a family is a sequence indexed by Nat; a stream is Nat → A. A presentation has range exactly L, while StreamIn only requires range contained in L. Repetition and arbitrary order are allowed; no injectivity, rate, or probability law for the input is imposed. At time t the history is the ordered length-t prefix at indices 0 through t−1. The sample Sₜ is the finite set of distinct values in that prefix, so repeated examples affect time and history but do not increase sample cardinality or empirical weight. Anchors: D:34,47,93,106,119,132,145,158,213,226; `textPrefix` D:5; source `Core/GenericGeneration.lean`:21–87 and `Core/Text.lean`:16.

**Laws and loss.** A DiscreteDistribution is specified by a real function m on A, pointwise nonnegative, summable, with total sum exactly 1. These conditions come from its exported constructor, not its name. Its mass projection is m. For a set B, groupMass is the real sum of m(x) over x∈B, using zero elsewhere. No finite-support condition or full-support requirement is imposed on a law. SupportedOn(μ,B) says every x with m(x)≠0 lies in B; it is not equality of support with B. For nonempty S, empirical group probability pᵢ(S) is |S∩groups(i)|/|S| in Real; for empty S it is 0. This weights distinct observations equally, rather than weighting their occurrences. Induced group probability is groupMass(μ,groups(i)). The loss Δ(μ,S) is the supremum over every natural group index of ENNReal.ofReal of the absolute real difference between induced and empirical probability. It is a supremum of group-coordinate errors, not a distance between individual output points. Anchors: D:295,598,667,807,820,867,880,962,975; source `Distribution.lean`:24–25,80–86,152,235–260.

**Generators, accuracy, and freshness.** A randomized generator is an arbitrary function taking t and a Fin t-indexed history to a distribution; distributionAt supplies the actual prefix. Accuracy at tolerance a means Δ≤ENNReal.ofReal(a) for every stream and every t>0, including streams unrelated to H. There is no accuracy requirement at time zero. ConsistentAt means the distribution assigns real mass exactly 1 to L∖Sₜ. ConsistentFrom(T) requires this at every natural time t≥T, including T. These are laws and mass conditions, not a theorem about each realized random sample or independence between draws. There is no joint probability space for outputs over times. Anchors: D:387,407,427,521,652; source `Definitions.lean`:53–76 and `Distribution.lean`:76.

**Three quantifier orders.** For a fixed a, AlphaRepresentativeUniformlyGeneratable means ∃gen [accuracy(a) ∧ ∃d∈Nat ∀L∈H ∀stream in L ∀t (|Sₜ|=d → ConsistentFrom(t))]. Thus gen and the distinct-sample trigger d precede the target and stream. RepresentativelyUniformlyGeneratable quantifies this only over 0<a≤1; it does not itself quantify over all positive a. RepresentativelyNonuniformlyGeneratable instead means ∀a>0 ∃gen [accuracy(a) ∧ ∀L∈H ∃d ∀stream in L ∀t (|Sₜ|=d → ConsistentFrom(t))]. Its language-specific d cannot depend on the stream. RepresentativelyGeneratableInLimit means ∀a>0 ∃gen [accuracy(a) ∧ ∀L∈H ∀stream presenting L ∃T ConsistentFrom(T)]. Its time threshold may depend on the full presentation. AlphaRepresentativelyGeneratableInLimit removes the outer ∀a>0 and fixes a. None of these predicates asks for a computable generator, a shared generator across tolerances, a named program, or a numeric bound on d or T. Anchors: D:252,275,535,557,582; source `Definitions.lean`:92–126 and `LimitFoundations.lean`:176.

**Generic hypotheses and ordinary generation.** UUS(H) is exactly “every member language of H is infinite”; it does not assert H is nonempty or infinite. Ordinary UniformlyGeneratable is ∃gen d for a single-element-output history function, such that, on every stream contained in every L∈H, reaching exactly d distinct samples forces every later output to lie in L and outside the sample at that later time. This output freshness is a pointwise condition, different from unit mass on a fresh set. Both notions are semantic existence here. IsNondecreasingCover(H,classes) means classes is monotone under class inclusion and H=⋃ₙclasses(n); its stages need not be finite or effectively given. Anchors: D:18,60,73,171,184; source `Core/ClassGeneration.lean`:13,26,33, `Core/GenericGeneration.lean`:367, and `Core/ClassCovers.lean`:14.

**Groups and finite extension.** IsCountablePartition requires disjointness for distinct natural indices and union equal to the entire ambient type. Individual groups need not be nonempty. GroupsCover requires only that union equality, so it permits overlap, repetition, and empty groups. A Fin k-indexed collection is extended to Nat by its given group for i<k and the empty set for i≥k. IsFinitePartition is precisely IsCountablePartition of that extension. Thus zero added indices do not mean extra nonempty groups; the case k=0 cannot cover a nonempty ambient type. Anchors: D:305,443,476,714; source `Definitions.lean`:20, `FiniteSupport.lean`:46, and `FinitePartitionCorollaries.lean`:33,52.

**The finite dimension condition.** Given a finite set S, V={L∈H:S⊆L}; C is the set of points belonging to every L∈V; unseen closure is C∖S. Let U={i:(C∖S)∩groups(i)=∅}, and let Vg=Nat∖U be its complement among group indices. Do not confuse the class V with the available-index set Vg. A group-closure witness requires all three: S≠∅, V≠∅, and one of two obstructions. The first is ∃i∈U with ENNReal.ofReal(a)<ENNReal.ofReal(pᵢ(S)). The second explicitly includes a certificate hfinite that Vg is finite and requires ENNReal.ofReal(a)·|Vg| < ∑'ᵢ [i∈U] ENNReal.ofReal(pᵢ(S)). Both inequalities are strict and in ENNReal; the sum counts indices, not points or a union of groups. HasFiniteGroupClosureDimension means ∃d∈Nat such that every such witness S has |S|≤d. It specifies a bound, not its least value. The finite certificate belongs to the mathematical predicate and is not an oracle supplied to a generator. Empty V makes the universal common-core predicate vacuous, but the witness explicitly excludes that case. Anchors: D:197,239,334,491,626,639,683,772,789,933,949; source `Core/VersionSpace.lean`:16,20, `Definitions.lean`:26,33, and `GroupClosure.lean`:137,144,152,267,281,859,880.

**Two different support conditions.** For every subset I of Nat, indexedGroupIntersection(L,groups,I) is L intersected with the requirement to belong to every group whose index is in I. It imposes no nonmembership requirement for indices outside I; I may be infinite or empty. Its contribution is its cardinality cast to ENNReal if the intersection is finite, and 0 if it is infinite. finiteSupportSize is the unconditional ENNReal sum of those contributions over *all* subsets I of Nat, and HasFiniteSupport requires this sum <∞ separately for every L∈H. Empty finite intersections contribute zero. Different index subsets remain separate summation indices even if their intersections coincide.

By contrast, exactGroupCell(groups,x) consists of all y having, for every index i, exactly the same group-membership truth value as x. finiteExactProfilePoints(L,groups) is the set of x∈L for which L∩exactGroupCell(groups,x) is finite. HasFiniteExactProfileSupport requires this set of points to be finite for each L∈H. It does not merely count group indices or assert each cell is finite. These definitions remain distinct when groups overlap; neither can be silently replaced by ordinary finite support of a distribution. Anchors: D:318,350,699,727,743,758,852; source `FiniteSupport.lean`:19,26,35,40 and `ExactProfileSupport.lean`:26,49,56.

**Feasibility and criticality.** IsAlphaFeasibleAt(L,groups,a,stream,t) is ∃μ [SupportedOn(μ,L∖Sₜ) ∧ Δ(μ,Sₜ)≤ENNReal.ofReal(a)]. The distribution is an existential for that time; no generator is part of this predicate. LanguageConsistentAt(L,stream,t) means Sₜ⊆L. IsCriticalAt(family,stream,t,n) conjoins n<t, sample consistency with family(n), and ∀i<n, if family(i) is sample-consistent then family(n)⊆family(i). The latter is containment of whole languages, not of samples or only unseen points. Anchors: D:366,457,508; source `LimitFoundations.lean`:26,35,110.

**Named concrete data.** UniformSeparationUniverse is Nat ⊕ Nat (D:613; `UniformSeparation.lean`:494). The separate tail data live on Nat: tailLanguage=univ, tailClass={tailLanguage}, tailGroups(n)={m:n≤m}, identityEnumeration(n)=n. These are actual exported definition values. The tail groups cover Nat but overlap and are not asserted to be a partition by either tail target. Anchors: D:839,894,907,920; source `TailCounterexample.lean`:27–34.

## Input byte census

| Stage 1 file | Bytes | Actual SHA256 |
|---|---:|---|
| START_HERE.md | 190 | `64bbaec5e9d9236b599f7cc915eac8ef4ebd4bd60eca6f74be17d98ca0410ebb` |
| PROMPT.md | 1827 | `d79a9f3221e3fdc6cdb3835026d91ba49ca51b6fade5f30a27d10c5aba9eed4e` |
| SHA256SUMS | 1126 | `61e14de56f3b5a6f32df509d758cbc161bcafeafe13e71b100e3f5c6ba02dd5e` |
| explicit-target-types/README.md | 515 | `32eaa6c83ca84b5d6901931d03ec27518572a50f3f7f6d3a45b49246bd489358` |
| explicit-target-types/SHA256SUMS | 154 | `c1a46b0364e322a449e7e4746b437b0b94aa09896660a172691cafcddfd4779c` |
| snapshot.json | 10916 | `a3091b33a57cd93ebb9bbe7e564f2214229b8b14dd34b8f82f049c4547d3c2e1` |
| targets.txt | 792 | `1886f88e3f949b0dc5a1337c2b2571ccbcc035b18fcc45d7932611ed0b31d5af` |
| external-constant-boundary.txt | 2909 | `a15e202e2b626b757c718ba33c32b49126fe0f8671658ae1cb208da898c1ac16` |
| 01-target-statements.md | 10119 | `ce3e4bcc96982ce3e462929ccbf82b23e5c3be0aeebca521bb53f9779a878374` |
| explicit-target-types/types.jsonl | 11258 | `f98a9f205119d25e674cb199e3706cf196635141b1d50d4f2f5a74225b2e66a3` |
| 02-definition-dependencies.md | 42982 | `26a9935cbd950aff901a4857d089137661331e2b7c397be21248f90d2ba12b13` |
| declarations.jsonl | 89216 | `debb6a23eafba5c0f48dc3b54e588e05c72af19ede4362b2fb0fe6476928c4b4` |
| lakefile.toml | 379 | `0fef48c5e314b7476f09da4caa5615d58a50937752aea1b192c0921a05b6e3d0` |
| lake-manifest.json | 3100 | `994d8b6a379cea0e626d27fe8fa2fc74a2d966197a6998ecde6bd419634991aa` |
| lean-toolchain | 25 | `42779d67b81608af8a12aa4328d2ab47ca201925b3b2bd68369587b5340bb434` |

## Target dossiers

The complete original target types follow, with whitespace preserved from the exported declaration records. Source anchors below are supplied metadata, not raw-source reads.

### 1. theorem_3_3

**Identifier:** `GenLimit.RepresentativeGeneration.Published.theorem_3_3`. **Anchor:** T:5; J row 90; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:31`.

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] [Countable.{u_1 + 1} α] (H : GenLimit.Generic.LanguageClass.{u_1} α)
  (groups : Nat → Set.{u_1} α) (alpha : Real),
  GenLimit.Generic.UUS.{u_1} H →
    GenLimit.RepresentativeGeneration.IsCountablePartition.{u_1} groups →
      LT.lt.{0} 0 alpha →
        Iff (GenLimit.RepresentativeGeneration.AlphaRepresentativeUniformlyGeneratable.{u_1} H groups alpha)
          (GenLimit.RepresentativeGeneration.HasFiniteGroupClosureDimension.{u_1} H groups alpha)
```

**Reconstruction.** For every nonempty countable ambient type A, every class H of its subsets, every Nat-indexed grouping, and every real a, assume every L∈H is infinite, the groups form the specified partition of all A, and a>0. Then fixed-a representative uniform generation exists if and only if group-closure witnesses have a common finite cardinality bound. On the generation side this includes the global accuracy obligation on arbitrary streams as well as the uniform distinct-sample trigger and every-later-time unit-mass consistency. On the dimension side it includes both strict obstruction alternatives, nonempty S and nonempty consistent class, exactly as expanded above.

**Skeleton and access.** ∀A [Nonempty A] [Countable A] ∀H groups a, UUS → partition → 0<a → ((∃gen [accuracy(a)∧∃d uniform-trigger-consistency]) ↔ ∃b ∀S [witness(S)→|S|≤b]). The generator and either bound may depend on H, groups, and a; there is no assertion that the dimension bound equals the generator threshold. The history is its only run-time argument; fixed parameters are accommodated by choosing a semantic function. Neither membership access nor effectiveness is specified.

**Edges and anchors.** There is no upper endpoint restriction a≤1 in this target. Empty H satisfies UUS vacuously and supplies no closure witness because its version spaces are empty, although the generation side still includes global accuracy. Repeats in streams and empty groups remain allowed. No rates or least-bound formula are stated. Dependencies: D:252,334,387,427,443,491,772,789, and the shared observation/law definitions.

### 2. corollary_3_4

**Identifier:** `GenLimit.RepresentativeGeneration.Published.corollary_3_4`. **Anchor:** T:19; J row 79; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:44`.

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] [Countable.{u_1 + 1} α] (H : GenLimit.Generic.LanguageClass.{u_1} α)
  (groups : Nat → Set.{u_1} α),
  GenLimit.Generic.UUS.{u_1} H →
    GenLimit.RepresentativeGeneration.IsCountablePartition.{u_1} groups →
      Iff (GenLimit.RepresentativeGeneration.RepresentativelyUniformlyGeneratable.{u_1} H groups)
        (∀ (alpha : Real),
          LT.lt.{0} 0 alpha → GenLimit.RepresentativeGeneration.HasFiniteGroupClosureDimension.{u_1} H groups alpha)
```

**Reconstruction.** For a nonempty countable A, H whose members are all infinite, and a Nat-indexed partition of A, representative uniform generation is equivalent to finite group-closure dimension separately for every positive real tolerance. The left-hand predicate actually quantifies over 0<a≤1; the right-hand side printed in the target quantifies over every a>0, with no upper bound. This distinction is preserved, rather than rewriting both sides with the same tolerance interval.

**Skeleton and access.** ∀A [Nonempty] [Countable] ∀H groups, UUS → partition → ((∀a,0<a→a≤1→∃gen,d [accuracy∧uniform-trigger-consistency]) ↔ (∀a,0<a→∃b ∀S [witness at a→|S|≤b])). Neither side chooses one gen, d, or b simultaneously independent of a. On each fixed-tolerance generation claim gen and d are independent of the target and stream.

**Edges and anchors.** The endpoint a=1 belongs to the left interval; a=0 does not. For a>1 only the right side directly asks for a bound. H may be empty, and empty partition pieces are permitted. The theorem states an equivalence of predicates under these assumptions, without providing an executable conversion between their witnesses. Dependencies: D:171,334,443,582 and the full fixed-a expansion at D:252.

### 3. corollary_3_5

**Identifier:** `GenLimit.RepresentativeGeneration.Published.corollary_3_5`. **Anchor:** T:33; J row 80; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:57`.

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] [Countable.{u_1 + 1} α] (H : GenLimit.Generic.LanguageClass.{u_1} α),
  Set.Finite.{u_1} H →
    GenLimit.Generic.UUS.{u_1} H →
      ∀ {k : Nat} (groups : Fin k → Set.{u_1} α),
        GenLimit.RepresentativeGeneration.IsFinitePartition.{u_1} groups →
          GenLimit.RepresentativeGeneration.RepresentativelyUniformlyGeneratable.{u_1} H
            (GenLimit.RepresentativeGeneration.extendFinitePartition.{u_1} groups)
```

**Reconstruction.** Every finite class H of infinite languages over a nonempty countable A is representatively uniformly generatable relative to the natural-index extension of any Fin k-indexed partition. The conclusion says that for each 0<a≤1 a globally a-accurate history-to-law function and one distinct-sample threshold work for every member of that class and every stream contained in that member.

**Skeleton and access.** ∀A [Nonempty] [Countable] ∀H, finite(H) → UUS(H) → ∀k∈Nat ∀groups:Fin k→Set A, finite-partition(groups) → ∀a∈(0,1] ∃gen,d ∀L∈H ∀stream in L ∀t (|Sₜ|=d→∀s≥t consistency at s), together with accuracy for all streams at positive times. k is arbitrary and implicit in Lean; it is not fixed globally or required to be positive by a separate binder.

**Edges and anchors.** Under nonempty A, k=0 makes the partition hypothesis impossible. A finite H may contain zero languages; UUS is vacuous then, but global accuracy remains part of the conclusion. Empty groups in the given finite partition and all empty extension groups are allowed. Finiteness of H is mathematical finiteness, without a supplied enumeration or effective membership test. No cardinality-dependent threshold formula appears. Dependencies: D:252,476,582,714, plus D:171.

### 4. corollary_3_6

**Identifier:** `GenLimit.RepresentativeGeneration.Published.corollary_3_6`. **Anchor:** T:47; J row 81; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:70`.

```lean
∃ H groups,
  And (Set.Countable.{0} H)
    (And (GenLimit.Generic.UUS.{0} H)
      (And (GenLimit.RepresentativeGeneration.IsFinitePartition.{0} groups)
        (And (GenLimit.Generic.UniformlyGeneratable.{0} H)
          (Not
            (GenLimit.RepresentativeGeneration.RepresentativelyUniformlyGeneratable.{0} H
              (GenLimit.RepresentativeGeneration.extendFinitePartition.{0} groups))))))
```

**Reconstruction.** There exist H⊆Set(Nat ⊕ Nat) and groups:Fin 2→Set(Nat ⊕ Nat) such that all five conjuncts hold: H is countable; each member is infinite; these two groups form a finite partition; H is ordinarily uniformly generatable by a single-output generator; and H is not representatively uniformly generatable for the extended grouping. The ambient type and the number two are fixed by the explicit target applications and exported signatures, even though notation hides them in the original type.

**Skeleton and access.** ∃H ∃groups [countable(H)∧UUS(H)∧finite-partition(groups)∧(∃ordinary-gen,d ordinary uniform correctness)∧¬(∀a∈(0,1]∃randomized-gen,d representative uniform correctness)]. Both generators, when present, take ordered finite histories; neither is required to be computable. The ordinary one outputs one fresh target element at each relevant later time, whereas the representative one would output laws satisfying the separate global group-error requirement.

**Edges and anchors.** The witnesses are not named in this type; no particular H or two sets can be recovered from the withheld proof. Countability does not assert H is countably infinite. The negative conjunct rules out the whole every-tolerance predicate, and does not itself name a failing tolerance or deny generation at every tolerance. Partition does not force each of the two pieces nonempty. Dependencies: explicit-types row 4; D:73,184,476,582,613,714.

### 5. theorem_3_7

**Identifier:** `GenLimit.RepresentativeGeneration.Published.theorem_3_7`. **Anchor:** T:62; J row 91; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:82`.

```lean
∀ {α : Type u_1} {H : GenLimit.Generic.LanguageClass.{u_1} α} {groups : Nat → Set.{u_1} α},
  Iff (GenLimit.RepresentativeGeneration.RepresentativelyNonuniformlyGeneratable.{u_1} H groups)
    (∀ (alpha : Real),
      LT.lt.{0} 0 alpha →
        ∃ classes,
          And (GenLimit.Generic.IsNondecreasingCover.{u_1} H classes)
            (∀ (n : Nat),
              GenLimit.RepresentativeGeneration.AlphaRepresentativeUniformlyGeneratable.{u_1} (classes n) groups alpha))
```

**Reconstruction.** For every ambient type A, class H, and Nat-indexed group family, representative nonuniform generation is equivalent to the following tolerance-dependent cover property: for every real a>0, there exists a nondecreasing sequence of classes whose union is H, and every stage of that sequence is fixed-a representatively uniformly generatable for the same groups. There are no ambient nonemptiness/countability, UUS, coverage, or disjointness assumptions in this target.

**Skeleton and access.** (∀a>0 ∃gen [accuracy(a)∧∀L∈H ∃d ∀stream in L trigger-consistency]) ↔ (∀a>0 ∃classes:Nat→Class(A) [Monotone(classes)∧H=⋃ₙclasses(n)∧∀n∃genₙ,dₙ fixed-a-uniform-generation(classes(n))]). The entire cover may vary with a. The right side does not require one cover for all accuracies, a common generator across n, finite stages, decidable stage membership, or effective discovery of the stage containing L.

**Edges and anchors.** The nonuniform threshold d is selected after L and before its stream; this is stronger than simply allowing an arbitrary presentation-dependent time. Empty H and even an empty ambient type are included syntactically; in such cases the existence of total history-to-distribution functions and available streams must be interpreted literally. The equivalence supplies no independent inhabitance premise. Dependencies: D:60,252,557 and the shared accuracy definition D:387.

### 6. corollary_3_8

**Identifier:** `GenLimit.RepresentativeGeneration.Published.corollary_3_8`. **Anchor:** T:77; J row 82; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:94`.

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] [Countable.{u_1 + 1} α] (H : GenLimit.Generic.LanguageClass.{u_1} α),
  Set.Countable.{u_1} H →
    Set.Infinite.{u_1} H →
      GenLimit.Generic.UUS.{u_1} H →
        ∀ {k : Nat} (groups : Fin k → Set.{u_1} α),
          GenLimit.RepresentativeGeneration.IsFinitePartition.{u_1} groups →
            And
              (GenLimit.RepresentativeGeneration.RepresentativelyNonuniformlyGeneratable.{u_1} H
                (GenLimit.RepresentativeGeneration.extendFinitePartition.{u_1} groups))
              (GenLimit.RepresentativeGeneration.RepresentativelyGeneratableInLimit.{u_1} H
                (GenLimit.RepresentativeGeneration.extendFinitePartition.{u_1} groups))
```

**Reconstruction.** Let A be nonempty and countable, and H a countable infinite class every one of whose member languages is infinite. For every finite partition indexed by Fin k, the extended groups satisfy both representative nonuniform generation and representative generation in the limit. Countability, infinitude of the class, and infinitude of each member are separate hypotheses, all retained.

**Skeleton and access.** ∀A [Nonempty] [Countable] ∀H, countable(H)→infinite(H)→UUS(H)→∀k groups, partition→(nonuniform(H,extended-groups)∧limit(H,extended-groups)). Expanding the first conjunct gives ∀a>0 ∃gen ∀L∈H ∃d before ∀stream in L; expanding the second gives ∀a>0 ∃gen ∀L∈H ∀stream presenting L ∃T. Each existential gen also carries global accuracy(a). The two conjuncts need not use the same witnesses.

**Edges and anchors.** The first conclusion controls streams contained in L even if they never enumerate all L; its consistency promise is conditional on reaching exactly d distinct values. The second concerns complete presentations and gives an eventual time instead of that trigger. Both allow repetitions. There is no finite upper accuracy endpoint in either of these conclusion predicates. k=0 again makes the premise impossible for nonempty A; the explicit infinite-H hypothesis is not silently weakened. Dependencies: D:171,476,535,557,714.

### 7. lemma_4_3

**Identifier:** `GenLimit.RepresentativeGeneration.Published.lemma_4_3`. **Anchor:** T:95; J row 85; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:110`.

```lean
∃ groups H,
  And (GenLimit.RepresentativeGeneration.IsCountablePartition.{0} groups)
    (And (Function.Injective.{1, 1} groups)
      (And (∀ (n : Nat), Set.Nonempty.{0} (groups n))
        (And (Set.Finite.{0} H)
          (And (Eq.{1} (Set.ncard.{0} H) 1)
            (And (GenLimit.Generic.UUS.{0} H)
              (And (Not (GenLimit.RepresentativeGeneration.HasFiniteSupport.{0} H groups))
                (And (Not (GenLimit.RepresentativeGeneration.RepresentativelyGeneratableInLimit.{0} H groups))
                  (∀ (alpha : Real),
                    LT.lt.{0} 0 alpha →
                      LT.lt.{0} alpha 1 →
                        Not
                          (GenLimit.RepresentativeGeneration.AlphaRepresentativelyGeneratableInLimit.{0} H groups
                            alpha)))))))))
```

**Reconstruction.** There exist groups:Nat→Set Nat and H⊆Set Nat with every following component: groups is a countable partition of Nat; the map from indices to groups is injective; each individual group is nonempty; H is finite; its ncard equals exactly 1; every member language is infinite; H fails HasFiniteSupport for these groups; H fails representative limit generation; and, separately, for every real 0<a<1 it fails fixed-a representative limit generation.

**Skeleton and access.** ∃groups ∃H [partition∧injective(groups)∧(∀n,groups(n)≠∅)∧finite(H)∧ncard(H)=1∧UUS(H)∧¬finite-support(H,groups)∧¬limit(H,groups)∧∀a(0<a→a<1→¬fixed-a-limit(H,groups,a))]. The singleton class assertion is supplied by finite(H) and ncard=1 together, not merely an informal gloss of a label. Its sole language is infinite, but the type does not identify it.

**Edges and anchors.** Nonempty pieces and injectivity are explicit extra conjuncts beyond partition. No group is asserted singleton, finite, or infinite. The stronger tolerance-by-tolerance failure excludes both endpoints 0 and 1; the separate negation of full limit generation must still be recorded. No particular group function or H is available without a witness body. The failed support predicate is the sum over positive intersections, not distribution support or exact profiles. Dependencies: explicit-types row 7; D:275,350,443,535,743,758,852.

### 8. lemma_4_6

**Identifier:** `GenLimit.RepresentativeGeneration.Published.lemma_4_6`. **Anchor:** T:117; J row 86; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:126`.

```lean
∀ {α : Type u_1} {family : GenLimit.Generic.LanguageFamily.{u_1} α} {stream : GenLimit.Generic.Stream.{u_1} α}
  {z : Nat},
  GenLimit.Generic.Presents.{u_1} stream (family z) →
    ∃ T, ∀ (t : Nat), LE.le.{0} T t → GenLimit.RepresentativeGeneration.IsCriticalAt.{u_1} family stream t z
```

**Reconstruction.** For any ambient type, any sequence family of languages, any stream, and any natural index z, if that stream presents family(z), then from some natural time T onward z is critical at every time. Expanded, each t≥T satisfies z<t, Sₜ⊆family(z), and every i<z whose language still contains Sₜ also contains the entire language family(z).

**Skeleton and access.** ∀A family stream z, range(stream)=family(z) → ∃T∈Nat ∀t∈Nat, T≤t → [z<t∧Sₜ⊆family(z)∧∀i<z(Sₜ⊆family(i)→family(z)⊆family(i))]. T follows the fixed family, presentation, and z, so it may depend on all three. There is no uniform time across presentations or indices, and no algorithm selecting T.

**Edges and anchors.** Repeated family languages and repeated stream values are allowed. No class H, infinite-language assumption, group family, distribution, learner, or countability/inhabitance typeclass is required. A presentation itself supplies range equality and therefore covers all elements of its target. Criticality includes strict z<t, so it is not merely “still consistent”; no comparison with indices ≥z is imposed. An empty target cannot have a Nat-indexed presentation, making that premise impossible. Dependencies: D:119,132,226,457,508.

### 9. printed_lemma_4_8_counterexample

**Identifier:** `GenLimit.RepresentativeGeneration.Published.printed_lemma_4_8_counterexample`. **Anchor:** T:128; J row 88; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:134`.

```lean
And (Set.Countable.{0} GenLimit.RepresentativeGeneration.tailClass)
  (And (GenLimit.Generic.UUS.{0} GenLimit.RepresentativeGeneration.tailClass)
    (And (GenLimit.RepresentativeGeneration.GroupsCover.{0} GenLimit.RepresentativeGeneration.tailGroups)
      (And
        (GenLimit.RepresentativeGeneration.HasFiniteSupport.{0} GenLimit.RepresentativeGeneration.tailClass
          GenLimit.RepresentativeGeneration.tailGroups)
        (And
          (Membership.mem.{0, 0} GenLimit.RepresentativeGeneration.tailClass
            GenLimit.RepresentativeGeneration.tailLanguage)
          (And
            (GenLimit.Generic.Presents.{0} GenLimit.RepresentativeGeneration.identityEnumeration
              GenLimit.RepresentativeGeneration.tailLanguage)
            (Not
              (∃ T,
                ∀ (t : Nat),
                  LE.le.{0} T t →
                    GenLimit.RepresentativeGeneration.IsAlphaFeasibleAt.{0}
                      GenLimit.RepresentativeGeneration.tailLanguage GenLimit.RepresentativeGeneration.tailGroups
                      (1 / 2) GenLimit.RepresentativeGeneration.identityEnumeration t)))))))
```

**Reconstruction.** This is a conjunction about the named Nat-valued data, with no existential choice of a different example: H={Nat}, groups(n)={m:n≤m}, and stream(n)=n. It asserts H is countable, all its members are infinite, these groups cover Nat, H has the positive-intersection finite-support property, Nat belongs to H, and this identity stream presents Nat. Finally, it asserts there is no T from which the target is feasible at tolerance exactly the real number 1/2 for every later time.

**Skeleton and access.** countable(tailClass)∧UUS(tailClass)∧cover(tailGroups)∧finite-support(tailClass,tailGroups)∧tailLanguage∈tailClass∧Presents(identity,tailLanguage)∧¬∃T∀t≥T∃μ [SupportedOn(μ,Nat∖Sₜ)∧Δ(μ,Sₜ)≤ofReal(1/2)]. Thus the final clause is failure of eventual timewise feasibility, equivalently arbitrarily late infeasible times under classical logic. It does not merely say a particular learner fails.

**Edges and anchors.** The conclusion is not strengthened to infeasibility at every time. Feasibility includes a normalized law and excludes nonzero mass on all already observed points. The overlapping tail groups are only required to cover; partition hypotheses from earlier targets cannot be imported here. The support hypothesis concerns all index subsets and positive intersections, despite those overlaps. The displayed half is real division, resolved in the explicit supplement. Dependencies: D:305,350,366,839,894,907,920 and explicit-types row 9.

### 10. printed_theorem_4_4_counterexample

**Identifier:** `GenLimit.RepresentativeGeneration.Published.printed_theorem_4_4_counterexample`. **Anchor:** T:154; J row 89; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:147`.

```lean
And (Set.Countable.{0} GenLimit.RepresentativeGeneration.tailClass)
  (And (GenLimit.Generic.UUS.{0} GenLimit.RepresentativeGeneration.tailClass)
    (And (GenLimit.RepresentativeGeneration.GroupsCover.{0} GenLimit.RepresentativeGeneration.tailGroups)
      (And
        (GenLimit.RepresentativeGeneration.HasFiniteSupport.{0} GenLimit.RepresentativeGeneration.tailClass
          GenLimit.RepresentativeGeneration.tailGroups)
        (Not
          (GenLimit.RepresentativeGeneration.RepresentativelyGeneratableInLimit.{0}
            GenLimit.RepresentativeGeneration.tailClass GenLimit.RepresentativeGeneration.tailGroups)))))
```

**Reconstruction.** For exactly the same named Nat data, all five conjuncts hold: tailClass is countable; each of its members is infinite; tailGroups covers Nat; tailClass has HasFiniteSupport; and tailClass is not representatively generatable in the limit for these groups. The four affirmative clauses are retained alongside the negative one.

**Skeleton and access.** countable(H₀)∧UUS(H₀)∧cover(groups₀)∧finite-support(H₀,groups₀)∧¬[∀a>0 ∃gen (global-accuracy(a)∧∀L∈H₀∀stream presenting L∃T∀t≥T unit-mass-fresh-consistency)]. The negative target is an absence of a semantic history-to-law function with the complete predicate, even before any effectiveness restriction is imposed.

**Edges and anchors.** This type does not itself give a numerical failing tolerance or say every positive tolerance fails; the quantifier negation is preserved. It does not assert a partition. H₀ is the specifically defined singleton containing Nat, so “countable” here does not introduce an unknown class or imply infinitely many languages. HasFiniteSupport cannot be replaced by HasFiniteExactProfileSupport when reading the premises. No assertion about a printed paper follows from the identifier. Dependencies: D:305,350,535,743,758,839,894,907,920.

### 11. corrected_lemma_4_8

**Identifier:** `GenLimit.RepresentativeGeneration.Published.corrected_lemma_4_8`. **Anchor:** T:170; J row 83; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:156`.

```lean
∀ {α : Type u_1} {H : GenLimit.Generic.LanguageClass.{u_1} α} {groups : Nat → Set.{u_1} α},
  GenLimit.Generic.UUS.{u_1} H →
    GenLimit.RepresentativeGeneration.HasFiniteExactProfileSupport.{u_1} H groups →
      ∀ {L : GenLimit.Generic.Language.{u_1} α},
        Membership.mem.{u_1, u_1} H L →
          ∀ {stream : GenLimit.Generic.Stream.{u_1} α},
            GenLimit.Generic.Presents.{u_1} stream L →
              ∀ {alpha : Real},
                LT.lt.{0} 0 alpha →
                  ∃ T,
                    ∀ (t : Nat),
                      LE.le.{0} T t → GenLimit.RepresentativeGeneration.IsAlphaFeasibleAt.{u_1} L groups alpha stream t
```

**Reconstruction.** For every A, H, and groups, suppose each member of H is infinite and H has finite exact-profile support. For every L∈H, every stream presenting L, and every real a>0, some natural T makes L feasible at every t≥T. Expanded feasibility chooses a normalized law supported on L∖Sₜ and within group-coordinate error a of the distinct-sample empirical probabilities at that same time.

**Skeleton and access.** ∀A H groups, UUS→exact-profile-support→∀L∈H∀stream, Presents→∀a>0∃T∀t≥T∃μ [SupportedOn(μ,L∖Sₜ)∧Δ(μ,Sₜ)≤ofReal(a)]. T may depend on H, groups, L, the presentation, and a; μ may additionally vary with t. No common μ, common threshold over presentations, history-function witness, or computable selection is concluded.

**Edges and anchors.** No ambient countability/nonemptiness, countability of H, group cover, partition, or upper bound a≤1 is assumed. In particular, exact profiles still compare membership at every group index even if groups overlap or fail to cover. Empty H makes the member-wise conclusion vacuous; finite member languages are excluded by UUS, so an actual target is not exhausted by a finite sample. Feasibility is still a statement about each eventual time, not just a frequently occurring subsequence. Dependencies: D:171,318,366,699,727.

### 12. corrected_theorem_4_4

**Identifier:** `GenLimit.RepresentativeGeneration.Published.corrected_theorem_4_4`. **Anchor:** T:189; J row 84; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:171`.

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] [Countable.{u_1 + 1} α] (H : GenLimit.Generic.LanguageClass.{u_1} α)
  (groups : Nat → Set.{u_1} α),
  Set.Countable.{u_1} H →
    GenLimit.Generic.UUS.{u_1} H →
      GenLimit.RepresentativeGeneration.GroupsCover.{u_1} groups →
        GenLimit.RepresentativeGeneration.HasFiniteExactProfileSupport.{u_1} H groups →
          GenLimit.RepresentativeGeneration.RepresentativelyGeneratableInLimit.{u_1} H groups
```

**Reconstruction.** For any nonempty countable A, countable class H of infinite languages, and Nat-indexed grouping whose union is A, finite exact-profile support implies representative generation in the limit. The result supplies, for each positive real tolerance, one semantic history-to-distribution function globally accurate on every stream at positive times; on each presentation of each member language its mass is eventually always 1 on the fresh part of that language.

**Skeleton and access.** ∀A [Nonempty] [Countable] ∀H groups, countable(H)→UUS(H)→cover(groups)→exact-profile-support(H,groups)→∀a>0∃gen [accuracy(a)∧∀L∈H∀stream presenting L∃T∀t≥T consistency]. The generator is uniform across L and presentations at its chosen tolerance; the eventual threshold need not be. The countability hypothesis is not an effective enumeration supplied as a run-time argument.

**Edges and anchors.** H need not itself be infinite or nonempty. Groups need only cover: no disjointness, injectivity, or nonempty-piece hypotheses are present, and duplicates are permitted. This theorem therefore cannot be read by importing the partition assumptions of the uniform characterization. Its support condition is exactly finite exact-profile points, rather than the earlier positive-intersection sum. No quantitative convergence rate, oracle implementation, or single generator across all a is stated. Dependencies: D:171,305,318,387,427,535,699,727.

### 13. lemma_4_9

**Identifier:** `GenLimit.RepresentativeGeneration.Published.lemma_4_9`. **Anchor:** T:203; J row 87; supplied source `GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean:185`.

```lean
GenLimit.RepresentativeGeneration.MembershipQuery.finiteQuery_impossibility_statement
```

**Reconstruction.** For every real a with 0<a<1/2, there is no M:Algorithm Nat Nat whose next-step function is ordinary computable and which has the specified guarantee for every infinite target subset of Nat and every firstGroup subset of Nat. One M must work for all those targets and groups at its fixed tolerance. The grouping is exactly firstGroup at index 0, its complement at index 1, and the empty set at every larger index.

**Oracle procedure and information.** Algorithm has two fields: next takes an ordered input list and a finite list of answered queries, returning either a new query or a natural-number output code; decode maps each natural code to a discrete distribution on Nat. A query is (Option Nat,point): none asks target membership; some i asks membership in group i. An answered query pairs this with a Boolean that is true exactly when the queried point belongs to that set. At trace position k, next on the same input history and the preceding k answered queries must request precisely that position’s query, and its answer must be correct. Termination additionally requires next on the full finite trace to return the given code. OutputsAt means existence of such a valid terminating trace for the prefix of the stream at that time. Empty traces and adaptive queries are allowed; no fixed number of queries, bound uniform across inputs, or finite total across all times is imposed.

**The three simultaneous guarantee clauses.** First, for every stream and every positive t, some output code exists. Second, for every such stream/time and every code that can be output, its decoded law has Δ≤ofReal(a) relative to that prefix’s distinct sample. These two obligations apply even off target presentations. Third, for every stream presenting the target, some T makes every output at every t≥T decode to a law SupportedOn(target∖Sₜ). This last clause retains its conditional “if OutputsAt” form and universal code quantifier; termination is separately guaranteed only at positive times. At time zero the support implication can be vacuous.

**Skeleton and scope.** ∀a∈(0,1/2), ¬∃M [Computable₂(M.next)∧∀target firstGroup (infinite(target)→[positive-time termination∧positive-time global accuracy∧presentation-wise eventual fresh support])]. M precedes both sets; no effective presentation of either set is required, because membership answers supply the declared oracle information. Computability applies to next, not decode. The decoder is total but may be noncomputable; there is no effective mass evaluation or sampling assumption to add. The target does not rule out noncomputable controllers, controllers specialized to a fixed target or grouping, or the endpoint a=1/2. a=0 is also excluded. An infinite target prevents exhausted finite samples; firstGroup may be empty or all Nat. This is a finite-transcript oracle model, not simply an unsupported claim that every imaginable oracle program fails.

**Anchors.** D:987,997,1036,1053,1066,1084,1097,1120,1146,1164,1181,1197,1210,1227,1243,1257; source `FiniteQueryImpossibility.lean`:39–114,137,184,194. D:1275 and D:1302 export generated matches for the displayed Nat/Option cases; D:1294 exports only an auxiliary numeral-instance theorem type. None adds a hidden learner premise. The ordinary computability/encoding boundary is assumed as declared, rather than audited recursively.

## Exhaustive target coverage

| # | Target suffix | Preserved hypothesis and conclusion coverage | Dependency / witness boundary |
|---|---|---|---|
| 1 | theorem_3_3 | Nonempty/countable A; UUS; partition; a>0; fixed-a generation iff finite dimension with both obstruction alternatives | gen and trigger uniform in L/stream; dimension bound separate |
| 2 | corollary_3_4 | Same ambient/class/group assumptions; left 0<a≤1; right every a>0 | All witnesses may vary with a |
| 3 | corollary_3_5 | Finite H; UUS; arbitrary finite partition; extended-group uniform conclusion | Mathematical finite class; no enumeration algorithm |
| 4 | corollary_3_6 | Existential H/groups; countability; UUS; two-group partition; ordinary uniform; negated representative uniform | Nat ⊕ Nat; Fin 2; unnamed witnesses |
| 5 | theorem_3_7 | Exact equivalence; monotone cover and union equality; every stage fixed-a uniform | Cover chosen after a; no ambient/partition assumptions |
| 6 | corollary_3_8 | Countable infinite H; UUS; arbitrary finite partition; both nonuniform and limit conclusions | Language threshold versus presentation time; separate witnesses |
| 7 | lemma_4_3 | Partition, injectivity, each piece nonempty, finite H, ncard=1, UUS, three negative clauses | Nat; unnamed witnesses; fixed-a failure only 0<a<1 |
| 8 | lemma_4_6 | Presentation; eventual all-time criticality with all three criticality conjuncts | family/stream/z-dependent T; earlier indices only |
| 9 | printed_lemma_4_8_counterexample | Four class/group/support clauses, target membership, presentation, no eventual feasibility at 1/2 | Named Nat data; ∃μ occurs inside every time |
| 10 | printed_theorem_4_4_counterexample | Countability, UUS, cover, finite support, negated complete limit predicate | Named data; no tolerance witness printed |
| 11 | corrected_lemma_4_8 | UUS, exact-profile support, target membership, presentation, positive a, eventual feasibility | ∃T∀t≥T∃μ; no generator conclusion |
| 12 | corrected_theorem_4_4 | Nonempty/countable A; countable H; UUS; cover; exact-profile support; complete limit conclusion | One gen per a; T per language/presentation |
| 13 | lemma_4_9 | 0<a<1/2; no universal computable controller; all infinite targets/all binary groupings; all three guarantee clauses | Finite adaptive oracle traces; arbitrary total decoder |

No target was omitted or replaced by another declaration with a similar label. Every original type is quoted in full above. The glossary and dossiers expand every project predicate in those types through the exported definition/constructor boundary, including the all-subsets support sum and all guarantee clauses. Conditional consistency promises retain their sample-trigger, presentation, or OutputsAt premises; their vacuous cases are not turned into unconditional outputs.

## Limits of the reconstruction

This is a type-and-definition reconstruction, not a proof audit, fresh compilation, source-paper comparison, judgment of the source labels, or human certification. Provided theorem types are treated as the objects to interpret. The report does not assert the excluded proof bodies are sound, that raw sources reproduce the export, or that the supplied dirty snapshot agrees with a clean checkout. Auxiliary theorem proof values were not inspected. Standard-library boundary meanings, including unconditional sums over possibly uncountable index types and computability encodings, were assumed rather than rederived.

Existential witnesses are left unspecified unless an exported definition fixes them. Countable/finiteness propositions do not become effective access for free. No results are claimed about output independence, full support, input sampling distributions, probabilistic success over a text distribution, convergence rates, least thresholds, or endpoint accuracies absent from the types. Actual input digests, scope, configuration observability, access history, and this report’s digest are in the paired run record.
