# P10: paper-withheld reconstruction from the Stage 1 interface

This report interprets statements and definition values, not proof correctness or fidelity to a paper. Its evidence is confined to this package's stage1/ interface. Identifier names and source anchors locate declarations; their wording supplies no extra mathematical meaning. There are ten targets and 37 recursively relevant definitions, with no missing project declaration in the exported dependency closure. The original types below are copied exactly from declarations.jsonl, including suppressed binder annotations. The additive explicit-type supplement is used only to disambiguate hidden arguments and domains.

## Input census and boundary

Input root: /Users/pengzhang/Documents/research/language-generation-non-p38/audit-packages/P10_2026-11-10_6062058/stage1

| Actual input | Bytes | SHA256 |
|---|---:|---|
| stage1/01-target-statements.md | 5307 | e8facfb0114515ff73c59152d6debf0b7d3d2785e17500113cfe796396d3404c |
| stage1/02-definition-dependencies.md | 15679 | e8e2ce5063abaf7109216ce04e31a4c73dfab65e9bbbd152334036f6cd692aca |
| stage1/PROMPT.md | 1827 | d79a9f3221e3fdc6cdb3835026d91ba49ca51b6fade5f30a27d10c5aba9eed4e |
| stage1/SHA256SUMS | 928 | cca1566cbdefc68b932df154c48d790654a70f2f73bf301b23bc14b2c76917ea |
| stage1/START_HERE.md | 190 | 71b6b5245181590824f4a8bed9a9d73631aa2d4d4af36770f0162a4d93db28a8 |
| stage1/declarations.jsonl | 34400 | a12211af653cb0cbef014d6e7bbedb506ec542d5aad2194f111ad66fbb025156 |
| stage1/external-constant-boundary.txt | 641 | f786bd7c7e3a2c6c56172c6f1faf3690d3cf897700e322ebf0909b26192fa917 |
| stage1/lake-manifest.json | 3100 | 994d8b6a379cea0e626d27fe8fa2fc74a2d966197a6998ecde6bd419634991aa |
| stage1/lakefile.toml | 379 | 0fef48c5e314b7476f09da4caa5615d58a50937752aea1b192c0921a05b6e3d0 |
| stage1/lean-toolchain | 25 | 42779d67b81608af8a12aa4328d2ab47ca201925b3b2bd68369587b5340bb434 |
| stage1/snapshot.json | 15553 | 4029efeb870df83ef0f08bd71475ef08c24fc7af55f5e0e8b57838bf12066ea9 |
| stage1/targets.txt | 455 | 0f6809cbf40ad65bb243cdbda6a6d58009a8eb787bfe6098b0376d84f9681a9a |
| stage1/explicit-target-types/README.md | 416 | 3f515d4347a3fe595f0760ec512dc956fbc0c3728260bf167e63d38511e7134b |
| stage1/explicit-target-types/SHA256SUMS | 154 | a498dd464eca6620c6f2bcdded7a5c77c85fa74ea6e8f6cc7a01ceb9db56effc |
| stage1/explicit-target-types/types.jsonl | 5189 | 5a516953f85b39be8b9f5089cedbfaff7f6db84662d4a5fa91779bbe95f98401 |

The original twelve files were consumed first. During reconstruction, suppressed alphabet arguments prompted a request for clarification. The coordinator then supplied only the additive three-file explicit-target-types/ supplement; it was read after the preliminary in-memory draft and before either output was written. Its two manifest entries were verified at 2026-11-10T05:58:54.836156+00:00. Every explicit target type fixes the alphabet to Int; in particular the hidden existential domains are G.LanguageClass Int. The original signatures remain unchanged.

All original SHA256SUMS entries were checked against actual bytes. The ten roots agree with targets.txt. The snapshot describes a dirty working-tree byte snapshot, not a clean-commit verification: captured_at_utc = 2026-11-10T05:48:29.344848+00:00, recorded head = 60620581aa210daec6fa7d3aa65d7f9fdb565b8c, recorded branch = work/non-p38. Those are supplied metadata, not independently checked Git facts. Source filenames and hashes in snapshot.json were read as metadata; the corresponding source files were not opened.

Lean v4.24.0 and Mathlib v4.24.0 are the supplied configuration; the manifest records Mathlib revision f897ebcf72cd16f89ab4577d0c826cd14afaafc7. No compiler or build was run. Standard Lean/Mathlib meanings of Nat, Int, sets, finite sets, countability, finiteness, infinitude, injectivity, logical connectives and coercions are assumed at the disclosed external-constant boundary. No recursive external-body audit was performed. No paper, proof body, developer commentary, owner/, other stage, previous result, PaperMap, registry or other audit package was consulted.

## Typed definition glossary

For compactness, G means GenLimit.Generic, U means GenLimit.UnionClosedness, and R means GenLimit.LiRamanTewari. These are namespace abbreviations in this report, not new exported definitions. Unless a definition fixes Int, α is implicitly quantified as {α : Type u}; all t, s, d, T and i below have type Nat. The formulas give the full binder and predicate structure in ordinary Lean notation.

### Histories, outputs and correctness: eleven definitions

The following signatures and equations reconstruct G.Language, G.LanguageClass, G.Stream, G.FiniteHistoryOperator and G.Generator:

~~~lean
Language (α : Type u) : Type u := Set α
LanguageClass (α : Type u) : Type u := Set (Language α)
Stream (α : Type u) : Type u := Nat → α
FiniteHistoryOperator (Input : Type u) (Output : Type v) : Type (max u v) :=
  (t : Nat) → (Fin t → Input) → Output
Generator (α : Type u) : Type u := FiniteHistoryOperator α α
~~~

For x : Stream α and F : Generator α, the remaining six are:

~~~lean
sample (x : Stream α) (t : Nat) : Finset α :=
  Finset.image x (Finset.range t)
output (F : Generator α) (x : Stream α) (t : Nat) : α :=
  F t (fun i : Fin t => x i.val)
CorrectAt (F : Generator α) (L : Language α) (x : Stream α) (t : Nat) : Prop :=
  output F x t ∈ L ∧ output F x t ∉ sample x t
StreamIn (x : Stream α) (L : Language α) : Prop := Set.range x ⊆ L
Presents (x : Stream α) (L : Language α) : Prop := Set.range x = L
UUS (H : LanguageClass α) : Prop := ∀ L, L ∈ H → Set.Infinite L
~~~

These come from GenLimitLean/GenLimit/Core/GenericGeneration.lean:21, :24, :31, :37, :41, :63, :87, :367, :54 and :50, respectively; UUS is anchored at GenLimitLean/GenLimit/Core/ClassGeneration.lean:13. A history has positions 0 through t−1; the current stream value x t is not observed at time t. The sample forgets order and duplicate occurrences, although the generator receives the ordered history. CorrectAt is a conjunction of target membership and novelty relative to observed inputs. It does not require distinct successive generated outputs.

### Sample-threshold generation: four definitions

Use S_x(t) for sample x t and C(F,L,x,t) for CorrectAt F L x t. All quantifiers over x below range over Stream α:

~~~lean
IsUniformGeneratorAt (F : Generator α) (H : LanguageClass α) (d : Nat) : Prop :=
  ∀ L, L ∈ H → ∀ x, StreamIn x L →
    ∀ t, (S_x(t)).card = d → ∀ s, t ≤ s → C(F,L,x,s)
UniformlyGeneratable (H : LanguageClass α) : Prop :=
  ∃ F d, IsUniformGeneratorAt F H d
IsNonuniformGenerator (F : Generator α) (H : LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∃ d, ∀ x, StreamIn x L →
    ∀ t, (S_x(t)).card = d → ∀ s, t ≤ s → C(F,L,x,s)
NonuniformlyGeneratable (H : LanguageClass α) : Prop :=
  ∃ F, IsNonuniformGenerator F H
~~~

Anchors: GenLimitLean/GenLimit/Core/ClassGeneration.lean:26, :33, :37 and :44. Write W(H) for UniformlyGeneratable H and N(H) for NonuniformlyGeneratable H. In N, one generator serves the whole class, while d may depend on L and that generator, and cannot depend on the stream. In W, both generator and d are chosen before every L and stream. The trigger is literally equality of distinct-sample cardinality to d, followed by correctness at every later s, not a fixed amount of elapsed time. No rate or numerical bound on d is supplied.

### Limit generation on injective presentations: two definitions

~~~lean
IsLimitGeneratorOnInjectivePresentations
    (F : Generator α) (H : LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∀ x, Function.Injective x → Presents x L →
    ∃ T, ∀ t, T ≤ t → C(F,L,x,t)
GeneratableInLimitOnInjectivePresentations (H : LanguageClass α) : Prop :=
  ∃ F, IsLimitGeneratorOnInjectivePresentations F H
~~~

Anchors: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Definitions.lean:32 and :41. Write I(H) for the second predicate. Here the convergence time may depend on the entire presentation as well as L and F. The generator still only sees its finite prefix at execution time. Injectivity forbids repeated input values; presentation requires every target element to appear. There is no single T for all streams.

Classically, ¬I(H) reads: for every F there exist L ∈ H and an injective x with range x = L such that, for every T, some t ≥ T violates C(F,L,x,t). Thus the target failures below are arbitrarily late failures of at least one correctness conjunct. They are not claims that every output fails, or statements of a quantitative limsup.

### Schedules with no stream input: five definitions

~~~lean
NoAdversaryInputSchedule (α : Type u) : Type u := Nat → α
IsUniformNoAdversaryInputScheduleAt
    (o : NoAdversaryInputSchedule α) (H : LanguageClass α) (T : Nat) : Prop :=
  Function.Injective o ∧ ∀ L, L ∈ H → ∀ t, T ≤ t → o t ∈ L
UniformlyGeneratableWithoutAdversaryInput (H : LanguageClass α) : Prop :=
  ∃ o T, IsUniformNoAdversaryInputScheduleAt o H T
IsNonuniformNoAdversaryInputSchedule
    (o : NoAdversaryInputSchedule α) (H : LanguageClass α) : Prop :=
  Function.Injective o ∧ ∀ L, L ∈ H → ∃ T, ∀ t, T ≤ t → o t ∈ L
NonuniformlyGeneratableWithoutAdversaryInput (H : LanguageClass α) : Prop :=
  ∃ o, IsNonuniformNoAdversaryInputSchedule o H
~~~

Anchors: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/WithoutAdversaryInput.lean:29, :33, :41, :48 and :56. Write W₀(H) and N₀(H) for the uniform and nonuniform existence predicates. One fixed injective sequence serves each class; the nonuniform tail start depends on L, whereas the uniform tail start is shared by all L. Injectivity holds from time zero, including the unconstrained initial membership segment. There is no adversary stream or sample argument, and no assertion of freshness relative to an adversary's observations.

### Version spaces and closure: four definitions

~~~lean
versionSpace (H : LanguageClass α) (S : Finset α) : Set (Language α) :=
  {L | L ∈ H ∧ (↑S : Set α) ⊆ L}
G.commonCore (H : LanguageClass α) (S : Finset α) : Language α :=
  {a | ∀ L, L ∈ versionSpace H S → a ∈ L}
R.commonCore (H : LanguageClass α) (S : Finset α) : Language α :=
  G.commonCore H S
EventuallyUnboundedClosure (H : LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∀ x, Presents x L →
    ∃ t, Set.Infinite (R.commonCore H (sample x t))
~~~

Anchors: GenLimitLean/GenLimit/Core/VersionSpace.lean:16 and :20; GenLimitLean/GenLimit/Paper02_LearningTheory/Definitions.lean:23; and GenLimitLean/GenLimit/Paper02_LearningTheory/EventuallyUnboundedClosure.lean:26. Write E(H) for the final predicate. It asks for one finite observation time with infinite intersection of consistent class members, separately for every exhaustive stream. Repetitions are allowed. It has no injectivity hypothesis, explicit cardinality growth rate, or global time bound.

Classically ¬E(H) means there exist L ∈ H and a presenting x such that every finite-time common core is not infinite (equivalently finite under the standard set boundary). The empty version space would give the whole alphabet as its common core by vacuity, but along a valid presentation L itself is consistent, so that case cannot produce the required infinitude spuriously.

### Integer families: eleven definitions

All classes below have the exact signature G.LanguageClass Int; integer subsets have type Set Int. Define N⁻ = U.negativeIntegers = {z : Int | z < 0}, P = U.positiveIntegers = {z : Int | 0 < z}, and U.negativeCode : Nat → Int by negativeCode n = Int.negSucc n = −(n+1). Anchors are GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/SignedIntegers.lean:18, :53 and :21.

U.signedDeletionLanguage : Set Int → Set Int → Set Int is
(A,B) ↦ (N⁻ ∖ A) ∪ (P ∖ B). Its anchor is GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/MainClasses.lean:20. The two class definitions at :25 and :34 are exactly:

~~~text
C_fi = finiteNegativeInfinitePositiveClass
L ∈ C_fi ↔ ∃ A B, A ⊆ N⁻ ∧ Set.Finite A ∧
                    B ⊆ P ∧ Set.Infinite B ∧ L = signedDeletionLanguage A B
C_if = infiniteNegativeFinitePositiveClass
L ∈ C_if ↔ ∃ A B, A ⊆ N⁻ ∧ Set.Infinite A ∧
                    B ⊆ P ∧ Set.Finite B ∧ L = signedDeletionLanguage A B
~~~

The finite/infinite qualifiers describe deleted subsets. In C_fi the retained positive side may be empty, even when the deleted B is infinite; the cofinite negative side supplies infinitude. In C_if the retained negative side may be empty; the cofinite positive side supplies infinitude. Neither class contains zero.

At GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/MinimalPairClasses.lean:25, :30, :36, :41 and :46, the five remaining definitions are:

~~~text
theorem43FirstLanguage : Set Int → Set Int
theorem43FirstLanguage A = N⁻ ∪ A
D = theorem43FirstClass
L ∈ D ↔ ∃ A, A ⊆ P ∧ L = theorem43FirstLanguage A

negativePrefix : Nat → Set Int
negativePrefix i = ↑(Finset.image negativeCode (Finset.range i))
                 = {−1, …, −i}
theorem43SecondLanguage : Nat → Set Int → Set Int
theorem43SecondLanguage i B = negativePrefix i ∪ (P ∖ B)
Bclass = theorem43SecondClass
L ∈ Bclass ↔ ∃ i B, B ⊆ P ∧ Set.Finite B ∧
                       (i = 0 → B = ∅) ∧ L = theorem43SecondLanguage i B
~~~

The notation {−1, …, −i} denotes the empty set at i = 0. D allows every positive subset, including empty or infinite ones. Bclass allows any finite positive deletion for i > 0. The zero condition is one implication: B = ∅ is also permitted for i > 0. At i = 0 only P occurs. Every Bclass member has a cofinite positive side; every D member contains all negative integers. These are extensional sets of languages, so any repeated representation does not create another class element. There is no indexed family of learner programs hidden in the index i.

## Shared interpretation and edge cases

Every existential generator or schedule is semantic existence of a total mathematical function. No computability predicate, algorithm encoding, oracle interface, access to a membership tester, runtime bound, or effective enumeration is supplied. Class-dependent choice of a function is permitted by the quantifiers; even the uniform predicates do not assert a uniform program that takes arbitrary H as input. A named class is specified, but its witnessing function and thresholds remain unspecified in these target types.

There are no probability laws, distributions, full-support assumptions, random seeds, support-valued outputs or statistical losses. Each output is one alphabet element. Sample-threshold and limit predicates use the same membership-and-input-novelty conjunction; schedule predicates use eventual membership plus global distinctness of scheduled outputs. None requires the outputs to enumerate the target.

For N and W, a stream may repeat forever without exhausting its target. If it never attains d distinct values, the trigger is never activated. In particular a finite target permits vacuity by choosing d above its size; d = 0 instead triggers at t = 0. If a sample exhausts a finite L, CorrectAt is impossible because no member remains fresh. Empty languages admit no Nat-indexed stream at all. Finite languages admit no injective Nat-indexed presentation, so I imposes no condition on them. N₀ and W₀ do require every member to contain an infinite injective tail. UUS explicitly excludes empty and finite member languages, but permits an empty class. An empty class vacuously satisfies universal member conditions; a schedule still must itself be injective, which is possible on Int.

For E, a nonempty finite target has a presenting stream and finite common cores, while an empty target has none. These distinctions matter for the unspecified existential classes: their displayed conjunctions do not separately include UUS. Do not import a UUS assertion from an adjacent named-class theorem.

Countability concerns the set of languages, not the alphabet or each individual language. A countable class may be finite or empty and need not have a supplied effective enumeration. An uncountable class of subsets of countable Int is consistent. Class union H₁ ∪ H₂ means languages belonging to either class, not unions of pairs of languages. No theorem quantifies over countable sequences of classes, a cover, or arbitrary repeated class indices. Only stream and schedule injectivity forbid repetitions; elsewhere duplicate observations are permitted. No constants, rates, scales or finite upper bounds are implicit in the theorem numbering.

## Target dossiers

The following exact exported types are followed by reconstructions using the glossary abbreviations. All ten targets have no displayed hypotheses or type/universe parameters. Their common source module is GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Results.Overview.

### 1. GenLimit.UnionClosedness.theorem_3_1

Source anchor supplied by the export: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean:28

Exact exported type:

~~~lean
∃ H₁ H₂,
  And (Not (Set.Countable.{0} H₁))
    (And (GenLimit.Generic.NonuniformlyGeneratable.{0} H₁)
      (And (Not (Set.Countable.{0} H₂))
        (And (GenLimit.Generic.NonuniformlyGeneratable.{0} H₂)
          (Not (GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations.{0} (Union.union.{0} H₁ H₂))))))
~~~

Reconstruction: there exist classes H₁ and H₂ of integer languages such that H₁ is uncountable and N(H₁), H₂ is uncountable and N(H₂), and I(H₁ ∪ H₂) fails. All five conjuncts apply to the same selected pair. The two component generators may differ; each has its own language-dependent sample threshold.

Skeleton: ∃ H₁ H₂ : G.LanguageClass Int, ¬Countable H₁ ∧ N(H₁) ∧ ¬Countable H₂ ∧ N(H₂) ∧ ¬I(H₁ ∪ H₂), with each N expanded by the complete glossary schema.

Information: each F receives time and ordered finite input history, with no target-language identifier. Any candidate union generator has the same interface. No named class is asserted to equal H₁ or H₂. The type does not separately require UUS, disjointness, or a specified overlap. Uncountability rules out empty or finite classes; the refuting injective presentation necessarily has an infinite target.

### 2. GenLimit.UnionClosedness.theorem_3_1_witness_uus

Source anchor supplied by the export: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean:38

Exact exported type:

~~~lean
And (GenLimit.Generic.UUS.{0} GenLimit.UnionClosedness.finiteNegativeInfinitePositiveClass)
  (GenLimit.Generic.UUS.{0} GenLimit.UnionClosedness.infiniteNegativeFinitePositiveClass)
~~~

Reconstruction and skeleton: [∀ L, L ∈ C_fi → Infinite L] ∧ [∀ L, L ∈ C_if → Infinite L]. This is exactly UUS(C_fi) ∧ UUS(C_if).

Information: no learner, stream or schedule is quantified. The conclusion is about every member's size, not uncountability of either class or existence of a generator. The finite deleted side may be empty; the opposite infinite deleted side may exhaust that entire sign. The cofinite retained side still prevents an empty or finite member. The type does not identify these classes with the pair existentially selected in target 1.

### 3. GenLimit.UnionClosedness.theorem_3_2_witness

Source anchor supplied by the export: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean:49

Exact exported type:

~~~lean
And (Set.Countable.{0} GenLimit.UnionClosedness.theorem43SecondClass)
  (And
    (GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput.{0}
      GenLimit.UnionClosedness.theorem43SecondClass)
    (And (Not (Set.Countable.{0} GenLimit.UnionClosedness.theorem43FirstClass))
      (And
        (GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput.{0}
          GenLimit.UnionClosedness.theorem43FirstClass)
        (Not
          (GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations.{0}
            (Union.union.{0} GenLimit.UnionClosedness.theorem43SecondClass
              GenLimit.UnionClosedness.theorem43FirstClass))))))
~~~

Reconstruction: Bclass is countable and N₀(Bclass); D is uncountable and W₀(D); I(Bclass ∪ D) fails. The class order in the union and in the five conjuncts is Bclass first, D second.

Skeleton: Countable Bclass ∧ [∃ o_B, Injective o_B ∧ ∀ L ∈ Bclass, ∃ T_L, ∀ t ≥ T_L, o_B t ∈ L] ∧ ¬Countable D ∧ [∃ o_D T_D, Injective o_D ∧ ∀ L ∈ D, ∀ t ≥ T_D, o_D t ∈ L] ∧ ¬I(Bclass ∪ D).

Information: o_B and o_D receive only their time index and may differ. Neither sequence observes a presentation. The failed union learner does observe finite histories. No schedule or tail start is named or bounded. In particular i = 0 in Bclass allows only the undeleted positive integers; arbitrary finite B at that index would change the statement.

### 4. GenLimit.UnionClosedness.theorem_3_2_witness_standard

Source anchor supplied by the export: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean:66

Exact exported type:

~~~lean
And (Set.Countable.{0} GenLimit.UnionClosedness.theorem43SecondClass)
  (And (GenLimit.Generic.NonuniformlyGeneratable.{0} GenLimit.UnionClosedness.theorem43SecondClass)
    (And (Not (Set.Countable.{0} GenLimit.UnionClosedness.theorem43FirstClass))
      (And (GenLimit.Generic.UniformlyGeneratable.{0} GenLimit.UnionClosedness.theorem43FirstClass)
        (Not
          (GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations.{0}
            (Union.union.{0} GenLimit.UnionClosedness.theorem43SecondClass
              GenLimit.UnionClosedness.theorem43FirstClass))))))
~~~

Reconstruction: Bclass is countable and N(Bclass); D is uncountable and W(D); I(Bclass ∪ D) fails. This retains the countability and failure conjuncts of target 3 but states different generation predicates.

Skeleton: Countable Bclass ∧ N(Bclass) ∧ ¬Countable D ∧ W(D) ∧ ¬I(Bclass ∪ D), with N and W expanded by their complete glossary schemas.

Information: both generators receive time and ordered histories from arbitrary streams contained in their targets. These streams need not be injective or exhaustive. The two generators and their thresholds need not agree with one another or be constructed from the schedules in target 3. Correctness includes input novelty. Countability does not specify a program enumerating Bclass.

### 5. GenLimit.UnionClosedness.theorem_3_2_witness_uus

Source anchor supplied by the export: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean:83

Exact exported type:

~~~lean
And (GenLimit.Generic.UUS.{0} GenLimit.UnionClosedness.theorem43SecondClass)
  (GenLimit.Generic.UUS.{0} GenLimit.UnionClosedness.theorem43FirstClass)
~~~

Reconstruction and skeleton: [∀ L, L ∈ Bclass → Infinite L] ∧ [∀ L, L ∈ D → Infinite L]. Both conjuncts quantify over the full respective classes.

Information: this is a size assertion without an information-processing interface. Bclass's finite negative prefix is allowed to be empty, but its positive part is cofinite. D may have no positive elements, but contains all negative integers. Neither family includes zero. This theorem adds no generation, countability or union-failure conjunct, and supplies no uniform lower bound beyond infinitude.

### 6. GenLimit.UnionClosedness.theorem_3_2

Source anchor supplied by the export: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean:92

Exact exported type:

~~~lean
∃ H₁ H₂,
  And (Set.Countable.{0} H₁)
    (And (GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput.{0} H₁)
      (And (Not (Set.Countable.{0} H₂))
        (And (GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput.{0} H₂)
          (Not (GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations.{0} (Union.union.{0} H₁ H₂))))))
~~~

Reconstruction: there exist integer-language classes H₁,H₂ such that H₁ is countable and N₀(H₁), H₂ is uncountable and W₀(H₂), and I(H₁ ∪ H₂) fails.

Skeleton: ∃ H₁ H₂, Countable H₁ ∧ N₀(H₁) ∧ ¬Countable H₂ ∧ W₀(H₂) ∧ ¬I(H₁ ∪ H₂). Expanding the schedule predicates places the schedule existential before every member, but the nonuniform T after its member and the uniform T before every member.

Information: the component witnesses are fixed injective time-indexed sequences; the refuted union witness is a history-based generator. No relationship between the two sequences is required. No particular H₁,H₂, output functions or times are specified. Countable does not mean countably infinite. The schedule clauses ensure infinite member languages without a separate UUS conjunct; the uncountable second class cannot be empty.

### 7. GenLimit.UnionClosedness.theorem_3_2_standard

Source anchor supplied by the export: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean:102

Exact exported type:

~~~lean
∃ H₁ H₂,
  And (Set.Countable.{0} H₁)
    (And (GenLimit.Generic.NonuniformlyGeneratable.{0} H₁)
      (And (Not (Set.Countable.{0} H₂))
        (And (GenLimit.Generic.UniformlyGeneratable.{0} H₂)
          (Not (GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations.{0} (Union.union.{0} H₁ H₂))))))
~~~

Reconstruction: there exist integer-language classes H₁,H₂ such that H₁ is countable and N(H₁), H₂ is uncountable and W(H₂), and I(H₁ ∪ H₂) fails.

Skeleton: ∃ H₁ H₂ : G.LanguageClass Int, Countable H₁ ∧ N(H₁) ∧ ¬Countable H₂ ∧ W(H₂) ∧ ¬I(H₁ ∪ H₂). The complete N and W schemas preserve every threshold quantifier.

Information: both component generators and every candidate union generator use finite ordered histories. Threshold d₂ is shared across H₂; d_L is shared across streams of its one L. This statement names no class witnesses and does not equate them with those selected in target 6. It has no explicit UUS conjunct, so finite member languages must be interpreted with the threshold-vacuity boundary above.

### 8. GenLimit.UnionClosedness.theorem_3_3_of_theorem_3_1

Source anchor supplied by the export: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean:117

Exact exported type:

~~~lean
Or
  (Not
    (GenLimit.LiRamanTewari.EventuallyUnboundedClosure.{0}
      GenLimit.UnionClosedness.finiteNegativeInfinitePositiveClass))
  (Not
    (GenLimit.LiRamanTewari.EventuallyUnboundedClosure.{0}
      GenLimit.UnionClosedness.infiniteNegativeFinitePositiveClass))
~~~

Reconstruction and skeleton: ¬E(C_fi) ∨ ¬E(C_if). At least one named class fails the closure predicate; the type neither selects a side nor asserts that exactly one side fails. Despite the identifier, there is no implication premise mentioning another theorem.

Classically, one side has some L in that class and a possibly repetitive exhaustive x such that ∀ t, commonCore(class, sample x t) is finite. The outer disjunction applies to this whole failure statement on each side. It supplies no fixed language or stream.

Information: closure quantifies over observed finite samples mathematically; it is not an algorithm given access to the common core. Its presentations need not be injective. Both named classes have only infinite members, but infinitude of L alone does not force the intersection of consistent alternatives to be infinite.

### 9. GenLimit.UnionClosedness.theorem_3_3

Source anchor supplied by the export: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean:177

Exact exported type:

~~~lean
∃ H,
  And (Not (Set.Countable.{0} H))
    (And (GenLimit.Generic.NonuniformlyGeneratable.{0} H)
      (Not (GenLimit.LiRamanTewari.EventuallyUnboundedClosure.{0} H)))
~~~

Reconstruction: there exists an integer-language class H that is uncountable, satisfies N(H), and fails E(H). The same H satisfies all three conjuncts.

Skeleton: ∃ H : G.LanguageClass Int, ¬Countable H ∧ N(H) ∧ ¬[∀ L ∈ H, ∀ x, Presents x L → ∃ t, Infinite(commonCore H (sample x t))], with N expanded by its complete glossary schema. Thus the generator is shared by H, thresholds depend on member languages, and closure failure admits a bad language and exhaustive stream.

Information: F receives ordered finite history. The closure clause concerns all consistent languages rather than a learner oracle. H, F, the thresholds and the bad presentation remain unspecified. No uniform threshold, quantitative rate or UUS conjunct occurs. Target 10 does not identify H. In particular one must not silently assume the closure-failure witness is infinite merely from this abstract type.

### 10. GenLimit.UnionClosedness.theorem_3_3_witness_uus

Source anchor supplied by the export: GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean:188

Exact exported type:

~~~lean
GenLimit.Generic.UUS.{0} GenLimit.UnionClosedness.finiteNegativeInfinitePositiveClass
~~~

Reconstruction and skeleton: ∀ L, L ∈ C_fi → Infinite L. This is exactly UUS(C_fi), repeating the first conjunct of target 2.

Information: no generator or presentation is involved. A finite set of deleted negatives leaves infinitely many negative integers, even if all positive integers are deleted. The assertion contains no uncountability, nonuniform generation, or closure-failure conjunct. In particular it does not prove ¬E(C_fi), choose the failing side of target 8, or say that the existential H in target 9 is C_fi. Those identifications cannot be supplied by the word “witness” in a name.


## Exhaustive coverage

| # | Exact target identifier | Dossier coverage |
|---:|---|---|
| 1 | GenLimit.UnionClosedness.theorem_3_1 | Two unspecified uncountable classes; type, skeleton, information and edge cases |
| 2 | GenLimit.UnionClosedness.theorem_3_1_witness_uus | Infinitude for both signed-deletion classes; type, skeleton, information and edge cases |
| 3 | GenLimit.UnionClosedness.theorem_3_2_witness | Named classes with fixed schedules; type, skeleton, information and edge cases |
| 4 | GenLimit.UnionClosedness.theorem_3_2_witness_standard | Named classes with history generators; type, skeleton, information and edge cases |
| 5 | GenLimit.UnionClosedness.theorem_3_2_witness_uus | Infinitude for the minimal integer families; type, skeleton, information and edge cases |
| 6 | GenLimit.UnionClosedness.theorem_3_2 | Unspecified classes with fixed schedules; type, skeleton, information and edge cases |
| 7 | GenLimit.UnionClosedness.theorem_3_2_standard | Unspecified classes with history generators; type, skeleton, information and edge cases |
| 8 | GenLimit.UnionClosedness.theorem_3_3_of_theorem_3_1 | A disjunctive closure failure; type, skeleton, information and edge cases |
| 9 | GenLimit.UnionClosedness.theorem_3_3 | An unspecified uncountable class with closure failure; type, skeleton, information and edge cases |
| 10 | GenLimit.UnionClosedness.theorem_3_3_witness_uus | A repeated signed-deletion infinitude assertion; type, skeleton, information and edge cases |

Every supplied root has one dossier and its exact original type; every exported definition occurs in the six glossary groups (11 + 4 + 2 + 5 + 4 + 11 = 37). Repetition across targets has been retained: the countability/generation/failure conjunctions recur with and without named classes, and target 10 repeats the first conjunct of target 2. These repetitions do not strengthen witness identification. This report certifies neither proof bodies nor fresh compilation, source correspondence, paper coverage, or human review. The run record contains actual input and report hashes; its own final-byte hash is returned externally to avoid self-reference.
