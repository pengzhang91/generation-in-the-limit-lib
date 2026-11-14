# Stage 1: reconstruction from Lean interfaces

## Scope and input census

This report reconstructs exactly two exported propositions. Its mathematical evidence consists only of the supplied Stage 1 target types, recursively relevant defining expressions, the explicit-type supplement present at initial handoff, and the subsequently requested code-only clarification described below. Names and source anchors identify declarations; they do not establish their intended meaning. No theorem proof value, raw source, source paper, owner material, registry, PaperMap, other audit package, Stage 2 material, or Stage 3 context was consulted. No compilation, proof audit, source-correspondence judgment, or human certification was performed.

The initial package contains 15 files: instructions (START_HERE.md and PROMPT.md), target census (targets.txt), target statements, dependency statements/values, machine-readable declarations, an external-constant boundary, snapshot metadata, three Lake/toolchain metadata files, explicit-target-types/README.md and types.jsonl, and two SHA256SUMS manifests. All 13 entries in the principal manifest and both entries in the initial explicit-target-types manifest matched their actual SHA256 values before interpretation. The snapshot identifies working-tree bytes, a dirty repository, and HEAD 60620581aa210daec6fa7d3aa65d7f9fdb565b8c; these are package metadata, not independently checked repository facts. Toolchain metadata specifies Lean v4.24.0 and Mathlib v4.24.0. Complete input hashes and chronological access events are recorded in stage1-run.json.

During reconstruction, the original printed Psi value left its existential domain implicit. The coordinator supplied requested-psi-value/README.md, value.jsonl, provenance.json and SHA256SUMS, without changing the initial handoff. Its manifest SHA256 is 7c7257296db0b716e768b4bc2ec72699ed1f66bed1d46b3e7f71ab52305895a6; all three listed files verified. Provenance timestamps its export at 2026-11-10T14:45:37.245699+00:00. The notation-disabled explicit value displays `@Exists (Finset α)` and the predecessor application `x.1 j`, settling the finite-witness domain and recursive argument. This was requested code clarification, not an additional mathematical assumption.

The external boundary authorizes ordinary Lean/Mathlib meanings for sets, finite sets, lists, finite indices, natural-number recursion, equality, order and logical connectives. Their raw library bodies were not inspected. Universe parameters are retained below: α is any type in Type u_1 with the displayed decidable-equality instance. There is no additional countability, infinitude, nonemptiness, decidable-language-membership, or effective-enumeration instance.

## Definition glossary and common quantifier skeleton

Write F_i for F i. Language α means Set α; LanguageFamily α means Nat → Set α; Stream α means Nat → α. Thus the class is indexed by all natural numbers, with no injectivity requirement on the indexing and no restriction on repetitions of equal languages. Presents s L is exactly Set.range s = L: every source item belongs to L, and every element of L appears at some finite source position. Repetitions and arbitrary order are permitted, including repetitions needed to present nonempty finite languages. No delay symbol or finite exhausted-source object appears.

Both targets have the common hypothesis

\[
H(F):\quad \forall i:\mathbb N,\ \exists s:\mathbb N\to\alpha,\quad
 \operatorname{range}(s)=F_i.
\]

This is separate existence of a complete source for each index. It neither supplies a uniform enumeration program nor fixes the source subsequently used by the learner. The success obligation quantifies over every complete source, rather than only the witnesses of H(F). Each F_i must therefore be nonempty and admit such an enumeration. α itself need not be countable or infinite; the family is countably indexed, and each represented language has the stipulated countable presentation.

FiniteHistoryOperator Input Output is (t : Nat) → (Fin t → Input) → Output. Consequently ListIdentifier α k is

\[
 A:(t:\mathbb N)\to(\operatorname{Fin}(t)\to\alpha)
      \to(\operatorname{Fin}(k)\to\mathbb N).
\]

At time t, listOutput A s t applies A to exactly the ordered prefix h_t(q)=s(q.val), q : Fin t. This excludes s(t) from the time-t input. At t=0 the history is empty. The output μ is a function from the k finite positions to natural-number indices, so it is an ordered k-tuple with repetitions permitted, not a Finset of distinct hypotheses.

TargetInGuess F z μ means ∃ r : Fin k, F (μ r) = F z. Equality is equality of sets of α, not equality μ r = z of indices. IdentifiesFrom A F z s means that there is a natural threshold T such that this property holds for every t≥T. ListIdentifies A F quantifies this over all z and all s presenting F_z. ListIdentifiable F k existentially quantifies A once, outside those quantifiers. Their complete expansion is

\[
\mathsf{LI}(F,k):\quad
\exists A,\ \forall z:\mathbb N,\ \forall s:\mathbb N\to\alpha,\
[\operatorname{range}(s)=F_z]\ \Longrightarrow\
\exists T:\mathbb N,\ \forall t:\mathbb N,\ T\le t\ \Longrightarrow\
\exists r:\operatorname{Fin}(k),\
F_{A(t,h_t)(r)}=F_z.
\]

A may depend on F and k. The threshold may depend on A, F, z and the entire presenting source. The successful slot may depend on t as well. No fixed correct slot, final fixed index, eventual fixed tuple, or uniform threshold is required. Every sufficiently late tuple must contain some semantic representative of the target; a merely frequent occurrence would be weaker. The other slots may remain incorrect.

The remaining dependency chain has these exact contents:

* Psi F i 0 is False. At a successor depth, its defining natural-number recursion gives
  \[
  \Psi(F,i,k+1)\ \Longleftrightarrow\
  \exists T:\operatorname{Finset}(\alpha),\
  T\subseteq F_i\ \land\
  \forall j:\mathbb N,\
  T\subseteq F_j\ \Longrightarrow\
  F_j\subsetneq F_i\ \Longrightarrow\ \Psi(F,j,k).
  \]
  Here finite sets are coerced to sets in every inclusion. The recursion is on depth, not on i or the cardinality of a language. The standard course-of-values recursion's predecessor component is the depth-k predicate applied to j. Psi.match_1 is the exported generated helper implementing the zero/successor case split with Nat.casesOn and Unit; it contributes no extra condition.
* KAngluinCondition F k is ∀ i : Nat, Psi F i k. Each i can have its own finite witness, and recursive witnesses can depend on the encountered j and remaining depth.
* IsRelativeTellTale F I i T has domain I : Set Nat and T : Finset α. It asserts T⊆F_i and
  \[
   \forall j:\mathbb N,\quad
   j\in I\ \Longrightarrow\ T\subseteq F_j\
   \Longrightarrow F_j\subseteq F_i\
   \Longrightarrow F_i\subseteq F_j.
  \]
  Thus a member of that indexed subfamily lying between T and F_i must equal F_i. The final reverse inclusion is essential. Equal duplicate languages satisfy it; incomparable languages and proper superlanguages of F_i do not trigger it.
* RelativeConditionTwo F I is ∀ i : Nat, i∈I → ∃ T : Finset α, IsRelativeTellTale F I i T. This definition requires i∈I at its call site, although IsRelativeTellTale by itself does not.
* CoversAllIndices layers, for layers : List (Set Nat), is ∀ i : Nat, ∃ I : Set Nat, I∈layers ∧ i∈I.
* HasAngluinStratification F k is ∃ layers : List (Set Nat), layers.length=k ∧ CoversAllIndices layers ∧ ∀ I : Set Nat, I∈layers → RelativeConditionTwo F I.

These expansions account for every project definition supplied in the dependency export, including the generic wrappers, output and success predicates, recursive helper, relative witness predicate, cover and list-of-layers predicate.

## Target 1 dossier

Identifier: GenLimit.ListIdentification.Results.theorem_1.

Supplied source anchor: GenLimitLean/GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean:34. This file was not opened.

Original target type, verbatim:

~~~lean
∀ {α : Type u_1} [DecidableEq.{u_1 + 1} α] {F : GenLimit.Generic.LanguageFamily.{u_1} α},
  (∀ (i : Nat), ∃ stream, GenLimit.Generic.Presents.{u_1} stream (F i)) →
    ∀ (k : Nat),
      Iff (GenLimit.ListIdentification.ListIdentifiable.{u_1} F k)
        (GenLimit.ListIdentification.KAngluinCondition.{u_1} F k)
~~~

For any such α, equality instance and indexed family, if every indexed language has a complete infinite source, then for each natural k one finite-history operator succeeds in the semantic k-tuple sense exactly when every index satisfies the depth-k recursive finite-witness property.

The quantifier skeleton is

\[
\forall\{\alpha\}\ [\operatorname{DecidableEq}\alpha]\ \forall\{F\},\
(\forall i\,\exists s\,P(s,F_i))\ \Longrightarrow\
\forall k,\quad
[\exists A\,\forall z\,\forall s,\ P(s,F_z)\to
 \exists T\,\forall t\ge T\,\exists r:\operatorname{Fin}(k),\
 F_{A(t,h_t)(r)}=F_z]
\ \Longleftrightarrow\ [\forall i\,\Psi(F,i,k)].
\]

The forward direction constrains the whole indexed family from the existence of one operator. It says that for each i, a finite subset T of F_i can be chosen so that every strict sublanguage F_j of F_i containing T satisfies the predecessor-depth condition. The witness is chosen before quantification over those j, so it must handle all of them simultaneously. It is not a separately chosen T for each competing j. The reverse direction supplies existence of one operator working for all indices and sources once the recursive property holds at every index. Neither direction names a particular operator or a numerical stabilization bound.

At depth 1, the predecessor is False: each F_i has a finite T excluding every strict sublanguage represented anywhere in F that contains T. At higher depths such strict competitors are permitted, but they must satisfy the lower-depth property. The recursion quantifies over all natural indices, with no restriction to previously occurring data, small indices, a decidable subfamily, or one stratum. It does not assert that T exhausts F_i or that F_i is finite. Empty T is admissible.

For k=0, Fin 0 has no successful slot, and Psi F i 0 is False for every i. Under H(F), taking index 0 and any of its presenting sources makes the learner obligation impossible; KAngluinCondition is also false at index 0. The equivalence includes this case; it does not assume k>0. A total zero-output operator can exist as a function, but cannot meet the success predicate under H(F).

There is no empty indexed family, since F has a value at every natural number. Empty component languages are excluded by H(F); if any occurs, the implication's hypothesis fails. For empty α no infinite α-valued source exists, so the same antecedent failure applies. Nonempty finite languages are admissible, as are infinite languages possessing the assumed sources. Duplicate-language indices count as separate indices in the universal quantifiers but semantic output equality accepts any duplicate representative. In the recursion equal duplicates are not strict sublanguages and create no descent obligation.

## Target 2 dossier

Identifier: GenLimit.ListIdentification.Results.theorem_2.

Supplied source anchor: GenLimitLean/GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean:46. This file was not opened.

Original target type, verbatim:

~~~lean
∀ {α : Type u_1} [DecidableEq.{u_1 + 1} α] {F : GenLimit.Generic.LanguageFamily.{u_1} α},
  (∀ (i : Nat), ∃ stream, GenLimit.Generic.Presents.{u_1} stream (F i)) →
    ∀ (k : Nat),
      Iff (GenLimit.ListIdentification.ListIdentifiable.{u_1} F k)
        (GenLimit.ListIdentification.HasAngluinStratification.{u_1} F k)
~~~

Under precisely the same presentation hypothesis, for each natural k the common learner property is equivalent to existence of a length-k list of sets of natural-number indices covering all indices, with relative finite witnesses throughout each listed set. This is a cover of the indexed family; the exported definition does not require a partition, disjointness, distinct layers, or nonempty layers.

Its right-hand side expands to the following skeleton, preserving every conjunction:

\[
\exists \mathcal I:\operatorname{List}(\operatorname{Set}\mathbb N),\
|\mathcal I|=k\ \land\
[\forall i:\mathbb N,\ \exists I:\operatorname{Set}\mathbb N,\
 I\in\mathcal I\land i\in I]\ \land\
[\forall I:\operatorname{Set}\mathbb N,\ I\in\mathcal I\to
 \forall i:\mathbb N,\ i\in I\to
 \exists T:\operatorname{Finset}\alpha,\
 T\subseteq F_i\land
 \forall j:\mathbb N,\ j\in I\to T\subseteq F_j\to
 F_j\subseteq F_i\to F_i\subseteq F_j].
\]

The outer binders and left-hand side are exactly those in the Target 1 skeleton, with this expression replacing ∀i Ψ(F,i,k). The forward direction supplies this entire list, its exact length, coverage of every natural index, and the relative witness condition for every list member. The reverse direction takes all these conditions together and supplies one successful finite-history operator. No direction only asserts a bound on the number of layers without supplying the covering and relative properties.

A finite witness may depend on F, I and i; it is not selected uniformly before I or i. Within that witness obligation, one T handles every j in the same I. Languages outside I impose no condition on that T. Layers can contain infinitely many indices. Their order has no role in the stated predicates beyond forming a list whose occurrences count toward length. Repeating a layer counts again toward k; list membership does not distinguish its occurrences. An empty layer satisfies its relative condition vacuously, but contributes nothing to coverage. Layers may overlap, and the cover witness I for i need not be unique. Indices denoting the same language may lie in different layers, or together, without an injectivity requirement.

For k=0, the only length-zero list is empty and cannot cover index 0. Hence the stratification property is false, matching the impossibility of the learner property under H(F). For positive k, empty padding layers and repeated layers remain permitted by the exact-length definition. Empty-language, empty-domain, finite-language, source-repetition and duplicate-index cases have the same treatment as Target 1. Relative witnesses may be empty finite sets; no nonempty-witness hypothesis appears.

## Information, effectiveness and limits

The learner's explicit observations are time and the complete ordered finite history. No target index, future source values, negative examples, language-membership oracle, equality-of-languages oracle, probability law, or randomness is an argument of A. Nevertheless existence of an arbitrary function is a semantic assertion: A may be chosen using the entire fixed F, and no computability restriction prevents noncomputable dependence on it. Thus these types assert neither an executable ordinary program nor a procedure relative to a specified oracle. DecidableEq α decides equality of source elements; it supplies no language-membership decision procedure.

The source witnesses, operator, thresholds, finite witnesses and layer sets are existential objects in propositions. The declarations do not demand recursive source enumerations, effective telltale selection, computable layer membership, a uniform program across F or k, or extraction of a named algorithm. Both equivalences quantify k after H(F). Their written quantifier order supplies existence for each k and contains no effective uniform selection across k. No statistical loss, support condition, probability distribution, success probability, frequency, limsup criterion, rate, sample-complexity constant, or resource bound is present. The sole time conclusion is eventual success at every later time.

This report establishes the meaning of the supplied propositions at the declared interface boundary. It does not establish that their proofs are valid, that the export matches compiled source, that the statements match any paper, or that an effective theorem follows from these semantic statements.

## Exhaustive coverage table

| Interface component | Preserved content |
|---|---|
| Both outer type binders | Arbitrary Type u_1, displayed DecidableEq instance, implicit Nat-indexed F |
| Presentation premise | ∀i ∃s with exact range equality, before ∀k |
| Source semantics | Infinite total source, positive soundness and completeness, repetitions and order allowed |
| Family/domain assumptions | Nat indexing; no injectivity, global countability, infinitude or membership-decidability instance |
| FiniteHistoryOperator, ListIdentifier | One total A, dependent time/prefix input, k positions containing Nat indices |
| listOutput | Ordered prefix at positions below t; empty time-zero history |
| TargetInGuess | ∃r : Fin k and equality of languages, not indices |
| IdentifiesFrom | ∃T ∀t, T≤t → target represented |
| ListIdentifies | ∀z ∀complete s; threshold follows those quantifiers |
| ListIdentifiable | ∃A outside all target/source quantifiers |
| Stabilization strength | All late times; slot/index/tuple need not stabilize |
| Psi base and helper | False at zero; standard zero/successor split |
| Psi successor | ∃finite T, T⊆F_i, all strict represented sublanguages containing T satisfy predecessor depth |
| KAngluinCondition | Every natural index satisfies the same depth-k predicate |
| Relative telltale | T⊆F_i plus j∈I, T⊆F_j, F_j⊆F_i implying reverse inclusion |
| RelativeConditionTwo | Every i∈I has its own finite witness |
| CoversAllIndices | Every Nat index lies in some list member |
| HasAngluinStratification | Exact length, complete index coverage and relative condition conjuncts |
| Layer edge cases | Overlaps, duplicate layers, empty layers and infinite index sets allowed |
| Both equivalences | Necessity and sufficiency with the same premise and same k |
| k=0 | Empty output cannot succeed under H; recursive and covering sides false |
| Empty/finite/repeated cases | Empty components violate H; finite nonempty sources may repeat; semantic duplicates allowed |
| Witness dependencies | A depends on F,k; T-time on z,s; recursive/relative finite witnesses local; slot can vary with time |
| Effectiveness | Arbitrary semantic functions/sets; no named program, oracle interface or effective uniformity |
| Omitted categories | No laws, support, loss, probability, rate, limsup or resource bound in these types |
| Audit boundary | No proofs, source correspondence, fresh build or certification claimed |
