# P00 Stage 2 independent source comparison

## Identity and source-first record

All 17 original P00 slots and all 19 source-locator records are compared. Source: E Mark Gold, *Language Identification in the Limit*, Information and Control 10 (1967), printed 447-474, DOI 10.1016/S0019-9958(67)91165-5; received February 20, 1967 (printed 466 / PDF 20). One pinned edition only. PDF SHA256: `a15cdcfe84d79ceb6b5a01bdd040948a04adb533c9afc8670ff191f474097693`. PDF indexes are one-based; printed page = PDF page + 446.

The complete 28-page marked source text, including definitions, standing conventions, remarks and interpretive proof text, was read before any Stage 1 or Lean evidence. Base-page images of PDF 3, 4, 12, 16, 17, 18, 19, 25, 26, 27 were visually checked for formulas and ambiguous notation. No annotation payload supplied mathematical evidence. The independent source inventory was saved at 2026-11-13T23:47:14.223533+00:00, SHA256 `212364751806cb1259a09baaaab502de3e8f47cdf50b535110188f1b128e00ec`, before Stage 1 access. It remains unchanged.

Original Stage 1 and the source-free supplement are frozen and hash-verified. The supplement was frozen at 2026-11-14T00:08:37.755477+00:00 and read on resumption beginning 2026-11-14T00:17:27Z. All 26 supplemental target types and dependency types/kinds/definition values match the original native census. It supports the existing findings; no classification changed. Exact exports remain in the frozen code-only inputs and supplement rather than being duplicated here. This pass reports statement/definition correspondence, not proof correctness, construction certification or human review.

## Independent source inventory and standing assumptions

`source-inventory.md` is the immutable complete source-first inventory. Each JSON row also preserves its full scoped source assertion and standing assumptions. The following table inventories every original slot; the individual comparisons below retain all material parts.

Source-global conventions: one fixed finite nonempty alphabet; languages are sets of finite strings, recoded by naturals. Time starts at 1. One learner must handle every target and every allowable presentation. A correct fixed name and finite stabilization time are chosen after each target/presentation; no uniform time, error, sample or computation bound follows. Ineffective identification removes only the computation requirement. Source Section 7 assumes observation/object countability and a name for every object; countability of each object's presentations is an additional premise only for its distinguishability-sufficiency clause.

A positive text is a total sequence whose range equals the target, with repetition and no blank/pause symbol. Empty targets consequently have no such text. Informants are truthful labeled observations covering every word; they can present empty/full languages. A methodical informant uses a fixed enumeration; a request informant answers learner-chosen queries. Tester and generator names are machine indices, with uniform effective translations when asserted. Primitive-recursive restrictions require uniform coding/algorithms, not arbitrary extensional functions or pointwise decidability. Superfinite means ALL finite languages plus at least one infinite language. No scoped claim has a probability law, distributional loss, statistical rate or density/frequency qualification.

| Slot | Source locator (printed / PDF) | Complete scoped assertion in brief |
|---|---|---|
| C01 | Theorem 7.1 (458--459 / 12-13) | Ineffective identification implies distinguishability; collapsing uncertainty makes every enumeration learner succeed; under per-object presentation countability, distinguishability suffices. |
| C02 | Language Identifiability, second paragraph (460 / 14) | Every countable named language class is ineffectively identifiable separately from recursive and primitive-recursive texts. |
| C03 | Language Identifiability, first paragraph (460 / 14) | Every countable named class is ineffectively identifiable from arbitrary truthful exhaustive informants. |
| C04 | Theorem 10.1 (learning-time theorem) (462 / 16) | No arbitrary guessing rule weakly improves a fixed enumeration learner on every run and strictly improves it on one run, with learning time measured by first stable correct name. |
| C05 | Theorem I.6 (469 / 23); finite-language learner restatement (459 / 13) | One effective learner guesses the observed finite language and emits a stable tester machine name on every arbitrary text for every finite target. |
| C06 | Language Identifiability, third paragraph (460 / 14) | For arbitrary texts, all finite languages are ineffectively identifiable and every proper superclass of that entire finite class is not. |
| C07 | Corollary I.2 (466--467 / 20-21) | For every presentation method, effective generator nonidentifiability implies effective tester nonidentifiability. |
| C08 | Theorem I.3 (467 / 21) | Arbitrary, fixed methodical and learner-request informants yield the same effectively identifiable classes for every naming relation. |
| C09 | Theorem 10.1 (naming-translation theorem) (464 / 18) | Effective identification in N1 plus a limiting-recursive valid-name translation yields effective identification in N2 using the same presentations. |
| C10 | Corollary 10.1 (464 / 18) | Literal source: no limiting-recursive tester-to-generator translation for a class containing all finite languages and an infinite recursive witness. Direction is suspect. |
| C11 | Theorem 10.2 (465 / 19) | No 2-recursive domain-generator-to-complement-domain-generator translation for such a class. |
| C12 | Theorem I.4 (467--468 / 21-22) | All primitive-recursive languages are effectively tester-identifiable from methodical informants via uniform enumeration/compiler. |
| C13 | Theorem I.5 (468--469 / 22-23) | All recursive languages are not effectively generator-identifiable from methodical informants. |
| C14 | Theorem I.7 (469--470 / 23-24); r.e.-language primitive-recursive-text restatement (459--460 / 13-14) | All r.e. languages are effectively generator-identifiable from primitive-recursive texts by identifying the text function and compiling its index. |
| C15 | Theorem I.9 (471--473 / 25-27) | Any superfinite class is not effectively tester-identifiable from primitive-recursive texts; the source constructs a primitive-recursive diagonal presentation. |
| C16 | Theorem I.8 (470--471 / 24-25) | Any superfinite class is not effectively generator-identifiable from recursive texts; the source uses effective repetitions/search. |
| C17 | Theorem I.1 (466 / 20) | For every presentation method, effective tester identification implies effective generator identification via a uniform index translator. |

## Comparison matrix

faithful-specialization: 2, partial: 5, not-covered: 9, faithful-generalization: 1. “Partial” records material missing obligations; “not-covered” is a bounded census finding after counterpart search, not merely absence of a registered endpoint.

| Slot | Correspondence | Finding |
|---|---|---|
| C01 | faithful-specialization | All three source components have native statements; the countable converse explicitly requires a nonempty object type. |
| C02 | partial | Generic countable-allowable ingredients exist; recursive-text and primitive-recursive-text specializations are missing. |
| C03 | faithful-specialization | Semantic arbitrary-informant learning for Nat-indexed families; bounded growing search differs at early times. |
| C04 | not-covered | No first-stabilization-time or Pareto non-domination theorem. |
| C05 | partial | Observed finite-set learner matches; effective tester-index representation/compiler is missing. |
| C06 | faithful-generalization | Semantic finite/superfinite maximality matches; the negative result extends to arbitrary classes and namings. |
| C07 | not-covered | No effective generator/tester nonidentification transfer. |
| C08 | not-covered | No methodical/request simulations or three-model equivalence. |
| C09 | not-covered | No limiting-recursive translation or effective diagonal learner. |
| C10 | not-covered | No translation obstruction; the literal source direction remains a suspected source error. |
| C11 | not-covered | No domain-generator, 2-recursive complement-index obstruction. |
| C12 | partial | Semantic informant template exists; the effective primitive-recursive/tester instance is absent. |
| C13 | not-covered | No effective recursive-language/methodical generator impossibility. |
| C14 | not-covered | No effective r.e.-target/primitive-recursive-text function learner/compiler. |
| C15 | partial | Semantic arbitrary-text obstruction does not provide a primitive-recursive counterexample text. |
| C16 | partial | Semantic arbitrary-text obstruction does not provide a recursive counterexample text. |
| C17 | not-covered | No effective tester-to-generator machine-name transfer. |

## Native search and interpretation boundary

All 693 native census records were parsed and searched by names, exported types and non-theorem values for computation, recursive/primitive-recursive, Partrec/Primrec, Turing, tester, translation, domain generator, methodical/request and learning-time/faster concepts. No such source-specific interface appeared. Public P00 declarations and plausible Core/support alternatives were inspected by their actual types/definitions. In particular this included abstract identification, positive-language enumeration, arbitrary-informant enumeration, finite learning, arbitrary-name superfinite corollaries, locking constructions and oracle/identification-to-generation interfaces. This is not individual semantic review of every compiler-generated record or a search outside the frozen P00/Core/support census.

A native learner is a total function on finite histories. `Classical.propDecidable`, arbitrary `Set Nat` membership and `Nat.find` do not certify computation. Oracle records provide Boolean query functions with truth laws; they neither certify computability nor encode the source unknown-target request protocol. Native `GeneratableInLimit` concerns output data, not convergence to a generator machine name. Names served only to locate evidence; meanings came from types and defining bodies. Theorem proof values were excluded.

## Individual target dossiers

### C01 — claim:g67:abstract-ineffective-identification-characterization

**faithful-specialization.** All three source components are present across native statements. The registered conjunction assumes per-object countability of allowable streams before ALL three clauses, whereas the source requires this only for distinguishability sufficiency. Native distinguishable_of_identifiable and identificationByEnumeration_identifies remove that extra restriction from necessity and collapsing-uncertainty sufficiency. The countable-stream converse is supplied by distinguishable_implies_identifiable_of_countable. The complete comparison is therefore stronger than the registered conjunction alone suggests. The source countable model is faithfully obtained for nonempty object types with a chosen naming section; the explicit Nonempty Object boundary in the countable converse remains. Nat time/prefix indexing recodes positive time without altering eventual convergence.

**Strength.** Mixed binder changes: registered conjunction specializes source clauses (a),(b) by an unnecessary countable-presentation premise. Native standalone (a),(b) generalize beyond source countability assumptions. Clause (c) retains source counts plus explicit Nonempty Object; no single strict ordering summarizes all changes. Conservative slot label records the remaining nonempty-object/naming-section specialization, not a missing (a) or (b).

**Quantifiers and witnesses.** Fix naming/allowable; one learner precedes all targets and allowable streams. The same named enumeration learner is used for every target/stream for each fixed enumeration. Stable name and time follow target/stream. Rival-elimination time follows each rival. All-future equality, not merely denotation correctness, is retained.

**Scoped algorithm comparison.** Source: First compatible object in each fixed surjective enumeration, output a fixed chosen name. Effectivity is not required in Theorem 7.1. Native: firstCompatibleIndex uses Classical.propDecidable, Nat.find on semantic allowed-continuation compatibility and fallback 0; identificationByEnumeration returns naming.nameOf of the chosen object. Definition input is only finite history plus fixed naming/allowable/enumeration; no actual future or true target is provided. Assessment: Faithful semantic first-compatible definition on valid histories; invalid-history fallback is extra totalization. No ordinary computability or explicit oracle guarantee follows. Standalone identificationByEnumeration_identifies concerns this same named definition, while the distinguishability converse supplies only an unspecified learner. Full construction/proof audit: excluded.

**Discrepancies:** Registered conjunction globally moves the countable-presentation hypothesis; standalone native components repair its first two source-coverage gaps. Nonempty Object is explicit in the countable converse; the source does not state it explicitly. Naming stores a chosen right inverse nameOf; source says every object has a name. Classical choice/reindexing relates them, without an effective claim.

Source-free supplemental reconstruction checked: 6 mapped target(s); no finding change. Exact inspected identifiers are in this slot’s JSON row; central anchors are below.

### C02 — claim:g67:countable-classes-ineffectively-identifiable-from-effective-texts

**partial.** Native generic countable-allowable/distinguishability results provide the abstract implication used by the source, but there is no native recursive-text or primitive-recursive-text predicate, no theorem proving their countability, and no specialization to a named language class with those presentation restrictions. Positive-text language enumeration was checked directly: it converges to leastCover and identifies only when that cover equals the target (or for inclusion antichains); this is not the source method of identifying the text FUNCTION. Both recursive and primitive-recursive source alternatives remain uninstantiated.

**Strength.** Only abstract ingredients are represented. The arbitrary-positive-text family theorem has an additional equality/antichain condition and a different enumeration object; it cannot substitute for the source conclusion for every countable class.

**Quantifiers and witnesses.** Source: for each countable named class and each choice of the two effective presentation families, exists ONE semantic learner, then forall target/presentation exists stable correct name/time. Native generic result has this semantic ordering once a countable allowable family is supplied; those concrete premises are not discharged by an exported native statement.

**Scoped algorithm comparison.** Source: Enumerate and semantically identify the complete allowed text function, then use its unique range-language/name; the recursive-text collection need not have an effective enumeration. Native: Abstract first-compatible learner is available, but no named recursive/primitive-recursive-text learner is defined. Text.enumerationLearner enumerates LANGUAGES, filters indices below history.length for positive compatibility and can stabilize to a proper covering language. Assessment: Generic semantic infrastructure only; the decisive text-function presentation restriction/specialization and naming transfer are missing. No effective learner is claimed by this source slot. Full construction/proof audit: excluded.

**Discrepancies:** No concrete countability theorem or allowed-text predicate for either source alternative. Language-enumeration convergence to leastCover is not identification of the text function.

Source-free supplemental reconstruction checked: 4 mapped target(s); no finding change. Exact inspected identifiers are in this slot’s JSON row; central anchors are below.

### C03 — claim:g67:countable-language-classes-identifiable-from-informants

**faithful-specialization.** The native theorem proves semantic identification of every arbitrary Nat-indexed language family from every correct exhaustive informant. Family indices serve as names. This faithfully realizes the source for nonempty countable families with family-index naming; no arbitrary-name reindex/translation theorem is exported here. The source existence guarantee is preserved, although the named algorithm differs at early prefixes from unbounded first-compatible enumeration: it examines only indices below the history length and otherwise uses fallback 0. Native supplemental types certify that this SAME named learner eventually equals leastEqualName C z, whose denotation equals C z.

**Strength.** Class/effectivity agreement is semantic. Nat-indexed nonempty families and index names specialize arbitrary countable named classes. In return, the native theorem names a successful learner and supplemental types fix its limit to the least equivalent index. This strengthens witness specificity without making it effective.

**Quantifiers and witnesses.** forall C, learner M_C fixed; forall z and correct complete info, exists n,T, C n=C z and forall t>=T output=n. Supplemental leastEqualName statement fixes n to the least family index with denotation C z; it is independent of presentation. No uniform convergence time or target index input is supplied.

**Scoped algorithm comparison.** Source: Identification by enumeration uses all prior labeled observations to reject each incorrect earlier candidate. Native: informantCompatibleIndices C h filters Finset.range h.length using semantic membership agreement; informantEnumerationLearnerWithFallback chooses its minimum/fallback and informantEnumerationLearner sets fallback 0. Classical proposition decision permits noncomputable C. Assessment: A growing finite-search variant preserves the semantic class conclusion; it is not literally the source first-compatible rule at every early time and may output an incompatible fallback. Uniform decidable membership for (index,word) would be an additional realization assumption, not supplied by arbitrary C or by pointwise decidability. No explicit oracle implementation is asserted. Full construction/proof audit: excluded.

**Discrepancies:** Family-index naming/nonempty enumeration specialization; arbitrary named-class transfer is not a separate native statement. Bounded growing candidate search with fallback differs from source unbounded first-compatible output at early times.

Source-free supplemental reconstruction checked: 4 mapped target(s); no finding change. Exact inspected identifiers are in this slot’s JSON row; central anchors are below.

### C04 — claim:g67:enumeration-learning-time-pareto-optimality

**not-covered.** The native enumeration learner and its eventual identification/index stability are present, but no learning-time value (including infinity), first-stable-time predicate, uniformly-faster comparison or Pareto non-domination theorem is present in the frozen census. Eventual identification does not imply the source optimality comparison. The source remark allowing enumeration learners that fail global identification is likewise unrepresented.

**Strength.** No comparison theorem is represented. A convergence theorem is an ingredient and has no ordering relation with the missing Pareto optimality conclusion.

**Quantifiers and witnesses.** Source denies exists G with a universal weak time improvement over ALL target/presentation pairs plus one existential strict improvement. Native stability types quantify only per-run eventual constancy and contain no comparison of two learners or least convergence times.

**Scoped algorithm comparison.** Source: Compare arbitrary G against fixed first-compatible G0, using first stabilization time in Nat-positive union {infinity}. Native: Named semantic first-compatible G0 inspected; no time-minimization interface or named comparison procedure. Assessment: Enumeration definition covered as prerequisite only. Source learning-time theorem and its boundary remark are not represented. Full construction/proof audit: excluded.

**Discrepancies:** Missing learning-time definition/infinity convention and universal/existential Pareto comparison. Least equivalent/compatible index is not least stabilization time.

No supplemental slot mapping. The native candidates checked for this slot are individually listed in its JSON row, with anchors below.

### C05 — claim:g67:finite-languages-arbitrary-text-tester-identifiable

**partial.** The observed-finite-set rule and exact eventual fixed Finset-name identification on ALL finite targets and arbitrary texts are present. The source theorem specifically demands an EFFECTIVE learner emitting TESTER MACHINE INDICES. Native finiteNaming denotes Finset Nat directly by its underlying set, and no tester-code representation or uniform compiler from Finset to tester index is supplied. List.toFinset with Nat equality is concretely computable, so the mathematical data rule matches, but that does not constitute a formal machine-index tester guarantee. Both the Section 7 restatement and I.6 theorem are compared.

**Strength.** The semantic finite-set representation and named data-processing rule are faithful. Dropping the tester-index/effective representation obligation weakens the full source theorem; no extra class/presentation power compensates for it.

**Quantifiers and witnesses.** Named finiteLearner fixed globally; forall finite L and stream with range L, exists F,T with coercion F=L and forall t>=T finiteLearner(prefix)=F. Separate existential theorem does not itself select a witness, while named theorem independently certifies this SAME concrete finiteLearner. Source tester-name convergence needs an additional uniform compiler and stable code choice.

**Scoped algorithm comparison.** Source: Maintain finite set of observed examples, output an effectively obtained tester for that exact set. Native: finiteLearner is List.toFinset Nat with decidable equality; output is Finset, finiteNaming is coercion to Set Nat. State interpretation F0=empty; update insert observed u; output F. Assessment: Exact definition-level observed-set algorithm, ordinary finite computation. Missing machine-code tester compiler and effective-code theorem. No construction proof audit or complexity bound. Full construction/proof audit: excluded.

**Discrepancies:** Finset names replace tester machine indices. No formal uniform tester compiler or computability predicate is present. Empty language is in the class but has no literal total positive text in both source and native model.

Source-free supplemental reconstruction checked: 3 mapped target(s); no finding change. Exact inspected identifiers are in this slot’s JSON row; central anchors are below.

### C06 — claim:g67:finite-languages-maximal-for-arbitrary-text

**faithful-generalization.** The source semantic finite/superfinite boundary is faithfully represented: the finite class is semantically identifiable, and every proper superclass is not. Native IsSuperfinite is exactly containment of ALL finite languages plus an infinite member. The source p.460 explicitly discusses INEFFECTIVE identification; the native arbitrary semantic learner is appropriate here. Native arbitrary-name obstruction superfinite_not_identifiableWith also makes the semantic-to-named direction explicit. The source standing countability assumption is not required by the native negative result, which ranges over arbitrary sets of languages. This slot does not separately supply the effective tester component of I.6 (C05).

**Strength.** Equivalent finite/maximality content on source countable named classes, generalized in the negative direction to uncountable classes and every denotation naming. The semantic positive conjunct has no machine-index effectiveness guarantee, which belongs to C05 rather than the specifically ineffective Section 8 boundary.

**Quantifiers and witnesses.** Positive conjunct exists one M then forall finite L/text exists name,T. Negative conjunct forall class strictly extending finiteLanguages, not exists one M working for every L/text. Target counterexample may depend on M; no fixed failing target for all learners is claimed. Maximal under inclusion, not greatest among all learnable families.

**Scoped algorithm comparison.** Source: Semantic finite-example learner plus arbitrary-text superfinite nonexistence; source references the diagonal finite-approximation method. Native: Concrete finiteLearner available separately; maximality and superfinite theorem statements use existential semantic functions. semanticLearner N M h=N.language(M h) forgets names; associated transfer theorem supports arbitrary-name nonexistence. Assessment: Semantic statement correspondence is faithful; no effective counterexample builder or effective learner inferred from existential proof. Definition/statement scope only. Full construction/proof audit: excluded.

**Discrepancies:** Negative class scope extends beyond the source standing countability convention. Semantic set names are an interpretation of ineffective naming independence; arbitrary-name obstruction is also native. No claim that every learnable class contains only finite languages, or that all incomparable families are excluded.

Source-free supplemental reconstruction checked: 9 mapped target(s); no finding change. Exact inspected identifiers are in this slot’s JSON row; central anchors are below.

### C07 — claim:g67:generator-nonidentification-implies-tester-nonidentification

**not-covered.** No tester/generator machine naming relations, effective tester-to-generator translation, or generator-nonidentification-to-tester-nonidentification corollary occurs in the census. Native semanticLearner composes a denotation map to output a SET, not a generator machine index. The Core identification-to-generation theorem was inspected: it assumes every family member infinite and concludes eventual generation of fresh data, a different notion from identifying a generator program. Neither is a native counterpart to I.2.

**Strength.** The source corollary is absent. Set-valued denotation forgetting and data generation do not express the source naming comparison, regardless of any superficial naming overlap.

**Quantifiers and witnesses.** Source: ANY presentation method, not EffectiveGeneratorIdentifiable(C) implies not EffectiveTesterIdentifiable(C). Native generic bridge concerns a supplied identifier on positive presentations of infinite family members, then GeneratableInLimit; it is not this implication.

**Scoped algorithm comparison.** Source: Contraposition of uniform recursive machine-index conversion. Native: Only set denotation postcomposition and identification-to-data-generation interfaces were found as plausible alternatives. Assessment: No scoped effective naming-conversion result. Full construction/proof audit: excluded.

**Discrepancies:** Missing both machine-based naming relations and a uniform recursive translator. Core GeneratableInLimit is an output-data guarantee, not program-name convergence.

No supplemental slot mapping. The native candidates checked for this slot are individually listed in its JSON row, with anchors below.

### C08 — claim:g67:informant-presentation-methods-equivalent

**not-covered.** Only arbitrary correct exhaustive informant streams and their semantic enumeration learner are represented. No methodical-informant predicate, interactive request strategy/run, wait simulation, or presentation-method equivalence for every naming relation is present. MembershipOracle/query records were inspected: they supply semantic candidate-family membership answers, not a single unknown-target interactive request protocol or a computability guarantee. Semantic identification from arbitrary informants is a prerequisite fact, not all three effective simulations.

**Strength.** The source equivalence is not represented. An arbitrary-informant semantic positive theorem for indexed classes is narrower in result kind and lacks the effective interactive transfer conclusions.

**Quantifiers and witnesses.** Source quantifies every naming relation and compares existence of effective learners in all three models. Native theorem fixes family-index names and a semantic learner on complete labeled streams; there is no quantifier over query policies or simulation time.

**Scoped algorithm comparison.** Source: Restrict arbitrary to fixed methodical order; ask that order by request; simulate a request learner on arbitrary data by waiting for each desired answer and repeating guesses during waits. Native: arbitrary-informant definition/learner only. Oracle constructors are mathematical Boolean query functions with truth laws, not computable request learners. Assessment: No methodical/request algorithm definition or equivalence theorem. Full construction/proof audit: excluded.

**Discrepancies:** Missing fixed methodical order, learner-selected query histories and causal request simulation. Missing effective nature of each simulation and naming-uniform equivalence.

No supplemental slot mapping. The native candidates checked for this slot are individually listed in its JSON row, with anchors below.

### C09 — claim:g67:limit-recursive-naming-translation-preserves-identifiability

**not-covered.** No partial machine-index translation, limiting-recursive approximation interface or diagonal translated learner is represented. Abstract.Naming has semantic denotes/nameOf, and Text.semanticLearner only postcomposes denotation to set-valued output. Neither supplies a total recursive two-variable approximator or effective N2 learner. Native arbitrary-function existence cannot be read as the source effective preservation theorem.

**Strength.** Not represented; semantic denotation forgetting is only an ingredient of a different statement and does not preserve the effective computational property demanded here.

**Quantifiers and witnesses.** Source fixes one total recursive g(n,t) approximating a partial valid-name translator, then effective G1; output at time t is g(G1(prefix_t),t). Native model has no g, translation validity domain or joint uniform computation.

**Scoped algorithm comparison.** Source: Diagonal use of the same time t in g(current G1 name,t). Both source learner and approximation are effective. Native: No named translator/diagonal-composition definition; inspected semantic postcomposition differs in output representation and does not use a limiting approximation. Assessment: No scoped algorithm or theorem. Full construction/proof audit: excluded.

**Discrepancies:** Missing partial valid-name domain and total recursive approximating function. Missing effective diagonal learner and corresponding fixed-name convergence transfer.

No supplemental slot mapping. The native candidates checked for this slot are individually listed in its JSON row, with anchors below.

### C10 — claim:g67:no-limit-recursive-tester-to-generator-translation

**not-covered.** No native limiting-recursive tester/generator translation theorem in either direction is present. The exact pinned source literally forbids tester-to-generator translation, which conflicts with its own effective tester-to-generator statements (p.451 and I.1); the literal direction was visually verified. This is recorded as a suspected source error/question, not silently reversed and not charged to Lean. The lack of a native counterpart is independent of how that source issue will later be adjudicated.

**Strength.** No native mathematical assertion is aligned to either literal or likely intended direction, so no Lean/source strength comparison is available.

**Quantifiers and witnesses.** Source literal: forall C containing all finite targets and at least one infinite recursive target, not exists a limiting-recursive map defined correctly on every tester name of C and returning a generator name of the same target. No native counterpart quantifiers exist.

**Scoped algorithm comparison.** Source: Uniform partial name translation with a total recursive approximation; literal direction tester to generator. Native: No tester/generator index relations or limiting translation definitions. Assessment: Not represented; suspected source correction reserved for Stage 3. Full construction/proof audit: excluded.

**Discrepancies:** Source direction appears inconsistent with the same pinned paper; no correction adopted. No native endpoint supports a no-translation claim in either direction.

No supplemental slot mapping. The native candidates checked for this slot are individually listed in its JSON row, with anchors below.

### C11 — claim:g67:no-two-recursive-domain-complement-translation

**not-covered.** No native domain-generator/anti-domain-generator naming relations, representing predicate, 2-recursive or limiting-recursive graph/translation model, or no-complementation theorem is present. Semantic set complementation would not provide the uniform machine-index statement. The source theorem and its hierarchy equivalence/cited recursive-composition context remain outside the formalized interfaces.

**Strength.** Not represented; abstract set/naming models do not settle the computational hierarchy obstruction.

**Quantifiers and witnesses.** Source forall superfinite-with-infinite-recursive-witness C, denies a uniform 2-recursive partial translator defined correctly on ALL valid domain-generator indices for members of C; outputs name the complement as a domain. Native types have no corresponding domain/index/hierarchy quantifiers.

**Scoped algorithm comparison.** Source: Uniform index complementation under 2-recursive graph condition; no effective such translator. Native: No domain-generator or hierarchy-specific definition/interface. Assessment: No scoped algorithm or theorem. Full construction/proof audit: excluded.

**Discrepancies:** Missing machine halting-domain naming, complement-index validity and 2-recursive graph condition. Source proof context invokes the suspect Corollary 10.1; no proof adjudication performed.

No supplemental slot mapping. The native candidates checked for this slot are individually listed in its JSON row, with anchors below.

### C12 — claim:g67:primitive-recursive-languages-methodical-informant-tester-identifiable

**partial.** For any arbitrary family C the native informant theorem supplies a semantic family-index learner; this includes the extensional shape of any chosen enumeration of primitive-recursive languages and works even for arbitrary informants. However the primitive-recursive language class is not defined, no uniform recursive enumerator/characteristic evaluator or tester compiler is provided, and methodical informants and effective learners are not formalized. The source positive theorem is therefore only partially represented by a semantic enumeration template, not proved as an effective tester theorem.

**Strength.** Opposing changes: native semantic template allows arbitrary families and arbitrary informants, broader semantic class/data scope, but drops the source effective learner/tester-index guarantee and does not instantiate its entire primitive-recursive class. These do not yield a full ordering or full source coverage.

**Quantifiers and witnesses.** Native forall C fixes learner before every target/info and eventually fixes one family index. Source requires a single effective learner for ALL primitive-recursive targets with methodical membership data and stable tester indices. An extensional family and pointwise computable members do not supply the joint uniform evaluator/compiler.

**Scoped algorithm comparison.** Source: Uniformly enumerate primitive-recursive characteristic functions; effectively test each on the methodical prefix; effectively compile the first matching candidate to a tester. Native: Bounded family-index semantic candidate filter with Classical membership decisions. No primitive-recursive enumerator/compiler definition or methodical restriction. Assessment: Semantic identification template and finite-search structure only; no ordinary effective realization asserted from arbitrary family C. Full construction/proof audit: excluded.

**Discrepancies:** Missing formal primitive-recursive class and uniform effective enumeration. Family index names replace tester program indices; no compiler. Arbitrary complete labeled stream model is available, but no effective methodical-informant theorem.

No supplemental slot mapping. The native candidates checked for this slot are individually listed in its JSON row, with anchors below.

### C13 — claim:g67:recursive-languages-methodical-informant-generator-impossibility

**not-covered.** No recursive-language class, methodical-informant definition, effective learner predicate or generator-name impossibility theorem is present. The native positive semantic arbitrary-family informant theorem does not contradict the source effective negative result: dropping computability makes a countable recursive class semantically learnable. It cannot substitute for the diagonal construction of a recursive membership sequence against each effective learner.

**Strength.** No counterpart. Native semantic positive result and source effective negative result occupy different computation models, so there is no contradiction and no direct stronger/weaker verdict.

**Quantifiers and witnesses.** Source denies exists effective generator-index learner, forall recursive targets under fixed methodical data, and allows the failing recursive target to depend on learner. Native existence permits noncomputable dependence on arbitrary family membership.

**Scoped algorithm comparison.** Source: Effectively extend a Boolean membership sequence by long zero and one blocks, searching for two positions with differing guesses; target remains recursive. Native: Only semantic complete-informant enumeration; no named recursive diagonal membership sequence or search interface. Assessment: No scoped recursive/effective counterexample construction or impossibility theorem. Full construction/proof audit: excluded.

**Discrepancies:** Missing recursive targets, effective rule restriction and generator-index naming. No recursive methodical diagonal sequence/witness guarantee.

No supplemental slot mapping. The native candidates checked for this slot are individually listed in its JSON row, with anchors below.

### C14 — claim:g67:recursively-enumerable-languages-primitive-recursive-text-generator-identifiable

**not-covered.** No primitive-recursive text-function class, effective enumeration of such functions, r.e.-language class, generator machine naming or effective text-index compiler is present. Native abstract enumeration can semantically identify suitable sequence objects if the required countability/collapse assumptions are supplied, but no source-specific instance or effective construction is exported. Native positive language enumeration may converge to a proper covering language and is not the source function-identification algorithm. Both I.7 and the Section 7 restatement are unrepresented as their stated effective result.

**Strength.** Not represented beyond generic semantic prerequisites. Source effectiveness, entire r.e. class and exact presentation restriction are all material and absent.

**Quantifiers and witnesses.** Source one effective learner, forall r.e. L and forall primitive-recursive text s for L, exists one stable correct generator index and finite time. Native generic assumptions do not assert the needed effective function-class enumeration or compiler.

**Scoped algorithm comparison.** Source: Find a stable primitive-recursive TEXT FUNCTION index from its observed values, then uniformly compile that index to a generator. Native: Generic semantic first-compatible construction; positive-language enumeration checked and distinguished. No effective function enumerator/compiler. Assessment: No scoped algorithm-definition/effectivity correspondence beyond a generic semantic pattern. Full construction/proof audit: excluded.

**Discrepancies:** Missing r.e. target class and primitive-recursive function/presentation definitions. Missing uniform effective function enumeration and generator compiler. Text-function and language enumeration must not be conflated.

No supplemental slot mapping. The native candidates checked for this slot are individually listed in its JSON row, with anchors below.

### C15 — claim:g67:superfinite-primitive-recursive-text-tester-impossibility

**partial.** The native superfinite semantic arbitrary-text obstruction and named-naming corollaries are relevant, but they do not establish tester impossibility under PRIMITIVE RECURSIVE texts. Failure on some arbitrary text need not occur on any primitive-recursive text. The source specific bounded-computation diagonal definition P_t,Q_t,X_t,i_t, primitive-recursive guessing approximation and primitive-recursive text guarantee are absent. Native locking counterexample definitions were inspected: changeExtension uses Classical.choose for a semantic set-output change, badState appends a base datum plus that chosen extension, and badText extracts the resulting history-chain stream; no computability restriction or primitive-recursive certificate appears.

**Strength.** Opposing changes prevent a stronger/weaker shortcut: native excludes even arbitrary semantic learners but permits arbitrary counterexample text; source excludes effective tester-index learners using only primitive-recursive counterexample texts. The latter presentation restriction is a material missing guarantee.

**Quantifiers and witnesses.** Source forall superfinite C, not exists effective tester learner successful on every PR text. Native forall superfinite C, not exists arbitrary semantic/named learner successful on every arbitrary text. A native failing stream can depend noncomputably on the learner/class; its recursive level is not established.

**Scoped algorithm comparison.** Source: Bounded rejection-search Q_t and repeated-output course-of-values recursion, with primitive-recursive f and guessing approximation, yield a primitive-recursive finite-or-infinite counterexample presentation. Native: Semantic locking/tell-tale obstruction; inspected changeExtension chooses an extension classically, badState appends base n and the chosen extension, badText is the induced chain stream. Assessment: A partial semantic obstruction with different presentation/computation scope. It is not the source named primitive-recursive diagonal algorithm, and no effective witness is inferred. Full construction/proof audit: excluded.

**Discrepancies:** Arbitrary counterexample text replaces primitive-recursive text. Arbitrary semantic learner obstruction differs from effective tester-index obstruction. Missing bounded computation predicate, PR normalization/recursion and primitive-recursive counterexample guarantee.

Source-free supplemental reconstruction checked: 2 mapped target(s); no finding change. Exact inspected identifiers are in this slot’s JSON row; central anchors are below.

### C16 — claim:g67:superfinite-recursive-text-generator-impossibility

**partial.** The same native superfinite arbitrary-text obstruction is supporting semantic coverage only. It neither restricts counterexample texts to recursive functions nor represents generator machine indices/effective learner constraints. The source recursive injective base enumeration and effective repetitions/search that force infinitely many name changes are absent as effective interfaces. The inspected native classical choice of changing extensions does not establish a recursive stream, even when a base stream happens to be recursive.

**Strength.** Opposing changes again: native stronger learner quantification, weaker restriction on allowed counterexample texts. Arbitrary-text nonidentifiability does not imply recursive-text nonidentifiability; no full source coverage or ordinary strength ordering follows.

**Quantifiers and witnesses.** Source for each proposed effective learner successful on finite recursive texts obtains a recursive presentation of an infinite r.e. witness causing failure. Native class-level semantic negation only supplies no common learner for all arbitrary presentations and no effective witness constructor.

**Scoped algorithm comparison.** Source: Choose recursive injective a_n enumerating the infinite witness, then effectively search repetition lengths forcing different guesses on successive finite subtargets. Native: Classical semantic extension choice and history-chain text, without recursive base/choice requirements or generator index names. Assessment: Partial conceptual finite-approximation obstruction; the scoped effective recursive-text construction is not represented. Full construction/proof audit: excluded.

**Discrepancies:** Missing recursive-text guarantee and uniform recursive base/extension search. No effective generator naming/learner model. Source non-r.e./nonpresentable witness reduction is a source-convention question, not silently repaired.

Source-free supplemental reconstruction checked: 2 mapped target(s); no finding change. Exact inspected identifiers are in this slot’s JSON row; central anchors are below.

### C17 — claim:g67:tester-identification-implies-generator-identification

**not-covered.** No uniform recursive tester-index-to-generator-index conversion or effective identification transfer for arbitrary presentation methods is represented. semanticLearner converts a stabilized name to its denoted set; the Core identification-to-generation theorem instead yields eventual fresh DATA generation for infinite languages. These inspected native results are different from stabilizing to a generator MACHINE NAME and do not cover I.1.

**Strength.** No effective name-translation theorem represented. Semantic denotation forgetting and fresh-data generation are incomparable in kind with the missing tester-to-generator program-name transfer.

**Quantifiers and witnesses.** Source arbitrary presentation method and class: exists effective tester-index learner implies exists effective generator-index learner via one uniform index translator. Native generic generation bridge has infinite-family assumptions, positive texts and a data-output conclusion.

**Scoped algorithm comparison.** Source: Compose the source learner with a single recursive translator on correct tester indices; stable input name yields stable correct generator index. Native: No tester/generator code relation or named index compiler; only set denotation and fresh-element generation bridges inspected. Assessment: No scoped naming-conversion theorem or algorithm. Full construction/proof audit: excluded.

**Discrepancies:** Missing machine-index naming and uniform recursive conversion. Generic GeneratableInLimit is not generator-name identification; its infinite-target assumptions also exclude source finite-target scope.

No supplemental slot mapping. The native candidates checked for this slot are individually listed in its JSON row, with anchors below.

## Registered target and supporting-native anchors

The original six targets remain exactly as frozen: C01’s conjunction; C03’s named family learner; C05’s existential Finset learner and separately its named `finiteLearner`; C06’s positive/negative maximality conjunction and separately its superfinite obstruction. Their complete quantifier expansions and definitions are in the frozen Stage 1 report. The26 source-free supplemental dossiers distinguish semantic predicates from proved statements and preserve exact additional types. The JSON rows identify which anchors were checked for each slot. No proof body was used to select a hidden existential witness.

The table below is the central locator map for all selectively checked declarations. `kind` is an exporter tag, not a source-fidelity verdict.

| Exact identifier | Frozen module:line | Kind |
|---|---|---|
| `GenLimit.Language` | `GenLimit.Core.Basic:20` | definition |
| `GenLimit.LanguageFamily` | `GenLimit.Core.Basic:23` | definition |
| `GenLimit.Learner` | `GenLimit.Core.Identification:18` | definition |
| `GenLimit.Presents` | `GenLimit.Core.Basic:26` | definition |
| `GenLimit.textPrefix` | `GenLimit.Core.Text:16` | definition |
| `GenLimit.StabilizesTo` | `GenLimit.Core.Identification:47` | definition |
| `GenLimit.IdentifiesInLimit` | `GenLimit.Core.Identification:53` | definition |
| `GenLimit.Gold.Abstract.Naming.mk` | `GenLimit.Paper00_LanguageIdentification.Abstract.Model:33` | constructor |
| `GenLimit.Gold.Abstract.Compatible` | `GenLimit.Paper00_LanguageIdentification.Abstract.Model:40` | definition |
| `GenLimit.Gold.Abstract.Distinguishable` | `GenLimit.Paper00_LanguageIdentification.Abstract.Model:57` | definition |
| `GenLimit.Gold.Abstract.CollapsingUncertainty` | `GenLimit.Paper00_LanguageIdentification.Abstract.Model:69` | definition |
| `GenLimit.Gold.Abstract.Identifiable` | `GenLimit.Paper00_LanguageIdentification.Abstract.Model:94` | definition |
| `GenLimit.Gold.Abstract.Identifies` | `GenLimit.Paper00_LanguageIdentification.Abstract.Model:86` | definition |
| `GenLimit.Gold.Abstract.firstCompatibleIndex` | `GenLimit.Paper00_LanguageIdentification.Abstract.Model:133` | definition |
| `GenLimit.Gold.Abstract.identificationByEnumeration` | `GenLimit.Paper00_LanguageIdentification.Abstract.Model:145` | definition |
| `GenLimit.Gold.Abstract.gold_theorem_7_1` | `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:275` | theorem |
| `GenLimit.Gold.Abstract.distinguishable_of_identifiable` | `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:93` | theorem |
| `GenLimit.Gold.Abstract.distinguishable_of_identifies` | `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:74` | theorem |
| `GenLimit.Gold.Abstract.identificationByEnumeration_identifies` | `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:104` | theorem |
| `GenLimit.Gold.Abstract.collapsingUncertainty_implies_identifiable` | `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:129` | theorem |
| `GenLimit.Gold.Abstract.distinguishable_implies_identifiable_of_countable` | `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:197` | theorem |
| `GenLimit.Gold.Abstract.firstCompatibleIndex_stabilizes` | `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:29` | theorem |
| `GenLimit.Gold.Abstract.allowableSequences` | `GenLimit.Paper00_LanguageIdentification.Abstract.Model:155` | definition |
| `GenLimit.Gold.Abstract.allowableSequences_countable` | `GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration:142` | theorem |
| `GenLimit.Gold.Abstract.classTextAllowable` | `GenLimit.Paper00_LanguageIdentification.Abstract.TextSpecialization:37` | definition |
| `GenLimit.Gold.Abstract.exactTextAllowable` | `GenLimit.Paper00_LanguageIdentification.Abstract.TextSpecialization:27` | definition |
| `GenLimit.Gold.Text.PositiveCompatible` | `GenLimit.Paper00_LanguageIdentification.Text.Consistency:19` | definition |
| `GenLimit.Gold.Text.compatibleIndices` | `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:57` | definition |
| `GenLimit.Gold.Text.enumerationLearnerWithFallback` | `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:72` | definition |
| `GenLimit.Gold.Text.enumerationLearner` | `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:81` | definition |
| `GenLimit.Gold.Text.leastCover` | `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:28` | definition |
| `GenLimit.Gold.Text.IsInclusionAntichain` | `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:178` | definition |
| `GenLimit.Gold.Text.enumerationLearner_identifiesOnText` | `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:166` | theorem |
| `GenLimit.Gold.Text.enumerationLearner_identifiesFamily_of_isInclusionAntichain` | `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:188` | theorem |
| `GenLimit.Gold.Text.enumerationLearner_stabilizesTo_leastCover` | `GenLimit.Paper00_LanguageIdentification.Text.Enumeration:155` | theorem |
| `GenLimit.Gold.Informant.InformantDatum` | `GenLimit.Paper00_LanguageIdentification.Informant.Model:25` | definition |
| `GenLimit.Gold.Informant.InformantCorrect` | `GenLimit.Paper00_LanguageIdentification.Informant.Model:31` | definition |
| `GenLimit.Gold.Informant.InformantComplete` | `GenLimit.Paper00_LanguageIdentification.Informant.Model:35` | definition |
| `GenLimit.Gold.Informant.IsInformantFor.mk` | `GenLimit.Paper00_LanguageIdentification.Informant.Model:39` | constructor |
| `GenLimit.Gold.Informant.InformantCompatible` | `GenLimit.Paper00_LanguageIdentification.Informant.Model:45` | definition |
| `GenLimit.Gold.Informant.IdentifiesOnInformant` | `GenLimit.Paper00_LanguageIdentification.Informant.Model:136` | definition |
| `GenLimit.Gold.Informant.IdentifiesFamilyFromInformant` | `GenLimit.Paper00_LanguageIdentification.Informant.Model:144` | definition |
| `GenLimit.Gold.Informant.informantCompatibleIndices` | `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:46` | definition |
| `GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback` | `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:61` | definition |
| `GenLimit.Gold.Informant.informantEnumerationLearner` | `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:69` | definition |
| `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily` | `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:170` | theorem |
| `GenLimit.Gold.Text.familyNaming` | `GenLimit.Paper00_LanguageIdentification.Text.Model:55` | definition |
| `GenLimit.Support.leastCandidateWithFallback` | `GenLimit.Support.LeastCandidate:20` | definition |
| `GenLimit.Gold.Informant.leastEqualName` | `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:27` | definition |
| `GenLimit.Gold.Informant.leastEqualName_spec` | `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:31` | theorem |
| `GenLimit.Gold.Informant.informantEnumerationLearner_stabilizesTo_leastEqualName` | `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:146` | theorem |
| `GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback_stabilizesTo_leastEqualName` | `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:98` | theorem |
| `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesOnInformant` | `GenLimit.Paper00_LanguageIdentification.Informant.Enumeration:159` | theorem |
| `GenLimit.Support.leastEquivalentIndex` | `GenLimit.Support.LeastCandidate:79` | definition |
| `GenLimit.Gold.Text.Naming.mk` | `GenLimit.Paper00_LanguageIdentification.Text.Model:25` | constructor |
| `GenLimit.Gold.Text.IdentifiesOnText` | `GenLimit.Paper00_LanguageIdentification.Text.Model:33` | definition |
| `GenLimit.Gold.Text.IdentifiesLanguage` | `GenLimit.Paper00_LanguageIdentification.Text.Model:39` | definition |
| `GenLimit.Gold.Text.IdentifiesClass` | `GenLimit.Paper00_LanguageIdentification.Text.Model:44` | definition |
| `GenLimit.Gold.Text.IdentifiableWith` | `GenLimit.Paper00_LanguageIdentification.Text.Model:50` | definition |
| `GenLimit.Gold.Text.SemanticallyIdentifiable` | `GenLimit.Paper00_LanguageIdentification.Text.Model:75` | definition |
| `GenLimit.Gold.Text.SemanticallyIdentifiesClass` | `GenLimit.Paper00_LanguageIdentification.Text.Model:70` | definition |
| `GenLimit.Gold.Text.semanticNaming` | `GenLimit.Paper00_LanguageIdentification.Text.Model:65` | definition |
| `GenLimit.Gold.Text.finiteNaming` | `GenLimit.Paper00_LanguageIdentification.Text.Finite:87` | definition |
| `GenLimit.Gold.Text.finiteLanguages` | `GenLimit.Paper00_LanguageIdentification.Text.Finite:39` | definition |
| `GenLimit.Gold.Text.finiteLearner` | `GenLimit.Paper00_LanguageIdentification.Text.Finite:91` | definition |
| `GenLimit.Gold.Text.finiteLanguages_identifiableWith` | `GenLimit.Paper00_LanguageIdentification.Text.Finite:127` | theorem |
| `GenLimit.Gold.Text.finiteLearner_identifiesFiniteLanguages` | `GenLimit.Paper00_LanguageIdentification.Text.Finite:120` | theorem |
| `GenLimit.Gold.Text.finiteLearner_identifiesOnText` | `GenLimit.Paper00_LanguageIdentification.Text.Finite:96` | theorem |
| `GenLimit.Gold.Text.eventually_sample_eq_of_finite` | `GenLimit.Paper00_LanguageIdentification.Text.Finite:71` | theorem |
| `GenLimit.Gold.Text.finiteLanguages_semanticallyIdentifiable` | `GenLimit.Paper00_LanguageIdentification.Text.Finite:133` | theorem |
| `GenLimit.Gold.Text.ContainsAllFiniteLanguages` | `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:171` | definition |
| `GenLimit.Gold.Text.IsSuperfinite` | `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:176` | definition |
| `GenLimit.Gold.Text.finiteLanguages_maximal_semanticallyIdentifiable` | `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:229` | theorem |
| `GenLimit.Gold.Text.superfinite_not_semanticallyIdentifiable` | `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:183` | theorem |
| `GenLimit.Gold.Text.superfinite_not_identifiableWith` | `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:207` | theorem |
| `GenLimit.Gold.Text.superfinite_not_text_identifiable` | `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:216` | theorem |
| `GenLimit.Gold.Text.all_finite_and_infinite_not_semanticallyIdentifiable` | `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:196` | theorem |
| `GenLimit.Gold.Text.semanticLearner` | `GenLimit.Paper00_LanguageIdentification.Text.Model:79` | definition |
| `GenLimit.Gold.Text.identifiesClass_semanticLearner` | `GenLimit.Paper00_LanguageIdentification.Text.Model:84` | theorem |
| `GenLimit.Gold.Text.identifiableWith_implies_semanticallyIdentifiable` | `GenLimit.Paper00_LanguageIdentification.Text.Model:95` | theorem |
| `GenLimit.Gold.Text.exists_locking_of_identifiesLanguage` | `GenLimit.Paper00_LanguageIdentification.Text.Locking:335` | theorem |
| `GenLimit.Gold.Text.exists_stabilizing_of_identifiesLanguage` | `GenLimit.Paper00_LanguageIdentification.Text.Locking:299` | theorem |
| `GenLimit.Gold.Text.finite_tellTale_of_semantic_identification` | `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:123` | theorem |
| `GenLimit.Gold.Text.finite_tellTale_of_semanticallyIdentifiable` | `GenLimit.Paper00_LanguageIdentification.Text.Superfinite:161` | theorem |
| `GenLimit.Generic.stabilizingIndexIdentifier_implies_generatableInLimit` | `GenLimit.Core.IdentificationGeneration:40` | theorem |
| `GenLimit.MembershipOracle.mk` | `GenLimit.Core.Basic:38` | constructor |
| `GenLimit.OracleFamily.mk` | `GenLimit.Core.OracleFamily:17` | constructor |
| `GenLimit.Gold.Text.IsStabilizing` | `GenLimit.Paper00_LanguageIdentification.Text.Locking:62` | definition |
| `GenLimit.Gold.Text.IsLocking` | `GenLimit.Paper00_LanguageIdentification.Text.Locking:69` | definition |
| `_private.GenLimit.Paper00_LanguageIdentification.Text.Locking.0.GenLimit.Gold.Text.changeExtension` | `GenLimit.Paper00_LanguageIdentification.Text.Locking:90` | definition |
| `_private.GenLimit.Paper00_LanguageIdentification.Text.Locking.0.GenLimit.Gold.Text.badState` | `GenLimit.Paper00_LanguageIdentification.Text.Locking:110` | definition |
| `_private.GenLimit.Paper00_LanguageIdentification.Text.Locking.0.GenLimit.Gold.Text.badHistory` | `GenLimit.Paper00_LanguageIdentification.Text.Locking:129` | definition |
| `_private.GenLimit.Paper00_LanguageIdentification.Text.Locking.0.GenLimit.Gold.Text.badHistoryChain` | `GenLimit.Paper00_LanguageIdentification.Text.Locking:207` | definition |
| `_private.GenLimit.Paper00_LanguageIdentification.Text.Locking.0.GenLimit.Gold.Text.badText` | `GenLimit.Paper00_LanguageIdentification.Text.Locking:225` | definition |

## Bidirectional coverage and Stage 1 reconciliation

C01(a), C01(b), C01(c) each have a native statement: standalone clauses avoid the registered conjunction’s extra common presentation-countability premise. The countable converse retains explicit nonemptiness. C03’s least-name stability and denotation equality concern the SAME named learner, not unrelated existential witnesses. C05 retains both the named observed-Finset rule and its separate existence statement. C06 retains both finite-class existence and nonexistence for every proper superclass, plus arbitrary-name corollaries. This is maximality under inclusion, not a greatest learnable class.

Native leastCover/antichain, locking/tell-tale, oracle and fresh-data-generation statements were checked as possible counterparts. They are ingredients or different results, not evidence of the missing effective machine-index statements. An arbitrary counterexample text does not yield a recursive or primitive-recursive counterexample. No effective program follows from an arbitrary semantic function or from a classically chosen extension. These distinctions explain C02/C12/C15/C16 partial coverage and the remaining absent source-specific results.

No incorrect reading of the six registered types was found in original Stage 1. Its thirteen empty-slot rows were historical registration facts, not global absence judgments. The frozen source-free supplement independently reconstructs all 26 requested native endpoints across seven opaque slot labels and agrees with the direct checks. It is a continuation of the original paper-withheld reviewer, not a fresh-from-zero repetition, and did not use source/comparison material. The supplement changes the recorded evidence basis, not the seventeen correspondence classifications.

## Suspected source issues and open questions

The base PDF printed 464 / PDF 18 literally states in Corollary 10.1 that no limiting-recursive translation goes from testers to generators. That conflicts with the same paper’s effective tester-to-generator statements at 451 / PDF 5 and I.1 at 466 / PDF 20; the surrounding argument suggests reversal. No correction is adopted, and no Lean error is inferred. Stage 3 must adjudicate it. The adjacent Theorem 10.2 proof context is also reserved for source scrutiny, not certified here.

The paper repeats Theorem 10.1 in Sections 10 and 11 and cites Theorem 9.1 in the learning-time remark; page locators distinguish them. Empty-text and total/partial generator conventions, nonpresentable-target reductions, and the external Gold 1965 primitive-recursive normalization remain explicit source questions. No pause symbol, code model or effective witness has been silently added.

## Completion and limitations

All 17 original identities and 19 source-locator records are individually represented; both grouped restatement pairs were compared. The source inventory was frozen before code access and preserved. Original and supplemental Stage 1 hashes match; all 26 supplemental target types and definition dependency values match the frozen census. There is exactly one JSON object per original slot with the required fields. Actual inputs, order, timestamps, hashes, model observability, rendering limitations and the source-free supplement are recorded in `stage2-run.json`.

Only the three Stage 2 comparison artifacts were updated on resumption. No source inventory/Stage 1/library/Git changes occurred. No owner material, developer explanations, PaperMap, registry assessments, prior audits, current human ledger, other paper packages or Stage 3 context were read. The original dispatch identified these 17 as not previously source-audited; no prior audit was rerun. Exact backend model/revision/reasoning and machine-attested context isolation are unavailable.

Targeted Lean verification: not run (interface-only audit, no Lean change). Final full Lake build: not run (no substantial Lean change). Build warnings and failures: not assessed. No proof, full algorithm-construction or human-review certification. Stage 2 is complete for coordinator validation/freezing; no adjudication has started.
