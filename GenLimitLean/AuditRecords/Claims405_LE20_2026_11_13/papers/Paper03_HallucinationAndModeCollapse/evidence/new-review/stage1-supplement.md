# P03 Stage 1 supplement — paper-withheld native reconstruction

This supplement reconstructs exactly seven supplied native targets. C14 and C16 are opaque grouping labels only. The original three-slot, zero-target Stage 1 report remains immutable; these newly supplied endpoints are recorded separately. There is no source comparison or interpretation of what a source claim should mean.

## Inputs and scope

All reconstruction evidence comes from `P03/stage1-supplement-input/`. The seven identifiers in `targets.txt` agree exactly with `targets-by-slot.json`: two C14 targets and five C16 targets. The supplied recursive interface contains 86 unique native declarations: 59 definitions, 15 theorem signatures, 6 structure/inductive declarations and 6 constructors. Every definition value and necessary interface was read; theorem proof bodies are absent. All six input-manifest entries match their actual SHA-256 hashes. Full hashes and file roles are in `stage1-supplement-run.json`.

The exported native dependency references are closed within these 86 records. This is a syntactic package check, not a certification of the exporter or of suppressed proof terms. Standard Lean/Mathlib semantics remain the external trust boundary. Source modules and line numbers below are locators copied from the export, not independently read source anchors.

## Shared operational reconstruction

Write `C_i = C i`, `prefix_t = [stream 0,...,stream (t-1)]`, and `sample_t` for its finite set of values. A learner is a total function `List Nat -> Nat`; this representation alone does not assert computability. Membership oracles answer whether a natural number belongs to an indexed language; subset oracles answer inclusion between entire indexed languages.

### Subset truth-table procedure

For input list xs, let n = length xs. Use encodings

```text
member(j,x)    = Nat.pair 0 (Nat.pair j x)
inclusion(j,k) = Nat.pair 1 (Nat.pair j k)
```

For each j in increasing order below n, the fixed query list first includes inclusion(j,k) for every k<j, then member(j,x) for every occurrence x in xs. All queries are fixed from xs before oracle answers are available. The combined oracle returns 1/0 for the membership or full-language-inclusion answer; any other tag returns 0.

The postprocessor reads table answers by first query-code occurrence. It tests consistency(j): every x in xs has member(j,x) answer 1. It tests critical(j): consistency(j), and for every k<j either k is inconsistent or inclusion(j,k) has answer 1. It scans j=0,...,n-1, retaining the last successful j; if none succeeds, it returns 0. `boundedAll` and `lastTrue` are explicit natural recursions with bounds strictly exclusive. No persistent state beyond the supplied input list and computed finite table appears in this interface.

`tableLookup` is exactly `(answers[queries.idxOf code]?).getD 0`. The absent-code default is 0 for the equal-length query/answer lists produced by `run`. An arbitrary longer malformed answer list could contain a value at index `queries.length`; the general function type does not validate the table. Repeated observations can duplicate query codes; correct functional oracle answers agree on repeats.

### Breadth distribution and support view

`identifiedBreadth O A xs = exactFreshSampler O xs (A xs)`. This law is the pushforward of `positiveGeometric = geometricPMF(1/2)` through the named seeded sampler. For encoded input `j :: seed :: xs`, the sampler's stage q asks the single membership query `(j,seed+q)`, then accepts y=seed+q exactly if the answer is 1 and y does not occur in xs. It uses `OracleSearchProgram.partialRun = Nat.rfindOpt(stage)` and a total `run` extracted by `Part.get` from the supplied termination certificate. The packaged O has infinitely many elements in each language, so the interface includes a theorem asserting termination for every encoded input. Its proof and construction are not certified here; no finite stage bound appears in the type.

The seed law and pushforward define a PMF on one output. The support targets concern its set of nonzero-mass outputs. `statisticalSupportView` wraps that support as a SupportGenerator and defines the Bool query by `Classical.propDecidable` on PMF-support membership. Consequently a Bool-valued query in this view does not certify an ordinary algorithm for testing support membership. The OracleFamily query and learner A likewise have no built-in computability fields. Freshness concerns observed xs; prior generated outputs are excluded only when present in xs.

## Seven target dossiers

### GenLimit.HallucinationModeCollapse.identifiedBreadth_online

Kind: **theorem**. Opaque slot: C14. Export locator: `GenLimit.Paper03_HallucinationAndModeCollapse.OnlineBreadthConstruction:19`.

Exact exported type:

```lean
∀ (O : GenLimit.OracleFamily) (A : GenLimit.Learner.{0, 0} Nat Nat),
  @GenLimit.Angluin.SemanticallyIdentifies.{0} Nat A O.language →
    GenLimit.HallucinationModeCollapse.FreshBreadthInLimit
      (GenLimit.HallucinationModeCollapse.statisticalSupportView
        (GenLimit.HallucinationModeCollapse.identifiedBreadth O A))
      O.language
```

**Reconstruction.** For every OracleFamily O and learner A, if A identifies the family O.language in the supplied stabilization sense, then the semantic support view of the named PMF-valued generator identifiedBreadth O A eventually has exactly every target-language element not yet observed, on every stream presenting each indexed target.

**Assumptions.** O packages a Nat-indexed family of infinite subsets of Nat and a correct Bool membership query. A : List Nat -> Nat is arbitrary. For every z and stream with range = O.language z, there exists an index e with O.language e = O.language z, followed by a cutoff N, such that for all t >= N, A(textPrefix stream t)=e.

**Quantifiers and dependencies.** forall O A, [forall z stream, range(stream)=O.language z -> exists e, O.language e=O.language z and exists N, forall t>=N, A(prefix_t)=e] -> forall z stream, range(stream)=O.language z -> exists T, forall t>=T, PMF.support(identifiedBreadth O A prefix_t)=O.language z minus sample(stream,t). The fixed e precedes its N. Both the hypothesis witnesses e,N and conclusion T may depend on O,A,z,stream; no bound uniform across streams is asserted.

**Operational and effectiveness boundary.** identifiedBreadth evaluates A on the ordered observation prefix, then applies the seeded exactFreshSampler at that returned index. Its support view exposes the resulting PMF support on Fin t histories. Full sampler operation and both semantic-identification definitions are expanded in the shared glossary and operational description. No computability hypothesis on A or O.query. statisticalSupportView.query uses Classical.propDecidable for PMF-support membership. This signature is a semantic eventual-support statement, not a certified ordinary support-testing or randomized-computation theorem. It supplies no rate, time bound or computable cutoff.

**Edge cases and limits.** Success is required on every presentation, but the cutoff is chosen after the particular stream. The correct stabilized index need not equal z. Range equality allows repeats; the sample removes duplicate observations as a finite set. All times after T are covered, not only infinitely many times. Each family language is infinite, so removing a finite sample cannot exhaust it. Empty target languages are excluded by OracleFamily. The conclusion is an equality of supports of single-output laws; it asserts neither uniform output probabilities nor convergence of realized random output paths.

Native recursive dependencies reviewed: 51; exact names are listed in the corresponding JSON row. Shared meanings are below. No theorem proof body was reviewed.

### GenLimit.HallucinationModeCollapse.identifiedBreadth_support

Kind: **theorem**. Opaque slot: C14. Export locator: `GenLimit.Paper03_HallucinationAndModeCollapse.BreadthConstruction:25`.

Exact exported type:

```lean
∀ (O : GenLimit.OracleFamily) (A : GenLimit.Learner.{0, 0} Nat Nat) (xs : List.{0} Nat),
  @Eq.{1} (Set.{0} Nat) (@PMF.support.{0} Nat (GenLimit.HallucinationModeCollapse.identifiedBreadth O A xs))
    (@SDiff.sdiff.{0} GenLimit.Language (@Set.instSDiff.{0} Nat) (O.language (A xs))
      (@setOf.{0} Nat fun x => @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) xs x))
```

**Reconstruction.** For every packaged OracleFamily O, every learner A, and every finite list xs, the PMF produced by identifiedBreadth O A xs has support exactly O.language (A xs) minus the set of values occurring in xs. Every fresh point of the currently predicted language has nonzero mass, and all other points have zero mass.

**Assumptions.** O packages infinite languages with a correct Bool membership query. A : List Nat -> Nat and xs : List Nat are arbitrary; no identification or validity assumption is imposed.

**Quantifiers and dependencies.** forall O A xs, PMF.support(identifiedBreadth O A xs) = O.language(A xs) minus {x | x in xs}. There are no existential cutoff, success premise or additional hypothesis arrows.

**Operational and effectiveness boundary.** The defining law is PMF.map (seededFreshSample O xs (A xs)) positiveGeometric. A seed is drawn from the geometric PMF with parameter 1/2; the named oracle search finds an unobserved member of the selected language at or above that seed. The exported definition supplies the pushforward representation, not a uniform law. No computability of A or O.query is assumed. The sampler program has primitive-recursive stage queries and a computable postprocessor, but its total run uses a termination certificate. This target certifies a support identity at the type level; no proof-body audit or ordinary randomized implementation is supplied here.

**Edge cases and limits.** For xs=[], the support is the entire predicted indexed language. For arbitrary xs, including entries outside the predicted language, set subtraction still means only values occurring in xs are excluded. Repetition changes the list presented to A but not the excluded set. Every selected language is infinite, so the finite list cannot exhaust its fresh part. Freshness is relative to xs, not to earlier generated outputs unless those were added to xs. Multiple draws may repeat. No probability lower bound or runtime bound is stated.

Native recursive dependencies reviewed: 34; exact names are listed in the corresponding JSON row. Shared meanings are below. No theorem proof body was reviewed.

### GenLimit.HallucinationModeCollapse.subsetIdentificationProgram

Kind: **definition**. Opaque slot: C16. Export locator: `GenLimit.Paper03_HallucinationAndModeCollapse.SubsetIdentification:102`.

Exact exported type:

```lean
GenLimit.Support.TruthTableProgram
```

Exact exported definition value:

```lean
{ queries := GenLimit.HallucinationModeCollapse.subsetIdentificationQueries,
  queries_primrec := GenLimit.HallucinationModeCollapse.subsetIdentificationQueries_primrec,
  output := GenLimit.HallucinationModeCollapse.subsetIdentificationPost,
  output_computable := GenLimit.HallucinationModeCollapse.subsetIdentificationPost_computable }
```

**Reconstruction.** A named TruthTableProgram value. Its query field is subsetIdentificationQueries, its postprocessor is subsetIdentificationPost, and its two proof fields reference the named primitive-recursion and computability certificates. It provides one fixed oracle-program template with finite, nonadaptive query batches.

**Assumptions.** No language family, oracle object, ConditionTwo assumption or correctness premise is an argument of this value. TruthTableProgram requires a primitive-recursive query function and a computable finite-table output function as fields.

**Quantifiers and dependencies.** This declaration has type TruthTableProgram : Type, not Prop. Its value is the record {queries=...Queries, queries_primrec=...Queries_primrec, output=...Post, output_computable=...Post_computable}. Running it is separately parameterized by oracle : Nat -> Nat and xs : List Nat.

**Operational and effectiveness boundary.** For n=length xs and each j<n in increasing order, query inclusion(j,k) for every k<j, then membership(j,x) for each occurrence x in xs. Collect all natural answers first. The postprocessor checks consistency and criticality from that table, scans j<n in increasing order, and returns the last true j or default 0. The primitive-recursive schedule and computable postprocessor are carried as named proof fields whose signatures were reviewed. Applying an arbitrary oracle does not imply ordinary computability. This data definition alone proves no language-identification proposition.

**Edge cases and limits.** An empty input has an empty query list and returns 0. Repeated observations may repeat queries. Lookup uses the first matching query code; correct functional oracle answers agree on repetitions. A table with no qualifying critical index returns 0, which need not be critical or below length xs. Raw postprocessing accepts arbitrary answer lists; no table-well-formedness condition is built into its input type. Exact lookup/default behavior is in the shared glossary.

Native recursive dependencies reviewed: 14; exact names are listed in the corresponding JSON row. Shared meanings are below. No theorem proof body was reviewed.

### GenLimit.HallucinationModeCollapse.subsetIdentifier

Kind: **definition**. Opaque slot: C16. Export locator: `GenLimit.Paper03_HallucinationAndModeCollapse.SubsetIdentification:138`.

Exact exported type:

```lean
{C : GenLimit.Generic.LanguageFamily.{0} Nat} →
  GenLimit.MembershipOracle C → @GenLimit.SubsetOracle.{0} Nat C → GenLimit.Learner.{0, 0} Nat Nat
```

Exact exported definition value:

```lean
fun {C} O S =>
  GenLimit.HallucinationModeCollapse.subsetIdentificationProgram.run
    (@GenLimit.HallucinationModeCollapse.subsetIdentificationOracle C O S)
```

**Reconstruction.** For any family C with correct membership oracle O and whole-language subset oracle S, this is the learner obtained by running the fixed subsetIdentificationProgram against the combined encoded oracle subsetIdentificationOracle O S. It maps each entire finite observation list to a natural-number family index.

**Assumptions.** C : Nat -> Set Nat is implicit and arbitrary. O.query i x=true iff x belongs to C i. S.query i j=true iff C i is a subset of C j. No computability or infinitude is part of these structures.

**Quantifiers and dependencies.** implicit C, then O, then S, produce a total function xs : List Nat -> Nat. The definition is Program.run (subsetIdentificationOracle O S); there is no success or computability proposition in its type.

**Operational and effectiveness boundary.** Uses the fixed batch schedule and postprocessor above. Tag 0 codes membership, tag 1 codes full-language inclusion, and other encoded tags return 0. There is no extra persistent state or update argument; each call receives and processes the full list xs. This is a specified oracle learner. Definition as a total Lean function does not assert ordinary computability. It has no ConditionTwo requirement to exist; correctness and conditional ordinary computability are separate supplied theorem signatures.

**Edge cases and limits.** C may contain finite or empty languages and duplicate language indices. If some critical j<n exists, the last-critical theorem constrains the result. Without that premise the definition still returns its default if needed. Input order and repeats are preserved in the list and query schedule. The searched index budget is length xs, not the number of distinct examples.

Native recursive dependencies reviewed: 30; exact names are listed in the corresponding JSON row. Shared meanings are below. No theorem proof body was reviewed.

### GenLimit.HallucinationModeCollapse.subsetIdentifier_computable

Kind: **theorem**. Opaque slot: C16. Export locator: `GenLimit.Paper03_HallucinationAndModeCollapse.SubsetIdentification:142`.

Exact exported type:

```lean
∀ {C : GenLimit.Generic.LanguageFamily.{0} Nat} (O : GenLimit.MembershipOracle C)
  (S : @GenLimit.SubsetOracle.{0} Nat C),
  @Computable₂.{0, 0, 0} Nat Nat Bool (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Primcodable.bool (@GenLimit.MembershipOracle.query C O) →
    @Computable₂.{0, 0, 0} Nat Nat Bool (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Primcodable.bool
        (@GenLimit.SubsetOracle.query.{0} Nat C S) →
      @Computable.{0, 0} (List.{0} Nat) Nat
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
        (@GenLimit.HallucinationModeCollapse.subsetIdentifier C O S)
```

**Reconstruction.** For every implicit family C and every pair of correct membership and subset oracles O,S, if the two-argument Bool query function of O is computable and the two-argument Bool query function of S is computable, then the particular learner subsetIdentifier O S is an ordinary computable function from List Nat to Nat.

**Assumptions.** C is implicit; O and S are quantified before the two effectiveness premises. Computable2 O.query on Nat,Nat -> Bool. Computable2 S.query on Nat,Nat -> Bool. The query functions also satisfy the semantic correctness built into their oracle structures.

**Quantifiers and dependencies.** forall {C} O S, Computable2(O.query) -> Computable2(S.query) -> Computable(subsetIdentifier O S). Uses the displayed canonical Primcodable instances for Nat, Bool and List Nat. Both effectiveness hypotheses are required by the signature; there is no ConditionTwo premise.

**Operational and effectiveness boundary.** The named fixed truth-table procedure combines two encoded computable queries with a primitive-recursive finite schedule and computable postprocessing. The target concludes effectiveness of that same named learner, without asserting that it identifies C. A separate conditional ordinary-computability theorem. It does not supply computability from a bare arbitrary family or arbitrary oracle access, nor a function extracting one uniform code from presentations/codes for all families. A fixed common oracle template is present operationally; the stated Computable conclusion is for each quantified pair of query functions.

**Edge cases and limits.** No infinitude, nonemptiness, distinct-index condition or identification premise is required. No runtime, query-complexity, convergence-rate or computable witness-selection bound is in the type.

Native recursive dependencies reviewed: 31; exact names are listed in the corresponding JSON row. Shared meanings are below. No theorem proof body was reviewed.

### GenLimit.HallucinationModeCollapse.subsetIdentifier_finiteWitness

Kind: **theorem**. Opaque slot: C16. Export locator: `GenLimit.Paper03_HallucinationAndModeCollapse.SubsetIdentificationRates:48`.

Exact exported type:

```lean
∀ (C : GenLimit.Generic.LanguageFamily.{0} Nat) (O : GenLimit.MembershipOracle C)
  (S : @GenLimit.SubsetOracle.{0} Nat C),
  @GenLimit.Angluin.ConditionTwo.{0} Nat C →
    GenLimit.HallucinationModeCollapse.FiniteWitnessIdentifies C
      (@GenLimit.HallucinationModeCollapse.subsetIdentifier C O S)
```

**Reconstruction.** For every family C and correct membership/subset oracles O,S, ConditionTwo C implies that the specific learner subsetIdentifier O S satisfies FiniteWitnessIdentifies C: each target index admits a finite positive witness T and a length threshold N after which every consistent list containing T is assigned an index denoting exactly that target language.

**Assumptions.** C : Nat -> Set Nat, correct membership oracle O, and correct full-language inclusion oracle S. ConditionTwo C: for each i there exists a finite U subset C i such that, for every j, U subset C j and C j subset C i imply C i subset C j. No oracle-computability, infinitude or effective enumeration of the tell-tales is assumed.

**Quantifiers and dependencies.** forall C O S, [forall i, exists U : Finset Nat, U subset C i and forall j, U subset C j -> C j subset C i -> C i subset C j] -> forall i, exists T : Finset Nat, T subset C i and exists N : Nat, forall xs : List Nat, N<=length(xs) -> (forall x in xs, x in C i) -> (forall x in T, x in xs) -> C(subsetIdentifier O S xs)=C i. T is chosen before N, and both before xs. They may depend on C,O,S,i; there is no uniform-in-i or computable selection claim. U from the assumption is not identified in the theorem type with the conclusion witness T.

**Operational and effectiveness boundary.** Uses the same named bounded-index truth-table learner; the conclusion quantifies over all qualifying finite lists, rather than over one sampled stream. The output need only denote C i; its exact index can vary across lists. The named learner is explicit as an oracle procedure. This theorem provides semantic finite witnesses and thresholds, not an effective method to obtain T,N and not ordinary computability without the separate two query-computability premises.

**Edge cases and limits.** Repeated samples can make lists long without covering T; the guarantee still requires every witness element to occur. N measures list length, not running time or time until T appears. Empty T and N=0 are permitted by the definition; the theorem does not require these choices. For an empty C i, only the empty list is consistent. A chosen positive N would make the list condition vacuous, so the definition alone does not force nonvacuous identification of an empty language. No exact-index stabilization is asserted; duplicate family indices are allowed.

Native recursive dependencies reviewed: 34; exact names are listed in the corresponding JSON row. Shared meanings are below. No theorem proof body was reviewed.

### GenLimit.HallucinationModeCollapse.subsetIdentifier_last_critical

Kind: **theorem**. Opaque slot: C16. Export locator: `GenLimit.Paper03_HallucinationAndModeCollapse.SubsetIdentificationRates:25`.

Exact exported type:

```lean
∀ {C : GenLimit.Generic.LanguageFamily.{0} Nat} (O : GenLimit.MembershipOracle C) (S : @GenLimit.SubsetOracle.{0} Nat C)
  (xs : List.{0} Nat) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@List.length.{0} Nat xs) →
    GenLimit.HallucinationModeCollapse.SubsetCritical C xs k →
      And
        (@LT.lt.{0} Nat instLTNat (@GenLimit.HallucinationModeCollapse.subsetIdentifier C O S xs)
          (@List.length.{0} Nat xs))
        (And
          (GenLimit.HallucinationModeCollapse.SubsetCritical C xs
            (@GenLimit.HallucinationModeCollapse.subsetIdentifier C O S xs))
          (@LE.le.{0} Nat instLENat k (@GenLimit.HallucinationModeCollapse.subsetIdentifier C O S xs)))
```

**Reconstruction.** For any family and correct membership/subset oracles, any list xs and any k below its length, if k is SubsetCritical for xs, then the actual learner output a is also below the list length, is SubsetCritical for xs, and satisfies k <= a. Thus, conditional on a bounded critical candidate, the result is a greatest critical candidate in that bounded range.

**Assumptions.** C is implicit; O,S are correct membership and full-language inclusion oracles. xs : List Nat and k : Nat. k < length xs. SubsetCritical C xs k: xs is contained in C k and for every h<k consistent with xs, C k subset C h.

**Quantifiers and dependencies.** forall {C} O S xs k, k<length(xs) -> SubsetCritical(C,xs,k) -> let a=subsetIdentifier O S xs in (a<length(xs) and (SubsetCritical(C,xs,a) and k<=a)). All three conclusion components are retained. There are no existential witnesses in this target.

**Operational and effectiveness boundary.** The finite postprocessor scans all candidates below length xs with lastTrue. This theorem connects its returned index to the semantic criticality predicate using the supplied correct oracle interfaces. No ConditionTwo or computability premise is present. The signature concerns bounded maximal criticality of the named oracle output, not success on every list, rates, or correctness of all program-construction proof steps.

**Edge cases and limits.** If xs=[], no natural k satisfies k<length xs; this implication is vacuous, while the learner definition returns 0. If no bounded critical index exists, the theorem supplies no output-criticality or output-bound guarantee. SubsetCritical itself does not include the length bound, so the separate k<length xs hypothesis is essential to the stated scope. Repeated language sets at different indices do not violate the premise or conclusion; the order is on indices, not set size.

Native recursive dependencies reviewed: 32; exact names are listed in the corresponding JSON row. Shared meanings are below. No theorem proof body was reviewed.

## Shared definition and interface glossary

This glossary accounts for all 79 non-target native records. Exact types and defining values remain available in the hashed `declarations.jsonl` and `definition-dependencies.md` inputs; they are not duplicated wholesale. Definitions of propositions below are predicate meanings, not additional proved theorem results. Named certificate entries describe only their supplied types.

| Native declaration | Reconstructed meaning or interface |
| --- | --- |
| `GenLimit.Angluin.ConditionTwo` | Proposition: for every index i there exists a finite set T satisfying IsTellTale C i T. No computable choice of T is part of this definition. |
| `GenLimit.Angluin.IsTellTale` | T is a finite subset of C i, and for every j, T subset C j and C j subset C i imply C i subset C j. Both subset conclusions together force equality in the tested case. |
| `GenLimit.Angluin.SemanticIdentifier` | Alias for Learner alpha Nat, hence a total function from finite lists of alpha to natural-number indices; no computability field. |
| `GenLimit.Angluin.SemanticallyIdentifies` | For every z and stream whose range is C z, IdentifiesInLimit C M stream (C z) holds. This includes eventual stabilization to a single correct name, not only eventual correctness of denoted sets. |
| `GenLimit.DiscreteIID.positiveGeometric` | The PMF ProbabilityTheory.geometricPMF with real parameter 1/2, supplied the positive-parameter and at-most-one proofs. It is the seed law; its standard Mathlib meaning is trusted. |
| `GenLimit.DiscreteIID.positiveGeometric._proof_1` | Type-only arithmetic certificate: natural 1+1 is AtLeastTwo. No proof body is supplied or reviewed. |
| `GenLimit.DiscreteIID.positiveGeometric._proof_2` | Type-only arithmetic certificate: 0 < (1/2 : Real). No proof body is supplied or reviewed. |
| `GenLimit.DiscreteIID.positiveGeometric._proof_3` | Type-only arithmetic certificate: (1/2 : Real) <= 1. No proof body is supplied or reviewed. |
| `GenLimit.Generic.Language` | Alias alpha -> Prop, represented as Set alpha. |
| `GenLimit.Generic.LanguageFamily` | Alias Nat -> Set alpha. Different indices may denote the same set; no injectivity or infinity is built in. |
| `GenLimit.Generic.Presents` | Presents stream L means Set.range stream = L. Repetitions are permitted; every stream value is in L and every member of L appears. |
| `GenLimit.Generic.Stream` | Alias Nat -> alpha, an infinite sequence with no blank symbol. |
| `GenLimit.Generic.sample` | Finite set image of stream on Finset.range t, using classical equality in the generic definition. It records distinct observations at positions 0 through t-1. |
| `GenLimit.HallucinationModeCollapse.FiniteWitnessIdentifies` | For every i, exists finite T subset C i, then exists N, such that every list xs of length at least N, with all entries in C i and containing all T, satisfies C (A xs) = C i. T and N precede xs; exact output-index stabilization is not required. |
| `GenLimit.HallucinationModeCollapse.FreshBreadthInLimit` | For every z and every stream presenting C z, exists cutoff T, then for every t >= T, supportAt G stream t = C z minus the finite sample at t. The cutoff is stream-specific; equality holds at all later times. |
| `GenLimit.HallucinationModeCollapse.StatisticalGenerator` | Alias List Nat -> PMF Nat: a law on one natural-number output for each finite observation list. |
| `GenLimit.HallucinationModeCollapse.SubsetCritical` | Critical(C,xs,j) means all entries of xs lie in C j, and for every k < j whose language contains xs, C j is a subset of C k. No j < length xs bound is part of this predicate itself. |
| `GenLimit.HallucinationModeCollapse.SupportGenerator` | Structure with a support set and a Bool membership query for each t and Fin t -> Nat history, plus exact query-correctness proof. It has no computability field. |
| `GenLimit.HallucinationModeCollapse.SupportGenerator.mk` | Constructor receives support, query and, for every t/history/x, query=true iff x is in that support. This constructor does not require an executable or computable query. |
| `GenLimit.HallucinationModeCollapse.SupportGenerator.support` | Projection of the first field of SupportGenerator. |
| `GenLimit.HallucinationModeCollapse.exactFreshSampler` | For O,xs,j, pushes the fixed positiveGeometric seed PMF forward through seed -> seededFreshSample O xs j seed. This specifies a law, with no equality to a uniform law asserted. |
| `GenLimit.HallucinationModeCollapse.generationOracle` | Unpairs code as (j,y), tests O.query j y and returns natural 1 for true, 0 for false. No computability assumption on O.query is built in. |
| `GenLimit.HallucinationModeCollapse.identifiedBreadth` | For O,A,xs, evaluates A xs and returns exactFreshSampler O xs (A xs). Freshness is relative to the observed list xs. |
| `GenLimit.HallucinationModeCollapse.samplerIndex` | First input-list entry, default 0 when missing. |
| `GenLimit.HallucinationModeCollapse.samplerPost` | On ((input,q),answers), y= samplerSeed(input)+q; returns some y exactly when y is not in samplerSample(input) and answers[0]? with default 0 equals 1; otherwise none. |
| `GenLimit.HallucinationModeCollapse.samplerPost_computable` | Type-only certificate that samplerPost is Computable under the displayed standard natural/list/product/option encodings. |
| `GenLimit.HallucinationModeCollapse.samplerProgram` | OracleSearchProgram record with samplerQueries and samplerPost, carrying the named Primrec-query and Computable-postprocessor certificates. |
| `GenLimit.HallucinationModeCollapse.samplerProgram_terminates` | For every packaged O, samplerProgram.Terminates (generationOracle O). Expanded: for every encoded input list, some stage q and output y give some y. No bound is supplied and the proof body is withheld. |
| `GenLimit.HallucinationModeCollapse.samplerQueries` | At (input,q), asks the singleton query Nat.pair (samplerIndex input) (samplerSeed input + q). The stage query is determined without earlier oracle answers. |
| `GenLimit.HallucinationModeCollapse.samplerQueries_primrec` | Type-only certificate that samplerQueries is primitive recursive in its finite-list/stage input. |
| `GenLimit.HallucinationModeCollapse.samplerSample` | Drops the first two input-list entries using tail twice. Missing entries yield the ordinary empty-tail behavior. |
| `GenLimit.HallucinationModeCollapse.samplerSeed` | Second input-list entry, default 0 when missing. |
| `GenLimit.HallucinationModeCollapse.seededFreshSample` | Runs samplerProgram on generationOracle O with input j :: seed :: xs, using the named termination certificate. The run extracts the partial-search result; no time bound is part of the definition. |
| `GenLimit.HallucinationModeCollapse.statisticalSupportView` | Sets support(t,h)=PMF.support(G(List.ofFn h)). Its Bool query decides membership using Classical.propDecidable, with a supplied correctness certificate. This is a semantic support view, without an effective support-testing theorem. |
| `GenLimit.HallucinationModeCollapse.statisticalSupportView._proof_1` | Type-only certificate that the classically decided membership Bool in statisticalSupportView is true iff the point lies in the corresponding PMF support. |
| `GenLimit.HallucinationModeCollapse.subsetAnswerAt` | At (xs,answers), looks up code in the query list subsetIdentificationQueries xs using tableLookup, preserving its first-occurrence and default behavior. |
| `GenLimit.HallucinationModeCollapse.subsetIdentificationOracle` | Unpairs code as (tag,payload) and payload as (a,b). Tag 0 asks membership O.query a b; tag 1 asks whole-language inclusion S.query a b. Returns natural 1 or 0 for the Bool answer; any other tag returns 0. |
| `GenLimit.HallucinationModeCollapse.subsetIdentificationPost` | At (xs,answers), scans subsetTableCritical over indices j < length xs with lastTrue and returns the greatest true index; if none, returns 0. |
| `GenLimit.HallucinationModeCollapse.subsetIdentificationPost_computable` | Type-only certificate that subsetIdentificationPost is Computable on the finite input/answer-list pair. |
| `GenLimit.HallucinationModeCollapse.subsetIdentificationQueries` | For j=0,...,length(xs)-1 in that order: first inclusionCode j k for k=0,...,j-1, then memberCode j x for each occurrence x in xs. Concatenates these blocks; duplicate observations can duplicate query codes. |
| `GenLimit.HallucinationModeCollapse.subsetIdentificationQueries_primrec` | Type-only certificate that the complete fixed query-list function subsetIdentificationQueries is primitive recursive. |
| `GenLimit.HallucinationModeCollapse.subsetInclusionCode` | Encodes full-language inclusion from index j to index k as Nat.pair 1 (Nat.pair j k). The orientation is C j subset C k. |
| `GenLimit.HallucinationModeCollapse.subsetMemberCode` | Encodes membership of x in language j as Nat.pair 0 (Nat.pair j x). |
| `GenLimit.HallucinationModeCollapse.subsetTableConsistent` | A finitely decidable Bool: every x appearing in xs has table answer 1 at memberCode j x. The forall is bounded by list membership. |
| `GenLimit.HallucinationModeCollapse.subsetTableCritical` | Bool conjunction of consistency at j and boundedAll over k < j of not-consistent(k) or table-answer(inclusionCode j k)=1. It tests the full direction j to k. |
| `GenLimit.HallucinationModeCollapse.supportAt` | Evaluates G.support t on the finite history i -> stream(i.val), i : Fin t. |
| `GenLimit.IdentifiesInLimit` | There exists a single name with correct denotation, and StabilizesTo of the learner on finite text prefixes to that name. The name is chosen before the stabilization cutoff. |
| `GenLimit.Language` | Alias Set Nat. |
| `GenLimit.LanguageFamily` | Alias Nat -> Language, hence Nat -> Set Nat. |
| `GenLimit.Learner` | Alias List Info -> Name, a total mathematical function with no computability assertion. |
| `GenLimit.MembershipOracle` | Structure over a natural-number language family with Bool membership query and correctness proof; no infinity or computability requirement. |
| `GenLimit.MembershipOracle.mk` | Receives query : Nat -> Nat -> Bool and proof, for all i,u, query i u=true iff u is in C i. |
| `GenLimit.MembershipOracle.query` | Projection of the membership query field; family and proof fields supply its semantic specification. |
| `GenLimit.OracleFamily` | Packages a language family, infinitude of every indexed language, a Bool membership query, and exact query correctness. The membership query need not be ordinarily computable. |
| `GenLimit.OracleFamily.language` | Projection of the language-family field. |
| `GenLimit.OracleFamily.mk` | Constructor receives language, a proof that each language is infinite, query, then proof that query i u=true iff u belongs to language i. |
| `GenLimit.OracleFamily.query` | Projection of the third OracleFamily field, the membership query. |
| `GenLimit.StabilizesTo` | There exists cutoff T such that for every natural t >= T, guess t equals the same fixed name. |
| `GenLimit.SubsetOracle` | Structure over a family with Bool query on two indices and exact whole-language inclusion specification, with no computability field. |
| `GenLimit.SubsetOracle.mk` | Receives query and proof that for every i,j, query i j=true iff C i subset C j. No counterexample is returned. |
| `GenLimit.SubsetOracle.query` | Projection of the Bool whole-language inclusion query. |
| `GenLimit.Support.OracleSearchProgram` | Structure containing stage-dependent finite queries : (List Nat x Nat) -> List Nat with Primrec certificate, and postprocessor : ((List Nat x Nat) x List Nat) -> Option Nat with Computable certificate. |
| `GenLimit.Support.OracleSearchProgram.Terminates` | For every finite input xs, there exist q and y such that P.stage oracle xs q=some y. q and y may depend on xs and oracle; no uniform bound is present. |
| `GenLimit.Support.OracleSearchProgram.mk` | Constructor takes stage-query function, its primitive-recursion proof, postprocessor, then its computability proof. It does not itself include a termination proof. |
| `GenLimit.Support.OracleSearchProgram.output` | Projection of the third field, the Option-valued postprocessor. |
| `GenLimit.Support.OracleSearchProgram.partialRun` | The partial natural-number search Nat.rfindOpt (P.stage oracle xs). Standard Mathlib partial-search semantics is trusted, not recursively audited here. |
| `GenLimit.Support.OracleSearchProgram.queries` | Projection of the stage-query function. |
| `GenLimit.Support.OracleSearchProgram.run` | Given a termination proof, extracts a Nat from partialRun by Part.get using the corresponding domain proof. The suppressed proof term is not an executable time bound. |
| `GenLimit.Support.OracleSearchProgram.run_dom` | Type-only certificate: Terminates P oracle implies partialRun oracle xs has domain for every xs. |
| `GenLimit.Support.OracleSearchProgram.stage` | At stage q, forms the finite answers by mapping oracle over P.queries (xs,q), then calls P.output ((xs,q),answers). |
| `GenLimit.Support.TruthTableProgram` | Structure containing queries : List Nat -> List Nat with Primrec certificate and output : (List Nat x List Nat) -> Nat with Computable certificate. No language family occurs in this representation. |
| `GenLimit.Support.TruthTableProgram.mk` | Constructor receives queries, proof Primrec queries, output, and proof Computable output; it constructs data with effectiveness certificates, not an identification theorem. |
| `GenLimit.Support.TruthTableProgram.output` | Projection of the third field, the finite-table postprocessor. |
| `GenLimit.Support.TruthTableProgram.queries` | Projection of the query-list field. |
| `GenLimit.Support.TruthTableProgram.run` | For P, oracle, xs, computes P.output (xs, List.map oracle (P.queries xs)); all queries are fixed before the answers are read. |
| `GenLimit.Support.boundedAll` | Recursion: value at 0 is true; value at k+1 is previous.and(p a k). Thus it tests all indices strictly below the supplied bound, including vacuous true at bound 0. |
| `GenLimit.Support.lastTrue` | Recursion: value at 0 is none; at k+1 replace previous with some k if p a k=true, otherwise keep previous. Thus it returns the greatest true index strictly below the bound, or none. |
| `GenLimit.Support.tableLookup` | Returns (answers[queries.idxOf code]?).getD 0. Uses the first matching query. For an absent code, idxOf is query-list length; well-formed run answer lists have that same length, so lookup returns 0. Arbitrary longer malformed answer lists need not have that absent-code behavior. |
| `GenLimit.textPrefix` | List.map stream (List.range t): ordered, length-t observations at positions 0 through t-1, preserving repeats. |

## Exhaustive target coverage

| Opaque slot | Exact native target | Kind | Status |
| --- | --- | --- | --- |
| C14 | `GenLimit.HallucinationModeCollapse.identifiedBreadth_online` | theorem | Type and relevant defining interfaces reconstructed; no proof/source certification |
| C14 | `GenLimit.HallucinationModeCollapse.identifiedBreadth_support` | theorem | Type and relevant defining interfaces reconstructed; no proof/source certification |
| C16 | `GenLimit.HallucinationModeCollapse.subsetIdentificationProgram` | definition | Type and relevant defining interfaces reconstructed; no proof/source certification |
| C16 | `GenLimit.HallucinationModeCollapse.subsetIdentifier` | definition | Type and relevant defining interfaces reconstructed; no proof/source certification |
| C16 | `GenLimit.HallucinationModeCollapse.subsetIdentifier_computable` | theorem | Type and relevant defining interfaces reconstructed; no proof/source certification |
| C16 | `GenLimit.HallucinationModeCollapse.subsetIdentifier_finiteWitness` | theorem | Type and relevant defining interfaces reconstructed; no proof/source certification |
| C16 | `GenLimit.HallucinationModeCollapse.subsetIdentifier_last_critical` | theorem | Type and relevant defining interfaces reconstructed; no proof/source certification |

## Provenance and limitations

The requested model remains `gpt-6.1-sol` with `xhigh` reasoning. Backend revision, actual model selection and actual reasoning configuration are not exposed to this reviewer and are not invented. This is a continuation of the retained paper-withheld Stage 1 context, not a fresh reset. Earlier exposure was Lean-only: the original Stage 1 instruction files, three opaque empty-endpoint slot records, export notices, frozen snapshot metadata/module locators and external-boundary list. The original native census was only hashed and newline-counted (1,569 entries); none of its declaration contents was semantically reviewed then. The no-target reports were written in that same earlier context. Their bytes were hash-checked here only to verify preservation, not used to infer mathematical or source content.

All three original Stage 1 report hashes match the retained pre-supplement hashes. They were not modified. Only the three assigned supplement output files were written. No source paper, Stage 2/3 material, owner notes, registry, PaperMap, developer comments, old audits or raw Lean source/proofs were accessed. No Git or library changes, compilation, external browsing, source correspondence verdicts, proof-body certification or human certification occurred. The prompt states that this supplement derives from the original frozen environment; this run verifies the supplied package hashes and internal references, without independently rebuilding that environment.

The semantic witness quantifiers and Boolean/probabilistic representations above are all that the supplied types establish. Existence of a finite witness or cutoff is not an effective construction, and a structure-valued definition is not a theorem that it identifies a family. Work ends after this supplemental Stage 1 reconstruction.
