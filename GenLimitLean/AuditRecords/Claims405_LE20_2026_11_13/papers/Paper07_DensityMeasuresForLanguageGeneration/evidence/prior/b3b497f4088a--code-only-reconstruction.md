# Paper-withheld reconstruction of nine Lean declarations

## Scope and input census

This report reconstructs the supplied statements as mathematics. It uses only the Stage1 interface, including its explicit-target-types supplement, which was supplied before the initial handoff, and the requested-choice-values supplement added on request during this reconstruction. Declaration names and source paths below are locators. They supply no evidence of an intended source theorem. No paper, owner material, Stage2, Stage3 context, registry, PaperMap, other audit, external mathematical source, raw library file, or theorem proof body was consulted.

The interface contains nine target declarations and 73 other exported declarations, including definitions, constructors, and theorem types used as dependency interfaces. All 13 entries of the root SHA256SUMS passed, as did both entries of explicit-target-types/SHA256SUMS. The later requested-choice-values/SHA256SUMS also passed all three entries, and its own hash matched the coordinator-provided 3b781c8353db3cc508fe19d683182ed27dbdcf40254cf3fccf0c0532f98c73c3. All three manifest files themselves are hashed in the run record. The source snapshot describes a dirty working-tree byte snapshot at Git head 60620581aa210daec6fa7d3aa65d7f9fdb565b8c, branch work/non-p38; this is provenance supplied by snapshot.json, not an independently checked checkout. The declared Lean toolchain is leanprover/lean4:v4.24.0, and the supplied Lake manifest records Mathlib revision f897ebcf72cd16f89ab4577d0c826cd14afaafc7.

The input census is: START_HERE.md and PROMPT.md (instructions); targets.txt and 01-target-statements.md (scope, types, source anchors); 02-definition-dependencies.md and declarations.jsonl (dependency types, definition values, constructors, generated dependency interfaces); explicit-target-types/README.md and types.jsonl (the same nine kernel types with implicit applications exposed); external-constant-boundary.txt (standard Lean/Mathlib boundary); snapshot.json, lean-toolchain, lakefile.toml and lake-manifest.json (provenance/configuration); and the initial two SHA256SUMS files (integrity). The requested-choice-values directory adds README.md, provenance.json, values.jsonl, and its own SHA256SUMS. Its supplied timestamp is 2026-11-10T14:33:35.173300+00:00. It mechanically exposes the implicit predicates in the existing levelOf and leastCommonAncestor definitions with proof bodies suppressed; it supplies no new assumption. Exact input hashes and the ordered access log are in stage1-run.json.

The configured reviewer model is coordinator-declared gpt-6.1-sol, reasoning effort xhigh, fresh fork none. The backend model revision is unknown; no runtime introspection verifies that revision. This is a statement reconstruction, not a fresh compilation, proof-body audit, source-correspondence judgment, or human certification. No Lean or Lake command was run and no library or Git file was edited.

## Definition glossary and dependency anchors

In this report D means the namespace GenLimit.KleinbergWei.DensityMeasures, P means D.FiniteRankParent, F means D.FiniteRankFallback, T means GenLimit.KleinbergWei.TowerTopology, and O means GenLimit.KleinbergWei.OrderedLanguage. Each anchor below is an exported declaration in 02-definition-dependencies.md and declarations.jsonl; source locations are transcribed from that interface.

**Languages and presentations.** GenLimit.Language is Set Nat, and LanguageFamily is Nat → Language (Core/Basic.lean:20,23). Families are therefore countably indexed, can repeat languages, and need not contain only infinite languages. Presents s L means range(s)=L (:26): every stream item lies in L and every element of L occurs at some finite time. It permits repetitions and has no computability requirement. A total Nat-indexed presentation forces L nonempty but does not force it infinite. sample s t is the finite set {s(i) | i<t} (:30); Consistent C s t i means sample s t ⊆ C(i) (:34).

**The fixed index selector.** D.StrictCritical C s t n means C(n) contains sample s t and is a proper subset of every consistent C(i) with i<n (StrictCritical.lean:18). FirstOccurrence C z says ∀i<z, C(i)≠C(z) (:57), leaving later duplicates unrestricted. scopedFocus is the greatest strict-critical index in {0,…,t}, with default 0 (Accurate.lean:16,29; Support/LeastCandidate.lean:49). For w, firstBadStrictCritical is the least strict-critical n omitting w if such an n exists, and 0 otherwise (Accurate.lean:63,68). boundaryCandidates consists of strict-critical indices strictly below that boundary whose languages contain w (:94). selectIndex C s t w uses scopedFocus if every strict-critical language contains w; otherwise it uses the greatest boundary candidate when nonempty and scopedFocus when empty (:110). guessIndex C s 0=0, and guessIndex C s (t+1)=selectIndex C s t (s t) (:175). Thus the index at time t+1 uses the prefix through s(t), but its strict-critical predicate uses the preceding sample of length t. Global subset and all-index tests are semantic predicates; these definitions do not supply an effective membership/subset oracle or a computable program.

**Validity and accuracy.** IndexValidInLimit means ∃T∀t≥T, C(guessIndex C s t)⊆C(z) (Accurate.lean:181). AccurateAt C s z r means equality of these languages, not equality of their indices (InfinitelyOften.lean:76).

**Ordered densities.** An OrderedLanguage consists of a carrier K⊆Nat and an injective enumeration e:Nat→Nat with range(e)=K (Core/OrderedDensity.lean:24, constructor mk). It necessarily has infinite carrier; no increasing numerical order is required. prefixCount K A n counts positions i<n with e(i)∈A (:33). prefixRatio is this count divided by n in Real for n>0, explicitly 0 at n=0 (:197). upperDensity and lowerDensity are respectively the limsup and liminf of these ratios along Nat atTop (:233,237). They measure A along K's enumeration; elements outside K are invisible. D.indexUpperDensityAt C s K t is upperDensity K (C(guessIndex C s t)), and indexUpperDensityLimsup takes a second, outer limsup over t (IndexLimsup.lean:18,23). All fractions and density comparisons in targets 2, 8, and 9 are real-valued, confirmed by explicit-target-types/types.jsonl.

**Feasible sequences.** A FeasibleSequence S L is data in Type: every S(n) is a proper subset of L, together with an enumeration e presenting L and ∀n i, i≤n→e(i)∈S(n) (Feasible.lean:18, mk). The inclusive i≤n is significant. There is no monotonicity or injectivity field for S or e. constrainedLanguages S A is {M | ∃n, A⊆S(n) ∧ M=S(n)} (:150); its elements are languages, not indices.

**Neighborhoods, towers, and finite rank.** Point X is the subtype {L:Language | L∈X} (Support/KleinbergWei/TowerTopology.lean:17). For K∈X and a finite set A, basicNeighborhood X K A={L∈X | A⊆L⊆K} (:20). KWOpen X U means that every K∈U has some finite A⊆K whose basic neighborhood lies inside U (:31). IsLimitPoint K means every such open U containing K contains L≠K (:92). RelativeLimitPoint Y K additionally requires K∈Y and, for every finite A⊆K, another L∈Y with A⊆L⊆K (CantorBendixson.lean:12). The derivative retains these relative limit points; D₀ is all points, Dₙ₊₁ is the derivative of Dₙ, cbLevel n=Dₙ∖Dₙ₊₁, and FiniteRankAtMost X r means Dᵣ=∅ (:20,42,65,85; D.cbLevel is an alias).

FixesAt tower n u means u belongs to tower(m) for every m≥n and either n=0 or u∉tower(n−1) (TowerTopology.lean:177). A PerfectTower in X ending at K requires every tower(n) to be a proper subset of K; for every n some u∈K fixes at n; and for every u∈K some n fixes u (:182, mk). D.PerfectTower is an alias (Topology.lean:15). Fixing entails permanent future presence with an immediate-predecessor absence condition, not absence from the entire earlier history.

**Finite-rank points and fallback.** P.FamilySpace C=range(C), FamilyPoint C=Point(range C), and familyPoint C i represents C(i) (ParentForest.lean:34,38,42). RemainingAt C s q L means sample s (q+1)⊆L, so RemainingPoint is a subtype carrying consistency through input s(q) (:51,57). identifiedPointAt C s q represents C(guessIndex C s (q+1)) (DynamicComponent.lean:506). These domains resolve the unprinted binders in target 5.

P.ParentCandidate at round q is an index n that is strict-critical at sample length q+1, properly contains the child language, and has strictly larger levelOf than the child (ParentForest.lean:157). parentIndexAt takes the greatest candidate if the candidate set is finite and nonempty, none if empty, and its q-th Nat.nth candidate if infinite (:165,173); parentAt maps the selected index to its family point (:341). EdgeAt is equality with this selected parent (:365), and AncestorAt is its reflexive transitive closure, allowing the child itself (DynamicComponent.lean:27). F.IsAncestorLanguageAt additionally packages the ancestor's consistency at that round; IsCommonAncestorAt requires ancestry at q for current and at q+1 for next (Fallback.lean:47,59,71).

fallbackChoice returns none for equal underlying current/next languages. For unequal languages it returns next if next⊆current and their levelOf values differ; otherwise it returns a chosen common ancestor when one exists, and none when none exists (Fallback.lean:280). The inequality in this branch is “different levels”; a direction of rank change is not inserted into the condition.

**Resolved choice predicates.** The requested-choice-values/values.jsonl supplement shows that levelOf hr L chooses a natural i satisfying i<r and L∈cbLevel X i. It is a classical semantic choice of a level, not an effective rank computation. The supplement also shows that leastCommonAncestor chooses a family point x satisfying IsCommonAncestorAt for the current/next pair and levelOf hr x equal to Nat.find of CommonAncestorLevel. CommonAncestorLevel k means some common ancestor has level k (Fallback.lean:129). Thus this is a common ancestor at the least available natural level; no unique ancestor or tie-breaking algorithm within that level is specified. The existential proof arguments remain elided, as permitted by the interface. Their bodies are not needed to read the now-explicit choice predicates.

## Target dossiers

All nine type strings below are copied verbatim from 01-target-statements.md (whitespace only may vary). The pp.explicit supplement disambiguates hidden domains without adding hypotheses. In the prose, natural quantifiers range over all naturals including zero, and all sets are semantic sets.

### 1. GenLimit.KleinbergWei.DensityMeasures.Results.theorem_2_1

Source anchor: GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean:26

Exact target type:

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {z : Nat},
  GenLimit.Presents stream (C z) →
    GenLimit.KleinbergWei.DensityMeasures.FirstOccurrence C z →
      And (GenLimit.KleinbergWei.DensityMeasures.IndexValidInLimit C stream z)
        (∀ (t : Nat), ∃ r, And (LE.le.{0} t r) (GenLimit.KleinbergWei.DensityMeasures.AccurateAt C stream z r))
```

**Reconstruction.** For every countably indexed family C, total stream s, and index z, if s presents C(z) and z is the first index of that language, the single fixed selector guessIndex has both of the following properties. There is a time T after which every selected language is a subset of C(z). Also, for every requested time t there exists a possibly later r≥t at which the selected language equals C(z).

**Quantifier skeleton.** ∀C,s,z, [range(s)=C(z)] → [∀i<z,C(i)≠C(z)] → [(∃T∀q≥T,C(g(q))⊆C(z)) ∧ (∀t∃r≥t,C(g(r))=C(z))], where g(q)=guessIndex C s q. The witnesses T and r may depend on C,s,z and the hypotheses; r additionally depends on t. There is no common numerical convergence rate.

**Dependencies and available information.** Use the language, selector, validity, and accuracy glossary entries, particularly AccurateAt and IndexValidInLimit. The selector's arguments are C,s,time; it does not take z, its first-occurrence proof, or a presentation proof as input. Its displayed evaluation depends on a finite stream prefix, but arbitrary family subset/equality tests are semantic. The type neither constructs a computable learner nor states an oracle model.

**Scope and edges.** Language equality can occur at a later duplicate index, so index stabilization to z is not claimed. The equality times are unbounded, not necessarily eventually all times. Eventual subset validity allows empty selected languages and has no nonemptiness or novelty conjunct. There is no single-token output, probability law, support-loss statement, or output-history freshness condition. At time 0 the index is 0 and is not guaranteed correct. z=0 makes FirstOccurrence vacuous. Empty target languages cannot satisfy Presents; finite nonempty targets and repeated inputs are allowed. C's other languages may be empty, finite, infinite, or repeated.

### 2. GenLimit.KleinbergWei.DensityMeasures.Results.corollary_2_2

Source anchor: GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean:27

Exact target type:

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {z : Nat} (ordering : GenLimit.KleinbergWei.OrderedLanguage),
  Eq.{1} (GenLimit.KleinbergWei.OrderedLanguage.carrier ordering) (C z) →
    GenLimit.Presents stream (C z) →
      GenLimit.KleinbergWei.DensityMeasures.FirstOccurrence C z →
        And (GenLimit.KleinbergWei.DensityMeasures.IndexValidInLimit C stream z)
          (Eq.{1} (GenLimit.KleinbergWei.DensityMeasures.indexUpperDensityLimsup C stream ordering) 1)
```

**Reconstruction.** For every family C, stream s, target index z, and ordered language K whose carrier equals C(z), a presentation of C(z) and first occurrence at z imply eventual selected-language containment in C(z), and the real number indexUpperDensityLimsup C s K equals 1.

**Quantifier skeleton.** ∀C,s,z,K, [carrier(K)=C(z)] → [range(s)=C(z)] → [FirstOccurrence C z] → [(∃T∀t≥T,C(g(t))⊆C(z)) ∧ limsupₜ(limsupₙ p_K(C(g(t)),n))=1]. Here p_K(A,n) counts enumeration positions below n in A, divided by n for n>0, and is 0 at n=0. Both limiting variables run along Nat atTop.

**Dependencies and available information.** The density definitions in IndexLimsup.lean:18,23 and OrderedDensity.lean:33,197,233 distinguish the two limsups. The selector does not use K as an argument; K supplies the reference ordering for the measurement. It is any injective enumeration of the target, with no connection required between its order and the possibly repeating presentation stream.

**Scope and edges.** The ordered-language constructor forces C(z) infinite, although no separate infinite-language premise is printed. A finite or empty C(z) admits no such K. This theorem concerns a sequence of language-valued guesses and their upper densities; it does not give a lower density of one accumulated output set. Outer limsup 1 does not assert convergence to 1, eventual density exactly 1, or lower density 1 for every late guess. The eventual subset assertion remains a separate conjunct. Repeated family indices and the default initial guess are handled as in target 1. The density equality is in Real; it is not natural division.

### 3. GenLimit.KleinbergWei.DensityMeasures.Results.theorem_2_4_feasibility_core

Source anchor: GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean:28

Exact target type:

```lean
∀ {sequence : Nat → GenLimit.Language} {terminal : GenLimit.Language}
  (h : GenLimit.KleinbergWei.DensityMeasures.FeasibleSequence sequence terminal) (F : Finset.{0} Nat),
  HasSubset.Subset.{0} (↑F) terminal →
    Set.Infinite.{0} (GenLimit.KleinbergWei.DensityMeasures.constrainedLanguages sequence F)
```

**Reconstruction.** For any sequence S:Nat→Set Nat and terminal L, given feasible-sequence data h and any finite F⊆L, infinitely many distinct languages occurring as values S(n) contain F. The conclusion is Set.Infinite of a subset of the type Language.

**Quantifier skeleton.** ∀S,L,h:FeasibleSequence S L,∀F:Finset Nat, [F⊆L] → Infinite{M:Set Nat | ∃n:Nat, F⊆S(n) ∧ M=S(n)}. Unpacking h supplies ∀n,S(n)⊊L, one e with range(e)=L, and ∀n∀i≤n,e(i)∈S(n). The same e serves all n; it is not chosen separately for each finite constraint.

**Dependencies and available information.** FeasibleSequence.mk and constrainedLanguages (Feasible.lean:18,150) settle both the inclusive prefix condition and the type of the infinite set. This is an abstract existence/infinity assertion about supplied data, with no learner or algorithm input and no effective procedure enumerating distinct constrained languages.

**Scope and edges.** S need not be increasing or injective. Counting infinitely many indices with repeated values would be weaker than the actual conclusion and is not substituted for it. F=∅ gives infinitude of the range of S. The conclusion is conditional on F⊆L; a constraint outside L is excluded. Empty L has no presentation. A finite L cannot support h: some finite prefix of its enumeration already includes all of L, contradicting the proper-subset condition for a sufficiently late S(n). The constructor does not separately require every S(n) infinite; it does force each S(n) to contain at least e(0). No topology, density, probability, or generation guarantee appears in this target.

### 4. GenLimit.KleinbergWei.DensityMeasures.Results.claim_6_1

Source anchor: GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean:30

Exact target type:

```lean
∀ {X : Set.{0} GenLimit.Language} {terminal : GenLimit.KleinbergWei.TowerTopology.Point X} (enumeration : Nat → Nat),
  GenLimit.Presents enumeration ↑terminal →
    Iff (GenLimit.KleinbergWei.TowerTopology.IsLimitPoint terminal)
      (∃ tower, GenLimit.KleinbergWei.DensityMeasures.PerfectTower X tower terminal)
```

**Reconstruction.** For any set X of languages, a terminal point K∈X, and any total enumeration e presenting K, K is a limit point for the exported finite-positive-constraint topology if and only if there exists a PerfectTower of points of X terminating at K.

**Quantifier skeleton.** ∀X,K∈X,e, [range(e)=K] → [(∀U, KWOpen X U → K∈U → ∃L∈U,L≠K) ↔ ∃a:Nat→Point X, PerfectTower X a K]. Expanded tower conditions are: ∀n,a(n)⊊K; ∀n∃u∈K, [∀m≥n,u∈a(m)] ∧ [n=0∨u∉a(n−1)]; and ∀u∈K∃n, [∀m≥n,u∈a(m)] ∧ [n=0∨u∉a(n−1)].

**Dependencies and available information.** T.KWOpen, basicNeighborhood, IsLimitPoint, FixesAt, and PerfectTower.mk provide the exact meanings (glossary). The right-hand tower can depend on X,K,e and the limit-point proof. The equivalence has the presentation assumption outside both directions; the supplied e does not itself appear in the tower predicate.

**Scope and edges.** X is an arbitrary set of languages; no countability of X is assumed. Only the witness tower is a Nat sequence. FixesAt at n>0 requires absence from a(n−1), not from every earlier a(i); prior transient occurrences are allowed. At n=0 no previous-stage absence is imposed, and some terminal element must already belong to all tower stages. No monotone-inclusion field for a is present. Every terminal element eventually persists, and each stage has a newly fixing witness. The constructor requires proper subset at every stage, not just inequality. Empty K fails the presentation premise; finite nonempty K is isolated by the basic neighborhood with F=K, so both sides are false under the premise. A singleton X has no such limit point. There is no computable tower construction or uniform program in the type.

### 5. GenLimit.KleinbergWei.DensityMeasures.Results.theorem_6_2_finite_rank_endgame

Source anchor: GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean:31

Exact target type:

```lean
∀ {C : GenLimit.LanguageFamily} {stream : Nat → Nat} {r z : Nat}
  (hr :
    GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost
      (GenLimit.KleinbergWei.DensityMeasures.FiniteRankParent.FamilySpace C) r),
  GenLimit.Presents stream (C z) →
    GenLimit.KleinbergWei.DensityMeasures.FirstOccurrence C z →
      ∃ T,
        ∀ (round : Nat),
          LE.le.{0} T round →
            ∃ current next,
              And
                (Eq.{1} (↑current)
                  (GenLimit.KleinbergWei.DensityMeasures.FiniteRankParent.identifiedPointAt C stream round))
                (And
                  (Eq.{1} (↑next)
                    (GenLimit.KleinbergWei.DensityMeasures.FiniteRankParent.identifiedPointAt C stream
                      (HAdd.hAdd.{0, 0, 0} round 1)))
                  (Ne.{1} ↑↑current ↑↑next →
                    ∃ fallback,
                      And
                        (Eq.{1}
                          (GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.fallbackChoice C stream r hr round
                            current next)
                          (Option.some.{0} fallback))
                        (HasSubset.Subset.{0} (↑fallback) (C z))))
```

**Reconstruction.** Fix a family C, stream s, natural rank bound r, target index z, and a proof hr that the r-th derivative of range(C) is empty. If s presents C(z) and z is its first occurrence, there is T such that every round q≥T admits consistent subtype representatives current at round q and next at round q+1 of the fixed identified family points. If their underlying languages differ, the specified fallbackChoice is some family point fallback whose language is contained in C(z).

**Quantifier skeleton.** ∀C,s,r,z,∀hr:FiniteRankAtMost(range C,r), Presents s C(z) → FirstOccurrence C z → ∃T:Nat,∀q≥T,∃current:RemainingPoint C s q,∃next:RemainingPoint C s (q+1), [val(current)=identifiedPointAt C s q] ∧ [val(next)=identifiedPointAt C s (q+1)] ∧ [language(current)≠language(next) → ∃fallback:FamilyPoint C, fallbackChoice C s r hr q current next=some fallback ∧ language(fallback)⊆C(z)].

**Dependencies and available information.** The explicit target type exposes both nested subtypes. current contains sample s (q+1), including s(q); next contains sample s (q+2), including s(q+1). Their represented languages are C(g(q+1)) and C(g(q+2)), respectively. P.identifiedPointAt, RemainingAt/RemainingPoint, and F.fallbackChoice anchor these offsets and the Option-valued conclusion. The requested choice-value supplement resolves levelOf as a classical choice of a level below r containing the point, and the common-ancestor branch as a choice at the least common-ancestor level. The fixed choice can depend on C,s,r,hr,q and these representatives. T precedes the universal q; current and next can depend on q, and fallback is inside the change guard. No bound on T is supplied.

**Scope and edges.** At unchanged rounds the implication has no fallback-existence requirement; the definition actually returns none for equal languages. At changed late rounds it guarantees some, not merely containment conditional on a value already existing. The fallback is a language in range(C), not a natural token or an index witness. It may be a proper subset of the target and may be empty; no novelty, output validity for individual tokens, or eventual stabilization of identified points is asserted. The full-domain derivative uses distinct language points, so repeated family indices do not create new points. Since range(C) is nonempty, r=0 cannot satisfy hr. A finite nonempty presented target is allowed when the other hypotheses hold. The statement does not provide a computable rank test, computable parent forest, or effective fallback procedure; Classical.choose and infinitary predicates occur in the definitions.

### 6. GenLimit.KleinbergWei.DensityMeasures.Results.theorem_6_2_persistence_diagnostic

Source anchor: GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean:33

Exact target type:

```lean
∀ (r : Nat), Not (GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.RankClimbWitness r)
```

**Reconstruction.** For every natural r, there is no natural-valued function levels on Nat whose values at positions 0 through r are all strictly below r and whose consecutive values strictly increase across each of the r steps.

**Quantifier skeleton.** ∀r:Nat, ¬∃levels:Nat→Nat, [(∀i:Nat,i≤r→levels(i)<r) ∧ (∀i:Nat,i<r→levels(i)<levels(i+1))]. The natural domain and codomain are fixed by the exported arithmetic instances and the applications in F.RankClimbWitness (Fallback.lean:1078).

**Dependencies and available information.** RankClimbWitness is the only project predicate needing expansion. This is a finite arithmetic impossibility packaged using an infinite-domain function; values above r are unrestricted. There is no C, stream, finite-rank proof, learner, historical state, or persistence predicate in this target type.

**Scope and edges.** The bound includes i=r, producing r+1 bounded values; the strict-increase condition has i<r. Dropping either endpoint changes the assertion. At r=0 it already fails because levels(0)<0 is impossible, even though the increase condition is vacuous. This target supplies no stabilization time or density consequence on its own. Its locator label does not add an application to the parent/fallback construction.

### 7. GenLimit.KleinbergWei.DensityMeasures.Results.theorem_6_12_finite_accounting

Source anchor: GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean:35

Exact target type:

```lean
∀ (n o g s b eSingleton eGood eLong : Nat),
  Eq.{1} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} o g) s) b) n →
    LE.le.{0} (HMul.hMul.{0, 0, 0} 2 s)
        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} o g) s) eSingleton) →
      LE.le.{0} g (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 o) eGood) →
        LE.le.{0} b (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 o) eLong) →
          LE.le.{0} n
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 8 o) eSingleton)
                (HMul.hMul.{0, 0, 0} 2 eGood))
              eLong)
```

**Reconstruction.** For arbitrary natural numbers n,o,g,s,b and natural error allowances eSingleton,eGood,eLong, the four hypotheses o+g+s+b=n, 2s≤o+g+s+eSingleton, g≤2o+eGood, and b≤2o+eLong imply n≤8o+eSingleton+2eGood+eLong.

**Quantifier skeleton.** ∀n,o,g,s,b,eS,eG,eL:Nat, [o+g+s+b=n] → [2s≤o+g+s+eS] → [g≤2o+eG] → [b≤2o+eL] → [n≤8o+eS+2eG+eL]. Each variable is independently universal before the hypotheses. The coefficients 8,1,2,1 and the original orientation of the equality are retained.

**Dependencies and available information.** Only ordinary natural addition, multiplication, equality, and order occur. No project definition or interpretation of the count names is needed. These are numbers at one instance, not automatically prefix counts or a partition produced by an algorithm.

**Scope and edges.** n=0 and zero counts/errors are included. Natural nonnegativity is built into the domains; no integer subtraction or positivity guard is assumed. There is no density, limit, output-language, stream, randomness, or computability claim. The theorem neither constructs these numbers nor proves that any particular process satisfies the four hypotheses. It is an accounting implication whose error allowances can be arbitrary naturals at this single instance.

### 8. GenLimit.KleinbergWei.DensityMeasures.Results.theorem_6_12_one_eighth_conditional

Source anchor: GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean:37

Exact target type:

```lean
∀ (O G Singleton Long : Nat → Nat) (eSingleton eGood eLong : Nat),
  (∀ (n : Nat),
      Eq.{1} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (O n) (G n)) (Singleton n)) (Long n)) n) →
    (∀ (n : Nat),
        LE.le.{0} (HMul.hMul.{0, 0, 0} 2 (Singleton n))
          (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (O n) (G n)) (Singleton n)) eSingleton)) →
      (∀ (n : Nat), LE.le.{0} (G n) (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (O n)) eGood)) →
        (∀ (n : Nat), LE.le.{0} (Long n) (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (O n)) eLong)) →
          LE.le.{0} (1 / 8) (Filter.liminf.{0, 0} (fun n => HDiv.hDiv.{0, 0, 0} ↑(O n) ↑n) Filter.atTop.{0})
```

**Reconstruction.** Let O,G,Singleton,Long be any four functions Nat→Nat, and fix three natural constants eSingleton,eGood,eLong. Suppose for every n their four values sum to n, twice Singleton(n) is at most O(n)+G(n)+Singleton(n)+eSingleton, G(n)≤2O(n)+eGood, and Long(n)≤2O(n)+eLong. Then liminf as n→∞ of the real ratio O(n)/n is at least 1/8.

**Quantifier skeleton.** ∀O,G,S,L:Nat→Nat,∀eS,eG,eL:Nat, [∀n,O(n)+G(n)+S(n)+L(n)=n] → [∀n,2S(n)≤O(n)+G(n)+S(n)+eS] → [∀n,G(n)≤2O(n)+eG] → [∀n,L(n)≤2O(n)+eL] → [1/8≤liminfₙ ((O(n):Real)/(n:Real))]. The constants precede all n and do not vary with n.

**Dependencies and available information.** The explicit-type supplement confirms Real division and a Real-valued Filter.liminf at Nat atTop. All four hypotheses hold at every n, including 0; they are not merely eventual hypotheses. The functions need not be monotone, computable, or realizable as counts from a language or history.

**Scope and edges.** At n=0 real division by zero has Lean's value 0; this one initial value does not alter the atTop conclusion. The sum identity forces all four counts at 0 to be zero. The finite accounting estimate gives, for n>0, O(n)/n≥1/8−(eS+2eG+eL)/(8n), a direct arithmetic consequence explaining why fixed errors disappear. The limiting assertion gives eventual lower bounds 1/8−ε for every ε>0; it does not require the ratio to reach 1/8 at every sufficiently large n. There is no language, ordering, infinite-rank premise, or construction of an output set in this target. Its conditional hypotheses must be supplied before applying the bound.

### 9. GenLimit.KleinbergWei.DensityMeasures.Results.theorem_6_12_one_tenth_conditional

Source anchor: GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean:39

Exact target type:

```lean
∀ (K : GenLimit.KleinbergWei.OrderedLanguage) (Output Good Singleton Long : GenLimit.Language) (eSingleton eGood : Nat),
  (∀ (n : Nat),
      Eq.{1}
        (HAdd.hAdd.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (GenLimit.KleinbergWei.OrderedLanguage.prefixCount K Output n)
              (GenLimit.KleinbergWei.OrderedLanguage.prefixCount K Good n))
            (GenLimit.KleinbergWei.OrderedLanguage.prefixCount K Singleton n))
          (GenLimit.KleinbergWei.OrderedLanguage.prefixCount K Long n))
        n) →
    (∀ᶠ (n : Nat) in Filter.atTop.{0},
        LE.le.{0} (HMul.hMul.{0, 0, 0} 2 (GenLimit.KleinbergWei.OrderedLanguage.prefixCount K Singleton n))
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0} (GenLimit.KleinbergWei.OrderedLanguage.prefixCount K Output n)
                (GenLimit.KleinbergWei.OrderedLanguage.prefixCount K Good n))
              (GenLimit.KleinbergWei.OrderedLanguage.prefixCount K Singleton n))
            eSingleton)) →
      (∀ᶠ (n : Nat) in Filter.atTop.{0},
          LE.le.{0} (GenLimit.KleinbergWei.OrderedLanguage.prefixCount K Good n)
            (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (GenLimit.KleinbergWei.OrderedLanguage.prefixCount K Output n))
              eGood)) →
        ∀ (C : GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.LongBadCapacityTwoCharge K Output Long),
          LE.le.{0} (1 / 10) (GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K Output)
```

**Reconstruction.** Fix an ordered infinite carrier K, arbitrary languages Output,Good,Singleton,Long, and two natural constants eSingleton,eGood. Require the four prefix counts to sum to n at every n. Require eventually 2·SingletonCount(n)≤OutputCount(n)+GoodCount(n)+SingletonCount(n)+eSingleton, and eventually GoodCount(n)≤2·OutputCount(n)+eGood. Then, for every supplied LongBadCapacityTwoCharge K Output Long certificate, the lower density of Output along K is at least the real number 1/10.

**Quantifier skeleton.** ∀K,Output,Good,S,L,eS,eG, [∀n,oₙ+gₙ+sₙ+lₙ=n] → [∃N₁∀n≥N₁,2sₙ≤oₙ+gₙ+sₙ+eS] → [∃N₂∀n≥N₂,gₙ≤2oₙ+eG] → ∀c:LongBadCapacityTwoCharge K Output L, [1/10≤liminfₙ prefixRatio K Output n]. Each count is O.prefixCount; the two eventual thresholds need not coincide. A shared later threshold may depend on the input data and certificate.

**Certificate expansion and dependencies.** CapacityCharge.lean:25 (mk) supplies a set R⊆Nat of retained positions, a total charge:Nat→Nat, a predicate inputFirst:Nat→Prop, and one constant longError:Nat. It requires: (1) every i∈R has e_K(i)∈Long; (2) eventually LongCount(n)≤2·|R∩[0,n)|+longError; (3) every i∈R satisfies charge(i)<i; (4) e_K(charge(i))∈Output for every i∈R; (5) charge is injective on R∩{i|inputFirst(i)}; and (6) it is separately injective on R∩{i|¬inputFirst(i)}. positionPrefixCount (LongCharge.lean:18) counts retained positions, not tokens outside the enumeration.

**Information and scope.** No relationship between inputFirst and any input stream is imposed: it is an arbitrary predicate carried by the certificate. Cross-class collisions of charge are allowed, giving capacity at most two overall; global injectivity is not required. Strict charge(i)<i is a position-timing guard that sends retained positions within a prefix to earlier Output positions in that prefix. There is no assertion that charge is computed online, that it is a fresh output token, or that the certificate exists for arbitrary sets. Its data are semantic and can depend on K,Output,Long. Values of charge outside R are unrestricted; i=0 cannot be retained.

The two certificate factors imply an eventual long-count allowance of 4·OutputCount(n)+longError, rather than the 2·O assumption of target 8; the resulting constant is 1/10. Together the hypotheses give eventual n≤10oₙ+eS+2eG+longError. This explains the constants without asserting a stronger unconditional density theorem.

**Edges and vacuity.** R may be finite or empty; the type has no infinitude field. If no certificate exists, the final universal quantification is vacuous. An empty Output cannot satisfy all these assumptions together with a certificate on an infinite ordered carrier. The count identity concerns only K's positions: none of the four languages is required to be globally contained in K, and their behavior outside K is invisible. Prefix identities hold at all n; the other numerical constraints, including the certificate's long bound, are eventual. No presentation, target-language validity, rank hypothesis, probability law, computable generator, or procedure constructing these four sets is in the theorem.

## Exhaustive coverage table

| Target locator suffix | Assumptions/domains preserved | Complete conclusion and timing | Witness or conditional boundary |
|---|---|---|---|
| theorem_2_1 | All C,s,z; presentation; first occurrence | Eventual subset validity AND equality at arbitrarily late times | T before all late times; r depends on requested t; fixed semantic selector |
| corollary_2_2 | Same plus ordered carrier equal to target | Eventual subset validity AND outer limsup of inner upper density equals real 1 | Injective target ordering forces infinite target; no accumulated-output density |
| theorem_2_4_feasibility_core | S,L, feasible data, finite F⊆L | Infinite set of distinct constrained language values | Inclusive feasibility coverage i≤n; no monotone sequence premise |
| claim_6_1 | Arbitrary X, terminal point, presenting enumeration | Limit-point predicate IFF existence of perfect tower | Every tower constructor field expanded; immediate-predecessor fixing guard |
| theorem_6_2_finite_rank_endgame | C,s,r,z, supplied finite-rank proof, presentation, first occurrence | Eventually consistent current/next representatives; on change, specified fallback is some and contained in target | RemainingPoint types and round offsets resolved; fallback lies inside implication |
| theorem_6_2_persistence_diagnostic | Every r including 0 | No r+1 values below r with r strict consecutive increases | Bounded range includes endpoint r; no stream application added |
| theorem_6_12_finite_accounting | Eight natural variables; equality and three inequalities | n≤8o+eSingleton+2eGood+eLong | Single-instance arithmetic; no semantic count realization assumed |
| theorem_6_12_one_eighth_conditional | Four Nat-valued functions; three constant errors; four all-n hypotheses | Real liminf O(n)/n≥1/8 | No monotonicity or language model; zero denominator handled by Real |
| theorem_6_12_one_tenth_conditional | Ordered K; four sets; constant errors; all-n identity; two eventual inequalities; supplied certificate | lowerDensity K Output≥real 1/10 | All six certificate constraints expanded; two separate injections; no existence assertion |

## Access boundary and residual limitations

The actual access sequence, checks, and byte hashes are recorded in the paired JSON. Original handoff integrity was checked before substantive reconstruction. The requested choice supplement was received and checked during reconstruction and before either output was frozen. It resolves the one decisive omission encountered; no statement-relevant project definition remains unresolved. Standard Lean/Mathlib meanings at external-constant-boundary.txt are accepted rather than recursively audited. This includes Nat.nth as natural enumeration of predicate-satisfying indices, classical choice, finite sets, subtype coercions, reflexive transitive closure, real division, and atTop liminf/limsup.

Some proof terms in definition values print as ⋯; that notation is not evidence of a proof hole. The hidden proof bodies were not inspected, and this report does not establish their correctness. Source anchors identify claimed origins in the exported snapshot without opening those files. No source-theorem strength, correspondence, proof validity, clean-checkout status, fresh build, effective implementation, or human sign-off is certified. The only writes are this report and stage1-run.json; both are frozen read-only after creation. Their SHA256 hashes are returned separately to the coordinator, with this report's hash additionally stored in stage1-run.json.
