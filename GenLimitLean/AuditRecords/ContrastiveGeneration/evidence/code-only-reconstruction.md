# 28 — Paper28_ContrastiveIdentificationAndGeneration — Contrastive Identification and Generation in the Limit — Stage 1 Lean Statement Reconstruction

## 0. Scope, integrity, and evidentiary method

This report is a code-only reconstruction of the mathematical interfaces exposed in the single bundle
`28__Paper28_ContrastiveIdentificationAndGeneration__lean-source-bundle.txt`.
The inspected file has byte size `291603` and SHA-256
`875fbf9e86e337e82b8e09783d8e39672bb993564af10a4f4981f2cac80ba79d`, exactly matching the supplied metadata.
No other project file, prior conversation, connector, web source, repository source, or author paper was used.

The bundle contains twenty-seven visible source labels. Twelve labels lie in the primary family
`GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/...`; the final root label only imports those modules and declares no new mathematics. I found 307 declarations in the twelve substantive primary labels: 120 `def` declarations, two abbreviations, two structures, two decidability instances, and 181 theorems. The imported Core, Dependency_Angluin1980, Paper08, and Paper02 declarations are separated below as background interfaces only.

The reconstruction uses declaration types, proposition expressions, and definition bodies needed to understand those types. It does not use comments, docstrings, section prose, theorem proof terms, tactic scripts, or proof-local facts as mathematical evidence. Source paths, declaration labels, and bundle line numbers are used only for provenance and cross-reference. Appendix A transcribes every one of the 307 primary-family declaration signatures or definition bodies after proof bodies have been removed, so that the coverage decision is auditable.

### Confidence and uncertainty

Confidence is high for direct translations of the displayed Lean types and definition bodies. The main residual uncertainty is classificatory rather than mathematical: some declarations are clearly low-level implementation lemmas, while the phrase “material theorem” has no formal boundary. To avoid silently omitting a declaration that another auditor might regard as material, this report gives detailed natural-language treatment to all public model definitions and all substantive theorem chains, and then includes the exhaustive proof-stripped declaration ledger in Appendix A. This is not an audit of proof correctness and is not a comparison with any external paper.

## 1. Global semantic interface

### 1.1 Universes, languages, classes, and indexing

Unless a declaration specializes to `ℕ`, the example domain is an arbitrary type `α`. A language/support is a set `h : Set α`. Two collection representations coexist:

* An indexed family is `F : ℕ → Set α`. Indices are observable outputs of identifiers, and repeated indices may denote extensionally equal sets.
* An extensional class is `𝓗 : Set (Set α)`. This forgets index order and repetitions.

A finite history of length `t` is a function `Fin t → ...`, so only the first `t` observations are available to an identifier or generator at time `t`.

The imported text-presentation predicate used by the primary declarations is exact range equality: a stream `ℕ → α` presents `L` when its range is exactly `L`. The primary contrastive-presentation predicate is different and is reconstructed below.

### 1.2 Semantic rather than effective algorithms

Every identifier and generator in the primary family is an arbitrary total Lean function on finite histories. Many concrete constructions are explicitly `noncomputable` and use classical choice, least witnesses, or arbitrary minimizers. The top-level statements do **not** assume or conclude computability, recursive enumerability, a membership oracle, decidable membership in arbitrary supports, a finite representation of supports, or an executable coding of the class. Countability hypotheses are set-theoretic typeclass assumptions used to obtain enumerations; they are not supplied computable enumerators.

The only explicit decidability interface in the primary family is decidable equality for finite endpoint and absence counts; the main corrupted co-singleton theorem is specialized to `ℕ`, where this is available.

### 1.3 Three distinct contrastive-generation notions

The code exposes three non-equivalent quantifier patterns, and they must not be conflated.

1. **Eventual stream-wise generation** (`ContrastivelyGeneratable`): one generator works for the whole class; for each target and each valid infinite contrastive presentation, there exists a time threshold that may depend on both the target and the presentation.
2. **Uniform distinct-edge-threshold generation** (`UniformlyContrastivelyGeneratableAt`): one fixed number `d` works for every target and every finite crossing history once that history contains at least `d` distinct **unordered** edges.
3. **Target-dependent distinct-edge-threshold generation** (`NonuniformlyContrastivelyGeneratable`): one generator works for the whole class, but the distinct-edge threshold may depend on the target; it is still uniform over all finite crossing histories of that target.

In every generation notion, “fresh” means absent from the vertices already observed in the current input prefix. It does **not** mean distinct from the generator’s own earlier outputs.

## 2. Paper-facing definitions reconstructed from their bodies

### 2.1 Oriented pair geometry and valid contrastive presentations

**`Edge`** is an ordered pair of distinct domain points, consisting of fields `left`, `right`, and a proof that they differ. The orientation is part of the carrier, although crossing is later shown invariant under swapping.  
Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`, bundle line 558.

**`Crosses h e`** holds exactly when one endpoint of `e` belongs to `h` and the other does not:
`(left ∈ h ∧ right ∉ h) ∨ (right ∈ h ∧ left ∉ h)`.  
Source: `.../Geometry.lean`, line 564.

**`CommonCrossing h g e`** means that the same edge crosses both cuts, and **`Incident x e`** means that `x` equals one of the two endpoints.  
Sources: `.../Geometry.lean`, lines 575 and 579.

**`commonVertices h g`** is the set of points incident to at least one edge that crosses both `h` and `g`:
`{x | ∃ e, Crosses h e ∧ Crosses g e ∧ Incident x e}`.  
Source: `.../Geometry.lean`, line 583.

The four region definitions are literal set operations:

* `bothPositive h g = h ∩ g`;
* `hOnly h g = h \ g`;
* `gOnly h g = g \ h`;
* `bothNegative h g = (h ∪ g)ᶜ`.

Sources: `.../Geometry.lean`, lines 619–622.

**`IsContrastivePresentation stream h`** requires two things, in this order:

1. every observed edge crosses `h`; and
2. every point of `h` occurs as an endpoint of at least one observed edge.

There is no requirement that every negative point be observed, no requirement that every crossing edge occur, and no ordering/frequency requirement.  
Source: `.../Geometry.lean`, line 682.

**`NotEliminableFrom g h`** means that there exists one infinite stream which is a valid contrastive presentation for `h` and whose every edge also crosses `g`. This is asymmetric: the coverage condition is only for positive points of `h`.  
Source: `.../Geometry.lean`, line 689.

**`AdmitCommonPresentation h g`** means that one stream is separately a valid contrastive presentation for both `h` and `g`, hence it crosses both cuts and covers every positive point of each support.  
Source: `.../Geometry.lean`, line 768.

The definitions `coveringEdge`, `presentationFromCoverage`, `unionCoveringEdge`, and `commonPresentationFromCoverage` are noncomputable choice constructions. Given a coverage proof, they select common-crossing edges incident to specified points and use a supplied enumeration plus a fallback positive point to assemble an infinite stream.  
Sources: `.../Geometry.lean`, lines 694, 706, 773, and 785.

### 2.2 Inclusion geometry for identification

**`Incomparable h g`** means neither support is contained in the other.  
Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`, line 876.

**`OverlappingCover h g`** means `h ∩ g` is nonempty and `h ∪ g` is the universal set.  
Source: `.../IdentificationGeometry.lean`, line 880.

**`NonEliminabilityContained 𝓗`** is the class-level condition

`∀ h ∈ 𝓗, ∀ g ∈ 𝓗, h ⊆ commonVertices h g → h ⊆ g`.

Thus the antecedent is the geometric common-vertex coverage relation, not the existential predicate `NotEliminableFrom` itself.  
Source: `.../IdentificationGeometry.lean`, line 886.

**`IncomparablePairsOverlap 𝓗`** requires every incomparable ordered pair from the class to have nonempty intersection and universal union.  
Source: `.../IdentificationGeometry.lean`, line 891.

### 2.3 Contrastive identifiers and convergence

A **`ContrastiveIdentifier α`** is a total map taking a history length and a finite edge history to a natural-number index:
`∀ t, (Fin t → Edge α) → ℕ`.  
Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`, line 3159.

**`contrastiveIdentifierOutput I stream t`** runs `I` on the first `t` edges of `stream`.  
Source: `.../IdentifierCharacterization.lean`, line 3163.

**`ContrastivelyIdentifiesFrom I F z stream`** means there exists an index `j` such that `F j = F z`, and there exists a time `T` after which every output is syntactically equal to `j`. The stable index may differ from `z`, and because `j` is chosen after the stream is fixed it may also depend on the presentation; its denoted support must nevertheless be extensionally equal to the target.  
Source: `.../IdentifierCharacterization.lean`, line 3170.

**`ContrastivelyIdentifies I F`** universally quantifies first over every target index `z`, then every edge stream, and asks for `ContrastivelyIdentifiesFrom` only under the implication that the stream is a valid contrastive presentation of `F z`.  
Source: `.../IdentifierCharacterization.lean`, line 3179.

**`ContrastivelyIdentifiable F`** existentially quantifies one semantic contrastive identifier that succeeds for all targets and all valid contrastive presentations.  
Source: `.../IdentifierCharacterization.lean`, line 3187.

**`TextIdentifiable F`** existentially quantifies one imported semantic positive-text identifier that semantically identifies the indexed family. This is an arbitrary function, not an effective machine.  
Source: `.../IdentifierCharacterization.lean`, line 3192.

**`AllProperNontrivial F`** requires, for every index `i`, both a point in `F i` and a point outside `F i`.  
Source: `.../IdentifierCharacterization.lean`, line 3199.

The concrete reduction from a contrastive identifier to a text identifier uses these noncomputable definitions:

* `firstUnseenIndex` chooses the least position in a supplied surjective enumeration whose point is absent from the current positive-text sample;
* `syntheticContrastiveHistory` pairs every positive example in the current history with that one unseen enumerated point;
* `textIdentifierOfContrastive` runs the contrastive identifier on the synthetic edge history.

Sources: `.../IdentifierCharacterization.lean`, lines 3223, 3245, and 3263.

The sufficiency construction uses:

* `chosenTellTale`, an arbitrary selected finite tell-tale for each family index, supplied by the imported finite-tell-tale condition;
* `ContrastiveEligible F T history i`, meaning `i ≤ t`, every vertex in `T i` has appeared in the history, and every observed edge crosses `F i`;
* `contrastiveTellTaleLearner`, which returns the least eligible index, or `0` if no index is eligible.

Sources: `.../IdentifierCharacterization.lean`, lines 3503, 3517, and 3526.

### 2.4 Eventual stream-wise generation, safe closures, and eventual cores

**`seenPrefix history`** is the set of all endpoints occurring in a finite edge history.  
Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`, line 1008.

A **`ContrastiveGenerator α`** is a total map `∀ t, (Fin t → Edge α) → α`, and `generatorOutput` runs it on a stream prefix.  
Sources: `.../GenerationCores.lean`, lines 1027 and 1031.

**`GeneratesFrom G h`** has quantifier order

`∀ stream, IsContrastivePresentation stream h → ∃ T, ∀ t ≥ T, ...`.

The conclusion at each late time is that the output belongs to `h` and is not an endpoint in the first `t` observed edges. The time threshold may depend on the stream.  
Source: `.../GenerationCores.lean`, line 1036.

**`ContrastivelyGeneratable 𝓗`** means one generator works in that sense for every member of the extensional class.  
Source: `.../GenerationCores.lean`, line 1046.

For a finite edge history, **`edgeVersionSpace 𝓗 history`** is the set of class members crossed by every observed edge. **`edgeClosure`** is the intersection of all supports in that version space when it is nonempty, and is defined to be empty when the version space is empty.  
Sources: `.../GenerationCores.lean`, lines 1051 and 1058.

**`InfiniteSafeCores 𝓗`** universally requires that for every class target, every valid contrastive stream for that target, and every time `t`, the corresponding edge closure is infinite.  
Source: `.../GenerationCores.lean`, line 1092.

**`safeCoreGenerator`** classically chooses a point in the current edge closure outside all seen endpoints when such a point exists; otherwise it returns an arbitrary inhabitant of `α`.  
Source: `.../GenerationCores.lean`, line 1104.

**`IsEventualCore 𝓗 core`** requires an injective sequence `core : ℕ → α` such that for every target `h ∈ 𝓗`, only finitely many sequence positions lie outside `h`. Equivalently, each target contains all but finitely many values of the common injective sequence.  
Source: `.../GenerationCores.lean`, line 1141.

**`eventualCoreGenerator`** uses a pairing function. At time `t`, it classically selects some point in the infinite fiber `core(pair(t,k))` outside the finite seen-prefix set. Since the selected sequence index is at least `t`, eventual containment of the core sequence in the target yields eventual correctness.  
Sources: `.../GenerationCores.lean`, lines 1164 and 1180.

### 2.5 Unordered edges, hollow sets, and uniform closure dimension

An **`UnorderedEdge α`** stores a finite set of vertices with cardinality exactly two.  
Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`, line 3824.

`Edge.unordered` forgets orientation. **`UnorderedCrosses h p`** means that among the two vertices of `p` there is at least one member of `h` and at least one nonmember. `UnorderedEdge.orient` classically chooses an orientation.  
Sources: `.../ClosureDimension.lean`, lines 3836, 3842, and 3880.

**`distinctUnorderedEdges history`** is the finite set of unoriented pairs occurring in the history, so repeated observations and reversed orientations are counted once. **`unorderedVertices E`** is the union of the vertex sets of the edges in `E`.  
Sources: `.../ClosureDimension.lean`, lines 3896 and 3903.

For a finite unordered edge set `E`, **`unorderedVersionSpace 𝓗 E`** consists of the class supports crossed by every edge of `E`. **`unorderedClosure 𝓗 E`** is their intersection when that version space is nonempty, and empty otherwise.  
Sources: `.../ClosureDimension.lean`, lines 3929 and 3936.

**`IsContrastivelyHollow 𝓗 E`** requires both that the unordered version space is nonempty and that every point forced positive by all consistent supports is already incident to an edge of `E`.  
Source: `.../ClosureDimension.lean`, line 3958.

**`ContrastiveClosureDimensionAtMost 𝓗 d`** says every finite hollow edge set has at most `d` distinct unordered edges. **`FiniteContrastiveClosureDimension 𝓗`** says some natural-number bound exists.  
Sources: `.../ClosureDimension.lean`, lines 3964 and 3970.

**`ContrastiveClosureDimensionEquals 𝓗 d`** says `d` is an upper bound and is less than or equal to every other natural upper bound. It is a least-bound definition; it does not separately require a hollow witness of size exactly `d`.  
Source: `.../ClosureDimension.lean`, line 3977.

**`UniformlyContrastivelyGeneratesAt G 𝓗 d`** universally quantifies over every target `h ∈ 𝓗`, every length `t`, and every finite edge history. If every edge crosses `h` and the history has at least `d` distinct unordered edges, then `G` must output an element of `h` outside the seen vertices. No infinite-stream presentation or positive-coverage premise appears in this definition.  
Source: `.../ClosureDimension.lean`, line 3986.

**`UniformlyContrastivelyGeneratableAt 𝓗 d`** existentially quantifies such a generator; **`UniformlyContrastivelyGeneratable 𝓗`** existentially quantifies both a natural threshold and a generator.  
Sources: `.../ClosureDimension.lean`, lines 3995 and 4002.

**`IsLeastPositiveUniformThreshold 𝓗 d`** requires `d > 0`, generation at threshold `d`, and minimality among all positive thresholds. Threshold zero is intentionally outside this comparison.  
Source: `.../ClosureDimension.lean`, line 4010.

**`closureDimensionGenerator`** classically chooses a point in the current unordered closure outside the current unordered vertex set, falling back to an arbitrary inhabitant if no such point exists.  
Source: `.../ClosureDimension.lean`, line 4026.

### 2.6 Target-dependent closure thresholds and increasing covers

**`NonuniformlyContrastivelyGenerates G 𝓗`** has quantifier order

`∀ h ∈ 𝓗, ∃ d, ∀ t, ∀ history, ...`.

The threshold may depend on `h` but not on the history. Under a crossing-history premise and at least `d` distinct unordered edges, the output must be valid and unseen.  
Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`, line 5036.

**`NonuniformlyContrastivelyGeneratable 𝓗`** existentially quantifies one generator with that property.  
Source: `.../NonuniformClosure.lean`, line 5045.

For a proposed generator, **`generatorLevel G 𝓗 n`** is the subcollection on which it is uniformly correct at threshold `n+1`.  
Source: `.../NonuniformClosure.lean`, line 5053.

Given an increasing cover with a chosen finite dimension bound for each level, the construction uses:

* `selectedClosureBound`, a classical choice of one bound per level;
* `nonuniformPaddedThreshold bound m = m + bound m + 1`;
* `nonuniformEligibleLevels bound k`, the finite set of levels whose padded threshold is at most the current distinct-edge count `k`;
* `selectedNonuniformLevel`, the maximum eligible level;
* `nonuniformClosureGenerator`, which runs the closure-dimension generator for that maximum level.

Sources: `.../NonuniformClosure.lean`, lines 5117, 5133, 5139, 5159, and 5180.

The imported predicate `IsNondecreasingCover 𝓗 classes` used here means that the sequence of classes is monotone under inclusion and its union is exactly `𝓗`; it remains background because its declaration lies in Paper02.

### 2.7 Hierarchy bridge and witness definitions

**`freshFromContrastiveGuess`** takes an indexed family all of whose members are infinite and a contrastive identifier. It classically selects, from the support named by the current guess, a point outside the finite seen endpoint set.  
Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`, line 5329.

**`freshFromTextGuess`** is the analogous construction for positive-text histories.  
Source: `.../Hierarchy.lean`, line 5379.

**`IsSharedPresentation stream family`** says the same contrastive stream is valid for every support in a finite family.  
Source: `.../Hierarchy.lean`, line 5539.

**`IsFiniteFamilyIntersection family core`** says a finite set `core` is extensionally exactly the intersection of the finite family:
`x ∈ core ↔ ∀ h ∈ family, x ∈ h`.  
Source: `.../Hierarchy.lean`, line 5544.

The **punctured witness** uses `puncturedCore(m)=2m`. Index `0` denotes the whole even-number range, and index `m+1` denotes that even range with the point `2m` removed.  
Sources: `.../Hierarchy.lean`, lines 5610 and 5617.

The **disjoint witness** uses the even and odd natural numbers. Index `0` denotes the even support; every positive index denotes the odd support. The shared edge stream pairs `2n` with `2n+1`. A concrete text identifier returns `0` or `1` based on whether the first positive example is even, with default `0` at empty history.  
Sources: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`, lines 5770, 5773, 5798, 5809, and 5849.

### 2.8 Corrupted presentations and corrupted identification

**`IsKCorruptedTextPresentation k stream h`** requires:

1. the set of occurrence indices at which `stream n ∉ h` is finite;
2. its finite cardinality is at most `k`; and
3. every point of `h` occurs somewhere in the stream.

The budget counts bad occurrences, not distinct bad values.  
Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`, line 5960.

**`IsKCorruptedContrastivePresentation k stream h`** analogously counts occurrence indices whose edge does not cross `h`, and still requires every positive point of `h` to occur as an endpoint somewhere.  
Source: `.../CorruptedPresentations.lean`, line 5968.

**`KTextIdentifiesFrom`** and **`KContrastivelyIdentifiesFrom`** are implications from validity of one corrupted presentation to eventual stabilization at an index denoting the target. **`KTextIdentifiable k F`** and **`KContrastivelyIdentifiable k F`** existentially quantify one identifier for all targets and all streams at the fixed budget.  
Sources: `.../CorruptedPresentations.lean`, lines 5977, 5986, 5993, and 6001.

**`FinitelyCorruptionContrastivelyIdentifiable F`** has the stronger quantifier order

`∃ I, ∀ k, ∀ z, ∀ stream, ...`.

The same single identifier must work for every finite corruption budget; it is not a family of identifiers indexed by `k`.  
Source: `.../CorruptedPresentations.lean`, line 6008.

**`coSingletonSupport s`** is the complement of the singleton `{s}`, represented as `{x | x ≠ s}`. **`coSingletonFamily`** indexes this support by its missing natural number.  
Sources: `.../CorruptedPresentations.lean`, lines 6015 and 6018.

### 2.9 Absence-count identifier

For a finite edge history, **`seenEndpoints`** is the finite set of observed endpoints. **`absenceCount history x`** is the number of observation positions whose edge is not incident to `x`; **`streamAbsenceCount stream x t`** is the same count on the first `t` observations of a stream.  
Sources: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`, lines 6105, 6111, and 6116.

**`absenceCountIdentifier`** chooses, among currently seen endpoints, an endpoint minimizing the absence count; ties are resolved by arbitrary classical choice. If no endpoint has been seen, it returns `0`.  
Source: `.../AbsenceCount.lean`, line 6364.

The private `competitorThreshold` chooses, for each false center, a time after which its absence count exceeds the corruption budget. The theorem proving the final identifier takes a maximum over the finitely many candidates seen in the first `k+1` observations.  
Source: `.../AbsenceCount.lean`, line 6442.

`example67History` is the six-edge history
`(3,0),(3,1),(0,4),(3,2),(3,4),(3,5)` in oriented form.  
Source: `.../AbsenceCount.lean`, line 6554.

### 2.10 The block-family reverse separation

For each budget `k`:

* **`robustCommonCore`** is the set of multiples of four;
* **`robustBlockPoint i r`** is `4 * pair(i,r) + 2` for `r : Fin(k+1)`;
* **`robustBlock k i`** is the finite set of the `k+1` such points;
* **`robustBlockSupport k i`** is the common core union the `i`-th block;
* **`robustBlockFamily k`** indexes these supports by `i`.

Sources: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`, lines 6649–6666.

**`CompleteRobustBlock k i history`** says every point in the `i`-th block occurs in the finite text history. **`robustBlockTextIdentifier k`** chooses any index whose full block has been observed, defaulting to zero if none exists.  
Sources: `.../CorruptedIncomparability.lean`, lines 6789 and 6795.

The shared contrastive stream is built from two edge types:

* `robustCoreEdge n = (4n,4n+1)`, pairing a common-positive point with a common-negative point;
* `robustBlockEdge k n`, pairing corresponding cycling points of blocks `0` and `1`.

`robustSharedStream` interleaves those types through the natural pairing/unpairing functions.  
Sources: `.../CorruptedIncomparability.lean`, lines 6917, 6923, and 6933.

### 2.11 Defect numbers and forced violation infima

**`positiveDefectSet h g`** is `h \ commonVertices h g`: the positive points of `h` not incident to any edge crossing both cuts.  
Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`, line 7145.

**`defectNumber h g`** is the extended-natural cardinality of that set, using `ℕ∞` so infinite defects have value `⊤`.  
Source: `.../DefectInfimum.lean`, line 7149.

For a stream, **`wrongCutViolationTimes g stream`** is the set of indices where the observed edge fails to cross `g`, and **`wrongCutViolationCount`** is its extended-natural cardinality.  
Sources: `.../DefectInfimum.lean`, lines 7153 and 7158.

**`cleanWrongCutViolationCounts h g`** is the set of all extended-natural wrong-cut counts achieved by streams that are clean valid contrastive presentations of `h`. **`forcedWrongCutViolationInfimum h g`** is the infimum of that set.  
Sources: `.../DefectInfimum.lean`, lines 7164 and 7171.

**`ProperNontrivialSupport h`** means `h` and its complement are both nonempty.  
Source: `.../DefectInfimum.lean`, line 7176.

The remaining definitions in this module are witness constructors:

* `defectIncidentTime` chooses one presentation time incident to a given defect point;
* `defectToViolationTime` maps each defect point to such a wrong-cut time;
* `positiveNondefectSet = h ∩ commonVertices h g`;
* `commonEdgeForNondefect` chooses a common-crossing edge incident to a nondefect positive;
* `edgeForDefect` pairs a defect positive with a fixed `h`-negative point;
* `edgeForPositive` pairs any `h`-positive with a fixed `h`-negative point.

Sources: `.../DefectInfimum.lean`, lines 7230, 7257, 7365, 7383, 7395, and 7419.

## 3. Primary and top-level claims

This section reconstructs the strongest public claims. Each entry preserves the displayed assumptions and quantifier structure, then audits access, possible vacuity, and where the hard content sits.

### 3.1 Common-crossing geometry

#### 3.1.1 Coverage by common-crossing vertices

```lean
theorem theorem_4_3
    (h g : Set α) :
    h ⊆ commonVertices h g ↔
      ((bothPositive h g).Nonempty → (bothNegative h g).Nonempty) ∧
      ((hOnly h g).Nonempty → (gOnly h g).Nonempty)
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`, bundle line 625.

**Exact reconstruction.** For arbitrary sets `h,g ⊆ α`, every point of `h` is incident to an edge that crosses both cuts if and only if both of the following implications hold:

1. if `h ∩ g` is nonempty, then the complement of `h ∪ g` is nonempty;
2. if `h \ g` is nonempty, then `g \ h` is nonempty.

The statement is asymmetric because only `h` is required to be covered. There are no countability, finiteness, nonemptiness, properness, decidability, or representation assumptions.

**Vacuity audit.** Each region condition is an implication. If `h ∩ g` is empty, the first condition is automatic; if `h \ g` is empty, the second is automatic. This is not circular: the right side is a direct region-existence characterization of the left side. For `h=∅`, the left side and both implications are vacuously true.

**Difficulty preservation.** The full set-theoretic combinatorial content is in the theorem statement itself. No helper premise assumes common-crossing coverage or supplies the desired edge family.

#### 3.1.2 Non-eliminability versus common-vertex coverage

```lean
theorem proposition_4_2
    {h g : Set α} (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α) (henum : h ⊆ Set.range enumeration) :
    NotEliminableFrom g h ↔ h ⊆ commonVertices h g
```

Source: `.../Geometry.lean`, line 746.

**Exact reconstruction.** Fix a point `x₀ ∈ h` and a supplied sequence whose range covers `h`. Then there exists a valid contrastive presentation of `h` all of whose edges also cross `g` if and only if every positive point of `h` lies in the common-crossing vertex set.

**Explicit access model.** The reverse implication receives rather than constructs:

* a concrete fallback point `x₀` in `h`;
* a concrete enumeration `ℕ → α` whose range covers `h`;
* the coverage proof `h ⊆ commonVertices h g`.

It then uses classical choice to select one common-crossing edge per positive point. There is no computability or decidable-membership guarantee. The theorem does not merely assume countability abstractly; its type explicitly supplies the enumeration and a positive point.

**Vacuity/nonvacuity.** The assumptions force `h` to be nonempty and at most countably coverable by the supplied sequence. Consequently this biconditional does not cover the empty-support case. The forward implication does not need those witnesses logically, but the theorem packages both directions under the same assumptions.

**Difficulty preservation.** The geometric equivalence is substantive, but the countability/listing step is delegated to an explicit argument, and the constructed stream is information-theoretic/noncomputable.

#### 3.1.3 One presentation valid for both supports

```lean
theorem lemma_4_4
    {h g : Set α} (x₀ : α) (hx₀ : x₀ ∈ h ∪ g)
    (enumeration : ℕ → α)
    (henum : h ∪ g ⊆ Set.range enumeration) :
    AdmitCommonPresentation h g ↔
      h ∪ g ⊆ commonVertices h g
```

Source: `.../Geometry.lean`, line 825.

**Exact reconstruction.** Given a point in `h ∪ g` and a supplied sequence covering the union, one stream is a valid contrastive presentation for both supports if and only if every point in their union is incident to some common-crossing edge.

**Access and vacuity.** The hypotheses force `h ∪ g` to be nonempty and countably covered. The reverse implication uses classical choices and the supplied enumeration. The common stream must cover positives of both supports, which is stronger than `NotEliminableFrom g h`.

**Difficulty preservation.** The exact common-presentation obstruction is stated, but the representation and selection mechanisms are supplied or classical rather than effective.

### 3.2 Geometric class condition

```lean
theorem theorem_4_7_geometric_equivalence
    (𝓗 : Set (Set α)) :
    NonEliminabilityContained 𝓗 ↔
      IncomparablePairsOverlap 𝓗
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`, line 974.

**Exact reconstruction.** For an arbitrary extensional class of supports, the following are equivalent:

* whenever `h,g` are class members and every positive point of `h` is a common-crossing vertex for `h,g`, then `h ⊆ g`;
* whenever `h,g` are incomparable class members, their intersection is nonempty and their union is universal.

No countability, nonemptiness, properness, indexing, or effectivity assumptions occur.

**Important interface qualification.** The left side uses the geometric antecedent `h ⊆ commonVertices h g`; it does not literally quantify `NotEliminableFrom g h`. Relating those predicates requires the separate nonempty/enumeration assumptions of `proposition_4_2`. Thus this theorem is an exact equivalence for the **defined geometric relation**, not an unconditional equivalence for arbitrary existential presentations over arbitrary supports.

**Vacuity.** If the class has no incomparable pairs, `IncomparablePairsOverlap` is automatic. The equivalent containment condition can likewise be automatic. This is a legitimate structural edge case, not circularity.

**Difficulty preservation.** The theorem states the full region-geometry equivalence and delegates only elementary region facts to helpers.

### 3.3 Safe-core and eventual-core sufficient conditions for eventual generation

#### 3.3.1 Infinite safe closures

```lean
theorem proposition_5_8 [Nonempty α]
    (𝓗 : Set (Set α)) (hsafe : InfiniteSafeCores 𝓗) :
    ContrastivelyGeneratable 𝓗
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`, line 1126.

**Exact reconstruction.** If `α` is inhabited and, for every target in `𝓗`, every valid contrastive presentation of that target, and every time, the intersection of all class hypotheses consistent with the observed edges is infinite, then there exists one generator that is correct and unseen at every time on every valid presentation. Formally the conclusion only asks for an eventual threshold, and the constructed witness satisfies it with threshold `0`.

**Access model.** The generator has semantic access to the entire class and current version-space intersection. It classically chooses a fresh point from that infinite intersection. It has no oracle interface, membership-decision procedure, finite representation, or computability property. `[Nonempty α]` is used only for arbitrary output on histories where the choice condition fails.

**Vacuity/circularity.** `InfiniteSafeCores` is extremely strong: it already asserts, at each valid prefix, an infinite set of points common to every consistent target. Since the seen endpoint set is finite, the existence of a correct fresh output is nearly immediate. The hypothesis does not literally supply a generator, so it is not logically circular, but it contains essentially all hard semantic content. If a target has no valid presentation, its universally quantified clause in `InfiniteSafeCores` and its generation obligation are both vacuous.

**Difficulty preservation.** The theorem reduces generation to the strong safe-core condition; it does not characterize when that condition holds.

#### 3.3.2 A supplied eventual common core

```lean
theorem proposition_5_11
    (𝓗 : Set (Set α)) (core : ℕ → α)
    (hcore : IsEventualCore 𝓗 core) :
    ContrastivelyGeneratable 𝓗
```

Source: `.../GenerationCores.lean`, line 1201.

**Exact reconstruction.** Suppose a specific injective sequence is supplied and every target in `𝓗` contains all but finitely many terms of that sequence. Then one semantic generator works eventually for every target and every valid contrastive presentation.

**Quantifier and access details.** The sequence is an explicit input to the theorem. The finite exceptional set may depend on the target. The generator uses pairing and classical choice to select, at each time, a sufficiently high-index sequence value outside the finitely many observed vertices. It does not need to inspect the target, the presentation-validity proof, or any membership oracle.

**Vacuity/circularity.** The premise does not state generation, but it supplies a universal tail of candidate outputs already lying in every target, so the main hard step is the existence of such a sequence. No `Nonempty α` assumption is needed because an injective map `ℕ → α` already implies an infinite inhabited domain.

**Difficulty preservation.** The theorem is a semantic reduction from an explicit strong witness to generation; the construction of the witness is entirely outside the theorem.

### 3.4 Contrastive identification characterization

#### 3.4.1 Contrastive identification implies text identification

```lean
theorem lemma_4_6_inclusion
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F → TextIdentifiable F
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`, line 3355.

**Exact reconstruction.** On an inhabited, countable, infinite domain, if every indexed support is nonempty and has a nonempty complement, then existence of a semantic contrastive identifier implies existence of a semantic exact-positive-text identifier.

**Access model.** Countability is used to choose a surjection `ℕ → α`; no enumeration is supplied in the theorem type, and no computability is asserted. The text identifier is noncomputable. It simulates the contrastive identifier by pairing every observed positive text point with the least enumerated point absent from the whole current text prefix. Properness guarantees a complement point for the target, while infinitude guarantees some currently unseen enumerated point at every finite stage.

**Vacuity.** `AllProperNontrivial` removes empty and universal targets, avoiding vacuous presentations and guaranteeing a genuine crossing partner. The theorem is one-way only.

**Difficulty preservation.** The reduction is substantive at the semantic level, but no effective transformation is claimed. The hard stabilization fact is exposed through helper statements about the least unseen enumeration index.

#### 3.4.2 Necessity of the geometric relation

```lean
theorem contrastiveIdentifiable_nonEliminabilityContained
    [Nonempty α] [Countable α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F)
    (hCtr : ContrastivelyIdentifiable F) :
    NonEliminabilityContained (Set.range F)
```

Source: `.../IdentifierCharacterization.lean`, line 3451.

**Exact reconstruction.** For a countable inhabited domain and a family of proper nontrivial supports, contrastive identifiability implies: for any two supports in the range of the indexed family, if the first is covered by common-crossing vertices with the second, then the first is contained in the second.

**Access model.** The available helper interfaces obtain a surjective domain enumeration from countability and a positive point from properness, then connect these to the common-presentation criterion. The theorem itself assumes only existence of an arbitrary semantic identifier.

**Vacuity and specialization.** Because the conclusion is over `Set.range F`, duplicate indices are collapsed extensionally. The theorem does not require `Infinite α`; finite countable domains are allowed provided every support is proper and nontrivial.

**Difficulty preservation.** The common-stream indistinguishability argument is stated through the helper `commonPresentation_for_noncontained` and `lemma_4_4`; the hard geometric link is not assumed as the conclusion.

#### 3.4.3 Sufficient link conditions and least-eligible learner

```lean
theorem contrastiveTellTaleLearner_identifies
    {F : GenLimit.Generic.LanguageFamily α}
    (hTell : GenLimit.Angluin.ConditionTwo F)
    (hrel : NonEliminabilityContained (Set.range F)) :
    ContrastivelyIdentifies
      (contrastiveTellTaleLearner F (chosenTellTale hTell)) F
```

Source: `.../IdentifierCharacterization.lean`, line 3679.

**Exact reconstruction.** If every indexed support has a finite Angluin tell-tale and the geometric non-eliminability containment condition holds on the range, then the classically chosen least-eligible contrastive learner semantically identifies the whole indexed family.

**Access model.** The finite tell-tales are existentially supplied by `ConditionTwo` and selected by classical choice. The eligibility test semantically evaluates whether every tell-tale vertex has appeared and whether every observed edge crosses each candidate support. No uniform enumeration, decision procedure, or computability is stated. The learner performs a bounded least-index search in logic, not an effective one.

**Vacuity/circularity.** `ConditionTwo` is not the desired contrastive conclusion, but it encodes the hard finite distinguishing content for positive-text identification. `hrel` is the substantive geometry needed to eliminate candidates not containing the target. Together they are exactly the two link conditions from which the learner is bookkeeping. If a family member has no valid contrastive presentation, identification for that member is vacuous; the theorem imposes no separate properness assumption.

```lean
theorem contrastivelyIdentifiable_of_text_and_nonEliminability
    [Nonempty α] [Countable α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hText : TextIdentifiable F)
    (hrel : NonEliminabilityContained (Set.range F)) :
    ContrastivelyIdentifiable F
```

Source: `.../IdentifierCharacterization.lean`, line 3739.

**Exact reconstruction.** On a nonempty countable domain, semantic text identifiability plus the geometric containment condition implies semantic contrastive identifiability. The imported locking/tell-tale bridge converts `hText` to finite tell-tales, after which the preceding least-eligible learner applies.

**Difficulty preservation.** The Paper28 statement delegates the hard text-identification-to-tell-tale necessity theorem to imported background. It does not assume the desired contrastive identifier, but it does rely on a strong semantic characterization result outside the primary module.

#### 3.4.4 Two equivalent top-level formulations

```lean
theorem theorem_4_7_identifier_equivalence
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F ↔
      TextIdentifiable F ∧
        NonEliminabilityContained (Set.range F)
```

Source: `.../IdentifierCharacterization.lean`, line 3755.

**Exact reconstruction.** Under an inhabited, countable, infinite domain and proper/nontriviality of every indexed support, contrastive identifiability is equivalent to the conjunction of semantic text identifiability and the geometric common-vertex containment condition on the extensional range.

**Assumptions and access.** All identifiers are arbitrary semantic functions. Countability is not an effective representation. No oracle is given. Properness is uniform over all indices. Duplicates in `F` are allowed; successful convergence is to one stable index denoting the target support.

**Vacuity.** Properness rules out the most immediate empty/universal-target vacuity. The right-hand geometric condition is still formulated using `commonVertices`, not directly `NotEliminableFrom`; under these hypotheses, countability and nonemptiness make the separate geometric/presentation link available.

**Difficulty preservation.** This is a genuine characterization at the semantic interface. Its sufficiency depends on imported finite-tell-tale necessity, and its necessity uses the synthetic-text reduction and common-presentation geometry. No effective characterization is preserved.

```lean
theorem theorem_4_7
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F ↔
      TextIdentifiable F ∧
        IncomparablePairsOverlap (Set.range F)
```

Source: `.../IdentifierCharacterization.lean`, line 3776.

**Exact reconstruction.** Under the same hypotheses, contrastive identifiability is equivalent to text identifiability plus the requirement that every incomparable pair of supports in the range has nonempty overlap and covers the whole domain.

**Difficulty preservation.** This statement combines the preceding identifier equivalence with the independent geometric equivalence. It is the cleanest top-level characterization in the bundle, but remains semantic and noneffective.

### 3.5 Uniform generation and contrastive closure dimension

#### 3.5.1 Exact quantitative equivalence

```lean
theorem theorem_5_4_quantitative
    [Nonempty α] (𝓗 : Set (Set α)) (d : ℕ) :
    UniformlyContrastivelyGeneratableAt 𝓗 (d + 1) ↔
      ContrastiveClosureDimensionAtMost 𝓗 d
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`, line 4215.

**Exact reconstruction.** On any inhabited domain, there exists one generator that is correct and unseen for every class target and every finite crossing history with at least `d+1` distinct unordered edges if and only if every finite hollow unordered-edge set has at most `d` edges.

**Access model.** The sufficiency generator uses the extensional class, its unordered version-space intersection, and classical choice. No countability of `α` or of the class is required, and no representation or membership oracle is supplied. Orientation of unordered edges in the lower bound is chosen noncomputably.

**Vacuity.** If no finite crossing history reaches `d+1` distinct edges for a target, that target’s generation obligation at this threshold is vacuous. If no hollow edge sets exist, the dimension bound is vacuous. The theorem aligns these edge cases. `[Nonempty α]` is enough to define arbitrary fallback outputs; it does not assert the existence of any edge, so domains with fewer than two points are permitted.

**Difficulty preservation.** This theorem states the full sharp combinatorial equivalence. The sufficiency hinge is the contrapositive fact that more than `d` edges cannot be hollow, so the closure contains an unseen point. The necessity hinge is the adversarial use of a hollow set. Neither hinge is assumed in the theorem.

#### 3.5.2 Qualitative and sharp forms

```lean
theorem theorem_5_4
    [Nonempty α] (𝓗 : Set (Set α)) :
    UniformlyContrastivelyGeneratable 𝓗 ↔
      FiniteContrastiveClosureDimension 𝓗
```

Source: `.../ClosureDimension.lean`, line 4228.

**Exact reconstruction.** Existence of some finite distinct-edge threshold and some semantic uniform generator is equivalent to existence of some natural upper bound on sizes of hollow finite edge sets.

**Threshold detail.** `UniformlyContrastivelyGeneratable` permits threshold `0`, while the quantitative theorem is phrased at `d+1`. In the forward direction, a generator at threshold `d` is also valid at threshold `d+1`, yielding a dimension bound `d`. Thus the qualitative equivalence does not identify the least threshold by itself.

```lean
theorem theorem_5_4_sharp_sample_complexity
    [Nonempty α] {𝓗 : Set (Set α)} {d : ℕ}
    (hdim : ContrastiveClosureDimensionEquals 𝓗 d) :
    IsLeastPositiveUniformThreshold 𝓗 (d + 1)
```

Source: `.../ClosureDimension.lean`, line 4245.

**Exact reconstruction.** If `d` is the least natural upper bound on cardinalities of hollow sets, then `d+1` is the least **positive** distinct-edge threshold at which a uniform generator exists.

**Vacuity/representation.** The exact-dimension premise is a least-upper-bound predicate and does not explicitly provide a hollow witness of size `d`. Natural-number minimality is enough for the threshold result. Restricting to positive thresholds avoids comparing against threshold zero.

```lean
theorem hollow_cardinality_lower_bound
    {𝓗 : Set (Set α)} {E : Finset (UnorderedEdge α)}
    (hollow : IsContrastivelyHollow 𝓗 E) :
    ¬UniformlyContrastivelyGeneratableAt 𝓗 E.card
```

Source: `.../ClosureDimension.lean`, line 4264.

**Exact reconstruction.** Any particular hollow finite edge set of size `m` rules out every generator at threshold `m`. This is a concrete witness lower bound, with no inhabitance assumption because it is a negation of existence.

### 3.6 Target-dependent thresholds and increasing finite-dimension covers

```lean
theorem theorem_5_5_necessity
    {𝓗 : Set (Set α)}
    (hNonuniform : NonuniformlyContrastivelyGeneratable 𝓗) :
    ∃ classes : ℕ → Set (Set α),
      GenLimit.LiRamanTewari.IsNondecreasingCover 𝓗 classes ∧
      ∀ n, FiniteContrastiveClosureDimension (classes n)
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`, line 5098.

**Exact reconstruction.** If one generator has a target-dependent finite distinct-edge threshold for every target in `𝓗`, then `𝓗` can be written as an increasing union of subcollections, each with finite contrastive closure dimension.

**Access and difficulty.** The cover is constructed from the given generator’s performance levels. No nonempty-domain assumption is needed for this direction. The hard quantitative theorem is invoked level by level; it is not re-assumed as a cover property.

```lean
theorem theorem_5_5_sufficiency
    [Nonempty α] {𝓗 : Set (Set α)}
    {classes : ℕ → Set (Set α)}
    (hcover :
      GenLimit.LiRamanTewari.IsNondecreasingCover 𝓗 classes)
    (hdim : ∀ n,
      FiniteContrastiveClosureDimension (classes n)) :
    NonuniformlyContrastivelyGeneratable 𝓗
```

Source: `.../NonuniformClosure.lean`, line 5212.

**Exact reconstruction.** On an inhabited domain, an increasing cover by subcollections each having some finite contrastive closure-dimension bound yields one generator with a target-dependent finite threshold.

**Access model.** The theorem receives only existential finiteness at each level, then classically chooses one numerical bound per level. At a finite history it chooses the maximum level whose padded threshold has been reached and runs that level’s noncomputable closure generator. There is no computable sequence of bounds or effective test of level membership.

**Vacuity/circularity.** The premise does not supply a generator but does supply the exact structural decomposition from which one is assembled. The padding `m + bound(m) + 1` is substantive bookkeeping ensuring only finitely many levels can be active and that a maximum exists.

```lean
theorem theorem_5_5
    [Nonempty α] (𝓗 : Set (Set α)) :
    NonuniformlyContrastivelyGeneratable 𝓗 ↔
      ∃ classes : ℕ → Set (Set α),
        GenLimit.LiRamanTewari.IsNondecreasingCover 𝓗 classes ∧
        ∀ n, FiniteContrastiveClosureDimension (classes n)
```

Source: `.../NonuniformClosure.lean`, line 5274.

**Exact reconstruction.** Target-dependent finite distinct-edge-threshold generation is exactly increasing-union decomposability into finite-contrastive-closure-dimension subcollections.

**Difficulty preservation.** This is a genuine structural characterization at a noneffective semantic interface. It is not the same as the earlier eventual stream-wise `ContrastivelyGeneratable` notion.

### 3.7 Hierarchy inclusions and obstruction

#### 3.7.1 Identification-to-generation inclusions

```lean
theorem contrastiveIdentification_implies_generation
    (F : Generic.LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite) :
    ContrastivelyIdentifiable F →
      ContrastivelyGeneratable (Set.range F)
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`, line 5354.

**Exact reconstruction.** If every indexed support is infinite, semantic contrastive identification implies eventual stream-wise contrastive generation of the extensional range.

**Access model.** Once the identifier stabilizes, the generator classically chooses an unseen point from the currently guessed infinite support. No countability or effectiveness is assumed.

**Difficulty preservation.** The inclusion is direct but depends essentially on infinitude to guarantee a point outside the finite observed endpoint set.

```lean
theorem textIdentification_implies_generation
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    TextIdentifiable F →
      GenLimit.LiRamanTewari.GeneratableInLimit (Set.range F)
```

Source: `.../Hierarchy.lean`, line 5405.

This is the analogous semantic inclusion for ordinary positive-text generation. Its conclusion belongs to an imported Paper02 interface and is background to the contrastive hierarchy, not a new definition of text generation in Paper28.

#### 3.7.2 Finite-family common-presentation obstruction

```lean
theorem proposition_5_12
    {𝓗 : Set (Set α)} {family : Finset (Set α)}
    {core : Finset α} {stream : ℕ → Edge α}
    (hfamilyNonempty : family.Nonempty)
    (hfamilyClass : ∀ h, h ∈ family → h ∈ 𝓗)
    (hshared : IsSharedPresentation stream family)
    (hcore : IsFiniteFamilyIntersection family core) :
    ¬ContrastivelyGeneratable 𝓗
```

Source: `.../Hierarchy.lean`, line 5551.

**Exact reconstruction.** Suppose a nonempty finite subfamily of `𝓗` has one stream valid for every member, and suppose its exact intersection is represented by a finite set `core`. Then no single generator can eventually generate correctly and freshly for all targets in `𝓗`.

**Why the assumptions matter.** The common stream makes the generator’s input identical across all selected targets. Eventual correctness for every target forces a late output into their intersection. Finiteness and exact representation of that intersection ensure that all intersection points eventually appear as endpoints in the shared stream, contradicting freshness.

**Vacuity/circularity.** The hypotheses are strong and supply the indistinguishability witness, but they do not state non-generatability. The finite intersection is essential; an infinite common core would not yield the same contradiction. The finite family must be nonempty so that one target can supply the presentation used to show the core is eventually seen.

**Difficulty preservation.** This is a clean obstruction lemma. The hard application-specific work is constructing the shared presentation and finite exact intersection.

### 3.8 Concrete hierarchy witnesses

```lean
theorem theorem_5_13_5_14_punctured_witness :
    ContrastivelyGeneratable (Set.range puncturedFamily) ∧
      ¬TextIdentifiable puncturedFamily ∧
      ¬ContrastivelyIdentifiable puncturedFamily
```

Source: `.../Hierarchy.lean`, line 5718.

**Exact reconstruction.** The indexed family consisting of the even-number spine and all one-point punctures of that spine is eventually contrastively generatable, but is neither semantically text-identifiable nor semantically contrastively identifiable.

**Mechanisms visible at the interface.** Contrastive generation is witnessed by the supplied even sequence as an eventual core. Failure of text identification is derived from failure of finite tell-tale existence for the unpunctured support. Failure of contrastive identification follows from the contrastive-to-text inclusion after the code separately establishes proper/nontriviality.

**Difficulty preservation.** This is a concrete theorem-level separation, not a universally quantified class-inclusion theorem. The negative text result relies on an imported semantic locking/tell-tale necessity bridge.

```lean
theorem theorem_5_13_5_14_disjoint_witness :
    TextIdentifiable disjointFamily ∧
      GenLimit.LiRamanTewari.GeneratableInLimit
        (Set.range disjointFamily) ∧
      ¬ContrastivelyGeneratable (Set.range disjointFamily)
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`, line 5923.

**Exact reconstruction.** The family with the even support at index zero and the odd support at every positive index is semantically text-identifiable and text-generatable, but its extensional range is not eventually contrastively generatable.

**Mechanisms.** The first positive text point separates even from odd. The edge stream `(2n,2n+1)` is a valid common contrastive presentation for both disjoint supports. Their intersection is the empty finite set, so `proposition_5_12` applies.

**Difficulty preservation.** The witness is fully explicit. It proves the stated separations for this family; no more general hierarchy theorem is encoded in this declaration.

### 3.9 Corrupted text and contrastive identification

#### 3.9.1 One text corruption defeats the co-singleton family

```lean
theorem theorem_6_5 :
    ¬KTextIdentifiable 1 coSingletonFamily
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`, line 6049.

**Exact reconstruction.** There is no single semantic text identifier that, for every missing point `s` and every text stream with at most one out-of-support occurrence while covering all of `ℕ \ {s}`, stabilizes to an index denoting `ℕ \ {s}`.

**Nonvacuity.** The identity stream is explicitly shown to be a valid one-corrupted text presentation for every co-singleton target. Therefore the negative theorem is not obtained from absence of legal presentations. The same input stream would force the learner to converge to extensionally different targets.

**Difficulty preservation.** This is a direct indistinguishability obstruction and makes no effectiveness claim.

#### 3.9.2 One identifier handles every finite contrastive corruption budget

```lean
theorem theorem_6_6 :
    FinitelyCorruptionContrastivelyIdentifiable
      coSingletonFamily
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`, line 6482.

**Exact reconstruction.** There exists one contrastive identifier `I` such that for every natural corruption budget `k`, every missing point `s`, and every `k`-corrupted contrastive presentation of `ℕ \ {s}`, `I` eventually stabilizes to an index denoting that co-singleton support. Because the family is indexed by the missing point, the constructed identifier in fact stabilizes to `s`.

**Access model and tie-breaking.** The same budget-independent identifier minimizes absence count among observed endpoints. It is noncomputable because a minimizer is chosen classically; no budget is passed to the identifier. The displayed helper statements use the budget only to bound the true center and eliminate false competitors. Ties may be broken arbitrarily.

**Substantive helper content.** The true center’s absence count is always at most `k`; every false center is absent from infinitely many edges; any candidate with absence count at most `k` must have appeared in the first `k+1` observations. This reduces eventual competition to a finite set, over which one maximum stabilization time exists.

**Vacuity.** The implication-based corrupted-identification definition is potentially vacuous for impossible streams, but this theorem’s mechanism addresses arbitrary streams satisfying the displayed nonempty coverage and finite-corruption premises.

**Difficulty preservation.** The hard infinite-versus-bounded absence argument is stated in dedicated helper theorems rather than assumed.

#### 3.9.3 Two-way incomparability at every positive budget

```lean
theorem theorem_6_8
    (k : ℕ) (hk : 1 ≤ k) :
    (KContrastivelyIdentifiable k coSingletonFamily ∧
      ¬KTextIdentifiable k coSingletonFamily) ∧
    (KTextIdentifiable k (robustBlockFamily k) ∧
      ¬KContrastivelyIdentifiable k (robustBlockFamily k))
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`, line 7090.

**Exact reconstruction.** For every positive integer budget `k`:

1. the fixed co-singleton family is contrastively identifiable under `k` corruptions but not text-identifiable under `k` corruptions; and
2. the budget-dependent block family with blocks of size `k+1` is text-identifiable under `k` corruptions but not contrastively identifiable under `k` corruptions.

**Quantifier qualification.** The reverse-separation family depends on `k`; the theorem does not exhibit one fixed family working simultaneously for all budgets in both directions. The co-singleton positive result uses the stronger budget-independent identifier from `theorem_6_6`. The assumption `1 ≤ k` is needed for monotonic transfer of the one-corruption text impossibility; the block-side declarations themselves are stated for all `k`.

**Block-side access and nonvacuity.** The text identifier classically chooses any fully observed block. A false block has `k+1` distinct points outside the target, so observing it completely would exceed the budget. The target block is fully covered and therefore eventually complete. Contrastive non-identifiability uses a clean shared stream for two distinct supports; clean presentations are valid at every corruption budget.

**Difficulty preservation.** The theorem contains explicit arithmetic supports, explicit block cardinality, an explicit text strategy, and an explicit common contrastive stream. It is a genuine concrete incomparability result at the semantic level.

### 3.10 Defect number as a forced wrong-cut infimum

#### 3.10.1 Exact extended-natural equality

```lean
theorem proposition_6_3_defect_eq_forced_wrong_cut_infimum
    [Countable α] {h g : Set α}
    (_hDistinct : h ≠ g)
    (hh : ProperNontrivialSupport h)
    (hg : ProperNontrivialSupport g) :
    forcedWrongCutViolationInfimum h g =
      defectNumber h g
```

Source: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`, line 7573.

**Exact reconstruction.** On a countable domain, for two distinct proper nontrivial supports, the infimum—taken in extended natural numbers—of the numbers of `g`-noncrossing observation occurrences over all clean valid contrastive presentations of `h` equals the extended cardinality of `h \ commonVertices h g`.

**Lower bound.** Every clean presentation must show every positive defect point as an endpoint. A crossing edge has a unique positive endpoint relative to `h`, so choosing one incident time per defect gives an injection from defect points to wrong-cut times. This yields the extended-cardinal lower bound, including infinite defects.

**Upper bound.** When the defect set is finite, the code constructs one presentation using exactly one wrong-cut edge per defect and common-crossing filler edges for all nondefect positives. When the defect set is infinite, the lower bound forces every attainable count and hence the infimum to be `⊤`.

**Access model.** Countability provides set-theoretic enumerations of positive supports. Witness edges and enumerations are chosen classically. No computability is claimed.

**Statement-level redundancy.** The distinctness hypothesis does not enter the conclusion, and the separately stated lower-bound and exact-attainment helpers are uniform in `h,g` without any distinctness premise. Those helper interfaces appear sufficient to derive the equality, so the extra assumption appears unnecessary at the statement level. Both properness assumptions do enter the finite-defect attainment interface, which needs positive, negative, and common-crossing filler points.

**Vacuity.** The infimum definition alone could face an empty attainable-count set. Here `Countable α` and properness of `h` imply existence of a clean presentation, so the set is explicitly nonempty before the infimum theorem is applied.

**Difficulty preservation.** The theorem states the full equality in `ℕ∞`; it does not weaken infinite cases to a finite approximation. The essential injection and exact finite construction are explicit helper statements.

#### 3.10.2 Zero defect and non-eliminability

```lean
theorem proposition_6_3_notEliminable_iff_defectNumber_zero
    [Countable α] {h g : Set α}
    (_hDistinct : h ≠ g)
    (hh : ProperNontrivialSupport h)
    (_hg : ProperNontrivialSupport g) :
    NotEliminableFrom g h ↔ defectNumber h g = 0
```

Source: `.../DefectInfimum.lean`, line 7606.

**Exact reconstruction.** On a countable domain, under the displayed properness and distinctness assumptions, there exists a clean presentation of `h` whose every edge also crosses `g` if and only if there are no positive defects, equivalently the extended cardinal of `h \ commonVertices h g` is zero.

**Access model.** The available coverage link can choose a positive point of `h` and a countable enumeration covering `h`, then apply `proposition_4_2`. No effectivity is supplied.

**Statement-level redundancy.** The displayed definitions together with `proposition_4_2` give a direct route from zero defect to `h ⊆ commonVertices h g` and then to non-eliminability using a countable enumeration and a positive point of `h`. That route appears to use neither `h ≠ g` nor properness of `g`. Thus this declaration is stronger in assumptions than the conclusion appears to require. The report does not remove those assumptions; it flags them as interface slack.


## 4. Helper and link-condition claims

The following declarations are not separately elevated as the strongest paper-level conclusions, but they carry substantive links or certify the concrete constructions. Pure proof-local facts are excluded because they are not declarations. Exact proof-stripped signatures for every item appear in Appendix A.

### 4.1 Geometry helpers

Source label for every declaration in this subsection: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`.

| Declaration and bundle line | Exact statement-level role |
|---|---|
| `crosses_swap_iff`, 568 | Reversing the orientation of a distinct-endpoint edge preserves the crossing predicate. |
| `right_not_mem_of_left_mem_of_crosses`, 586 | If the left endpoint is positive and the edge crosses, the right endpoint is negative. |
| `right_mem_of_left_not_mem_of_crosses`, 594 | If the left endpoint is negative and the edge crosses, the right endpoint is positive. |
| `left_not_mem_of_right_mem_of_crosses`, 602 | Symmetric endpoint-membership consequence with a positive right endpoint. |
| `left_mem_of_right_not_mem_of_crosses`, 610 | Symmetric endpoint-membership consequence with a negative right endpoint. |
| `coveringEdge_spec`, 699 | A classically chosen edge from a pointwise coverage proof both crosses `h,g` and is incident to the selected `h`-point. |
| `presentationFromCoverage_common`, 717 | Every edge of the stream assembled from pointwise coverage crosses both supports. |
| `presentationFromCoverage_covers`, 729 | If the supplied enumeration covers `h`, the assembled stream covers every positive point of `h`. |
| `unionCoveringEdge_spec`, 778 | The analogous selected-edge specification for points in `h ∪ g`. |
| `commonPresentationFromCoverage_common`, 796 | Every edge in the union-covering construction crosses both cuts. |
| `commonPresentationFromCoverage_covers`, 808 | A union-covering enumeration ensures all points of `h ∪ g` occur as endpoints. |

These claims make explicit that the reverse directions of `proposition_4_2` and `lemma_4_4` are choice-and-enumeration constructions, not effective procedures.

### 4.2 Identification-geometry links

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `incomparable_hOnly_nonempty`, 895 | Incomparability implies `h \ g` is nonempty. |
| `incomparable_gOnly_nonempty`, 904 | Incomparability implies `g \ h` is nonempty. |
| `nonEliminabilityContained_implies_overlap`, 914 | The geometric containment condition implies that every incomparable pair overlaps and covers the universe. |
| `incomparableOverlap_implies_nonEliminabilityContained`, 941 | The pairwise overlap-and-cover condition implies the geometric containment condition. |

The two directional claims are the substantive components of the biconditional at line 974.

### 4.3 Safe-closure and eventual-core links

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `seenPrefix_finite`, 1011 | The endpoint set of any finite edge history is finite. |
| `target_mem_edgeVersionSpace`, 1068 | A target in the class belongs to every edge version space induced by a prefix of its valid presentation. |
| `edgeClosure_subset_target`, 1075 | Along such a valid prefix, the edge closure is contained in the target. |
| `exists_safe_fresh`, 1097 | An infinite edge closure contains a point outside the finite seen endpoint set. |
| `safeCoreGenerator_spec`, 1116 | Under closure infinitude, the chosen safe-core output lies in the closure and is unseen. |
| `pairFiber_injective`, 1145 | For an injective core sequence, every pairing-function fiber at fixed time remains injective. |
| `exists_pairFiber_fresh`, 1151 | Such an infinite fiber contains a value outside any finite seen-prefix set. |
| `eventualCoreChoice_spec`, 1169 | The classically selected fiber coordinate is unseen. |
| `eventualCoreGenerator_fresh`, 1186 | Every output of the eventual-core generator is unseen, at every time and history. |
| `eventualCoreGenerator_index_ge`, 1192 | The core-sequence index used at time `t` is at least `t`. |

The target-validity part of `proposition_5_11` therefore comes solely from eventual containment of high sequence indices; the freshness part is unconditional on the target.

### 4.4 Identifier-characterization helper chain

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `exists_enumerated_point_not_seen`, 3205 | A finite positive history cannot exhaust an infinite domain when a surjective enumeration is available. |
| `firstUnseenIndex_spec`, 3232 | The point at the selected least unseen enumeration index is absent from the current sample. |
| `firstUnseenIndex_eventually_eq_first_complement`, 3271 | Along an exact text presentation, if index `k` is the first enumerated point outside the target, the least unseen index eventually stabilizes to `k`. |
| `syntheticContrastiveHistory_eq_fixed`, 3339 | Once that least-unseen index is `k`, the synthetic edge history is extensionally the history paired with the fixed point `enumerate k`. |
| `commonPresentation_for_noncontained`, 3422 | If `h` has common-vertex coverage with `g` but is not contained in `g`, then `g` also has common-vertex coverage with `h` (with `commonVertices h g` as codomain). |
| `chosenTellTale_spec`, 3508 | The classically selected finite set is a tell-tale for its index. |
| `contrastiveTellTaleLearner_eligible`, 3537 | If any eligible index exists, the least-eligible learner’s output is eligible. |
| `contrastiveTellTaleLearner_le_of_eligible`, 3547 | The learner output is no larger than any supplied eligible index. |
| `finite_vertices_eventually_seen`, 3557 | Every finite subset of the positive support eventually appears among endpoints of a valid contrastive presentation. |
| `eventually_target_contrastiveEligible`, 3585 | A target index becomes permanently eligible once its finite chosen set has appeared, with the index-bound condition also eventually met. |
| `incident_member_of_target_of_candidate_consistency`, 3603 | If `h ⊆ g`, an edge crosses both, and an incident point is in `g`, then that incident point is in `h`. |
| `eligible_candidate_eq_of_target_subset`, 3620 | An eligible candidate containing the target and carrying a tell-tale must denote exactly the target. |
| `eventually_not_eligible_of_target_not_subset`, 3637 | Under the geometric containment relation, a candidate not containing the target eventually fails edge consistency. |
| `eventually_not_eligible_of_different_language`, 3661 | Combining the containing and noncontaining cases, every extensionally wrong fixed candidate eventually becomes ineligible. |

The sufficiency chain’s hard link conditions are precisely finite tell-tales and `NonEliminabilityContained`; the least-index convergence after those links is finite-order stabilization.

### 4.5 Uniform closure-dimension helper chain

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `UnorderedEdge.ext`, 3828 | Two unordered-edge structures are equal when their stored vertex finsets are equal. |
| `unorderedCrosses_edge_iff`, 3846 | Forgetting orientation preserves crossing. |
| `exists_orientation`, 3869 | Every two-vertex finset has some oriented distinct-endpoint representative. |
| `UnorderedEdge.orient_unordered`, 3884 | Forgetting the chosen orientation recovers the original unordered edge. |
| `unorderedCrosses_orient_iff`, 3889 | The chosen orientation crosses exactly when the unordered edge crosses. |
| `seenPrefix_eq_unorderedVertices`, 3907 | Seen endpoints of a history equal the vertex union of its distinct unordered edges. |
| `unorderedClosure_subset_version`, 3946 | The closure is contained in every member of a nonempty unordered version space. |
| `uniformThreshold_mono`, 4017 | A generator valid at threshold `d` remains valid at every larger threshold `d'`. |
| `closureDimensionGenerator_spec`, 4039 | Whenever an unseen closure point exists, the selected output is such a point. |
| `finite_history_target_in_version`, 4053 | Any target crossed by every history edge belongs to the unordered version space generated by the history’s distinct edges. |
| `fresh_closure_point_of_dimension_bound`, 4068 | If a nonempty version space is induced by at least `d+1` distinct edges under a dimension-at-most-`d` assumption, the closure contains an unseen vertex. |
| `dimensionBound_suffices`, 4093 | The closure generator works uniformly at threshold `d+1` under the dimension bound. |
| `enumerate_unordered_edges_exactly`, 4115 | Orienting and listing all members of a finite unordered-edge set yields a history whose distinct unordered edges are exactly that set. |
| `orientation_history_crosses`, 4142 | Every support in an unordered version space crosses every edge in the chosen oriented listing. |
| `hollow_obstructs_generator`, 4151 | A hollow set with at least threshold-many edges defeats any proposed generator at that threshold. |
| `generator_implies_dimension_bound`, 4201 | A generator at threshold `d+1` forces every hollow set to have at most `d` edges. |

This chain preserves the exact off-by-one: size `d+1` forces a fresh closure point, while a hollow set of size `d+1` would obstruct that threshold.

### 4.6 Nonuniform-cover construction

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `generatorLevel_mono`, 5062 | Performance levels of one generator are monotone increasing in `n`. |
| `generatorLevels_cover`, 5072 | If the generator has a target-dependent threshold, the union of its levels is exactly the target class. |
| `generatorLevel_uniform`, 5088 | The same generator is uniformly correct on level `n` at threshold `n+1`. |
| `selectedClosureBound_spec`, 5123 | The classically selected number is a valid closure-dimension upper bound for the corresponding cover level. |
| `mem_nonuniformEligibleLevels_iff`, 5144 | Membership in the finite active-level set is equivalent to having reached the padded threshold. |
| `selectedNonuniformLevel_mem`, 5164 | The maximum active level is active. |
| `le_selectedNonuniformLevel`, 5171 | Every active level is below the selected maximum. |
| `nonuniformClosureGenerator_eq_selected`, 5194 | On histories with at least one active level, the global generator equals the closure generator of the selected maximum level. |

The padding term `m` is not cosmetic: from `m + bound(m) + 1 ≤ k` it follows that `m ≤ k`, so active levels lie in a finite range.

### 4.7 Hierarchy and punctured-family helpers

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `freshFromContrastiveGuess_spec`, 5338 | The selected output lies in the currently guessed infinite support and outside seen endpoints. |
| `freshFromTextGuess_spec`, 5390 | The analogous output lies in the currently guessed infinite support and outside the finite text sample. |
| `listIdentifierOfSemantic_prefix`, 5441 | Converting a finite-function semantic identifier to a list interface preserves outputs on stream prefixes. |
| `semanticIdentification_implies_conditionTwo`, 5488 | For indexed nonempty languages over `ℕ`, semantic positive-text identification implies a finite tell-tale for every index. |
| `puncturedCore_injective`, 5612 | The even spine is injectively enumerated. |
| `puncturedFamily_nonempty`, 5621 | Every support in the punctured family is nonempty. |
| `puncturedCore_eventual`, 5636 | The even spine is an eventual core: the unpunctured support misses none of it and each punctured support misses exactly one term. |
| `punctured_contrastivelyGeneratable`, 5665 | The punctured range is contrastively generatable via the eventual-core theorem. |
| `punctured_no_tellTale_at_zero`, 5670 | No finite set can be a tell-tale for the unpunctured support at index zero. |
| `punctured_not_conditionTwo`, 5701 | Therefore the family fails the finite-tell-tale condition. |
| `punctured_not_textIdentifiable`, 5709 | Semantic text identifiability would imply tell-tales, so it fails. |

The theorem `semanticIdentification_implies_conditionTwo` is a Paper28-facing bridge, but its hard diagonal/locking ingredients are imported dependency results and it is specialized to `ℕ` with all supports nonempty.

### 4.8 Disjoint-family helpers

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `evenSupport_infinite`, 5775; `oddSupport_infinite`, 5781 | Both explicit supports are infinite. |
| `evenSupport_disjoint_oddSupport`, 5787 | No natural number belongs to both supports. |
| `disjointFamily_infinite`, 5802 | Every indexed support in the family is infinite. |
| `disjointPairStream_crosses_even`, 5812; `..._crosses_odd`, 5822 | Each paired even/odd edge crosses both supports. |
| `disjointPairStream_presents_even`, 5832; `..._presents_odd`, 5840 | The one shared stream covers all positives of each support and is valid for both. |
| `disjointTextIdentifier_identifies`, 5857 | The concrete first-example identifier semantically identifies every family index, stabilizing at `0` for even and `1` for odd. |
| `disjoint_textIdentifiable`, 5884 | Packages that identifier as `TextIdentifiable`. |
| `disjoint_not_contrastivelyGeneratable`, 5888 | Applies the finite-family shared-presentation obstruction with empty intersection. |

### 4.9 Corrupted co-singleton helpers

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `coSingletonSupport_ne`, 6021 | Distinct missing points give extensionally distinct co-singleton supports. |
| `identity_is_oneCorruptedText`, 6029 | The identity stream is a one-corrupted text presentation of every co-singleton support. |

The second fact supplies the single common stream used to refute one-corruption text identification.

### 4.10 Absence-count helper chain

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `instDecidableIncident`, 6093; `instDecidableCrossesCoSingleton`, 6098 | Under decidable equality, endpoint incidence and co-singleton crossing are decidable propositions. These are computational instances, not mathematical conclusions. |
| `absenceCount_streamPrefix`, 6120 | Finite-history and stream-prefix absence counts agree exactly. |
| `mem_seenEndpoints_iff`, 6140 | Membership in the finite endpoint set is equivalent to incidence at some history position. |
| `crosses_coSingletonSupport_iff_incident`, 6160 | An edge crosses `α \ {s}` exactly when it is incident to the unique negative point `s`. |
| `trueCenter_absence_indices_subset_bad`, 6176 | Every prefix position omitting the true center is a corrupted edge position. |
| `trueCenter_streamAbsenceCount_le`, 6189 | Hence the true center’s absence count is at most the corruption budget at every time. |
| `verticesAtIndices_finite`, 6224 | Endpoints appearing at a finite set of stream indices form a finite set. |
| `mem_verticesAtIndices_of_incident`, 6230 | Incidence at an index in `I` places the point in the endpoint set generated by `I`. |
| `incident_eq_of_two_distinct_incident`, 6238 | If two distinct points are both endpoints of a two-point edge, every incident point equals one of them. |
| `falseCenter_omission_indices_infinite`, 6258 | Every false center is omitted at infinitely many positions of any finitely corrupted co-singleton presentation. |
| `eventually_streamAbsenceCount_gt`, 6312 | Infinitely many omissions force the prefix absence count eventually above any fixed `k`. |
| `trueCenter_eventually_seen`, 6341 | The true center eventually belongs permanently to the seen-endpoint set. |
| `absenceCountIdentifier_mem`, 6374 | On a nonempty seen-endpoint set, the chosen minimizer is a seen endpoint. |
| `absenceCountIdentifier_minimal`, 6386 | Its absence count is no larger than that of any seen endpoint. |
| `seen_early_of_streamAbsenceCount_le`, 6403 | Any seen candidate whose absence count by time `t` is at most `k` must already have appeared among the first `k+1` edges. |
| `competitorThreshold_spec`, 6455 | After the chosen threshold, every fixed false early candidate has absence count greater than `k`. |
| `earlyCandidates_nonempty`, 6469 | The first `k+1` edges have at least one observed endpoint. |
| `example_6_7_absence_counts`, 6563 | On the explicit six-edge history the absence counts for `0,1,2,3,4,5` are respectively `4,5,5,1,4,5`. |
| `example_6_7_unique_minimizer`, 6574 | Point `3` is seen and has strictly smaller absence count than every other seen endpoint. |

The private `example67Edge` is only a constructor wrapper; `example67History` is the concrete diagnostic input reconstructed in §2.9.

### 4.11 Corrupted-incomparability helper chain

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `isKCorruptedTextPresentation_mono`, 6617 | A presentation valid with budget `k` remains valid for any larger budget `ℓ`. |
| `kTextIdentifiable_antitone`, 6624 | Identifiability at a larger corruption budget implies identifiability at every smaller budget. |
| `coSingleton_kContrastivelyIdentifiable`, 6635 | The budget-independent co-singleton identifier yields fixed-budget contrastive identifiability for every `k`. |
| `coSingleton_not_kTextIdentifiable`, 6640 | For every `k ≥ 1`, text identifiability would imply the already-refuted budget-one case. |
| `robustBlockPoint_pair_injective`, 6669 | Equality of encoded block points forces equality of both the block index and within-block coordinate. |
| `robustBlockPoint_fixed_injective`, 6683 | Within each fixed block, the point encoding is injective. |
| `robustBlock_card`, 6690 | Each block has exactly `k+1` points. |
| `mem_robustBlock_iff`, 6697 | Membership in a block is equivalent to equality with one encoded coordinate. |
| `robustCommonCore_infinite`, 6703; `robustBlockSupport_infinite`, 6710 | The common core and every support are infinite. |
| `robustBlockPoint_not_mem_commonCore`, 6715 | Block points are disjoint from the common core. |
| `robustBlockPoint_mem_own`, 6723 | Every encoded block point belongs to its own block. |
| `robustBlockPoint_not_mem_other`, 6728; `..._otherSupport`, 6735 | A block point does not belong to any differently indexed block or support. |
| `robustBlockSupport_ne`, 6742 | Distinct block indices define distinct supports. |
| `finset_eventually_subset_sample_of_subset_range`, 6759 | A finite set contained in a stream’s range is eventually contained in every later finite sample. |
| `robustBlockTextIdentifier_spec`, 6803 | Whenever a complete block exists in the history, the chosen identifier output names a complete block. |
| `completeRobustBlock_eq_target`, 6814 | Under a `k`-corrupted text presentation of support `i`, any fully observed `(k+1)`-point block must be the target block `i`. |
| `robustBlock_kTextIdentifiable`, 6880 | The complete-block identifier gives `k`-corrupted text identification of the block family. |
| `robustCoreEdge_crosses`, 6939 | Every core/common-negative edge crosses every support in the block family. |
| `robustBlockEdge_crosses_zero`, 6954; `..._one`, 6965 | The block-zero/block-one edge crosses each of the first two supports, with opposite orientation roles. |
| `robustSharedStream_crosses_zero`, 6976; `..._one`, 6985 | Every edge of the interleaved stream crosses both selected supports. |
| `robustSharedStream_covers_zero`, 6994; `..._one`, 7009 | The interleaved stream covers all positive points of each selected support. |
| `robustSharedStream_presents_zero`, 7024; `..._one`, 7031 | The stream is a clean valid contrastive presentation for both distinct supports. |
| `cleanPresentation_is_kCorrupted`, 7038 | Every clean presentation is a `k`-corrupted presentation for every budget `k`. |
| `not_kContrastivelyIdentifiable_of_shared`, 7054 | Any two extensionally different indexed supports sharing one clean presentation refute `k`-corrupted contrastive identifiability. |
| `robustBlock_not_kContrastivelyIdentifiable`, 7076 | Applies that obstruction to block supports `0` and `1`. |

### 4.12 Defect and exact-infimum helper chain

Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`.

| Declaration and line | Exact statement-level role |
|---|---|
| `isContrastivePresentation_iff_zeroCorrupted`, 7181 | Clean contrastive presentation is equivalent to zero-corrupted contrastive presentation. |
| `incident_positive_unique`, 7214 | Relative to a crossing edge for `h`, two incident positive points must be equal. |
| `defectIncidentTime_spec`, 7236 | The selected time for a defect point is incident to that point. |
| `defectIncidentTime_is_violation`, 7243 | That selected time necessarily fails to cross `g`. |
| `defectToViolationTime_injective`, 7266 | Distinct defect positives map to distinct wrong-cut occurrence times. |
| `defectNumber_le_wrongCutViolationCount`, 7286 | Every clean presentation’s wrong-cut count is at least the defect number in `ℕ∞`. |
| `defectNumber_le_forcedWrongCutViolationInfimum`, 7294 | If at least one attainable count exists, the defect number is below their infimum. |
| `exists_commonCrossing_of_proper`, 7308 | Any two proper nontrivial supports admit at least one common-crossing edge. |
| `positiveNondefectSet_nonempty`, 7368 | Under the same assumptions, `h` has at least one positive common-crossing vertex. |
| `commonEdgeForNondefect_spec`, 7388 | The selected edge for a nondefect point crosses both cuts and is incident to that point. |
| `edgeForDefect_crosses`, 7400 | Pairing a defect positive with an `h`-negative point crosses `h`. |
| `edgeForDefect_not_crosses`, 7406 | The same edge cannot cross `g`, by the definition of defect. |
| `edgeForPositive_crosses`, 7424 | Pairing any `h`-positive with a fixed `h`-negative crosses `h`. |
| `exists_clean_contrastive_presentation`, 7429 | Every proper nontrivial support over a countable domain has a clean contrastive presentation. |
| `cleanWrongCutViolationCounts_nonempty`, 7452 | Therefore the attainable wrong-cut-count set is nonempty. |
| `exists_clean_presentation_wrongCutCount_eq_defect`, 7466 | If the defect set is finite and both supports are proper nontrivial, there is a clean presentation attaining exactly the defect number. |

The exact-infimum theorem combines the universal injection lower bound with the finite-defect attainment statement and the `⊤` behavior of infinite extended cardinality.

## 5. Diagnostics, counterexamples, and source-interface repairs visible in the statements

### 5.1 The geometric relation is not definitionally the existential relation

`NonEliminabilityContained` is defined using `h ⊆ commonVertices h g`; it does not mention `NotEliminableFrom`. The only primary equivalence between those predicates is `proposition_4_2`, whose type requires a supplied point in `h` and a supplied enumeration covering `h`. Consequently:

* the geometric characterization is exact as stated;
* calling it an unconditional characterization of existential non-eliminability would silently drop nonemptiness and countable-enumeration hypotheses;
* under the top-level countable/proper assumptions of `theorem_4_7`, the missing witnesses can be obtained set-theoretically, but that bridge is not definitionally built into `NonEliminabilityContained`.

This is the highest-risk link-condition issue in the identification part.

### 5.2 All main learning and generation conclusions are semantic

The identifiers and generators are arbitrary total functions. Concrete constructions repeatedly use `Classical.choose`, `Nat.find`, arbitrary finite minimizers, selected orientations, selected closure bounds, and selected tell-tales. Countability only gives existence of enumerations. Therefore none of the following should be upgraded to an algorithmic or computable theorem without extra work:

* the contrastive/text identification characterization;
* the safe-core, eventual-core, closure-dimension, or cover generators;
* the absence-count or complete-block identifiers as formalized here;
* the defect-attaining presentation construction.

Some finite computations, such as absence counts on `ℕ`, are definitionally decidable, but the theorem-level witnesses remain semantic because of arbitrary choice and lack of encoded class access.

### 5.3 Ordinary, uniform, and nonuniform generation are genuinely different interfaces

`ContrastivelyGeneratable` allows the time threshold to depend on the particular infinite presentation. `NonuniformlyContrastivelyGeneratable` requires a target-dependent **distinct unordered edge** threshold uniform over all finite crossing histories. `UniformlyContrastivelyGeneratableAt` requires one class-wide threshold. Theorem 5.5 characterizes the second notion, while the hierarchy witnesses and Propositions 5.8, 5.11, and 5.12 concern the first. Replacing one with another would change quantifier order and theorem strength.

### 5.4 Freshness is only relative to observed input vertices

Every primary generator conclusion excludes `seenPrefix history`. No definition records earlier generated outputs. A generator is therefore permitted to output the same unseen point repeatedly if that point never appears in the input stream. Any interpretation requiring pairwise distinct generated outputs would be strictly stronger than the Lean statements.

### 5.5 Positive coverage is one-sided and exact

A clean contrastive presentation must cover every positive target point as an endpoint but need not cover negative points. A corrupted presentation keeps the same exact positive-side coverage despite allowing finitely many bad observations. This is substantive in:

* the synthetic common-presentation obstructions;
* the false-center omission argument;
* the target-block completeness argument;
* the defect-point injection.

The corruption budgets count bad **occurrence indices**, not distinct bad edges or values.

### 5.6 Empty-support and no-history vacuity

For `h=∅`, no edge crosses `h`, so no infinite contrastive stream can satisfy `IsContrastivePresentation stream h`. Exact positive-text presentation of an empty language is likewise absent in the usual nonempty-stream interface. Therefore implication/universal definitions of identification and eventual generation can hold vacuously on empty targets. The top-level identification equivalence avoids this through `AllProperNontrivial`; many general definitions and closure theorems do not.

Uniform finite-history generation can also be vacuous for a target at a threshold that no crossing history can reach. This includes small domains or cuts admitting too few distinct crossing edges. The closure-dimension equivalence is formulated so that its obstruction side has matching edge cases.

### 5.7 Strong sufficient hypotheses delegate the hard object

`InfiniteSafeCores` already provides an infinite intersection of all consistent targets at every valid prefix; `IsEventualCore` supplies an injective sequence eventually lying in every target. The corresponding generation theorems are mathematically correct reductions, but they do not establish these strong properties from more primitive assumptions. Their difficulty is almost entirely in obtaining the supplied core condition.

Similarly, `proposition_5_12` receives the common indistinguishing stream and a finite exact intersection. It proves the obstruction cleanly, but applications must construct those witnesses.

### 5.8 The exact-dimension predicate is a least-bound predicate

`ContrastiveClosureDimensionEquals 𝓗 d` does not state that a hollow set of size exactly `d` exists. It states that `d` is an upper bound and no smaller natural upper bound exists. The sharp-threshold theorem is therefore based on minimality of bounds rather than a displayed extremal witness. The separate `hollow_cardinality_lower_bound` gives witness-based lower bounds when a hollow set is explicitly available.

### 5.9 Threshold zero is treated differently from positive thresholds

`UniformlyContrastivelyGeneratable` permits an existential threshold `0`, but `IsLeastPositiveUniformThreshold` compares only thresholds `k>0`. The sharp result concludes that `d+1`, always positive, is least among positive thresholds. One must not rewrite it as an unrestricted least-threshold theorem without analyzing the zero convention.

### 5.10 Indexed convergence and extensional class conditions coexist

Identifiers output natural indices and must eventually stabilize syntactically to one index `j`, while correctness only requires `F j = F z`. Geometric conditions and generation classes often use `Set.range F`, which forgets repetitions and index order. This is deliberate in the types, but it means:

* duplicate indices do not hurt correctness;
* class-level geometric conditions cannot distinguish duplicate representations;
* statements about stable indices are stronger than eventual extensional correctness at each time, because the output index itself must stop changing.

### 5.11 Concrete hierarchy claims are witness theorems, not one universal lattice theorem

The bundle proves general inclusions from identification to generation under infinitude, a finite-family obstruction, and two explicit separating families. The declarations `theorem_5_13_5_14_punctured_witness` and `..._disjoint_witness` are concrete conjunctions about named families. They do not themselves quantify over all classes or define a formal partial order of hierarchy levels.

### 5.12 Corruption incomparability uses a budget-dependent reverse witness

For every `k≥1`, the co-singleton family gives one direction and is fixed independently of `k`. The reverse family is `robustBlockFamily k`; its block size is explicitly `k+1`. Thus the theorem gives a family for each budget, not a single reverse-separation family uniform in all budgets.

### 5.13 Redundant assumptions in the defect corollaries

At statement level, the distinctness premise in both displayed Proposition 6.3 declarations is not needed by the separately stated lower-bound/attainment or coverage/cardinality interfaces from which the conclusions can be reconstructed. In the zero-defect/non-eliminability theorem, the same direct reconstruction also appears not to need properness of `g`. These assumptions must still be reported because they are part of the Lean theorem types, but they appear stronger than necessary. This is interface slack, not a mathematical contradiction.

### 5.14 The defect infimum is protected from empty-set ambiguity only in the theorem

`forcedWrongCutViolationInfimum` is defined for every `h,g` as an infimum, whether or not any clean presentation of `h` exists. The equality theorem adds countability and properness of `h`, and a helper proves the attainable-count set is nonempty. Outside those hypotheses, no primary theorem in the bundle characterizes the empty-attainment behavior.

## 6. Statement-level vacuity and circularity audit

| Interface or theorem | Vacuity/circularity assessment |
|---|---|
| `IsContrastivePresentation` / `ContrastivelyIdentifies` / `GeneratesFrom` | Empty targets, or any target with no valid presentation, make the implication-based obligations vacuous. Proper/nontrivial assumptions remove this in the main identification theorem. |
| `proposition_4_2` | Nonvacuous reverse direction is conditioned on an explicit positive point and enumeration. The conclusion is not assumed, but the representation work is supplied. |
| `lemma_4_4` | Same issue for `h ∪ g`; the hypotheses force a nonempty countably covered union. |
| `NonEliminabilityContained` | Not circular, but it is a surrogate geometric relation. Its link to existential non-eliminability is conditional. |
| `proposition_5_8` | The infinite-safe-core premise essentially guarantees an immediately usable fresh point at every valid prefix. Hard content is assumed in the premise. |
| `proposition_5_11` | A supplied injective eventual core already gives an eventual common tail of target points. Hard content is the core’s existence. |
| Uniform generation at threshold `d` | Obligations are vacuous on histories with fewer than `d` distinct crossing edges; this is intrinsic to threshold formulations. |
| `ContrastiveClosureDimensionAtMost` | If there are no hollow sets, every upper bound works; least-bound value is then `0`. |
| `theorem_5_5_sufficiency` | The increasing cover and finite dimension of each level are strong structural inputs, but do not themselves supply the one global generator. Padding/selection performs nontrivial assembly. |
| `proposition_5_12` | Strong witnesses are supplied, but the contradiction between common input, finite intersection, correctness, and freshness is not tautological. |
| `KTextIdentifiesFrom` / `KContrastivelyIdentifiesFrom` | Each is an implication and is vacuous for streams not satisfying the corruption-presentation premise. The concrete negative and positive examples construct or handle valid streams. |
| `theorem_6_5` | Nonvacuous: the same identity stream is a legal one-corrupted presentation for two distinct targets. |
| `theorem_6_6` | Nonvacuous for every stream satisfying the finite-corruption and coverage premises; one identifier works for all budgets. |
| Defect infimum equality | Nonempty attainment is separately proved under the theorem hypotheses, avoiding vacuous infimum reasoning. |

No top-level theorem literally assumes its own conclusion. The principal “circularity risk” is instead **semantic delegation**: strong core, tell-tale, cover, or witness hypotheses encode much of the hard object needed for the conclusion.

## 7. Access-model audit for primary claims

| Claim cluster | Arbitrary existence or supplied construction | Enumeration/countability | Decidability/effectivity | Finiteness/coding/tie-breaking |
|---|---|---|---|---|
| Common-crossing geometry | Pointwise edges and streams selected by classical choice in reverse directions | `proposition_4_2` and `lemma_4_4` receive explicit enumerations | None | Fallback positive point explicitly supplied; no canonical tie-breaking |
| Identification characterization | Existence of arbitrary semantic identifiers; chosen tell-tales; least eligible index | `[Countable α]` yields a set-theoretic surjection; `[Infinite α]` ensures unseen points | No computability, membership oracle, or effective family representation | Finite tell-tales; syntactic stabilization to a single index; least-index search in logic |
| Safe/eventual cores | Explicit strong core premise; outputs chosen classically | Eventual core is a supplied sequence `ℕ→α` | None | Seen endpoints finite; pairing-function coding; arbitrary fresh coordinate |
| Uniform closure dimension | Semantic access to version-space intersections; chosen orientations and outputs | No countability assumption | None | Finite unordered edge sets; distinct-edge counting; arbitrary orientation and fallback |
| Nonuniform cover theorem | Chosen bound per level; maximum active level | Countable sequence of levels is part of cover witness | None | Padded thresholds ensure finite active set and maximum |
| Hierarchy inclusions | Fresh point chosen from guessed infinite support | None | None | Infinitude beats finite observed set |
| Finite-family obstruction | Shared stream and exact finite intersection explicitly supplied | None | None | Finite family, finite core, maximum of finitely many convergence thresholds |
| Co-singleton corrupted result | Absence minimizer chosen classically | Domain fixed to `ℕ` | Incidence/counts decidable on `ℕ`, but identifier not declared computable | Arbitrary tie-breaking; finite early candidate set; one identifier uniform in budget |
| Robust block result | Complete block and identifier output chosen classically | Arithmetic coding by `Nat.pair` | No computability claim despite explicit arithmetic | Blocks have exact size `k+1`; false complete block exceeds `k` bad occurrences |
| Defect infimum | Incident times, enumerations, common edges selected classically | `[Countable α]` for clean presentations | None | Extended-natural cardinality and infimum; exact finite-defect construction |

## 8. Difficulty-preservation assessment

### 8.1 Hard content genuinely present in theorem statements

The following statements preserve substantial mathematical content rather than assuming it away:

* the exact four-region characterization of common-vertex coverage;
* the geometric equivalence between containment and incomparable overlap/cover;
* the semantic two-part identification characterization;
* the exact `d+1` versus `d` closure-dimension equivalence and sharp positive threshold;
* the increasing-cover characterization of target-dependent uniform thresholds;
* the finite-family shared-presentation obstruction;
* the two explicit hierarchy witnesses;
* the corrupted co-singleton positive/negative results and block-family reverse separation;
* the exact extended-natural defect-infimum equality.

### 8.2 Hard steps delegated to hypotheses or imported interfaces

The following conclusions are mainly reductions once their hypotheses are granted:

* infinite safe cores imply generation;
* a supplied eventual core implies generation;
* finite tell-tales plus the geometric relation imply contrastive identification;
* an increasing cover plus one finite dimension bound per level implies nonuniform generation;
* a supplied shared stream plus a finite exact intersection implies non-generation.

The full characterization of contrastive identification also delegates semantic text-identification-to-finite-tell-tale necessity to imported Angluin/Paper08 infrastructure. Nothing in the Paper28 theorem types preserves an effective version of that necessity.

### 8.3 Specializations and weakenings at the interface

* The identification theorem is for an **indexed countable family** on a countable infinite domain, not an arbitrary unindexed class.
* The non-eliminability relation used in the class condition is a common-vertex surrogate; the existential relation needs a separate countability/nonempty bridge.
* Generation freshness is weaker than global novelty because earlier outputs are ignored.
* Uniform sample complexity counts distinct unordered observed edges, not observation time, total occurrences, or distinct vertices.
* The sharp threshold is least only among positive thresholds.
* The corrupted reverse witness depends on the budget.
* All learning/generation results are semantic and noneffective.

## 9. Dependency/background only

The following bundled labels are imported interfaces and are not primary results of Paper28. They are included here only to make the Paper28 statements intelligible.

### 9.1 Core interfaces

`GenLimitLean/GenLimit/Core/Countable.lean` supplies:

* `Generic.Language α = Set α`;
* indexed families `ℕ → Set α` and extensional classes `Set (Set α)`;
* streams `ℕ → α`, finite-history generators, exact `Presents`, finite samples, and `CorrectAt`;
* finite-sample and exact-presentation lemmas used for eventual coverage.

`GenLimitLean/GenLimit/Core/Basic.lean` is an older `ℕ`-domain core and is background only; no theorem from it is presented here as a Paper28 claim.

### 9.2 Angluin dependency

The `Dependency_Angluin1980` labels supply semantic identifiers, syntactic convergence, finite tell-tales (`IsTellTale` and `ConditionTwo`), and locking-sequence necessity/sufficiency infrastructure. Paper28 uses these as a bridge between text identification and finite tell-tales. The dependency also distinguishes effective statements, but the Paper28 top-level declarations use the semantic interfaces and do not inherit an effective conclusion.

### 9.3 Paper08 dependency

`Paper08_AutomatedHallucinationDetection/AngluinCondition.lean` supplies, in particular, a generic theorem that semantic text identifiability on a nonempty countable domain implies `ConditionTwo`. Paper28 invokes that theorem in the sufficiency direction of its identification characterization. This imported theorem is background, not a Paper28 primary result.

### 9.4 Paper02 dependency

The Paper02 labels supply:

* ordinary positive-text `GeneratableInLimit` used in the hierarchy statement;
* `IsNondecreasingCover`, meaning monotonicity of `classes : ℕ → Set (Set α)` together with equality of `𝓗` to their union.

Paper28’s contrastive closure-dimension theorems are separate from Paper02’s ordinary text closure dimension, even though the cover predicate is reused.

## 10. Overall code-only assessment

At the statement level, the bundle contains a broad and internally coherent semantic theory: exact common-crossing geometry, a contrastive-identification characterization, uniform and target-dependent closure-dimension characterizations, explicit hierarchy witnesses, corrupted-model separations, and an exact extended-cardinal defect formula. The most consequential audit qualifications are that the algorithms are noncomputable semantic functions; that common-vertex coverage is used as a surrogate for existential non-eliminability and needs explicit countability/nonempty links; that three generation notions have different quantifier orders; that freshness ignores previous outputs; and that several sufficient conditions supply most of the hard witness.

The report does **not** assert correspondence with any external author paper. It only records what the displayed Lean declarations state.

## Appendix A. Exhaustive primary-family declaration ledger

This appendix covers all 307 declarations found under the twelve substantive `Paper28_ContrastiveIdentificationAndGeneration` source labels. For theorems, only the type signature is transcribed; proof bodies are omitted. For definitions, the defining body is retained because it may determine the interface. Embedded proof terms used only to satisfy structure fields are not used as semantic evidence in the prose audit. Source labels and bundle line numbers are provenance only.

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

#### `Edge`

- Kind: `structure`
- Classification: definition or construction
- Bundle line: 558
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
structure Edge (α : Type*) where
  left : α
  right : α
  ne : left ≠ right
```

#### `Crosses`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 564
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def Crosses (h : Set α) (e : Edge α) : Prop :=
  (e.left ∈ h ∧ e.right ∉ h) ∨
    (e.right ∈ h ∧ e.left ∉ h)
```

#### `crosses_swap_iff`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 568
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem crosses_swap_iff (h : Set α) (x y : α) (hxy : x ≠ y) :
    Crosses h ⟨x, y, hxy⟩ ↔
      Crosses h ⟨y, x, Ne.symm hxy⟩
```

#### `CommonCrossing`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 575
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def CommonCrossing (h g : Set α) (e : Edge α) : Prop :=
  Crosses h e ∧ Crosses g e
```

#### `Incident`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 579
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def Incident (x : α) (e : Edge α) : Prop :=
  x = e.left ∨ x = e.right
```

#### `commonVertices`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 583
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def commonVertices (h g : Set α) : Set α :=
  {x | ∃ e : Edge α, CommonCrossing h g e ∧ Incident x e}
```

#### `right_not_mem_of_left_mem_of_crosses`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 586
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem right_not_mem_of_left_mem_of_crosses
    {h : Set α} {e : Edge α}
    (hleft : e.left ∈ h) (hcross : Crosses h e) :
    e.right ∉ h
```

#### `right_mem_of_left_not_mem_of_crosses`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 594
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem right_mem_of_left_not_mem_of_crosses
    {h : Set α} {e : Edge α}
    (hleft : e.left ∉ h) (hcross : Crosses h e) :
    e.right ∈ h
```

#### `left_not_mem_of_right_mem_of_crosses`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 602
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem left_not_mem_of_right_mem_of_crosses
    {h : Set α} {e : Edge α}
    (hright : e.right ∈ h) (hcross : Crosses h e) :
    e.left ∉ h
```

#### `left_mem_of_right_not_mem_of_crosses`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 610
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem left_mem_of_right_not_mem_of_crosses
    {h : Set α} {e : Edge α}
    (hright : e.right ∉ h) (hcross : Crosses h e) :
    e.left ∈ h
```

#### `bothPositive`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 619
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def bothPositive (h g : Set α) : Set α := h ∩ g
```

#### `hOnly`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 620
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def hOnly (h g : Set α) : Set α := h \ g
```

#### `gOnly`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 621
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def gOnly (h g : Set α) : Set α := g \ h
```

#### `bothNegative`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 622
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def bothNegative (h g : Set α) : Set α := (h ∪ g)ᶜ
```

#### `theorem_4_3`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 625
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem theorem_4_3
    (h g : Set α) :
    h ⊆ commonVertices h g ↔
      ((bothPositive h g).Nonempty → (bothNegative h g).Nonempty) ∧
      ((hOnly h g).Nonempty → (gOnly h g).Nonempty)
```

#### `IsContrastivePresentation`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 682
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def IsContrastivePresentation
    (stream : ℕ → Edge α) (h : Set α) : Prop :=
  (∀ n, Crosses h (stream n)) ∧
    h ⊆ {x | ∃ n, Incident x (stream n)}
```

#### `NotEliminableFrom`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 689
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def NotEliminableFrom (g h : Set α) : Prop :=
  ∃ stream : ℕ → Edge α,
    IsContrastivePresentation stream h ∧
      ∀ n, Crosses g (stream n)
```

#### `coveringEdge`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 694
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
noncomputable def coveringEdge
    {h g : Set α} (hcover : h ⊆ commonVertices h g)
    (x : α) (hx : x ∈ h) : Edge α :=
  Classical.choose (hcover hx)
```

#### `coveringEdge_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 699
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem coveringEdge_spec
    {h g : Set α} (hcover : h ⊆ commonVertices h g)
    (x : α) (hx : x ∈ h) :
    CommonCrossing h g (coveringEdge hcover x hx) ∧
      Incident x (coveringEdge hcover x hx)
```

#### `presentationFromCoverage`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 706
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
noncomputable def presentationFromCoverage
    {h g : Set α} (hcover : h ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α) : ℕ → Edge α := by
  classical
  exact fun n =>
    if hx : enumeration n ∈ h then
        coveringEdge hcover (enumeration n) hx
      else
        coveringEdge hcover x₀ hx₀
```

#### `presentationFromCoverage_common`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 717
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem presentationFromCoverage_common
    {h g : Set α} (hcover : h ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α) (n : ℕ) :
    CommonCrossing h g
      (presentationFromCoverage hcover x₀ hx₀ enumeration n)
```

#### `presentationFromCoverage_covers`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 729
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem presentationFromCoverage_covers
    {h g : Set α} (hcover : h ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α)
    (henum : h ⊆ Set.range enumeration) :
    h ⊆
      {x | ∃ n,
        Incident x
          (presentationFromCoverage hcover x₀ hx₀ enumeration n)}
```

#### `proposition_4_2`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 746
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem proposition_4_2
    {h g : Set α} (x₀ : α) (hx₀ : x₀ ∈ h)
    (enumeration : ℕ → α) (henum : h ⊆ Set.range enumeration) :
    NotEliminableFrom g h ↔ h ⊆ commonVertices h g
```

#### `AdmitCommonPresentation`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 768
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
def AdmitCommonPresentation (h g : Set α) : Prop :=
  ∃ stream : ℕ → Edge α,
    IsContrastivePresentation stream h ∧
      IsContrastivePresentation stream g
```

#### `unionCoveringEdge`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 773
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
noncomputable def unionCoveringEdge
    {h g : Set α} (hcover : h ∪ g ⊆ commonVertices h g)
    (x : α) (hx : x ∈ h ∪ g) : Edge α :=
  Classical.choose (hcover hx)
```

#### `unionCoveringEdge_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 778
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem unionCoveringEdge_spec
    {h g : Set α} (hcover : h ∪ g ⊆ commonVertices h g)
    (x : α) (hx : x ∈ h ∪ g) :
    CommonCrossing h g (unionCoveringEdge hcover x hx) ∧
      Incident x (unionCoveringEdge hcover x hx)
```

#### `commonPresentationFromCoverage`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 785
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
noncomputable def commonPresentationFromCoverage
    {h g : Set α} (hcover : h ∪ g ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h ∪ g)
    (enumeration : ℕ → α) : ℕ → Edge α := by
  classical
  exact fun n =>
    if hx : enumeration n ∈ h ∪ g then
        unionCoveringEdge hcover (enumeration n) hx
      else
        unionCoveringEdge hcover x₀ hx₀
```

#### `commonPresentationFromCoverage_common`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 796
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem commonPresentationFromCoverage_common
    {h g : Set α} (hcover : h ∪ g ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h ∪ g)
    (enumeration : ℕ → α) (n : ℕ) :
    CommonCrossing h g
      (commonPresentationFromCoverage hcover x₀ hx₀ enumeration n)
```

#### `commonPresentationFromCoverage_covers`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 808
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem commonPresentationFromCoverage_covers
    {h g : Set α} (hcover : h ∪ g ⊆ commonVertices h g)
    (x₀ : α) (hx₀ : x₀ ∈ h ∪ g)
    (enumeration : ℕ → α)
    (henum : h ∪ g ⊆ Set.range enumeration) :
    h ∪ g ⊆
      {x | ∃ n,
        Incident x
          (commonPresentationFromCoverage hcover x₀ hx₀ enumeration n)}
```

#### `lemma_4_4`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 825
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Geometry.lean`

```lean
theorem lemma_4_4
    {h g : Set α} (x₀ : α) (hx₀ : x₀ ∈ h ∪ g)
    (enumeration : ℕ → α)
    (henum : h ∪ g ⊆ Set.range enumeration) :
    AdmitCommonPresentation h g ↔
      h ∪ g ⊆ commonVertices h g
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`

#### `Incomparable`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 876
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`

```lean
def Incomparable (h g : Set α) : Prop :=
  ¬h ⊆ g ∧ ¬g ⊆ h
```

#### `OverlappingCover`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 880
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`

```lean
def OverlappingCover (h g : Set α) : Prop :=
  (h ∩ g).Nonempty ∧ h ∪ g = Set.univ
```

#### `NonEliminabilityContained`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 886
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`

```lean
def NonEliminabilityContained (𝓗 : Set (Set α)) : Prop :=
  ∀ h ∈ 𝓗, ∀ g ∈ 𝓗,
    h ⊆ commonVertices h g → h ⊆ g
```

#### `IncomparablePairsOverlap`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 891
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`

```lean
def IncomparablePairsOverlap (𝓗 : Set (Set α)) : Prop :=
  ∀ h ∈ 𝓗, ∀ g ∈ 𝓗,
    Incomparable h g → OverlappingCover h g
```

#### `incomparable_hOnly_nonempty`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 895
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`

```lean
theorem incomparable_hOnly_nonempty
    {h g : Set α} (hinc : Incomparable h g) :
    (hOnly h g).Nonempty
```

#### `incomparable_gOnly_nonempty`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 904
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`

```lean
theorem incomparable_gOnly_nonempty
    {h g : Set α} (hinc : Incomparable h g) :
    (gOnly h g).Nonempty
```

#### `nonEliminabilityContained_implies_overlap`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 914
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`

```lean
theorem nonEliminabilityContained_implies_overlap
    {𝓗 : Set (Set α)}
    (hrel : NonEliminabilityContained 𝓗) :
    IncomparablePairsOverlap 𝓗
```

#### `incomparableOverlap_implies_nonEliminabilityContained`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 941
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`

```lean
theorem incomparableOverlap_implies_nonEliminabilityContained
    {𝓗 : Set (Set α)}
    (hoverlap : IncomparablePairsOverlap 𝓗) :
    NonEliminabilityContained 𝓗
```

#### `theorem_4_7_geometric_equivalence`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 974
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentificationGeometry.lean`

```lean
theorem theorem_4_7_geometric_equivalence
    (𝓗 : Set (Set α)) :
    NonEliminabilityContained 𝓗 ↔
      IncomparablePairsOverlap 𝓗
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

#### `seenPrefix`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1008
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
def seenPrefix {t : ℕ} (history : Fin t → Edge α) : Set α :=
  {x | ∃ i, Incident x (history i)}
```

#### `seenPrefix_finite`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 1011
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem seenPrefix_finite {t : ℕ} (history : Fin t → Edge α) :
    (seenPrefix history).Finite
```

#### `streamPrefix`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1023
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
def streamPrefix (stream : ℕ → Edge α) (t : ℕ) : Fin t → Edge α :=
  fun i => stream i
```

#### `ContrastiveGenerator`

- Kind: `abbrev`
- Classification: definition or construction
- Bundle line: 1027
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
abbrev ContrastiveGenerator (α : Type*) :=
  ∀ t : ℕ, (Fin t → Edge α) → α
```

#### `generatorOutput`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1031
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
def generatorOutput
    (G : ContrastiveGenerator α) (stream : ℕ → Edge α) (t : ℕ) : α :=
  G t (streamPrefix stream t)
```

#### `GeneratesFrom`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1036
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
def GeneratesFrom
    (G : ContrastiveGenerator α) (h : Set α) : Prop :=
  ∀ stream : ℕ → Edge α,
    IsContrastivePresentation stream h →
      ∃ T, ∀ t, T ≤ t →
        generatorOutput G stream t ∈ h ∧
          generatorOutput G stream t ∉
            seenPrefix (streamPrefix stream t)
```

#### `ContrastivelyGeneratable`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1046
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
def ContrastivelyGeneratable (𝓗 : Set (Set α)) : Prop :=
  ∃ G : ContrastiveGenerator α,
    ∀ h, h ∈ 𝓗 → GeneratesFrom G h
```

#### `edgeVersionSpace`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1051
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
def edgeVersionSpace
    (𝓗 : Set (Set α)) {t : ℕ} (history : Fin t → Edge α) :
    Set (Set α) :=
  {h | h ∈ 𝓗 ∧ ∀ i, Crosses h (history i)}
```

#### `edgeClosure`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1058
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
noncomputable def edgeClosure
    (𝓗 : Set (Set α)) {t : ℕ} (history : Fin t → Edge α) : Set α :=
  by
    classical
    exact
      if (edgeVersionSpace 𝓗 history).Nonempty then
        {x | ∀ h, h ∈ edgeVersionSpace 𝓗 history → x ∈ h}
      else
        ∅
```

#### `target_mem_edgeVersionSpace`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 1068
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem target_mem_edgeVersionSpace
    {𝓗 : Set (Set α)} {h : Set α} (hh : h ∈ 𝓗)
    {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream h) (t : ℕ) :
    h ∈ edgeVersionSpace 𝓗 (streamPrefix stream t)
```

#### `edgeClosure_subset_target`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 1075
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem edgeClosure_subset_target
    {𝓗 : Set (Set α)} {h : Set α} (hh : h ∈ 𝓗)
    {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream h) (t : ℕ) :
    edgeClosure 𝓗 (streamPrefix stream t) ⊆ h
```

#### `InfiniteSafeCores`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1092
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
def InfiniteSafeCores (𝓗 : Set (Set α)) : Prop :=
  ∀ h, h ∈ 𝓗 → ∀ stream : ℕ → Edge α,
    IsContrastivePresentation stream h →
      ∀ t, (edgeClosure 𝓗 (streamPrefix stream t)).Infinite
```

#### `exists_safe_fresh`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 1097
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem exists_safe_fresh
    {𝓗 : Set (Set α)} {t : ℕ} {history : Fin t → Edge α}
    (hinfinite : (edgeClosure 𝓗 history).Infinite) :
    ∃ x, x ∈ edgeClosure 𝓗 history ∧ x ∉ seenPrefix history
```

#### `safeCoreGenerator`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1104
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
noncomputable def safeCoreGenerator [Nonempty α]
    (𝓗 : Set (Set α)) : ContrastiveGenerator α :=
  by
    classical
    exact fun _t history =>
      if hex :
          ∃ x, x ∈ edgeClosure 𝓗 history ∧
            x ∉ seenPrefix history then
        Classical.choose hex
      else
        Classical.choice inferInstance
```

#### `safeCoreGenerator_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 1116
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem safeCoreGenerator_spec [Nonempty α]
    {𝓗 : Set (Set α)} {t : ℕ} {history : Fin t → Edge α}
    (hinfinite : (edgeClosure 𝓗 history).Infinite) :
    safeCoreGenerator 𝓗 t history ∈ edgeClosure 𝓗 history ∧
      safeCoreGenerator 𝓗 t history ∉ seenPrefix history
```

#### `proposition_5_8`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 1126
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem proposition_5_8 [Nonempty α]
    (𝓗 : Set (Set α)) (hsafe : InfiniteSafeCores 𝓗) :
    ContrastivelyGeneratable 𝓗
```

#### `IsEventualCore`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1141
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
def IsEventualCore (𝓗 : Set (Set α)) (core : ℕ → α) : Prop :=
  Function.Injective core ∧
    ∀ h, h ∈ 𝓗 → {m : ℕ | core m ∉ h}.Finite
```

#### `pairFiber_injective`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 1145
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem pairFiber_injective
    (core : ℕ → α) (hcore : Function.Injective core) (t : ℕ) :
    Function.Injective (fun k => core (Nat.pair t k))
```

#### `exists_pairFiber_fresh`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 1151
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem exists_pairFiber_fresh
    (core : ℕ → α) (hcore : Function.Injective core)
    {t : ℕ} (history : Fin t → Edge α) :
    ∃ k, core (Nat.pair t k) ∉ seenPrefix history
```

#### `eventualCoreChoice`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1164
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
noncomputable def eventualCoreChoice
    (core : ℕ → α) (hcore : Function.Injective core)
    {t : ℕ} (history : Fin t → Edge α) : ℕ :=
  Classical.choose (exists_pairFiber_fresh core hcore history)
```

#### `eventualCoreChoice_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 1169
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem eventualCoreChoice_spec
    (core : ℕ → α) (hcore : Function.Injective core)
    {t : ℕ} (history : Fin t → Edge α) :
    core (Nat.pair t (eventualCoreChoice core hcore history)) ∉
      seenPrefix history
```

#### `eventualCoreGenerator`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 1180
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
noncomputable def eventualCoreGenerator
    (core : ℕ → α) (hcore : Function.Injective core) :
    ContrastiveGenerator α :=
  fun t history =>
    core (Nat.pair t (eventualCoreChoice core hcore history))
```

#### `eventualCoreGenerator_fresh`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 1186
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem eventualCoreGenerator_fresh
    (core : ℕ → α) (hcore : Function.Injective core)
    {t : ℕ} (history : Fin t → Edge α) :
    eventualCoreGenerator core hcore t history ∉ seenPrefix history
```

#### `eventualCoreGenerator_index_ge`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 1192
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem eventualCoreGenerator_index_ge
    (core : ℕ → α) (hcore : Function.Injective core)
    {t : ℕ} (history : Fin t → Edge α) :
    t ≤ Nat.pair t (eventualCoreChoice core hcore history)
```

#### `proposition_5_11`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 1201
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/GenerationCores.lean`

```lean
theorem proposition_5_11
    (𝓗 : Set (Set α)) (core : ℕ → α)
    (hcore : IsEventualCore 𝓗 core) :
    ContrastivelyGeneratable 𝓗
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

#### `ContrastiveIdentifier`

- Kind: `abbrev`
- Classification: definition or construction
- Bundle line: 3159
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
abbrev ContrastiveIdentifier (α : Type*) :=
  ∀ t : ℕ, (Fin t → Edge α) → ℕ
```

#### `contrastiveIdentifierOutput`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3163
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
def contrastiveIdentifierOutput
    (I : ContrastiveIdentifier α) (stream : ℕ → Edge α) (t : ℕ) : ℕ :=
  I t (streamPrefix stream t)
```

#### `ContrastivelyIdentifiesFrom`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3170
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
def ContrastivelyIdentifiesFrom
    (I : ContrastiveIdentifier α)
    (F : GenLimit.Generic.LanguageFamily α)
    (z : ℕ) (stream : ℕ → Edge α) : Prop :=
  ∃ j, F j = F z ∧
    ∃ T, ∀ t, T ≤ t →
      contrastiveIdentifierOutput I stream t = j
```

#### `ContrastivelyIdentifies`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3179
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
def ContrastivelyIdentifies
    (I : ContrastiveIdentifier α)
    (F : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : ℕ → Edge α,
    IsContrastivePresentation stream (F z) →
      ContrastivelyIdentifiesFrom I F z stream
```

#### `ContrastivelyIdentifiable`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3187
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
def ContrastivelyIdentifiable
    (F : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ I : ContrastiveIdentifier α, ContrastivelyIdentifies I F
```

#### `TextIdentifiable`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3192
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
def TextIdentifiable
    (F : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ M : GenLimit.Angluin.SemanticIdentifier α,
    GenLimit.Angluin.SemanticallyIdentifies M F
```

#### `AllProperNontrivial`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3199
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
def AllProperNontrivial
    (F : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ i, (F i).Nonempty ∧ (F i)ᶜ.Nonempty
```

#### `exists_enumerated_point_not_seen`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3205
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem exists_enumerated_point_not_seen
    [Infinite α] (enumerate : ℕ → α) (henumerate : Function.Surjective enumerate)
    {t : ℕ} (history : Fin t → α) :
    ∃ n, enumerate n ∉ GenLimit.Generic.sequenceSample history
```

#### `firstUnseenIndex`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3223
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
noncomputable def firstUnseenIndex
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    {t : ℕ} (history : Fin t → α) : ℕ := by
  classical
  exact
    Nat.find
      (exists_enumerated_point_not_seen enumerate henumerate history)
```

#### `firstUnseenIndex_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3232
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem firstUnseenIndex_spec
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    {t : ℕ} (history : Fin t → α) :
    enumerate (firstUnseenIndex enumerate henumerate history) ∉
      GenLimit.Generic.sequenceSample history
```

#### `syntheticContrastiveHistory`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3245
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
noncomputable def syntheticContrastiveHistory
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    {t : ℕ} (history : Fin t → α) : Fin t → Edge α :=
  fun i =>
    ⟨history i,
      enumerate (firstUnseenIndex enumerate henumerate history),
      by
        intro heq
        have hi :
            history i ∈ GenLimit.Generic.sequenceSample history :=
          GenLimit.Generic.mem_sequenceSample_iff.mpr ⟨i, rfl⟩
        have hnot :=
          firstUnseenIndex_spec enumerate henumerate history
        exact hnot (heq ▸ hi)⟩
```

#### `textIdentifierOfContrastive`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3263
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
noncomputable def textIdentifierOfContrastive
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    (I : ContrastiveIdentifier α) :
    GenLimit.Angluin.SemanticIdentifier α :=
  fun _t history =>
    I _ (syntheticContrastiveHistory enumerate henumerate history)
```

#### `firstUnseenIndex_eventually_eq_first_complement`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3271
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem firstUnseenIndex_eventually_eq_first_complement
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    {L : Set α} (k : ℕ)
    (hknot : enumerate k ∉ L)
    (hkmin : ∀ n, n < k → enumerate n ∈ L)
    {stream : GenLimit.Generic.Stream α}
    (hP : GenLimit.Generic.Presents stream L) :
    ∃ T, ∀ t, T ≤ t →
      firstUnseenIndex enumerate henumerate
        (fun i : Fin t => stream i) = k
```

#### `syntheticContrastiveHistory_eq_fixed`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3339
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem syntheticContrastiveHistory_eq_fixed
    [Infinite α] (enumerate : ℕ → α)
    (henumerate : Function.Surjective enumerate)
    {stream : GenLimit.Generic.Stream α} {t k : ℕ}
    (hk :
      firstUnseenIndex enumerate henumerate
        (fun i : Fin t => stream i) = k)
    (hne : ∀ i : Fin t, stream i ≠ enumerate k) :
    syntheticContrastiveHistory enumerate henumerate
        (fun i : Fin t => stream i) =
      fun i : Fin t => (⟨stream i, enumerate k, hne i⟩ : Edge α)
```

#### `lemma_4_6_inclusion`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 3355
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem lemma_4_6_inclusion
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F → TextIdentifiable F
```

#### `commonPresentation_for_noncontained`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3422
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem commonPresentation_for_noncontained
    {h g : Set α}
    (hcover : h ⊆ commonVertices h g)
    (hnsub : ¬h ⊆ g) :
    g ⊆ commonVertices h g
```

#### `contrastiveIdentifiable_nonEliminabilityContained`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 3451
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem contrastiveIdentifiable_nonEliminabilityContained
    [Nonempty α] [Countable α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F)
    (hCtr : ContrastivelyIdentifiable F) :
    NonEliminabilityContained (Set.range F)
```

#### `chosenTellTale`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3503
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
noncomputable def chosenTellTale
    {F : GenLimit.Generic.LanguageFamily α}
    (hTell : GenLimit.Angluin.ConditionTwo F) (i : ℕ) : Finset α :=
  Classical.choose (hTell i)
```

#### `chosenTellTale_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3508
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem chosenTellTale_spec
    {F : GenLimit.Generic.LanguageFamily α}
    (hTell : GenLimit.Angluin.ConditionTwo F) (i : ℕ) :
    GenLimit.Angluin.IsTellTale F i (chosenTellTale hTell i)
```

#### `ContrastiveEligible`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3517
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
def ContrastiveEligible
    (F : GenLimit.Generic.LanguageFamily α)
    (T : ℕ → Finset α)
    {t : ℕ} (history : Fin t → Edge α) (i : ℕ) : Prop :=
  i ≤ t ∧
    (↑(T i) : Set α) ⊆ seenPrefix history ∧
    ∀ r, Crosses (F i) (history r)
```

#### `contrastiveTellTaleLearner`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3526
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
noncomputable def contrastiveTellTaleLearner
    (F : GenLimit.Generic.LanguageFamily α)
    (T : ℕ → Finset α) :
    ContrastiveIdentifier α := by
  classical
  exact fun t history =>
    if h : ∃ i, ContrastiveEligible F T history i then
      Nat.find h
    else
      0
```

#### `contrastiveTellTaleLearner_eligible`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3537
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem contrastiveTellTaleLearner_eligible
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {t : ℕ} {history : Fin t → Edge α}
    (h : ∃ i, ContrastiveEligible F T history i) :
    ContrastiveEligible F T history
      (contrastiveTellTaleLearner F T t history)
```

#### `contrastiveTellTaleLearner_le_of_eligible`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3547
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem contrastiveTellTaleLearner_le_of_eligible
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {t i : ℕ} {history : Fin t → Edge α}
    (hi : ContrastiveEligible F T history i) :
    contrastiveTellTaleLearner F T t history ≤ i
```

#### `finite_vertices_eventually_seen`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3557
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem finite_vertices_eventually_seen
    {stream : ℕ → Edge α} {h : Set α}
    (hstream : IsContrastivePresentation stream h)
    (S : Finset α) (hS : (↑S : Set α) ⊆ h) :
    ∃ T, ∀ t, T ≤ t →
      (↑S : Set α) ⊆ seenPrefix (streamPrefix stream t)
```

#### `eventually_target_contrastiveEligible`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3585
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem eventually_target_contrastiveEligible
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {z : ℕ} {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream (F z))
    (hT : (↑(T z) : Set α) ⊆ F z) :
    ∃ N, ∀ t, N ≤ t →
      ContrastiveEligible F T (streamPrefix stream t) z
```

#### `incident_member_of_target_of_candidate_consistency`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3603
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem incident_member_of_target_of_candidate_consistency
    {h g : Set α} (hsub : h ⊆ g)
    {e : Edge α} (hh : Crosses h e) (hg : Crosses g e)
    {x : α} (hxg : x ∈ g) (hxinc : Incident x e) :
    x ∈ h
```

#### `eligible_candidate_eq_of_target_subset`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3620
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem eligible_candidate_eq_of_target_subset
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {z i t : ℕ} {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream (F z))
    (hTell : GenLimit.Angluin.IsTellTale F i (T i))
    (hsub : F z ⊆ F i)
    (heligible :
      ContrastiveEligible F T (streamPrefix stream t) i) :
    F i = F z
```

#### `eventually_not_eligible_of_target_not_subset`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3637
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem eventually_not_eligible_of_target_not_subset
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {z i : ℕ} {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream (F z))
    (hrel : NonEliminabilityContained (Set.range F))
    (hnsub : ¬F z ⊆ F i) :
    ∃ N, ∀ t, N ≤ t →
      ¬ContrastiveEligible F T (streamPrefix stream t) i
```

#### `eventually_not_eligible_of_different_language`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3661
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem eventually_not_eligible_of_different_language
    {F : GenLimit.Generic.LanguageFamily α} {T : ℕ → Finset α}
    {z i : ℕ} {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream (F z))
    (hrel : NonEliminabilityContained (Set.range F))
    (hTell : GenLimit.Angluin.IsTellTale F i (T i))
    (hdiff : F i ≠ F z) :
    ∃ N, ∀ t, N ≤ t →
      ¬ContrastiveEligible F T (streamPrefix stream t) i
```

#### `contrastiveTellTaleLearner_identifies`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 3679
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem contrastiveTellTaleLearner_identifies
    {F : GenLimit.Generic.LanguageFamily α}
    (hTell : GenLimit.Angluin.ConditionTwo F)
    (hrel : NonEliminabilityContained (Set.range F)) :
    ContrastivelyIdentifies
      (contrastiveTellTaleLearner F (chosenTellTale hTell)) F
```

#### `contrastivelyIdentifiable_of_text_and_nonEliminability`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 3739
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem contrastivelyIdentifiable_of_text_and_nonEliminability
    [Nonempty α] [Countable α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hText : TextIdentifiable F)
    (hrel : NonEliminabilityContained (Set.range F)) :
    ContrastivelyIdentifiable F
```

#### `theorem_4_7_identifier_equivalence`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 3755
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem theorem_4_7_identifier_equivalence
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F ↔
      TextIdentifiable F ∧
        NonEliminabilityContained (Set.range F)
```

#### `theorem_4_7`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 3776
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/IdentifierCharacterization.lean`

```lean
theorem theorem_4_7
    [Nonempty α] [Countable α] [Infinite α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hproper : AllProperNontrivial F) :
    ContrastivelyIdentifiable F ↔
      TextIdentifiable F ∧
        IncomparablePairsOverlap (Set.range F)
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

#### `UnorderedEdge`

- Kind: `structure`
- Classification: definition or construction
- Bundle line: 3824
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
structure UnorderedEdge (α : Type*) where
  vertices : Finset α
  card_eq_two : vertices.card = 2
```

#### `UnorderedEdge.ext`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3828
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem UnorderedEdge.ext
    {p q : UnorderedEdge α} (h : p.vertices = q.vertices) :
    p = q
```

#### `Edge.unordered`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3836
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
noncomputable def Edge.unordered (e : Edge α) : UnorderedEdge α := by
  classical
  exact ⟨{e.left, e.right}, Finset.card_pair e.ne⟩
```

#### `UnorderedCrosses`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3842
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def UnorderedCrosses (h : Set α) (p : UnorderedEdge α) : Prop :=
  ∃ x, x ∈ p.vertices ∧ x ∈ h ∧
    ∃ y, y ∈ p.vertices ∧ y ∉ h
```

#### `unorderedCrosses_edge_iff`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3846
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem unorderedCrosses_edge_iff
    (h : Set α) (e : Edge α) :
    UnorderedCrosses h e.unordered ↔ Crosses h e
```

#### `exists_orientation`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3869
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem exists_orientation (p : UnorderedEdge α) :
    ∃ e : Edge α, e.unordered = p
```

#### `UnorderedEdge.orient`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3880
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
noncomputable def UnorderedEdge.orient
    (p : UnorderedEdge α) : Edge α :=
  Classical.choose (exists_orientation p)
```

#### `UnorderedEdge.orient_unordered`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3884
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem UnorderedEdge.orient_unordered
    (p : UnorderedEdge α) :
    p.orient.unordered = p
```

#### `unorderedCrosses_orient_iff`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3889
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem unorderedCrosses_orient_iff
    (h : Set α) (p : UnorderedEdge α) :
    Crosses h p.orient ↔ UnorderedCrosses h p
```

#### `distinctUnorderedEdges`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3896
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
noncomputable def distinctUnorderedEdges
    {t : ℕ} (history : Fin t → Edge α) :
    Finset (UnorderedEdge α) := by
  classical
  exact Finset.univ.image (fun i => (history i).unordered)
```

#### `unorderedVertices`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3903
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def unorderedVertices
    (E : Finset (UnorderedEdge α)) : Set α :=
  {x | ∃ p, p ∈ E ∧ x ∈ p.vertices}
```

#### `seenPrefix_eq_unorderedVertices`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3907
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem seenPrefix_eq_unorderedVertices
    {t : ℕ} (history : Fin t → Edge α) :
    seenPrefix history =
      unorderedVertices (distinctUnorderedEdges history)
```

#### `unorderedVersionSpace`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3929
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def unorderedVersionSpace
    (𝓗 : Set (Set α)) (E : Finset (UnorderedEdge α)) :
    Set (Set α) :=
  {h | h ∈ 𝓗 ∧ ∀ p, p ∈ E → UnorderedCrosses h p}
```

#### `unorderedClosure`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3936
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
noncomputable def unorderedClosure
    (𝓗 : Set (Set α)) (E : Finset (UnorderedEdge α)) :
    Set α := by
  classical
  exact
    if (unorderedVersionSpace 𝓗 E).Nonempty then
      {x | ∀ h, h ∈ unorderedVersionSpace 𝓗 E → x ∈ h}
    else
      ∅
```

#### `unorderedClosure_subset_version`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 3946
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem unorderedClosure_subset_version
    {𝓗 : Set (Set α)} {E : Finset (UnorderedEdge α)}
    {h : Set α} (hh : h ∈ unorderedVersionSpace 𝓗 E) :
    unorderedClosure 𝓗 E ⊆ h
```

#### `IsContrastivelyHollow`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3958
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def IsContrastivelyHollow
    (𝓗 : Set (Set α)) (E : Finset (UnorderedEdge α)) : Prop :=
  (unorderedVersionSpace 𝓗 E).Nonempty ∧
    unorderedClosure 𝓗 E ⊆ unorderedVertices E
```

#### `ContrastiveClosureDimensionAtMost`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3964
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def ContrastiveClosureDimensionAtMost
    (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  ∀ E : Finset (UnorderedEdge α),
    IsContrastivelyHollow 𝓗 E → E.card ≤ d
```

#### `FiniteContrastiveClosureDimension`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3970
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def FiniteContrastiveClosureDimension
    (𝓗 : Set (Set α)) : Prop :=
  ∃ d, ContrastiveClosureDimensionAtMost 𝓗 d
```

#### `ContrastiveClosureDimensionEquals`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3977
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def ContrastiveClosureDimensionEquals
    (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  ContrastiveClosureDimensionAtMost 𝓗 d ∧
    ∀ b, ContrastiveClosureDimensionAtMost 𝓗 b → d ≤ b
```

#### `UniformlyContrastivelyGeneratesAt`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3986
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def UniformlyContrastivelyGeneratesAt
    (G : ContrastiveGenerator α) (𝓗 : Set (Set α))
    (d : ℕ) : Prop :=
  ∀ h, h ∈ 𝓗 → ∀ t, ∀ history : Fin t → Edge α,
    (∀ i, Crosses h (history i)) →
    d ≤ (distinctUnorderedEdges history).card →
      G t history ∈ h ∧ G t history ∉ seenPrefix history
```

#### `UniformlyContrastivelyGeneratableAt`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 3995
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def UniformlyContrastivelyGeneratableAt
    (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  ∃ G : ContrastiveGenerator α,
    UniformlyContrastivelyGeneratesAt G 𝓗 d
```

#### `UniformlyContrastivelyGeneratable`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 4002
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def UniformlyContrastivelyGeneratable
    (𝓗 : Set (Set α)) : Prop :=
  ∃ d, UniformlyContrastivelyGeneratableAt 𝓗 d
```

#### `IsLeastPositiveUniformThreshold`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 4010
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
def IsLeastPositiveUniformThreshold
    (𝓗 : Set (Set α)) (d : ℕ) : Prop :=
  0 < d ∧
    UniformlyContrastivelyGeneratableAt 𝓗 d ∧
    ∀ k, 0 < k →
      UniformlyContrastivelyGeneratableAt 𝓗 k → d ≤ k
```

#### `uniformThreshold_mono`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 4017
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem uniformThreshold_mono
    {G : ContrastiveGenerator α} {𝓗 : Set (Set α)}
    {d d' : ℕ} (hdd' : d ≤ d')
    (hG : UniformlyContrastivelyGeneratesAt G 𝓗 d) :
    UniformlyContrastivelyGeneratesAt G 𝓗 d'
```

#### `closureDimensionGenerator`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 4026
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
noncomputable def closureDimensionGenerator
    [Nonempty α] (𝓗 : Set (Set α)) :
    ContrastiveGenerator α := by
  classical
  exact fun _t history =>
    let E := distinctUnorderedEdges history
    if hex :
        ∃ x, x ∈ unorderedClosure 𝓗 E ∧
          x ∉ unorderedVertices E then
      Classical.choose hex
    else
      Classical.choice inferInstance
```

#### `closureDimensionGenerator_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 4039
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem closureDimensionGenerator_spec
    [Nonempty α] {𝓗 : Set (Set α)}
    {t : ℕ} {history : Fin t → Edge α}
    (hex :
      ∃ x,
        x ∈ unorderedClosure 𝓗 (distinctUnorderedEdges history) ∧
        x ∉ unorderedVertices (distinctUnorderedEdges history)) :
    closureDimensionGenerator 𝓗 t history ∈
        unorderedClosure 𝓗 (distinctUnorderedEdges history) ∧
      closureDimensionGenerator 𝓗 t history ∉
        unorderedVertices (distinctUnorderedEdges history)
```

#### `finite_history_target_in_version`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 4053
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem finite_history_target_in_version
    {𝓗 : Set (Set α)} {h : Set α} (hh : h ∈ 𝓗)
    {t : ℕ} {history : Fin t → Edge α}
    (hcross : ∀ i, Crosses h (history i)) :
    h ∈ unorderedVersionSpace 𝓗
      (distinctUnorderedEdges history)
```

#### `fresh_closure_point_of_dimension_bound`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 4068
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem fresh_closure_point_of_dimension_bound
    {𝓗 : Set (Set α)} {d t : ℕ}
    {history : Fin t → Edge α}
    (hbound : ContrastiveClosureDimensionAtMost 𝓗 d)
    (hnonempty :
      (unorderedVersionSpace 𝓗
        (distinctUnorderedEdges history)).Nonempty)
    (hcard : d + 1 ≤ (distinctUnorderedEdges history).card) :
    ∃ x,
      x ∈ unorderedClosure 𝓗
          (distinctUnorderedEdges history) ∧
        x ∉ unorderedVertices
          (distinctUnorderedEdges history)
```

#### `dimensionBound_suffices`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 4093
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem dimensionBound_suffices
    [Nonempty α] {𝓗 : Set (Set α)} {d : ℕ}
    (hbound : ContrastiveClosureDimensionAtMost 𝓗 d) :
    UniformlyContrastivelyGeneratesAt
      (closureDimensionGenerator 𝓗) 𝓗 (d + 1)
```

#### `enumerate_unordered_edges_exactly`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 4115
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem enumerate_unordered_edges_exactly
    (E : Finset (UnorderedEdge α)) :
    distinctUnorderedEdges
        (fun i : Fin E.card =>
          ((E.equivFin.symm i).1).orient) = E
```

#### `orientation_history_crosses`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 4142
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem orientation_history_crosses
    {𝓗 : Set (Set α)} {E : Finset (UnorderedEdge α)}
    {h : Set α} (hh : h ∈ unorderedVersionSpace 𝓗 E) :
    ∀ i : Fin E.card,
      Crosses h ((E.equivFin.symm i).1).orient
```

#### `hollow_obstructs_generator`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 4151
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem hollow_obstructs_generator
    {𝓗 : Set (Set α)} {E : Finset (UnorderedEdge α)}
    (hollow : IsContrastivelyHollow 𝓗 E)
    {G : ContrastiveGenerator α} {d : ℕ}
    (hcard : d ≤ E.card) :
    ¬UniformlyContrastivelyGeneratesAt G 𝓗 d
```

#### `generator_implies_dimension_bound`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 4201
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem generator_implies_dimension_bound
    {𝓗 : Set (Set α)} {d : ℕ}
    {G : ContrastiveGenerator α}
    (hG : UniformlyContrastivelyGeneratesAt G 𝓗 (d + 1)) :
    ContrastiveClosureDimensionAtMost 𝓗 d
```

#### `theorem_5_4_quantitative`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 4215
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem theorem_5_4_quantitative
    [Nonempty α] (𝓗 : Set (Set α)) (d : ℕ) :
    UniformlyContrastivelyGeneratableAt 𝓗 (d + 1) ↔
      ContrastiveClosureDimensionAtMost 𝓗 d
```

#### `theorem_5_4`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 4228
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem theorem_5_4
    [Nonempty α] (𝓗 : Set (Set α)) :
    UniformlyContrastivelyGeneratable 𝓗 ↔
      FiniteContrastiveClosureDimension 𝓗
```

#### `theorem_5_4_sharp_sample_complexity`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 4245
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem theorem_5_4_sharp_sample_complexity
    [Nonempty α] {𝓗 : Set (Set α)} {d : ℕ}
    (hdim : ContrastiveClosureDimensionEquals 𝓗 d) :
    IsLeastPositiveUniformThreshold 𝓗 (d + 1)
```

#### `hollow_cardinality_lower_bound`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 4264
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/ClosureDimension.lean`

```lean
theorem hollow_cardinality_lower_bound
    {𝓗 : Set (Set α)} {E : Finset (UnorderedEdge α)}
    (hollow : IsContrastivelyHollow 𝓗 E) :
    ¬UniformlyContrastivelyGeneratableAt 𝓗 E.card
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

#### `NonuniformlyContrastivelyGenerates`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5036
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
def NonuniformlyContrastivelyGenerates
    (G : ContrastiveGenerator α) (𝓗 : Set (Set α)) : Prop :=
  ∀ h, h ∈ 𝓗 →
    ∃ d, ∀ t, ∀ history : Fin t → Edge α,
      (∀ i, Crosses h (history i)) →
      d ≤ (distinctUnorderedEdges history).card →
        G t history ∈ h ∧ G t history ∉ seenPrefix history
```

#### `NonuniformlyContrastivelyGeneratable`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5045
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
def NonuniformlyContrastivelyGeneratable
    (𝓗 : Set (Set α)) : Prop :=
  ∃ G : ContrastiveGenerator α,
    NonuniformlyContrastivelyGenerates G 𝓗
```

#### `generatorLevel`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5053
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
def generatorLevel
    (G : ContrastiveGenerator α) (𝓗 : Set (Set α))
    (n : ℕ) : Set (Set α) :=
  {h | h ∈ 𝓗 ∧
    ∀ t, ∀ history : Fin t → Edge α,
      (∀ i, Crosses h (history i)) →
      n + 1 ≤ (distinctUnorderedEdges history).card →
        G t history ∈ h ∧ G t history ∉ seenPrefix history}
```

#### `generatorLevel_mono`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5062
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem generatorLevel_mono
    (G : ContrastiveGenerator α) (𝓗 : Set (Set α)) :
    Monotone (generatorLevel G 𝓗)
```

#### `generatorLevels_cover`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5072
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem generatorLevels_cover
    {G : ContrastiveGenerator α} {𝓗 : Set (Set α)}
    (hG : NonuniformlyContrastivelyGenerates G 𝓗) :
    𝓗 = ⋃ n, generatorLevel G 𝓗 n
```

#### `generatorLevel_uniform`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5088
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem generatorLevel_uniform
    {G : ContrastiveGenerator α} {𝓗 : Set (Set α)}
    (n : ℕ) :
    UniformlyContrastivelyGeneratesAt
      G (generatorLevel G 𝓗 n) (n + 1)
```

#### `theorem_5_5_necessity`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 5098
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem theorem_5_5_necessity
    {𝓗 : Set (Set α)}
    (hNonuniform : NonuniformlyContrastivelyGeneratable 𝓗) :
    ∃ classes : ℕ → Set (Set α),
      GenLimit.LiRamanTewari.IsNondecreasingCover 𝓗 classes ∧
      ∀ n, FiniteContrastiveClosureDimension (classes n)
```

#### `selectedClosureBound`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5117
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
noncomputable def selectedClosureBound
    (classes : ℕ → Set (Set α))
    (hdim : ∀ n, FiniteContrastiveClosureDimension (classes n))
    (n : ℕ) : ℕ :=
  Classical.choose (hdim n)
```

#### `selectedClosureBound_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5123
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem selectedClosureBound_spec
    {classes : ℕ → Set (Set α)}
    (hdim : ∀ n, FiniteContrastiveClosureDimension (classes n))
    (n : ℕ) :
    ContrastiveClosureDimensionAtMost
      (classes n) (selectedClosureBound classes hdim n)
```

#### `nonuniformPaddedThreshold`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5133
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
def nonuniformPaddedThreshold
    (bound : ℕ → ℕ) (m : ℕ) : ℕ :=
  m + bound m + 1
```

#### `nonuniformEligibleLevels`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5139
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
def nonuniformEligibleLevels
    (bound : ℕ → ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter
    (fun m => nonuniformPaddedThreshold bound m ≤ k)
```

#### `mem_nonuniformEligibleLevels_iff`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5144
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem mem_nonuniformEligibleLevels_iff
    {bound : ℕ → ℕ} {m k : ℕ} :
    m ∈ nonuniformEligibleLevels bound k ↔
      nonuniformPaddedThreshold bound m ≤ k
```

#### `selectedNonuniformLevel`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5159
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
noncomputable def selectedNonuniformLevel
    (bound : ℕ → ℕ) (k : ℕ)
    (hE : (nonuniformEligibleLevels bound k).Nonempty) : ℕ :=
  (nonuniformEligibleLevels bound k).max' hE
```

#### `selectedNonuniformLevel_mem`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5164
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem selectedNonuniformLevel_mem
    {bound : ℕ → ℕ} {k : ℕ}
    (hE : (nonuniformEligibleLevels bound k).Nonempty) :
    selectedNonuniformLevel bound k hE ∈
      nonuniformEligibleLevels bound k
```

#### `le_selectedNonuniformLevel`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5171
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem le_selectedNonuniformLevel
    {bound : ℕ → ℕ} {m k : ℕ}
    (hm : m ∈ nonuniformEligibleLevels bound k)
    (hE : (nonuniformEligibleLevels bound k).Nonempty) :
    m ≤ selectedNonuniformLevel bound k hE
```

#### `nonuniformClosureGenerator`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5180
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
noncomputable def nonuniformClosureGenerator
    [Nonempty α]
    (classes : ℕ → Set (Set α)) (bound : ℕ → ℕ) :
    ContrastiveGenerator α := by
  classical
  exact fun t history =>
    let k := (distinctUnorderedEdges history).card
    let eligible := nonuniformEligibleLevels bound k
    if hE : eligible.Nonempty then
      closureDimensionGenerator (classes (eligible.max' hE))
        t history
    else
      Classical.choice inferInstance
```

#### `nonuniformClosureGenerator_eq_selected`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5194
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem nonuniformClosureGenerator_eq_selected
    [Nonempty α]
    {classes : ℕ → Set (Set α)} {bound : ℕ → ℕ}
    {t : ℕ} {history : Fin t → Edge α}
    (hE :
      (nonuniformEligibleLevels bound
        (distinctUnorderedEdges history).card).Nonempty) :
    nonuniformClosureGenerator classes bound t history =
      closureDimensionGenerator
        (classes
          (selectedNonuniformLevel bound
            (distinctUnorderedEdges history).card hE))
        t history
```

#### `theorem_5_5_sufficiency`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 5212
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem theorem_5_5_sufficiency
    [Nonempty α] {𝓗 : Set (Set α)}
    {classes : ℕ → Set (Set α)}
    (hcover :
      GenLimit.LiRamanTewari.IsNondecreasingCover 𝓗 classes)
    (hdim : ∀ n,
      FiniteContrastiveClosureDimension (classes n)) :
    NonuniformlyContrastivelyGeneratable 𝓗
```

#### `theorem_5_5`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 5274
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/NonuniformClosure.lean`

```lean
theorem theorem_5_5
    [Nonempty α] (𝓗 : Set (Set α)) :
    NonuniformlyContrastivelyGeneratable 𝓗 ↔
      ∃ classes : ℕ → Set (Set α),
        GenLimit.LiRamanTewari.IsNondecreasingCover 𝓗 classes ∧
        ∀ n, FiniteContrastiveClosureDimension (classes n)
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

#### `freshFromContrastiveGuess`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5329
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
noncomputable def freshFromContrastiveGuess
    (F : Generic.LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite)
    (I : ContrastiveIdentifier α) : ContrastiveGenerator α := by
  classical
  exact fun t history =>
    Classical.choose
      ((hInfinite (I t history)).exists_notMem_finite
        (seenPrefix_finite history))
```

#### `freshFromContrastiveGuess_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5338
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem freshFromContrastiveGuess_spec
    (F : Generic.LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite)
    (I : ContrastiveIdentifier α) {t : ℕ}
    (history : Fin t → Edge α) :
    freshFromContrastiveGuess F hInfinite I t history ∈
        F (I t history) ∧
      freshFromContrastiveGuess F hInfinite I t history ∉
        seenPrefix history
```

#### `contrastiveIdentification_implies_generation`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 5354
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem contrastiveIdentification_implies_generation
    (F : Generic.LanguageFamily α) (hInfinite : ∀ i, (F i).Infinite) :
    ContrastivelyIdentifiable F →
      ContrastivelyGeneratable (Set.range F)
```

#### `freshFromTextGuess`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5379
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
noncomputable def freshFromTextGuess
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite)
    (M : GenLimit.Angluin.SemanticIdentifier α) :
    Generic.Generator α := by
  classical
  exact fun _t history =>
    Classical.choose
      ((hInfinite (M _t history)).exists_notMem_finset
        (Generic.sequenceSample history))
```

#### `freshFromTextGuess_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5390
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem freshFromTextGuess_spec
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite)
    (M : GenLimit.Angluin.SemanticIdentifier α)
    {t : ℕ} (history : Fin t → α) :
    freshFromTextGuess F hInfinite M t history ∈ F (M t history) ∧
      freshFromTextGuess F hInfinite M t history ∉
        Generic.sequenceSample history
```

#### `textIdentification_implies_generation`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 5405
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem textIdentification_implies_generation
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    TextIdentifiable F →
      GenLimit.LiRamanTewari.GeneratableInLimit (Set.range F)
```

#### `listIdentifierOfSemantic`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5436
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
def listIdentifierOfSemantic
    (M : GenLimit.Angluin.SemanticIdentifier ℕ) :
    List ℕ → ℕ :=
  fun xs => M xs.length xs.get
```

#### `listIdentifierOfSemantic_prefix`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5441
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem listIdentifierOfSemantic_prefix
    (M : GenLimit.Angluin.SemanticIdentifier ℕ)
    (stream : Stream ℕ) (t : ℕ) :
    listIdentifierOfSemantic M
        (GenLimit.Angluin.streamPrefix stream t) =
      GenLimit.Angluin.identifierOutput M stream t
```

#### `semanticIdentification_implies_conditionTwo`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5488
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem semanticIdentification_implies_conditionTwo
    (F : Generic.LanguageFamily ℕ)
    (hNonempty : GenLimit.Angluin.AllNonempty F)
    (hIdentifiable :
      ∃ M : GenLimit.Angluin.SemanticIdentifier ℕ,
        GenLimit.Angluin.SemanticallyIdentifies M F) :
    GenLimit.Angluin.ConditionTwo F
```

#### `IsSharedPresentation`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5539
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
def IsSharedPresentation
    (stream : ℕ → Edge α) (family : Finset (Set α)) : Prop :=
  ∀ h, h ∈ family → IsContrastivePresentation stream h
```

#### `IsFiniteFamilyIntersection`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5544
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
def IsFiniteFamilyIntersection
    (family : Finset (Set α)) (core : Finset α) : Prop :=
  ∀ x, x ∈ core ↔ ∀ h, h ∈ family → x ∈ h
```

#### `proposition_5_12`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 5551
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem proposition_5_12
    {𝓗 : Set (Set α)} {family : Finset (Set α)}
    {core : Finset α} {stream : ℕ → Edge α}
    (hfamilyNonempty : family.Nonempty)
    (hfamilyClass : ∀ h, h ∈ family → h ∈ 𝓗)
    (hshared : IsSharedPresentation stream family)
    (hcore : IsFiniteFamilyIntersection family core) :
    ¬ContrastivelyGeneratable 𝓗
```

#### `puncturedCore`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5610
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
def puncturedCore (m : ℕ) : ℕ := 2 * m
```

#### `puncturedCore_injective`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5612
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem puncturedCore_injective : Function.Injective puncturedCore
```

#### `puncturedFamily`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5617
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
def puncturedFamily : Generic.LanguageFamily ℕ
  | 0 => Set.range puncturedCore
  | m + 1 => Set.range puncturedCore \ {puncturedCore m}
```

#### `puncturedFamily_nonempty`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5621
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem puncturedFamily_nonempty :
    GenLimit.Angluin.AllNonempty puncturedFamily
```

#### `puncturedCore_eventual`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5636
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem puncturedCore_eventual :
    IsEventualCore (Set.range puncturedFamily) puncturedCore
```

#### `punctured_contrastivelyGeneratable`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 5665
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem punctured_contrastivelyGeneratable :
    ContrastivelyGeneratable (Set.range puncturedFamily)
```

#### `punctured_no_tellTale_at_zero`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 5670
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem punctured_no_tellTale_at_zero
    (T : Finset ℕ)
    (hT : GenLimit.Angluin.IsTellTale puncturedFamily 0 T) :
    False
```

#### `punctured_not_conditionTwo`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 5701
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem punctured_not_conditionTwo :
    ¬GenLimit.Angluin.ConditionTwo puncturedFamily
```

#### `punctured_not_textIdentifiable`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 5709
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem punctured_not_textIdentifiable :
    ¬TextIdentifiable puncturedFamily
```

#### `theorem_5_13_5_14_punctured_witness`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 5718
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/Hierarchy.lean`

```lean
theorem theorem_5_13_5_14_punctured_witness :
    ContrastivelyGeneratable (Set.range puncturedFamily) ∧
      ¬TextIdentifiable puncturedFamily ∧
      ¬ContrastivelyIdentifiable puncturedFamily
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

#### `evenSupport`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5770
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
def evenSupport : Set ℕ := Set.range (fun n => 2 * n)
```

#### `oddSupport`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5773
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
def oddSupport : Set ℕ := Set.range (fun n => 2 * n + 1)
```

#### `evenSupport_infinite`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5775
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem evenSupport_infinite : evenSupport.Infinite
```

#### `oddSupport_infinite`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5781
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem oddSupport_infinite : oddSupport.Infinite
```

#### `evenSupport_disjoint_oddSupport`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5787
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem evenSupport_disjoint_oddSupport :
    Disjoint evenSupport oddSupport
```

#### `disjointFamily`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5798
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
def disjointFamily : Generic.LanguageFamily ℕ
  | 0 => evenSupport
  | _ + 1 => oddSupport
```

#### `disjointFamily_infinite`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5802
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem disjointFamily_infinite (i : ℕ) :
    (disjointFamily i).Infinite
```

#### `disjointPairStream`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5809
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
def disjointPairStream (n : ℕ) : Edge ℕ :=
  ⟨2 * n, 2 * n + 1, by omega⟩
```

#### `disjointPairStream_crosses_even`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5812
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem disjointPairStream_crosses_even (n : ℕ) :
    Crosses evenSupport (disjointPairStream n)
```

#### `disjointPairStream_crosses_odd`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5822
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem disjointPairStream_crosses_odd (n : ℕ) :
    Crosses oddSupport (disjointPairStream n)
```

#### `disjointPairStream_presents_even`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5832
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem disjointPairStream_presents_even :
    IsContrastivePresentation disjointPairStream evenSupport
```

#### `disjointPairStream_presents_odd`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5840
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem disjointPairStream_presents_odd :
    IsContrastivePresentation disjointPairStream oddSupport
```

#### `disjointTextIdentifier`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5849
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
noncomputable def disjointTextIdentifier :
    GenLimit.Angluin.SemanticIdentifier ℕ := by
  classical
  exact fun t history =>
    if ht : t = 0 then 0
    else if history ⟨0, Nat.pos_of_ne_zero ht⟩ ∈ evenSupport then 0
    else 1
```

#### `disjointTextIdentifier_identifies`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 5857
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem disjointTextIdentifier_identifies :
    GenLimit.Angluin.SemanticallyIdentifies
      disjointTextIdentifier disjointFamily
```

#### `disjoint_textIdentifiable`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 5884
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem disjoint_textIdentifiable :
    TextIdentifiable disjointFamily
```

#### `disjoint_not_contrastivelyGeneratable`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 5888
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem disjoint_not_contrastivelyGeneratable :
    ¬ContrastivelyGeneratable (Set.range disjointFamily)
```

#### `theorem_5_13_5_14_disjoint_witness`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 5923
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DisjointHierarchy.lean`

```lean
theorem theorem_5_13_5_14_disjoint_witness :
    TextIdentifiable disjointFamily ∧
      GenLimit.LiRamanTewari.GeneratableInLimit
        (Set.range disjointFamily) ∧
      ¬ContrastivelyGeneratable (Set.range disjointFamily)
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

#### `IsKCorruptedTextPresentation`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5960
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
def IsKCorruptedTextPresentation
    (k : ℕ) (stream : Generic.Stream α) (h : Set α) : Prop :=
  {n : ℕ | stream n ∉ h}.Finite ∧
    {n : ℕ | stream n ∉ h}.ncard ≤ k ∧
    h ⊆ Set.range stream
```

#### `IsKCorruptedContrastivePresentation`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5968
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
def IsKCorruptedContrastivePresentation
    (k : ℕ) (stream : ℕ → Edge α) (h : Set α) : Prop :=
  {n : ℕ | ¬Crosses h (stream n)}.Finite ∧
    {n : ℕ | ¬Crosses h (stream n)}.ncard ≤ k ∧
    h ⊆ {x | ∃ n, Incident x (stream n)}
```

#### `KTextIdentifiesFrom`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5977
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
def KTextIdentifiesFrom
    (k : ℕ) (M : GenLimit.Angluin.SemanticIdentifier α)
    (F : Generic.LanguageFamily α) (z : ℕ)
    (stream : Generic.Stream α) : Prop :=
  IsKCorruptedTextPresentation k stream (F z) →
    ∃ j, F j = F z ∧
      GenLimit.Angluin.ConvergesTo M stream j
```

#### `KTextIdentifiable`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5986
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
def KTextIdentifiable
    (k : ℕ) (F : Generic.LanguageFamily α) : Prop :=
  ∃ M : GenLimit.Angluin.SemanticIdentifier α,
    ∀ z stream, KTextIdentifiesFrom k M F z stream
```

#### `KContrastivelyIdentifiesFrom`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 5993
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
def KContrastivelyIdentifiesFrom
    (k : ℕ) (I : ContrastiveIdentifier α)
    (F : Generic.LanguageFamily α) (z : ℕ)
    (stream : ℕ → Edge α) : Prop :=
  IsKCorruptedContrastivePresentation k stream (F z) →
    ContrastivelyIdentifiesFrom I F z stream
```

#### `KContrastivelyIdentifiable`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6001
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
def KContrastivelyIdentifiable
    (k : ℕ) (F : Generic.LanguageFamily α) : Prop :=
  ∃ I : ContrastiveIdentifier α,
    ∀ z stream, KContrastivelyIdentifiesFrom k I F z stream
```

#### `FinitelyCorruptionContrastivelyIdentifiable`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6008
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
def FinitelyCorruptionContrastivelyIdentifiable
    (F : Generic.LanguageFamily α) : Prop :=
  ∃ I : ContrastiveIdentifier α,
    ∀ k z stream, KContrastivelyIdentifiesFrom k I F z stream
```

#### `coSingletonSupport`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6015
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
def coSingletonSupport (s : α) : Set α := {x | x ≠ s}
```

#### `coSingletonFamily`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6018
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
def coSingletonFamily : Generic.LanguageFamily ℕ :=
  coSingletonSupport
```

#### `coSingletonSupport_ne`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6021
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
theorem coSingletonSupport_ne
    {s t : α} (hst : s ≠ t) :
    coSingletonSupport s ≠ coSingletonSupport t
```

#### `identity_is_oneCorruptedText`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 6029
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
theorem identity_is_oneCorruptedText
    (s : ℕ) :
    IsKCorruptedTextPresentation 1 (fun n : ℕ => n)
      (coSingletonSupport s)
```

#### `theorem_6_5`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 6049
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedPresentations.lean`

```lean
theorem theorem_6_5 :
    ¬KTextIdentifiable 1 coSingletonFamily
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

#### `instDecidableIncident`

- Kind: `instance`
- Classification: representation/decidability instance
- Bundle line: 6093
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
instance instDecidableIncident [DecidableEq α]
    (x : α) (e : Edge α) : Decidable (Incident x e)
```

#### `instDecidableCrossesCoSingleton`

- Kind: `instance`
- Classification: representation/decidability instance
- Bundle line: 6098
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
instance instDecidableCrossesCoSingleton [DecidableEq α]
    (s : α) (e : Edge α) :
    Decidable (Crosses (coSingletonSupport s) e)
```

#### `seenEndpoints`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6105
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
def seenEndpoints [DecidableEq α]
    {t : ℕ} (history : Fin t → Edge α) : Finset α :=
  (Finset.univ.image fun i => (history i).left) ∪
    (Finset.univ.image fun i => (history i).right)
```

#### `absenceCount`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6111
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
def absenceCount [DecidableEq α]
    {t : ℕ} (history : Fin t → Edge α) (x : α) : ℕ :=
  (Finset.univ.filter fun i => ¬Incident x (history i)).card
```

#### `streamAbsenceCount`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6116
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
def streamAbsenceCount [DecidableEq α]
    (stream : ℕ → Edge α) (x : α) (t : ℕ) : ℕ :=
  ((Finset.range t).filter fun i => ¬Incident x (stream i)).card
```

#### `absenceCount_streamPrefix`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6120
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem absenceCount_streamPrefix
    [DecidableEq α]
    (stream : ℕ → Edge α) (x : α) (t : ℕ) :
    absenceCount (streamPrefix stream t) x =
      streamAbsenceCount stream x t
```

#### `mem_seenEndpoints_iff`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6140
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem mem_seenEndpoints_iff
    [DecidableEq α]
    {t : ℕ} {history : Fin t → Edge α} {x : α} :
    x ∈ seenEndpoints history ↔
      ∃ i, Incident x (history i)
```

#### `crosses_coSingletonSupport_iff_incident`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6160
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem crosses_coSingletonSupport_iff_incident
    (s : α) (e : Edge α) :
    Crosses (coSingletonSupport s) e ↔ Incident s e
```

#### `trueCenter_absence_indices_subset_bad`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6176
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem trueCenter_absence_indices_subset_bad
    [DecidableEq α]
    (stream : ℕ → Edge α) (s : α) (t : ℕ) :
    ((Finset.range t).filter fun i => ¬Incident s (stream i)) ⊆
      ((Finset.range t).filter fun i =>
        ¬Crosses (coSingletonSupport s) (stream i))
```

#### `trueCenter_streamAbsenceCount_le`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6189
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem trueCenter_streamAbsenceCount_le
    {k s t : ℕ} {stream : ℕ → Edge ℕ}
    (hP :
      IsKCorruptedContrastivePresentation k stream
        (coSingletonSupport s)) :
    streamAbsenceCount stream s t ≤ k
```

#### `verticesAtIndices`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6219
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
def verticesAtIndices
    (stream : ℕ → Edge α) (I : Set ℕ) : Set α :=
  (fun n => (stream n).left) '' I ∪
    (fun n => (stream n).right) '' I
```

#### `verticesAtIndices_finite`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6224
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem verticesAtIndices_finite
    {stream : ℕ → Edge α} {I : Set ℕ} (hI : I.Finite) :
    (verticesAtIndices stream I).Finite
```

#### `mem_verticesAtIndices_of_incident`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6230
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem mem_verticesAtIndices_of_incident
    {stream : ℕ → Edge α} {I : Set ℕ} {n : ℕ} {x : α}
    (hn : n ∈ I) (hx : Incident x (stream n)) :
    x ∈ verticesAtIndices stream I
```

#### `incident_eq_of_two_distinct_incident`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6238
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem incident_eq_of_two_distinct_incident
    {e : Edge α} {s x u : α}
    (hsx : s ≠ x)
    (hs : Incident s e) (hx : Incident x e)
    (hu : Incident u e) :
    u = s ∨ u = x
```

#### `falseCenter_omission_indices_infinite`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6258
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem falseCenter_omission_indices_infinite
    {k s x : ℕ} {stream : ℕ → Edge ℕ}
    (hxs : x ≠ s)
    (hP :
      IsKCorruptedContrastivePresentation k stream
        (coSingletonSupport s)) :
    {n : ℕ | ¬Incident x (stream n)}.Infinite
```

#### `eventually_streamAbsenceCount_gt`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6312
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem eventually_streamAbsenceCount_gt
    [DecidableEq α]
    {stream : ℕ → Edge α} {x : α}
    (hinfinite : {n : ℕ | ¬Incident x (stream n)}.Infinite)
    (k : ℕ) :
    ∃ T, ∀ t, T ≤ t →
      k < streamAbsenceCount stream x t
```

#### `trueCenter_eventually_seen`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6341
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem trueCenter_eventually_seen
    {k s : ℕ} {stream : ℕ → Edge ℕ}
    (hP :
      IsKCorruptedContrastivePresentation k stream
        (coSingletonSupport s)) :
    ∃ T, ∀ t, T ≤ t →
      s ∈ seenEndpoints (streamPrefix stream t)
```

#### `absenceCountIdentifier`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6364
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
noncomputable def absenceCountIdentifier : ContrastiveIdentifier ℕ :=
  fun _t history => by
    classical
    by_cases hseen : (seenEndpoints history).Nonempty
    · exact Classical.choose
        (Finset.exists_min_image
          (seenEndpoints history)
          (fun x => absenceCount history x) hseen)
    · exact 0
```

#### `absenceCountIdentifier_mem`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6374
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem absenceCountIdentifier_mem
    {t : ℕ} {history : Fin t → Edge ℕ}
    (hseen : (seenEndpoints history).Nonempty) :
    absenceCountIdentifier t history ∈ seenEndpoints history
```

#### `absenceCountIdentifier_minimal`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6386
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem absenceCountIdentifier_minimal
    {t : ℕ} {history : Fin t → Edge ℕ}
    (hseen : (seenEndpoints history).Nonempty)
    {x : ℕ} (hx : x ∈ seenEndpoints history) :
    absenceCount history (absenceCountIdentifier t history) ≤
      absenceCount history x
```

#### `seen_early_of_streamAbsenceCount_le`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6403
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem seen_early_of_streamAbsenceCount_le
    [DecidableEq α]
    {stream : ℕ → Edge α} {x : α} {t k : ℕ}
    (hx : x ∈ seenEndpoints (streamPrefix stream t))
    (hcount : streamAbsenceCount stream x t ≤ k) :
    x ∈ seenEndpoints (streamPrefix stream (k + 1))
```

#### `competitorThreshold`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6442
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
private noncomputable def competitorThreshold
    {k s : ℕ} {stream : ℕ → Edge ℕ}
    (hP :
      IsKCorruptedContrastivePresentation k stream
        (coSingletonSupport s))
    (x : ℕ) : ℕ := by
  classical
  by_cases hxs : x = s
  · exact 0
  · exact Classical.choose
      (eventually_streamAbsenceCount_gt
        (falseCenter_omission_indices_infinite hxs hP) k)
```

#### `competitorThreshold_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6455
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
private theorem competitorThreshold_spec
    {k s x : ℕ} {stream : ℕ → Edge ℕ}
    (hP :
      IsKCorruptedContrastivePresentation k stream
        (coSingletonSupport s))
    (hxs : x ≠ s) :
    ∀ t, competitorThreshold hP x ≤ t →
      k < streamAbsenceCount stream x t
```

#### `earlyCandidates_nonempty`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6469
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
private theorem earlyCandidates_nonempty
    [DecidableEq α]
    (stream : ℕ → Edge α) (k : ℕ) :
    (seenEndpoints
      (streamPrefix stream (k + 1))).Nonempty
```

#### `theorem_6_6`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 6482
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem theorem_6_6 :
    FinitelyCorruptionContrastivelyIdentifiable
      coSingletonFamily
```

#### `example67Edge`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6550
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
private def example67Edge (a b : ℕ) (hab : a ≠ b) : Edge ℕ :=
  ⟨a, b, hab⟩
```

#### `example67History`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6554
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
def example67History : Fin 6 → Edge ℕ
  | ⟨0, _⟩ => example67Edge 3 0 (by omega)
  | ⟨1, _⟩ => example67Edge 3 1 (by omega)
  | ⟨2, _⟩ => example67Edge 0 4 (by omega)
  | ⟨3, _⟩ => example67Edge 3 2 (by omega)
  | ⟨4, _⟩ => example67Edge 3 4 (by omega)
  | ⟨5, _⟩ => example67Edge 3 5 (by omega)
```

#### `example_6_7_absence_counts`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 6563
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem example_6_7_absence_counts :
    absenceCount example67History 0 = 4 ∧
    absenceCount example67History 1 = 5 ∧
    absenceCount example67History 2 = 5 ∧
    absenceCount example67History 3 = 1 ∧
    absenceCount example67History 4 = 4 ∧
    absenceCount example67History 5 = 5
```

#### `example_6_7_unique_minimizer`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 6574
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/AbsenceCount.lean`

```lean
theorem example_6_7_unique_minimizer :
    3 ∈ seenEndpoints example67History ∧
      ∀ x ∈ seenEndpoints example67History,
        x ≠ 3 → absenceCount example67History 3 <
          absenceCount example67History x
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

#### `isKCorruptedTextPresentation_mono`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6617
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem isKCorruptedTextPresentation_mono
    {k ℓ : ℕ} (hkl : k ≤ ℓ)
    {stream : Stream α} {L : Set α}
    (hP : IsKCorruptedTextPresentation k stream L) :
    IsKCorruptedTextPresentation ℓ stream L
```

#### `kTextIdentifiable_antitone`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6624
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem kTextIdentifiable_antitone
    {k ℓ : ℕ} (hkl : k ≤ ℓ)
    {F : Generic.LanguageFamily α}
    (hF : KTextIdentifiable ℓ F) :
    KTextIdentifiable k F
```

#### `coSingleton_kContrastivelyIdentifiable`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 6635
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem coSingleton_kContrastivelyIdentifiable (k : ℕ) :
    KContrastivelyIdentifiable k coSingletonFamily
```

#### `coSingleton_not_kTextIdentifiable`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 6640
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem coSingleton_not_kTextIdentifiable
    {k : ℕ} (hk : 1 ≤ k) :
    ¬KTextIdentifiable k coSingletonFamily
```

#### `robustCommonCore`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6649
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
def robustCommonCore : Set ℕ :=
  Set.range fun n => 4 * n
```

#### `robustBlockPoint`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6653
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
def robustBlockPoint (i : ℕ) {k : ℕ} (r : Fin (k + 1)) : ℕ :=
  4 * Nat.pair i r.val + 2
```

#### `robustBlock`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6657
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
def robustBlock (k i : ℕ) : Finset ℕ :=
  Finset.univ.image fun r : Fin (k + 1) =>
    robustBlockPoint i r
```

#### `robustBlockSupport`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6662
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
def robustBlockSupport (k i : ℕ) : Set ℕ :=
  robustCommonCore ∪ (robustBlock k i : Set ℕ)
```

#### `robustBlockFamily`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6666
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
def robustBlockFamily (k : ℕ) : Generic.LanguageFamily ℕ :=
  robustBlockSupport k
```

#### `robustBlockPoint_pair_injective`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6669
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockPoint_pair_injective
    {k i j : ℕ} {r q : Fin (k + 1)}
    (h : robustBlockPoint i r = robustBlockPoint j q) :
    i = j ∧ r = q
```

#### `robustBlockPoint_fixed_injective`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6683
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockPoint_fixed_injective
    (k i : ℕ) :
    Function.Injective (fun r : Fin (k + 1) =>
      robustBlockPoint i r)
```

#### `robustBlock_card`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6690
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlock_card (k i : ℕ) :
    (robustBlock k i).card = k + 1
```

#### `mem_robustBlock_iff`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6697
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem mem_robustBlock_iff
    {k i x : ℕ} :
    x ∈ robustBlock k i ↔
      ∃ r : Fin (k + 1), robustBlockPoint i r = x
```

#### `robustCommonCore_infinite`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6703
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustCommonCore_infinite :
    robustCommonCore.Infinite
```

#### `robustBlockSupport_infinite`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6710
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockSupport_infinite
    (k i : ℕ) :
    (robustBlockSupport k i).Infinite
```

#### `robustBlockPoint_not_mem_commonCore`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6715
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockPoint_not_mem_commonCore
    {k i : ℕ} (r : Fin (k + 1)) :
    robustBlockPoint i r ∉ robustCommonCore
```

#### `robustBlockPoint_mem_own`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6723
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockPoint_mem_own
    {k i : ℕ} (r : Fin (k + 1)) :
    robustBlockPoint i r ∈ robustBlock k i
```

#### `robustBlockPoint_not_mem_other`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6728
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockPoint_not_mem_other
    {k i j : ℕ} (hij : i ≠ j) (r : Fin (k + 1)) :
    robustBlockPoint i r ∉ robustBlock k j
```

#### `robustBlockPoint_not_mem_otherSupport`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6735
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockPoint_not_mem_otherSupport
    {k i j : ℕ} (hij : i ≠ j) (r : Fin (k + 1)) :
    robustBlockPoint i r ∉ robustBlockSupport k j
```

#### `robustBlockSupport_ne`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6742
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockSupport_ne
    {k i j : ℕ} (hij : i ≠ j) :
    robustBlockSupport k i ≠ robustBlockSupport k j
```

#### `finset_eventually_subset_sample_of_subset_range`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6759
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem finset_eventually_subset_sample_of_subset_range
    {stream : Stream α} (F : Finset α)
    (hF : (F : Set α) ⊆ Set.range stream) :
    ∃ T, ∀ t, T ≤ t → F ⊆ Generic.sample stream t
```

#### `CompleteRobustBlock`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6789
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
def CompleteRobustBlock
    (k i : ℕ) {t : ℕ} (history : Fin t → ℕ) : Prop :=
  robustBlock k i ⊆ sequenceSample history
```

#### `robustBlockTextIdentifier`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6795
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
noncomputable def robustBlockTextIdentifier
    (k : ℕ) : GenLimit.Angluin.SemanticIdentifier ℕ :=
  fun _t history => by
    classical
    by_cases h : ∃ i, CompleteRobustBlock k i history
    · exact Classical.choose h
    · exact 0
```

#### `robustBlockTextIdentifier_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6803
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockTextIdentifier_spec
    {k t : ℕ} {history : Fin t → ℕ}
    (h : ∃ i, CompleteRobustBlock k i history) :
    CompleteRobustBlock k
      (robustBlockTextIdentifier k t history) history
```

#### `completeRobustBlock_eq_target`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6814
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem completeRobustBlock_eq_target
    {k i j t : ℕ} {stream : Stream ℕ}
    (hP :
      IsKCorruptedTextPresentation k stream
        (robustBlockSupport k i))
    (hcomplete : robustBlock k j ⊆ Generic.sample stream t) :
    j = i
```

#### `robustBlock_kTextIdentifiable`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 6880
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlock_kTextIdentifiable (k : ℕ) :
    KTextIdentifiable k (robustBlockFamily k)
```

#### `robustCoreEdge`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6917
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
def robustCoreEdge (n : ℕ) : Edge ℕ :=
  ⟨4 * n, 4 * n + 1, by omega⟩
```

#### `robustCyclingIndex`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6920
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
def robustCyclingIndex (k n : ℕ) : Fin (k + 1) :=
  ⟨n % (k + 1), Nat.mod_lt _ (Nat.zero_lt_succ k)⟩
```

#### `robustBlockEdge`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6923
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
def robustBlockEdge (k n : ℕ) : Edge ℕ :=
  ⟨robustBlockPoint 0 (robustCyclingIndex k n),
    robustBlockPoint 1 (robustCyclingIndex k n),
    by
      intro h
      exact Nat.zero_ne_one
        (robustBlockPoint_pair_injective h).1⟩
```

#### `robustSharedStream`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 6933
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
def robustSharedStream (k : ℕ) (n : ℕ) : Edge ℕ :=
  if (Nat.unpair n).1 = 0 then
    robustCoreEdge (Nat.unpair n).2
  else
    robustBlockEdge k (Nat.unpair n).2
```

#### `robustCoreEdge_crosses`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6939
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustCoreEdge_crosses
    (k i n : ℕ) :
    Crosses (robustBlockSupport k i)
      (robustCoreEdge n)
```

#### `robustBlockEdge_crosses_zero`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6954
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockEdge_crosses_zero
    (k n : ℕ) :
    Crosses (robustBlockSupport k 0)
      (robustBlockEdge k n)
```

#### `robustBlockEdge_crosses_one`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6965
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlockEdge_crosses_one
    (k n : ℕ) :
    Crosses (robustBlockSupport k 1)
      (robustBlockEdge k n)
```

#### `robustSharedStream_crosses_zero`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6976
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustSharedStream_crosses_zero
    (k n : ℕ) :
    Crosses (robustBlockSupport k 0)
      (robustSharedStream k n)
```

#### `robustSharedStream_crosses_one`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6985
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustSharedStream_crosses_one
    (k n : ℕ) :
    Crosses (robustBlockSupport k 1)
      (robustSharedStream k n)
```

#### `robustSharedStream_covers_zero`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 6994
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustSharedStream_covers_zero
    (k : ℕ) :
    robustBlockSupport k 0 ⊆
      {x | ∃ n, Incident x (robustSharedStream k n)}
```

#### `robustSharedStream_covers_one`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7009
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustSharedStream_covers_one
    (k : ℕ) :
    robustBlockSupport k 1 ⊆
      {x | ∃ n, Incident x (robustSharedStream k n)}
```

#### `robustSharedStream_presents_zero`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7024
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustSharedStream_presents_zero
    (k : ℕ) :
    IsContrastivePresentation
      (robustSharedStream k) (robustBlockSupport k 0)
```

#### `robustSharedStream_presents_one`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7031
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustSharedStream_presents_one
    (k : ℕ) :
    IsContrastivePresentation
      (robustSharedStream k) (robustBlockSupport k 1)
```

#### `cleanPresentation_is_kCorrupted`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7038
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem cleanPresentation_is_kCorrupted
    (k : ℕ) {stream : ℕ → Edge α} {L : Set α}
    (hP : IsContrastivePresentation stream L) :
    IsKCorruptedContrastivePresentation k stream L
```

#### `not_kContrastivelyIdentifiable_of_shared`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7054
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem not_kContrastivelyIdentifiable_of_shared
    (k : ℕ) {F : Generic.LanguageFamily α}
    {i j : ℕ} (hij : F i ≠ F j)
    {stream : ℕ → Edge α}
    (hi : IsContrastivePresentation stream (F i))
    (hj : IsContrastivePresentation stream (F j)) :
    ¬KContrastivelyIdentifiable k F
```

#### `robustBlock_not_kContrastivelyIdentifiable`

- Kind: `theorem`
- Classification: diagnostic/counterexample/witness claim
- Bundle line: 7076
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem robustBlock_not_kContrastivelyIdentifiable
    (k : ℕ) :
    ¬KContrastivelyIdentifiable k (robustBlockFamily k)
```

#### `theorem_6_8`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 7090
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/CorruptedIncomparability.lean`

```lean
theorem theorem_6_8
    (k : ℕ) (hk : 1 ≤ k) :
    (KContrastivelyIdentifiable k coSingletonFamily ∧
      ¬KTextIdentifiable k coSingletonFamily) ∧
    (KTextIdentifiable k (robustBlockFamily k) ∧
      ¬KContrastivelyIdentifiable k (robustBlockFamily k))
```

### Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

#### `positiveDefectSet`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7145
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
def positiveDefectSet (h g : Set α) : Set α :=
  h \ commonVertices h g
```

#### `defectNumber`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7149
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
noncomputable def defectNumber (h g : Set α) : ℕ∞ :=
  (positiveDefectSet h g).encard
```

#### `wrongCutViolationTimes`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7153
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
def wrongCutViolationTimes
    (g : Set α) (stream : ℕ → Edge α) : Set ℕ :=
  {t | ¬Crosses g (stream t)}
```

#### `wrongCutViolationCount`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7158
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
noncomputable def wrongCutViolationCount
    (g : Set α) (stream : ℕ → Edge α) : ℕ∞ :=
  (wrongCutViolationTimes g stream).encard
```

#### `cleanWrongCutViolationCounts`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7164
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
def cleanWrongCutViolationCounts
    (h g : Set α) : Set ℕ∞ :=
  {c | ∃ stream : ℕ → Edge α,
    IsContrastivePresentation stream h ∧
      wrongCutViolationCount g stream = c}
```

#### `forcedWrongCutViolationInfimum`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7171
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
noncomputable def forcedWrongCutViolationInfimum
    (h g : Set α) : ℕ∞ :=
  sInf (cleanWrongCutViolationCounts h g)
```

#### `ProperNontrivialSupport`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7176
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
def ProperNontrivialSupport (h : Set α) : Prop :=
  h.Nonempty ∧ hᶜ.Nonempty
```

#### `isContrastivePresentation_iff_zeroCorrupted`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7181
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem isContrastivePresentation_iff_zeroCorrupted
    {stream : ℕ → Edge α} {h : Set α} :
    IsContrastivePresentation stream h ↔
      IsKCorruptedContrastivePresentation 0 stream h
```

#### `incident_positive_unique`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7214
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem incident_positive_unique
    {h : Set α} {e : Edge α} {x y : α}
    (he : Crosses h e)
    (hxInc : Incident x e) (hyInc : Incident y e)
    (hx : x ∈ h) (hy : y ∈ h) :
    x = y
```

#### `defectIncidentTime`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7230
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
noncomputable def defectIncidentTime
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h)
    (x : positiveDefectSet h g) : ℕ :=
  Classical.choose (hP.2 x.2.1)
```

#### `defectIncidentTime_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7236
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem defectIncidentTime_spec
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h)
    (x : positiveDefectSet h g) :
    Incident x.1 (stream (defectIncidentTime hP x))
```

#### `defectIncidentTime_is_violation`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7243
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem defectIncidentTime_is_violation
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h)
    (x : positiveDefectSet h g) :
    defectIncidentTime hP x ∈
      wrongCutViolationTimes g stream
```

#### `defectToViolationTime`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7257
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
noncomputable def defectToViolationTime
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h) :
    positiveDefectSet h g →
      wrongCutViolationTimes g stream :=
  fun x =>
    ⟨defectIncidentTime hP x,
      defectIncidentTime_is_violation hP x⟩
```

#### `defectToViolationTime_injective`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7266
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem defectToViolationTime_injective
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h) :
    Function.Injective
      (defectToViolationTime (g := g) hP)
```

#### `defectNumber_le_wrongCutViolationCount`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7286
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem defectNumber_le_wrongCutViolationCount
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h) :
    defectNumber h g ≤ wrongCutViolationCount g stream
```

#### `defectNumber_le_forcedWrongCutViolationInfimum`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7294
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem defectNumber_le_forcedWrongCutViolationInfimum
    (h g : Set α)
    (hCounts : (cleanWrongCutViolationCounts h g).Nonempty) :
    defectNumber h g ≤
      forcedWrongCutViolationInfimum h g
```

#### `exists_commonCrossing_of_proper`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7308
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem exists_commonCrossing_of_proper
    {h g : Set α}
    (hh : ProperNontrivialSupport h)
    (hg : ProperNontrivialSupport g) :
    ∃ e : Edge α, CommonCrossing h g e
```

#### `positiveNondefectSet`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7365
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
def positiveNondefectSet (h g : Set α) : Set α :=
  h ∩ commonVertices h g
```

#### `positiveNondefectSet_nonempty`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7368
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem positiveNondefectSet_nonempty
    {h g : Set α}
    (hh : ProperNontrivialSupport h)
    (hg : ProperNontrivialSupport g) :
    (positiveNondefectSet h g).Nonempty
```

#### `commonEdgeForNondefect`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7383
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
noncomputable def commonEdgeForNondefect
    {h g : Set α} (x : positiveNondefectSet h g) :
    Edge α :=
  Classical.choose x.2.2
```

#### `commonEdgeForNondefect_spec`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7388
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem commonEdgeForNondefect_spec
    {h g : Set α} (x : positiveNondefectSet h g) :
    CommonCrossing h g (commonEdgeForNondefect x) ∧
      Incident x.1 (commonEdgeForNondefect x)
```

#### `edgeForDefect`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7395
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
def edgeForDefect
    {h g : Set α} (z : ↥(hᶜ : Set α))
    (x : positiveDefectSet h g) : Edge α :=
  ⟨x.1, z.1, fun hEq => z.2 (hEq ▸ x.2.1)⟩
```

#### `edgeForDefect_crosses`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7400
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem edgeForDefect_crosses
    {h g : Set α} (z : ↥(hᶜ : Set α))
    (x : positiveDefectSet h g) :
    Crosses h (edgeForDefect z x)
```

#### `edgeForDefect_not_crosses`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7406
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem edgeForDefect_not_crosses
    {h g : Set α} (z : ↥(hᶜ : Set α))
    (x : positiveDefectSet h g) :
    ¬Crosses g (edgeForDefect z x)
```

#### `edgeForPositive`

- Kind: `def`
- Classification: definition or construction
- Bundle line: 7419
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
def edgeForPositive
    {h : Set α} (z : ↥(hᶜ : Set α)) (x : h) :
    Edge α :=
  ⟨x.1, z.1, fun hEq => z.2 (hEq ▸ x.2)⟩
```

#### `edgeForPositive_crosses`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7424
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem edgeForPositive_crosses
    {h : Set α} (z : ↥(hᶜ : Set α)) (x : h) :
    Crosses h (edgeForPositive z x)
```

#### `exists_clean_contrastive_presentation`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7429
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem exists_clean_contrastive_presentation
    [Countable α] {h : Set α}
    (hh : ProperNontrivialSupport h) :
    ∃ stream : ℕ → Edge α,
      IsContrastivePresentation stream h
```

#### `cleanWrongCutViolationCounts_nonempty`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7452
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem cleanWrongCutViolationCounts_nonempty
    [Countable α] {h g : Set α}
    (hh : ProperNontrivialSupport h) :
    (cleanWrongCutViolationCounts h g).Nonempty
```

#### `exists_clean_presentation_wrongCutCount_eq_defect`

- Kind: `theorem`
- Classification: helper or link-condition claim
- Bundle line: 7466
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem exists_clean_presentation_wrongCutCount_eq_defect
    [Countable α] {h g : Set α}
    (hh : ProperNontrivialSupport h)
    (hg : ProperNontrivialSupport g)
    (hDefectFinite : (positiveDefectSet h g).Finite) :
    ∃ stream : ℕ → Edge α,
      IsContrastivePresentation stream h ∧
      wrongCutViolationCount g stream =
        defectNumber h g
```

#### `proposition_6_3_defect_eq_forced_wrong_cut_infimum`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 7573
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem proposition_6_3_defect_eq_forced_wrong_cut_infimum
    [Countable α] {h g : Set α}
    (_hDistinct : h ≠ g)
    (hh : ProperNontrivialSupport h)
    (hg : ProperNontrivialSupport g) :
    forcedWrongCutViolationInfimum h g =
      defectNumber h g
```

#### `proposition_6_3_notEliminable_iff_defectNumber_zero`

- Kind: `theorem`
- Classification: primary/top-level claim
- Bundle line: 7606
- Source label: `GenLimitLean/GenLimit/Paper28_ContrastiveIdentificationAndGeneration/DefectInfimum.lean`

```lean
theorem proposition_6_3_notEliminable_iff_defectNumber_zero
    [Countable α] {h g : Set α}
    (_hDistinct : h ≠ g)
    (hh : ProperNontrivialSupport h)
    (_hg : ProperNontrivialSupport g) :
    NotEliminableFrom g h ↔ defectNumber h g = 0
```
