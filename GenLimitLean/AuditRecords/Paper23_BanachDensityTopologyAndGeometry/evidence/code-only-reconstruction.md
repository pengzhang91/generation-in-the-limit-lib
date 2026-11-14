# P23 — Stage 1 code-only reconstruction
This is a paper-withheld reconstruction of the supplied Lean interfaces. It covers all 13 opaque slots: seven slots map to eight exact theorem targets, and six slots have no supplied endpoint. It does not certify theorem proofs, paper correspondence, fresh compilation, or human review. Names and source-module paths are used only as identifiers and anchors.

The requested configuration is gpt-6.1-sol with xhigh reasoning and task-local context isolation. The backend model revision and independently verified runtime configuration are unobservable. Only the stage1 directory was used as input. No paper, web, source package, registry, PaperMap, prior audit, other stage, independently prepared result, or Git data was read. No agents were spawned and no Lean source was changed. The coordinator, rather than this report, freezes outputs and determines any subsequent stage.

## Input census

The bundle has 40 recursive records: 28 definitions (including two generated natural-number match helpers), eight target theorems, two inductives, and their two constructors. The code-only native census has 325 records: 98 definitions, 215 theorem interfaces, four inductives, four constructors, and four recursors. The 40 recursive records agree with their native-census copies in identifier, kind, module, source line, type, and value. Their listed project dependencies are closed within the recursive bundle. All target identifiers match both targets.txt and the slot-map union. All native theorem values are suppressed.

All 11 files below were read. SHA256SUMS matches all ten files it lists; its own hash is independently recorded here. The source_snapshot_sha256 value in snapshot.json is metadata supplied by the bundle, not a source tree independently opened or hashed by this reviewer.
| Stage 1 input | SHA-256 |
|---|---|
| 01-target-statements.md | f5c146d29b935970abb0ddca6ef9122e4469a0daeb97e7bd963a745c4c0dc701 |
| 02-definition-dependencies.md | d8fbcd6ecf37084cae6c7e91191ae76e1c8ab23818686e758ef686893a3248c8 |
| PROMPT.md | c63aad9d119a37687071a9dd61f3139f0f318647c5237a6cfd05e4ecd3e38de3 |
| SHA256SUMS | 81befe3bac8db77c5b3a01e48d5caa322be79d1ee4b94d4a91279f4f6b440944 |
| START_HERE.md | 52dbb6f80b47a22d94f222fd499cc75c3e793e710b44d74dd69922866c1c02d7 |
| claim-slots.json | 3b5e9914370e1e2fcf4e79a05b35d6d1610c487eca102628e249cc17e5cd63ac |
| declarations.jsonl | e7b456861361b5ccaefeeceeb770ffdf011ba125f2db0e21f27d01747d86466a |
| external-boundary.txt | 4f95ca42c0920824864bd661c21e786c0f937fadaf4e249d3bfc83cf126d0051 |
| native-declaration-census.jsonl | c7fa1cdd18d5da1dddaaac84eabfa02a2e0b3e8a5a8a7e0c25accde7be395caf |
| snapshot.json | 84cc24e2c8a990aff8d285176e9f307ef4c77060b383148f0eb432159eba9f0b |
| targets.txt | e4ac1cd31aa3fb7eb58aad08928b55d09ee53e1db5c8bb1d3be098652d21c131 |

The native census was scanned for its identifiers/kinds and structural consistency. Individual semantic review is limited to the eight targets, the recursive definitions/constructor interfaces below, and the explicitly listed additional native interfaces. It is not a claim that all 325 declarations or their proof steps were reviewed.

## Notation and external boundary

In prose, a point K is identified with its underlying language K.val only when stating set membership/inclusion. B abbreviates GenLimit.KleinbergWei.Banach and T abbreviates GenLimit.KleinbergWei.TowerTopology. Exact identifiers remain explicit in dossiers. D_n denotes T.cbDerivative X n, and C(n) denotes B.prefixLCA vertices n.

Nat, sets/subtypes, finite sets and cardinality, WithTop Nat, ENNReal, infima, atTop liminf, induced semilattice orders and meets, natural recursion, and the other constants listed in external-boundary.txt are trusted standard Lean/Mathlib meanings. No recursive Mathlib audit was attempted. In particular, PredOrder and IsPredArchimedean are kept as exact external typeclass hypotheses; their internals were not supplied. Additional native definitions visibly use Classical.choose and standard finite-set insertion/image operations; these are likewise treated as standard logical/collection operations. Embedded proof placeholders are exporter suppression, not evidence of proof holes.

These targets quantify mathematical objects, not a learner interface. No supplied target states support loss, single-output loss, a distributional law, full support, training access, or a runtime bound. The named construction inspected below has more input information than its enumeration alone.

## Definition glossary

The following exhausts the 32 non-theorem recursive records, including the two inductives and two constructor types. Definition values and constructor interfaces were inspected; no theorem proof body was inspected.

### GenLimit.KleinbergWei.Banach.AdmissibleWindowBound
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:32.

AdmissibleWindowBound f means Monotone f ∧ ∀ k : Nat, 1 ≤ f k, for f : Nat → WithTop Nat. Infinity is allowed, as are constant finite bounds; growth to infinity is not required.

### GenLimit.KleinbergWei.Banach.FiniteRankAtMost
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.Topology:25.

Alias of GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost X R; it says the R-th derivative is empty.

### GenLimit.KleinbergWei.Banach.HasFiniteCBRank
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:30.

HasFiniteCBRank X K r means K ∈ cbLevel X r, namely K ∈ D_r and K ∉ D_(r+1). The level is exact, not merely an upper rank bound.

### GenLimit.KleinbergWei.Banach.Nice
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:13.

For every T : Nat there exist m : Nat and total functions k,a : Nat → Nat such that: 2 ≤ m; for all i,j<m, i≤j implies k i≤k j; for all i,j<m, i<j implies a i<a j; T<a 0; for every i with i+1<m, a i+k i+1≤a(i+1); and for all i<m, a i≤f(k i). No restrictions are placed on k or a at indices ≥m.

### GenLimit.KleinbergWei.Banach.PerfectTower
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.Topology:14.

Alias of GenLimit.KleinbergWei.TowerTopology.PerfectTower X tower terminal; all three constructor conditions below are retained.

### GenLimit.KleinbergWei.Banach.UniversallyUnbounded
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:23.

UniversallyUnbounded f means ∀ M : Nat, ∃ n : Nat, M < f n.

### GenLimit.KleinbergWei.Banach.banachMinimum
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:49.

banachMinimum A k = inf over all m : Nat of (if 1 ≤ m then windowRatio A m k else ∞). Start 0 is excluded.

### GenLimit.KleinbergWei.Banach.lowerBanachDensity
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:54.

lowerBanachDensity A = Filter.liminf (banachMinimum A) Filter.atTop. No ordinary limit is asserted.

### GenLimit.KleinbergWei.Banach.lowerWindowDensity
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:44.

lowerWindowDensity f A = Filter.liminf (windowMinimum f A) Filter.atTop. The asymptotic index is the natural window length k, and the value lies in ENNReal.

### GenLimit.KleinbergWei.Banach.prefixLCA
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:24.

For v : Nat → Vertex, put C(0)=v(0) and C(n+1)=C(n) ⊓ v(n+1). This is the meet of v(0),…,v(n), so index n refers to a nonempty prefix of length n+1. The displayed Min.min is SemilatticeInf.toMin, hence meet rather than the minimum of a separately assumed linear order.

### GenLimit.KleinbergWei.Banach.prefixLCA.match_1
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA (generated; no line supplied).

Generated natural-number eliminator: at 0 use h₁ Unit.unit; at n.succ use h₂ n. It makes the preceding zero/successor recurrence explicit. No source line is supplied for this generated helper.

### GenLimit.KleinbergWei.Banach.prefixLCAChangeIndices
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:85.

prefixLCAChangeIndices v n = {i ∈ Finset.Icc 1 n | C(i) ≠ C(i−1)}. Natural subtraction is harmless here because all retained indices satisfy i≥1.

### GenLimit.KleinbergWei.Banach.windowCount
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:22.

windowCount A m k = card {x ∈ Finset.Ico m (m+k) | x ∈ A}. The interval is [m,m+k), with k positions.

### GenLimit.KleinbergWei.Banach.windowMinimum
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:36.

windowMinimum f A k = inf over all m : Nat of (if 1 ≤ m ∧ (m : WithTop Nat) ≤ f k then windowRatio A m k else ∞). Thus f bounds the starting position m, not the window length k.

### GenLimit.KleinbergWei.Banach.windowRatio
Kind: definition; supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:27.

windowRatio A m k = if k = 0 then 0 else (windowCount A m k : ENNReal) / (k : ENNReal).

### GenLimit.KleinbergWei.TowerTopology.ConvergentProperTower
Kind: inductive; supplied source anchor: GenLimit.Support.KleinbergWei.TowerTopology:191.

A Prop-valued structure characterized by its constructor below. Its name does not impose a monotone inclusion sequence.

### GenLimit.KleinbergWei.TowerTopology.ConvergentProperTower.mk
Kind: constructor; supplied source anchor: GenLimit.Support.KleinbergWei.TowerTopology:191.

Two fields: (1) ∀ n : Nat, (tower n).val ⊊ terminal.val; (2) ∀ u : Nat, u∈terminal.val → ∃ N : Nat, ∀ n : Nat, N≤n → u∈(tower n).val. The threshold may depend on u.

### GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.CantorBendixson:85.

FiniteRankAtMost X R means cbDerivative X R = ∅. In particular R=0 forces Point X empty, since D_0=univ.

### GenLimit.KleinbergWei.TowerTopology.FixesAt
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.TowerTopology:177.

FixesAt tower n u means (∀ m : Nat, n≤m → u∈tower m) ∧ (n=0 ∨ u∉tower(n−1)). It requires permanent membership from n and absence at the immediate predecessor when n>0; it does not prohibit earlier intermittent membership.

### GenLimit.KleinbergWei.TowerTopology.IsLimitPoint
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.TowerTopology:92.

IsLimitPoint K means ∀ O : Set (Point X), KWOpen X O → K∈O → ∃ L : Point X, L∈O ∧ L≠K. This uses the supplied KWOpen definition.

### GenLimit.KleinbergWei.TowerTopology.KWOpen
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.TowerTopology:31.

KWOpen X O means ∀ K : Point X, K∈O → ∃ F : Finset Nat, F⊆K.val ∧ basicNeighborhood X K F ⊆ O.

### GenLimit.KleinbergWei.TowerTopology.PerfectTower
Kind: inductive; supplied source anchor: GenLimit.Support.KleinbergWei.TowerTopology:182.

A Prop-valued structure with exactly the constructor conditions described in PerfectTower.mk. A term is an infinite natural-indexed sequence of points of X with a terminal; no inter-term inclusion chain is a separate field.

### GenLimit.KleinbergWei.TowerTopology.PerfectTower.mk
Kind: constructor; supplied source anchor: GenLimit.Support.KleinbergWei.TowerTopology:182.

Given tower and terminal: (1) ∀ n, (tower n).val ⊊ terminal.val; (2) ∀ n, ∃ u : Nat, u∈terminal.val ∧ FixesAt (fun m => (tower m).val) n u; (3) ∀ u : Nat, u∈terminal.val → ∃ n : Nat, FixesAt (fun m => (tower m).val) n u. These three fields construct PerfectTower X tower terminal.

### GenLimit.KleinbergWei.TowerTopology.Point
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.TowerTopology:17.

Point X = {L : Language // L ∈ X}. Every tower/sequence term and terminal is supplied together with membership in X.

### GenLimit.KleinbergWei.TowerTopology.RelativeLimitPoint
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.CantorBendixson:12.

RelativeLimitPoint Y K means K∈Y ∧ ∀ F : Finset Nat, F⊆K.val → ∃ L : Point X, L∈Y ∧ L≠K ∧ L∈basicNeighborhood X K F. The K∈Y conjunct makes the derivative an internal derivative.

### GenLimit.KleinbergWei.TowerTopology.basicNeighborhood
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.TowerTopology:20.

basicNeighborhood X K F = {L : Point X | (F : Set Nat) ⊆ L.val ∧ L.val ⊆ K.val}. F is a finite set of positive membership requirements; the upper-inclusion condition L⊆K is also essential.

### GenLimit.KleinbergWei.TowerTopology.cbDerivative
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.CantorBendixson:42.

Write D_n = cbDerivative X n. The recurrence is D_0 = Set.univ on Point X and D_(n+1) = derivative D_n.

### GenLimit.KleinbergWei.TowerTopology.cbDerivative.match_1
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.CantorBendixson (generated; no line supplied).

Generated natural-number case splitter: zero uses h₁ Unit.unit, successor n+1 uses h₂ n. The value confirms the displayed derivative recurrence; no source line is supplied.

### GenLimit.KleinbergWei.TowerTopology.cbLevel
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.CantorBendixson:65.

cbLevel X n = cbDerivative X n \ cbDerivative X (n+1) = D_n \ D_(n+1).

### GenLimit.KleinbergWei.TowerTopology.derivative
Kind: definition; supplied source anchor: GenLimit.Support.KleinbergWei.CantorBendixson:20.

derivative Y = {K : Point X | RelativeLimitPoint Y K}.

### GenLimit.Language
Kind: definition; supplied source anchor: GenLimit.Core.Basic:20.

Language = Set Nat. A language may be empty, finite, or infinite; it is not a program, distribution, or indexed family.

### GenLimit.Presents
Kind: definition; supplied source anchor: GenLimit.Core.Basic:26.

Presents e K means Set.range e = K, where e : Nat → Nat. Every stream value belongs to K and every member appears somewhere; neither injectivity nor an appearance rate is required.

## Native procedure and interface inspection

This section distinguishes the existential tower endpoint from a named definition. It does not certify the construction's proof steps.

T.BasisLimitPoint K means that every finite F⊆K has a distinct point L of X with F⊆L⊆K. T.ApproachedFrom Y K additionally requires the chosen L to lie in Y but, unlike RelativeLimitPoint, does not separately require K∈Y. T.relativeApproximant Y K hK enumeration hP n uses Classical.choose to select L∈Y, L≠K in basicNeighborhood X K (sample enumeration (n+1)). GenLimit.sample e t is the finite image of e over Finset.range t, so duplicates collapse and only indices <t are sampled. T.approximant specializes Y to all points of X.

For the adaptive construction, the inspected state contains a finite fixed⊆terminal, a point in X distinct from terminal with fixed⊆point⊆terminal, and a natural missing∈terminal with missing∉point. The fixed, point, and missing projections were inspected. T.adaptiveStageOf terminal hterminal F hF uses Classical.choose once for a point below terminal containing F and again for a missing member of terminal. It returns that state. The choices use full mathematical terminal/X information and the BasisLimitPoint proof; neither a membership-oracle interface nor computable realizers are parameters.

The recursion in T.adaptiveStages starts with T.adaptiveStageOf on {enumeration(0)}. At step n, T.nextFixed is insert stage.missing (insert (enumeration(n+1)) stage.fixed); T.advance invokes adaptiveStageOf again with that set. The generated natural-number matcher confirms zero/successor recursion. T.adaptiveTower outputs each state's point. Thus enumeration values are consumed by finite prefixes, while the point/missing choices remain classical semantic selections. Their state transition does not assert point(n)⊆point(n+1).

The inspected type of T.perfectTower_of_basisLimitPoint separately identifies adaptiveTower as satisfying PerfectTower, given terminal, a BasisLimitPoint proof, the enumeration and its presentation proof. The target B.claim_3_6 only existentially quantifies a tower and does not itself name adaptiveTower. The native T.isLimitPoint_iff_exists_perfectTower type has the same existence shape. T.PerfectTower.toConvergentProperTower is a separate theorem interface. Only these theorem types were read, not their derivations.

B.BasisConverges sequence terminal means every finite F⊆terminal has a threshold after which sequence(n) belongs to basicNeighborhood X terminal F. The inspected B.claim_4_11 interface uses this hypothesis plus ∀n, sequence(n)≠terminal for the same eventual lower-rank conclusion. The supplied target instead takes ConvergentProperTower. These interfaces are recorded separately rather than conflated.

B.prefixLCAChangeCount starts at 0 and adds 0 or 1 depending on whether the next running meet is equal to the current one. The additional B.claim_4_18_change_bound interface bounds this count under the same depth hypotheses. The supplied target bounds the cardinality of prefixLCAChangeIndices. The zero and successor prefixLCA theorem interfaces agree with the inspected recursion.

The exact additional native records individually inspected are:
- GenLimit.KleinbergWei.Banach.BasisConverges — definition; GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:38.
- GenLimit.KleinbergWei.Banach.prefixLCAChangeCount — definition; GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:61.
- GenLimit.KleinbergWei.TowerTopology.BasisLimitPoint — definition; GenLimit.Support.KleinbergWei.TowerTopology:87.
- GenLimit.KleinbergWei.TowerTopology.ApproachedFrom — definition; GenLimit.Support.KleinbergWei.TowerTopology.Converse:13.
- GenLimit.KleinbergWei.TowerTopology.approximant — definition; GenLimit.Support.KleinbergWei.TowerTopology.Converse:73.
- GenLimit.KleinbergWei.TowerTopology.relativeApproximant — definition; GenLimit.Support.KleinbergWei.TowerTopology.Converse:21.
- GenLimit.KleinbergWei.TowerTopology.AdaptiveStage — inductive; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:14.
- GenLimit.KleinbergWei.TowerTopology.AdaptiveStage.mk — constructor; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:14.
- GenLimit.KleinbergWei.TowerTopology.adaptiveStageOf — definition; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:27.
- GenLimit.KleinbergWei.TowerTopology.nextFixed — definition; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:66.
- GenLimit.KleinbergWei.TowerTopology.advance — definition; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:87.
- GenLimit.KleinbergWei.TowerTopology.adaptiveStages — definition; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:112.
- GenLimit.KleinbergWei.TowerTopology.adaptiveTower — definition; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:167.
- GenLimit.KleinbergWei.TowerTopology.perfectTower_of_basisLimitPoint — theorem; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:245.
- GenLimit.KleinbergWei.TowerTopology.isLimitPoint_iff_exists_perfectTower — theorem; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:290.
- GenLimit.KleinbergWei.TowerTopology.PerfectTower.toConvergentProperTower — theorem; GenLimit.Support.KleinbergWei.TowerTopology:196.
- GenLimit.KleinbergWei.Banach.claim_4_11 — theorem; GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:170.
- GenLimit.KleinbergWei.Banach.claim_4_18_change_bound — theorem; GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:167.
- GenLimit.KleinbergWei.Banach.prefixLCA_zero — theorem; GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:29.
- GenLimit.KleinbergWei.Banach.prefixLCA_succ — theorem; GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:35.
- GenLimit.sample — definition; GenLimit.Core.Basic:30.
- GenLimit.KleinbergWei.TowerTopology.adaptiveStages.match_1 — definition; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse (generated; no line supplied).
- GenLimit.KleinbergWei.TowerTopology.AdaptiveStage.fixed — definition; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:16.
- GenLimit.KleinbergWei.TowerTopology.AdaptiveStage.point — definition; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:18.
- GenLimit.KleinbergWei.TowerTopology.AdaptiveStage.missing — definition; GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:22.

## Per-target dossiers

### GenLimit.KleinbergWei.Banach.claim_3_3
Slot: C06. Kind: theorem. Supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:72.

**Exact exported type**

    ∀ {f g : Nat → WithTop.{0} Nat} {A : GenLimit.Language},
      GenLimit.KleinbergWei.Banach.AdmissibleWindowBound f →
        GenLimit.KleinbergWei.Banach.AdmissibleWindowBound g →
          (∀ (k : Nat),
              @LE.le.{0} (WithTop.{0} Nat)
                (@Preorder.toLE.{0} (WithTop.{0} Nat) (@WithTop.preorder.{0} Nat Nat.instPreorder)) (g k) (f k)) →
            @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
              (GenLimit.KleinbergWei.Banach.lowerWindowDensity f A) (GenLimit.KleinbergWei.Banach.lowerWindowDensity g A)

**Precise reconstruction.** For any f,g : Nat→WithTop Nat and A ⊆ Nat, if both f and g are nondecreasing and everywhere at least 1, and g(k)≤f(k) for every k, then lowerWindowDensity f A≤lowerWindowDensity g A in ENNReal. These densities are liminf over window lengths k of the infimum of the normalized A-count in [m,m+k) with starts 1≤m≤the given bound at k, and zero-length ratios are 0.

**Quantifier skeleton and dependencies.** ∀ {f g : Nat→WithTop Nat} {A : Set Nat}, AdmissibleWindowBound f → AdmissibleWindowBound g → (∀k : Nat,g(k)≤f(k)) → lowerWindowDensity f A≤lowerWindowDensity g A. The same A is used on both sides; the result is uniform as a theorem over the supplied data but does not quantify a common program.

**Information and algorithm scope.** Antitonic semantic comparison in the bound on starting positions. No estimator, learner, oracle procedure, convergence rate, or strict inequality is provided.

**Edge cases and boundaries.** For fixed length k, enlarging the admissible bound enlarges the set of eligible starting positions. The direction in the statement is therefore lowerWindowDensity f A≤lowerWindowDensity g A when g≤f. Neither f≤g nor strictness is asserted. Both functions have their own monotonicity and lower-bound hypotheses. Pointwise domination is required at every natural k, not merely eventually.

Admissibility ensures a nonempty set of starts (m=1); f or g may take ∞. k=0 has windowRatio 0 by definition, while the asymptotic filter ignores any fixed finite prefix. Empty A, full A, finite A, and f=g are all covered. No infinite-language, distribution, full-support, freshness, convergence-rate, or ordinary-limit premise is present.

**Definitions inspected.** GenLimit.Language, GenLimit.KleinbergWei.Banach.AdmissibleWindowBound, GenLimit.KleinbergWei.Banach.windowCount, GenLimit.KleinbergWei.Banach.windowRatio, GenLimit.KleinbergWei.Banach.windowMinimum, GenLimit.KleinbergWei.Banach.banachMinimum, GenLimit.KleinbergWei.Banach.lowerWindowDensity, GenLimit.KleinbergWei.Banach.lowerBanachDensity.

**Limitations.** Paper and source claims withheld; theorem proof bodies, fresh compilation, source correspondence, and human certification are outside this review. The comparison is for the supplied ENNReal liminf definitions; it does not assert existence of ordinary limits or constrain f,g to finite values.

### GenLimit.KleinbergWei.Banach.claim_3_5
Slot: C01. Kind: theorem. Supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:111.

**Exact exported type**

    ∀ (A : GenLimit.Language),
      @Eq.{1} ENNReal (GenLimit.KleinbergWei.Banach.lowerBanachDensity A)
        (⨅ f,
          GenLimit.KleinbergWei.Banach.lowerWindowDensity
            (@Subtype.val.{1} (Nat → WithTop.{0} Nat) (fun f => GenLimit.KleinbergWei.Banach.AdmissibleWindowBound f) f) A)

**Precise reconstruction.** For every A ⊆ Nat, the ENNReal liminf, as the window length k tends to infinity, of the infimum of |A∩[m,m+k)|/k over all natural starts m≥1 equals the infimum of the analogous liminf over all nondecreasing f : Nat → WithTop Nat satisfying f(k)≥1, restricting starts to 1≤m≤f(k). Ratios at k=0 are defined as 0. The outer infimum is over admissible functions, not a single finite bound.

**Quantifier skeleton and dependencies.** ∀ A : Set Nat, lowerBanachDensity A = inf {lowerWindowDensity f A | f : Nat → WithTop Nat, Monotone f ∧ ∀k, 1≤f(k)}. No existential witness function or rate is quantified by the target.

**Information and algorithm scope.** Semantic identity of infima and liminf values; arbitrary set membership and arbitrary admissible functions are mathematical inputs. No learner, oracle interface, estimator, program, or computational rate occurs.

**Edge cases and boundaries.** The infimum over bounds is indexed by the subtype {f // AdmissibleWindowBound f}; proofs of admissibility are part of that index, and the value uses f.val. Each admissible bound admits at least the start m=1 at every k, so no eligible-start set is exhausted. Without admissibility, the total definition of windowMinimum would return ∞ at a k with no eligible start. Constant f=1 and constant f=∞ are both allowed. In particular the infinite bound leaves all m≥1 eligible and reproduces banachMinimum at each k; this is a consequence of the definition, not an additional minimizer algorithm in the target.

For empty A the positive-length ratios are 0, and for A=Nat they are 1; the exceptional k=0 term has no effect on the atTop liminf. All windows exclude 0, so changing membership of 0 leaves these quantities unchanged. Finite or exhausted language sets are allowed: no freshness or generation requirement occurs. Infima and liminf do not assert an ordinary limit, sampling law, full support, support loss, or single-output loss.

**Definitions inspected.** GenLimit.Language, GenLimit.KleinbergWei.Banach.AdmissibleWindowBound, GenLimit.KleinbergWei.Banach.windowCount, GenLimit.KleinbergWei.Banach.windowRatio, GenLimit.KleinbergWei.Banach.windowMinimum, GenLimit.KleinbergWei.Banach.banachMinimum, GenLimit.KleinbergWei.Banach.lowerWindowDensity, GenLimit.KleinbergWei.Banach.lowerBanachDensity.

**Limitations.** Paper and source claims withheld; theorem proof bodies, fresh compilation, source correspondence, and human certification are outside this review. Infinity is allowed in f and ENNReal. Ordinary real-valued densities, an attained minimum over finite-valued f, and an actual limit are not asserted.

### GenLimit.KleinbergWei.Banach.claim_3_6
Slot: C02. Kind: theorem. Supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.Topology:57.

**Exact exported type**

    ∀ {X : Set.{0} GenLimit.Language} {terminal : GenLimit.KleinbergWei.TowerTopology.Point X} (enumeration : Nat → Nat),
      GenLimit.Presents enumeration
          (@Subtype.val.{1} GenLimit.Language
            (fun L =>
              @Membership.mem.{0, 0} GenLimit.Language (Set.{0} GenLimit.Language)
                (@Set.instMembership.{0} GenLimit.Language) X L)
            terminal) →
        Iff (@GenLimit.KleinbergWei.TowerTopology.IsLimitPoint X terminal)
          (∃ tower, GenLimit.KleinbergWei.Banach.PerfectTower X tower terminal)

**Precise reconstruction.** For arbitrary X ⊆ Set Nat, terminal K : Point X, and total enumeration e : Nat → Nat with range(e)=K.val, K is a limit point for KWOpen iff there exists tower : Nat → Point X such that every tower(n) is a proper subset of K; every stage n has some u∈K that belongs to all tower(m) for m≥n and, if n>0, is absent from tower(n−1); and every u∈K has some such stage n. All three tower conditions, including the per-stage witness, are part of the conclusion.

**Quantifier skeleton and dependencies.** ∀ {X} {K : Point X}, ∀ e : Nat→Nat, Presents e K.val → (IsLimitPoint K ↔ ∃ tower : Nat→Point X, [∀n, tower(n).val⊊K.val] ∧ [∀n ∃u∈K.val, FixesAt tower n u] ∧ [∀u∈K.val ∃n, FixesAt tower n u]). Stage witnesses may depend on tower and n; fixation times may depend on u. The tower may depend on X,K,e and the limit-point premise.

**Information and algorithm scope.** The target is a logical equivalence with an unspecified tower witness. Separately inspected native adaptiveTower starts with fixed={e(0)}, chooses a proper point below K containing fixed and a missing u∈K, then inserts the missing u and e(n+1) into fixed and chooses again; its outputs are chosen points. adaptiveStageOf uses Classical.choose for both point and missing element. Inputs include X,K and a BasisLimitPoint proof, plus e and its presentation proof; enumeration alone is not the complete input. No computability, finite oracle reduction, or resource bound is certified.

**Edge cases and boundaries.** KWOpen is defined from the neighborhoods {L∈X | F⊆L⊆K}, with F finite and F⊆K. It does not inspect negative examples one at a time: the upper inclusion L⊆K is present in each neighborhood definition. IsLimitPoint requires every such open neighborhood of K to contain a distinct point of X. Both directions of the equivalence are under the same supplied presentation premise.

FixesAt n u means permanent membership from n, plus n=0 or absence at n−1. It does not mean first-ever occurrence. The two tower witness clauses differ: every stage must permanently introduce some member, and every terminal member must eventually be permanently present. The first clause cannot be replaced by mere convergence. There is no explicit inter-term subset chain. Nonetheless a later fresh permanent witness rules out equal tower terms at different indices. Thus these conditions are stronger than permitting an eventually constant sequence of a single proper subset.

The enumeration may repeat values, and there is no order or speed of enumeration. Its total range-equality presentation forces K nonempty. A finite K cannot support a perfect tower: one cannot have a fresh permanent witness at every positive stage; finite positive requirements also isolate K in its downward neighborhood. Empty X has no terminal parameter. An empty terminal has no such presentation and would also have no proper-subset tower. No distribution, membership oracle, output-loss notion, or learner-information restriction is quantified.

**Definitions inspected.** GenLimit.Language, GenLimit.Presents, GenLimit.KleinbergWei.TowerTopology.Point, GenLimit.KleinbergWei.TowerTopology.basicNeighborhood, GenLimit.KleinbergWei.TowerTopology.KWOpen, GenLimit.KleinbergWei.TowerTopology.IsLimitPoint, GenLimit.KleinbergWei.TowerTopology.FixesAt, GenLimit.KleinbergWei.TowerTopology.PerfectTower, GenLimit.KleinbergWei.TowerTopology.PerfectTower.mk, GenLimit.KleinbergWei.Banach.PerfectTower, GenLimit.KleinbergWei.TowerTopology.BasisLimitPoint, GenLimit.KleinbergWei.TowerTopology.ApproachedFrom, GenLimit.KleinbergWei.TowerTopology.AdaptiveStage, GenLimit.KleinbergWei.TowerTopology.AdaptiveStage.mk, GenLimit.KleinbergWei.TowerTopology.adaptiveStageOf, GenLimit.KleinbergWei.TowerTopology.nextFixed, GenLimit.KleinbergWei.TowerTopology.advance, GenLimit.KleinbergWei.TowerTopology.adaptiveStages, GenLimit.KleinbergWei.TowerTopology.adaptiveTower, GenLimit.KleinbergWei.TowerTopology.relativeApproximant, GenLimit.KleinbergWei.TowerTopology.approximant, GenLimit.KleinbergWei.TowerTopology.adaptiveStages.match_1, GenLimit.KleinbergWei.TowerTopology.AdaptiveStage.fixed, GenLimit.KleinbergWei.TowerTopology.AdaptiveStage.point, GenLimit.KleinbergWei.TowerTopology.AdaptiveStage.missing, GenLimit.sample.

**Limitations.** Paper and source claims withheld; theorem proof bodies, fresh compilation, source correspondence, and human certification are outside this review. The target does not identify its existential witness with adaptiveTower; that named construction has a separate native theorem interface, whose type alone was inspected. The presentation excludes empty K, permits repetitions, and gives no rate.

### GenLimit.KleinbergWei.Banach.claim_4_11_of_convergentProperTower
Slot: C03. Kind: theorem. Supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:191.

**Exact exported type**

    ∀ {X : Set.{0} GenLimit.Language} {sequence : Nat → GenLimit.KleinbergWei.TowerTopology.Point X}
      {terminal : GenLimit.KleinbergWei.TowerTopology.Point X} {R r : Nat},
      GenLimit.KleinbergWei.Banach.FiniteRankAtMost X R →
        GenLimit.KleinbergWei.Banach.HasFiniteCBRank X terminal r →
          GenLimit.KleinbergWei.TowerTopology.ConvergentProperTower X sequence terminal →
            ∃ N,
              ∀ (n : Nat),
                @LE.le.{0} Nat instLENat N n →
                  ∃ q, And (@LT.lt.{0} Nat instLTNat q r) (GenLimit.KleinbergWei.Banach.HasFiniteCBRank X (sequence n) q)

**Precise reconstruction.** Let X be any set of languages, sequence : Nat → Point X, terminal K : Point X, and R,r : Nat. If the R-th internal derivative D_R of X is empty, K lies in D_r \ D_(r+1), every sequence term is a proper subset of K, and each u∈K belongs to all sufficiently late sequence terms, then there is N such that for every n≥N there is q<r with sequence(n)∈D_q \ D_(q+1). The derivative starts at all points and repeatedly retains a point of the current set exactly when every finite positive neighborhood below it contains another point of the current set.

**Quantifier skeleton and dependencies.** ∀ {X} {sequence : Nat→Point X} {K : Point X} {R r : Nat}, [D_R=∅] → [K∈D_r ∧ K∉D_(r+1)] → [(∀n,sequence(n).val⊊K.val) ∧ (∀u∈K.val ∃N_u ∀n≥N_u,u∈sequence(n).val)] → ∃N ∀n≥N ∃q : Nat, q<r ∧ sequence(n)∈D_q\D_(q+1). N can depend on all preceding data and hypotheses; q can additionally depend on n.

**Information and algorithm scope.** Eventual semantic rank comparison for a supplied sequence and rank hypotheses. No program computes N or q, no uniform convergence modulus is supplied, and no presentation/learner/oracle is a target parameter.

**Edge cases and boundaries.** The derivative is internal: RelativeLimitPoint Y K includes K∈Y as well as the finite-neighborhood approximation clause. Explicitly, D_0=Point X and
D_(j+1)={K∈D_j | ∀ finite F⊆K, ∃L∈D_j, L≠K ∧ F⊆L⊆K}.
The exact rank condition is D_r\D_(r+1), and global finite rank is emptiness at index R, not a cardinality bound on X. No independent relation r≤R is an input hypothesis; with the other hypotheses, rank existence constrains these values.

The sequence input supplies both proper inclusion at every n and pointwise eventual containment of every u∈K. It need not be an increasing chain of sets. An element-dependent containment threshold is different from the theorem's one eventual threshold for the rank conclusion. Beyond that threshold the rank q may change with n and need not decrease as n increases. The conclusion is eventual (all n≥N), rather than merely frequent or a limsup statement.

If r=0, the conclusion would require q<0 at n=N, impossible; hence those full hypotheses are incompatible. If R=0, D_0=∅ prevents a terminal point. If K were finite, pointwise eventual containment plus inclusion would eventually force sequence(n)=K, contradicting properness. Repeated initial or occasional terms are not syntactically forbidden, though no fixed proper term can recur unboundedly while an element it omits must eventually remain present. There is no empty-prefix convention, target exhaustion protocol, rank-computing oracle, or quantitative convergence scale in the type.

**Definitions inspected.** GenLimit.Language, GenLimit.KleinbergWei.TowerTopology.Point, GenLimit.KleinbergWei.TowerTopology.basicNeighborhood, GenLimit.KleinbergWei.TowerTopology.RelativeLimitPoint, GenLimit.KleinbergWei.TowerTopology.derivative, GenLimit.KleinbergWei.TowerTopology.cbDerivative, GenLimit.KleinbergWei.TowerTopology.cbDerivative.match_1, GenLimit.KleinbergWei.TowerTopology.cbLevel, GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost, GenLimit.KleinbergWei.Banach.FiniteRankAtMost, GenLimit.KleinbergWei.Banach.HasFiniteCBRank, GenLimit.KleinbergWei.TowerTopology.ConvergentProperTower, GenLimit.KleinbergWei.TowerTopology.ConvergentProperTower.mk, GenLimit.KleinbergWei.Banach.BasisConverges.

**Limitations.** Paper and source claims withheld; theorem proof bodies, fresh compilation, source correspondence, and human certification are outside this review. No monotone inclusion relation between sequence terms, fixed eventual q, rank decrease at every step, finite cardinality of X, or explicit numerical bound on N is asserted. r=0 and R=0 make the full hypotheses incompatible with the other supplied data.

### GenLimit.KleinbergWei.Banach.claim_4_18_change_index_card_bound
Slot: C04. Kind: theorem. Supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:179.

**Exact exported type**

    ∀ {Vertex : Type u_1} [inst : SemilatticeInf.{u_1} Vertex] [inst_1 : DecidableEq.{u_1 + 1} Vertex]
      (vertices : Nat → Vertex) (depth : Vertex → Nat) (r : Nat),
      @StrictMono.{u_1, 0} Vertex Nat
          (@PartialOrder.toPreorder.{u_1} Vertex (@SemilatticeInf.toPartialOrder.{u_1} Vertex inst)) Nat.instPreorder
          depth →
        @LE.le.{0} Nat instLENat (depth (vertices (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) r →
          ∀ (n : Nat),
            @LE.le.{0} Nat instLENat
              (@Finset.card.{0} Nat
                (@GenLimit.KleinbergWei.Banach.prefixLCAChangeIndices.{u_1} Vertex inst inst_1 vertices n))
              r

**Precise reconstruction.** For any universe-polymorphic type Vertex with SemilatticeInf and DecidableEq, any total vertices : Nat→Vertex, depth : Vertex→Nat, and r : Nat, if depth is strictly increasing on strict order comparisons and depth(vertices(0))≤r, then every prefix index n has at most r indices i∈{1,…,n} at which the running meet C(i)=vertices(0)⊓⋯⊓vertices(i) differs from C(i−1).

**Quantifier skeleton and dependencies.** ∀ {Vertex : Type u} [SemilatticeInf Vertex] [DecidableEq Vertex], ∀ vertices depth r, StrictMono depth → depth(vertices 0)≤r → ∀n : Nat, card {i∈Icc 1 n | C(i)≠C(i−1)}≤r. r bounds the initial depth; no hypothesis bounds every input vertex depth.

**Information and algorithm scope.** prefixLCA computes the finite running meet; prefixLCAChangeIndices filters 1,…,n using the supplied equality decision. This is finite-prefix computation relative to the supplied meet and equality operations. The theorem is an all-n cardinal bound, with no learning protocol or complexity bound.

**Edge cases and boundaries.** C(n) includes n+1 input vertices. The index set starts at 1, so it counts changes after the initial value and includes a change at index n. At n=0, Icc 1 0 is empty and the bound is 0≤r. StrictMono depth means x<y implies depth(x)<depth(y) in the semilattice's induced order; it does not require a globally injective depth map on incomparable vertices. Only the initial depth is compared to r.

The conclusion holds for every finite prefix, so there can be at most r changes in total, but it gives no bound on when the final change occurs. r=0 implies C(n)=C(0) for all n. Repeating a vertex is allowed; adding a vertex above the current meet produces no change. The Vertex type need not be finite and the sequence need not enumerate distinct vertices. The natural-valued depth and initial bound supply the relevant finite scale; no other constants or asymptotic rates occur. The inspected alternate recursive count increments by 0 for equal consecutive meets and by 1 otherwise, but this endpoint specifically bounds the Finset cardinality.

**Definitions inspected.** GenLimit.KleinbergWei.Banach.prefixLCA, GenLimit.KleinbergWei.Banach.prefixLCA.match_1, GenLimit.KleinbergWei.Banach.prefixLCAChangeIndices, GenLimit.KleinbergWei.Banach.prefixLCAChangeCount.

**Limitations.** Paper and source claims withheld; theorem proof bodies, fresh compilation, source correspondence, and human certification are outside this review. No finite Vertex type, no rank hypothesis, no eventual time bound for the last change, and no linear order are assumed.

### GenLimit.KleinbergWei.Banach.claim_4_20_adjacent_pair_lca
Slot: C05. Kind: theorem. Supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:200.

**Exact exported type**

    ∀ {Vertex : Type u_1} [inst : SemilatticeInf.{u_1} Vertex]
      [inst_1 :
        @PredOrder.{u_1} Vertex (@PartialOrder.toPreorder.{u_1} Vertex (@SemilatticeInf.toPartialOrder.{u_1} Vertex inst))]
      [@IsPredArchimedean.{u_1} Vertex
          (@PartialOrder.toPreorder.{u_1} Vertex (@SemilatticeInf.toPartialOrder.{u_1} Vertex inst)) inst_1]
      (vertices : Nat → Vertex) (Q : Vertex) (n : Nat),
      @Eq.{u_1 + 1} Vertex
          (@GenLimit.KleinbergWei.Banach.prefixLCA.{u_1} Vertex inst vertices
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Q →
        ∃ i,
          And (@LE.le.{0} Nat instLENat i n)
            (@Eq.{u_1 + 1} Vertex
              (@Min.min.{u_1} Vertex (@SemilatticeInf.toMin.{u_1} Vertex inst) (vertices i)
                (vertices
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              Q)

**Precise reconstruction.** For every type Vertex with SemilatticeInf, PredOrder on its induced order, and IsPredArchimedean for that predecessor structure, every vertices : Nat→Vertex, Q : Vertex and n : Nat satisfy: if C(n+1)=Q, where C is the running meet starting at vertices(0), then some natural i≤n has vertices(i)⊓vertices(i+1)=Q. Thus the meet of n+2 supplied consecutive-prefix entries is achieved by one adjacent pair among them.

**Quantifier skeleton and dependencies.** ∀ {Vertex : Type u} [SemilatticeInf Vertex] [PredOrder Vertex] [IsPredArchimedean Vertex], ∀ vertices : Nat→Vertex, ∀Q : Vertex, ∀n : Nat, C(n+1)=Q → ∃i : Nat, i≤n ∧ (vertices i ⊓ vertices(i+1))=Q. i may depend on all data and the equality premise.

**Information and algorithm scope.** Logical existence of an adjacent-pair index. The target contains no named selection procedure, DecidableEq premise, search resource bound, learner, or oracle. Prefix meets are defined recursively from supplied operations.

**Edge cases and boundaries.** The type retains three order-related instances: SemilatticeInf, PredOrder on its induced preorder, and IsPredArchimedean for that PredOrder. Their formal assumptions cannot be replaced by the informal claim that Vertex is an arbitrary tree, and no separate finite-tree, depth, rank, or DecidableEq condition occurs. PredOrder and IsPredArchimedean belong to the declared trusted Lean/Mathlib boundary. Their field definitions are not supplied here; this report retains their exact typeclass requirements without claiming a separately audited characterization.

The hypothesis C(n+1)=Q refers to vertices(0),…,vertices(n+1), a prefix of length n+2. The witness uses one of precisely the adjacent pairs indexed 0,…,n, with both indices in that prefix. The conclusion is equality of the meet, not that either endpoint equals Q or that the chosen pair is unique. At n=0 the only possible index is 0, and the premise is already vertices(0)⊓vertices(1)=Q. Repeated vertices and repeated adjacent meets are allowed. A total sequence supplies an inhabitant of Vertex; no sequence can be supplied for an empty Vertex type. No algorithm selecting i is identified or certified by this existential proposition.

**Definitions inspected.** GenLimit.KleinbergWei.Banach.prefixLCA, GenLimit.KleinbergWei.Banach.prefixLCA.match_1.

**Limitations.** Paper and source claims withheld; theorem proof bodies, fresh compilation, source correspondence, and human certification are outside this review. PredOrder and IsPredArchimedean are retained exactly as external standard-library assumptions; their definitions were not recursively supplied or inspected. The claim is not reconstructed for bare arbitrary meet-semilattices. No finite Vertex or depth hypothesis appears.

### GenLimit.KleinbergWei.Banach.claim_4_4
Slot: C07. Kind: theorem. Supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:75.

**Exact exported type**

    ∀ {f : Nat → Nat},
      @Monotone.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder f →
        Iff (GenLimit.KleinbergWei.Banach.Nice f) (GenLimit.KleinbergWei.Banach.UniversallyUnbounded f)

**Precise reconstruction.** Both exact endpoints assert the same statement: for every monotone f : Nat→Nat, Nice f iff ∀M : Nat,∃n : Nat,M<f(n). Nice means that for every T one can choose m≥2 and total k,a : Nat→Nat such that k is nondecreasing on indices <m, a is strictly increasing on those indices, T<a(0), a(i)+k(i)+1≤a(i+1) whenever i+1<m, and a(i)≤f(k(i)) for every i<m. Every conjunct and the offset +1 are required.

**Quantifier skeleton and dependencies.** ∀ {f : Nat→Nat}, Monotone f → ((∀T : Nat ∃m : Nat ∃k : Nat→Nat ∃a : Nat→Nat, 2≤m ∧ [∀i,j<m, i≤j→k(i)≤k(j)] ∧ [∀i,j<m, i<j→a(i)<a(j)] ∧ T<a(0) ∧ [∀i, i+1<m→a(i)+k(i)+1≤a(i+1)] ∧ [∀i<m,a(i)≤f(k(i))]) ↔ (∀M : Nat ∃n : Nat,M<f(n))). Witnesses m,k,a may depend on f,T; n may depend on f,M. Each endpoint retains the monotonicity premise.

**Information and algorithm scope.** Two logical equivalences with semantic existential witnesses. No named construction of m,k,a,n, computational witness extraction, oracle model, uniform program, or quantitative growth rate occurs in either target type.

**Edge cases and boundaries.** Monotone f is a premise of both directions at each endpoint; the types do not state an equivalence for arbitrary nonmonotone f. The k-prefix is nondecreasing, not strictly increasing, so k(i)=k(j) is allowed. In contrast, a is strictly increasing for i<j<m. The gap inequality uses the actual value k(i) and the literal +1. The final a(i)≤f(k(i)) condition applies to every i<m, including the last index.

The witness m is chosen after T and need only satisfy m≥2. No claim about arbitrarily long configurations is explicit. Total functions k and a are supplied as witnesses, but only their first m entries are constrained. The threshold T=0 still requires a(0)>0; m≥2 prevents an empty or singleton witness block and ensures at least one gap inequality. UniversallyUnbounded is ∀M∃n rather than an eventual-rate assertion; together with monotonicity it entails the familiar eventual surpassing property, but the endpoint itself gives no modulus. A bounded or constant f does not satisfy the right side. There are no probabilistic laws, sample access, losses, or learner outputs.

**Definitions inspected.** GenLimit.KleinbergWei.Banach.Nice, GenLimit.KleinbergWei.Banach.UniversallyUnbounded.

**Limitations.** Paper and source claims withheld; theorem proof bodies, fresh compilation, source correspondence, and human certification are outside this review. k need not be strictly increasing: repeated k-indices are allowed. m need only be at least 2; the target does not demand arbitrarily long m. Values of k,a outside the chosen finite prefix are unconstrained.

### GenLimit.KleinbergWei.Banach.claim_7_1
Slot: C07. Kind: theorem. Supplied source anchor: GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:81.

**Exact exported type**

    ∀ {f : Nat → Nat},
      @Monotone.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder f →
        Iff (GenLimit.KleinbergWei.Banach.Nice f) (GenLimit.KleinbergWei.Banach.UniversallyUnbounded f)

**Precise reconstruction.** Both exact endpoints assert the same statement: for every monotone f : Nat→Nat, Nice f iff ∀M : Nat,∃n : Nat,M<f(n). Nice means that for every T one can choose m≥2 and total k,a : Nat→Nat such that k is nondecreasing on indices <m, a is strictly increasing on those indices, T<a(0), a(i)+k(i)+1≤a(i+1) whenever i+1<m, and a(i)≤f(k(i)) for every i<m. Every conjunct and the offset +1 are required.

**Quantifier skeleton and dependencies.** ∀ {f : Nat→Nat}, Monotone f → ((∀T : Nat ∃m : Nat ∃k : Nat→Nat ∃a : Nat→Nat, 2≤m ∧ [∀i,j<m, i≤j→k(i)≤k(j)] ∧ [∀i,j<m, i<j→a(i)<a(j)] ∧ T<a(0) ∧ [∀i, i+1<m→a(i)+k(i)+1≤a(i+1)] ∧ [∀i<m,a(i)≤f(k(i))]) ↔ (∀M : Nat ∃n : Nat,M<f(n))). Witnesses m,k,a may depend on f,T; n may depend on f,M. Each endpoint retains the monotonicity premise.

**Information and algorithm scope.** Two logical equivalences with semantic existential witnesses. No named construction of m,k,a,n, computational witness extraction, oracle model, uniform program, or quantitative growth rate occurs in either target type.

**Edge cases and boundaries.** Monotone f is a premise of both directions at each endpoint; the types do not state an equivalence for arbitrary nonmonotone f. The k-prefix is nondecreasing, not strictly increasing, so k(i)=k(j) is allowed. In contrast, a is strictly increasing for i<j<m. The gap inequality uses the actual value k(i) and the literal +1. The final a(i)≤f(k(i)) condition applies to every i<m, including the last index.

The witness m is chosen after T and need only satisfy m≥2. No claim about arbitrarily long configurations is explicit. Total functions k and a are supplied as witnesses, but only their first m entries are constrained. The threshold T=0 still requires a(0)>0; m≥2 prevents an empty or singleton witness block and ensures at least one gap inequality. UniversallyUnbounded is ∀M∃n rather than an eventual-rate assertion; together with monotonicity it entails the familiar eventual surpassing property, but the endpoint itself gives no modulus. A bounded or constant f does not satisfy the right side. There are no probabilistic laws, sample access, losses, or learner outputs.

**Definitions inspected.** GenLimit.KleinbergWei.Banach.Nice, GenLimit.KleinbergWei.Banach.UniversallyUnbounded.

**Limitations.** Paper and source claims withheld; theorem proof bodies, fresh compilation, source correspondence, and human certification are outside this review. k need not be strictly increasing: repeated k-indices are allowed. m need only be at least 2; the target does not demand arbitrarily long m. Values of k,a outside the chosen finite prefix are unconstrained.

The complete exported type above is identical to that of GenLimit.KleinbergWei.Banach.claim_4_4 after declaration-name removal. The same full reconstruction applies independently to this endpoint. No distinction in mathematics is inferred from its locator.

## Exhaustive slot coverage

“No supplied target” records a mapping boundary, not an invented mathematical failure or a source-correspondence judgment.

| Slot | Exact reviewed declaration(s) | Reconstruction coverage |
|---|---|---|
| C01 | GenLimit.KleinbergWei.Banach.claim_3_5 | Complete supplied-type reconstruction; dossier above |
| C02 | GenLimit.KleinbergWei.Banach.claim_3_6 | Complete supplied-type reconstruction; dossier above |
| C03 | GenLimit.KleinbergWei.Banach.claim_4_11_of_convergentProperTower | Complete supplied-type reconstruction; dossier above |
| C04 | GenLimit.KleinbergWei.Banach.claim_4_18_change_index_card_bound | Complete supplied-type reconstruction; dossier above |
| C05 | GenLimit.KleinbergWei.Banach.claim_4_20_adjacent_pair_lca | Complete supplied-type reconstruction; dossier above |
| C06 | GenLimit.KleinbergWei.Banach.claim_3_3 | Complete supplied-type reconstruction; dossier above |
| C07 | GenLimit.KleinbergWei.Banach.claim_4_4<br>GenLimit.KleinbergWei.Banach.claim_7_1 | Complete supplied-type reconstruction; dossier above |
| C08 | None supplied | No supplied reconstruction target; endpoint flag true, declarations and absent-name lists empty |
| C09 | None supplied | No supplied reconstruction target; endpoint flag true, declarations and absent-name lists empty |
| C10 | None supplied | No supplied reconstruction target; endpoint flag true, declarations and absent-name lists empty |
| C11 | None supplied | No supplied reconstruction target; endpoint flag true, declarations and absent-name lists empty |
| C12 | None supplied | No supplied reconstruction target; endpoint flag true, declarations and absent-name lists empty |
| C13 | None supplied | No supplied reconstruction target; endpoint flag true, declarations and absent-name lists empty |

### Slots without endpoints

- C08: No supplied reconstruction target. claim-slots.json gives an empty declarations array, no absent linked names, and no_registered_lean_endpoint=true. No mathematical statement or source interpretation can be reconstructed for this opaque slot from the authorized inputs.
- C09: No supplied reconstruction target. claim-slots.json gives an empty declarations array, no absent linked names, and no_registered_lean_endpoint=true. No mathematical statement or source interpretation can be reconstructed for this opaque slot from the authorized inputs.
- C10: No supplied reconstruction target. claim-slots.json gives an empty declarations array, no absent linked names, and no_registered_lean_endpoint=true. No mathematical statement or source interpretation can be reconstructed for this opaque slot from the authorized inputs.
- C11: No supplied reconstruction target. claim-slots.json gives an empty declarations array, no absent linked names, and no_registered_lean_endpoint=true. No mathematical statement or source interpretation can be reconstructed for this opaque slot from the authorized inputs.
- C12: No supplied reconstruction target. claim-slots.json gives an empty declarations array, no absent linked names, and no_registered_lean_endpoint=true. No mathematical statement or source interpretation can be reconstructed for this opaque slot from the authorized inputs.
- C13: No supplied reconstruction target. claim-slots.json gives an empty declarations array, no absent linked names, and no_registered_lean_endpoint=true. No mathematical statement or source interpretation can be reconstructed for this opaque slot from the authorized inputs.

## Verification and limits

Target/slot counts, recursive closure of listed project dependencies, recursive/native record agreement, hash-manifest agreement, and suppression of theorem values were checked mechanically. This is interface-package validation, not Lean verification. No targeted Lean check or repository-wide lake build was run because no Lean code was changed and fresh compilation is explicitly outside Stage 1. There are no build failures or build warnings to report; builds were not attempted.

No context needed for the eight project-definition reconstructions is missing within the supplied recursive bundle. The remaining boundary is standard Lean/Mathlib semantics, with the unexpanded predecessor typeclasses explicitly retained. For C08–C13 there is no type to reconstruct and no source meaning available. No positive or negative source-correspondence conclusion is made for any slot.

The SHA-256 values for this Markdown report and stage1-claims.json are recorded in stage1-run.json. The run manifest does not embed its own self-referential hash; its final byte hash is returned to the coordinator separately. Stage 1 ends here.
