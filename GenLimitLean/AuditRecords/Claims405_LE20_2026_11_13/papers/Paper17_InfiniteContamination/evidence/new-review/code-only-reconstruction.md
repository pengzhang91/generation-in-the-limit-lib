# P17 — Stage 1 code-only reconstruction (narrowed C03)

This report reconstructs only opaque slot C03 and its one supplied target from the current Stage 1 exports. It makes no source-paper correspondence judgment. The source paper remains withheld.

## Scope, isolation and input census

The current claim-slots.json has exactly C03; targets.txt has one identifier. declarations.jsonl contains 49 records: 38 definitions, 9 theorem types (one target and eight supporting interfaces), one inductive structure and its constructor. All 38 definition values and the structure/constructor were inspected, together with the supplied supporting interface types. Embedded `⋯` entries suppress proof terms; they are not evidence of proof holes. All native dependencies named in the 49 records resolve within that file. The target type agrees exactly with 01-target-statements.md.

The current native-declaration-census.jsonl contains 1,305 supporting records according to the packet snapshot. Its bytes were hashed in this narrowed review; the census is not an individual audit of those declarations. No additional census lookup was needed for C03. START_HERE.md, PROMPT.md, claim-slots.json, targets.txt, snapshot.json, 01-target-statements.md, 02-definition-dependencies.md, declarations.jsonl, external-boundary.txt and SHA256SUMS were consulted. SHA256SUMS matches the current named files. Exact current file hashes and the distinction between semantic inspection and hashing are in stage1-run.json.

The requested configuration was gpt-6.1-sol with xhigh reasoning and fresh isolated context. Backend model identity/revision and effective reasoning setting are not independently observable. The initial broader Lean-only packet was read before the coordinator interrupted the run and narrowed it. This continuation is **not fresh relative to C03 alone**. No earlier draft was written. Broader Lean-only exposure is disclosed as a limitation; only the current target is reconstructed here. No paper, archive, registry, PaperMap, developer commentary/proof text, prior audit verdict, owner record, human record, Stage 2 or Stage 3 material was accessed. Parent coordination messages provided the scope change, not mathematical source interpretations.

## Definition glossary

The prefixes `G`, `I` and `K` below mean `GenLimit.Generic`, `GenLimit.InfiniteContamination` and `GenLimit.KleinbergWei`. These are locators; meanings come from the exported values.

| Definition | Reconstructed value |
|---|---|
| `G.FiniteHistoryOperator` | For input and output types, the type (t : Nat) → (Fin t → Input) → Output. A complete ordered length-t history is supplied. |
| `G.Generator` | FiniteHistoryOperator α α; one element per history. |
| `G.IsInfiniteSetGenerator` | For every t and every length-t history xs, the set gen t xs is infinite; this is a global, all-history requirement. |
| `G.Language` | Set α. |
| `G.SetGenerator` | FiniteHistoryOperator α (Set α); a semantic set per history, without a representation or computability requirement. |
| `G.Stream` | Nat → α. |
| `G.output` | output gen stream t = gen t (fun i => stream i.val); the samples have indices strictly below t. |
| `G.sequenceSample` | The Finset image of xs on all of Fin t; repeated values are deduplicated. |
| `I.AlgorithmEightAdmissible` | At stage s and time t: s = 0 or AlgorithmEightBudget holds. Stage zero is always admissible. |
| `I.AlgorithmEightBudget` | c_s / δ_s ≤ 2(t+1)/ρ, where c_s is algorithmEightStageCutoff and δ_s = densitySlack s; all operations in this inequality are real. |
| `I.IsInfiniteSetGenerator` | Alias of the global Generic.IsInfiniteSetGenerator condition. |
| `I.SetCoreSelectionInvariant` | For every t,xs, setGen t xs is contained in the intersection of all family languages selected by selection t xs, with every sampled value removed. This is an inclusion, not equality. |
| `I.SetGenerator` | Alias of Generic.SetGenerator. |
| `I.algorithmEightChosenSet` | Complete xs by zero after t, compute k = algorithmEightHistoryIndex, and return the original setGen output on the first k values of that completed stream. |
| `I.algorithmEightGenerator` | The element generator algorithmEightOutput with fixed setGen, hinfinite, selection, orders and ρ; family and target are not runtime parameters. |
| `I.algorithmEightHistoryIndex` | algorithmEightIndexOn on the stream equal to xs below t and zero at and above t, evaluated at time t. |
| `I.algorithmEightIndexOn` | The greatest s ≤ t satisfying AlgorithmEightAdmissible, found with Nat.findGreatest and classical proposition decisions. |
| `I.algorithmEightOutput` | Packages (t,xs) for the well-founded recursive _unary definition. |
| `I.algorithmEightOutput._unary` | Recurses on shorter histories. Let previous be the finite set of this procedure’s outputs on every proper prefix of xs; forbidden is sequenceSample xs union previous. Return the least natural n in algorithmEightChosenSet and outside forbidden, via Nat.find. Infinitude supports the existence argument. |
| `I.algorithmEightRankCutoff` | Nat.ceil (2 * (t+1) * δ_s / ρ), with casts to Real before arithmetic; this is a natural-number bound. |
| `I.algorithmEightStageCutoff` | At stage s, apply finiteDensityCutoff to orders, selection on the first s stream values, the original setGen output on those values, and slack stage s. |
| `I.canonicalIndex` | If x belongs to K.carrier, the least n with K.enumeration n = x; otherwise 0. The enumeration is injective and onto its carrier. |
| `I.canonicalRank` | If x belongs to L, K.prefixCount L (canonicalIndex K x + 1); otherwise 0. In this target L is K.carrier, so members have one-based enumeration rank and nonmembers have rank zero. |
| `I.densityCutoff` | Classically choose an N such that for every m ≥ N, K.lowerDensity A / δ_s ≤ K.prefixRatio A m. No least choice, effective modulus, or finite method for obtaining N is supplied. |
| `I.densitySlack` | δ_s = 1 + (1/2)^(s+1), a positive real strictly above 1, at most 3/2, tending to 1 as s tends to infinity. |
| `I.elementOutputStream` | At t, the Generic.output of the given element generator on the first t stream values. |
| `I.finiteCommonCore` | Intersection of the finite set of languages: x is in every member. For the empty set of languages this is the universal set. |
| `I.finiteDensityCutoff` | The Finset.sup (maximum, with default 0) of densityCutoff (orders i) A s over selected indices i. |
| `I.indexedLanguages` | The Finset image of family on the selected index Finset; equal languages at different indices are deduplicated. |
| `I.prefixCompletion` | Equal to xs n for n < t and to the specified fallback otherwise; here the fallback is 0. |
| `I.setOutput` | setOutput setGen stream t = setGen t (fun i => stream i.val). |
| `K.DensityMeasures.FiniteRankFallback.InheritsAmbientOrder` | StrictMono K.enumeration in the ordinary natural-number order; it requires increasing enumeration, beyond mere injectivity. |
| `K.OrderedLanguage.carrier` | The carrier set field of OrderedLanguage. |
| `K.OrderedLanguage.enumeration` | The Nat → Nat enumeration field of OrderedLanguage. |
| `K.OrderedLanguage.lowerDensity` | liminf atTop of K.prefixRatio A n. This is density along K’s enumeration, not along the observed stream or the sequence of output times. |
| `K.OrderedLanguage.prefixCount` | Number of indices j < n for which K.enumeration j belongs to A. |
| `K.OrderedLanguage.prefixRatio` | Zero at n = 0; otherwise real prefixCount/n. |
| `GenLimit.Language` | Set Nat. |

`K.OrderedLanguage` has a carrier subset of Nat, a Nat → Nat enumeration, a proof of enumeration injectivity, and a proof that its range equals the carrier. Hence its carrier is infinite. It does not intrinsically require an increasing enumeration; the target separately requires `InheritsAmbientOrder` for every indexed order. `K.OrderedLanguage.mk` exposes those four fields in that order.

The supporting theorem interface `I.exists_eventual_density_cutoff` supplies, for every K,A,stage, an existential eventual prefix-ratio threshold with the exact inequality used by densityCutoff. The generated `_proof_1` through `_proof_5` interfaces on the recursive output certify well-foundedness, proper-prefix indexing/decrease, chosen-set infinitude, and existence of a permitted natural. The canonicalIndex generated interface supplies carrier-to-enumeration-range membership; densitySlack’s generated interface supplies a numeral instance. These eight interfaces were used only to understand total definitions. Their proofs and independent theorem correctness were not audited.

## C03 target dossier

**Identifier:** `GenLimit.InfiniteContamination.claim_6_17_algorithmEight_rank`  
**Kind:** theorem  
**Exported source anchor:** `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:756`  
**Evidence:** current `01-target-statements.md` and matching record in `declarations.jsonl`.

### Exact exported type

```lean
∀ (setGen : GenLimit.InfiniteContamination.SetGenerator.{0} Nat)
  (hinfinite : @GenLimit.InfiniteContamination.IsInfiniteSetGenerator.{0} Nat setGen) (family : Nat → Set.{0} Nat)
  (selection : (t : Nat) → (Fin t → Nat) → Finset.{0} Nat) (orders : Nat → GenLimit.KleinbergWei.OrderedLanguage)
  (ρ : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ρ →
    GenLimit.InfiniteContamination.SetCoreSelectionInvariant setGen family selection →
      (∀ (i : Nat), @Eq.{1} GenLimit.Language (orders i).carrier (family i)) →
        (∀ (i : Nat), GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.InheritsAmbientOrder (orders i)) →
          ∀ (target : Nat) (stream : GenLimit.Generic.Stream.{0} Nat),
            (∃ N,
                ∀ (t : Nat),
                  @LE.le.{0} Nat instLENat N t →
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                      (selection t fun i => stream (@Fin.val t i)) target) →
              (∃ N,
                  ∀ (t : Nat),
                    @LE.le.{0} Nat instLENat N t →
                      @LE.le.{0} Real Real.instLE ρ
                        ((orders target).lowerDensity
                          (@GenLimit.InfiniteContamination.setOutput.{0} Nat setGen stream t))) →
                ∃ N,
                  ∀ (t : Nat),
                    @LE.le.{0} Nat instLENat N t →
                      @LE.le.{0} Nat instLENat
                        (GenLimit.InfiniteContamination.canonicalRank (orders target) (orders target).carrier
                          (GenLimit.InfiniteContamination.elementOutputStream
                            (GenLimit.InfiniteContamination.algorithmEightGenerator setGen hinfinite selection orders ρ)
                            stream t))
                        (GenLimit.InfiniteContamination.algorithmEightRankCutoff ρ
                          (GenLimit.InfiniteContamination.algorithmEightIndexOn setGen selection orders ρ stream t) t)
```

### Natural-language reconstruction

For every set-valued finite-history operator setGen on Nat, every certificate hinfinite that its output is infinite on every finite history, every indexed family of subsets of Nat, every finite-index selection function on histories, every indexed family of OrderedLanguage values, and every real ρ > 0: assume globally that each setGen output lies in the intersection of the selected family languages and avoids the sampled values, that every order carrier equals the matching family language, and that all order enumerations are strictly increasing. Then for every target index and every Nat-valued stream, if the target belongs to the selected indices at every sufficiently late time and the original setGen output has lower density at least ρ in the target order at every sufficiently late time, there is a threshold N such that at every t ≥ N the canonical rank, in the target carrier, of the output of algorithmEightGenerator setGen hinfinite selection orders ρ is at most Nat.ceil (2 * (t+1) * (1 + (1/2)^(s_t+1)) / ρ), where s_t is algorithmEightIndexOn setGen selection orders ρ stream t. The conclusion is solely this eventual natural-number rank inequality; canonicalRank is zero outside the target carrier.

### Quantifiers and dependencies

In the exact order of the type:

```text
∀ setGen,
∀ hinfinite : ∀ t xs, Infinite (setGen t xs),
∀ family : Nat → Set Nat,
∀ selection : (t : Nat) → (Fin t → Nat) → Finset Nat,
∀ orders : Nat → OrderedLanguage,
∀ ρ : Real,
  0 < ρ →
  (∀ t xs, setGen t xs ⊆ (⋂ i ∈ selection t xs, family i) \ sample(xs)) →
  (∀ i, (orders i).carrier = family i) →
  (∀ i, StrictMono (orders i).enumeration) →
  ∀ target : Nat,
  ∀ stream : Nat → Nat,
    (∃ Nsel, ∀ t ≥ Nsel, target ∈ selection t stream[0:t]) →
    (∃ Nden, ∀ t ≥ Nden,
       ρ ≤ (orders target).lowerDensity (setGen t stream[0:t])) →
    ∃ Nrank, ∀ t ≥ Nrank,
       canonicalRank (orders target) (orders target).carrier (g t stream[0:t])
       ≤ ceil_Nat (2*(t+1)*δ(s_t)/ρ),
where g = algorithmEightGenerator setGen hinfinite selection orders ρ,
      s_t = algorithmEightIndexOn setGen selection orders ρ stream t,
      δ(s) = 1 + (1/2)^(s+1).
```

The fixed generator depends on setGen, hinfinite, selection, orders and ρ, and is the same for every target and stream satisfying the hypotheses. Family appears only in the global invariant/carrier hypotheses, not as a direct generator argument. Nsel and Nden are separate existential witnesses, downstream of target and stream. Nrank is further downstream of all parameters and hypotheses; no uniform threshold or computable rate is asserted. s_t depends on the fixed generator data, the stream prefix below t and t, not on target. The rank cutoff depends on ρ,s_t,t.

The bound is eventual **for every** later t. There is no asserted all-time rank bound, probability law, loss function, frequently-only statement, limsup rank conclusion or explicit rate for Nrank. The density premise is a separate pointwise eventual lower bound on each set’s lower density, not just a lower bound on a liminf over time. The target has no element-density conclusion. Both coefficients 2 and t+1, the positive denominator ρ, natural ceiling, and stage-dependent slack are retained.

### Named procedure, inputs and access

At time t, `g` receives exactly the ordered finite history of the first t observations. Its fixed data are setGen, its global infinitude certificate, selection, orders and ρ. It receives no target index, membership labels for the true target, noise classification, future observations, or stabilization witnesses. Family is used in correctness hypotheses but is not a direct argument to g.

For each candidate stage s ≤ t, it forms the original set output A_s from the first s observations and the selection at s. For each selected index i it classically chooses a threshold beyond which the order-i prefix ratios of A_s are at least lowerDensity(A_s)/δ_s, and takes the finite maximum c_s (zero for empty selection). It declares s admissible when s=0 or c_s/δ_s ≤ 2(t+1)/ρ, then takes the greatest admissible s≤t. Stage zero ensures a candidate even if its budget inequality fails. The chosen set is the original setGen output at that stage.

The element output is defined by well-founded recursion on history length. It computes this same procedure’s outputs on every proper prefix, places them together with all observed values in a finite forbidden set, and selects the least natural in the chosen infinite set outside that set. This describes a total mathematical function using semantic infinitude and least-witness choice. No separately stored mutable state is specified. The chosen stage is at most t, so the zero-fallback completion supplies no actual future information; all prefix queries used here are within the available history.

The rank bound uses `algorithmEightIndexOn` on the actual stream; the generator uses its zero-completed finite history through `algorithmEightHistoryIndex`. Their formulas inspect only stages at most t and histories below those stages. This is a definitional access reconstruction; no proof of equality or correctness of the resulting rank bound was checked.

The access boundary is substantial: arbitrary setGen and selection functions, semantic sets and carriers, ordered-language enumerations, exact lower-density values, `Classical.choose` of eventual cutoffs, classical decisions of real budget propositions and set membership, plus least-natural search. There is no supplied oracle record for these operations, effective modulus of density convergence, finite query bound, computability assumption or complexity guarantee. Even if other supplied functions happen to be computable, this interface alone does not establish ordinary computation of the complete procedure. The theorem is about this named semantic generator; it does not merely assert an unspecified existential learner.

### Validity, freshness and edge cases

- The conclusion has exactly one component: a natural-number rank inequality. In `canonicalRank K K.carrier`, a member has rank `canonicalIndex K x + 1`, while a nonmember has rank zero. Thus the inequality in isolation permits nonmembers. The target does not explicitly conjoin validity or freshness.
- The named definition separately requires the output to lie in its chosen set and to avoid all sampled values and all earlier-prefix outputs. These are the inspected selection/exclusion rules, not an independent certification of their proofs or of eventual target validity.
- Global infinitude holds for every setGen history, including t=0 and histories that repeat values or violate the eventual stream assumptions. Together with the finite forbidden set it supplies a candidate; an exhausted or finite setGen output is excluded by the global premise. At t=0 the history and previous-output sets are empty and stage 0 is the only possible stage. The theorem still permits an arbitrary finite initial period before Nrank.
- The invariant is global, on every history, and is only a containment in the common core minus the sample. It does not assert that setGen returns the entire core, nor that it excludes past element outputs; the latter exclusion is done by g.
- Selection may be empty at early times or on other histories. Its common core is then universal, its finiteDensityCutoff is zero, and the target-selection premise rules out empty selection only eventually on the chosen stream. Selection is not required to consist of indices below t; its type allows any finite set of Nat.
- No injectivity, no-omission, noise-rate or presentation premise is imposed on stream. Observations may repeat, and both samples and earlier outputs are represented by Finsets. Duplicate family languages at different indices are allowed; indexedLanguages deduplicates equal language values, while finiteDensityCutoff still runs over the selected index set and its associated orders.
- The orders’ carriers are infinite by their enumeration fields, so the global carrier-equality premise excludes empty or finite family languages. There is no separate assumption that stream enumerates a target or even has infinite target overlap.
- Only ρ>0 is assumed; there is no explicit upper restriction ρ≤1. Since these lower densities are ratios bounded by 1, the eventual density premise is unsatisfiable for ρ>1. The theorem remains a conditional statement in that case. The degenerate ρ=0 case is outside its assumptions.
- There is no explicit convergence or unboundedness claim for s_t, and the target alone supplies no uniform Nrank across targets/streams. The slack δ_s is part of the displayed cutoff; replacing it by its limit 1 would strengthen the claimed bound without evidence from this target.

## Exhaustive current coverage

| Slot | Exact declaration | Reconstruction status | Scope limitation |
|---|---|---|---|
| C03 | `GenLimit.InfiniteContamination.claim_6_17_algorithmEight_rank` | Complete exported-type and necessary-definition reconstruction above | Paper withheld; no proof/compilation/effectivity certification |

Current totals: **1/1 slot addressed; 1/1 supplied target reconstructed; 0 absent-endpoint slots in the current packet.** No completion status is assigned to the other 26 formerly listed slots.

## Supporting-record inventory

This inventory is exhaustive for the current recursive package. “Support interface” means that only the exported type was used to interpret a total definition; it is not an independent claim audit.

| Exact identifier | Kind | Exported source anchor | Use |
|---|---|---|---|
| `GenLimit.Generic.FiniteHistoryOperator` | definition | `GenLimit.Core.GenericGeneration:37` | Definition value reconstructed |
| `GenLimit.Generic.Generator` | definition | `GenLimit.Core.GenericGeneration:41` | Definition value reconstructed |
| `GenLimit.Generic.IsInfiniteSetGenerator` | definition | `GenLimit.Core.SetGeneration:30` | Definition value reconstructed |
| `GenLimit.Generic.Language` | definition | `GenLimit.Core.GenericGeneration:21` | Definition value reconstructed |
| `GenLimit.Generic.SetGenerator` | definition | `GenLimit.Core.SetGeneration:19` | Definition value reconstructed |
| `GenLimit.Generic.Stream` | definition | `GenLimit.Core.GenericGeneration:31` | Definition value reconstructed |
| `GenLimit.Generic.output` | definition | `GenLimit.Core.GenericGeneration:87` | Definition value reconstructed |
| `GenLimit.Generic.sequenceSample` | definition | `GenLimit.Core.GenericGeneration:58` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.AlgorithmEightAdmissible` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:142` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.AlgorithmEightBudget` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:130` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.IsInfiniteSetGenerator` | definition | `GenLimit.Paper17_InfiniteContamination.Definitions:290` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.SetCoreSelectionInvariant` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:686` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.SetGenerator` | definition | `GenLimit.Paper17_InfiniteContamination.Definitions:285` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.algorithmEightChosenSet` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:296` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.algorithmEightGenerator` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:331` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.algorithmEightHistoryIndex` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:225` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.algorithmEightIndexOn` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:153` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.algorithmEightOutput` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:306` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.algorithmEightOutput._unary` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:not supplied` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.algorithmEightOutput._unary._proof_1` | theorem | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:not supplied` | Support interface only |
| `GenLimit.InfiniteContamination.algorithmEightOutput._unary._proof_2` | theorem | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:not supplied` | Support interface only |
| `GenLimit.InfiniteContamination.algorithmEightOutput._unary._proof_3` | theorem | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:not supplied` | Support interface only |
| `GenLimit.InfiniteContamination.algorithmEightOutput._unary._proof_4` | theorem | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:not supplied` | Support interface only |
| `GenLimit.InfiniteContamination.algorithmEightOutput._unary._proof_5` | theorem | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:not supplied` | Support interface only |
| `GenLimit.InfiniteContamination.algorithmEightRankCutoff` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:530` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.algorithmEightStageCutoff` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:119` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.canonicalIndex` | definition | `GenLimit.Paper17_InfiniteContamination.BoundedDisplacement:38` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.canonicalIndex._proof_1` | theorem | `GenLimit.Paper17_InfiniteContamination.BoundedDisplacement:not supplied` | Support interface only |
| `GenLimit.InfiniteContamination.canonicalRank` | definition | `GenLimit.Paper17_InfiniteContamination.BoundedDisplacement:57` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.claim_6_17_algorithmEight_rank` | theorem | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:756` | Target dossier |
| `GenLimit.InfiniteContamination.densityCutoff` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:87` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.densitySlack` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:38` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.densitySlack._proof_1` | theorem | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:not supplied` | Support interface only |
| `GenLimit.InfiniteContamination.elementOutputStream` | definition | `GenLimit.Paper17_InfiniteContamination.ElementDensity:38` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.exists_eventual_density_cutoff` | theorem | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:59` | Support interface only |
| `GenLimit.InfiniteContamination.finiteCommonCore` | definition | `GenLimit.Paper17_InfiniteContamination.VanishingNoise:80` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.finiteDensityCutoff` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:100` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.indexedLanguages` | definition | `GenLimit.Paper17_InfiniteContamination.PriorityStabilization:366` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.prefixCompletion` | definition | `GenLimit.Paper17_InfiniteContamination.AlgorithmFour:646` | Definition value reconstructed |
| `GenLimit.InfiniteContamination.setOutput` | definition | `GenLimit.Paper17_InfiniteContamination.Definitions:294` | Definition value reconstructed |
| `GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.InheritsAmbientOrder` | definition | `GenLimit.Support.KleinbergWei.OrderedPositions:18` | Definition value reconstructed |
| `GenLimit.KleinbergWei.OrderedLanguage` | inductive | `GenLimit.Core.OrderedDensity:24` | Structure fields reconstructed |
| `GenLimit.KleinbergWei.OrderedLanguage.carrier` | definition | `GenLimit.Core.OrderedDensity:25` | Definition value reconstructed |
| `GenLimit.KleinbergWei.OrderedLanguage.enumeration` | definition | `GenLimit.Core.OrderedDensity:26` | Definition value reconstructed |
| `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity` | definition | `GenLimit.Core.OrderedDensity:237` | Definition value reconstructed |
| `GenLimit.KleinbergWei.OrderedLanguage.mk` | constructor | `GenLimit.Core.OrderedDensity:24` | Structure fields reconstructed |
| `GenLimit.KleinbergWei.OrderedLanguage.prefixCount` | definition | `GenLimit.Core.OrderedDensity:33` | Definition value reconstructed |
| `GenLimit.KleinbergWei.OrderedLanguage.prefixRatio` | definition | `GenLimit.Core.OrderedDensity:197` | Definition value reconstructed |
| `GenLimit.Language` | definition | `GenLimit.Core.Basic:20` | Definition value reconstructed |

## Verification and remaining limits

Verification here was structural: matching current target/slot counts, exact-type agreement between the two exports, native dependency closure, exact input SHA256 checks, JSON schema/coverage checks, and output hashes. No Lean build or single-file check was run because only an exported interface packet was authorized and no Lean code was changed. No build warnings or failures were observed because no build was attempted.

Standard Lean and Mathlib meanings in external-boundary.txt are trusted. No decisive unresolved native definition remains in the current packet. Source correspondence, proof validity, full algorithm construction correctness, execution and human certification remain outside this stage. Requested model/reasoning settings are recorded without inventing a backend revision. Stage 1 stops with these three files; no later stage was begun.
