# P17 / C03 — supplemental paper-withheld Stage 1 reconstruction

One supplied target is reconstructed below. The original frozen Stage 1 outputs are preserved. Evidence is limited to the mechanically exported supplemental code packet; no paper or source-comparison material was consulted.

## Exact target

**Name:** `GenLimit.InfiniteContamination.algorithmEight_generates_of_eventually_selected`  
**Kind:** theorem, not a definition-valued proposition  
**Exported source anchor:** `GenLimit.Paper17_InfiniteContamination.AlgorithmEight:698`  
**Exact input references:** `stage1-supplement-input/target-statements.md`, its matching record in `declarations.jsonl`, and the recursively necessary values/types in `definition-dependencies.md`. `targets-by-slot.json` associates this target with C03. Exact input hashes are in `stage1-supplement-run.json`.

```lean
∀ (setGen : GenLimit.InfiniteContamination.SetGenerator.{0} Nat)
  (hinfinite : @GenLimit.InfiniteContamination.IsInfiniteSetGenerator.{0} Nat setGen) (family : Nat → Set.{0} Nat)
  (selection : (t : Nat) → (Fin t → Nat) → Finset.{0} Nat) (orders : Nat → GenLimit.KleinbergWei.OrderedLanguage)
  (ρ : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ρ →
    GenLimit.InfiniteContamination.SetCoreSelectionInvariant setGen family selection →
      ∀ (target : Nat) (stream : GenLimit.Generic.Stream.{0} Nat),
        (∃ N,
            ∀ (t : Nat),
              @LE.le.{0} Nat instLENat N t →
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                  (selection t fun i => stream (@Fin.val t i)) target) →
          @GenLimit.InfiniteContamination.GeneratesElementInLimitOn.{0} Nat
            (GenLimit.InfiniteContamination.algorithmEightGenerator setGen hinfinite selection orders ρ) (family target)
            stream
```

## Reconstruction and quantifier order

For every set-valued finite-history operator setGen on Nat, every proof hinfinite that its output is infinite on every finite history, every indexed family of subsets of Nat, every finite-index selection function on histories, every indexed sequence of OrderedLanguage values, and every real ρ: if ρ > 0 and for every finite history the setGen output is contained in the common core of the selected family languages with the sampled values removed, then for every target index and every Nat-valued stream, eventual permanent selection of that target implies eventual fresh element generation by the fixed named generator algorithmEightGenerator setGen hinfinite selection orders ρ. Explicitly, there is T such that for every t ≥ T its output on stream[0:t] belongs to family target, is absent from all stream observations with indices below t, and is absent from all this same generator’s outputs with indices below t, including outputs before T.

```text
∀ setGen,
∀ hinfinite : ∀ t xs, Infinite (setGen t xs),
∀ family : Nat → Set Nat,
∀ selection : (t : Nat) → (Fin t → Nat) → Finset Nat,
∀ orders : Nat → OrderedLanguage,
∀ ρ : Real,
  0 < ρ →
  (∀ t xs,
     setGen t xs ⊆ (⋂ i ∈ selection t xs, family i) \ sequenceSample(xs)) →
  ∀ target : Nat,
  ∀ stream : Nat → Nat,
    (∃ Nsel, ∀ t ≥ Nsel, target ∈ selection t stream[0:t]) →
    ∃ T, ∀ t ≥ T,
      output(g,stream,t) ∈ family target ∧
      (output(g,stream,t) ∉ {stream s | s < t} ∧
       output(g,stream,t) ∉ {output(g,stream,s) | s < t}),
where g = algorithmEightGenerator setGen hinfinite selection orders ρ.
```

The generator is fixed by setGen, hinfinite, selection, orders and ρ before target and stream; family is a correctness parameter, not a direct generator argument. Nsel is existential only after target and stream. T is existential after all parameters, hypotheses and the selection premise, and may depend on them; there is no uniform threshold or explicit/effective function converting Nsel into T. T is not asserted equal to Nsel. All three correctness conjuncts share this single T.

The explicit premises after the data binders are exactly positive ρ, the global set-core selection invariant, and eventual target selection. There is **no** hypothesis of a lower-density bound on setGen outputs, equality between orders’ carriers and family languages, strictly increasing order enumerations, stream injectivity, noise control, omission control or a presentation of the target. Orders are arbitrary values of their declared structure. Any positive ρ is admitted, including ρ>1; ρ is an algorithm parameter here, without a density guarantee in this statement.

## Necessary definitions and named procedure

The prefixes G, I and K in this paragraph mean GenLimit.Generic, GenLimit.InfiniteContamination and GenLimit.KleinbergWei. All 36 definition values in the 46-record recursive packet were inspected. They fall into six groups recorded with exact names in the supplemental JSON:

- Finite-history representation: a generator has type `(t : Nat) → (Fin t → Nat) → Nat`; setGen returns `Set Nat`. Both observe the first t samples, in their original order. Samples are Finsets of observed values, so repeats are deduplicated.
- Global conditions: `I.IsInfiniteSetGenerator` means every output is infinite on every finite history, not merely eventually on a particular stream. `I.SetCoreSelectionInvariant` requires inclusion in the common selected core minus the sample on every history. The common core is an intersection; empty selection gives the universal set, and equal family languages at distinct indices are deduplicated by the Finset image.
- Conclusion predicates: `I.FreshElementCorrectAt` is membership AND (sample freshness AND freshness relative to all prior outputs). `I.GeneratesElementInLimitOn` is one existential threshold followed by this full conjunction at every later time. These two are definitions of propositions; their declarations do not independently prove such propositions.
- Stage selection: put δ_s = `1+(1/2)^(s+1)`. For a set A and ordered language K, `densityCutoff K A s` classically chooses a natural N satisfying `∀ m ≥ N, lowerDensity_K(A)/δ_s ≤ prefixRatio_K(A,m)`. `finiteDensityCutoff` takes the finite maximum across selected order indices, with default zero. At stage s, the original setGen output and selection on the first s observations determine c_s. Stage s is admissible at t if `s=0` or `c_s/δ_s ≤ 2(t+1)/ρ`. `algorithmEightIndexOn` chooses the greatest admissible s≤t. Stage zero is always available even when its budget fails.
- Element output: complete the current history by zero, obtain that selected stage k, and use the original setGen output on its first k observations as the chosen infinite set. The recursively defined output function reconstructs its own outputs on every proper prefix of the current history, unions them with the observed sample, and uses `Nat.find` to choose the least natural in the chosen set outside that finite forbidden set. `algorithmEightGenerator` is this function with the fixed data. Recursion is on smaller history lengths; no separately stored mutable state is specified.
- Ordered density: an OrderedLanguage contains a carrier, an injective Nat enumeration, and a range-equals-carrier certificate. Thus its carrier is infinite. `prefixCount` counts positions j<n whose enumerated value is in A; `prefixRatio` is zero at n=0 and real prefixCount/n otherwise; `lowerDensity` is their liminf atTop. Increasing enumeration is not intrinsic to this structure or required by this target.

At time t, the named procedure has the ordered observations below t plus fixed setGen, hinfinite, selection, orders and ρ. It may evaluate setGen/selection on earlier prefixes and recursively reconstruct its own earlier-prefix outputs. It receives no target, family as a direct argument, noise labels, future samples, Nsel or T. It uses semantic ordered-language prefix ratios/lower densities, Classical.choose of eventual density cutoffs, classical decisions of budgets and chosen-set membership, Nat.findGreatest over bounded stages, and Nat.find for a least permitted natural. No effective density modulus, set encoding, oracle record, bounded query interface, ordinary computability hypothesis or complexity bound is supplied. Fallback zero does not add actual lookahead, since only stages k ≤ t and their earlier prefixes are used.

Seven supporting theorem types were consulted only to interpret total definitions: five generated recursive-output interfaces (well-foundedness, valid/decreasing prefix indices, chosen-set infinitude and permitted-element existence), the numeral-instance interface for densitySlack, and `exists_eventual_density_cutoff`. Their proof bodies were unavailable and not audited. No independent claim audit of those seven interfaces is asserted. Embedded `⋯` terms are the export’s suppression of proof terms, not proof holes.

## Edge cases and limits of the conclusion

- The guarantee is eventual for **every** later time, not all-time, infinitely-often-only, limsup or a probabilistic guarantee. All three correctness components use the same T. Earlier outputs may be invalid or nonfresh as far as this theorem’s conclusion says, but every later output must avoid them too.
- The observation stream may repeat arbitrarily; no stream injectivity or target coverage is assumed. The output exclusion rule concerns the finite observed prefix at that time, not future observations.
- Selection may be empty initially or on other histories. Eventual permanent selection makes it nonempty along the chosen stream after Nsel. Selected indices need not be below the history length. Distinct indices may denote equal languages; no distinctness or injective family hypothesis is present.
- Global infinitude rules out exhausted chosen sets. The global invariant implies any language selected on any history contains that history’s infinite setGen output. Consequently an empty or finite target cannot satisfy the complete premises together with eventual target selection; that case is conditional vacuity. Other unselected family members need not be infinite.
- At t=0 the history and prior-output sets are empty, only stage zero is considered, and its admissibility is automatic. The theorem may choose T>0 and promises no initial correctness period.
- There is no claimed lower density of the element-output language, canonical rank bound, uniform bound on T or effectiveness of obtaining T. No stage-growth lemma is being certified. The source correspondence and proof/construction correctness remain outside this supplement.

## Scope, isolation and mechanical checks

This supplement covers **1 target in C03**, with 46 recursive records: 36 definitions, 8 theorem types (one target and seven supporting interfaces), one structure and its constructor. All named native dependencies in the packet resolve internally. The exact target type matches its Markdown export, and all six SHA256SUMS entries match the actual inputs; the manifest itself is also hashed in the run record. The JSON has one target row.

Requested model/reasoning: gpt-6.1-sol / xhigh. Backend identity/revision and effective reasoning setting are not independently observable. This is retained paper-withheld context, not a fresh session: before an earlier interruption it saw a broader Lean-only Stage 1 packet, and later reconstructed the narrowed C03 rank target and shared definitions. That exposure is disclosed; no paper, prior audit explanation/verdict, Stage 2 result, owner/human record, registry, PaperMap or developer commentary was accessed for this supplement. The original three Stage 1 result files were hashed before and after to confirm byte-for-byte preservation, without semantic rereading.

Mechanical checks cover the target list/slot/type, native dependency closure, manifest and report hashes, JSON coverage and frozen-output preservation. No Lean code changed, no compilation was attempted, and no proof-body audit or later-stage source comparison was begun. Standard Lean/Mathlib semantics are trusted under the retained Stage 1 external boundary.
