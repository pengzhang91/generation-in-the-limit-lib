# P21 — Stage 1 code-only reconstruction

This report reconstructs supplied Lean interfaces only. It does not infer source-paper claims from identifiers or paths. All 14 opaque slots and all 18 distinct target declarations have supplied endpoints. Each target has a dossier below; each supplied recursive definition has an exact-value appendix entry. This is a statement-and-definition audit, not verification of proof bodies, source correspondence, fresh compilation, or human certification.

## Input census and isolation

The only evidentiary inputs read were the 11 files in the supplied `P21/stage1` directory, beginning with `START_HERE.md` and `PROMPT.md`. No paper, web page, source checkout, parent conversation, registry, PaperMap, owner interpretation, old audit, existing result, other paper package, or later-stage context was consulted. A temporary report-writing script is an output-generation aid, not an additional evidence source. No Lean or Git command was run and no input file was edited.

The package contains 14 slot rows; every slot has `no_registered_lean_endpoint=false` and empty absent-linked-name lists. There are 18 distinct targets, 86 recursive declaration rows (65 definitions, 21 theorem interfaces: the 18 targets plus 3 numeral-instance helper types), and 1,106 native census rows (288 definitions, 794 theorems, 8 inductives, 8 constructors, 8 recursors) across 49 modules. The native census was parsed for counts, names, target/recursive-row equality and boundary completeness; it was not individually audited declaration by declaration. Every recursive GenLimit dependency listed by the 86 rows is supplied. Each recursive row equals its native-census row. No target theorem proof value is supplied. All 65 recursive definition values and all 18 target types were semantically inspected; the three helper theorem types were inspected without proofs.

The supplied manifest hashes were recomputed from actual file bytes and all ten manifest entries match. `SHA256SUMS` itself was also hashed. The snapshot's original-source hash is metadata only: the source package was not opened or rehashed. The requested reviewer configuration is `gpt-6.1-sol / xhigh`, with fresh paper-withheld context. The actual serving backend model/revision, temperature, seed, and enforcement of runtime context isolation are not independently observable. The observable audit boundary is the files and tool calls described here; no claims of hidden backend revision or fresh Lean compilation are made.

| Input file | Bytes | Actual SHA-256 |
|---|---:|---|
| `01-target-statements.md` | 45937 | `21b256be8bae2f54ff4736f872e36ff5f12b05dc8bbb2ffbf86b4eae1bf6ddc5` |
| `02-definition-dependencies.md` | 42922 | `e60fd04c070633f1d5fe89f5c78d3ac263b12eec0d9aad912c29c7ecc1af9b81` |
| `PROMPT.md` | 3356 | `c63aad9d119a37687071a9dd61f3139f0f318647c5237a6cfd05e4ecd3e38de3` |
| `SHA256SUMS` | 854 | `1926951256cffc4a725c67bd4ef8f9ff9f660ec553f8889ad63308852d0e342f` |
| `START_HERE.md` | 217 | `52dbb6f80b47a22d94f222fd499cc75c3e793e710b44d74dd69922866c1c02d7` |
| `claim-slots.json` | 3061 | `47fde18d07e89a91246ec70421706b8641bc4de3e3675c678017aa9c9ecb015c` |
| `declarations.jsonl` | 129974 | `becd98fae05739e0c459e3b40c0220067d38d3c4b4a7dcda6da51f4f76c46bfe` |
| `external-boundary.txt` | 2048 | `5eda69397aaac976d1cc3d03406766a66ad45586357ee3f55a9768e0f2dd7b81` |
| `native-declaration-census.jsonl` | 1855802 | `9c31ad6b61a23bc9c4360cb64a412149728c66ff538f8df1a83e9cc4c688228b` |
| `snapshot.json` | 3432 | `1f5c90bb068b72da38e88fc45e1fc2ac04afd3044639d6cc5bef323d51e20331` |
| `targets.txt` | 768 | `a3881705c146003fb3da4854986334b7028deabd09a6ba27a27e215c25f75eab` |

Snapshot metadata source hash: `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc` (not independently revalidated against source). Standard Lean/Mathlib meanings are trusted as authorized by `external-boundary.txt`; no recursive Mathlib audit was performed. No decisive missing native definition was found. Suppressed embedded proof placeholders are not interpreted as proof holes.

## Shared semantic glossary

All equations here are direct expansions of supplied definition values. The exact identifier, type, definition value, and source anchor for every one of the 65 definitions appear in the definition appendix. No theorem proof body is used. Write ℝ for Lean `Real`, ℕ for `Nat`, and ℓ² for the underlying subtype of `HilbertAxisReservoir.Hilbert2`.

- `GenLimit.Generic.Language α = Set α`; `LanguageClass α = Set (Set α)`; `Stream α = ℕ → α`.
- `FiniteHistoryOperator Input Output = (t : ℕ) → (Fin t → Input) → Output`; `Generator α` specializes both types to α. A generator is a total single-output function even at t=0. `output g stream t = g t (fun i => stream i.val)`. Thus the output at time t has access exactly to indices 0,…,t−1. This is causal prefix access, with no explicit mutable state; arbitrary functions of the full observed prefix are allowed.
- `sequenceSample xs` is the finite image of all `Fin t` indices; `sample stream t` is the finite image of indices in `Finset.range t`. Both collapse repeated values. The prefix function still retains order and repetitions. Equality for these finite images is resolved classically in the supplied definitions, without a `DecidableEq α` binder.
- `StreamIn stream L` says `range stream ⊆ L`; `Presents stream L` says `range stream = L`. Repetitions are allowed. No probabilities, laws, distributions, full-support measures, randomized outputs, support losses, or multiple-output losses appear in any of these interfaces.
- `GenLimit.MetricSpaces.Distance α = α → α → ℝ`; the name alone includes no metric law. Only the explicit hypotheses and global typeclasses in each target constrain it.
- Define `Nρ(A,r) = closedNeighborhood ρ A r`. Its exact membership predicate `InClosedNeighborhood` is `y ∈ Nρ(A,r) ↔ ∀η:ℝ, r<η → ∃x∈A, ρ x y<η`. The direction is from x in A to y. This is an approximation-to-radius definition, not an assumed attained witness with distance ≤r. For infinite A the witness may depend on η. We keep the literal predicate for arbitrary real functions/scales; symmetry and nonnegativity are not built in. The empty set has empty neighborhood for every real r.
- `MetricPresentation ρ ε stream L` is `range stream ⊆ L ∧ L ⊆ Nρ(range stream,ε)`. It need not enumerate all of L. The second component is over the entire infinite range, whereas a learner still sees only a finite prefix.
- Let `S_t = sample stream t`. `MetricCorrectAt ρ ε′ g L stream t` is exactly `[output g stream t ∈ L] ∧ [output g stream t ∉ Nρ((S_t : Set α),ε′)]`. Membership in L and novelty outside the neighborhood are separate required conjuncts. At nonnegative scale for diagonal-zero distances, novelty in particular prevents repeating an observed value; at arbitrary negative scales retain the literal predicate.
- Let `CAρ(r,A,d)` abbreviate `CoveringNumberAtLeast ρ r A d`: for every finite center set C, `A ⊆ Nρ(C,r) → d ≤ C.card`. Centers are ambient α points and need not belong to A. `d=0` always satisfies this lower-bound predicate. If no finite cover exists, every d satisfies it vacuously; it is not an asserted finite numeric covering number.
- Let `CEρ(r,A,d)` abbreviate `CoveringNumberEq ρ r A d`: `CAρ(r,A,d) ∧ ∃C:Finset α,C.card=d ∧ A⊆Nρ(C,r)`. It includes an actual finite cover and lower bound, so both components matter. A finite observed sample has a self-cover at nonnegative scales under diagonal-zero ρ, but the definition imposes no such assumptions itself.
- Let `ICρ(r,A)` abbreviate `HasFiniteInternalCover ρ r A`: `∃C:Finset α,(C:Set α)⊆A ∧ A⊆Nρ(C,r)`. Here the centers must belong to A. For empty A the empty center set is allowed. There is no asserted cardinality bound.
- `GenLimit.Generic.versionSpace H S = {L | L∈H ∧ (S:Set α)⊆L}`; `commonCore H S = {x | ∀L∈versionSpace H S,x∈L}`. The metric namespaces `versionSpace` and `commonCore` are aliases. If the version space is empty the universal common core is all α, but the closure-witness definition explicitly requires a nonempty version space.
- `IsScaleClosureWitness ρ ε ε′ H S d = VS(H,S).Nonempty ∧ CEρ(ε,(S:Set α),d) ∧ ICρ(ε′,Core(H,S))`.
- `HasFiniteScaleClosureDimension ρ ε ε′ H = ∃D:ℕ,∀d:ℕ,D<d → ¬∃S:Finset α,IsScaleClosureWitness ρ ε ε′ H S d`. D is any upper bound, not a least number or a numeric function value.

The generator quantifiers are crucial. In the following formulas `Correct` is the two-conjunct metric correctness above, and `CA` is the ambient-center lower-bound predicate above:

```text
IsLimitGeneratorAt ρ ε ε′ g H
  = ∀L, L∈H → ∀stream, MetricPresentation ρ ε stream L →
      ∃T:ℕ, ∀t:ℕ, T≤t → Correct(ρ,ε′,g,L,stream,t).
Lρ(ε,ε′,H) := GeneratableInLimitAt ρ ε ε′ H = ∃g, IsLimitGeneratorAt ρ ε ε′ g H.

IsUniformGeneratorAt ρ ε ε′ g H d
  = ∀L, L∈H → ∀stream, StreamIn stream L → ∀t:ℕ,
      CAρ(ε,(S_t:Set α),d) → ∀s:ℕ, t≤s → Correct(ρ,ε′,g,L,stream,s).
Uρ(ε,ε′,H) := UniformlyGeneratableAt ρ ε ε′ H = ∃g,∃d:ℕ, IsUniformGeneratorAt ρ ε ε′ g H d.

IsNonuniformGeneratorAt ρ ε ε′ g H
  = ∀L, L∈H → ∃d:ℕ, ∀stream, StreamIn stream L → ∀t:ℕ,
      CAρ(ε,(S_t:Set α),d) → ∀s:ℕ, t≤s → Correct(ρ,ε′,g,L,stream,s).
Nρ(ε,ε′,H) := NonuniformlyGeneratableAt ρ ε ε′ H = ∃g, IsNonuniformGeneratorAt ρ ε ε′ g H.
```

For L, T may depend on g, the fixed parameters, L and the full stream, but g sees only each prefix. For U, d is common to all L and streams. For N, d can depend on L but precedes every stream, t and s. In all three cases there is one g for the entire fixed H, chosen before L. No generator takes its target language as an argument. U/N require only in-language streams, without presentation/density, and give all-future correctness conditional on an attained covering trigger. L gives eventual all-time correctness on presentations. None states merely frequent or limsup success. No numeric rate or bound on T,d is specified. Negations of L,U,N rule out all total semantic functions of this shape, including noncomputable ones, for the given property.

- `Bρ(r,H) := UniformlyUnboundedSupportAt ρ r H` expands to `∀L,L∈H → [L.Nonempty ∧ ∀stream,MetricPresentation ρ r stream L → ∀d:ℕ,∃t:ℕ,CAρ(r,(S_t:Set α),d)]`. The same r is common to H, but there is no uniform time bound over languages, streams, or d. For languages without a metric presentation only the nonemptiness component is nonvacuous.
- `IsNondecreasingMetricCover H classes` aliases `Generic.IsNondecreasingCover`: monotonicity for set inclusion and `H=⋃n,classes n`. It does not mean each class is finite or countable.
- `DistanceDominatedBy ρ₂ ρ₁ M` is `∀x y,ρ₂ x y ≤ M*ρ₁ x y`. `MutuallyLipschitzDominated ρ₁ ρ₂ M₁₂ M₂₁` is the conjunction `DistanceDominatedBy ρ₂ ρ₁ M₁₂ ∧ DistanceDominatedBy ρ₁ ρ₂ M₂₁`.
- `Double(ρ) := IsDoublingDistance ρ` is `∃M:ℕ,0<M ∧ ∀x:α∀r:ℝ,0<r → ∃C:Finset α,C.card≤M ∧ ∀y:α,ρ x y≤r → ∃z∈C,ρ z y≤r/2`. The centers may lie anywhere in α; they are not required to lie in the original ball. This definition uses actual ≤ distances, whereas the general neighborhood uses the approximation predicate. M is global over x,r. It does not include diagonal, symmetry, or triangle laws.
- `discreteDistance [DecidableEq α] x y = if x=y then 0 else 1`.
- `Generic.CorrectAt g L stream t = output∈L ∧ output∉S_t`. `Generic.IsLimitGenerator` quantifies exact presentations `range stream=L` and eventual all-time correctness. `Generic.IsUniformGeneratorAt g H d` quantifies all L∈H and in-language streams, and uses the trigger `S_t.card=d` before all s≥t correctness. `Generic.IsNonuniformGenerator` places ∃d after L and before stream with that same equality trigger. `Generic.GeneratableInLimit`, `UniformlyGeneratable`, and `NonuniformlyGeneratable` existentially quantify g (and d for uniform) in the corresponding order. Each of the three `GenLimit.LiRamanTewari` predicates in proposition_D_1 is exactly an alias to its same-named `Generic` predicate.

The real-line class definitions are fully explicit: `realDistance x y=|x−y|`; `positiveEvenIntegers={x:ℝ | ∃n:ℕ,x=cast(2*(n+1))}`; `primePairSupport p={x:ℝ | ∃n:ℕ,x=cast(p^(n+1)) ∨ x=cast(p^(n+1)−1)}`, where subtraction occurs in ℕ before casting. `RealLineThreshold.languageClass={L | ∃p:ℕ,Prime p ∧ Odd p ∧ ∃B:Set ℝ,B⊆positiveEvenIntegers ∧ L=primePairSupport p∪B}`.

For the supplied Hilbert definitions, `Hilbert2` is the additive subgroup `lp (fun _:ℕ => ℝ) 2`; its underlying type is the real square-summable sequences, with the normed additive commutative group instance exported in the target types. `axisPoint c k=lp.single k c = c e_k`, and `hilbertDistance x y=dist x y` from that ℓ² norm. The numeric helper theorem types `Hilbert2._proof_1`, `example48U._proof_1`, and `IsDoublingDistance._proof_1` certify the pretty-printed numeral-instance obligations 2≥2 or 4≥2; their proof values are absent and unnecessary here.

For the exact example48 class:

```text
Zero = axisPoint 0 0.
U(r,k) = axisPoint (4*r) k.
A(ε,k) = axisPoint ε k.
G(ε′,k) = axisPoint ε′ k.
USet(r,I₁) = {U(r,k) | k∈I₁}.
Optimal(ε,ε′,I₂)
  = {A(ε,2*k) | k∈I₂} ∪ {G(ε′,2*k^n+1) | k∈I₂, n:ℕ}.
Disturbing(ε′,I₃) = {G(ε′,2*k+1) | k∈I₃}.
Language(r,ε,ε′,I₁,I₂,I₃)
  = {Zero} ∪ (USet(r,I₁) ∪ (Optimal(ε,ε′,I₂) ∪ Disturbing(ε′,I₃))).
example48LanguageClass(r,ε,ε′)
  = {L | ∃I₁ I₂ I₃:Set ℕ,
        Infinite I₁ ∧ Infinite I₂ ∧ Infinite I₃ ∧
        (∀k∈I₁,0<k) ∧ (∀k∈I₂,0<k) ∧ (∀k∈I₃,0<k) ∧
        L=Language(r,ε,ε′,I₁,I₂,I₃)}.
```

These formulas expand the identifiers with prefixes `GenLimit.MetricSpaces.HilbertAxisReservoir.`: `example48Zero`, `example48U`, `example48A`, `example48G`, `example48USet`, `example48Optimal`, `example48Disturbing`, `example48Language`, `example48LanguageClass`. No hidden requirements on the three index sets are added. Coordinates can repeat across these set comprehensions; unions are sets, not multisets.

The named algorithm in example_4_8 has the exact candidate predicate:

```text
IsExample48CausalCandidate ε ε′ γ′ xs y
  ↔ ∃k:ℕ,2≤k ∧ (∃i:Fin t,xs i=A(ε,2*k)) ∧
      ∃n:ℕ,y=G(ε′,2*k^(n+1)+1) ∧
        y ∉ Nhilbert((sequenceSample xs:Set ℓ²),γ′).
example48CausalGenerator ε ε′ γ′ t xs
  = if h : ∃y,IsExample48CausalCandidate ε ε′ γ′ xs y
      then Classical.choose h else Zero.
```

The candidate existential does not require k prime or a hidden language-index membership proof. Existence testing uses `Classical.propDecidable`; successful output uses `Classical.choose`. It supplies no executable real comparison, decidable existential search, least candidate rule, external oracle parameter, or complexity bound. The only state is the given prefix. Thus the named witness is more specific than unspecified semantic existence but is not a certified ordinary computable algorithm. This reconstruction does not inspect its correctness proof.

## Shared boundary and edge-case rules

For every dossier, universal quantification over a missing language or stream is vacuous. A class can be empty unless excluded by an explicit predicate. A language may have no metric presentation: L-properties and presentation-conditioned B clauses then impose no stream obligation on it. U/N also permit streams repeating the same point forever; their guarantee is conditional on a covering threshold being reached. Exhausting a finite set, repeated indices/values, or arbitrarily slow discovery of new points creates no hidden time-bound promise. The t=0 sample is empty. Threshold d=0 is allowed and triggers immediately because CA at zero is always true, but existence statements need not choose zero.

A generator must return α even from the empty prefix. Consequently for empty α no generator exists, even for empty H; for inhabited α and empty H the language-dependent conditions are vacuous. Do not infer Nonempty α when it is not an explicit binder, except standard inhabited structures such as real vector spaces. Similarly, B requires nonempty member languages, not nonempty H. No targets add a law of data generation, full support, effective enumeration, computational uniformity over parameters, or explicit convergence rate. A function g may be specialized to fixed H,ρ and scales without those being run-time inputs. Such parameter dependence is different from being given L or an oracle. A theorem ∀parameters∃g is not itself a single computable meta-program for constructing g.

## Exhaustive slot coverage

| Slot | Supplied target declarations | Status |
|---|---|---|
| C01 | `GenLimit.MetricSpaces.Results.theorem_3_1` | Reconstructed in full |
| C02 | `GenLimit.MetricSpaces.Results.corollary_3_2`; `GenLimit.MetricSpaces.Results.corollary_3_4` | Reconstructed in full |
| C03 | `GenLimit.MetricSpaces.Results.theorem_3_3` | Reconstructed in full |
| C04 | `GenLimit.MetricSpaces.Results.theorem_3_5` | Reconstructed in full |
| C05 | `GenLimit.MetricSpaces.Results.corollary_4_3`; `GenLimit.MetricSpaces.Results.theorem_4_1`; `GenLimit.MetricSpaces.Results.theorem_4_2` | Reconstructed in full |
| C06 | `GenLimit.MetricSpaces.Results.theorem_4_4` | Reconstructed in full |
| C07 | `GenLimit.MetricSpaces.Results.theorem_4_6`; `GenLimit.MetricSpaces.Results.theorem_4_7` | Reconstructed in full |
| C08 | `GenLimit.MetricSpaces.Results.theorem_4_10` | Reconstructed in full |
| C09 | `GenLimit.MetricSpaces.Results.proposition_D_1` | Reconstructed in full |
| C10 | `GenLimit.MetricSpaces.Results.example_4_5` | Reconstructed in full |
| C11 | `GenLimit.MetricSpaces.Results.example_4_8` | Reconstructed in full |
| C12 | `GenLimit.MetricSpaces.Results.example_4_9` | Reconstructed in full |
| C13 | `GenLimit.MetricSpaces.Results.example_4_11` | Reconstructed in full |
| C14 | `GenLimit.MetricSpaces.Results.example_B_3` | Reconstructed in full |

No absent/unlinked or no-endpoint slots occur in this supplied list. This table describes code coverage only and makes no source-correspondence judgment.

## Per-target dossiers

The shared glossary expands every abbreviation used below. The exact exported type is retained for each target, including implicit/global binders, universes, and instance arguments. `diag0`, `symm`, and `triangle` in schematic formulas denote the full universally quantified equations/inequality stated in the prose and exact type, not additional assumptions.

### C01 — `GenLimit.MetricSpaces.Results.theorem_3_1`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:51`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] {ρ : GenLimit.MetricSpaces.Distance.{u_1} α} {ε ε' : Real}
  {H : GenLimit.Generic.LanguageClass.{u_1} α},
  (∀ (x : α), @Eq.{1} Real (ρ x x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
      Iff (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} α ρ ε ε' H)
        (@GenLimit.MetricSpaces.HasFiniteScaleClosureDimension.{u_1} α ρ ε ε' H)
```

**Reconstruction.** For every nonempty type α, arbitrary real-valued distance function ρ with ρ(x,x)=0, real input scale ε≥0, arbitrary real output scale ε′, and class H of subsets of α, existence of one uniform metric generator with one natural covering threshold for H is equivalent to existence of a natural bound D beyond which no scale-closure witness exists. A scale-closure witness is a finite sample S consistent with at least one language in H, whose ambient-center ε-covering number is exactly d, and whose common consistent-language core has a finite internal ε′-cover. The bound excludes every d>D, not just one d.

**Quantifier skeleton and dependencies.** ∀ {α : Type u} [Nonempty α] {ρ : α→α→ℝ} {ε ε′ : ℝ} {H : Set (Set α)}, (∀x,ρ x x=0) → 0≤ε → (Uρ(ε,ε′,H) ↔ ∃D:ℕ,∀d:ℕ,D<d → ¬∃S:Finset α, VS(H,S).Nonempty ∧ CEρ(ε,S,d) ∧ ICρ(ε′,Core(H,S))). U expands as ∃g∃d∀L∈H∀stream∈L∀t,CAρ(ε,S_t,d)→∀s≥t,Correctρ(ε′,g,L,stream,s). D and g,d may depend on all fixed inputs; there is no least-bound claim.

**Information available to the learner.** The generator receives only t and the ordered prefix Fin t→α; it may be selected using the entire fixed class H and scales. Neither L nor a presentation, membership oracle, covering oracle, or core oracle is supplied as a generator argument.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** ε=0 and ε′<0 are allowed. No symmetry, triangle inequality, nonnegativity, separation, countability, or support hypothesis is explicit. Empty H gives empty version spaces, so no witnesses; α is nevertheless nonempty. The common core may itself be empty, whose empty internal cover is permitted. D=0 and d=0 are natural possibilities; witnesses are excluded only strictly above D.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.commonCore`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.Generic.versionSpace`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.CoveringNumberEq`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.HasFiniteInternalCover`; `GenLimit.MetricSpaces.HasFiniteScaleClosureDimension`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsScaleClosureWitness`; `GenLimit.MetricSpaces.IsUniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.UniformlyGeneratableAt`; `GenLimit.MetricSpaces.closedNeighborhood`; `GenLimit.MetricSpaces.commonCore`; `GenLimit.MetricSpaces.versionSpace`.

### C02 — `GenLimit.MetricSpaces.Results.corollary_3_2`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:64`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] {ρ : GenLimit.MetricSpaces.Distance.{u_1} α} {ε ε' : Real}
  {H : GenLimit.Generic.LanguageClass.{u_1} α},
  (∀ (x : α), @Eq.{1} Real (ρ x x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
      @LE.le.{0} Real Real.instLE ε' ε →
        @Set.Finite.{u_1} (GenLimit.Generic.Language.{u_1} α) H →
          @GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} α ρ ε ε' H
```

**Reconstruction.** For every nonempty α, diagonal-zero real function ρ, scales with 0≤ε and ε′≤ε, and finite class H, a uniform metric generator exists: one g and one natural covering threshold work for every language of H, every stream lying in that language, every triggering time, and every later time.

**Quantifier skeleton and dependencies.** ∀{α}[Nonempty α]{ρ}{ε ε′}{H}, (∀x,ρxx=0) → 0≤ε → ε′≤ε → H.Finite → ∃g∃d:ℕ,∀L∈H∀stream,StreamIn(stream,L)→∀t,CAρ(ε,S_t,d)→∀s,t≤s→Correctρ(ε′,g,L,stream,s). g,d depend on H,ρ,ε,ε′, not on L or stream.

**Information available to the learner.** Only finite observed prefixes are inputs; the existentially chosen g can depend on the fixed finite class, with no enumeration or membership oracle stipulated.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** The class, not each language, is finite. H may be empty and may contain empty or finitely exhausted languages. No lower bound on ε′ is imposed; ε=ε′=0 is included. A stream whose sample never attains the threshold incurs no triggered obligation.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsUniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.UniformlyGeneratableAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C02 — `GenLimit.MetricSpaces.Results.corollary_3_4`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:100`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] {ρ : GenLimit.MetricSpaces.Distance.{u_1} α} {ε ε' : Real}
  {H : GenLimit.Generic.LanguageClass.{u_1} α},
  (∀ (x : α), @Eq.{1} Real (ρ x x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
      @LE.le.{0} Real Real.instLE ε' ε →
        @Set.Countable.{u_1} (GenLimit.Generic.Language.{u_1} α) H →
          @GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} α ρ ε ε' H
```

**Reconstruction.** Under the same nonempty-type, diagonal-zero, 0≤ε and ε′≤ε assumptions, a countable class H admits a single nonuniform metric generator. Each language receives its own natural covering threshold, chosen before the stream; once any in-language stream reaches that threshold, every later output is correct.

**Quantifier skeleton and dependencies.** ∀{α}[Nonempty α]{ρ}{ε ε′}{H}, (∀x,ρxx=0)→0≤ε→ε′≤ε→H.Countable→∃g,∀L∈H,∃d:ℕ,∀stream,StreamIn(stream,L)→∀t,CAρ(ε,S_t,d)→∀s≥t,Correctρ(ε′,g,L,stream,s). g is common to H; d may depend on L but not on stream or t.

**Information available to the learner.** The generator receives the prefix and length, without L, its chosen threshold, a countable enumeration, or a membership oracle as input.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** Countable permits finite and empty H. It refers to the family of languages, not to α or to an individual language. No positive output-scale requirement and no density/presentation requirement for the streams in this nonuniform property are imposed.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C03 — `GenLimit.MetricSpaces.Results.theorem_3_3`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:84`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} [Nonempty.{u_1 + 1} α] {ρ : GenLimit.MetricSpaces.Distance.{u_1} α} {ε ε' : Real}
  {H : GenLimit.Generic.LanguageClass.{u_1} α},
  (∀ (x : α), @Eq.{1} Real (ρ x x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
      Iff (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} α ρ ε ε' H)
        (∃ classes,
          And (@GenLimit.MetricSpaces.IsNondecreasingMetricCover.{u_1} α H classes)
            (∀ (n : Nat), @GenLimit.MetricSpaces.HasFiniteScaleClosureDimension.{u_1} α ρ ε ε' (classes n)))
```

**Reconstruction.** For every nonempty α and diagonal-zero ρ at nonnegative input scale ε and arbitrary output scale ε′, nonuniform metric generatability of H is equivalent to the existence of an increasing sequence of language classes with union exactly H, each of which has finite scale-closure dimension at the same two scales. The finite dimension bound may differ across sequence indices.

**Quantifier skeleton and dependencies.** ∀{α}[Nonempty α]{ρ}{ε ε′}{H},(∀x,ρxx=0)→0≤ε→(Nρ(ε,ε′,H) ↔ ∃classes:ℕ→Set(Set α),(∀m n,m≤n→classes m⊆classes n) ∧ H=⋃n,classes n ∧ ∀n,∃D_n:ℕ,∀d>D_n,¬∃S,VS(classes n,S).Nonempty∧CEρ(ε,S,d)∧ICρ(ε′,Core(classes n,S))). On the left ∃g∀L∈H∃d_L∀stream∀t∀s as in N. The cover is selected after H,ρ,scales; each D_n depends on n.

**Information available to the learner.** The existence statement does not supply the generator with the sequence, its dimension bounds, a language index, or tests for class membership. An existential cover is not an effective listing.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** No countability of each class is assumed, no uniform bound over n is concluded, and the cover equality includes every member of H. Empty classes and repeated classes/indices are allowed; monotone means inclusion for every m≤n. ε′ has no sign or ordering constraint.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.IsNondecreasingCover`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.commonCore`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.Generic.versionSpace`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.CoveringNumberEq`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.HasFiniteInternalCover`; `GenLimit.MetricSpaces.HasFiniteScaleClosureDimension`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsNondecreasingMetricCover`; `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`; `GenLimit.MetricSpaces.IsScaleClosureWitness`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`; `GenLimit.MetricSpaces.closedNeighborhood`; `GenLimit.MetricSpaces.commonCore`; `GenLimit.MetricSpaces.versionSpace`.

### C04 — `GenLimit.MetricSpaces.Results.theorem_3_5`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:115`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `(none)`.

```lean
∀ {r ε ε' : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε' →
        @LE.le.{0} Real Real.instLE ε r →
          @LE.le.{0} Real Real.instLE ε' r →
            ∃ H₁ H₂,
              And
                (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{0} Real
                  (@Dist.dist.{0} Real (@PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace)) r H₁)
                (And
                  (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{0} Real
                    (@Dist.dist.{0} Real (@PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace)) r H₂)
                  (And
                    (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{0} Real
                      (@Dist.dist.{0} Real (@PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace)) ε ε' H₁)
                    (And
                      (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{0} Real
                        (@Dist.dist.{0} Real (@PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace)) ε ε' H₂)
                      (Not
                        (@GenLimit.MetricSpaces.GeneratableInLimitAt.{0} Real
                          (@Dist.dist.{0} Real (@PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace)) ε ε'
                          (@Union.union.{0} (GenLimit.Generic.LanguageClass.{0} Real)
                            (@Set.instUnion.{0} (GenLimit.Generic.Language.{0} Real)) H₁ H₂))))))
```

**Reconstruction.** For each r>0 and two positive scales ε,ε′ no larger than r, there exist two classes H₁,H₂ of real subsets, each with uniformly unbounded support at r and each uniformly generatable at (ε,ε′), while their union is not generatable in the limit at the same scales. All properties use the ordinary real distance.

**Quantifier skeleton and dependencies.** ∀{r ε ε′:ℝ},0<r→0<ε→0<ε′→ε≤r→ε′≤r→∃H₁ H₂: Set(Set ℝ), Bdist(r,H₁) ∧ Bdist(r,H₂) ∧ Udist(ε,ε′,H₁) ∧ Udist(ε,ε′,H₂) ∧ ¬Ldist(ε,ε′,H₁∪H₂). H₁,H₂ may depend on r,ε,ε′. Each U contains its own ∃g∃d. The negation ranges over all finite-history functions, not just a chosen algorithm.

**Information available to the learner.** Any positive witnesses have only prefix input. The target names no class definitions or generators; the two uniform generators need not coincide.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** Equality ε=r or ε′=r is allowed; no order between ε and ε′ is imposed. This is class union, not pointwise union of two languages. H₁,H₂ are chosen before the conjunction, so the same two classes satisfy all five components. The target asserts no threshold or construction uniform in the three real parameters.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.GeneratableInLimitAt`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsLimitGeneratorAt`; `GenLimit.MetricSpaces.IsUniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.UniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C05 — `GenLimit.MetricSpaces.Results.corollary_4_3`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:174`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ (E : Type u_1) [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : @NormedSpace.{0, u_1} Real E Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} E inst)]
  [@FiniteDimensional.{0, u_1} Real E Real.instDivisionRing (@NormedAddCommGroup.toAddCommGroup.{u_1} E inst)
      (@NormedSpace.toModule.{0, u_1} Real E Real.normedField
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} E inst) inst_1)]
  {H : GenLimit.Generic.LanguageClass.{u_1} E} {r δ δ' ε ε' : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r →
    @GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{u_1} E
        (@Dist.dist.{u_1} E
          (@PseudoMetricSpace.toDist.{u_1} E
            (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} E
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} E inst))))
        r H →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ' →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε' →
              And
                (Iff
                  (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} E
                    (@Dist.dist.{u_1} E
                      (@PseudoMetricSpace.toDist.{u_1} E
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} E
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} E inst))))
                    ε ε' H)
                  (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} E
                    (@Dist.dist.{u_1} E
                      (@PseudoMetricSpace.toDist.{u_1} E
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} E
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} E inst))))
                    δ δ' H))
                (Iff
                  (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} E
                    (@Dist.dist.{u_1} E
                      (@PseudoMetricSpace.toDist.{u_1} E
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} E
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} E inst))))
                    ε ε' H)
                  (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} E
                    (@Dist.dist.{u_1} E
                      (@PseudoMetricSpace.toDist.{u_1} E
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_1} E
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} E inst))))
                    δ δ' H))
```

**Reconstruction.** For every type E with a normed additive commutative group structure, a compatible real normed-space structure, and finite dimension over ℝ, any class H with uniformly unbounded support at some positive r has uniform and nonuniform generatability invariant between any two positive scale pairs (ε,ε′) and (δ,δ′), measured by the distance induced by the given norm. The result is the conjunction of those two equivalences.

**Quantifier skeleton and dependencies.** ∀(E:Type u)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{H}{r δ δ′ ε ε′:ℝ},0<r→Bdist(r,H)→0<δ→0<δ′→0<ε→0<ε′→[(Udist(ε,ε′,H)↔Udist(δ,δ′,H)) ∧ (Ndist(ε,ε′,H)↔Ndist(δ,δ′,H))]. All typeclass structures are global binders; no bound/order relating the scales to r is required.

**Information available to the learner.** The semantic generators are chosen for the fixed normed space, class and scales; their types expose only prefixes, without a coordinate system, dimension input, or norm oracle interface.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** The displayed Bdist premise must be preserved even though other exported endpoints have different assumptions. All four generation scales are strictly positive, with no order among them. No limit-generation equivalence or numeric dimension-dependent threshold is stated.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`; `GenLimit.MetricSpaces.IsUniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C05 — `GenLimit.MetricSpaces.Results.theorem_4_1`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:131`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} {ρ : GenLimit.MetricSpaces.Distance.{u_1} α} {H : GenLimit.Generic.LanguageClass.{u_1} α} {r : Real},
  @GenLimit.MetricSpaces.IsDoublingDistance.{u_1} α ρ →
    (∀ (x : α), @Eq.{1} Real (ρ x x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
      (∀ (x y : α), @Eq.{1} Real (ρ x y) (ρ y x)) →
        (∀ (x y z : α),
            @LE.le.{0} Real Real.instLE (ρ x z)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ρ x y) (ρ y z))) →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r →
            @GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{u_1} α ρ r H →
              ∀ (r' : Real),
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    r' →
                  @GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{u_1} α ρ r' H
```

**Reconstruction.** If ρ is doubling, diagonal-zero, symmetric, and satisfies the triangle inequality, then uniformly unbounded support of H at one positive r implies uniformly unbounded support of the same H at every positive r′. The doubling property has one positive natural multiplicity M common to all centers and positive radii, with at most M ambient centers covering every closed radius-r ball by closed radius-r/2 balls.

**Quantifier skeleton and dependencies.** ∀{α}{ρ}{H}{r}, Double(ρ)→(∀x,ρxx=0)→(∀x y,ρxy=ρyx)→(∀x y z,ρxz≤ρxy+ρyz)→0<r→Bρ(r,H)→∀r′:ℝ,0<r′→Bρ(r′,H). Bρ(r′,H) expands as ∀L∈H,L.Nonempty ∧ ∀stream,Presentationρ(r′,stream,L)→∀d:ℕ,∃t,CAρ(r′,S_t,d). The growth time can depend on L,stream,d,r′.

**Information available to the learner.** This is a property of languages and streams, with no learner, algorithm, numerical growth rate, or support oracle.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** No Nonempty α or nonempty H instance is assumed. Empty H makes B vacuous. Each language is explicitly required nonempty, but its stream clause is conditional on existence of a metric presentation. There is no separate strict positivity/separation axiom on distinct points and no displayed nonnegativity axiom.

**Recursive definitions reviewed.** `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsDoublingDistance`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C05 — `GenLimit.MetricSpaces.Results.theorem_4_2`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:150`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} {ρ : GenLimit.MetricSpaces.Distance.{u_1} α} {δ δ' ε ε' : Real}
  {H : GenLimit.Generic.LanguageClass.{u_1} α},
  @GenLimit.MetricSpaces.IsDoublingDistance.{u_1} α ρ →
    (∀ (x : α), @Eq.{1} Real (ρ x x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
      (∀ (x y : α), @Eq.{1} Real (ρ x y) (ρ y x)) →
        (∀ (x y z : α),
            @LE.le.{0} Real Real.instLE (ρ x z)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ρ x y) (ρ y z))) →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ →
            @LT.lt.{0} Real Real.instLT δ ε →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  δ' →
                @LT.lt.{0} Real Real.instLT δ' ε' →
                  And
                    (Iff (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} α ρ ε ε' H)
                      (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} α ρ δ δ' H))
                    (Iff (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} α ρ ε ε' H)
                      (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} α ρ δ δ' H))
```

**Reconstruction.** For every doubling, diagonal-zero, symmetric, triangle-inequality real distance and every class H, uniform generatability at (ε,ε′) is equivalent to that at (δ,δ′), and nonuniform generatability has the same equivalence, whenever 0<δ<ε and 0<δ′<ε′. Both equivalences are part of one conjunction.

**Quantifier skeleton and dependencies.** ∀{α}{ρ}{δ δ′ ε ε′:ℝ}{H},Double(ρ)→diag0→symm→triangle→0<δ→δ<ε→0<δ′→δ′<ε′→[(Uρ(ε,ε′,H)↔Uρ(δ,δ′,H)) ∧ (Nρ(ε,ε′,H)↔Nρ(δ,δ′,H))]. Each side has its own semantic ∃g (and ∃d for U); the type does not identify the witnesses.

**Information available to the learner.** No named program or access model beyond the finite-history function definition is supplied.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** No unbounded-support assumption is present. No Nonempty α is assumed. Only the displayed strict inequalities are covered directly, not equality at either smaller scale. No equivalence for L (generation in the limit) is included.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsDoublingDistance`; `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`; `GenLimit.MetricSpaces.IsUniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyGeneratableAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C06 — `GenLimit.MetricSpaces.Results.theorem_4_4`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:192`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} {ρ₁ ρ₂ : GenLimit.MetricSpaces.Distance.{u_1} α} {M₁₂ M₂₁ r₁ r₂ ε₁ ε₁' ε₂ ε₂' : Real}
  {H : GenLimit.Generic.LanguageClass.{u_1} α},
  @GenLimit.MetricSpaces.IsDoublingDistance.{u_1} α ρ₁ →
    (∀ (x : α), @Eq.{1} Real (ρ₁ x x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
      (∀ (x y : α), @Eq.{1} Real (ρ₁ x y) (ρ₁ y x)) →
        (∀ (x y z : α),
            @LE.le.{0} Real Real.instLE (ρ₁ x z)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ρ₁ x y) (ρ₁ y z))) →
          (∀ (x : α),
              @Eq.{1} Real (ρ₂ x x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
            (∀ (x y : α), @Eq.{1} Real (ρ₂ x y) (ρ₂ y x)) →
              (∀ (x y z : α),
                  @LE.le.{0} Real Real.instLE (ρ₂ x z)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ρ₂ x y) (ρ₂ y z))) →
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    M₁₂ →
                  @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) M₂₁ →
                    @GenLimit.MetricSpaces.MutuallyLipschitzDominated.{u_1} α ρ₁ ρ₂ M₁₂ M₂₁ →
                      @LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r₁ →
                        @LT.lt.{0} Real Real.instLT
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r₂ →
                          @LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε₁ →
                            @LT.lt.{0} Real Real.instLT
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε₁' →
                              @LT.lt.{0} Real Real.instLT
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε₂ →
                                @LT.lt.{0} Real Real.instLT
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε₂' →
                                  And
                                    (Iff (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{u_1} α ρ₁ r₁ H)
                                      (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{u_1} α ρ₂ r₂ H))
                                    (And
                                      (Iff (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} α ρ₁ ε₁ ε₁' H)
                                        (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} α ρ₂ ε₂ ε₂' H))
                                      (Iff (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} α ρ₁ ε₁ ε₁' H)
                                        (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} α ρ₂ ε₂ ε₂' H)))
```

**Reconstruction.** For two real distance functions on the same type, assume the first is doubling, both are diagonal-zero, symmetric and satisfy the triangle inequality, and there are positive constants M₁₂,M₂₁ such that ρ₂≤M₁₂ρ₁ and ρ₁≤M₂₁ρ₂ pointwise. At arbitrary independent positive support radii r₁,r₂ and arbitrary independent positive generation scales ε₁,ε₁′,ε₂,ε₂′, the same class H has equivalent uniformly unbounded support at the two respective radii, equivalent uniform generatability at the two respective scale pairs, and equivalent nonuniform generatability at those scale pairs. All three equivalences are conjuncts.

**Quantifier skeleton and dependencies.** ∀{α}{ρ₁ ρ₂}{M₁₂ M₂₁ r₁ r₂ ε₁ ε₁′ ε₂ ε₂′:ℝ}{H},Double(ρ₁)→diag0(ρ₁)→symm(ρ₁)→triangle(ρ₁)→diag0(ρ₂)→symm(ρ₂)→triangle(ρ₂)→0<M₁₂→0<M₂₁→[(∀x y,ρ₂xy≤M₁₂*ρ₁xy) ∧ (∀x y,ρ₁xy≤M₂₁*ρ₂xy)]→0<r₁→0<r₂→0<ε₁→0<ε₁′→0<ε₂→0<ε₂′→[(Bρ₁(r₁,H)↔Bρ₂(r₂,H)) ∧ (Uρ₁(ε₁,ε₁′,H)↔Uρ₂(ε₂,ε₂′,H)) ∧ (Nρ₁(ε₁,ε₁′,H)↔Nρ₂(ε₂,ε₂′,H))]. The exact exported type below retains the separate universally quantified domination clauses.

**Information available to the learner.** No generator identity or algorithm is named; semantic witnesses can depend on the distance, scales and H.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** Only ρ₁ has an explicit doubling assumption. B is an equivalence in the conclusion, not a premise that H has unbounded support. No ordering or ratio constraints connect the six positive radii/scales or either M. No Nonempty α and no L-equivalence is included.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.DistanceDominatedBy`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsDoublingDistance`; `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`; `GenLimit.MetricSpaces.IsUniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.MutuallyLipschitzDominated`; `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C07 — `GenLimit.MetricSpaces.Results.theorem_4_6`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:234`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} {ρ : GenLimit.MetricSpaces.Distance.{u_1} α} {H : GenLimit.Generic.LanguageClass.{u_1} α}
  {δ δ' ε ε' : Real},
  @LE.le.{0} Real Real.instLE δ ε →
    @LE.le.{0} Real Real.instLE δ' ε' →
      @GenLimit.MetricSpaces.GeneratableInLimitAt.{u_1} α ρ ε ε' H →
        @GenLimit.MetricSpaces.GeneratableInLimitAt.{u_1} α ρ δ δ' H
```

**Reconstruction.** For every type, arbitrary real function ρ and class H, generation in the limit at (ε,ε′) implies generation in the limit at (δ,δ′) whenever δ≤ε and δ′≤ε′.

**Quantifier skeleton and dependencies.** ∀{α}{ρ}{H}{δ δ′ ε ε′:ℝ},δ≤ε→δ′≤ε′→Lρ(ε,ε′,H)→Lρ(δ,δ′,H). Each L expands as ∃g∀L∈H∀stream,Presentationρ(inputScale,stream,L)→∃T∀t≥T,Correctρ(outputScale,g,L,stream,t). No witness equality is part of the target.

**Information available to the learner.** The underlying generator interface is finite prefix only. No metric laws, ability to decide distance comparisons, or explicit transfer program is an assumption.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** All scales may be zero or negative and equalities are allowed. The input scale decreases here. There are no uniform/nonuniform or support conclusions, no Nonempty α assumption, and no rate or common stabilization time.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.GeneratableInLimitAt`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsLimitGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C07 — `GenLimit.MetricSpaces.Results.theorem_4_7`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:246`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} {ρ : GenLimit.MetricSpaces.Distance.{u_1} α} {H : GenLimit.Generic.LanguageClass.{u_1} α}
  {ε ε' δ δ' : Real},
  @LE.le.{0} Real Real.instLE ε δ →
    @LE.le.{0} Real Real.instLE δ' ε' →
      And
        (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} α ρ ε ε' H →
          @GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} α ρ δ δ' H)
        (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} α ρ ε ε' H →
          @GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} α ρ δ δ' H)
```

**Reconstruction.** For arbitrary ρ and H, if ε≤δ and δ′≤ε′, uniform generatability at (ε,ε′) implies uniform generatability at (δ,δ′), and nonuniform generatability obeys the same implication. Both implications are asserted.

**Quantifier skeleton and dependencies.** ∀{α}{ρ}{H}{ε ε′ δ δ′:ℝ},ε≤δ→δ′≤ε′→[(Uρ(ε,ε′,H)→Uρ(δ,δ′,H)) ∧ (Nρ(ε,ε′,H)→Nρ(δ,δ′,H))]. U has ∃g∃d∀L∈H∀stream∀t∀s≥t; N has ∃g∀L∈H∃d∀stream∀t∀s≥t; triggers use CA at the respective input scale.

**Information available to the learner.** No named transferred program or covering-number decision procedure is supplied.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** No positivity or metric laws are required; equality is allowed. The input scale increases (ε≤δ), which must not be replaced by the input inequality in theorem_4_6. Neither reverse implication nor L property is concluded.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`; `GenLimit.MetricSpaces.IsUniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyGeneratableAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C08 — `GenLimit.MetricSpaces.Results.theorem_4_10`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:307`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} {ρ₁ ρ₂ : GenLimit.MetricSpaces.Distance.{u_1} α} {M r ε ε' : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) M →
    @GenLimit.MetricSpaces.DistanceDominatedBy.{u_1} α ρ₂ ρ₁ M →
      ∀ {H : GenLimit.Generic.LanguageClass.{u_1} α},
        And
          (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{u_1} α ρ₂ r H →
            @GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{u_1} α ρ₁
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) r M)
              H)
          (@GenLimit.MetricSpaces.GeneratableInLimitAt.{u_1} α ρ₂ ε ε' H →
            @GenLimit.MetricSpaces.GeneratableInLimitAt.{u_1} α ρ₁
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) ε M)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) ε' M)
              H)
```

**Reconstruction.** For arbitrary real functions ρ₁,ρ₂ with ρ₂(x,y)≤Mρ₁(x,y) everywhere and positive M, every class H satisfies both of these implications: uniformly unbounded support under ρ₂ at r implies it under ρ₁ at r/M; and generation in the limit under ρ₂ at (ε,ε′) implies it under ρ₁ at (ε/M,ε′/M).

**Quantifier skeleton and dependencies.** ∀{α}{ρ₁ ρ₂}{M r ε ε′:ℝ},0<M→(∀x y,ρ₂xy≤M*ρ₁xy)→∀{H:Set(Set α)},[(Bρ₂(r,H)→Bρ₁(r/M,H)) ∧ (Lρ₂(ε,ε′,H)→Lρ₁(ε/M,ε′/M,H))]. M and the scales are fixed before H; the theorem is universal in H. No reverse direction is asserted.

**Information available to the learner.** There is no named generator in the target, no division operation offered to a learner, and no specified oracle. The claims concern semantic properties.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** No signs for r,ε,ε′ and no metric axioms or Nonempty α are assumed. M>0 rules out division by zero. The dominance direction is ρ₂≤Mρ₁, and both generation scales divide by that same M. No U or N transfer is included.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.DistanceDominatedBy`; `GenLimit.MetricSpaces.GeneratableInLimitAt`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsLimitGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C09 — `GenLimit.MetricSpaces.Results.proposition_D_1`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:347`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `u_1`.

```lean
∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] {ε ε' : Real} {H : GenLimit.Generic.LanguageClass.{u_1} α},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε' →
        @LT.lt.{0} Real Real.instLT ε' (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
          And
            (Iff
              (@GenLimit.MetricSpaces.GeneratableInLimitAt.{u_1} α
                (@GenLimit.MetricSpaces.discreteDistance.{u_1} α inst) ε ε' H)
              (@GenLimit.LiRamanTewari.GeneratableInLimit.{u_1} α H))
            (And
              (Iff
                (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{u_1} α
                  (@GenLimit.MetricSpaces.discreteDistance.{u_1} α inst) ε ε' H)
                (@GenLimit.LiRamanTewari.UniformlyGeneratable.{u_1} α H))
              (Iff
                (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{u_1} α
                  (@GenLimit.MetricSpaces.discreteDistance.{u_1} α inst) ε ε' H)
                (@GenLimit.LiRamanTewari.NonuniformlyGeneratable.{u_1} α H)))
```

**Reconstruction.** For every type α with decidable equality, every class H and scales in [0,1), using the 0/1 discrete distance yields three equivalences: metric generation in the limit equals the generic exact-presentation property; metric uniform generation equals generic uniform generation; and metric nonuniform generation equals generic nonuniform generation. The right-hand-side namespaces are aliases to the supplied generic definitions, not external paper claims. The generic uniform/nonuniform triggers use equality of distinct-sample cardinality with d, while metric triggers use a covering lower bound.

**Quantifier skeleton and dependencies.** ∀{α}[DecidableEq α]{ε ε′:ℝ}{H},0≤ε→ε<1→0≤ε′→ε′<1→[(Ldiscrete(ε,ε′,H)↔GenericL(H)) ∧ (Udiscrete(ε,ε′,H)↔GenericU(H)) ∧ (Ndiscrete(ε,ε′,H)↔GenericN(H))]. GenericL=∃g∀L∈H∀stream,(range stream=L)→∃T∀s≥T,[output∈L∧output∉S_s]. GenericU=∃g∃d∀L∈H∀stream,StreamIn→∀t,|S_t|=d→∀s≥t,GenericCorrect; GenericN=∃g∀L∈H∃d∀stream,StreamIn→∀t,|S_t|=d→∀s≥t,GenericCorrect.

**Information available to the learner.** Each side quantifies semantic functions on the same finite-history input shape. Decidable equality supplies the discrete-distance case split; it is not a theorem of computability of every quantified generator.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** Zero is included and one excluded for each scale. No Nonempty α, nonempty H, infinitude, or countability assumption occurs. On empty α no total generator exists, so even empty H does not remove that existential obstruction. Finite/exhausted targets and unattained exact-cardinality triggers remain governed by the literal generic definitions.

**Recursive definitions reviewed.** `GenLimit.Generic.CorrectAt`; `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.GeneratableInLimit`; `GenLimit.Generic.Generator`; `GenLimit.Generic.IsLimitGenerator`; `GenLimit.Generic.IsNonuniformGenerator`; `GenLimit.Generic.IsUniformGeneratorAt`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.NonuniformlyGeneratable`; `GenLimit.Generic.Presents`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.UniformlyGeneratable`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.LiRamanTewari.GeneratableInLimit`; `GenLimit.LiRamanTewari.NonuniformlyGeneratable`; `GenLimit.LiRamanTewari.UniformlyGeneratable`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.GeneratableInLimitAt`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsLimitGeneratorAt`; `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`; `GenLimit.MetricSpaces.IsUniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyGeneratableAt`; `GenLimit.MetricSpaces.closedNeighborhood`; `GenLimit.MetricSpaces.discreteDistance`.

### C10 — `GenLimit.MetricSpaces.Results.example_4_5`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:221`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `(none)`.

```lean
∀ {ε : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      And
        (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{0} Real
          GenLimit.MetricSpaces.RealLineThreshold.realDistance
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          GenLimit.MetricSpaces.RealLineThreshold.languageClass)
        (And
          (@GenLimit.MetricSpaces.GeneratableInLimitAt.{0} Real GenLimit.MetricSpaces.RealLineThreshold.realDistance ε
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            GenLimit.MetricSpaces.RealLineThreshold.languageClass)
          (Not
            (@GenLimit.MetricSpaces.GeneratableInLimitAt.{0} Real GenLimit.MetricSpaces.RealLineThreshold.realDistance
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              GenLimit.MetricSpaces.RealLineThreshold.languageClass)))
```

**Reconstruction.** For every 0<ε<1, a specific class of real languages has uniformly unbounded support at 1, is generatable in the limit at (ε,1), and is not generatable in the limit at (1,1), for the absolute-value distance. Its languages are exactly primePairSupport(p)∪B for an odd natural prime p and an arbitrary subset B of the positive even integers. primePairSupport(p) consists of real casts of p^(n+1) and of the natural-number subtraction p^(n+1)−1, for n∈ℕ.

**Quantifier skeleton and dependencies.** ∀{ε:ℝ},0<ε→ε<1→[Babs(1,Hreal) ∧ Labs(ε,1,Hreal) ∧ ¬Labs(1,1,Hreal)], where Hreal={L|∃p:ℕ,Prime(p)∧Odd(p)∧∃B⊆{(2*(n+1):ℕ) cast to ℝ|n:ℕ},L={cast(p^(n+1)),cast(p^(n+1)−1)|n:ℕ}∪B}. Hreal is fixed independently of ε. In the positive L clause ∃g is inside ∀ε, and T may depend on L and stream.

**Information available to the learner.** The generator receives only observed real prefixes, not the prime p, B, L or a membership oracle. The target supplies a named class and distance but no named generator.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** The three conjuncts all refer to the same class. The negative clause fixes both scales at 1 and denies all semantic generators. The theorem does not include ε=0 or ε=1 for its positive clause. B may be empty or arbitrary; primality and oddness are separate predicates retained from the definition.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.GeneratableInLimitAt`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsLimitGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.RealLineThreshold.languageClass`; `GenLimit.MetricSpaces.RealLineThreshold.positiveEvenIntegers`; `GenLimit.MetricSpaces.RealLineThreshold.primePairSupport`; `GenLimit.MetricSpaces.RealLineThreshold.realDistance`; `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C11 — `GenLimit.MetricSpaces.Results.example_4_8`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:263`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `(none)`.

```lean
∀ {r ε ε' : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
      @LE.le.{0} Real Real.instLE ε r →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε' →
          @LE.le.{0} Real Real.instLE ε' r →
            have H := GenLimit.MetricSpaces.HilbertAxisReservoir.example48LanguageClass r ε ε';
            And
              (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{0}
                (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                GenLimit.MetricSpaces.HilbertAxisReservoir.hilbertDistance r H)
              (And
                (∀ (γ γ' : Real),
                  @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ →
                    @LE.le.{0} Real Real.instLE γ r →
                      @LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ' →
                        @LE.le.{0} Real Real.instLE γ' r →
                          Iff
                            (@GenLimit.MetricSpaces.GeneratableInLimitAt.{0}
                              (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                              GenLimit.MetricSpaces.HilbertAxisReservoir.hilbertDistance γ γ' H)
                            (And (@LT.lt.{0} Real Real.instLT γ ε) (@LT.lt.{0} Real Real.instLT γ' ε')))
                (∀ (γ γ' : Real),
                  @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ →
                    @LT.lt.{0} Real Real.instLT γ ε →
                      @LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ' →
                        @LT.lt.{0} Real Real.instLT γ' ε' →
                          @GenLimit.MetricSpaces.IsLimitGeneratorAt.{0}
                            (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                            GenLimit.MetricSpaces.HilbertAxisReservoir.hilbertDistance γ γ'
                            (GenLimit.MetricSpaces.HilbertAxisReservoir.example48CausalGenerator ε ε' γ') H))
```

**Reconstruction.** For each r>0, 0<ε≤r and 0<ε′≤r, let H be the explicitly defined example48LanguageClass(r,ε,ε′) on real ℓ²(ℕ). Then H has uniformly unbounded support at r. For every 0<γ≤r and 0<γ′≤r, H is generatable in the limit at (γ,γ′) exactly when γ<ε and γ′<ε′. Moreover, for every 0<γ<ε and 0<γ′<ε′, the explicitly named example48CausalGenerator(ε,ε′,γ′) is a limit generator for H at (γ,γ′). The class and generator definitions are reconstructed in the glossary and dedicated algorithm paragraph.

**Quantifier skeleton and dependencies.** ∀{r ε ε′:ℝ},0<r→0<ε→ε≤r→0<ε′→ε′≤r→let H=example48LanguageClass r ε ε′; [Bhilbert(r,H) ∧ (∀γ γ′:ℝ,0<γ→γ≤r→0<γ′→γ′≤r→(Lhilbert(γ,γ′,H)↔(γ<ε∧γ′<ε′))) ∧ (∀γ γ′:ℝ,0<γ→γ<ε→0<γ′→γ′<ε′→IsLimitGeneratorAt(hilbertDistance,γ,γ′,example48CausalGenerator ε ε′ γ′,H))]. H is fixed before both ∀γγ′ clauses. The named g does not depend on γ or r; for a fixed γ′ it is the same function for every permitted γ. It does depend on γ′, and no single function for all γ′ is asserted.

**Information available to the learner.** The named function takes ε,ε′,γ′ as fixed parameters and at run time t and xs:Fin t→ℓ². It inspects only that prefix; no stream tail, r, γ, target language, hidden index sets, membership oracle, or persistent state is an argument.

**Algorithm scope.** This target names a total finite-history function, defined by classical proposition decidability and Classical.choose. Given xs, it tests existence of a candidate y; if one exists it chooses an unspecified candidate, otherwise returns the zero vector. A candidate has some k≥2 with an observed point ε e_(2k), and y=ε′ e_(2*k^(n+1)+1) for some n:ℕ, outside the γ′ closed neighborhood of the distinct prefix sample. This is a causal semantic choice rule, without a supplied effective decision/search operation, tie-break rule, numerical representation, oracle interface, or runtime proof. Its correctness assertion is eventual for each metric presentation, not correctness at every prefix. No algorithm proof body was inspected.

**Edge cases and vacuity.** Threshold equalities γ=ε or γ′=ε′ fail within the stated positive rectangle; ε=r and ε′=r are allowed. No claim covers γ=0,γ′=0 or scales beyond r. The named generator fallback can occur before stabilization. All three hidden index sets are infinite and contain only positive naturals; no pairwise disjointness or primality restriction is imposed on them. Powers in the class include n=0, whereas the candidate uses n+1.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.Generic.sequenceSample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.GeneratableInLimitAt`; `GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2`; `GenLimit.MetricSpaces.HilbertAxisReservoir.IsExample48CausalCandidate`; `GenLimit.MetricSpaces.HilbertAxisReservoir.axisPoint`; `GenLimit.MetricSpaces.HilbertAxisReservoir.example48A`; `GenLimit.MetricSpaces.HilbertAxisReservoir.example48CausalGenerator`; `GenLimit.MetricSpaces.HilbertAxisReservoir.example48Disturbing`; `GenLimit.MetricSpaces.HilbertAxisReservoir.example48G`; `GenLimit.MetricSpaces.HilbertAxisReservoir.example48Language`; `GenLimit.MetricSpaces.HilbertAxisReservoir.example48LanguageClass`; `GenLimit.MetricSpaces.HilbertAxisReservoir.example48Optimal`; `GenLimit.MetricSpaces.HilbertAxisReservoir.example48U`; `GenLimit.MetricSpaces.HilbertAxisReservoir.example48USet`; `GenLimit.MetricSpaces.HilbertAxisReservoir.example48Zero`; `GenLimit.MetricSpaces.HilbertAxisReservoir.hilbertDistance`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsLimitGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C12 — `GenLimit.MetricSpaces.Results.example_4_9`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:288`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `(none)`.

```lean
∀ {r ε₁ ε₂ ε' : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε₁ →
      @LE.le.{0} Real Real.instLE ε₁ ε₂ →
        @LE.le.{0} Real Real.instLE ε₂ r →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε' →
            @LE.le.{0} Real Real.instLE ε' r →
              ∃ H,
                And
                  (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{0}
                    (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                    (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                      (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                          (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                            (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                            (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                              (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                      instAddCommMonoidWithOneENNReal))
                                  GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                              (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
                    r H)
                  (And
                    (∀ (γ γ' : Real),
                      @LE.le.{0} Real Real.instLE ε₂ γ →
                        @LE.le.{0} Real Real.instLE γ r →
                          @LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ' →
                            @LT.lt.{0} Real Real.instLT γ' ε' →
                              @GenLimit.MetricSpaces.UniformlyGeneratableAt.{0}
                                (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                  (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                    (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                                      (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                                        (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                        (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                                          (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                            (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                                  instAddCommMonoidWithOneENNReal))
                                              GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                                          (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
                                γ γ' H)
                    (And
                      (∀ (γ γ' : Real),
                        @LE.le.{0} Real Real.instLE ε₁ γ →
                          @LT.lt.{0} Real Real.instLT γ ε₂ →
                            @LT.lt.{0} Real Real.instLT
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ' →
                              @LT.lt.{0} Real Real.instLT γ' ε' →
                                And
                                  (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{0}
                                    (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                    (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                      (@PseudoMetricSpace.toDist.{0}
                                        (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                                          (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                                            (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                            (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                                              (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                                (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                                      instAddCommMonoidWithOneENNReal))
                                                  GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                                              (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
                                    γ γ' H)
                                  (Not
                                    (@GenLimit.MetricSpaces.UniformlyGeneratableAt.{0}
                                      (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                      (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                        (@PseudoMetricSpace.toDist.{0}
                                          (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                          (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                                            (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                                              (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                              (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                                                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                                        instAddCommMonoidWithOneENNReal))
                                                    GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                                                (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
                                      γ γ' H)))
                      (And
                        (∀ (γ γ' : Real),
                          @LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ →
                            @LT.lt.{0} Real Real.instLT γ ε₁ →
                              @LT.lt.{0} Real Real.instLT
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ' →
                                @LT.lt.{0} Real Real.instLT γ' ε' →
                                  And
                                    (@GenLimit.MetricSpaces.GeneratableInLimitAt.{0}
                                      (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                      (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                        (@PseudoMetricSpace.toDist.{0}
                                          (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                          (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                                            (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                                              (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                              (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                                                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                                        instAddCommMonoidWithOneENNReal))
                                                    GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                                                (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
                                      γ γ' H)
                                    (Not
                                      (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{0}
                                        (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                        (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                          (@PseudoMetricSpace.toDist.{0}
                                            (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                            (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                                              (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                                                (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                                (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                                                  (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                                    (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                                          instAddCommMonoidWithOneENNReal))
                                                      GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                                                  (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
                                        γ γ' H)))
                        (∀ (γ γ' : Real),
                          @LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ →
                            @LE.le.{0} Real Real.instLE γ r →
                              @LE.le.{0} Real Real.instLE ε' γ' →
                                @LE.le.{0} Real Real.instLE γ' r →
                                  Not
                                    (@GenLimit.MetricSpaces.GeneratableInLimitAt.{0}
                                      (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                      (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                        (@PseudoMetricSpace.toDist.{0}
                                          (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                          (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                                            (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                                              (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                                              (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                                                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                                        instAddCommMonoidWithOneENNReal))
                                                    GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                                                (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
                                      γ γ' H)))))
```

**Reconstruction.** For each r>0, 0<ε₁≤ε₂≤r and 0<ε′≤r, there exists one class H of subsets of real ℓ²(ℕ) with all five properties: (1) uniformly unbounded support at r; (2) uniform generatability at every (γ,γ′) with ε₂≤γ≤r and 0<γ′<ε′; (3) nonuniform but not uniform generatability when ε₁≤γ<ε₂ and 0<γ′<ε′; (4) generation in the limit but no nonuniform generatability when 0<γ<ε₁ and 0<γ′<ε′; (5) no generation in the limit when 0<γ≤r and ε′≤γ′≤r. These are simultaneously quantified regions for the same H.

**Quantifier skeleton and dependencies.** ∀{r ε₁ ε₂ ε′:ℝ},0<r→0<ε₁→ε₁≤ε₂→ε₂≤r→0<ε′→ε′≤r→∃H:Set(Set ℓ²), [Bdist(r,H) ∧ (∀γ γ′,ε₂≤γ→γ≤r→0<γ′→γ′<ε′→Udist(γ,γ′,H)) ∧ (∀γ γ′,ε₁≤γ→γ<ε₂→0<γ′→γ′<ε′→[Ndist(γ,γ′,H)∧¬Udist(γ,γ′,H)]) ∧ (∀γ γ′,0<γ→γ<ε₁→0<γ′→γ′<ε′→[Ldist(γ,γ′,H)∧¬Ndist(γ,γ′,H)]) ∧ (∀γ γ′,0<γ→γ≤r→ε′≤γ′→γ′≤r→¬Ldist(γ,γ′,H))]. H depends on the four parameters but precedes all γ,γ′ quantifiers. Positive generators and thresholds may depend on γ,γ′ because their existentials are inside the corresponding ∀ clauses.

**Information available to the learner.** No named class witness or generator is exposed by the target type. All positive generator witnesses share the finite-prefix interface; their existence supplies no target language as an input.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** ε₁=ε₂ is allowed, making the middle region empty. ε₂=r leaves the top region at γ=r; ε′=r leaves the forbidden output strip at γ′=r. The lower and middle positive-output inequalities are strict, and the forbidden strip includes γ′=ε′. The target makes no assertion at zero input/output scales or beyond r. The negative statements rule out all semantic generators for the stated property, not just named procedures.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.GeneratableInLimitAt`; `GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsLimitGeneratorAt`; `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`; `GenLimit.MetricSpaces.IsUniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C13 — `GenLimit.MetricSpaces.Results.example_4_11`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:320`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `(none)`.

```lean
∀ {r : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r →
    ∃ H metric',
      And
        (@GenLimit.MetricSpaces.MutuallyLipschitzDominated.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
          (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
            (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                  (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
                        GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                    (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
          (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
            (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
              (@MetricSpace.toPseudoMetricSpace.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) metric')))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2) (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast ⋯)))
        (And
          (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
            (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
              (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                    (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                    (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
                          GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                      (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
            r H)
          (And
            (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{0}
              (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
              (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                  (@MetricSpace.toPseudoMetricSpace.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                    metric')))
              r H)
            (And
              (∀ (ε : Real),
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    ε →
                  @LT.lt.{0} Real Real.instLT ε r →
                    @GenLimit.MetricSpaces.UniformlyGeneratableAt.{0}
                      (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                      (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                        (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                          (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                            (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                              (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                              (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                        instAddCommMonoidWithOneENNReal))
                                    GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                                (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
                      ε ε H)
              (∀ (ε : Real),
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    ε →
                  @LT.lt.{0} Real Real.instLT ε r →
                    Not
                      (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{0}
                        (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                        (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                          (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                            (@MetricSpace.toPseudoMetricSpace.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                              metric')))
                        ε ε H)))))
```

**Reconstruction.** For every r>0 there exist one class H of subsets of real ℓ²(ℕ) and one alternate MetricSpace structure metric′ on that same underlying type. If d is its original norm distance and d′ the distance of metric′, then d′≤d and d≤2d′ pointwise; H has uniformly unbounded support at r for both distances; at every 0<ε<r H is uniformly generatable at (ε,ε) under d; and at every such ε H is not nonuniformly generatable at (ε,ε) under d′. The five conjuncts are all required.

**Quantifier skeleton and dependencies.** ∀{r:ℝ},0<r→∃H:Set(Set ℓ²)∃metric′:MetricSpace ℓ², [(∀x y,d′xy≤1*dxy) ∧ (∀x y,dxy≤2*d′xy)] ∧ Bd(r,H) ∧ Bd′(r,H) ∧ (∀ε:ℝ,0<ε→ε<r→Ud(ε,ε,H)) ∧ (∀ε:ℝ,0<ε→ε<r→¬Nd′(ε,ε,H)). The pair H,metric′ is chosen after r and before either ∀ε. Generators/thresholds for Ud may vary with ε; metric′ and H do not.

**Information available to the learner.** Both distances live on precisely the same ℓ² underlying type. metric′ is an existential full MetricSpace structure, not a named computation or merely an arbitrary real function. No alternate metric formula or generator witness is identified by this target.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** The domination constants are exactly 1 and 2 with d′ in the first left side; reversing them would change the claim. Both B conjuncts use the same r, and both generation scales equal ε. Neither endpoint ε=0,r is covered. The negative clause is ¬N, not ¬L. There is no explicit doubling premise on either metric in this example.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.DistanceDominatedBy`; `GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`; `GenLimit.MetricSpaces.IsUniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.MutuallyLipschitzDominated`; `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

### C14 — `GenLimit.MetricSpaces.Results.example_B_3`

Kind: `theorem`. Exported source anchor: `GenLimit.Paper21_GenerationInMetricSpaces.Results.Overview:387`. Evidence: `01-target-statements.md` and matching `declarations.jsonl` row. Universe parameters: `(none)`.

```lean
∀ {r ε ε' : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
      @LT.lt.{0} Real Real.instLT ε ε' →
        @LE.le.{0} Real Real.instLE ε' r →
          ∃ H,
            And
              (@Eq.{1} Nat
                (@Set.ncard.{0} (GenLimit.Generic.Language.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) H)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (And
                (@GenLimit.MetricSpaces.UniformlyUnboundedSupportAt.{0}
                  (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                  (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                    (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                        (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                          (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                          (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                            (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    instAddCommMonoidWithOneENNReal))
                                GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                            (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
                  r H)
                (Not
                  (@GenLimit.MetricSpaces.NonuniformlyGeneratableAt.{0}
                    (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                    (@Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                      (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                        (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                          (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                            (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                            (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
                              (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                      instAddCommMonoidWithOneENNReal))
                                  GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
                              (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal)))))
                    ε ε' H)))
```

**Reconstruction.** For every r>0 and scales 0<ε<ε′≤r, there exists a class H of subsets of real ℓ²(ℕ) with Set.ncard H=2, uniformly unbounded support at r, and no nonuniform metric generator at (ε,ε′), using the original ℓ² norm distance.

**Quantifier skeleton and dependencies.** ∀{r ε ε′:ℝ},0<r→0<ε→ε<ε′→ε′≤r→∃H:Set(Set ℓ²), Set.ncard H=2 ∧ Bdist(r,H) ∧ ¬Ndist(ε,ε′,H). H may depend on all three parameters; the nonuniform negation is ¬∃g∀L∈H∃d:ℕ∀stream,StreamIn→∀t,CA(ε,S_t,d)→∀s≥t,Correct(ε′).

**Information available to the learner.** The class is existential and the target identifies neither its two member languages nor an algorithm. The impossibility is over all finite-history functions.

**Algorithm scope.** Semantic existence/property only. No named generator, effective access primitive, runtime bound, or implementation witness is specified by this target type.

**Edge cases and vacuity.** The exact finite-cardinality predicate is Set.ncard H=2 (which forces finiteness under the trusted standard meaning). ε′=r is allowed, ε=ε′ is excluded, and the input scale is strictly smaller than the output scale. No failure of limit generation is asserted and no specific lower-bound stream is supplied.

**Recursive definitions reviewed.** `GenLimit.Generic.FiniteHistoryOperator`; `GenLimit.Generic.Generator`; `GenLimit.Generic.Language`; `GenLimit.Generic.LanguageClass`; `GenLimit.Generic.Stream`; `GenLimit.Generic.StreamIn`; `GenLimit.Generic.output`; `GenLimit.Generic.sample`; `GenLimit.MetricSpaces.CoveringNumberAtLeast`; `GenLimit.MetricSpaces.Distance`; `GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2`; `GenLimit.MetricSpaces.InClosedNeighborhood`; `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`; `GenLimit.MetricSpaces.MetricCorrectAt`; `GenLimit.MetricSpaces.MetricPresentation`; `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`; `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`; `GenLimit.MetricSpaces.closedNeighborhood`.

## Complete recursive-definition appendix

All 65 definition interfaces and values are copied from the frozen declaration rows below, with their exact source anchors. The semantic glossary supplies their interpretations. The three helper theorem interfaces are included at the end; theorem proof bodies are absent and were not requested. Native-census helpers outside this recursive closure were not individually reviewed.

### `GenLimit.Generic.CorrectAt`

Source: `GenLimit.Core.GenericGeneration:367`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} →
  GenLimit.Generic.Generator.{u_1} α → GenLimit.Generic.Language.{u_1} α → GenLimit.Generic.Stream.{u_1} α → Nat → Prop
```

Definition value:
```lean
fun {α} G L stream t =>
  And
    (@Membership.mem.{u_1, u_1} α (GenLimit.Generic.Language.{u_1} α) (@Set.instMembership.{u_1} α) L
      (@GenLimit.Generic.output.{u_1} α G stream t))
    (@GenLimit.Generic.output.{u_1} α G stream t ∉ @GenLimit.Generic.sample.{u_1} α stream t)
```

### `GenLimit.Generic.FiniteHistoryOperator`

Source: `GenLimit.Core.GenericGeneration:37`; universe parameters: `u_1, u_2`.

Type:
```lean
Type u_1 → Type u_2 → Type (max u_1 u_2)
```

Definition value:
```lean
fun Input Output => (t : Nat) → (Fin t → Input) → Output
```

### `GenLimit.Generic.GeneratableInLimit`

Source: `GenLimit.Core.ClassGeneration:22`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} H => ∃ gen, @GenLimit.Generic.IsLimitGenerator.{u_1} α gen H
```

### `GenLimit.Generic.Generator`

Source: `GenLimit.Core.GenericGeneration:41`; universe parameters: `u_1`.

Type:
```lean
Type u_1 → Type u_1
```

Definition value:
```lean
fun α => GenLimit.Generic.FiniteHistoryOperator.{u_1, u_1} α α
```

### `GenLimit.Generic.IsLimitGenerator`

Source: `GenLimit.Core.ClassGeneration:17`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.Generator.{u_1} α → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} gen H =>
  ∀ (L : GenLimit.Generic.Language.{u_1} α),
    @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
        (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) H L →
      ∀ (stream : GenLimit.Generic.Stream.{u_1} α),
        @GenLimit.Generic.Presents.{u_1} α stream L →
          ∃ T, ∀ (s : Nat), @LE.le.{0} Nat instLENat T s → @GenLimit.Generic.CorrectAt.{u_1} α gen L stream s
```

### `GenLimit.Generic.IsNondecreasingCover`

Source: `GenLimit.Core.ClassCovers:14`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → (Nat → GenLimit.Generic.LanguageClass.{u_1} α) → Prop
```

Definition value:
```lean
fun {α} H classes =>
  And
    (@Monotone.{0, u_1} Nat (GenLimit.Generic.LanguageClass.{u_1} α) Nat.instPreorder
      (@PartialOrder.toPreorder.{u_1} (GenLimit.Generic.LanguageClass.{u_1} α)
        (@CompleteSemilatticeInf.toPartialOrder.{u_1} (GenLimit.Generic.LanguageClass.{u_1} α)
          (@CompleteLattice.toCompleteSemilatticeInf.{u_1} (GenLimit.Generic.LanguageClass.{u_1} α)
            (@CompleteBooleanAlgebra.toCompleteLattice.{u_1} (GenLimit.Generic.LanguageClass.{u_1} α)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{u_1} (GenLimit.Generic.LanguageClass.{u_1} α)
                (@Set.instCompleteAtomicBooleanAlgebra.{u_1} (GenLimit.Generic.Language.{u_1} α)))))))
      classes)
    (@Eq.{u_1 + 1} (GenLimit.Generic.LanguageClass.{u_1} α) H (⋃ n, classes n))
```

### `GenLimit.Generic.IsNonuniformGenerator`

Source: `GenLimit.Core.ClassGeneration:37`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.Generator.{u_1} α → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} gen H =>
  ∀ (L : GenLimit.Generic.Language.{u_1} α),
    @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
        (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) H L →
      ∃ d,
        ∀ (stream : GenLimit.Generic.Stream.{u_1} α),
          @GenLimit.Generic.StreamIn.{u_1} α stream L →
            ∀ (t : Nat),
              @Eq.{1} Nat (@Finset.card.{u_1} α (@GenLimit.Generic.sample.{u_1} α stream t)) d →
                ∀ (s : Nat), @LE.le.{0} Nat instLENat t s → @GenLimit.Generic.CorrectAt.{u_1} α gen L stream s
```

### `GenLimit.Generic.IsUniformGeneratorAt`

Source: `GenLimit.Core.ClassGeneration:26`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.Generator.{u_1} α → GenLimit.Generic.LanguageClass.{u_1} α → Nat → Prop
```

Definition value:
```lean
fun {α} gen H d =>
  ∀ (L : GenLimit.Generic.Language.{u_1} α),
    @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
        (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) H L →
      ∀ (stream : GenLimit.Generic.Stream.{u_1} α),
        @GenLimit.Generic.StreamIn.{u_1} α stream L →
          ∀ (t : Nat),
            @Eq.{1} Nat (@Finset.card.{u_1} α (@GenLimit.Generic.sample.{u_1} α stream t)) d →
              ∀ (s : Nat), @LE.le.{0} Nat instLENat t s → @GenLimit.Generic.CorrectAt.{u_1} α gen L stream s
```

### `GenLimit.Generic.Language`

Source: `GenLimit.Core.GenericGeneration:21`; universe parameters: `u_1`.

Type:
```lean
Type u_1 → Type u_1
```

Definition value:
```lean
fun α => Set.{u_1} α
```

### `GenLimit.Generic.LanguageClass`

Source: `GenLimit.Core.GenericGeneration:24`; universe parameters: `u_1`.

Type:
```lean
Type u_1 → Type u_1
```

Definition value:
```lean
fun α => Set.{u_1} (GenLimit.Generic.Language.{u_1} α)
```

### `GenLimit.Generic.NonuniformlyGeneratable`

Source: `GenLimit.Core.ClassGeneration:44`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} H => ∃ gen, @GenLimit.Generic.IsNonuniformGenerator.{u_1} α gen H
```

### `GenLimit.Generic.Presents`

Source: `GenLimit.Core.GenericGeneration:50`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.Stream.{u_1} α → GenLimit.Generic.Language.{u_1} α → Prop
```

Definition value:
```lean
fun {α} stream L => @Eq.{u_1 + 1} (Set.{u_1} α) (@Set.range.{u_1, 1} α Nat stream) L
```

### `GenLimit.Generic.Stream`

Source: `GenLimit.Core.GenericGeneration:31`; universe parameters: `u_1`.

Type:
```lean
Type u_1 → Type u_1
```

Definition value:
```lean
fun α => Nat → α
```

### `GenLimit.Generic.StreamIn`

Source: `GenLimit.Core.GenericGeneration:54`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.Stream.{u_1} α → GenLimit.Generic.Language.{u_1} α → Prop
```

Definition value:
```lean
fun {α} stream L =>
  @HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) (@Set.range.{u_1, 1} α Nat stream) L
```

### `GenLimit.Generic.UniformlyGeneratable`

Source: `GenLimit.Core.ClassGeneration:33`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} H => ∃ gen d, @GenLimit.Generic.IsUniformGeneratorAt.{u_1} α gen H d
```

### `GenLimit.Generic.commonCore`

Source: `GenLimit.Core.VersionSpace:20`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → Finset.{u_1} α → GenLimit.Generic.Language.{u_1} α
```

Definition value:
```lean
fun {α} H S =>
  @setOf.{u_1} α fun x =>
    ∀ (L : GenLimit.Generic.Language.{u_1} α),
      @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (Set.{u_1} (GenLimit.Generic.Language.{u_1} α))
          (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) (@GenLimit.Generic.versionSpace.{u_1} α H S)
          L →
        @Membership.mem.{u_1, u_1} α (GenLimit.Generic.Language.{u_1} α) (@Set.instMembership.{u_1} α) L x
```

### `GenLimit.Generic.output`

Source: `GenLimit.Core.GenericGeneration:87`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.Generator.{u_1} α → GenLimit.Generic.Stream.{u_1} α → Nat → α
```

Definition value:
```lean
fun {α} G stream t => G t fun i => stream (@Fin.val t i)
```

### `GenLimit.Generic.sample`

Source: `GenLimit.Core.GenericGeneration:63`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.Stream.{u_1} α → Nat → Finset.{u_1} α
```

Definition value:
```lean
fun {α} stream t =>
  @Finset.image.{0, u_1} Nat α (fun a b => Classical.propDecidable (@Eq.{u_1 + 1} α a b)) stream (Finset.range t)
```

### `GenLimit.Generic.sequenceSample`

Source: `GenLimit.Core.GenericGeneration:58`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → {t : Nat} → (Fin t → α) → Finset.{u_1} α
```

Definition value:
```lean
fun {α} {t} xs =>
  @Finset.image.{0, u_1} (Fin t) α (fun a b => Classical.propDecidable (@Eq.{u_1 + 1} α a b)) xs
    (@Finset.univ.{0} (Fin t) (Fin.fintype t))
```

### `GenLimit.Generic.versionSpace`

Source: `GenLimit.Core.VersionSpace:16`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → Finset.{u_1} α → Set.{u_1} (GenLimit.Generic.Language.{u_1} α)
```

Definition value:
```lean
fun {α} H S =>
  @setOf.{u_1} (GenLimit.Generic.Language.{u_1} α) fun L =>
    And
      (@Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
        (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) H L)
      (@HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) (@Finset.toSet.{u_1} α S) L)
```

### `GenLimit.LiRamanTewari.GeneratableInLimit`

Source: `GenLimit.Paper02_LearningTheory.Definitions:34`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} H => @GenLimit.Generic.GeneratableInLimit.{u_1} α H
```

### `GenLimit.LiRamanTewari.NonuniformlyGeneratable`

Source: `GenLimit.Paper02_LearningTheory.Definitions:47`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} H => @GenLimit.Generic.NonuniformlyGeneratable.{u_1} α H
```

### `GenLimit.LiRamanTewari.UniformlyGeneratable`

Source: `GenLimit.Paper02_LearningTheory.Definitions:41`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} H => @GenLimit.Generic.UniformlyGeneratable.{u_1} α H
```

### `GenLimit.MetricSpaces.CoveringNumberAtLeast`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:121`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Real → Set.{u_1} α → Nat → Prop
```

Definition value:
```lean
fun {α} ρ r A d =>
  ∀ (centers : Finset.{u_1} α),
    @HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) A
        (@GenLimit.MetricSpaces.closedNeighborhood.{u_1} α ρ (@Finset.toSet.{u_1} α centers) r) →
      @LE.le.{0} Nat instLENat d (@Finset.card.{u_1} α centers)
```

### `GenLimit.MetricSpaces.CoveringNumberEq`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:129`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Real → Set.{u_1} α → Nat → Prop
```

Definition value:
```lean
fun {α} ρ r A d =>
  And (@GenLimit.MetricSpaces.CoveringNumberAtLeast.{u_1} α ρ r A d)
    (∃ centers,
      And (@Eq.{1} Nat (@Finset.card.{u_1} α centers) d)
        (@HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) A
          (@GenLimit.MetricSpaces.closedNeighborhood.{u_1} α ρ (@Finset.toSet.{u_1} α centers) r)))
```

### `GenLimit.MetricSpaces.Distance`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:33`; universe parameters: `u_1`.

Type:
```lean
Type u_1 → Type u_1
```

Definition value:
```lean
fun α => α → α → Real
```

### `GenLimit.MetricSpaces.DistanceDominatedBy`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.LipschitzTransfer:15`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → GenLimit.MetricSpaces.Distance.{u_1} α → Real → Prop
```

Definition value:
```lean
fun {α} ρ₂ ρ₁ M =>
  ∀ (x y : α),
    @LE.le.{0} Real Real.instLE (ρ₂ x y)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) M (ρ₁ x y))
```

### `GenLimit.MetricSpaces.GeneratableInLimitAt`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:260`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Real → Real → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} ρ ε ε' H => ∃ gen, @GenLimit.MetricSpaces.IsLimitGeneratorAt.{u_1} α ρ ε ε' gen H
```

### `GenLimit.MetricSpaces.HasFiniteInternalCover`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:98`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Real → Set.{u_1} α → Prop
```

Definition value:
```lean
fun {α} ρ r A =>
  ∃ centers,
    And (@HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) (@Finset.toSet.{u_1} α centers) A)
      (@HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) A
        (@GenLimit.MetricSpaces.closedNeighborhood.{u_1} α ρ (@Finset.toSet.{u_1} α centers) r))
```

### `GenLimit.MetricSpaces.HasFiniteScaleClosureDimension`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:192`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Real → Real → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} ρ ε ε' H =>
  ∃ D,
    ∀ (d : Nat),
      @LT.lt.{0} Nat instLTNat D d → Not (∃ S, @GenLimit.MetricSpaces.IsScaleClosureWitness.{u_1} α ρ ε ε' H S d)
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.HilbertAxisReservoir:37`; universe parameters: `(none)`.

Type:
```lean
@AddSubgroup.{0} (@PreLp.{0, 0} Nat (fun x => Real) fun i => Real.normedAddCommGroup)
  (@AddCommGroup.toAddGroup.{0} (@PreLp.{0, 0} Nat (fun x => Real) fun i => Real.normedAddCommGroup)
    (@instAddCommGroupPreLp.{0, 0} Nat (fun x => Real) fun i => Real.normedAddCommGroup))
```

Definition value:
```lean
@lp.{0, 0} Nat (fun x => Real) (fun i => Real.normedAddCommGroup)
  (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
    (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
      (@AddMonoidWithOne.toNatCast.{0} ENNReal
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
      GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.IsExample48CausalCandidate`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Example48Positive:418`; universe parameters: `(none)`.

Type:
```lean
Real →
  Real →
    Real →
      {t : Nat} →
        (Fin t → ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) →
          ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2 → Prop
```

Definition value:
```lean
fun ε ε' γ' {t} xs y =>
  ∃ k,
    And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
      (And
        (∃ i,
          @Eq.{1} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) (xs i)
            (GenLimit.MetricSpaces.HilbertAxisReservoir.example48A ε
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
        (∃ n,
          And
            (@Eq.{1} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) y
              (GenLimit.MetricSpaces.HilbertAxisReservoir.example48G ε'
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (y ∉
              @GenLimit.MetricSpaces.closedNeighborhood.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                GenLimit.MetricSpaces.HilbertAxisReservoir.hilbertDistance
                (@Finset.toSet.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
                  (@GenLimit.Generic.sequenceSample.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) t xs))
                γ')))
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.axisPoint`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.HilbertAxisReservoir:40`; universe parameters: `(none)`.

Type:
```lean
Real → Nat → ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun c k =>
  @lp.single.{0, 0} Nat (fun x => Real) (fun i => Real.normedAddCommGroup) instDecidableEqNat
    (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
        GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
    k c
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.example48A`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.HilbertAxisReservoir:143`; universe parameters: `(none)`.

Type:
```lean
Real → Nat → ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun ε k => GenLimit.MetricSpaces.HilbertAxisReservoir.axisPoint ε k
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.example48CausalGenerator`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Example48Positive:433`; universe parameters: `(none)`.

Type:
```lean
Real → Real → Real → GenLimit.Generic.Generator.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun ε ε' γ' x xs =>
  @dite.{1} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
    (∃ y, @GenLimit.MetricSpaces.HilbertAxisReservoir.IsExample48CausalCandidate ε ε' γ' x xs y)
    (Classical.propDecidable
      (∃ y, @GenLimit.MetricSpaces.HilbertAxisReservoir.IsExample48CausalCandidate ε ε' γ' x xs y))
    (fun h =>
      @Classical.choose.{1} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
        (@GenLimit.MetricSpaces.HilbertAxisReservoir.IsExample48CausalCandidate ε ε' γ' x xs) h)
    fun h => GenLimit.MetricSpaces.HilbertAxisReservoir.example48Zero
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.example48Disturbing`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Example48Positive:32`; universe parameters: `(none)`.

Type:
```lean
Real → Set.{0} Nat → Set.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun ε' I =>
  @setOf.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2 fun x =>
    ∃ k,
      And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) I k)
        (@Eq.{1} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) x
          (GenLimit.MetricSpaces.HilbertAxisReservoir.example48G ε'
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.example48G`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.HilbertAxisReservoir:147`; universe parameters: `(none)`.

Type:
```lean
Real → Nat → ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun ε' k => GenLimit.MetricSpaces.HilbertAxisReservoir.axisPoint ε' k
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.example48Language`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Example48Positive:36`; universe parameters: `(none)`.

Type:
```lean
Real →
  Real → Real → Set.{0} Nat → Set.{0} Nat → Set.{0} Nat → Set.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun r ε ε' I₁ I₂ I₃ =>
  @Union.union.{0} (Set.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
    (@Set.instUnion.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
    (@Singleton.singleton.{0, 0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
      (Set.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
      (@Set.instSingletonSet.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
      GenLimit.MetricSpaces.HilbertAxisReservoir.example48Zero)
    (@Union.union.{0} (Set.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
      (@Set.instUnion.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
      (GenLimit.MetricSpaces.HilbertAxisReservoir.example48USet r I₁)
      (@Union.union.{0} (Set.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
        (@Set.instUnion.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
        (GenLimit.MetricSpaces.HilbertAxisReservoir.example48Optimal ε ε' I₂)
        (GenLimit.MetricSpaces.HilbertAxisReservoir.example48Disturbing ε' I₃)))
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.example48LanguageClass`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Example48Positive:46`; universe parameters: `(none)`.

Type:
```lean
Real → Real → Real → GenLimit.Generic.LanguageClass.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun r ε ε' =>
  @setOf.{0} (GenLimit.Generic.Language.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) fun L =>
    ∃ I₁ I₂ I₃,
      And (@Set.Infinite.{0} Nat I₁)
        (And (@Set.Infinite.{0} Nat I₂)
          (And (@Set.Infinite.{0} Nat I₃)
            (And
              (∀ (k : Nat),
                @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) I₁ k →
                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (And
                (∀ (k : Nat),
                  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) I₂ k →
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (And
                  (∀ (k : Nat),
                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) I₃ k →
                      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@Eq.{1} (GenLimit.Generic.Language.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) L
                    (GenLimit.MetricSpaces.HilbertAxisReservoir.example48Language r ε ε' I₁ I₂ I₃)))))))
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.example48Optimal`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.HilbertAxisReservoir:152`; universe parameters: `(none)`.

Type:
```lean
Real → Real → Set.{0} Nat → Set.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun ε ε' I =>
  @Union.union.{0} (Set.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
    (@Set.instUnion.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
    (@setOf.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2 fun x =>
      ∃ k,
        And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) I k)
          (@Eq.{1} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) x
            (GenLimit.MetricSpaces.HilbertAxisReservoir.example48A ε
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))))
    (@setOf.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2 fun x =>
      ∃ k,
        And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) I k)
          (∃ n,
            @Eq.{1} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) x
              (GenLimit.MetricSpaces.HilbertAxisReservoir.example48G ε'
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k n))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.example48U`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.HilbertAxisReservoir:139`; universe parameters: `(none)`.

Type:
```lean
Real → Nat → ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun r k =>
  GenLimit.MetricSpaces.HilbertAxisReservoir.axisPoint
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
          GenLimit.MetricSpaces.HilbertAxisReservoir.example48U._proof_1))
      r)
    k
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.example48USet`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Example48Positive:28`; universe parameters: `(none)`.

Type:
```lean
Real → Set.{0} Nat → Set.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun r I =>
  @setOf.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2 fun x =>
    ∃ k,
      And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) I k)
        (@Eq.{1} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2) x
          (GenLimit.MetricSpaces.HilbertAxisReservoir.example48U r k))
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.example48Zero`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Example48Positive:24`; universe parameters: `(none)`.

Type:
```lean
↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
GenLimit.MetricSpaces.HilbertAxisReservoir.axisPoint
  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```

### `GenLimit.MetricSpaces.HilbertAxisReservoir.hilbertDistance`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.HilbertAxisReservoir:44`; universe parameters: `(none)`.

Type:
```lean
GenLimit.MetricSpaces.Distance.{0} ↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2
```

Definition value:
```lean
fun x y =>
  @Dist.dist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
    (@PseudoMetricSpace.toDist.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} (↥GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2)
          (@lp.normedAddCommGroup.{0, 0} Nat (fun x => Real)
            (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
                GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1))
            (fun i => Real.normedAddCommGroup) fact_one_le_two_ennreal))))
    x y
```

### `GenLimit.MetricSpaces.InClosedNeighborhood`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:39`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Set.{u_1} α → Real → α → Prop
```

Definition value:
```lean
fun {α} ρ A r y =>
  ∀ (η : Real),
    @LT.lt.{0} Real Real.instLT r η →
      ∃ x,
        And (@Membership.mem.{u_1, u_1} α (Set.{u_1} α) (@Set.instMembership.{u_1} α) A x)
          (@LT.lt.{0} Real Real.instLT (ρ x y) η)
```

### `GenLimit.MetricSpaces.IsDoublingDistance`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.DoublingUUS:29`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Prop
```

Definition value:
```lean
fun {α} ρ =>
  ∃ M,
    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) M)
      (∀ (x : α) (r : Real),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r →
          ∃ centers,
            And (@LE.le.{0} Nat instLENat (@Finset.card.{u_1} α centers) M)
              (∀ (y : α),
                @LE.le.{0} Real Real.instLE (ρ x y) r →
                  ∃ z,
                    And (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α) (@Finset.instMembership.{u_1} α) centers z)
                      (@LE.le.{0} Real Real.instLE (ρ z y)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) r
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              GenLimit.MetricSpaces.IsDoublingDistance._proof_1))))))
```

### `GenLimit.MetricSpaces.IsLimitGeneratorAt`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:249`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} →
  GenLimit.MetricSpaces.Distance.{u_1} α →
    Real → Real → GenLimit.Generic.Generator.{u_1} α → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} ρ ε ε' gen H =>
  ∀ (L : GenLimit.Generic.Language.{u_1} α),
    @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
        (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) H L →
      ∀ (stream : GenLimit.Generic.Stream.{u_1} α),
        @GenLimit.MetricSpaces.MetricPresentation.{u_1} α ρ ε stream L →
          ∃ T,
            ∀ (t : Nat),
              @LE.le.{0} Nat instLENat T t → @GenLimit.MetricSpaces.MetricCorrectAt.{u_1} α ρ ε' gen L stream t
```

### `GenLimit.MetricSpaces.IsNondecreasingMetricCover`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.NonuniformCharacterization:20`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → (Nat → GenLimit.Generic.LanguageClass.{u_1} α) → Prop
```

Definition value:
```lean
fun {α} H classes => @GenLimit.Generic.IsNondecreasingCover.{u_1} α H classes
```

### `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:294`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} →
  GenLimit.MetricSpaces.Distance.{u_1} α →
    Real → Real → GenLimit.Generic.Generator.{u_1} α → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} ρ ε ε' gen H =>
  ∀ (L : GenLimit.Generic.Language.{u_1} α),
    @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
        (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) H L →
      ∃ d,
        ∀ (stream : GenLimit.Generic.Stream.{u_1} α),
          @GenLimit.Generic.StreamIn.{u_1} α stream L →
            ∀ (t : Nat),
              @GenLimit.MetricSpaces.CoveringNumberAtLeast.{u_1} α ρ ε
                  (@Finset.toSet.{u_1} α (@GenLimit.Generic.sample.{u_1} α stream t)) d →
                ∀ (s : Nat),
                  @LE.le.{0} Nat instLENat t s → @GenLimit.MetricSpaces.MetricCorrectAt.{u_1} α ρ ε' gen L stream s
```

### `GenLimit.MetricSpaces.IsScaleClosureWitness`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:182`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} →
  GenLimit.MetricSpaces.Distance.{u_1} α →
    Real → Real → GenLimit.Generic.LanguageClass.{u_1} α → Finset.{u_1} α → Nat → Prop
```

Definition value:
```lean
fun {α} ρ ε ε' H S d =>
  And (@Set.Nonempty.{u_1} (GenLimit.Generic.Language.{u_1} α) (@GenLimit.MetricSpaces.versionSpace.{u_1} α H S))
    (And (@GenLimit.MetricSpaces.CoveringNumberEq.{u_1} α ρ ε (@Finset.toSet.{u_1} α S) d)
      (@GenLimit.MetricSpaces.HasFiniteInternalCover.{u_1} α ρ ε' (@GenLimit.MetricSpaces.commonCore.{u_1} α H S)))
```

### `GenLimit.MetricSpaces.IsUniformGeneratorAt`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:272`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} →
  GenLimit.MetricSpaces.Distance.{u_1} α →
    Real → Real → GenLimit.Generic.Generator.{u_1} α → GenLimit.Generic.LanguageClass.{u_1} α → Nat → Prop
```

Definition value:
```lean
fun {α} ρ ε ε' gen H d =>
  ∀ (L : GenLimit.Generic.Language.{u_1} α),
    @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
        (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) H L →
      ∀ (stream : GenLimit.Generic.Stream.{u_1} α),
        @GenLimit.Generic.StreamIn.{u_1} α stream L →
          ∀ (t : Nat),
            @GenLimit.MetricSpaces.CoveringNumberAtLeast.{u_1} α ρ ε
                (@Finset.toSet.{u_1} α (@GenLimit.Generic.sample.{u_1} α stream t)) d →
              ∀ (s : Nat),
                @LE.le.{0} Nat instLENat t s → @GenLimit.MetricSpaces.MetricCorrectAt.{u_1} α ρ ε' gen L stream s
```

### `GenLimit.MetricSpaces.MetricCorrectAt`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:237`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} →
  GenLimit.MetricSpaces.Distance.{u_1} α →
    Real →
      GenLimit.Generic.Generator.{u_1} α →
        GenLimit.Generic.Language.{u_1} α → GenLimit.Generic.Stream.{u_1} α → Nat → Prop
```

Definition value:
```lean
fun {α} ρ ε' gen L stream t =>
  And
    (@Membership.mem.{u_1, u_1} α (GenLimit.Generic.Language.{u_1} α) (@Set.instMembership.{u_1} α) L
      (@GenLimit.Generic.output.{u_1} α gen stream t))
    (@GenLimit.Generic.output.{u_1} α gen stream t ∉
      @GenLimit.MetricSpaces.closedNeighborhood.{u_1} α ρ
        (@Finset.toSet.{u_1} α (@GenLimit.Generic.sample.{u_1} α stream t)) ε')
```

### `GenLimit.MetricSpaces.MetricPresentation`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:201`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} →
  GenLimit.MetricSpaces.Distance.{u_1} α →
    Real → GenLimit.Generic.Stream.{u_1} α → GenLimit.Generic.Language.{u_1} α → Prop
```

Definition value:
```lean
fun {α} ρ ε stream L =>
  And (@GenLimit.Generic.StreamIn.{u_1} α stream L)
    (@HasSubset.Subset.{u_1} (GenLimit.Generic.Language.{u_1} α) (@Set.instHasSubset.{u_1} α) L
      (@GenLimit.MetricSpaces.closedNeighborhood.{u_1} α ρ (@Set.range.{u_1, 1} α Nat stream) ε))
```

### `GenLimit.MetricSpaces.MutuallyLipschitzDominated`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.BiLipschitzTransfer:18`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → GenLimit.MetricSpaces.Distance.{u_1} α → Real → Real → Prop
```

Definition value:
```lean
fun {α} ρ₁ ρ₂ M₁₂ M₂₁ =>
  And (@GenLimit.MetricSpaces.DistanceDominatedBy.{u_1} α ρ₂ ρ₁ M₁₂)
    (@GenLimit.MetricSpaces.DistanceDominatedBy.{u_1} α ρ₁ ρ₂ M₂₁)
```

### `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:309`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Real → Real → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} ρ ε ε' H => ∃ gen, @GenLimit.MetricSpaces.IsNonuniformGeneratorAt.{u_1} α ρ ε ε' gen H
```

### `GenLimit.MetricSpaces.RealLineThreshold.languageClass`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.RealLineThreshold:56`; universe parameters: `(none)`.

Type:
```lean
GenLimit.Generic.LanguageClass.{0} Real
```

Definition value:
```lean
@setOf.{0} (GenLimit.Generic.Language.{0} Real) fun L =>
  ∃ p,
    And (Nat.Prime p)
      (And (@Odd.{0} Nat Nat.instSemiring p)
        (∃ B,
          And
            (@HasSubset.Subset.{0} (Set.{0} Real) (@Set.instHasSubset.{0} Real) B
              GenLimit.MetricSpaces.RealLineThreshold.positiveEvenIntegers)
            (@Eq.{1} (GenLimit.Generic.Language.{0} Real) L
              (@Union.union.{0} (Set.{0} Real) (@Set.instUnion.{0} Real)
                (GenLimit.MetricSpaces.RealLineThreshold.primePairSupport p) B))))
```

### `GenLimit.MetricSpaces.RealLineThreshold.positiveEvenIntegers`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.RealLineThreshold:52`; universe parameters: `(none)`.

Type:
```lean
Set.{0} Real
```

Definition value:
```lean
@setOf.{0} Real fun x =>
  ∃ n,
    @Eq.{1} Real x
      (@Nat.cast.{0} Real Real.instNatCast
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### `GenLimit.MetricSpaces.RealLineThreshold.primePairSupport`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.RealLineThreshold:46`; universe parameters: `(none)`.

Type:
```lean
Nat → Set.{0} Real
```

Definition value:
```lean
fun p =>
  @setOf.{0} Real fun x =>
    ∃ n,
      Or
        (@Eq.{1} Real x
          (@Nat.cast.{0} Real Real.instNatCast
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) p
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@Eq.{1} Real x
          (@Nat.cast.{0} Real Real.instNatCast
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) p
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### `GenLimit.MetricSpaces.RealLineThreshold.realDistance`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.RealLineThreshold:42`; universe parameters: `(none)`.

Type:
```lean
Real → Real → Real
```

Definition value:
```lean
fun x y =>
  @abs.{0} Real Real.lattice Real.instAddGroup
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) x y)
```

### `GenLimit.MetricSpaces.UniformlyGeneratableAt`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:286`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Real → Real → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} ρ ε ε' H => ∃ gen d, @GenLimit.MetricSpaces.IsUniformGeneratorAt.{u_1} α ρ ε ε' gen H d
```

### `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:212`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Real → GenLimit.Generic.LanguageClass.{u_1} α → Prop
```

Definition value:
```lean
fun {α} ρ r H =>
  ∀ (L : GenLimit.Generic.Language.{u_1} α),
    @Membership.mem.{u_1, u_1} (GenLimit.Generic.Language.{u_1} α) (GenLimit.Generic.LanguageClass.{u_1} α)
        (@Set.instMembership.{u_1} (GenLimit.Generic.Language.{u_1} α)) H L →
      And (@Set.Nonempty.{u_1} α L)
        (∀ (stream : GenLimit.Generic.Stream.{u_1} α),
          @GenLimit.MetricSpaces.MetricPresentation.{u_1} α ρ r stream L →
            ∀ (d : Nat),
              ∃ t,
                @GenLimit.MetricSpaces.CoveringNumberAtLeast.{u_1} α ρ r
                  (@Finset.toSet.{u_1} α (@GenLimit.Generic.sample.{u_1} α stream t)) d)
```

### `GenLimit.MetricSpaces.closedNeighborhood`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:44`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.MetricSpaces.Distance.{u_1} α → Set.{u_1} α → Real → Set.{u_1} α
```

Definition value:
```lean
fun {α} ρ A r => @setOf.{u_1} α fun y => @GenLimit.MetricSpaces.InClosedNeighborhood.{u_1} α ρ A r y
```

### `GenLimit.MetricSpaces.commonCore`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:176`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → Finset.{u_1} α → GenLimit.Generic.Language.{u_1} α
```

Definition value:
```lean
fun {α} H S => @GenLimit.Generic.commonCore.{u_1} α H S
```

### `GenLimit.MetricSpaces.discreteDistance`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.DiscreteReduction:21`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → [DecidableEq.{u_1 + 1} α] → GenLimit.MetricSpaces.Distance.{u_1} α
```

Definition value:
```lean
fun {α} [inst : DecidableEq.{u_1 + 1} α] x y =>
  @ite.{1} Real (@Eq.{u_1 + 1} α x y) (inst x y)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

### `GenLimit.MetricSpaces.versionSpace`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.Definitions:170`; universe parameters: `u_1`.

Type:
```lean
{α : Type u_1} → GenLimit.Generic.LanguageClass.{u_1} α → Finset.{u_1} α → Set.{u_1} (GenLimit.Generic.Language.{u_1} α)
```

Definition value:
```lean
fun {α} H S => @GenLimit.Generic.versionSpace.{u_1} α H S
```

### Helper interface `GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2._proof_1`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.HilbertAxisReservoir:None`.

```lean
(@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).AtLeastTwo
```

No proof value inspected.

### Helper interface `GenLimit.MetricSpaces.HilbertAxisReservoir.example48U._proof_1`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.HilbertAxisReservoir:None`.

```lean
(@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).AtLeastTwo
```

No proof value inspected.

### Helper interface `GenLimit.MetricSpaces.IsDoublingDistance._proof_1`

Source: `GenLimit.Paper21_GenerationInMetricSpaces.DoublingUUS:None`.

```lean
(@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).AtLeastTwo
```

No proof value inspected.

## Scope limits

No decisive missing native definition remains. Standard Lean/Mathlib constants (`lp`, `lp.single`, `MetricSpace`, normed-space instances, set/cardinality operations, and classical choice) are trusted at the declared external boundary. This report certifies only that the supplied types and definition values have been reconstructed. It does not certify theorem validity, proof dependencies, absence of axioms or unsoundness, the original source snapshot, algorithm computability, proof-body correctness, correspondence with any paper statement, current compilability, or human approval. No later stage was run.
