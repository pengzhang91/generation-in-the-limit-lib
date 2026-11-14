# P00A supplemental Stage 1 reconstruction

The sole supplemental target, `GenLimit.Angluin.TheoremTwoStatement`, is a **definition of type `Prop`**. It defines an existential separation proposition. It is **not a theorem proving that proposition**, and the supplied declaration provides no witness family and no proof of its existence.

This report continues the earlier paper-withheld Lean-only worker context. The original Stage 1 outputs remain unchanged. The supplemental locator map assigns C01 to this definition; that supplies a target locator only, without a source interpretation. It does not retroactively change the original frozen C01 no-endpoint record. No source paper, Stage 2 finding/report, owner material, registry, PaperMap, developer explanation, other audit, raw source comment, or proof body was consulted.

## Actual input census and provenance

Seven files in `stage1-supplement-input/` were read. The supplied manifest has six entries, and all six matched freshly computed SHA-256 hashes; the manifest itself was separately hashed. Its 19 recursive records comprise one target and 18 non-target dependencies: 17 definitions, one inductive family type, and one constructor. All 19 records exactly match the corresponding records in the original frozen native census. Eighteen already occur in the original 34-record recursive interface.

The retained earlier Stage 1 context includes the original five target types, 29 non-target dependency records, 39 additional definition bodies, and six supporting theorem types, plus metadata/selective inspection of the 569-record native census. The supplemental target's name/kind was among that census metadata; it was not a target dossier in the original reconstruction. The complete census is supporting evidence, not an individual audit of every helper. This supplemental pass reads the exact target value and reconstructs it individually. No source comparison has entered this worker context.

The original requested configuration was `gpt-6.1-sol` with `xhigh` reasoning and a fresh Stage 1 worker context. This supplemental request **continues** that context and is not claimed to be fresh or blind. Actual backend model/revision, applied reasoning configuration, and backend context-reset attestation are unobservable.

| Supplemental input actually read | Bytes | SHA-256 |
|---|---:|---|
| `PROMPT.md` | 1212 | `fe5ce01116fe2210fe060f472422dca8e6b205802c47016a746930697a0b6dce` |
| `target-statements.md` | 504 | `ac5fbd70454fd3b9d3f3237ecc3e76f8d33529d549b41dc984dc84a8a9db724e` |
| `definition-dependencies.md` | 6602 | `8e4fca4526fcc65d4d8e77b60b27f655d79abc5af6490f0f00d84a41de643a92` |
| `declarations.jsonl` | 11250 | `afa5d3f2c1b25a6d398899322b6d772f7abe5ad2c68a4196e4494ea4cf6fd2cd` |
| `targets-by-slot.json` | 62 | `5ff7cffa86df39f30afa102aa129424fca3e1991b46580f16b8c5c0d3aeae620` |
| `targets.txt` | 37 | `57d1daff6b0ff6385e70829439b7275d7ec416d778f0e28137adcec3fd16621a` |
| `SHA256SUMS` | 506 | `25ebf1533e346e268f750d527e00914f5406c64ccbbe2ff7e054cb90263a6d8d` |

The following original Stage 1 files were read again solely for frozen-record comparison and the declared external boundary:

| Original Stage 1 input | Bytes | SHA-256 |
|---|---:|---|
| `declarations.jsonl` | 21802 | `8a7b0e04a23bcf1d0ac6bb8dfb09fb5cfcf34cd374ee0ed31bdff3cee833cdf3` |
| `native-declaration-census.jsonl` | 532427 | `0c8270eac1c5e679a1e1c3678d88a8c732f822d3a83184ea481ca0ee12987fb0` |
| `external-boundary.txt` | 515 | `e3cbb360dda98b3e1c2b438d46955f2b6a63be9e0985c738a2707396400f7cdb` |

Original result files were read at the byte/hash level to verify preservation. Their contents were not used as new source-comparison evidence; the mathematical Stage 1 report is already in this worker's retained Lean-only context. Their frozen hashes are recorded in the run JSON.

## Exact target dossier

### `GenLimit.Angluin.TheoremTwoStatement`

Kind: definition. Source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:92`.

Exact type:

```lean
Prop
```

Definition value:

```lean
∃ F, And (@GenLimit.Angluin.ConditionTwo.{0} Nat F.language) (Not (GenLimit.Angluin.EffectiveInferrable F))
```

The target has no outer hypothesis or parameter. Its type `Prop` is the universe of propositions; the definition value is the proposition being named. A proof of the named proposition would have type `GenLimit.Angluin.TheoremTwoStatement`. This declaration instead has type `Prop`, so it does not inhabit the existential proposition it defines. No truth, existence, or construction certification follows from registering this definition.

Let `L_i=F.language i` and `prefix(s,t)=List.map s (List.range t)`. Expanding every relevant definition yields:

```text
∃ F : EffectiveIndexedFamily,
  (∀ i : Nat, ∃ T_i : Finset Nat,
    (T_i:Set Nat)⊆L_i ∧
    ∀ j : Nat, (T_i:Set Nat)⊆L_j → L_j⊆L_i → L_i⊆L_j)
  ∧
  ¬(∃ M : List Nat → Nat,
    Computable M ∧
    ∀ z : Nat, ∀ s : Nat → Nat,
      Set.range s=L_z →
      ∃ k : Nat, L_k=L_z ∧
        ∃ N : Nat, ∀ t : Nat, N≤t → M(prefix(s,t))=k).
```

The existential F is a bundled family with all five constructor components preserved:

```text
language : Nat → Set Nat
membership : Nat → Nat → Bool
∀ i x, membership i x=true ↔ x∈language i
Computable₂ membership
∀ i, (language i).Nonempty
```

Thus the proposition would ask for a family of **nonempty** natural-number languages with one jointly total computable exact membership decision function, not merely an arbitrary or nonuniformly decidable family. No injectivity of indices, infinitude of languages, inclusion decider, learner, emitter, or explicit representation-to-code transformer is included in the package.

The first conjunct is per-index semantic finite tell-tale existence. Each T_i lies in L_i, and any represented language L_j containing T_i and contained in L_i must also contain L_i, hence must equal it. The tell-tale need not exclude incomparable languages or proper superlanguages. It may be empty. T_i is chosen after i and before j; no computable choice of completed tell-tales and no uniform effective enumeration is asserted. The family F is chosen before both conjuncts; neither a concrete F nor its membership program is named in this definition value.

The second conjunct negates the existence of **one total computable identifier for the whole fixed family**. Such a learner would take an ordered finite list of Nat and output one Nat hypothesis index. It would have to work for all z and all streams presenting L_z. For a particular z and whole stream s, the eventual index k may depend on z,s and can differ from z, provided L_k=L_z. A corresponding threshold N may depend on those witnesses; every time t≥N must produce that very same k. This requires eventual stability of the exact name, rather than only eventual semantic correctness while names continue to change. The prefix has length t and is empty at t=0. No convergence rate, uniform threshold, confidence, scale, numerical constant, or other bound occurs.

A classical logical reformulation of the **negated learner conjunct only** is:

```text
∀ M : List Nat → Nat, Computable M →
  ∃ z : Nat, ∃ s : Nat → Nat,
    Set.range s=L_z ∧
    ∀ k : Nat, L_k=L_z →
      ∀ N : Nat, ∃ t : Nat, N≤t ∧ M(prefix(s,t))≠k.
```

This is a logical reading of failure, not an additional proved declaration or a supplied adversarial-stream construction. A failing (z,s) may depend on M. It does not force a single target or stream to defeat every computable M. It does not necessarily mean infinitely many outputs denote the wrong language: with repeated equivalent indices, never stabilizing on one correct name already violates the identification predicate. A learner that stabilizes on a wrong language also fails it.

The excluded uniform M has to precede all target indices and presentations. The proposition does not exclude a different computable constant learner for each individually fixed target index: the constant function returning z identifies L_z alone. It also does not negate unrestricted semantic inferability or claim that all arbitrary, noncomputable history functions fail. The direct statement is the conjunction of finite tell-tales and failure of the displayed computable family-wide identification property. Any further relation to the earlier semantic equivalence would be an inference from another supplied Lean statement, not a proof that the existential F exists.

## Representation, access, and edge cases

`Language Nat` is `Set Nat`; `LanguageFamily Nat` is `Nat → Set Nat`; `Stream Nat` is `Nat → Nat`. `Presents s L` means exactly `Set.range s=L`. It requires every datum to lie in L and every member of L to occur at least once; it supplies no frequency or ordering bound and does not require s to be computable. Arbitrary repetitions are allowed, and the learner sees those repetitions and the order in its history list. A finite nonempty target is still presented forever; data exhaustion does not terminate the stream. Empty target languages are excluded by the existential family's constructor, so no member's success obligation is made vacuous by emptiness. The type of the family remains Nat-indexed even when many indices denote the same language.

`Learner Info Name` is `List Info → Name`; both identifier aliases specialize this to histories and Nat names. `SemanticallyIdentifies` quantifies over all exact positive presentations, `IdentifiesInLimit` conjoins correct denotation and stabilization, and `StabilizesTo` means equality to one fixed name for every sufficiently large time. These are identification statements, not datum generation, novelty, support-valued loss, distributions, full-support laws, or randomized access.

`Computable M` and `Computable₂ membership` use the displayed standard Nat and List Primcodable encodings. They express ordinary total computability for those functions. The definition has no extra membership-oracle argument for the learner; for any fixed F the bundled membership procedure is itself computable and could be incorporated into a family-specific learner program. No arbitrary noncomputable oracle, uniform program taking F as encoded runtime input, or finite-state update machine is specified. There is no named algorithm body or explicit family-construction rule in this supplemental target, so no state, update, or output rules beyond the learner's history-to-index signature can be reconstructed from it.

## Coverage and limits

| Supplemental slot locator | Exact target | Kind | Result |
|---|---|---|---|
| C01 | `GenLimit.Angluin.TheoremTwoStatement` | definition, type `Prop` | Proposition meaning reconstructed; no proof or existential witness supplied by this declaration. |

All 19 recursive records are reproduced below with exact kinds, types, source locators, and available definition values. They establish the representation and quantifier meanings above; no additional helper audit is claimed. Lean and Mathlib standard meanings, including the displayed computability encodings, set/finset operations, and logical negation/quantification, are trusted under the original external-boundary instruction. No decisive unknown nonstandard constant remained in this reconstruction.

No theorem proving or refuting this proposition was a supplemental target. No source-paper meaning is inferred from its name or selection. No proof body, witness construction, or construction correctness is certified. No fresh compilation, build, source-snapshot recreation, recursive Mathlib audit, human certification, Git change, library edit, or input edit was performed. The original frozen Stage 1 files are preserved, including their original absent-endpoint rows; this supplemental report is separate evidence.

## Exact recursive interface appendix

### `GenLimit.Angluin.AllNonempty`

Kind: definition. Source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:35`.

Exact type:

```lean
{α : Type u_1} → GenLimit.Generic.LanguageFamily.{u_1} α → Prop
```

Definition value:

```lean
fun {α} C => ∀ (i : Nat), @Set.Nonempty.{u_1} α (C i)
```

### `GenLimit.Angluin.ConditionTwo`

Kind: definition. Source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:52`.

Exact type:

```lean
{α : Type u_1} → GenLimit.Generic.LanguageFamily.{u_1} α → Prop
```

Definition value:

```lean
fun {α} C => ∀ (i : Nat), ∃ T, @GenLimit.Angluin.IsTellTale.{u_1} α C i T
```

### `GenLimit.Angluin.EffectiveIdentifier`

Kind: definition. Source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:27`.

Exact type:

```lean
Type
```

Definition value:

```lean
GenLimit.Angluin.SemanticIdentifier.{0} Nat
```

### `GenLimit.Angluin.EffectiveIndexedFamily`

Kind: inductive. Source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:18`.

Exact type:

```lean
Type
```

Constructors: `GenLimit.Angluin.EffectiveIndexedFamily.mk`.

### `GenLimit.Angluin.EffectiveIndexedFamily.language`

Kind: definition. Source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:19`.

Exact type:

```lean
GenLimit.Angluin.EffectiveIndexedFamily → GenLimit.Generic.LanguageFamily.{0} Nat
```

Definition value:

```lean
fun self => self.1
```

### `GenLimit.Angluin.EffectiveIndexedFamily.mk`

Kind: constructor. Source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:18`.

Exact type:

```lean
(language : GenLimit.Generic.LanguageFamily.{0} Nat) →
  (membership : Nat → Nat → Bool) →
    (∀ (i x : Nat),
        Iff (@Eq.{1} Bool (membership i x) Bool.true)
          (@Membership.mem.{0, 0} Nat (GenLimit.Generic.Language.{0} Nat) (@Set.instMembership.{0} Nat) (language i)
            x)) →
      @Computable₂.{0, 0, 0} Nat Nat Bool (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
          (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Primcodable.bool membership →
        @GenLimit.Angluin.AllNonempty.{0} Nat language → GenLimit.Angluin.EffectiveIndexedFamily
```

### `GenLimit.Angluin.EffectiveInferrable`

Kind: definition. Source locator: `GenLimit.Paper00A_PositiveDataInference.Effective.Definitions:33`.

Exact type:

```lean
GenLimit.Angluin.EffectiveIndexedFamily → Prop
```

Definition value:

```lean
fun F =>
  ∃ M,
    And
      (@Computable.{0, 0} (List.{0} Nat) Nat
        (@Primcodable.list.{0} Nat (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat))
        (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) M)
      (@GenLimit.Angluin.SemanticallyIdentifies.{0} Nat M F.language)
```

### `GenLimit.Angluin.IsTellTale`

Kind: definition. Source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:39`.

Exact type:

```lean
{α : Type u_1} → GenLimit.Generic.LanguageFamily.{u_1} α → Nat → Finset.{u_1} α → Prop
```

Definition value:

```lean
fun {α} C i T =>
  And (@HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) (@Finset.toSet.{u_1} α T) (C i))
    (∀ (j : Nat),
      @HasSubset.Subset.{u_1} (Set.{u_1} α) (@Set.instHasSubset.{u_1} α) (@Finset.toSet.{u_1} α T) (C j) →
        @HasSubset.Subset.{u_1} (GenLimit.Generic.Language.{u_1} α) (@Set.instHasSubset.{u_1} α) (C j) (C i) →
          @HasSubset.Subset.{u_1} (GenLimit.Generic.Language.{u_1} α) (@Set.instHasSubset.{u_1} α) (C i) (C j))
```

### `GenLimit.Angluin.SemanticIdentifier`

Kind: definition. Source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:18`.

Exact type:

```lean
Type u_1 → Type (max 0 u_1)
```

Definition value:

```lean
fun α => GenLimit.Learner.{u_1, 0} α Nat
```

### `GenLimit.Angluin.SemanticallyIdentifies`

Kind: definition. Source locator: `GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions:24`.

Exact type:

```lean
{α : Type u_1} → GenLimit.Angluin.SemanticIdentifier.{u_1} α → GenLimit.Generic.LanguageFamily.{u_1} α → Prop
```

Definition value:

```lean
fun {α} M C =>
  ∀ (z : Nat) (stream : GenLimit.Generic.Stream.{u_1} α),
    @GenLimit.Generic.Presents.{u_1} α stream (C z) →
      @GenLimit.IdentifiesInLimit.{u_1, 0, u_1} α Nat (GenLimit.Generic.Language.{u_1} α) C M stream (C z)
```

### `GenLimit.Generic.Language`

Kind: definition. Source locator: `GenLimit.Core.GenericGeneration:21`.

Exact type:

```lean
Type u_1 → Type u_1
```

Definition value:

```lean
fun α => Set.{u_1} α
```

### `GenLimit.Generic.LanguageFamily`

Kind: definition. Source locator: `GenLimit.Core.GenericGeneration:28`.

Exact type:

```lean
Type u_1 → Type u_1
```

Definition value:

```lean
fun α => Nat → GenLimit.Generic.Language.{u_1} α
```

### `GenLimit.Generic.Presents`

Kind: definition. Source locator: `GenLimit.Core.GenericGeneration:50`.

Exact type:

```lean
{α : Type u_1} → GenLimit.Generic.Stream.{u_1} α → GenLimit.Generic.Language.{u_1} α → Prop
```

Definition value:

```lean
fun {α} stream L => @Eq.{u_1 + 1} (Set.{u_1} α) (@Set.range.{u_1, 1} α Nat stream) L
```

### `GenLimit.Generic.Stream`

Kind: definition. Source locator: `GenLimit.Core.GenericGeneration:31`.

Exact type:

```lean
Type u_1 → Type u_1
```

Definition value:

```lean
fun α => Nat → α
```

### `GenLimit.IdentifiesInLimit`

Kind: definition. Source locator: `GenLimit.Core.Identification:53`.

Exact type:

```lean
{Info : Type uInfo} →
  {Name : Type uName} →
    {Object : Type uObject} → (Name → Object) → GenLimit.Learner.{uInfo, uName} Info Name → (Nat → Info) → Object → Prop
```

Definition value:

```lean
fun {Info} {Name} {Object} denote learner stream target =>
  ∃ name,
    And (@Eq.{uObject + 1} Object (denote name) target)
      (@GenLimit.StabilizesTo.{uName} Name (fun t => learner (@GenLimit.textPrefix.{uInfo} Info stream t)) name)
```

### `GenLimit.Learner`

Kind: definition. Source locator: `GenLimit.Core.Identification:18`.

Exact type:

```lean
Type uInfo → Type uName → Type (max uName uInfo)
```

Definition value:

```lean
fun Info Name => List.{uInfo} Info → Name
```

### `GenLimit.StabilizesTo`

Kind: definition. Source locator: `GenLimit.Core.Identification:47`.

Exact type:

```lean
{Name : Type uName} → (Nat → Name) → Name → Prop
```

Definition value:

```lean
fun {Name} guess name => ∃ T, ∀ (t : Nat), @LE.le.{0} Nat instLENat T t → @Eq.{uName + 1} Name (guess t) name
```

### `GenLimit.textPrefix`

Kind: definition. Source locator: `GenLimit.Core.Text:16`.

Exact type:

```lean
{α : Type u_1} → (Nat → α) → Nat → List.{u_1} α
```

Definition value:

```lean
fun {α} stream t => @List.map.{0, u_1} Nat α stream (List.range t)
```

