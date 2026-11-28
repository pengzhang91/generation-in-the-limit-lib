# Check log

Written by `reader.py` from the saved pages; do not edit.

- P00: 19/19 readings checked; 1879/1879 random trees recovered
- P00A: 9/9 readings checked; 884/884 random trees recovered
- P01: 3/3 readings checked; control A rejected by the kernel; 3185/3185 random trees recovered
- P02: 12/12 readings checked; 1180/1180 random trees recovered
- P03: 13/13 readings checked; 1281/1281 random trees recovered
- P04: 5/5 readings checked; 500/500 random trees recovered
- P05: 13/13 readings checked; 1286/1286 random trees recovered
- P06: 4/4 readings checked; 391/391 random trees recovered
- P07: 16/16 readings checked; 1591/1591 random trees recovered
- P08: 2/2 readings checked; 197/197 random trees recovered
- P09: 3/3 readings checked; 296/296 random trees recovered
- P10: 10/10 readings checked; 983/983 random trees recovered
- P11: 23/23 readings checked; 2266/2266 random trees recovered
- P12: 8/8 readings checked; 788/788 random trees recovered
- P13: 7/7 readings checked; 698/698 random trees recovered
- P14: 5/5 readings checked; 497/497 random trees recovered
- P15: 9/9 readings checked; 887/887 random trees recovered
- P16: 4/4 readings checked; 398/398 random trees recovered
- P17: 22/22 readings checked; 2186/2186 random trees recovered
- P18: 7/7 readings checked; 692/692 random trees recovered
- P19: 4/4 readings checked; 400/400 random trees recovered
- P20: 10/10 readings checked; 994/994 random trees recovered
- P21: 19/20 readings checked; 1 without a reading; 1890/1890 random trees recovered
- P22: 6/6 readings checked; 588/588 random trees recovered
- P23: 13/13 readings checked; 1298/1298 random trees recovered
- P24: 6/6 readings checked; 598/598 random trees recovered
- P25: 6/6 readings checked; 598/598 random trees recovered
- P26: 4/4 readings checked; 396/396 random trees recovered
- P27: 9/9 readings checked; 892/892 random trees recovered
- P28: 15/15 readings checked; 1475/1475 random trees recovered
- P29: 4/4 readings checked; 400/400 random trees recovered
- P30: 4/4 readings checked; 399/399 random trees recovered
- P31: 13/13 readings checked; 1287/1287 random trees recovered
- P32: 11/11 readings checked; 1094/1094 random trees recovered
- P39: 2/2 readings checked; 196/196 random trees recovered

## P00

SHA-256 of the checked page: `75368312caad9bac76d174ce13f70dd50c284eee9b767522978dd15c812e2dc4`

### Theorem 7.1 · `GenLimit.Gold.Results.theorem_7_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( I O N : Type _ ) , ∀ [ Countable I ] , ∀ [ Countable O ] , ∀ [ Nonempty O ] , ∀ ( naming : ( GenLimit.Gold.Abstract.Naming N O ) ) , ∀ ( allowed : ( GenLimit.Gold.Abstract.Allowable I O ) ) , ( ∀ ( _ : ( GenLimit.Gold.Abstract.Identifiable naming allowed ) ) , ( GenLimit.Gold.Abstract.Distinguishable allowed ) ) ∧ ( ( ∀ ( _ : ( GenLimit.Gold.Abstract.CollapsingUncertainty allowed ) ) , ∀ ( e : ( ℕ → O ) ) , ∀ ( _ : ( Function.Surjective e ) ) , ( GenLimit.Gold.Abstract.Identifies naming allowed ( GenLimit.Gold.Abstract.identificationByEnumeration naming allowed e ) ) ) ∧ ( ∀ ( _ : ( ∀ o : O , ( Set.Countable ( allowed o ) ) ) ) , ∀ ( _ : ( GenLimit.Gold.Abstract.Distinguishable allowed ) ) , ( GenLimit.Gold.Abstract.Identifiable naming allowed ) ) )
```

### Section 8 named informants · `GenLimit.Gold.Results.section_8_named_informants`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( N : Type _ ) , ∀ [ Nonempty N ] , ∀ ( names : ( GenLimit.Gold.Effective.NameRelation N ) ) , ∀ ( C : ( Set GenLimit.Language ) ) , ∀ ( _ : ( Set.Countable C ) ) , ∀ ( _ : ( ∀ L ∈ C , ( ∃ n : N , ( names n L ) ) ) ) , ( ∃ M : ( ( List GenLimit.Gold.Informant.InformantDatum ) → N ) , ( GenLimit.Gold.Effective.Learns M names GenLimit.Gold.Effective.arbitraryInformant C ) )
```

### Complete informant enumeration · `GenLimit.Gold.Results.complete_informant_enumeration`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ( GenLimit.Gold.Informant.IdentifiesFamilyFromInformant C ( GenLimit.Gold.Informant.informantEnumerationLearner C ) )
```

### Section 8 restricted texts · `GenLimit.Gold.Results.section_8_restricted_texts`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( N : Type _ ) , ∀ [ Nonempty N ] , ∀ ( names : ( GenLimit.Gold.Effective.NameRelation N ) ) , ∀ ( C : ( Set GenLimit.Language ) ) , ∀ ( _ : ( Set.Countable C ) ) , ∀ ( _ : ( ∀ L ∈ C , ( ∃ n : N , ( names n L ) ) ) ) , ( ( ∃ M : ( ( List ℕ ) → N ) , ( GenLimit.Gold.Effective.Learns M names GenLimit.Gold.Effective.recursiveText C ) ) ) ∧ ( ( ∃ M : ( ( List ℕ ) → N ) , ( GenLimit.Gold.Effective.Learns M names GenLimit.Gold.Effective.primitiveRecursiveText C ) ) )
```

### Section 8 finite superfinite boundary · `GenLimit.Gold.Results.section_8_finite_superfinite_boundary`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( GenLimit.Gold.Text.SemanticallyIdentifiable GenLimit.Gold.Text.finiteLanguages ) ) ∧ ( ∀ ( «𝒸» : ( Set GenLimit.Language ) ) , ∀ ( _ : ( HasSSubset.SSubset GenLimit.Gold.Text.finiteLanguages «𝒸» ) ) , ( ¬ ( GenLimit.Gold.Text.SemanticallyIdentifiable «𝒸» ) ) )
```

### Positive text enumeration limit · `GenLimit.Gold.Results.positive_text_enumeration_limit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( z : ℕ ) , ∀ ( _ : ( Set.range x = ( C z ) ) ) , ( GenLimit.StabilizesTo ( fun t => ( GenLimit.Gold.Text.enumerationLearner C ( GenLimit.textPrefix x t ) ) ) ( GenLimit.Gold.Text.leastCover C z ) )
```

### Theorem 10.1 learning time · `GenLimit.Gold.Results.theorem_10_1_learning_time`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( N O I : Type _ ) , ∀ ( naming : ( GenLimit.Gold.Abstract.Naming N O ) ) , ∀ ( allowed : ( GenLimit.Gold.Abstract.Allowable I O ) ) , ∀ ( e : ( ℕ → O ) ) , ∀ ( _ : ( Function.Surjective e ) ) , ∀ ( M : ( GenLimit.Learner I N ) ) , let G := ( GenLimit.Gold.Abstract.identificationByEnumeration naming allowed e ) ; ∀ ( _ : ( GenLimit.Gold.Abstract.NoSlower naming allowed M G ) ) , ( GenLimit.Gold.Abstract.NoSlower naming allowed G M )
```

### Theorem 10.1 translation · `GenLimit.Gold.Results.theorem_10_1_translation`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( I A B O : Type _ ) , ∀ [ Primcodable I ] , ∀ [ Primcodable A ] , ∀ [ Primcodable B ] , ∀ ( method : ( GenLimit.Gold.Effective.Presentations I O ) ) , ∀ ( src : ( GenLimit.Gold.Effective.Denotation A O ) ) , ∀ ( dst : ( GenLimit.Gold.Effective.Denotation B O ) ) , ∀ ( C : ( Set O ) ) , ∀ ( _ : ( GenLimit.Gold.Effective.Identifiable src method C ) ) , ∀ ( _ : ( GenLimit.Gold.Effective.LimitTranslation src dst C ) ) , ( GenLimit.Gold.Effective.Identifiable dst method C )
```

### Corollary 10.1 corrected · `GenLimit.Gold.Results.corollary_10_1_corrected`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( Set GenLimit.Language ) ) , ∀ ( _ : ( binrel% HasSubset.Subset GenLimit.Gold.Text.finiteLanguages C ) ) , ∀ L ∈ C , ∀ ( _ : ( Set.Infinite L ) ) , ∀ ( _ : ( L ∈ GenLimit.Gold.Effective.recursiveLanguages ) ) , ( ¬ ( GenLimit.Gold.Effective.LimitTranslation GenLimit.Gold.Effective.Generator GenLimit.Gold.Effective.Tester C ) )
```

### Theorem 10.2 · `GenLimit.Gold.Results.theorem_10_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( Set GenLimit.Language ) ) , ∀ ( _ : ( binrel% HasSubset.Subset GenLimit.Gold.Text.finiteLanguages C ) ) , ∀ L ∈ C , ∀ ( _ : ( Set.Infinite L ) ) , ∀ ( _ : ( L ∈ GenLimit.Gold.Effective.recursiveLanguages ) ) , ( ¬ ( GenLimit.Gold.Effective.TwoRecursiveTranslation GenLimit.Gold.Effective.DomainGenerator GenLimit.Gold.Effective.AntiDomainGenerator C ) )
```

### Theorem I.1 · `GenLimit.Gold.Results.theorem_I_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( I : Type _ ) , ∀ [ Primcodable I ] , ∀ ( m : ( GenLimit.Gold.Effective.Method I ) ) , ∀ ( C : ( Set GenLimit.Language ) ) , ∀ ( _ : ( GenLimit.Gold.Effective.Identifiable GenLimit.Gold.Effective.Tester m C ) ) , ( GenLimit.Gold.Effective.Identifiable GenLimit.Gold.Effective.Generator m C )
```

### Corollary I.2 · `GenLimit.Gold.Results.corollary_I_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( I : Type _ ) , ∀ [ Primcodable I ] , ∀ ( m : ( GenLimit.Gold.Effective.Method I ) ) , ∀ ( C : ( Set GenLimit.Language ) ) , ∀ ( _ : ( ¬ ( GenLimit.Gold.Effective.Identifiable GenLimit.Gold.Effective.Generator m C ) ) ) , ( ¬ ( GenLimit.Gold.Effective.Identifiable GenLimit.Gold.Effective.Tester m C ) )
```

### Theorem I.3 · `GenLimit.Gold.Results.theorem_I_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( N : Type _ ) , ∀ [ Primcodable N ] , ∀ ( names : ( GenLimit.Gold.Effective.NameRelation N ) ) , ∀ ( C : ( Set GenLimit.Language ) ) , ( ( ( GenLimit.Gold.Effective.Identifiable names GenLimit.Gold.Effective.arbitraryInformant C ) ↔ ( GenLimit.Gold.Effective.Identifiable names GenLimit.Gold.Effective.methodical C ) ) ) ∧ ( ( ( GenLimit.Gold.Effective.Identifiable names GenLimit.Gold.Effective.methodical C ) ↔ ( GenLimit.Gold.Effective.RequestIdentifiable names C ) ) )
```

### Theorem I.4 · `GenLimit.Gold.Results.theorem_I_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Gold.Effective.Identifiable GenLimit.Gold.Effective.Tester GenLimit.Gold.Effective.methodical GenLimit.Gold.Effective.primitiveLanguages )
```

### Theorem I.5 · `GenLimit.Gold.Results.theorem_I_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ¬ ( GenLimit.Gold.Effective.Identifiable GenLimit.Gold.Effective.Generator GenLimit.Gold.Effective.methodical GenLimit.Gold.Effective.recursiveLanguages ) )
```

### Theorem I.6 · `GenLimit.Gold.Results.theorem_I_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Gold.Effective.Identifiable GenLimit.Gold.Effective.Tester GenLimit.Gold.Effective.arbitraryText GenLimit.Gold.Text.finiteLanguages )
```

### Theorem I.7 · `GenLimit.Gold.Results.theorem_I_7`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Gold.Effective.Identifiable GenLimit.Gold.Effective.Generator GenLimit.Gold.Effective.primitiveRecursiveText GenLimit.Gold.Effective.enumerableLanguages )
```

### Theorem I.8 · `GenLimit.Gold.Results.theorem_I_8`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( Set GenLimit.Language ) ) , ∀ ( _ : ( GenLimit.Gold.Text.IsSuperfinite C ) ) , ( ¬ ( ( ( GenLimit.Gold.Effective.Named GenLimit.Gold.Effective.Generator C ) ∧ ( GenLimit.Gold.Effective.Identifiable GenLimit.Gold.Effective.Generator GenLimit.Gold.Effective.recursiveText C ) ) ) )
```

### Theorem I.9 · `GenLimit.Gold.Results.theorem_I_9`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( Set GenLimit.Language ) ) , ∀ ( _ : ( GenLimit.Gold.Text.IsSuperfinite C ) ) , ( ¬ ( ( ( GenLimit.Gold.Effective.Named GenLimit.Gold.Effective.Tester C ) ∧ ( GenLimit.Gold.Effective.Identifiable GenLimit.Gold.Effective.Tester GenLimit.Gold.Effective.primitiveRecursiveText C ) ) ) )
```

Grammar regression for P00: 1879/1879 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P00A

SHA-256 of the checked page: `d25994ac7bb6336ddb4656112175b9643336d36a2f864a98713f5b47931fbad0`

### Semantic characterization · `GenLimit.Angluin.Results.semantic_characterization`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Nonempty α ] , ∀ [ Countable α ] , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.Angluin.SemanticallyInferrable C ) ↔ ( GenLimit.Angluin.ConditionTwo C ) )
```

### Theorem 1 · `GenLimit.Angluin.Results.theorem_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ( ( GenLimit.Angluin.EffectiveInferrable F ) ↔ ( GenLimit.Angluin.ConditionOne F ) )
```

### Theorem 2 · `GenLimit.Angluin.Results.theorem_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ F : GenLimit.Angluin.EffectiveIndexedFamily , ( ( GenLimit.Angluin.ConditionTwo ( GenLimit.Angluin.EffectiveIndexedFamily.language F ) ) ∧ ( ¬ ( GenLimit.Angluin.EffectiveInferrable F ) ) ) )
```

### Theorem 3 · `GenLimit.Angluin.Results.theorem_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ F : GenLimit.Angluin.EffectiveIndexedFamily , ( ( GenLimit.Angluin.EffectiveInferrable F ) ∧ ( ¬ ( GenLimit.Angluin.ConditionOnePrime F ) ) ) )
```

### Theorem 4 · `GenLimit.Angluin.Results.theorem_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ F : GenLimit.Angluin.EffectiveIndexedFamily , ( ( GenLimit.Angluin.EffectiveInferrable F ) ) ∧ ( ( ¬ ( ∃ M : GenLimit.Angluin.InferenceMachine , ( ( GenLimit.Angluin.InferenceMachine.Identifies M F ) ∧ ( GenLimit.Angluin.InferenceMachine.Conservative M F ) ) ) ) ) )
```

### Theorem 5 · `GenLimit.Angluin.Results.theorem_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ∀ ( _ : ( GenLimit.Angluin.ConditionThree ( GenLimit.Angluin.EffectiveIndexedFamily.language F ) ) ) , ∀ ( _ : ( GenLimit.Angluin.ConditionFive F ) ) , ( ∃ M : GenLimit.Angluin.InferenceMachine , ( ( GenLimit.Angluin.InferenceMachine.Identifies M F ) ∧ ( ( GenLimit.Angluin.InferenceMachine.Consistent M F ) ∧ ( ( GenLimit.Angluin.InferenceMachine.Responsive M F ) ∧ ( GenLimit.Angluin.InferenceMachine.Conservative M F ) ) ) ) )
```

### Corollary 1 · `GenLimit.Angluin.Results.corollary_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ∀ ( _ : ( GenLimit.Angluin.EffectiveInferrable F ) ) , ( GenLimit.Angluin.ConditionTwo ( GenLimit.Angluin.EffectiveIndexedFamily.language F ) )
```

### Corollary 2 · `GenLimit.Angluin.Results.corollary_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ∀ ( _ : ( GenLimit.Angluin.ConditionThree ( GenLimit.Angluin.EffectiveIndexedFamily.language F ) ) ) , ( GenLimit.Angluin.EffectiveInferrable F )
```

### Corollary 3 · `GenLimit.Angluin.Results.corollary_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ∀ ( _ : ( GenLimit.Angluin.ConditionTwo ( GenLimit.Angluin.EffectiveIndexedFamily.language F ) ) ) , ∀ ( _ : ( GenLimit.Angluin.ConditionFour F ) ) , ( GenLimit.Angluin.EffectiveInferrable F )
```

Grammar regression for P00A: 884/884 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P01

SHA-256 of the checked page: `7bdfa945e3339131ecfd2496cdc8a6d75d52be867240e5f23915df78dc647fb6`

### Theorem 2.1 · `GenLimit.KM.Results.theorem_2_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.OracleFamily ) , let G := ( GenLimit.OracleFamily.kmGenerator C ) ; ∀ ( x : ( ℕ → ℕ ) ) , let o := fun t => ( G x t ) ; ∀ ( z : ℕ ) , ∀ ( _ : ( Set.range x = ( C.language z ) ) ) , depends_only% [ C , x , z ] ( ∃ «t⋆» : ℕ , ( ∀ ( t : ℕ ) , «t⋆» ≤ t → ( ( o t ) ∈ ( ( C.language z ) \ ( IRStatement.FirstTerms.firstTerms x t ) ) ) ) )
```

### Theorem 2.2 · `GenLimit.KM.Results.theorem_2_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( C : ( Finset ℕ ) ) , depends_only% [ O , C ] ( ∃ t_C : ℕ , ∀ ( S : ( Finset ℕ ) ) , ∀ ( _ : ( t_C ≤ Finset.card S ) ) , let I := ( Finset.filter ( fun i => ( ∀ x ∈ S , ( O.query i x = true ) ) ) C ) ; let A := { x : ℕ | ( x ∉ S ) ∧ ( ( ∀ i ∈ I , ( O.query i x = true ) ) ) } ; ∀ z ∈ C , ∀ ( _ : ( binrel% HasSubset.Subset S ( O.language z ) ) ) , ∃ ( _ : Set.Infinite A ) , let u := IRStatement.increasingEnumeration A ( by assumption ) ; ( ( Function.Injective u ) ∧ ( Set.range u ⊆ ( ( O.language z ) \ S ) ) ) )
```

### Theorem 7.1 · `GenLimit.KM.Results.theorem_7_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A : Type _ ) , ∀ [ DecidableEq A ] , ∀ ( e : ( ( List A ) ≃ ℕ ) ) , ∀ ( C : ( GenLimit.KM.Transport.IndexedOracleFamily ( List A ) ) ) , let robust := fun ( subject : ( List A ) ) => ∀ ( i n : ℕ ) , ∃ c , n ≤ List.length c ∧ ( subject ++ c ) ∈ C.language i ; let G := ( GenLimit.KM.Prompted.generatorOfEquiv e C ) ; ∀ ( x : ( ℕ → ( List A ) ) ) , ∀ ( z : ℕ ) , ∀ ( _ : ( Set.range x = ( C.language z ) ) ) , ∀ ( p : ( ℕ → ( List A ) ) ) , ∀ ( _ : ( ∀ t : ℕ , ( robust ( p t ) ) ) ) , let w := fun t => ( G x p ( by assumption ) t ) ; depends_only% [ A , e , C , x , z , p ] ( ∃ «t⋆» : ℕ , ( ∀ ( t : ℕ ) , «t⋆» ≤ t → ( ( List.IsPrefix ( p t ) ( w t ) ) ∧ ( ( w t ) ∈ ( ( C.language z ) \ ( IRStatement.FirstTerms.firstTerms x t ) ) ) ) ) )
```

## Negative control · P01 Theorem 2.2 with the sample chosen before the threshold

### A. Dependency list updated to include S

Edited English (temporary copy):

```text
Let O be an indexed family of languages L_0, L_1, L_2, … ⊆ ℕ. Each L_i is infinite. O has a membership oracle. Let C be a finite set of natural numbers. Let S be a finite set of natural numbers.

There is t_C ∈ ℕ, depending only on O, C and S, with the following property.

Suppose that |S| ≥ t_C.

Let I = {i ∈ C : the oracle confirms x ∈ L_i for every x ∈ S}. Let A = {x ∈ ℕ ∖ S : the oracle confirms x ∈ L_i for every i ∈ I}. Let z ∈ C with S ⊆ L_z.

Then A is infinite. Let u list the elements of A in increasing order. Then u is injective and every value of u lies in L_z ∖ S.
```

- GF parses: 1 complete
- Outcome: kernel: statement mismatch

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( C : ( Finset ℕ ) ) , ∀ ( S : ( Finset ℕ ) ) , depends_only% [ O , C , S ] ( ∃ t_C : ℕ , ∀ ( _ : ( t_C ≤ Finset.card S ) ) , let I := ( Finset.filter ( fun i => ( ∀ x ∈ S , ( O.query i x = true ) ) ) C ) ; let A := { x : ℕ | ( x ∉ S ) ∧ ( ( ∀ i ∈ I , ( O.query i x = true ) ) ) } ; ∀ z ∈ C , ∀ ( _ : ( binrel% HasSubset.Subset S ( O.language z ) ) ) , ∃ ( _ : Set.Infinite A ) , let u := IRStatement.increasingEnumeration A ( by assumption ) ; ( ( Function.Injective u ) ∧ ( Set.range u ⊆ ( ( O.language z ) \ S ) ) ) )
```

### B. Dependency list left as “O and C”

Edited English (temporary copy):

```text
Let O be an indexed family of languages L_0, L_1, L_2, … ⊆ ℕ. Each L_i is infinite. O has a membership oracle. Let C be a finite set of natural numbers. Let S be a finite set of natural numbers.

There is t_C ∈ ℕ, depending only on O and C, with the following property.

Suppose that |S| ≥ t_C.

Let I = {i ∈ C : the oracle confirms x ∈ L_i for every x ∈ S}. Let A = {x ∈ ℕ ∖ S : the oracle confirms x ∈ L_i for every i ∈ I}. Let z ∈ C with S ⊆ L_z.

Then A is infinite. Let u list the elements of A in increasing order. Then u is injective and every value of u lies in L_z ∖ S.
```

- GF parses: 1 complete
- Outcome: elaboration: the reading says the choice depends only on [O, C], but the variables in scope are [O, C, S]

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( C : ( Finset ℕ ) ) , ∀ ( S : ( Finset ℕ ) ) , depends_only% [ O , C ] ( ∃ t_C : ℕ , ∀ ( _ : ( t_C ≤ Finset.card S ) ) , let I := ( Finset.filter ( fun i => ( ∀ x ∈ S , ( O.query i x = true ) ) ) C ) ; let A := { x : ℕ | ( x ∉ S ) ∧ ( ( ∀ i ∈ I , ( O.query i x = true ) ) ) } ; ∀ z ∈ C , ∀ ( _ : ( binrel% HasSubset.Subset S ( O.language z ) ) ) , ∃ ( _ : Set.Infinite A ) , let u := IRStatement.increasingEnumeration A ( by assumption ) ; ( ( Function.Injective u ) ∧ ( Set.range u ⊆ ( ( O.language z ) \ S ) ) ) )
```

Grammar regression for P01: 3185/3185 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P02

SHA-256 of the checked page: `f8eaeefd35a3ba4f959d55111f0578bac3c344aab18426bab811e889eab84731`

### Proposition 2.1 · `GenLimit.LiRamanTewari.Results.proposition_2_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒳» : Type , ( ( Countable «𝒳» ) ) ∧ ( ( ( Infinite «𝒳» ) ) ∧ ( ( ( ∃ «ℋ_1» : ( GenLimit.Generic.LanguageClass «𝒳» ) , ( ( GenLimit.LiRamanTewari.UUS «ℋ_1» ) ∧ ( ( GenLimit.LiRamanTewari.NonuniformlyGeneratable «ℋ_1» ) ∧ ( ¬ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ_1» ) ) ) ) ) ) ∧ ( ( ∃ «ℋ_2» : ( GenLimit.Generic.LanguageClass «𝒳» ) , ( ( GenLimit.LiRamanTewari.UUS «ℋ_2» ) ∧ ( ( GenLimit.LiRamanTewari.GeneratableInLimit «ℋ_2» ) ∧ ( ¬ ( GenLimit.LiRamanTewari.NonuniformlyGeneratable «ℋ_2» ) ) ) ) ) ) ) ) )
```

### Theorem 3.3 · `GenLimit.LiRamanTewari.Results.theorem_3_3`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.LiRamanTewari.UUS «ℋ» ) ) , ( ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ↔ ( GenLimit.LiRamanTewari.HasFiniteClosureDimension «ℋ» ) )
```

### Theorem 3.3 sample complexity bounds · `GenLimit.LiRamanTewari.Results.theorem_3_3_sample_complexity_bounds`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , let O := ( GenLimit.LiRamanTewari.optimalUniformGenerationSampleComplexity «ℋ» ) ; ∀ ( _ : ( GenLimit.LiRamanTewari.UUS «ℋ» ) ) , ∀ ( d : ℕ ) , ∀ ( _ : ( GenLimit.LiRamanTewari.HasClosureDimension «ℋ» d ) ) , ( ( ( ↑ d ) ≤ O ) ∧ ( O ≤ ( ↑ ( d + 1 ) ) ) )
```

### Theorem 3.5 · `GenLimit.LiRamanTewari.Results.theorem_3_5`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.LiRamanTewari.UUS «ℋ» ) ) , ( ( GenLimit.LiRamanTewari.NonuniformlyGeneratable «ℋ» ) ) ↔ ( ( ∃ classes : ( ℕ → ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ( ( GenLimit.LiRamanTewari.IsNondecreasingCover «ℋ» classes ) ) ∧ ( ( ∀ n : ℕ , ( GenLimit.LiRamanTewari.HasFiniteClosureDimension ( classes n ) ) ) ) ) )
```

### Theorem 3.10 · `GenLimit.LiRamanTewari.Results.theorem_3_10`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.LiRamanTewari.UUS «ℋ» ) ) , ∀ ( _ : ( ∃ n : ℕ , ( ∃ classes : ( ( Fin n ) → ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ( ( GenLimit.LiRamanTewari.IsFiniteCover «ℋ» classes ) ∧ ( ∀ i : ( Fin n ) , ( GenLimit.LiRamanTewari.HasFiniteClosureDimension ( classes i ) ) ) ) ) ) ) , ( GenLimit.LiRamanTewari.GeneratableInLimit «ℋ» )
```

### Theorem 4.1 · `GenLimit.LiRamanTewari.Results.theorem_4_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ℤ ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ∧ ( ¬ ( GenLimit.LiRamanTewari.PACLearnable «ℋ» ) ) ) ) ) ) ∧ ( ( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ( ( ℕ × ℕ ) ⊕ ( Bool × ℕ ) ) ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.OnlineLearnable «ℋ» ) ∧ ( ¬ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ) ) ) ) ) ∧ ( ( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ℤ ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.OnlineLearnable «ℋ» ) ∧ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ) ) ) ) ∧ ( ( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ( ℕ ⊕ ( ( ℕ × ℕ ) ⊕ ( Bool × ℕ ) ) ) ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.PACLearnable «ℋ» ) ∧ ( ( ¬ ( GenLimit.LiRamanTewari.OnlineLearnable «ℋ» ) ) ∧ ( ¬ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ) ) ) ) ) ) ∧ ( ( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ℕ ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.PACLearnable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ∧ ( ¬ ( GenLimit.LiRamanTewari.OnlineLearnable «ℋ» ) ) ) ) ) ) ) ∧ ( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ℕ ) , ( ( Set.Countable «ℋ» ) ∧ ( ( ¬ ( GenLimit.LiRamanTewari.PACLearnable «ℋ» ) ) ∧ ( ¬ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ) ) ) ) ) ) ) ) )
```

### Theorem 4.1 combinatorial core · `GenLimit.LiRamanTewari.Results.theorem_4_1_combinatorial_core`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ℤ ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ∧ ( ¬ ( GenLimit.LiRamanTewari.HasFiniteVCDimension «ℋ» ) ) ) ) ) ) ∧ ( ( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ( ( ℕ × ℕ ) ⊕ ( Bool × ℕ ) ) ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.HasFiniteLittlestoneDimension «ℋ» ) ∧ ( ¬ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ) ) ) ) ) ∧ ( ( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ℤ ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.HasFiniteLittlestoneDimension «ℋ» ) ∧ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ) ) ) ) ∧ ( ( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ( ℕ ⊕ ( ( ℕ × ℕ ) ⊕ ( Bool × ℕ ) ) ) ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.HasFiniteVCDimension «ℋ» ) ∧ ( ( ¬ ( GenLimit.LiRamanTewari.HasFiniteLittlestoneDimension «ℋ» ) ) ∧ ( ¬ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ) ) ) ) ) ) ∧ ( ( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ℕ ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.HasFiniteVCDimension «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ∧ ( ¬ ( GenLimit.LiRamanTewari.HasFiniteLittlestoneDimension «ℋ» ) ) ) ) ) ) ) ∧ ( ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ℕ ) , ( ( Set.Countable «ℋ» ) ∧ ( ( ¬ ( GenLimit.LiRamanTewari.HasFiniteVCDimension «ℋ» ) ) ∧ ( ¬ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ) ) ) ) ) ) ) ) )
```

### Theorem 5.1 · `GenLimit.LiRamanTewari.Results.theorem_5_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» «𝒴» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ [ Countable «𝒴» ] , ∀ ( «ℋ» : ( GenLimit.LiRamanTewari.MulticlassHypothesisClass «𝒳» «𝒴» ) ) , ∀ ( _ : ( GenLimit.LiRamanTewari.PUUS «ℋ» ) ) , ( ( GenLimit.LiRamanTewari.PromptedUniformlyGeneratable «ℋ» ) ↔ ( GenLimit.LiRamanTewari.HasFinitePromptedClosureDimension «ℋ» ) )
```

### Theorem 5.2 · `GenLimit.LiRamanTewari.Results.theorem_5_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» «𝒴» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ [ Countable «𝒴» ] , ∀ ( «ℋ» : ( GenLimit.LiRamanTewari.MulticlassHypothesisClass «𝒳» «𝒴» ) ) , ∀ ( _ : ( GenLimit.LiRamanTewari.PUUS «ℋ» ) ) , ( ( GenLimit.LiRamanTewari.PromptedNonuniformlyGeneratable «ℋ» ) ) ↔ ( ( ∃ classes : ( ℕ → ( GenLimit.LiRamanTewari.MulticlassHypothesisClass «𝒳» «𝒴» ) ) , ( ( ( Monotone classes ) ∧ ( «ℋ» = ( Set.iUnion ( fun n => ( classes n ) ) ) ) ) ) ∧ ( ( ∀ n : ℕ , ( GenLimit.LiRamanTewari.HasFinitePromptedClosureDimension ( classes n ) ) ) ) ) )
```

### Theorem C.2 · `GenLimit.LiRamanTewari.Results.theorem_C_2`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.LiRamanTewari.UUS «ℋ» ) ) , ∀ ( _ : ( ∃ n : ℕ , ( ∃ classes : ( ( Fin n ) → ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ( ( GenLimit.LiRamanTewari.IsFiniteCover «ℋ» classes ) ∧ ( ∀ i : ( Fin n ) , ( GenLimit.LiRamanTewari.EventuallyUnboundedClosure ( classes i ) ) ) ) ) ) ) , ( GenLimit.LiRamanTewari.GeneratableInLimit «ℋ» )
```

### Theorem C.4 · `GenLimit.LiRamanTewari.Results.theorem_C_4`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.LiRamanTewari.UUS «ℋ» ) ) , ∀ ( _ : ( ∃ classes : ( ℕ → ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ( ( GenLimit.LiRamanTewari.IsNondecreasingCover «ℋ» classes ) ∧ ( ∀ n : ℕ , ( GenLimit.LiRamanTewari.EventuallyUnboundedClosure ( classes n ) ) ) ) ) ) , ( GenLimit.LiRamanTewari.GeneratableInLimit «ℋ» )
```

### Euc not imply uniform · `GenLimit.LiRamanTewari.Results.euc_not_imply_uniform`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ( ℕ ⊕ ( ℕ × ℕ ) ) ) , ( ( Set.Countable «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.UUS «ℋ» ) ∧ ( ( GenLimit.LiRamanTewari.EventuallyUnboundedClosure «ℋ» ) ∧ ( ¬ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ) ) ) ) )
```

Grammar regression for P02: 1180/1180 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P03

SHA-256 of the checked page: `7870e61c3e3742aa7989ff4e95398c1848ef4ed6ffcba57c03a3ebf248fa067b`

### Theorem 3.1 · `GenLimit.HallucinationModeCollapse.Results.theorem_3_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.NontrivialCollection «𝓛» ) ) , ( ( ( ( GenLimit.HallucinationModeCollapse.AlmostExponentialIdentifiable «𝓛» ) ) ∧ ¬ ( ( GenLimit.HallucinationModeCollapse.NoIdentificationRate «𝓛» ) ) ) ∨ ( ¬ ( ( GenLimit.HallucinationModeCollapse.AlmostExponentialIdentifiable «𝓛» ) ) ∧ ( ( GenLimit.HallucinationModeCollapse.NoIdentificationRate «𝓛» ) ) ) ) ∧ ( ( ( ( GenLimit.HallucinationModeCollapse.AlmostExponentialIdentifiable «𝓛» ) ) ↔ ( ∀ ( i : ℕ ) , ( ∃ T : ( Finset ℕ ) , ( GenLimit.Angluin.IsTellTale «𝓛» i T ) ) ) ) ∧ ( ∀ ( A : ( ( List ℕ ) → ( PMF ℕ ) ) ) , ( ∃ i : ℕ , ∃ «𝒫» : ( PMF ℕ ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution «𝓛» i «𝒫» ) ∧ ( ∃ᶠ ( n : ℕ ) in Filter.atTop , ( ( Real.exp ( ( - 2 ) * ( ↑ n ) ) ) ≤ ( GenLimit.HallucinationModeCollapse.identificationError «𝓛» A «𝒫» i n ) ) ) ) ) ) )
```

### Theorem 3.2 · `GenLimit.HallucinationModeCollapse.Results.theorem_3_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ( ( GenLimit.HallucinationModeCollapse.ExponentialGenerates ( O.language ) ( GenLimit.HallucinationModeCollapse.deterministicIdentifier ( GenLimit.HallucinationModeCollapse.certifiedKM O ) ) ) ) ∧ ( ( ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query O ) ) ) , ( Computable ( GenLimit.HallucinationModeCollapse.certifiedKM O ) ) ) ∧ ( ∀ ( _ : ( GenLimit.HallucinationModeCollapse.GenerationNontrivial ( O.language ) ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ∃ i : ℕ , ∃ «𝒫» : ( PMF ℕ ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution ( O.language ) i «𝒫» ) ) ∧ ( ( ∃ c : ℝ , ( ( 0 < c ) ) ∧ ( ( ∃ D : ℝ , ( ( 0 < D ) ∧ ( ∃ᶠ ( n : ℕ ) in Filter.atTop , ( ( D * ( Real.exp ( ( - c ) * ( ↑ n ) ) ) ) ≤ ( GenLimit.HallucinationModeCollapse.generationError ( O.language ) G «𝒫» i n ) ) ) ) ) ) ) ) ) ) )
```

### Theorem 3.3 · `GenLimit.HallucinationModeCollapse.Results.theorem_3_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.GenerationNontrivial ( O.language ) ) ) , ( ∀ ( _ : ( ¬ ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit ( O.language ) ) ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.DecidableMOP G ) ) , ( GenLimit.HallucinationModeCollapse.NoBreadthRate ( O.language ) G ) ) ∧ ( ( ( ∃ G : GenLimit.HallucinationModeCollapse.StatisticalGenerator , ( ( GenLimit.HallucinationModeCollapse.DecidableMOP G ) ) ∧ ( ( ( GenLimit.HallucinationModeCollapse.OracleMOP ( GenLimit.HallucinationModeCollapse.generationOracle O ) G ) ) ∧ ( ( ( GenLimit.HallucinationModeCollapse.ExponentialGenerates ( O.language ) G ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query O ) ) ) , ( GenLimit.HallucinationModeCollapse.HasComputableSampler G ) ) ) ) ) ) ∧ ( ( ∀ ( _ : ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit ( O.language ) ) ) , ( GenLimit.HallucinationModeCollapse.CertifiedBreadthPositiveBranch O ) ) ∧ ( ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ∃ i : ℕ , ∃ «𝒫» : ( PMF ℕ ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution ( O.language ) i «𝒫» ) ) ∧ ( ( ∃ c : ℝ , ( ( 0 < c ) ) ∧ ( ( ∃ D : ℝ , ( ( 0 < D ) ∧ ( ∃ᶠ ( n : ℕ ) in Filter.atTop , ( ( D * ( Real.exp ( ( - c ) * ( ↑ n ) ) ) ) ≤ ( GenLimit.HallucinationModeCollapse.generationError ( O.language ) G «𝒫» i n ) ) ) ) ) ) ) ) ) ) ) )
```

### Theorem 3.4 · `GenLimit.HallucinationModeCollapse.Results.theorem_3_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( G : GenLimit.HallucinationModeCollapse.TokenGenerator ) , ∀ ( _ : ( GenLimit.Support.RandomBitMachine.Machine.AlwaysHalts ( GenLimit.HallucinationModeCollapse.TokenGenerator.machine G ) ) ) , ( ∃ query : ( ( List ℕ ) → Bool ) , ( ( Computable query ) ) ∧ ( ∀ ( word : ( List ℕ ) ) , ( ( ( query word ) = Bool.true ) ↔ ( 0 < ( GenLimit.HallucinationModeCollapse.TokenGenerator.wordProbability (hG := by assumption) G word ) ) ) ) )
```

### Theorem 3.5 · `GenLimit.HallucinationModeCollapse.Results.theorem_3_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ( ∀ ( _ : ( ¬ ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit ( O.language ) ) ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.DecidableMOP G ) ) , ( ¬ ( GenLimit.HallucinationModeCollapse.FreshBreadthInLimit ( GenLimit.HallucinationModeCollapse.statisticalSupportView G ) ( O.language ) ) ) ) ∧ ( ∀ ( _ : ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit ( O.language ) ) ) , ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query O ) ) ) , ( ∃ G : GenLimit.HallucinationModeCollapse.StatisticalGenerator , ( ( GenLimit.HallucinationModeCollapse.DecidableMOP G ) ∧ ( GenLimit.HallucinationModeCollapse.FreshBreadthInLimit ( GenLimit.HallucinationModeCollapse.statisticalSupportView G ) ( O.language ) ) ) ) )
```

### Theorem 3.6 · `GenLimit.HallucinationModeCollapse.Results.theorem_3_6`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( _ : ( ¬ ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit «𝓛» ) ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.StatisticalStable G «𝓛» ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.DecidableMOP G ) ) , ( GenLimit.HallucinationModeCollapse.NoUnambiguousRate «𝓛» G )
```

### Theorem 3.7 · `GenLimit.HallucinationModeCollapse.Results.theorem_3_7`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( _ : ( ¬ ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit «𝓛» ) ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.StatisticalStable G «𝓛» ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.DecidableMOP G ) ) , ( ¬ ( GenLimit.HallucinationModeCollapse.UnambiguousInLimit ( GenLimit.HallucinationModeCollapse.statisticalSupportView G ) «𝓛» ) )
```

### Theorem 3.8 · `GenLimit.HallucinationModeCollapse.Results.theorem_3_8`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( _ : ( ¬ ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit «𝓛» ) ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.StatisticalStable G «𝓛» ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.DecidableMOP G ) ) , ( GenLimit.HallucinationModeCollapse.NoApproximateBreadthRate «𝓛» G )
```

### Theorem 3.9 · `GenLimit.HallucinationModeCollapse.Results.theorem_3_9`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( _ : ( ¬ ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit «𝓛» ) ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.StatisticalStable G «𝓛» ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.DecidableMOP G ) ) , ( ¬ ( ( GenLimit.HallucinationModeCollapse.ApproximateBreadthInLimit ( GenLimit.HallucinationModeCollapse.statisticalSupportView G ) «𝓛» ) ) )
```

### Proposition 3.10 · `GenLimit.HallucinationModeCollapse.Results.proposition_3_10`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( O : ( GenLimit.MembershipOracle «𝓛» ) ) , ∀ ( S : ( GenLimit.SubsetOracle «𝓛» ) ) , let K := ( GenLimit.HallucinationModeCollapse.subsetIdentifier O S ) ; ∀ ( _ : ( ∀ i : ℕ , ( ∃ T : ( Finset ℕ ) , ( GenLimit.Angluin.IsTellTale «𝓛» i T ) ) ) ) , ( ( GenLimit.HallucinationModeCollapse.ExponentialIdentifies «𝓛» ( GenLimit.HallucinationModeCollapse.deterministicIdentifier K ) ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.MembershipOracle.query O ) ) ) , ∀ ( _ : ( Computable₂ ( GenLimit.SubsetOracle.query S ) ) ) , ( Computable K ) )
```

### Proposition 3.11 · `GenLimit.HallucinationModeCollapse.Results.proposition_3_11`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( O : ( GenLimit.MembershipOracle «𝓛» ) ) , let F := ( GenLimit.HallucinationModeCollapse.finiteVersionSpaceLearner O ) ; ∀ ( _ : ( Set.Finite ( Set.range «𝓛» ) ) ) , ( ( GenLimit.HallucinationModeCollapse.ExponentialIdentifies «𝓛» ( GenLimit.HallucinationModeCollapse.deterministicIdentifier F ) ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.MembershipOracle.query O ) ) ) , ( Computable F ) )
```

### Proposition 3.12 · `GenLimit.HallucinationModeCollapse.Results.proposition_3_12`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( O : ( GenLimit.MembershipOracle «𝓛» ) ) , let F := ( GenLimit.HallucinationModeCollapse.finiteVersionSpaceLearner O ) ; ∀ ( _ : ( ∀ i : ℕ , ( Set.Finite ( «𝓛» i ) ) ) ) , ( ( GenLimit.HallucinationModeCollapse.ExponentialIdentifies «𝓛» ( GenLimit.HallucinationModeCollapse.deterministicIdentifier F ) ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.MembershipOracle.query O ) ) ) , ( Computable F ) )
```

### Theorem 3.13 · `GenLimit.HallucinationModeCollapse.Results.theorem_3_13`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( O : ( GenLimit.MembershipOracle «𝓛» ) ) , let L := ( GenLimit.HallucinationModeCollapse.labeledEnumerationLearner O ) ; ( ( GenLimit.HallucinationModeCollapse.ExponentialLabeledIdentifies «𝓛» ( GenLimit.HallucinationModeCollapse.deterministicLabeledIdentifier L ) ) ) ∧ ( ( ∀ ( _ : ( Computable₂ ( GenLimit.MembershipOracle.query O ) ) ) , ( Computable L ) ) ∧ ( ∀ ( _ : ( GenLimit.HallucinationModeCollapse.NontrivialCollection «𝓛» ) ) , ∀ ( A : ( ( List GenLimit.HallucinationModeCollapse.LabeledDatum ) → ( PMF ℕ ) ) ) , ( ∃ i : ℕ , ∃ «𝒫» : ( PMF GenLimit.HallucinationModeCollapse.LabeledDatum ) , ( ( GenLimit.HallucinationModeCollapse.ValidLabeledDistribution «𝓛» i «𝒫» ) ∧ ( ∃ᶠ ( n : ℕ ) in Filter.atTop , ( ( Real.exp ( ( - 2 ) * ( ↑ n ) ) ) ≤ ( GenLimit.HallucinationModeCollapse.labeledIdentificationError «𝓛» A «𝒫» i n ) ) ) ) ) ) )
```

Grammar regression for P03: 1281/1281 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P04

SHA-256 of the checked page: `616880369c05dc3eba10c4a0a3a916ac2eabdd802f3ec568679dbd630479252b`

### Theorem 1 · `GenLimit.CharikarPabbaraju.Results.theorem_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Infinite α ] , ∀ [ Countable α ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ L ∈ ( Set.range «𝒞» ) , ( Set.Infinite L ) ) ) , ( GenLimit.CharikarPabbaraju.NonuniformlyGeneratable «𝒞» )
```

### Theorem 2 · `GenLimit.CharikarPabbaraju.Results.theorem_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ¬ ( ∃ A : GenLimit.CharikarPabbaraju.TwoLanguageMembershipAlgorithm , ( ( Computable A ) ∧ ( ∀ ( L₀ L₁ : ( Set ℕ ) ) , ( ( L₀ ≠ L₁ ) → ( ( Set.Infinite L₀ ) → ( ( Set.Infinite L₁ ) → ( GenLimit.CharikarPabbaraju.NonuniformTwoLanguageMembershipGuarantee A L₀ L₁ ) ) ) ) ) ) ) )
```

### Theorem 3 · `GenLimit.CharikarPabbaraju.Results.theorem_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒞» : ( Set ( GenLimit.Generic.Language ( List Bool ) ) ) , ( ( Set.Countable «𝒞» ) ) ∧ ( ( ( ∀ L ∈ «𝒞» , ( Set.Infinite L ) ) ) ∧ ( ( ( ∀ K ∈ «𝒞» , ( Language.IsRegular K ) ) ) ∧ ( ( ¬ ( GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable «𝒞» ) ) ) ) ) )
```

### Theorem 4 · `GenLimit.CharikarPabbaraju.Results.theorem_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Countable α ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ L ∈ ( Set.range «𝒞» ) , ( Set.Infinite L ) ) ) , ( ( GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable ( Set.range «𝒞» ) ) ↔ ( GenLimit.CharikarPabbaraju.WeakAngluinExistence ( Set.range «𝒞» ) ) )
```

### Theorem 5 · `GenLimit.CharikarPabbaraju.Results.theorem_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Countable α ] , ∀ ( «𝒞» : ( Set ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝒞» , ( Set.Infinite L ) ) ) , ( ( GenLimit.CharikarPabbaraju.UniformlyGeneratableWithFeedback «𝒞» ) ↔ ( GenLimit.CharikarPabbaraju.HasFiniteGFDimension «𝒞» ) )
```

Grammar regression for P04: 500/500 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P05

SHA-256 of the checked page: `bc2b7784fc489402f0af9bf23a5254d55ce4052aceeb351cc40a1d1d10f7ff02`

### Theorem 3.3 · `GenLimit.BreadthCharacterizations.Results.theorem_3_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ( ( ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( GenLimit.BreadthCharacterizations.IsExactBreadthGenerator «𝒢» ( O.language ) ) ) ) ↔ ( ( GenLimit.Angluin.ConditionTwo ( O.language ) ) ) ) ∧ ( ∀ ( emit : ( ℕ → ( ℕ → ( Option ℕ ) ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( GenLimit.Angluin.IsEnumeratedTellTale ( O.language ) i ( GenLimit.Angluin.enumeratedSet emit i ) ) ) ) , let A := ( GenLimit.Support.TruthTableProgram.run GenLimit.HallucinationModeCollapse.identificationProgram ( GenLimit.HallucinationModeCollapse.identificationOracle ( GenLimit.HallucinationModeCollapse.familyMembership O ) emit ) ) ; let «𝒢» := ( fun S => ( GenLimit.HallucinationModeCollapse.exactFreshSampler O S ( A S ) ) ) ; ( ( GenLimit.BreadthCharacterizations.IsExactBreadthGenerator ( fun S => ( PMF.support ( «𝒢» S ) ) ) ( O.language ) ) ) ∧ ( ( ( GenLimit.HallucinationModeCollapse.OracleMOP ( GenLimit.HallucinationModeCollapse.generationOracle O ) «𝒢» ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query O ) ) ) , ∀ ( _ : ( Computable₂ emit ) ) , ( ( GenLimit.HallucinationModeCollapse.HasComputableSampler «𝒢» ) ∧ ( GenLimit.HallucinationModeCollapse.UniformDecidableMOP «𝒢» ) ) ) ) )
```

### Theorem 3.5 · `GenLimit.BreadthCharacterizations.Results.theorem_3_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Countable α ] , ∀ ( «ℒ» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Nonempty ( «ℒ» i ) ) ) ) , ∀ ( P : ( ( List α ) → ( ( Set α ) → Prop ) ) ) , ∀ ( _ : ( ∀ S : ( List α ) , ( ∀ ( i j : ℕ ) , ( ( P S ( «ℒ» i ) ) → ( ( P S ( «ℒ» j ) ) → ( ( «ℒ» i ) = ( «ℒ» j ) ) ) ) ) ) ) , ∀ ( _ : ( GenLimit.BreadthCharacterizations.EventuallyGeneratesWith P «ℒ» ) ) , ( GenLimit.Angluin.ConditionTwo «ℒ» )
```

### Theorem 3.8 · `GenLimit.BreadthCharacterizations.Results.theorem_3_8`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , let K := ( GenLimit.HallucinationModeCollapse.generationOracle O ) ; ( ( ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator «𝒢» ( O.language ) ) ) ) ↔ ( ( GenLimit.BreadthCharacterizations.WeakAngluinCondition ( O.language ) ) ) ) ∧ ( ( ∀ ( S : ( GenLimit.SubsetOracle ( O.language ) ) ) , ∀ ( _ : ( GenLimit.BreadthCharacterizations.WeakAngluinCondition ( O.language ) ) ) , let «𝒢» := ( GenLimit.BreadthCharacterizations.criticalSampler O S ) ; ( ( GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator ( fun xs => ( PMF.support ( «𝒢» xs ) ) ) ( O.language ) ) ) ∧ ( ( ( GenLimit.HallucinationModeCollapse.OracleMOP K «𝒢» ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query O ) ) ) , ∀ ( _ : ( Computable₂ ( GenLimit.SubsetOracle.query S ) ) ) , ( ( GenLimit.HallucinationModeCollapse.HasComputableSampler «𝒢» ) ∧ ( GenLimit.HallucinationModeCollapse.UniformDecidableMOP «𝒢» ) ) ) ) ) ∧ ( ∀ ( emit : ( ℕ → ( ℕ → ( Option ℕ ) ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( GenLimit.CharikarPabbaraju.IsEnumeratedWeakTellTale ( O.language ) i ( GenLimit.Angluin.enumeratedSet emit i ) ) ) ) , let «𝒢» := ( GenLimit.BreadthCharacterizations.weakLaw O emit ) ; ( ( GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator ( fun xs => ( PMF.support ( «𝒢» xs ) ) ) ( O.language ) ) ) ∧ ( ( ( GenLimit.HallucinationModeCollapse.OracleMOP K «𝒢» ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query O ) ) ) , ∀ ( _ : ( Computable₂ emit ) ) , ( ( GenLimit.HallucinationModeCollapse.HasComputableSampler «𝒢» ) ∧ ( GenLimit.HallucinationModeCollapse.UniformDecidableMOP «𝒢» ) ) ) ) ) )
```

### Theorem 3.10 · `GenLimit.BreadthCharacterizations.Results.theorem_3_10`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Countable α ] , ∀ ( «ℒ» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «ℒ» i ) ) ) ) , ∀ ( P : ( ( List α ) → ( ( Set α ) → Prop ) ) ) , ∀ ( _ : ( ∀ S : ( List α ) , ( ∀ ( i j : ℕ ) , ( ( P S ( «ℒ» i ) ) → ( ( P S ( «ℒ» j ) ) → ( Set.Finite ( symmDiff ( «ℒ» i ) ( «ℒ» j ) ) ) ) ) ) ) ) , ∀ ( _ : ( GenLimit.BreadthCharacterizations.EventuallyGeneratesWith P «ℒ» ) ) , ( GenLimit.BreadthCharacterizations.WeakAngluinCondition «ℒ» )
```

### Theorem 3.15 · `GenLimit.BreadthCharacterizations.Results.theorem_3_15`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ( ( ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» ( O.language ) ) ∧ ( GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator «𝒢» ( O.language ) ) ) ) ) ↔ ( ( GenLimit.Angluin.ConditionTwo ( O.language ) ) ) ) ∧ ( ( ( ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsWholeTargetGenerator «𝒢» ( O.language ) ) ∧ ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» ( O.language ) ) ) ) ) ↔ ( ( GenLimit.Angluin.ConditionTwo ( O.language ) ) ) ) ∧ ( ( ( ¬ ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» ( O.language ) ) ∧ ( GenLimit.BreadthCharacterizations.IsExactBreadthGenerator «𝒢» ( O.language ) ) ) ) ) ) ∧ ( ∀ ( emit : ( ℕ → ( ℕ → ( Option ℕ ) ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( GenLimit.Angluin.IsEnumeratedTellTale ( O.language ) i ( GenLimit.Angluin.enumeratedSet emit i ) ) ) ) , let A := ( GenLimit.Support.TruthTableProgram.run GenLimit.HallucinationModeCollapse.identificationProgram ( GenLimit.HallucinationModeCollapse.identificationOracle ( GenLimit.HallucinationModeCollapse.familyMembership O ) emit ) ) ; let «𝒢» := ( fun S => ( GenLimit.HallucinationModeCollapse.exactFreshSampler O [] ( A S ) ) ) ; ( ( GenLimit.BreadthCharacterizations.IsWholeTargetGenerator ( fun S => ( PMF.support ( «𝒢» S ) ) ) ( O.language ) ) ) ∧ ( ( ( GenLimit.BreadthCharacterizations.IsStableGenerator ( fun S => ( PMF.support ( «𝒢» S ) ) ) ( O.language ) ) ) ∧ ( ( ( GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator ( fun S => ( PMF.support ( «𝒢» S ) ) ) ( O.language ) ) ) ∧ ( ( ( GenLimit.HallucinationModeCollapse.OracleMOP ( GenLimit.HallucinationModeCollapse.generationOracle O ) «𝒢» ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query O ) ) ) , ∀ ( _ : ( Computable₂ emit ) ) , ( ( GenLimit.HallucinationModeCollapse.HasComputableSampler «𝒢» ) ∧ ( GenLimit.HallucinationModeCollapse.UniformDecidableMOP «𝒢» ) ) ) ) ) ) ) ) )
```

### Theorem 4.3 · `GenLimit.BreadthCharacterizations.Results.theorem_4_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Nonempty α ] , ∀ [ Countable α ] , ∀ ( «ℒ» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «ℒ» i ) ) ) ) , ( ( ( ∃ «𝒢» : ( ( List α ) → ( Set α ) ) , ( GenLimit.BreadthCharacterizations.IsExactBreadthGenerator «𝒢» «ℒ» ) ) ) ↔ ( ( GenLimit.Angluin.ConditionTwo «ℒ» ) ) ) ∧ ( ( ( ( ∃ «𝒢» : ( ( List α ) → ( Set α ) ) , ( GenLimit.BreadthCharacterizations.GeneratesUnambiguously «𝒢» «ℒ» ) ) ) ↔ ( ( GenLimit.Angluin.ConditionTwo «ℒ» ) ) ) ∧ ( ( ( ( ∃ «𝒢» : ( ( List α ) → ( Set α ) ) , ( GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator «𝒢» «ℒ» ) ) ) ↔ ( ( GenLimit.BreadthCharacterizations.WeakAngluinCondition «ℒ» ) ) ) ∧ ( ( ( ∃ A : ( ( List α ) → ( ℕ → α ) ) , ( GenLimit.BreadthCharacterizations.EnumeratesExhaustively A «ℒ» ) ) ) ↔ ( ( GenLimit.BreadthCharacterizations.WeakAngluinCondition «ℒ» ) ) ) ) )
```

### Theorem 4.5 · `GenLimit.BreadthCharacterizations.Results.theorem_4_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ( ( ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» ( O.language ) ) ∧ ( GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator «𝒢» ( O.language ) ) ) ) ) ↔ ( ( GenLimit.Angluin.ConditionTwo ( O.language ) ) ) ) ∧ ( ( ( ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsWholeTargetGenerator «𝒢» ( O.language ) ) ∧ ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» ( O.language ) ) ) ) ) ↔ ( ( GenLimit.Angluin.ConditionTwo ( O.language ) ) ) ) ∧ ( ( ( ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» ( O.language ) ) ∧ ( GenLimit.BreadthCharacterizations.GeneratesUnambiguously «𝒢» ( O.language ) ) ) ) ) ↔ ( ( GenLimit.Angluin.ConditionTwo ( O.language ) ) ) ) ∧ ( ( ( ¬ ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» ( O.language ) ) ∧ ( GenLimit.BreadthCharacterizations.IsExactBreadthGenerator «𝒢» ( O.language ) ) ) ) ) ) ∧ ( ( ( ∃ B : ( ( List ℕ ) → ( ℕ → ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator ( fun S => ( Set.range ( B S ) ) ) ( O.language ) ) ∧ ( GenLimit.BreadthCharacterizations.EnumeratesExhaustively B ( O.language ) ) ) ) ) ↔ ( ( GenLimit.BreadthCharacterizations.WeakAngluinCondition ( O.language ) ) ) ) ) ) )
```

### Theorem 5.2 · `GenLimit.BreadthCharacterizations.Results.theorem_5_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ( ∀ ( _ : ( GenLimit.HallucinationModeCollapse.NontrivialCollection ( O.language ) ) ) , ∀ ( «𝒢» : ( ( List ℕ ) → ( PMF ℕ ) ) ) , ( ∃ i : ℕ , ∃ p : ( PMF ℕ ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution ( O.language ) i p ) ∧ ( ∃ᶠ ( n : ℕ ) in Filter.atTop , ( ( Real.exp ( ( - 2 ) * ( ↑ n ) ) ) ≤ ( GenLimit.DiscreteIID.probability ( GenLimit.DiscreteIID.samples p n ) { S : ( List ℕ ) | ( ( PMF.support ( «𝒢» S ) ) ≠ ( ( O.language i ) \ { x : ℕ | ( x ∈ S ) } ) ) } ) ) ) ) ) ) ∧ ( ( ∀ ( _ : ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit ( O.language ) ) ) , ( ∃ «𝒢» : ( ( List ℕ ) → ( PMF ℕ ) ) , ( GenLimit.HallucinationModeCollapse.ExponentialBreadth ( O.language ) «𝒢» ) ) ) ∧ ( ∀ ( _ : ( ¬ ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit ( O.language ) ) ) ) , ∀ ( «𝒢» : ( ( List ℕ ) → ( PMF ℕ ) ) ) , ( GenLimit.HallucinationModeCollapse.NoBreadthRate ( O.language ) «𝒢» ) ) )
```

### Theorem 5.3 · `GenLimit.BreadthCharacterizations.Results.theorem_5_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ( ∀ ( _ : ( GenLimit.HallucinationModeCollapse.GenerationNontrivial ( O.language ) ) ) , ∀ ( «𝒢» : ( ( List ℕ ) → ( PMF ℕ ) ) ) , ( ∃ i : ℕ , ∃ p : ( PMF ℕ ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution ( O.language ) i p ) ∧ ( ∃ᶠ ( n : ℕ ) in Filter.atTop , ( ( Real.exp ( ( - 2 ) * ( ↑ n ) ) ) ≤ ( GenLimit.DiscreteIID.probability ( GenLimit.DiscreteIID.samples p n ) { S : ( List ℕ ) | ( ¬ ( GenLimit.HallucinationModeCollapse.ApproximateBreadthAt ( PMF.support ( «𝒢» S ) ) ( O.language i ) ) ) } ) ) ) ) ) ) ∧ ( ( ∀ ( _ : ( GenLimit.BreadthCharacterizations.WeakAngluinCondition ( O.language ) ) ) , ( ∃ «𝒢» : ( ( List ℕ ) → ( PMF ℕ ) ) , ( GenLimit.HallucinationModeCollapse.AchievesScaledApproximateBreadthRate ( O.language ) «𝒢» ( fun r => ( Real.exp ( - r ) ) ) ) ) ) ∧ ( ∀ ( _ : ( ¬ ( GenLimit.BreadthCharacterizations.WeakAngluinCondition ( O.language ) ) ) ) , ∀ ( «𝒢» : ( ( List ℕ ) → ( PMF ℕ ) ) ) , ( GenLimit.HallucinationModeCollapse.NoBreadthRate ( O.language ) «𝒢» ) ) )
```

### Corollary 6.1 · `GenLimit.BreadthCharacterizations.Results.corollary_6_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Countable α ] , ∀ ( «ℒ» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «ℒ» i ) ) ) ) , ∀ ( _ : ( ¬ ( ∃ M : ( GenLimit.Angluin.SemanticIdentifier α ) , ( GenLimit.Angluin.SemanticallyIdentifies M «ℒ» ) ) ) ) , ∀ ( «𝒢» : ( ( List α ) → ( Set α ) ) ) , ∀ ( _ : ( GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator «𝒢» «ℒ» ) ) , ( ∃ z : ℕ , ∃ «E⋆» : ( ℕ → α ) , ∃ j : ( ℕ → ℕ ) , ∃ t : ( ℕ → ℕ ) , ( ( Set.range «E⋆» = ( «ℒ» z ) ) ) ∧ ( ( ( Function.Injective ( fun n => ( «ℒ» ( j n ) ) ) ) ) ∧ ( ( ( StrictMono t ) ) ∧ ( ∀ ( n : ℕ ) , ( ( HasSSubset.SSubset ( «ℒ» ( j n ) ) ( «ℒ» z ) ) ∧ ( GenLimit.BreadthCharacterizations.ApproximateBreadthCorrectAt «𝒢» ( «ℒ» ( j n ) ) «E⋆» ( t n ) ) ) ) ) ) )
```

### Corollary 7.2 · `GenLimit.BreadthCharacterizations.Results.corollary_7_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( S : ( GenLimit.SubsetOracle ( O.language ) ) ) , let «𝒢» := ( fun xs => ( PMF.support ( GenLimit.BreadthCharacterizations.criticalSampler O S xs ) ) ) ; ( ∀ ( _ : ( GenLimit.Angluin.ConditionTwo ( O.language ) ) ) , ( GenLimit.BreadthCharacterizations.IsExactBreadthGenerator «𝒢» ( O.language ) ) ) ∧ ( ( ∀ ( _ : ( GenLimit.BreadthCharacterizations.WeakAngluinCondition ( O.language ) ) ) , ( GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator «𝒢» ( O.language ) ) ) ∧ ( ( GenLimit.BreadthCharacterizations.IsInfiniteCoverageGenerator «𝒢» ( O.language ) ) ) )
```

### Theorem 8.7 · `GenLimit.BreadthCharacterizations.Results.theorem_8_7`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( GenLimit.BreadthCharacterizations.WeakAngluinCondition GenLimit.CharikarPabbaraju.coSingletonNatFamily ) ) ∧ ( ( ( ¬ ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» GenLimit.CharikarPabbaraju.coSingletonNatFamily ) ∧ ( GenLimit.BreadthCharacterizations.IsInfiniteCoverageGenerator «𝒢» GenLimit.CharikarPabbaraju.coSingletonNatFamily ) ) ) ) ) ∧ ( ( ¬ ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» GenLimit.CharikarPabbaraju.coSingletonNatFamily ) ∧ ( GenLimit.BreadthCharacterizations.SampleAllowingInfiniteCoverage «𝒢» GenLimit.CharikarPabbaraju.coSingletonNatFamily ) ) ) ) ) )
```

### Corollary 8.11 · `GenLimit.BreadthCharacterizations.Results.corollary_8_11`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( _ : ( Set.Finite ( Set.range ( O.language ) ) ) ) , ( let A := ( GenLimit.HallucinationModeCollapse.finiteVersionSpaceLearner ( GenLimit.HallucinationModeCollapse.familyMembership O ) ) ; let «𝒢» := ( fun S => ( GenLimit.HallucinationModeCollapse.exactFreshSampler O [] ( A S ) ) ) ; ( ( GenLimit.BreadthCharacterizations.IsWholeTargetGenerator ( fun S => ( PMF.support ( «𝒢» S ) ) ) ( O.language ) ) ) ∧ ( ( ( GenLimit.BreadthCharacterizations.IsStableGenerator ( fun S => ( PMF.support ( «𝒢» S ) ) ) ( O.language ) ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query O ) ) ) , ( GenLimit.HallucinationModeCollapse.HasComputableSampler «𝒢» ) ) ) ) ∧ ( ( ∀ ( m : ℕ ) , ∀ ( _ : ( ∀ i : ℕ , ( ∃ ( j : ℕ ) , j < m ∧ ( ( O.language j ) = ( O.language i ) ) ) ) ) , ( ∃ d : ℕ , ( ( GenLimit.Generic.HasClosureDimension ( Set.range ( O.language ) ) d ) ) ∧ ( ∀ ( i : ℕ ) , ∀ ( S : ( List ℕ ) ) , ∀ ( _ : ( ∀ x ∈ S , ( x ∈ ( O.language i ) ) ) ) , ∀ ( _ : ( d < ( Finset.card ( List.toFinset S ) ) ) ) , ( ∃ U : ( Set ℕ ) , ( ( Set.Infinite U ) ) ∧ ( ( ( binrel% HasSubset.Subset U ( O.language i ) ) ) ∧ ( ( ∀ ys : ( List ℕ ) , ( ( PMF.support ( GenLimit.BreadthCharacterizations.frozenCoverageLaw ( GenLimit.BreadthCharacterizations.finiteVSI (covers := by assumption) O m ) d ( HAppend.hAppend S ys ) ) ) = U ) ) ) ) ) ) ) ) ∧ ( ( ( ¬ ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» ( O.language ) ) ∧ ( GenLimit.BreadthCharacterizations.IsExactBreadthGenerator «𝒢» ( O.language ) ) ) ) ) ) ∧ ( ( ¬ ( ∃ «𝒢» : ( ( List ℕ ) → ( Set ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator «𝒢» ( O.language ) ) ∧ ( GenLimit.BreadthCharacterizations.IsInfiniteCoverageGenerator «𝒢» ( O.language ) ) ) ) ) ) ) )
```

Grammar regression for P05: 1286/1286 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P06

SHA-256 of the checked page: `02bdbb275127d98520febff82bdcbd0597d38a44a2a9de5f104742623b56a7eb`

### Theorem 3.1 · `GenLimit.NoisyExamples.Results.theorem_3_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.Generic.UUS «ℋ» ) ) , ( ( GenLimit.NoisyExamples.UniformNoiseIndependentGeneratable «ℋ» ) ↔ ( Set.Infinite ( GenLimit.NoisyExamples.commonIntersection «ℋ» ) ) )
```

### Theorem 3.3 · `GenLimit.NoisyExamples.Results.theorem_3_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Nonempty «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.Generic.UUS «ℋ» ) ) , ( ( GenLimit.NoisyExamples.UniformNoiseDependentGeneratable «ℋ» ) ) ↔ ( ∀ ( n : ℕ ) , ( GenLimit.NoisyExamples.FiniteNoisyClosureDimensionAt «ℋ» n ) )
```

### Theorem 3.9 · `GenLimit.NoisyExamples.Results.theorem_3_9`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.Generic.UUS «ℋ» ) ) , ∀ ( _ : ( GenLimit.Generic.NonuniformlyGeneratable «ℋ» ) ) , ( GenLimit.NoisyExamples.NoisilyGeneratableInLimit «ℋ» )
```

### Theorem 3.10 · `GenLimit.NoisyExamples.Results.theorem_3_10`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.Generic.UUS «ℋ» ) ) , ∀ ( _ : ( ∃ k : ℕ , ( ∃ classes : ( ( Fin k ) → ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ( ( «ℋ» = ( Set.iUnion ( fun i => ( classes i ) ) ) ) ∧ ( ∀ i : ( Fin k ) , ( GenLimit.NoisyExamples.UniformNoiseIndependentGeneratable ( classes i ) ) ) ) ) ) ) , ( GenLimit.NoisyExamples.NoisilyGeneratableInLimit «ℋ» )
```

Grammar regression for P06: 391/391 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P07

SHA-256 of the checked page: `acb2a74c0c6986dd6f1c1890896638e5e71b9b0f2767928d1ce99b840f036043`

### Theorem 2.1 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_2_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ( ∃ «𝒜» : ( ( List ℕ ) → ℕ ) , ( ∀ ( z : ℕ ) , ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range E = ( «𝒳» z ) ) ) , ( ∀ᶠ ( t : ℕ ) in Filter.atTop , ( binrel% HasSubset.Subset ( «𝒳» ( «𝒜» ( GenLimit.textPrefix E t ) ) ) ( «𝒳» z ) ) ) ) ∧ ( ∀ ( z : ℕ ) , ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range E = ( «𝒳» z ) ) ) , ∀ ( t : ℕ ) , ( ∃ ( r : ℕ ) , r ≥ t ∧ ( ( «𝒳» ( «𝒜» ( GenLimit.textPrefix E r ) ) ) = ( «𝒳» z ) ) ) ) )
```

### Corollary 2.2 · `GenLimit.KleinbergWei.DensityMeasures.Results.corollary_2_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( z : ℕ ) , ∀ ( ordering : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier ordering ) = ( «𝒳» z ) ) ) , ∀ ( _ : ( Set.range E = ( «𝒳» z ) ) ) , ( depends_only% [ «𝒳» , E , z , ordering ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( binrel% HasSubset.Subset ( «𝒳» ( GenLimit.KleinbergWei.DensityMeasures.guessIndex «𝒳» E t ) ) ( «𝒳» z ) ) ) ) ) ∧ ( ( ( Filter.limsup ( GenLimit.KleinbergWei.DensityMeasures.indexUpperDensityAt «𝒳» E ordering ) Filter.atTop ) = 1 ) )
```

### Theorem 2.3 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_2_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒳» : ( ℕ → GenLimit.Language ) , ∃ z : ℕ , ∃ O : GenLimit.KleinbergWei.OrderedLanguage , ( ( ∀ i : ℕ , ( Set.Infinite ( «𝒳» i ) ) ) ) ∧ ( ( ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier O ) = ( «𝒳» z ) ) ) ∧ ( ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.Vanishing «𝒳» z O ) ) ) )
```

### Theorem 2.4 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_2_4`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝒳» i ) ) ) ) , ∀ ( z : ℕ ) , ∀ ( O : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier O ) = ( «𝒳» z ) ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.Vanishing «𝒳» z O ) ) ↔ ( ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ( GenLimit.KleinbergWei.DensityMeasures.HasPerfectTowerBound ( Set.range «𝒳» ) ( ⟨ ( «𝒳» z ) , by first | assumption | exact ⟨ _ , rfl ⟩ | simp ⟩ ) O ε ) )
```

### Theorem 2.5 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_2_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( c : ℝ ) , ∀ ( _ : ( c < ( 1 / 2 ) ) ) , ∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) , depends_only% [ c , O ] ( ∃ «𝒜» : ( ( List ℕ ) → ℕ ) , ∀ ( z : ℕ ) , let K := ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ; ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range E = K ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid E ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play «𝒜» E ) K ) ∧ ( c ≤ ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity ( O z ) ( ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play «𝒜» E ) ) ∩ K ) ) ) ) )
```

### Theorem 2.6 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_2_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ c : ℝ , ( ( 0 < c ) ) ∧ ( ∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) , depends_only% [ c , O ] ( ∃ «𝒜» : ( ( List ℕ ) → ℕ ) , ∀ ( z : ℕ ) , let K := ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ; ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range E = K ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid E ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play «𝒜» E ) K ) ∧ ( c ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( O z ) ( ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play «𝒜» E ) ) ∩ K ) ) ) ) ) ) )
```

### Theorem 3.1 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_3_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( z : ℕ ) , ∀ ( _ : ( Set.range E = ( «𝒳» z ) ) ) , ( depends_only% [ «𝒳» , E , z ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( binrel% HasSubset.Subset ( «𝒳» ( GenLimit.KleinbergWei.DensityMeasures.guessIndex «𝒳» E t ) ) ( «𝒳» z ) ) ) ) ) ∧ ( ∀ ( t : ℕ ) , ( ∃ r : ℕ , ( ( t ≤ r ) ∧ ( GenLimit.KleinbergWei.DensityMeasures.AccurateAt «𝒳» E z r ) ) ) )
```

### Theorem 4.1 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_4_1`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝒳» i ) ) ) ) , ∀ ( z : ℕ ) , ∀ ( O : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier O ) = ( «𝒳» z ) ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.Vanishing «𝒳» z O ) ) ↔ ( ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ( GenLimit.KleinbergWei.DensityMeasures.HasPerfectTowerBound ( Set.range «𝒳» ) ( ⟨ ( «𝒳» z ) , by first | assumption | exact ⟨ _ , rfl ⟩ | simp ⟩ ) O ε ) )
```

### Theorem 4.9 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_4_9`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝒳» i ) ) ) ) , ∀ ( z : ℕ ) , ∀ ( O : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier O ) = ( «𝒳» z ) ) ) , ( ∃ τ : ℝ , ( ( GenLimit.KleinbergWei.DensityMeasures.IsTruthIndex ( Set.range «𝒳» ) ( ⟨ ( «𝒳» z ) , by first | assumption | exact ⟨ _ , rfl ⟩ | simp ⟩ ) O τ ) ) ∧ ( ( ∀ ( «𝒜» : ( ( Finset ℕ ) → ℕ ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidIndex «𝒳» «𝒜» ) ) , ( ∃ E : ( ℕ → ℕ ) , ( ( Set.range E = ( «𝒳» z ) ) ∧ ( ( GenLimit.KleinbergWei.DensityMeasures.indexBreadth «𝒳» O ( fun xs => ( «𝒜» ( List.toFinset xs ) ) ) E ) ≤ τ ) ) ) ) ∧ ( ( ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidIndex «𝒳» ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.selector «𝒳» ) ) ) ∧ ( ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range E = ( «𝒳» z ) ) ) , ( τ ≤ ( GenLimit.KleinbergWei.DensityMeasures.indexBreadth «𝒳» O ( fun xs => ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.selector «𝒳» ( List.toFinset xs ) ) ) E ) ) ) ) ) )
```

### Theorem 5.1 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_5_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) , depends_only% [ O ] ( ∃ «𝒜» : ( ( List ℕ ) → ℕ ) , ∀ ( z : ℕ ) , let K := ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ; ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range E = K ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid E ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play «𝒜» E ) K ) ) ∧ ( ∀ ( c : ℝ ) , ∀ ( _ : ( c < 1 ) ) , ( ( c / 2 ) ≤ ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity ( O z ) ( ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play «𝒜» E ) ) ∩ K ) ) ) ) )
```

### Claim 6.1 · `GenLimit.KleinbergWei.DensityMeasures.Results.claim_6_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( Set GenLimit.Language ) ) , ∀ ( L' : ( ↥ «𝒳» ) ) , ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range E = ( ↑ L' ) ) ) , ( ( GenLimit.KleinbergWei.TowerTopology.IsLimitPoint L' ) ) ↔ ( ( ∃ Λ : ( ℕ → ( ↥ «𝒳» ) ) , ( GenLimit.KleinbergWei.DensityMeasures.PerfectTower «𝒳» Λ L' ) ) )
```

### Theorem 6.2 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_6_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) , depends_only% [ O ] ( ∃ «𝒜» : ( ( List ℕ ) → ℕ ) , ∀ ( r : ℕ ) , ∀ ( _ : ( 0 < r ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost ( Set.range ( fun i => ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O i ) ) ) ) r ) ) , ∀ ( z : ℕ ) , let K := ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ; ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range E = K ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid E ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play «𝒜» E ) K ) ∧ ( ( 1 / ( 3 * ( ( ↑ r ) + 1 ) ) ) ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( O z ) ( ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play «𝒜» E ) ) ∩ K ) ) ) ) )
```

### Claim 6.11 counterexample · `GenLimit.KleinbergWei.DensityMeasures.Results.claim_6_11_counterexample`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒳» : ( ℕ → GenLimit.Language ) , ( ∃ ( hi : ( ∀ i : ℕ , ( Set.Infinite ( «𝒳» i ) ) ) ) , ( ∃ ( hr : ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost ( Set.range «𝒳» ) 1 ) ) , ( ∃ E : ( ℕ → ℕ ) , ∃ O : GenLimit.KleinbergWei.OrderedLanguage , ( ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier O ) = ( «𝒳» 0 ) ) ) ∧ ( ( ( Set.range E = ( «𝒳» 0 ) ) ) ∧ ( ( ¬ ( ∃ m : ℕ , ( ∀ ( start : ℕ ) , m ≤ start → ( ¬ ( ( GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.HasBadRunFrom O ( GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.badInputs O E ( GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.canonicalRunOutput (hInfinite := by assumption) (hr := by assumption) E 1 ) ) start ( 1 + 1 ) ) ) ) ) ) ) ) ) ) ) ) )
```

### Theorem 6.12 · `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_6_12`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) , depends_only% [ O ] ( ∃ «𝒜» : ( ( List ℕ ) → ℕ ) , ∀ ( z : ℕ ) , let K := ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ; ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range E = K ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid E ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play «𝒜» E ) K ) ∧ ( ( 1 / 8 ) ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( O z ) ( ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play «𝒜» E ) ) ∩ K ) ) ) ) )
```

### Index set counterexample · `GenLimit.KleinbergWei.DensityMeasures.Results.index_set_counterexample`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒳» : ( ℕ → GenLimit.Language ) , ∃ z : ℕ , ∃ O : GenLimit.KleinbergWei.OrderedLanguage , ( ( ∀ i : ℕ , ( Set.Infinite ( «𝒳» i ) ) ) ) ∧ ( ( ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier O ) = ( «𝒳» z ) ) ) ∧ ( ∀ ( «𝒜» : ( ( Finset ℕ ) → ℕ ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidIndexOnInjective «𝒳» «𝒜» ) ) , ( ∃ E : ( ℕ → ℕ ) , ( ( Function.Injective E ) ∧ ( ( Set.range E = ( «𝒳» z ) ) ∧ ( ( ∀ᶠ ( t : ℕ ) in Filter.atTop , ( ( «𝒳» ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.output «𝒜» E t ) ) ≠ ( «𝒳» z ) ) ) ∧ ( ( Filter.limsup ( fun t => ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity O ( «𝒳» ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.output «𝒜» E t ) ) ) ) Filter.atTop ) = 0 ) ) ) ) ) ) ) )
```

### Element set counterexample · `GenLimit.KleinbergWei.DensityMeasures.Results.element_set_counterexample`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) , ∃ z : ℕ , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) ∧ ( ( ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost ( Set.range ( fun i => ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O i ) ) ) ) 2 ) ) ∧ ( ∀ ( «𝒜» : ( ( Finset ℕ ) → ℕ ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidElementOnInjective ( fun i => ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O i ) ) ) «𝒜» ) ) , ( ∃ E : ( ℕ → ℕ ) , ( ( Function.Injective E ) ∧ ( ( Set.range E = ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ) ∧ ( ( ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity ( O z ) ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.output «𝒜» E ) ) ) = 0 ) ∧ ( ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( O z ) ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.output «𝒜» E ) ) ) = 0 ) ) ) ) ) ) ) )
```

Grammar regression for P07: 1591/1591 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P08

SHA-256 of the checked page: `c51063107028a30e6320b61bfbf943efd08683fed29a7574d33a845289f5d15d`

### Theorem 2.1 · `GenLimit.HallucinationDetection.Results.theorem_2_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language «𝒳» ) ) ) , ( ( ∃ D : ( GenLimit.HallucinationDetection.Detector «𝒳» ) , ( GenLimit.HallucinationDetection.DetectsHallucinations D «𝓛» ) ) ) ↔ ( ( GenLimit.HallucinationDetection.IdentifiableInLimit «𝓛» ) )
```

### Theorem 2.3 · `GenLimit.HallucinationDetection.Results.theorem_2_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language «𝒳» ) ) ) , ( ∃ D : ( GenLimit.HallucinationDetection.NegativeExampleDetector «𝒳» ) , ( GenLimit.HallucinationDetection.DetectsWithNegativeExamples D «𝓛» ) )
```

Grammar regression for P08: 197/197 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P09

SHA-256 of the checked page: `a534af986f65f47e780b42b09e1ee9365bf23ce8f30c3b32dd0e7ec412f5dd2a`

### Theorem 3.3 · `GenLimit.RepresentativeGeneration.Published.theorem_3_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( «𝒜» : ( ℕ → ( Set «𝒳» ) ) ) , ∀ ( α : ℝ ) , ∀ ( _ : ( GenLimit.Generic.UUS «ℋ» ) ) , ∀ ( _ : ( GenLimit.RepresentativeGeneration.IsCountablePartition «𝒜» ) ) , ∀ ( _ : ( 0 < α ) ) , ( ( GenLimit.RepresentativeGeneration.AlphaRepresentativeUniformlyGeneratable «ℋ» «𝒜» α ) ↔ ( GenLimit.RepresentativeGeneration.HasFiniteGroupClosureDimension «ℋ» «𝒜» α ) )
```

### Theorem 3.7 · `GenLimit.RepresentativeGeneration.Published.theorem_3_7`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( «𝒜» : ( ℕ → ( Set «𝒳» ) ) ) , ( ( GenLimit.RepresentativeGeneration.RepresentativelyNonuniformlyGeneratable «ℋ» «𝒜» ) ) ↔ ( ∀ ( α : ℝ ) , ∀ ( _ : ( 0 < α ) ) , ( ∃ classes : ( ℕ → ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ( ( ( Monotone classes ) ∧ ( «ℋ» = ( Set.iUnion ( fun n => ( classes n ) ) ) ) ) ) ∧ ( ( ∀ n : ℕ , ( GenLimit.RepresentativeGeneration.AlphaRepresentativeUniformlyGeneratable ( classes n ) «𝒜» α ) ) ) ) )
```

### Corrected theorem 4.4 · `GenLimit.RepresentativeGeneration.Published.corrected_theorem_4_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ [ Countable «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( «𝒜» : ( ℕ → ( Set «𝒳» ) ) ) , ∀ ( _ : ( Set.Countable «ℋ» ) ) , ∀ ( _ : ( GenLimit.Generic.UUS «ℋ» ) ) , ∀ ( _ : ( ( Set.iUnion ( fun i => ( «𝒜» i ) ) ) = Set.univ ) ) , ∀ ( _ : ( ∀ L ∈ «ℋ» , ( Set.Finite ( GenLimit.RepresentativeGeneration.finiteExactProfilePoints L «𝒜» ) ) ) ) , ( GenLimit.RepresentativeGeneration.RepresentativelyGeneratableInLimit «ℋ» «𝒜» )
```

Grammar regression for P09: 296/296 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P10

SHA-256 of the checked page: `069293f76488f8acfacbe45a8058dc6f87500b4f97f81d87cead3e14dc32b582`

### Theorem 3.1 · `GenLimit.UnionClosedness.theorem_3_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝓛_1» : ( Set ( GenLimit.Generic.Language ℤ ) ) , ∃ «𝓛_2» : ( Set ( GenLimit.Generic.Language ℤ ) ) , ( ( ¬ ( Set.Countable «𝓛_1» ) ) ∧ ( ( GenLimit.Generic.NonuniformlyGeneratable «𝓛_1» ) ∧ ( ( ¬ ( Set.Countable «𝓛_2» ) ) ∧ ( ( GenLimit.Generic.NonuniformlyGeneratable «𝓛_2» ) ∧ ( ¬ ( GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations ( «𝓛_1» ∪ «𝓛_2» ) ) ) ) ) ) ) )
```

### Theorem 3.1 witness uus · `GenLimit.UnionClosedness.theorem_3_1_witness_uus`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( ∀ L ∈ GenLimit.UnionClosedness.finiteNegativeInfinitePositiveClass , ( Set.Infinite L ) ) ) ∧ ( ( ∀ L ∈ GenLimit.UnionClosedness.infiniteNegativeFinitePositiveClass , ( Set.Infinite L ) ) )
```

### Theorem 3.2 witness · `GenLimit.UnionClosedness.theorem_3_2_witness`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( Set.Countable GenLimit.UnionClosedness.theorem43SecondClass ) ∧ ( ( GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput GenLimit.UnionClosedness.theorem43SecondClass ) ∧ ( ( ¬ ( Set.Countable GenLimit.UnionClosedness.theorem43FirstClass ) ) ∧ ( ( GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput GenLimit.UnionClosedness.theorem43FirstClass ) ∧ ( ¬ ( GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations ( GenLimit.UnionClosedness.theorem43SecondClass ∪ GenLimit.UnionClosedness.theorem43FirstClass ) ) ) ) ) ) )
```

### Theorem 3.2 witness standard · `GenLimit.UnionClosedness.theorem_3_2_witness_standard`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( Set.Countable GenLimit.UnionClosedness.theorem43SecondClass ) ∧ ( ( GenLimit.Generic.NonuniformlyGeneratable GenLimit.UnionClosedness.theorem43SecondClass ) ∧ ( ( ¬ ( Set.Countable GenLimit.UnionClosedness.theorem43FirstClass ) ) ∧ ( ( GenLimit.Generic.UniformlyGeneratable GenLimit.UnionClosedness.theorem43FirstClass ) ∧ ( ¬ ( GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations ( GenLimit.UnionClosedness.theorem43SecondClass ∪ GenLimit.UnionClosedness.theorem43FirstClass ) ) ) ) ) ) )
```

### Theorem 3.2 witness uus · `GenLimit.UnionClosedness.theorem_3_2_witness_uus`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( ∀ L ∈ GenLimit.UnionClosedness.theorem43SecondClass , ( Set.Infinite L ) ) ) ∧ ( ( ∀ L ∈ GenLimit.UnionClosedness.theorem43FirstClass , ( Set.Infinite L ) ) )
```

### Theorem 3.2 · `GenLimit.UnionClosedness.theorem_3_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝓛_1» : ( Set ( GenLimit.Generic.Language ℤ ) ) , ∃ «𝓛_2» : ( Set ( GenLimit.Generic.Language ℤ ) ) , ( ( Set.Countable «𝓛_1» ) ∧ ( ( GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput «𝓛_1» ) ∧ ( ( ¬ ( Set.Countable «𝓛_2» ) ) ∧ ( ( GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput «𝓛_2» ) ∧ ( ¬ ( GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations ( «𝓛_1» ∪ «𝓛_2» ) ) ) ) ) ) ) )
```

### Theorem 3.2 standard · `GenLimit.UnionClosedness.theorem_3_2_standard`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝓛_1» : ( Set ( GenLimit.Generic.Language ℤ ) ) , ∃ «𝓛_2» : ( Set ( GenLimit.Generic.Language ℤ ) ) , ( ( Set.Countable «𝓛_1» ) ∧ ( ( GenLimit.Generic.NonuniformlyGeneratable «𝓛_1» ) ∧ ( ( ¬ ( Set.Countable «𝓛_2» ) ) ∧ ( ( GenLimit.Generic.UniformlyGeneratable «𝓛_2» ) ∧ ( ¬ ( GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations ( «𝓛_1» ∪ «𝓛_2» ) ) ) ) ) ) ) )
```

### Theorem 3.3 of theorem 3 1 · `GenLimit.UnionClosedness.theorem_3_3_of_theorem_3_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( ¬ ( GenLimit.LiRamanTewari.EventuallyUnboundedClosure GenLimit.UnionClosedness.finiteNegativeInfinitePositiveClass ) ) ∨ ( ¬ ( GenLimit.LiRamanTewari.EventuallyUnboundedClosure GenLimit.UnionClosedness.infiniteNegativeFinitePositiveClass ) ) )
```

### Theorem 3.3 · `GenLimit.UnionClosedness.theorem_3_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝓛» : ( Set ( GenLimit.Generic.Language ℤ ) ) , ( ( ¬ ( Set.Countable «𝓛» ) ) ∧ ( ( GenLimit.Generic.NonuniformlyGeneratable «𝓛» ) ∧ ( ¬ ( GenLimit.LiRamanTewari.EventuallyUnboundedClosure «𝓛» ) ) ) ) )
```

### Theorem 3.3 witness uus · `GenLimit.UnionClosedness.theorem_3_3_witness_uus`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ L ∈ GenLimit.UnionClosedness.finiteNegativeInfinitePositiveClass , ( Set.Infinite L )
```

Grammar regression for P10: 983/983 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P11

SHA-256 of the checked page: `c021622ef64a25b941a67d19101eeaaac56de98eb9d649d00e7b1ad5b6877336`

### Lemma 9 distinguishability · `GenLimit.LearningAlgorithmsLimit.Results.lemma_9_distinguishability`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Input Obs : Type _ ) , ∀ ( Rep Model : Sort _ ) , ∀ ( Output : Type _ ) , ∀ ( «𝓛» : ( ( Set ( Input × Obs ) ) → Rep ) ) , ∀ ( observe : ( Model → ( Input → Obs ) ) ) , ∀ ( modelSemantics : ( Model → ( Input → ( Option Output ) ) ) ) , ∀ ( representationSemantics : ( Rep → ( Input → ( Option Output ) ) ) ) , ∀ ( I S_m S_n : ( Set Input ) ) , ∀ ( m n : Model ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet «𝓛» observe modelSemantics representationSemantics I m S_m ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet «𝓛» observe modelSemantics representationSemantics I n S_n ) ) , ∀ ( _ : ( ¬ ( ( ∀ x ∈ I , ( ( modelSemantics m x ) = ( modelSemantics n x ) ) ) ) ) ) , ( ∃ x ∈ ( S_m ∪ S_n ) , ( ( observe m x ) ≠ ( observe n x ) ) )
```

### Theorem 12 time Restricted IOO core · `GenLimit.LearningAlgorithmsLimit.Results.theorem_12_timeRestrictedIOO_core`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Output Input : Type _ ) , ∀ [ DecidableEq Output ] , ∀ ( enumeration : ( GenLimit.LearningAlgorithmsLimit.BoundedEnumeration Input Output ) ) , let S := ( GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.semantics enumeration ) ; ∀ ( f : ( Input → ( Option Output ) ) ) , ∀ ( w : ( ℕ → Input ) ) , ∀ ( I : ( Set Input ) ) , ∀ ( _ : ( Set.range w = I ) ) , ∀ ( _ : ( ∃ candidate : ℕ , ( ∀ x_1 ∈ I , ( ( S candidate x_1 ) = ( f x_1 ) ) ) ) ) , ( GenLimit.LearningAlgorithmsLimit.LearnsInLimit ( GenLimit.LearningAlgorithmsLimit.labeledEnumerationLearner S ) ( GenLimit.LearningAlgorithmsLimit.labeledStream f w ) S f I )
```

### Theorem 12 min Index claim not justified · `GenLimit.LearningAlgorithmsLimit.Results.theorem_12_minIndex_claim_not_justified`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( ∃ budget : ℕ , ( ( GenLimit.LearningAlgorithmsLimit.minIndexDiagnosticRun budget 0 () ) = ( Option.some Bool.false ) ) ) ) ∧ ( ( ( ∃ budget : ℕ , ( ( GenLimit.LearningAlgorithmsLimit.minIndexDiagnosticRun budget 1 () ) = ( Option.some Bool.false ) ) ) ) ∧ ( ( ( ( GenLimit.LearningAlgorithmsLimit.minIndexDiagnosticRun 2 0 () ) = Option.none ) ) ∧ ( ( ( GenLimit.LearningAlgorithmsLimit.minIndexDiagnosticRun 2 1 () ) = ( Option.some Bool.false ) ) ) ) )
```

### Corollary 13 parametrized TMClass core · `GenLimit.LearningAlgorithmsLimit.Results.corollary_13_parametrizedTMClass_core`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Output Input : Type _ ) , ∀ [ DecidableEq Output ] , ∀ ( enumeration : ( GenLimit.LearningAlgorithmsLimit.BoundedEnumeration Input Output ) ) , let S := ( GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.semantics enumeration ) ; ∀ ( f : ( Input → ( Option Output ) ) ) , ∀ ( w : ( ℕ → Input ) ) , ∀ ( I : ( Set Input ) ) , ∀ ( _ : ( Set.range w = I ) ) , ∀ ( _ : ( ∃ candidate : ℕ , ( ∀ x_1 ∈ I , ( ( S candidate x_1 ) = ( f x_1 ) ) ) ) ) , ( GenLimit.LearningAlgorithmsLimit.LearnsInLimit ( GenLimit.LearningAlgorithmsLimit.labeledEnumerationLearner S ) ( GenLimit.LearningAlgorithmsLimit.labeledStream f w ) S f I )
```

### Theorem 14 universal TBO core · `GenLimit.LearningAlgorithmsLimit.Results.theorem_14_universalTBO_core`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Output Input : Type _ ) , ∀ [ DecidableEq Output ] , ∀ ( simulate : ( ℕ → ( Input → ( ℕ → ( Option Output ) ) ) ) ) , ∀ ( observation : ( Input → ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation Input Output ) ) ) , ∀ ( w : ( ℕ → Input ) ) , ∀ ( I : ( Set Input ) ) , let N := ( fun candidate => ( ∀ input ∈ I , ( ( simulate candidate input ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation.timeBound ( observation input ) ) ) = ( Option.some ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation.value ( observation input ) ) ) ) ) ) ; ∀ ( _ : ( Set.range w = I ) ) , ∀ ( _ : ( ∀ input ∈ I , ( ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation.input ( observation input ) ) = input ) ) ) , ∀ ( _ : ( ∃ candidate : ℕ , ( N candidate ) ) ) , ( GenLimit.LearningAlgorithmsLimit.LearnsByCriterion ( GenLimit.LearningAlgorithmsLimit.timeObservedLearner simulate ) ( fun n => ( observation ( w n ) ) ) N )
```

### Corollary 15 turing TBO · `GenLimit.LearningAlgorithmsLimit.Results.corollary_15_turingTBO`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Γ Output Input : Type _ ) , ∀ [ Fintype Γ ] , ∀ [ DecidableEq Γ ] , ∀ [ Encodable Γ ] , ∀ [ DecidableEq Output ] , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO Γ Input Output ) ) , ( GenLimit.LearningAlgorithmsLimit.SolvesTuringTBO io ( GenLimit.LearningAlgorithmsLimit.turingTBOLearner io ) )
```

### Theorem 16 recursive To Rational behavior · `GenLimit.LearningAlgorithmsLimit.Results.theorem_16_recursiveToRational_behavior`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( State Tape : Type _ ) , ∀ ( M : ( GenLimit.LearningAlgorithmsLimit.PolicyMachine State Tape ) ) , ∀ ( scanned : ( List Tape ) ) , ( ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.tapeBehavior M scanned ) = ( Prod.snd ( GenLimit.LearningAlgorithmsLimit.Mealy.run ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST M ) scanned ) ) )
```

### Theorem 16 rational Enumeration core · `GenLimit.LearningAlgorithmsLimit.Results.theorem_16_rationalEnumeration_core`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( B State A : Type _ ) , ∀ [ DecidableEq B ] , ∀ ( machines : ( ℕ → ( GenLimit.LearningAlgorithmsLimit.Mealy State A B ) ) ) , ∀ ( targetIndex : ℕ ) , let N := ( GenLimit.LearningAlgorithmsLimit.rationalSemantics ( machines targetIndex ) ) ; ∀ ( w : ( ℕ → ( List A ) ) ) , ∀ ( I : ( Set ( List A ) ) ) , ∀ ( _ : ( Set.range w = I ) ) , ( GenLimit.LearningAlgorithmsLimit.LearnsInLimit ( GenLimit.LearningAlgorithmsLimit.labeledEnumerationLearner ( fun j => ( GenLimit.LearningAlgorithmsLimit.rationalSemantics ( machines j ) ) ) ) ( GenLimit.LearningAlgorithmsLimit.labeledStream N w ) ( fun j => ( GenLimit.LearningAlgorithmsLimit.rationalSemantics ( machines j ) ) ) N I )
```

### Theorem 17 late Split characteristic obstruction · `GenLimit.LearningAlgorithmsLimit.Results.theorem_17_lateSplit_characteristic_obstruction`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ( Set ( ℕ × Bool ) ) → Bool ) ) , ∀ ( splitAt : ℕ ) , let L := ( GenLimit.LearningAlgorithmsLimit.lateSplitObservation splitAt ) ; let N := ( fun branch => ( fun inputLength => ( Option.some ( L branch inputLength ) ) ) ) ; ∀ ( coreFalse coreTrue : ( Set ℕ ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet «𝓛» L N N Set.univ Bool.false coreFalse ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet «𝓛» L N N Set.univ Bool.true coreTrue ) ) , ( ∃ n ∈ ( coreFalse ∪ coreTrue ) , ( splitAt ≤ n ) )
```

### Theorem 17 mass lower bound core · `GenLimit.LearningAlgorithmsLimit.Results.theorem_17_mass_lower_bound_core`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ( Set ( ℕ × Bool ) ) → Bool ) ) , ∀ ( splitAt : ℕ ) , let L := ( GenLimit.LearningAlgorithmsLimit.lateSplitObservation splitAt ) ; let N := ( fun branch => ( fun inputLength => ( Option.some ( L branch inputLength ) ) ) ) ; ∀ ( coreFalse coreTrue : ( Finset ℕ ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet «𝓛» L N N Set.univ Bool.false ( Finset.toSet coreFalse ) ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet «𝓛» L N N Set.univ Bool.true ( Finset.toSet coreTrue ) ) ) , ( ( splitAt + 1 ) ≤ ( ( Finset.sum coreFalse ( fun n => ( n + 1 ) ) ) + ( Finset.sum coreTrue ( fun n => ( n + 1 ) ) ) ) )
```

### Corollary 18 forgetting preserves indistinguishability · `GenLimit.LearningAlgorithmsLimit.Results.corollary_18_forgetting_preserves_indistinguishability`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Model : Sort _ ) , ∀ ( Input : Type _ ) , ∀ ( Rich Poor : Sort _ ) , ∀ ( rich : ( Model → ( Input → Rich ) ) ) , ∀ ( forget : ( Rich → Poor ) ) , ∀ ( m n : Model ) , ∀ ( inputs : ( Set Input ) ) , ∀ ( _ : ( ∀ x ∈ inputs , ( ( rich m x ) = ( rich n x ) ) ) ) , ∀ x ∈ inputs , ( ( forget ( rich m x ) ) = ( forget ( rich n x ) ) )
```

### Corollary 18 characteristic bound lifts to richer observations · `GenLimit.LearningAlgorithmsLimit.Results.corollary_18_characteristic_bound_lifts_to_richer_observations`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Input Poor : Type _ ) , ∀ ( Rep Model : Sort _ ) , ∀ ( Rich Output : Type _ ) , ∀ ( «𝓛» : ( ( Set ( Input × Poor ) ) → Rep ) ) , ∀ ( rich : ( Model → ( Input → Rich ) ) ) , ∀ ( forget : ( Rich → Poor ) ) , ∀ ( modelSemantics : ( Model → ( Input → ( Option Output ) ) ) ) , ∀ ( representationSemantics : ( Rep → ( Input → ( Option Output ) ) ) ) , ∀ ( I : ( Set Input ) ) , ∀ ( mass : ( ( Set Input ) → ℕ ) ) , ∀ ( bound : ( Model → ℕ ) ) , ∀ ( _ : ( ∀ m : Model , ( ∃ S_m : ( Set Input ) , ( ( GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet «𝓛» ( fun model => ( fun input => ( forget ( rich model input ) ) ) ) modelSemantics representationSemantics I m S_m ) ∧ ( ( mass S_m ) ≤ ( bound m ) ) ) ) ) ) , ∀ ( m : Model ) , ( ∃ S_m : ( Set Input ) , ( ( GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet ( GenLimit.LearningAlgorithmsLimit.liftLearnerAlongForget «𝓛» forget ) rich modelSemantics representationSemantics I m S_m ) ∧ ( ( mass S_m ) ≤ ( bound m ) ) ) )
```

### Theorem 21 tagged two step · `GenLimit.LearningAlgorithmsLimit.Results.theorem_21_tagged_two_step`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( State Tape : Type _ ) , ∀ [ DecidableEq State ] , ∀ [ DecidableEq Tape ] , ∀ ( M : ( GenLimit.LearningAlgorithmsLimit.PolicyMachine State Tape ) ) , ∀ ( q : State ) , ∀ ( a : Tape ) , ( ( GenLimit.LearningAlgorithmsLimit.Mealy.runFrom ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST ( GenLimit.LearningAlgorithmsLimit.taggedMachine M ) ) ( Sum.inl q ) [ ( Sum.inl a ) , ( Sum.inr ( q , a ) ) ] ) = ( ( Sum.inl ( Prod.fst ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.step M q a ) ) ) , [ ( GenLimit.LearningAlgorithmsLimit.markerAction ( q , a ) ) , ( GenLimit.LearningAlgorithmsLimit.liftAction ( Prod.snd ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.step M q a ) ) ) ] ) )
```

### Tagged Machine run From · `GenLimit.LearningAlgorithmsLimit.Results.taggedMachine_runFrom`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( State Tape : Type _ ) , ∀ [ DecidableEq State ] , ∀ [ DecidableEq Tape ] , ∀ ( M : ( GenLimit.LearningAlgorithmsLimit.PolicyMachine State Tape ) ) , ∀ ( q : State ) , ∀ ( w : ( List Tape ) ) , ( ( GenLimit.LearningAlgorithmsLimit.Mealy.runFrom ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST ( GenLimit.LearningAlgorithmsLimit.taggedMachine M ) ) ( Sum.inl q ) ( GenLimit.LearningAlgorithmsLimit.taggedScannedFrom M q w ) ) = ( ( Sum.inl ( Prod.fst ( GenLimit.LearningAlgorithmsLimit.Mealy.runFrom ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST M ) q w ) ) ) , ( GenLimit.LearningAlgorithmsLimit.taggedActionsFrom M q w ) ) )
```

### Theorem 21 transition cover core · `GenLimit.LearningAlgorithmsLimit.Results.theorem_21_transition_cover_core`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Transition Sample : Type _ ) , ∀ [ DecidableEq Transition ] , ∀ [ DecidableEq Sample ] , ∀ ( used : ( Finset Transition ) ) , ∀ ( exercises : ( Sample → ( Set Transition ) ) ) , ∀ ( witness : ( Transition → Sample ) ) , let N := ( Finset.image witness used ) ; ∀ ( _ : ( ∀ e ∈ used , ( e ∈ ( exercises ( witness e ) ) ) ) ) , ∀ ( w : ( ℕ → Sample ) ) , ∀ ( I : ( Set Sample ) ) , ∀ ( _ : ( Set.range w = I ) ) , ∀ ( _ : ( ∀ e ∈ used , ( ( witness e ) ∈ I ) ) ) , ( ( ( Finset.card N ) ≤ Finset.card used ) ) ∧ ( ( ∀ e ∈ used , ( ∃ sample ∈ N , ( e ∈ ( exercises sample ) ) ) ) ∧ ( depends_only% [ Transition , Sample , used , exercises , witness , w , I ] ( ∃ t : ℕ , ∀ sample ∈ N , ( ∃ ( n : ℕ ) , n < t ∧ ( ( w n ) = sample ) ) ) ) )
```

### Theorem 21 msm merge order core · `GenLimit.LearningAlgorithmsLimit.Results.theorem_21_msm_merge_order_core`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Candidate Config : Type _ ) , ∀ [ DecidableEq Candidate ] , ∀ ( candidates : ( Config → ( Finset Candidate ) ) ) , ∀ ( score : ( Config → ( Candidate → ℕ ) ) ) , ∀ ( merge : ( Config → ( Candidate → Config ) ) ) , ∀ ( remaining : ( Config → ℕ ) ) , ∀ ( intended : ( Config → ( Candidate → Prop ) ) ) , ∀ ( Sound Complete : ( Config → Prop ) ) , ∀ ( initial : Config ) , ∀ ( _ : ( Sound initial ) ) , ∀ ( _ : ( ∀ config : Config , ( ( Sound config ) → ( ( ¬ ( Complete config ) ) → ( ∃ good ∈ ( candidates config ) , ( ( intended config good ) ∧ ( 2 ≤ ( score config good ) ) ) ) ) ) ) ) , ∀ ( _ : ( ∀ config : Config , ( ( Sound config ) → ( ( ¬ ( Complete config ) ) → ( ∀ bad ∈ ( candidates config ) , ( ( ¬ ( intended config bad ) ) → ( ( score config bad ) ≤ 1 ) ) ) ) ) ) ) , ∀ ( _ : ( ∀ config : Config , ( ∀ choice : Candidate , ( ( Sound config ) → ( ( intended config choice ) → ( Sound ( merge config choice ) ) ) ) ) ) ) , ∀ ( _ : ( ∀ config : Config , ( ( Sound config ) → ( ( Complete config ) → ( ¬ ( ∃ choice : Candidate , ( GenLimit.LearningAlgorithmsLimit.IsMSMChoice candidates score config choice ) ) ) ) ) ) ) , ∀ ( _ : ( ∀ config : Config , ( ∀ choice : Candidate , ( ( GenLimit.LearningAlgorithmsLimit.IsMSMChoice candidates score config choice ) → ( ( remaining ( merge config choice ) ) < ( remaining config ) ) ) ) ) ) , ( ∃ final : Config , ( ( Relation.ReflTransGen ( GenLimit.LearningAlgorithmsLimit.MSMStep candidates score merge ) initial final ) ) ∧ ( ( ( Sound final ) ) ∧ ( ( ( Complete final ) ) ∧ ( ( ¬ ( ∃ choice : Candidate , ( GenLimit.LearningAlgorithmsLimit.IsMSMChoice candidates score final choice ) ) ) ) ) ) )
```

### Theorem 12 · `GenLimit.LearningAlgorithmsLimit.Results.theorem_12`

- The body begins with Setting B; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Γ Y X : Type _ ) , ∀ [ Encodable Γ ] , ∀ [ DecidableEq Y ] , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO Γ X Y ) ) , ∀ ( q Q : ( ℕ → ( ℕ → ℕ ) ) ) , ∀ ( size : ( X → ℕ ) ) , ∀ ( _ : ( ∀ a : ℕ , ( Monotone ( q a ) ) ) ) , ∀ ( M : ( Set ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher X Y ) ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.Quantitative.QECTT io q M ) ) , ∀ m ∈ M , ∀ ( _ : ( ∃ c : ℕ , ( ∃ C : ℕ , ( ∀ x_2 ∈ ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.domain m ) , ( ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.steps m x_2 ) ≤ ( C * ( Q c ( size x_2 ) ) ) ) ) ) ) ) , ∀ ( I : ( Set X ) ) , ∀ ( _ : ( binrel% HasSubset.Subset I ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.domain m ) ) ) , ∀ ( s : ( ℕ → X ) ) , ∀ ( _ : ( Set.range s = I ) ) , ( GenLimit.LearningAlgorithmsLimit.LearnsByCriterion ( GenLimit.LearningAlgorithmsLimit.labeledEnumerationLearner ( GenLimit.LearningAlgorithmsLimit.Quantitative.ioRun io q Q size ) ) ( GenLimit.LearningAlgorithmsLimit.labeledStream ( fun x_2 => ( Option.some ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.value m x_2 ) ) ) s ) ( fun n => ( GenLimit.LearningAlgorithmsLimit.TuringComputesOn io ( GenLimit.LearningAlgorithmsLimit.Quantitative.prog n ) ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.value m ) I ) ) )
```

### Corollary 13 · `GenLimit.LearningAlgorithmsLimit.Results.corollary_13`

- The body begins with Setting B; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Γ Y X : Type _ ) , ∀ [ Encodable Γ ] , ∀ [ DecidableEq Y ] , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO Γ X Y ) ) , ∀ ( Q : ( ℕ → ( ℕ → ℕ ) ) ) , ∀ ( size : ( X → ℕ ) ) , ∀ ( P : ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) ) , ∀ ( domain : ( Set X ) ) , ∀ ( value : ( X → Y ) ) , ∀ ( _ : ( ∃ b : ℕ , ( ∃ c : ℕ , ( ∀ x_2 ∈ domain , ( ( GenLimit.LearningAlgorithmsLimit.TuringProgram.runWithin ( b * ( Q c ( size x_2 ) ) ) io P x_2 ) = ( Option.some ( value x_2 ) ) ) ) ) ) ) , ∀ ( I : ( Set X ) ) , ∀ ( _ : ( binrel% HasSubset.Subset I domain ) ) , ∀ ( s : ( ℕ → X ) ) , ∀ ( _ : ( Set.range s = I ) ) , ( GenLimit.LearningAlgorithmsLimit.LearnsByCriterion ( GenLimit.LearningAlgorithmsLimit.labeledEnumerationLearner ( GenLimit.LearningAlgorithmsLimit.Quantitative.ioRun io ( fun ( x_2 : ℕ ) => ( fun t => t ) ) Q size ) ) ( GenLimit.LearningAlgorithmsLimit.labeledStream ( fun x_2 => ( Option.some ( value x_2 ) ) ) s ) ( fun n => ( GenLimit.LearningAlgorithmsLimit.TuringComputesOn io ( GenLimit.LearningAlgorithmsLimit.Quantitative.prog n ) value I ) ) )
```

### Theorem 14 · `GenLimit.LearningAlgorithmsLimit.Results.theorem_14`

- The body begins with Setting B; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Γ Y X : Type _ ) , ∀ [ Encodable Γ ] , ∀ [ DecidableEq Y ] , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO Γ X Y ) ) , ∀ ( q : ( ℕ → ( ℕ → ℕ ) ) ) , ∀ ( _ : ( ∀ a : ℕ , ( Monotone ( q a ) ) ) ) , ∀ ( M : ( Set ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher X Y ) ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.Quantitative.QECTT io q M ) ) , ∀ m ∈ M , ∀ ( I : ( Set X ) ) , ∀ ( _ : ( binrel% HasSubset.Subset I ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.domain m ) ) ) , ∀ ( obs : ( X → ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation X Y ) ) ) , ∀ ( _ : ( ∀ x_2 ∈ I , ( ( ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation.input ( obs x_2 ) ) = x_2 ) ∧ ( ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation.value ( obs x_2 ) ) = ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.value m x_2 ) ) ) ) ) , ∀ ( _ : ( ∃ b : ℕ , ( ∀ x_2 ∈ I , ( ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.steps m x_2 ) ≤ ( b * ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation.timeBound ( obs x_2 ) ) ) ) ) ) ) , ∀ ( s : ( ℕ → X ) ) , ∀ ( _ : ( Set.range s = I ) ) , ( GenLimit.LearningAlgorithmsLimit.LearnsByCriterion ( GenLimit.LearningAlgorithmsLimit.timeObservedLearner ( GenLimit.LearningAlgorithmsLimit.Quantitative.tbRun io q ) ) ( fun n => ( obs ( s n ) ) ) ( fun n => ( GenLimit.LearningAlgorithmsLimit.TuringComputesOn io ( GenLimit.LearningAlgorithmsLimit.Quantitative.prog n ) ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.value m ) I ) ) )
```

### Theorem 16 · `GenLimit.LearningAlgorithmsLimit.Results.theorem_16`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Γ X Y : Type _ ) , ∀ [ Encodable Γ ] , ∀ [ Fintype Γ ] , ∀ ( R : ( GenLimit.LearningAlgorithmsLimit.Rational.IOAlgorithm Γ ( Γ × GenLimit.LearningAlgorithmsLimit.TuringHeadMove ) ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.Rational.Solves R ) ) , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO Γ X Y ) ) , ∀ ( P : ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) ) , ∀ ( f : ( X → Y ) ) , ∀ ( I : ( Set X ) ) , ∀ ( s : ( ℕ → ( GenLimit.LearningAlgorithmsLimit.Policy.Observation Γ X Y ) ) ) , ∀ ( _ : ( ( Set.range ( fun n => ( GenLimit.LearningAlgorithmsLimit.Policy.Observation.input ( s n ) ) ) ) = I ) ) , ∀ ( _ : ( ∀ n : ℕ , ( ( ( GenLimit.LearningAlgorithmsLimit.Policy.Observation.value ( s n ) ) = ( f ( GenLimit.LearningAlgorithmsLimit.Policy.Observation.input ( s n ) ) ) ) ∧ ( ∃ out : ( GenLimit.LearningAlgorithmsLimit.TuringTape Γ ) , ( ( GenLimit.LearningAlgorithmsLimit.Policy.Execution P ( GenLimit.LearningAlgorithmsLimit.TuringIO.blank io ) 1 ( GenLimit.LearningAlgorithmsLimit.TuringIO.initTape io ( GenLimit.LearningAlgorithmsLimit.Policy.Observation.input ( s n ) ) ) ( GenLimit.LearningAlgorithmsLimit.Policy.Observation.events ( s n ) ) out ) ∧ ( ( GenLimit.LearningAlgorithmsLimit.TuringIO.readOutput io out ) = ( Option.some ( GenLimit.LearningAlgorithmsLimit.Policy.Observation.value ( s n ) ) ) ) ) ) ) ) ) , ( GenLimit.LearningAlgorithmsLimit.LearnsByCriterion ( GenLimit.LearningAlgorithmsLimit.Policy.reducedLearner R ( GenLimit.LearningAlgorithmsLimit.TuringIO.blank io ) ) s ( fun Q => ( GenLimit.LearningAlgorithmsLimit.TuringComputesOn io Q f I ) ) )
```

### Theorem 17 · `GenLimit.LearningAlgorithmsLimit.Results.theorem_17`

- The body begins with Setting C; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Γ «Σ» : Type ) , ∀ [ Inhabited Γ ] , ∀ [ DecidableEq Γ ] , ∀ [ Fintype Γ ] , ∀ [ Primcodable Γ ] , ∀ [ Primcodable «Σ» ] , ∀ [ Finite «Σ» ] , ∀ ( R : Sort _ ) , ∀ ( ι : ( «Σ» ↪ Γ ) ) , ∀ ( _ : ( ∀ a : «Σ» , ( ( DFunLike.coe ι a ) ≠ Inhabited.default ) ) ) , ∀ ( a : «Σ» ) , ∀ ( A : ( ( Set ( ( List «Σ» ) × ( GenLimit.LearningAlgorithmsLimit.NativeTape.WordObservation «Σ» Γ ) ) ) → R ) ) , ∀ ( rep : ( R → ( ( List «Σ» ) → ( Option ( List «Σ» ) ) ) ) ) , ∀ ( β : ( ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) → ℕ ) ) , ∀ ( _ : ( Computable ( fun n => ( β ( GenLimit.LearningAlgorithmsLimit.decodeTuringProgram n ) ) ) ) ) , ∀ ( sideLength : ( ( Unit ⊕ ( ℕ ⊕ ( List ( Γ × ( Γ × GenLimit.LearningAlgorithmsLimit.TuringHeadMove ) ) ) ) ) → ℕ ) ) , let clock := ( fun ( x_5 : ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) ) => ( fun ( x_6 : ( List «Σ» ) ) => 0 ) ) ; let obs := ( GenLimit.LearningAlgorithmsLimit.NativeTape.observed GenLimit.LearningAlgorithmsLimit.NativeTape.Mode.policyTrajectory ι clock ) ; ( ( ¬ ( GenLimit.LearningAlgorithmsLimit.NativeTape.HasMass ι A rep obs ( GenLimit.LearningAlgorithmsLimit.NativeTape.exampleLength GenLimit.LearningAlgorithmsLimit.NativeTape.Mode.policyTrajectory ι clock sideLength ) β ) ) ∧ ( ¬ ( GenLimit.LearningAlgorithmsLimit.NativeTape.HasSelector ι A rep obs ) ) )
```

### Corollary 18 · `GenLimit.LearningAlgorithmsLimit.Results.corollary_18`

- The body begins with Setting C; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Γ «Σ» : Type ) , ∀ [ Inhabited Γ ] , ∀ [ DecidableEq Γ ] , ∀ [ Fintype Γ ] , ∀ [ Primcodable Γ ] , ∀ [ Primcodable «Σ» ] , ∀ [ Finite «Σ» ] , ∀ ( R : Sort _ ) , ∀ ( m : GenLimit.LearningAlgorithmsLimit.NativeTape.Mode ) , ∀ ( ι : ( «Σ» ↪ Γ ) ) , ∀ ( _ : ( ∀ a : «Σ» , ( ( DFunLike.coe ι a ) ≠ Inhabited.default ) ) ) , ∀ ( a : «Σ» ) , ∀ ( clock : ( ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) → ( ( List «Σ» ) → ℕ ) ) ) , ∀ ( A : ( ( Set ( ( List «Σ» ) × ( GenLimit.LearningAlgorithmsLimit.NativeTape.WordObservation «Σ» Γ ) ) ) → R ) ) , ∀ ( rep : ( R → ( ( List «Σ» ) → ( Option ( List «Σ» ) ) ) ) ) , ∀ ( sideLength : ( ( Unit ⊕ ( ℕ ⊕ ( List ( Γ × ( Γ × GenLimit.LearningAlgorithmsLimit.TuringHeadMove ) ) ) ) ) → ℕ ) ) , ( ¬ ( ∃ K : ℕ , ( ∃ d : ℕ , ( GenLimit.LearningAlgorithmsLimit.NativeTape.HasMass ι A rep ( GenLimit.LearningAlgorithmsLimit.NativeTape.observed m ι clock ) ( GenLimit.LearningAlgorithmsLimit.NativeTape.exampleLength m ι clock sideLength ) ( fun P => ( K * ( ( ( Finset.card ( GenLimit.LearningAlgorithmsLimit.Policy.states P ) ) + 1 ) ^ d ) ) ) ) ) ) )
```

### Theorem 21 · `GenLimit.LearningAlgorithmsLimit.Results.theorem_21`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X Y : Type _ ) , ∀ ( Γ : Type ) , ∀ [ Fintype Γ ] , ∀ [ Encodable Γ ] , ∀ [ DecidableEq Γ ] , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO Γ X Y ) ) , ∀ ( f : ( X → Y ) ) , ∀ ( _ : ( ∃ P : ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) , ( GenLimit.LearningAlgorithmsLimit.TuringComputesOn io P f Set.univ ) ) ) , ( ∃ n : ℕ , ∃ T : ( GenLimit.LearningAlgorithmsLimit.TuringProgram ( Γ ⊕ ( ( Fin n ) × ( Γ × ( Fin n ) ) ) ) ) , ( ( GenLimit.LearningAlgorithmsLimit.TuringComputesOn ( GenLimit.LearningAlgorithmsLimit.TaggedTape.liftIO n io ) T f Set.univ ) ) ∧ ( ( ∀ I : ( Set X ) , ( GenLimit.LearningAlgorithmsLimit.MSM.Learning.LearnsWithSamples GenLimit.LearningAlgorithmsLimit.TaggedTape.endpoints ( GenLimit.LearningAlgorithmsLimit.TaggedTape.liftIO n io ) T f I ( ( 2 * ( Finset.card ( GenLimit.LearningAlgorithmsLimit.Policy.states T ) ) ) * ( Fintype.card Γ ) ) ) ) ) )
```

Grammar regression for P11: 2266/2266 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P12

SHA-256 of the checked page: `299623b6c25855722f40fa55de1ad84232940548b4c90283517f73cabc3f1618`

### Theorem 1.1 · `GenLimit.NoiseLossFeedback.Results.theorem_1_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒞_1» : ( Set ( GenLimit.Generic.Language ℕ ) ) , ∃ «𝒞_2» : ( Set ( GenLimit.Generic.Language ℕ ) ) , ( ( ( GenLimit.NoiseLossFeedback.NonuniformlyGeneratableWithoutRepetitions «𝒞_1» ) ∧ ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutSamples «𝒞_1» ) ) ) ∧ ( ( ( ( GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutRepetitions «𝒞_2» ) ∧ ( GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutSamples «𝒞_2» ) ) ) ∧ ( ( ¬ ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutRepetitions ( «𝒞_1» ∪ «𝒞_2» ) ) ) ) ) )
```

### Theorem 1.2 · `GenLimit.NoiseLossFeedback.Results.theorem_1_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒞» : ( Set ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝒞» , ( Set.Infinite L ) ) ) , ( ( ( GenLimit.NoiseLossFeedback.UniformlyNoisilyGeneratable «𝒞» ) ↔ ( GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutSamples «𝒞» ) ) ) ∧ ( ( ( GenLimit.NoiseLossFeedback.NonuniformlyNoisilyGeneratable «𝒞» ) ↔ ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutSamples «𝒞» ) ) )
```

### Theorem 1.3 · `GenLimit.NoiseLossFeedback.Results.theorem_1_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Countable α ] , ∀ ( «𝒞» : ( Set ( GenLimit.Generic.Language α ) ) ) , ( ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutSamples «𝒞» ) ↔ ( GenLimit.NoiseLossFeedback.HasIncreasingInfiniteCoreCover «𝒞» ) )
```

### Theorem 1.4 · `GenLimit.NoiseLossFeedback.Results.theorem_1_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Countable α ] , ∀ ( «𝒞» : ( Set ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝒞» , ( Set.Infinite L ) ) ) , ( ∀ ( G : ( GenLimit.Generic.Generator α ) ) , ∀ ( _ : ( GenLimit.NoiseLossFeedback.IsUniformGenerator G «𝒞» ) ) , ( GenLimit.NoiseLossFeedback.IsUniformInfiniteOmissionGenerator G «𝒞» ) ) ∧ ( ∀ ( G : ( GenLimit.Generic.Generator α ) ) , ∀ ( _ : ( GenLimit.NoiseLossFeedback.IsNonuniformGenerator G «𝒞» ) ) , ( GenLimit.NoiseLossFeedback.IsNonuniformInfiniteOmissionGenerator G «𝒞» ) )
```

### Theorem 1.5 · `GenLimit.NoiseLossFeedback.Results.theorem_1_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( i : ℕ ) , ( ∃ «𝒞» : ( Set ( GenLimit.Generic.Language ℤ ) ) , ( ( ∀ L ∈ «𝒞» , ( Set.Infinite L ) ) ) ∧ ( ( ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithOmissions «𝒞» i ) ) ∧ ( ( ( ¬ ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithOmissions «𝒞» ( i + 1 ) ) ) ) ∧ ( ( ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel «𝒞» i ) ) ∧ ( ( ¬ ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel «𝒞» ( i + 1 ) ) ) ) ) ) ) )
```

### Theorem 1.6 · `GenLimit.NoiseLossFeedback.Results.theorem_1_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒞» : ( Set ( GenLimit.Generic.Language ℤ ) ) , ( ( ∀ i : ℕ , ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel «𝒞» i ) ) ) ∧ ( ( ¬ ( GenLimit.NoiseLossFeedback.NoisilyGeneratableInLimit «𝒞» ) ) ) )
```

### Theorem 1.7 · `GenLimit.NoiseLossFeedback.Results.theorem_1_7`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒞» : ( Set ( GenLimit.Generic.Language ℕ ) ) , ( ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithTotalFeedback «𝒞» ) ) ∧ ( ( ( ¬ ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutRepetitions «𝒞» ) ) ) ∧ ( ( ∀ budget : ℕ , ( ¬ ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithQueries «𝒞» budget ) ) ) ) ) )
```

### Theorem 1.8 · `GenLimit.NoiseLossFeedback.Results.theorem_1_8`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ( GenLimit.NoiseLossFeedback.NonuniformlyIdentifiableWithFeedback «𝒞» )
```

Grammar regression for P12: 788/788 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P13

SHA-256 of the checked page: `164d80032db17834a47670d0c90aac4384014a16fbf402c05bf67e7920213d53`

### Theorem 1 · `GenLimit.ParetoGeneration.Results.theorem_1`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Infinite α ] , ∀ ( «𝒞» : ( ℕ → ( Set α ) ) ) , ∀ ( stage : ℕ ) , ( ∃ «𝒢» : ( GenLimit.Generic.Generator α ) , ∃ t : GenLimit.ParetoGeneration.TimeVector , ( ( GenLimit.ParetoGeneration.AchievesTimeVector «𝒢» «𝒞» t ) ) ∧ ( ( ( ∀ i : ℕ , ( 1 ≤ ( t i ) ) ) ) ∧ ( ( ( ∀ ( i : ℕ ) , i < stage → ( ( t i ) = ( ( GenLimit.ParetoGeneration.ProcedureStage.complexity ( GenLimit.ParetoGeneration.canonicalProcedureStage «𝒞» stage ) i ) + 1 ) ) ) ) ∧ ( ∀ t_1 ∈ ( GenLimit.ParetoGeneration.RealizableTimeVectors «𝒞» ) , ∀ ( _ : ( ∃ ( i : ℕ ) , i < stage ∧ ( ( t_1 i ) < ( t i ) ) ) ) , ( ∃ ( j : ℕ ) , j < stage ∧ ( ( t j ) < ( t_1 j ) ) ) ) ) ) )
```

### Theorem 4 · `GenLimit.ParetoGeneration.Results.theorem_4`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Infinite α ] , ∀ ( «𝒞» : ( ℕ → ( Set α ) ) ) , ∀ ( f : ( ℕ → ℕ ) ) , ∀ ( _ : ( ( Monotone f ) ∧ ( ∀ i : ℕ , ( ∃ t : ℕ , ( i < ( f t ) ) ) ) ) ) , let «t⋆» := ( fun i => ( Max.max ( GenLimit.ParetoGeneration.schedulerEntryTime (hf := by assumption) f i ) ( ( GenLimit.ParetoGeneration.canonicalComplexity «𝒞» i ) + 1 ) ) ) ; ( ( GenLimit.ParetoGeneration.AchievesTimeVector ( GenLimit.ParetoGeneration.schedulerGenerator «𝒞» f ) «𝒞» «t⋆» ) ) ∧ ( ( ∀ i : ℕ , ( 1 ≤ ( «t⋆» i ) ) ) )
```

### Theorem 5 · `GenLimit.ParetoGeneration.Results.theorem_5`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Infinite α ] , ∀ ( «𝒞» : ( ℕ → ( Set α ) ) ) , let «m⋆» := ( GenLimit.ParetoGeneration.canonicalComplexity «𝒞» ) ; ∀ ( _ : ( ∀ t : ℕ , ( Set.Finite { i : ℕ | ( ( ( «m⋆» i ) + 1 ) ≤ t ) } ) ) ) , ( ∃ «𝒢» : ( GenLimit.Generic.Generator α ) , ( ( GenLimit.ParetoGeneration.AchievesTimeVector «𝒢» «𝒞» ( fun i => ( ( «m⋆» i ) + 1 ) ) ) ) ∧ ( ( ( ∀ i : ℕ , ( 1 ≤ ( ( «m⋆» i ) + 1 ) ) ) ) ∧ ( ( GenLimit.ParetoGeneration.ParetoOptimal ( GenLimit.ParetoGeneration.RealizableTimeVectors «𝒞» ) ( fun i => ( ( «m⋆» i ) + 1 ) ) ) ) ) )
```

### Theorem 6 · `GenLimit.ParetoGeneration.Results.theorem_6`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Infinite α ] , ∀ ( «𝒞» : ( ℕ → ( Set α ) ) ) , ∀ ( noise f : ( ℕ → ℕ ) ) , ∀ ( _ : ( ( Monotone f ) ∧ ( ∀ i : ℕ , ( ∃ t : ℕ , ( i < ( f t ) ) ) ) ) ) , let «t⋆» := ( fun coordinate => ( Max.max ( GenLimit.ParetoGeneration.schedulerEntryTime (hf := by assumption) f coordinate ) ( ( GenLimit.ParetoGeneration.canonicalNoisyComplexity «𝒞» noise coordinate ) + 1 ) ) ) ; ( ( GenLimit.ParetoGeneration.AchievesNoisyTimeVector ( GenLimit.ParetoGeneration.noisySchedulerGenerator «𝒞» noise f ) «𝒞» noise «t⋆» ) ) ∧ ( ( ∀ i : ℕ , ( 1 ≤ ( «t⋆» i ) ) ) )
```

### Theorem 8 · `GenLimit.ParetoGeneration.Results.theorem_8`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Infinite α ] , ∀ ( «𝒞» : ( ℕ → ( Set α ) ) ) , ∀ ( noise : ( ℕ → ℕ ) ) , let N := ( GenLimit.ParetoGeneration.NoisyRealizableTimeVectors «𝒞» noise ) ; let «m⋆» := ( GenLimit.ParetoGeneration.canonicalNoisyComplexity «𝒞» noise ) ; let «t⋆» := ( fun i => ( ( «m⋆» i ) + 1 ) ) ; ∀ ( _ : ( ∀ t : ℕ , ( Set.Finite { i : ℕ | ( ( ( «m⋆» i ) + 1 ) ≤ t ) } ) ) ) , ( ( «t⋆» ∈ N ) ∧ ( GenLimit.ParetoGeneration.ParetoOptimal N «t⋆» ) )
```

### Theorem 7 · `GenLimit.ParetoGeneration.Results.theorem_7`

- The body begins with Setting B; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ DecidableEq α ] , ∀ ( k : ℕ ) , ∀ [ Nonempty α ] , ∀ ( «𝒞» : ( ℕ → ( Set α ) ) ) , ∀ ( groups : ( ( Fin k ) → ( Set α ) ) ) , let E := ( GenLimit.RepresentativeGeneration.extendFinitePartition groups ) ; ∀ ( _ : ( GenLimit.RepresentativeGeneration.IsFinitePartition groups ) ) , ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( f : ( ℕ → ℕ ) ) , ∀ ( _ : ( ( Monotone f ) ∧ ( ∀ i : ℕ , ( ∃ t : ℕ , ( i < ( f t ) ) ) ) ) ) , ( ( fun i => ( Max.max ( GenLimit.ParetoGeneration.schedulerEntryTime (hf := by assumption) f i ) ( ( GenLimit.ParetoGeneration.Representative.complexity «𝒞» E ε i ) + 1 ) ) ) ∈ ( GenLimit.ParetoGeneration.Representative.Realizable «𝒞» E ε ) )
```

### Theorem 9 · `GenLimit.ParetoGeneration.Results.theorem_9`

- The body begins with Setting B; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ DecidableEq α ] , ∀ ( k : ℕ ) , ∀ [ Nonempty α ] , ∀ ( «𝒞» : ( ℕ → ( Set α ) ) ) , ∀ ( groups : ( ( Fin k ) → ( Set α ) ) ) , let E := ( GenLimit.RepresentativeGeneration.extendFinitePartition groups ) ; ∀ ( _ : ( GenLimit.RepresentativeGeneration.IsFinitePartition groups ) ) , ∀ ( ε : ℝ ) , let R := ( GenLimit.ParetoGeneration.Representative.Realizable «𝒞» E ε ) ; let «m⋆» := ( GenLimit.ParetoGeneration.Representative.complexity «𝒞» E ε ) ; let «t⋆» := ( fun i => ( ( «m⋆» i ) + 1 ) ) ; ∀ ( _ : ( 0 < ε ) ) , ∀ ( _ : ( ∀ t : ℕ , ( Set.Finite { i : ℕ | ( ( ( «m⋆» i ) + 1 ) ≤ t ) } ) ) ) , ( ( «t⋆» ∈ R ) ∧ ( GenLimit.ParetoGeneration.ParetoOptimal R «t⋆» ) )
```

Grammar regression for P13: 698/698 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P14

SHA-256 of the checked page: `0c5e83025949b42e821162b6c9bb33bea5eabc1ac1a2430a1456e9e5af30d51f`

### Theorem 1 · `GenLimit.ListIdentification.Results.theorem_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ DecidableEq α ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( ∃ x : ( ℕ → α ) , ( Set.range x = ( «𝒞» i ) ) ) ) ) , ∀ ( k : ℕ ) , ( ( GenLimit.ListIdentification.ListIdentifiable «𝒞» k ) ↔ ( GenLimit.ListIdentification.KAngluinCondition «𝒞» k ) )
```

### Theorem 2 · `GenLimit.ListIdentification.Results.theorem_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ DecidableEq α ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( ∃ x : ( ℕ → α ) , ( Set.range x = ( «𝒞» i ) ) ) ) ) , ∀ ( k : ℕ ) , ( ( GenLimit.ListIdentification.ListIdentifiable «𝒞» k ) ↔ ( GenLimit.ListIdentification.HasAngluinStratification «𝒞» k ) )
```

### Theorem 3 · `GenLimit.ListIdentification.Results.theorem_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Countable α ] , ∀ [ DecidableEq α ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( k : ℕ ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Nonempty ( «𝒞» i ) ) ) ) , ( ∀ ( _ : ( GenLimit.ListIdentification.ListIdentifiable «𝒞» k ) ) , ( ∃ «𝒜» : ( GenLimit.ListIdentification.Statistical.Kernel α k ) , ( GenLimit.ListIdentification.Statistical.Exponential «𝒞» «𝒜» ) ) ) ∧ ( ( ∀ ( _ : ( GenLimit.ListIdentification.Statistical.NontrivialFor «𝒞» k ) ) , ∀ ( «𝒜» : ( GenLimit.ListIdentification.Statistical.Kernel α k ) ) , ( ∃ i : ℕ , ∃ p : ( PMF α ) , ( ( ( PMF.support p ) = ( «𝒞» i ) ) ∧ ( ∃ᶠ ( t : ℕ ) in Filter.atTop , ( ( Real.exp ( ( - 2 ) * ( ↑ t ) ) ) ≤ ( GenLimit.ListIdentification.Statistical.error «𝒞» «𝒜» p ( «𝒞» i ) t ) ) ) ) ) ) ∧ ( ∀ ( _ : ( ¬ ( GenLimit.ListIdentification.ListIdentifiable «𝒞» k ) ) ) , ∀ ( «𝒜» : ( GenLimit.ListIdentification.Statistical.Kernel α k ) ) , ( ∃ i : ℕ , ∃ p : ( PMF α ) , ( ( ( PMF.support p ) = ( «𝒞» i ) ) ∧ ( ∃ᶠ ( t : ℕ ) in Filter.atTop , ( ( 1 / ( ( ↑ k ) + 2 ) ) < ( GenLimit.ListIdentification.Statistical.error «𝒞» «𝒜» p ( «𝒞» i ) t ) ) ) ) ) ) )
```

### Theorem 9 · `GenLimit.ListIdentification.Results.theorem_9`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( k : ℕ ) , ∀ ( p : ℝ ) , ∀ ( _ : ( p ≤ 1 ) ) , ( ∀ ( _ : ( GenLimit.ListIdentification.ListIdentifiable «𝒞» k ) ) , ( GenLimit.ListIdentification.Probabilistic.Identifies «𝒞» k p ) ) ∧ ( ∀ ( _ : ( ( ( ↑ k ) / ( ( ↑ k ) + 1 ) ) < p ) ) , ∀ ( _ : ( GenLimit.ListIdentification.Probabilistic.Identifies «𝒞» k p ) ) , ( GenLimit.ListIdentification.ListIdentifiable «𝒞» k ) )
```

### Theorem 10 · `GenLimit.ListIdentification.Results.theorem_10`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ MeasurableSpace α ] , ∀ [ Countable α ] , ∀ [ MeasurableSingletonClass α ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( k : ℕ ) , ∀ ( p : ℝ ) , ∀ ( _ : ( p ≤ 1 ) ) , ( ( GenLimit.ListIdentification.InfiniteDraws.Identifies «𝒞» k p ) ↔ ( GenLimit.ListIdentification.Probabilistic.Identifies «𝒞» k p ) )
```

Grammar regression for P14: 497/497 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P15

SHA-256 of the checked page: `a3ea5e8aa132c73754d8e765489cd4648764f43e3ebb3a5b8396e060d5416460`

### Theorem 1.3 · `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) , ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range s = ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid s ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.generate O s ) ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ) ∧ ( ( 1 / 2 ) ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( O z ) ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.generate O s ) ) ) ) )
```

### Theorem 1.5 · `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_5`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( ℕ → GenLimit.Language ) ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( E : GenLimit.Language ) , ∀ ( z : ℕ ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( C i ) ) ) ) , ∀ ( _ : ( Set.range x = E ) ) , ∀ ( _ : ( Set.Infinite E ) ) , ∀ ( _ : ( binrel% HasSubset.Subset E ( C z ) ) ) , ( GenLimit.KleinbergWei.PartialEnumeration.GeneratesFromPartialEnumeration C x z )
```

### Theorem 1.6 · `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_6`

- The body begins with Setting B; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , let M := ( GenLimit.Bridge.Paper39ToPaper15.orderedClosure O ) ; ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) , ∀ ( z : ℕ ) , ∀ ( E : GenLimit.Language ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range s = E ) ) , ∀ ( _ : ( Set.Infinite E ) ) , ∀ ( _ : ( binrel% HasSubset.Subset E ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ) ) , ∀ ( α : ℝ ) , ∀ ( _ : ( α ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( O z ) E ) ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid s ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.generate M s ) ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ) ∧ ( ( α / 2 ) ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( O z ) ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.generate M s ) ) ) ) )
```

### Theorem 1.7 · `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_7`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( ℕ → GenLimit.Language ) ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( E : GenLimit.Language ) , ∀ ( z : ℕ ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( C i ) ) ) ) , ∀ ( _ : ( Set.range x = E ) ) , ∀ ( _ : ( Set.Infinite E ) ) , ∀ ( _ : ( binrel% HasSubset.Subset E ( C z ) ) ) , ( GenLimit.KleinbergWei.PartialEnumeration.SemiIndexGenerates C x z )
```

### Theorem 1.8 · `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_8`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( ℕ → GenLimit.Language ) ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( E : GenLimit.Language ) , ∀ ( z : ℕ ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( C i ) ) ) ) , ∀ ( _ : ( Set.range x = E ) ) , ∀ ( _ : ( Set.Infinite E ) ) , ∀ ( _ : ( binrel% HasSubset.Subset E ( C z ) ) ) , ( ( GenLimit.KleinbergWei.PartialEnumeration.SemiIndexTraceGenerates C ( GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices C x ) z ) ) ∧ ( ∀ ( T : ℕ ) , ( ∃ t : ℕ , ( ( T ≤ t ) ∧ ( binrel% HasSubset.Subset E ( GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C ( GenLimit.KleinbergWei.PartialEnumeration.algorithmOneIndices C x t ) ) ) ) ) )
```

### Theorem 1.9 · `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_9`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( Set GenLimit.Language ) ) , ∀ ( _ : ( ∀ L ∈ «𝒳» , ( Set.Nonempty L ) ) ) , ( ( GenLimit.KleinbergWei.PartialEnumeration.FullTopology.IdentifiableOnFullTexts «𝒳» ) ) ↔ ( ( ( Set.Countable «𝒳» ) ∧ ( GenLimit.KleinbergWei.PartialEnumeration.FullTopology.TDSpace «𝒳» ) ) )
```

### Theorem 1.10 counterexample · `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_10_counterexample`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ¬ ( ( ( GenLimit.KleinbergWei.PartialEnumeration.PartialIdentifiable GenLimit.KleinbergWei.PartialEnumeration.PartialTopology.coSingleClass ) ↔ ( ∀ L ∈ GenLimit.KleinbergWei.PartialEnumeration.PartialTopology.coSingleClass , ( ∀ C : GenLimit.Language , ( ( Set.Infinite C ) → ( ( binrel% HasSubset.Subset C L ) → ( GenLimit.KleinbergWei.PartialEnumeration.PartialTopology.QuotientTD GenLimit.KleinbergWei.PartialEnumeration.PartialTopology.coSingleClass C ) ) ) ) ) ) ) )
```

### Theorem 1.11 · `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_1_11`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( Set GenLimit.Language ) ) , ∀ ( W : ( Finset ℕ ) ) , ( ( GenLimit.KleinbergWei.PartialEnumeration.PartialIdentifiable «𝒳» ) ↔ ( GenLimit.KleinbergWei.PartialEnumeration.PartialIdentifiable ( GenLimit.KleinbergWei.PartialEnumeration.deleteWords W «𝒳» ) ) )
```

### Theorem 3.3 · `GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_3_3`

- The body begins with Setting B; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , let M := ( GenLimit.Bridge.Paper39ToPaper15.orderedClosure O ) ; ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) , ∀ ( z : ℕ ) , ∀ ( E : GenLimit.Language ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range s = E ) ) , ∀ ( _ : ( Set.Infinite E ) ) , ∀ ( _ : ( binrel% HasSubset.Subset E ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ) ) , ∀ ( α : ℝ ) , ∀ ( _ : ( α ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( O z ) E ) ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid s ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.generate M s ) ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( O z ) ) ) ∧ ( ( α / 2 ) ≤ ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity ( O z ) ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.generate M s ) ) ) ) )
```

Grammar regression for P15: 887/887 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P16

SHA-256 of the checked page: `0910ffcef3e0e14a137808fb8f30f8effb923949c5b3dde6596591e9d5660f9b`

### Theorem 3.1 · `GenLimit.ComplexityBarriers.Results.theorem_3_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ¬ ( ∃ A : ( PFun ( GenLimit.ComplexityBarriers.CFG.Description × GenLimit.ComplexityBarriers.CFG.Description ) ℕ ) , ( ( Partrec A ) ∧ ( ∀ ( G_1 G_2 : GenLimit.ComplexityBarriers.CFG.Description ) , ( ( Set.Infinite ( GenLimit.ComplexityBarriers.CFG.language G_1 ) ) → ( ( Set.Infinite ( GenLimit.ComplexityBarriers.CFG.language G_2 ) ) → ( ∃ m ∈ ( A ( G_1 , G_2 ) ) , ( GenLimit.ComplexityBarriers.MGeneratable ( Insert.insert ( GenLimit.ComplexityBarriers.CFG.language G_1 ) ( Singleton.singleton ( GenLimit.ComplexityBarriers.CFG.language G_2 ) ) ) m ) ) ) ) ) ) ) )
```

### Theorem 4.1 · `GenLimit.ComplexityBarriers.Results.theorem_4_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∀ ( «Σ» : Type ) , ∀ [ Fintype «Σ» ] , ∀ ( _ : ( 2 ≤ ( Fintype.card «Σ» ) ) ) , ∀ ( «ℱ» : ( Finset ( Set ( List «Σ» ) ) ) ) , ∀ ( s : ℕ ) , ∀ ( _ : ( ∀ L ∈ «ℱ» , ( Set.Infinite L ) ) ) , ∀ ( _ : ( ( ∀ L ∈ «ℱ» , ( GenLimit.ComplexityBarriers.Automata.NFAAtMost s L ) ) ∨ ( ∀ L ∈ «ℱ» , ( ∃ r : ( RegularExpression «Σ» ) , ( ( ( RegularExpression.matches' r ) = L ) ∧ ( ( GenLimit.ComplexityBarriers.Automata.writtenSize r ) ≤ ( s - 1 ) ) ) ) ) ) ) , ( GenLimit.ComplexityBarriers.MGeneratable ( Finset.toSet «ℱ» ) ( ( Fintype.card «Σ» ) ^ ( s ^ ( Finset.card «ℱ» ) ) ) ) ) ∧ ( ( ∃ k : ℕ , ∀ ( «ℓ» n : ℕ ) , ∀ ( _ : ( 0 < «ℓ» ) ) , ∀ ( _ : ( 0 < n ) ) , ( ∃ «ℱ» : ( Finset ( Set ( List Bool ) ) ) , ( ( ( Finset.card «ℱ» ) = ( 2 ^ «ℓ» ) ) ) ∧ ( ( ∀ L ∈ «ℱ» , ( ( Set.Infinite L ) ) ∧ ( ( ( GenLimit.ComplexityBarriers.Blocks.DFAAtMost ( ( k * «ℓ» ) * n ) L ) ) ∧ ( ( ∃ r : ( RegularExpression Bool ) , ( ( ( RegularExpression.matches' r ) = L ) ∧ ( ( GenLimit.ComplexityBarriers.Automata.writtenSize r ) ≤ ( ( k * ( «ℓ» ^ 2 ) ) * ( n ^ 2 ) ) ) ) ) ) ) ) ∧ ( ( ¬ ( GenLimit.ComplexityBarriers.MGeneratable ( Finset.toSet «ℱ» ) ( 2 ^ ( n ^ ( Finset.card «ℱ» ) ) ) ) ) ) ) ) ) )
```

### Theorem 5.1 · `GenLimit.ComplexityBarriers.Results.theorem_5_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∀ ( «Σ» : Type ) , ∀ [ Fintype «Σ» ] , ∀ ( _ : ( 2 ≤ ( Fintype.card «Σ» ) ) ) , ∀ ( «ℱ» : ( Finset ( Set ( List «Σ» ) ) ) ) , ∀ ( s : ℕ ) , ∀ ( _ : ( ∀ L ∈ «ℱ» , ( Set.Infinite L ) ) ) , ∀ ( _ : ( ∀ L ∈ «ℱ» , ( GenLimit.ComplexityBarriers.LTT.LTTAtMost s L ) ) ) , ( GenLimit.ComplexityBarriers.MGeneratable ( Finset.toSet «ℱ» ) ( ( Fintype.card «Σ» ) ^ ( ( 3 * ( s * ( Finset.card «ℱ» ) ) ) * ( ( ( ( s * ( Finset.card «ℱ» ) ) ^ 2 ) + 1 ) ^ 2 ) ) ) ) ) ∧ ( ∀ ( n : ℕ ) , ∀ ( _ : 4 ≤ n ) , ( ∃ P : ( GenLimit.ComplexityBarriers.LTT.Profile ( Fin n ) ) , ∃ Q : ( GenLimit.ComplexityBarriers.LTT.Profile ( Fin n ) ) , let K := ( GenLimit.ComplexityBarriers.LTT.Profile.language P ) ; let M := ( GenLimit.ComplexityBarriers.LTT.Profile.language Q ) ; ( ( ( GenLimit.ComplexityBarriers.LTT.Profile.size P ) ≤ ( 7 * ( n + 1 ) ) ) ) ∧ ( ( ( ( GenLimit.ComplexityBarriers.LTT.Profile.size Q ) ≤ ( 7 * ( n + 1 ) ) ) ) ∧ ( ( ( Set.Infinite K ) ) ∧ ( ( ( Set.Infinite M ) ) ∧ ( ( ( K ≠ M ) ) ∧ ( ( ¬ ( GenLimit.ComplexityBarriers.MGeneratable ( Insert.insert K ( Singleton.singleton M ) ) ( 2 ^ n ) ) ) ) ) ) ) ) ) )
```

### Theorem 6.1 · `GenLimit.ComplexityBarriers.Results.theorem_6_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( n : ℕ ) , ( ( ∃ p_1 : GenLimit.ComplexityBarriers.Patterns.Pattern , ∃ p_2 : GenLimit.ComplexityBarriers.Patterns.Pattern , let K := ( GenLimit.ComplexityBarriers.Patterns.language p_1 ) ; let M := ( GenLimit.ComplexityBarriers.Patterns.language p_2 ) ; ( ( ( List.length p_1 ) = ( 44 * n ) ) ) ∧ ( ( ( ( List.length p_2 ) = 2 ) ) ∧ ( ( ( Set.Infinite K ) ) ∧ ( ( ( Set.Infinite M ) ) ∧ ( ( ( K ≠ M ) ) ∧ ( ( ¬ ( GenLimit.ComplexityBarriers.MGeneratable ( Insert.insert K ( Singleton.singleton M ) ) ( 2 ^ n ) ) ) ) ) ) ) ) ) ) ↔ ( ( 0 < n ) )
```

Grammar regression for P16: 398/398 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P17

SHA-256 of the checked page: `788955e3a2724251abc1706299c8dd841b982df5e3c8b8e8d62e719e9b263951`

### Corollary 4.5 · `GenLimit.InfiniteContamination.Results.corollary_4_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : GenLimit.OracleFamily ) , let G := ( GenLimit.HallucinationModeCollapse.generationOracle ( GenLimit.InfiniteContamination.membershipExpansion «𝓛» ) ) ; ( ∃ ( h : ( GenLimit.Support.OracleSearchProgram.Terminates GenLimit.InfiniteContamination.boundedMembershipProgram G ) ) , let run := ( GenLimit.Support.OracleSearchProgram.run (h := by assumption) GenLimit.InfiniteContamination.boundedMembershipProgram G ) ; ( ∀ ( z : ℕ ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration x ( «𝓛».language z ) ) ) , ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn ( GenLimit.InfiniteContamination.replayGenerator run ) ( «𝓛».language z ) x ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query «𝓛» ) ) ) , ( Computable ( GenLimit.InfiniteContamination.membershipReplay run ) ) ) )
```

### Theorem 5.1 · `GenLimit.InfiniteContamination.Results.theorem_5_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language U ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝓛» i ) ) ) ) , depends_only% [ U , «𝓛» ] ( ∃ «𝔾» : ( GenLimit.Generic.Generator U ) , ∀ ( target : ℕ ) , ∀ ( x : ( ℕ → U ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.VanishingNoiseArbitraryOmissionEnumeration x ( «𝓛» target ) ) ) , ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» ( «𝓛» target ) x ) )
```

### Theorem 5.4 · `GenLimit.InfiniteContamination.Results.theorem_5_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ ( «𝓛» : ( Set ( GenLimit.Generic.Language U ) ) ) , ∀ ( c : ℝ ) , ∀ ( _ : ( 0 < c ) ) , ∀ ( _ : ( c < 1 ) ) , ∀ ( family : ( ℕ → ( GenLimit.Generic.Language U ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( family i ) ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( ( family i ) ∈ «𝓛» ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝓛» , ( ∃ i : ℕ , ( ( family i ) = L ) ) ) ) , ( depends_only% [ U , «𝓛» , c , family ] ( ∃ «𝔾» : ( GenLimit.Generic.Generator U ) , ∀ L ∈ «𝓛» , ∀ ( x : ( ℕ → U ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.ConstantNoiseArbitraryOmissionEnumeration x L c ) ) , ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» L x ) ) ) ↔ ( ( GenLimit.InfiniteContamination.ConstantNoiseGenerationProperty «𝓛» c ) )
```

### Theorem 6.1 · `GenLimit.InfiniteContamination.Results.theorem_6_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : GenLimit.OracleFamily ) , let F := ( GenLimit.InfiniteContamination.finiteExpansionOracleFamily «𝓛» ) ; let N := ( GenLimit.InfiniteContamination.algorithmFiveGenerator ( GenLimit.OracleFamily.language F ) ) ; ∀ ( orders : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( ∀ i : ℕ , ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( orders i ) ) = ( «𝓛».language i ) ) ) ) , ∀ ( z : ℕ ) , let K := ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( orders z ) ) ; ∀ ( c : ℝ ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.FiniteNoise x ( «𝓛».language z ) ) ) , ∀ ( _ : ( ( 1 - c ) ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( orders z ) ( ( Set.range x ) ∩ K ) ) ) ) , ( ( ( GenLimit.InfiniteContamination.IsInfiniteSetGenerator N ) ∧ ( GenLimit.InfiniteContamination.GeneratesSetInLimitOn N K x ) ) ) ∧ ( ( ( 1 - c ) ≤ ( GenLimit.InfiniteContamination.setBasedUpperDensity N ( orders z ) x ) ) )
```

### Theorem 6.4 · `GenLimit.InfiniteContamination.Results.theorem_6_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( c : ℝ ) , ∀ ( _ : ( 0 < c ) ) , ∀ ( _ : ( c < 1 ) ) , ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( «𝔾» : ( GenLimit.InfiniteContamination.SetGenerator ℕ ) ) , ( ¬ ( GenLimit.InfiniteContamination.GuaranteesSetBasedUpperDensityUnderOmissionsOn «𝔾» ( GenLimit.InfiniteContamination.theoremSixFourFamily ( 1 - c ) ) ( GenLimit.InfiniteContamination.theoremSixFourOrders (hp := by first | assumption | linarith | positivity | simp_all +zetaDelta) (hp1 := by first | assumption | linarith | positivity | simp_all +zetaDelta) ( 1 - c ) ) c ( ( 1 - c ) + ε ) ) )
```

### Theorem 6.5 · `GenLimit.InfiniteContamination.Results.theorem_6_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : GenLimit.OracleFamily ) , ∀ ( orders : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( ∀ i : ℕ , ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( orders i ) ) = ( «𝓛».language i ) ) ) ) , ∀ ( c : ℝ ) , ( ( ∃ «𝔾» : ( GenLimit.InfiniteContamination.SetGenerator ℕ ) , ( ( GenLimit.InfiniteContamination.IsInfiniteSetGenerator «𝔾» ) ) ∧ ( ∀ ( z : ℕ ) , let K := ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( orders z ) ) ; ( ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration x K ) ) , ( GenLimit.InfiniteContamination.GeneratesSetInLimitOn «𝔾» K x ) ) ∧ ( ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration x K ) ) , ( c ≤ ( GenLimit.InfiniteContamination.setBasedLowerDensity «𝔾» ( orders z ) x ) ) ) ) ) ) ↔ ( ∀ ( i j : ℕ ) , ∀ ( _ : ( Set.Finite ( ( «𝓛».language i ) \ ( «𝓛».language j ) ) ) ) , ( c ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( orders j ) ( «𝓛».language i ) ) ) )
```

### Theorem 6.11 · `GenLimit.InfiniteContamination.Results.theorem_6_11`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝓛» i ) ) ) ) , ∀ ( orders : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( ∀ i : ℕ , ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( orders i ) ) = ( «𝓛» i ) ) ) ) , ∀ ( ρ : ℝ ) , ( ( ∃ «𝔾» : ( GenLimit.InfiniteContamination.SetGenerator ℕ ) , ( ( GenLimit.InfiniteContamination.IsInfiniteSetGenerator «𝔾» ) ) ∧ ( ∀ ( target : ℕ ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.VanishingNoiseArbitraryOmissionEnumeration x ( «𝓛» target ) ) ) , ( ( GenLimit.InfiniteContamination.GeneratesSetInLimitOn «𝔾» ( «𝓛» target ) x ) ∧ ( ρ ≤ ( GenLimit.InfiniteContamination.setBasedLowerDensity «𝔾» ( orders target ) x ) ) ) ) ) ) ↔ ( ( GenLimit.InfiniteContamination.VanishingNoiseDenseSetCondition «𝓛» orders ρ ) )
```

### Theorem 6.14 including one · `GenLimit.InfiniteContamination.Results.theorem_6_14_including_one`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝓛» i ) ) ) ) , ∀ ( orders : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( ∀ i : ℕ , ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( orders i ) ) = ( «𝓛» i ) ) ) ) , ∀ ( c ρ : ℝ ) , ∀ ( _ : ( 0 < c ) ) , ∀ ( _ : ( c ≤ 1 ) ) , ∀ ( _ : ( 0 < ρ ) ) , ( ( ∃ «𝔾» : ( GenLimit.InfiniteContamination.SetGenerator ℕ ) , ( ( GenLimit.InfiniteContamination.IsInfiniteSetGenerator «𝔾» ) ) ∧ ( ∀ ( target : ℕ ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.ConstantNoiseArbitraryOmissionEnumeration x ( «𝓛» target ) c ) ) , ( ( GenLimit.InfiniteContamination.GeneratesSetInLimitOn «𝔾» ( «𝓛» target ) x ) ∧ ( ρ ≤ ( GenLimit.InfiniteContamination.setBasedLowerDensity «𝔾» ( orders target ) x ) ) ) ) ) ) ↔ ( ( GenLimit.InfiniteContamination.ConstantNoiseDenseSetCondition «𝓛» orders c ρ ) )
```

### Theorem 6.18 · `GenLimit.InfiniteContamination.Results.theorem_6_18`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : GenLimit.OracleFamily ) , let F := ( GenLimit.InfiniteContamination.finiteExpansionOracleFamily «𝓛» ) ; ∀ ( «𝔾» : ( GenLimit.Generic.Generator ℕ ) ) , ∀ ( ρ_low ρ_up : ℝ ) , ∀ ( _ : ( ∀ j : ℕ , ( ∀ x : ( ℕ → ℕ ) , ( ( Set.range x = ( F.language j ) ) → ( ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» ( F.language j ) x ) ∧ ( ( ρ_low ≤ ( GenLimit.InfiniteContamination.elementBasedLowerDensity «𝔾» ( GenLimit.InfiniteContamination.canonicalFamilyOrders F j ) x ) ) ∧ ( ρ_up ≤ ( GenLimit.InfiniteContamination.elementBasedUpperDensity «𝔾» ( GenLimit.InfiniteContamination.canonicalFamilyOrders F j ) x ) ) ) ) ) ) ) ) , ∀ ( z : ℕ ) , let N := ( GenLimit.InfiniteContamination.canonicalFamilyOrders «𝓛» z ) ; ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration x ( «𝓛».language z ) ) ) , ( ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» ( «𝓛».language z ) x ) ) ∧ ( ( ( ρ_low ≤ ( GenLimit.InfiniteContamination.elementBasedLowerDensity «𝔾» N x ) ) ) ∧ ( ( ρ_up ≤ ( GenLimit.InfiniteContamination.elementBasedUpperDensity «𝔾» N x ) ) ) )
```

### Theorem 6.19 · `GenLimit.InfiniteContamination.Results.theorem_6_19`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : GenLimit.OracleFamily ) , depends_only% [ «𝓛» ] ( ∃ «𝔾» : ( GenLimit.Generic.Generator ℕ ) , ∀ ( j : ℕ ) , let N := ( GenLimit.InfiniteContamination.canonicalFamilyOrders «𝓛» j ) ; ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range x = ( «𝓛».language j ) ) ) , ( ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» ( «𝓛».language j ) x ) ) ∧ ( ( ( ( 1 / 8 ) ≤ ( GenLimit.InfiniteContamination.elementBasedLowerDensity «𝔾» N x ) ) ) ∧ ( ( ( 1 / 2 ) ≤ ( GenLimit.InfiniteContamination.elementBasedUpperDensity «𝔾» N x ) ) ) ) )
```

### Corollary 6.20 · `GenLimit.InfiniteContamination.Results.corollary_6_20`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : GenLimit.OracleFamily ) , depends_only% [ «𝓛» ] ( ∃ «𝔾» : ( GenLimit.Generic.Generator ℕ ) , ∀ ( j : ℕ ) , let N := ( GenLimit.InfiniteContamination.canonicalFamilyOrders «𝓛» j ) ; ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration x ( «𝓛».language j ) ) ) , ( ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» ( «𝓛».language j ) x ) ) ∧ ( ( ( ( 1 / 8 ) ≤ ( GenLimit.InfiniteContamination.elementBasedLowerDensity «𝔾» N x ) ) ) ∧ ( ( ( 1 / 2 ) ≤ ( GenLimit.InfiniteContamination.elementBasedUpperDensity «𝔾» N x ) ) ) ) )
```

### Theorem 6.21 · `GenLimit.InfiniteContamination.Results.theorem_6_21`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ small : ( Set ℕ ) , ∃ large : GenLimit.KleinbergWei.OrderedLanguage , ∃ x : ( ℕ → ℕ ) , ( ( Set.Infinite small ) ) ∧ ( ( ( HasSSubset.SSubset small ( GenLimit.KleinbergWei.OrderedLanguage.carrier large ) ) ) ∧ ( ( ( GenLimit.InfiniteContamination.VanishingNoiseEnumeration x small ) ) ∧ ( ( ( GenLimit.InfiniteContamination.VanishingNoiseEnumeration x ( GenLimit.KleinbergWei.OrderedLanguage.carrier large ) ) ) ∧ ( ∀ ( «𝔾» : ( GenLimit.Generic.Generator ℕ ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» small x ) ) , ( ( GenLimit.InfiniteContamination.elementBasedUpperDensity «𝔾» large x ) = 0 ) ) ) ) ) )
```

### Theorem 7.6 · `GenLimit.InfiniteContamination.Results.theorem_7_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( M : ℝ ) , ∀ ( _ : ( 1 < M ) ) , ( ¬ ( ∃ A : ( ( List ℕ ) → ( Set ℕ ) ) , ( ∀ i : ℕ , ( ∀ x : ( ℕ → ℕ ) , ( ( Function.Injective x ) → ( ( Set.range x = ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( GenLimit.InfiniteContamination.puncturedFamilyOrders i ) ) ) → ( ( GenLimit.InfiniteContamination.BoundedDisplacement ( GenLimit.InfiniteContamination.puncturedFamilyOrders i ) x ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( GenLimit.InfiniteContamination.puncturedFamilyOrders i ) ) M ) → ( ∃ T : ℕ , ( ∀ t : ℕ , ( ( t ≥ T ) → ( ( A ( GenLimit.textPrefix x t ) ) = ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( GenLimit.InfiniteContamination.puncturedFamilyOrders i ) ) ) ) ) ) ) ) ) ) ) ) )
```

### Theorem 7.7 printed impossible · `GenLimit.InfiniteContamination.Results.theorem_7_7_printed_impossible`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( k : ℕ ) , ∀ ( _ : 2 ≤ k ) , ∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.ConstantNoise x ( GenLimit.KleinbergWei.OrderedLanguage.carrier K ) ( 1 / ( ↑ k ) ) ) ) , ( ¬ ( GenLimit.InfiniteContamination.BoundedDisplacement K x ( GenLimit.KleinbergWei.OrderedLanguage.carrier K ) ( 1 / ( ↑ k ) ) ) )
```

### Theorem 7.7 corrected · `GenLimit.InfiniteContamination.Results.theorem_7_7_corrected`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( k : ℕ ) , ∀ ( _ : 2 ≤ k ) , ∀ ( M : ℝ ) , ∀ ( _ : ( 1 ≤ M ) ) , ( ∃ K : ( ( Fin k ) → GenLimit.KleinbergWei.OrderedLanguage ) , ( ( Function.Injective ( fun i => ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( K i ) ) ) ) ) ∧ ( ( ∃ x : ( ℕ → ℕ ) , ( ∀ ( i : ( Fin k ) ) , ( ( GenLimit.InfiniteContamination.ConstantNoiseEnumeration x ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( K i ) ) ( 1 / ( ↑ k ) ) ) ∧ ( GenLimit.InfiniteContamination.BoundedDisplacement ( K i ) x ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( K i ) ) M ) ) ) ∧ ( ( ¬ ( ∃ «𝔾» : ( GenLimit.Generic.Generator ℕ ) , ( ∀ i : ( Fin k ) , ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( K i ) ) x ) ) ) ) ) ) ) )
```

### Theorem 7.8 · `GenLimit.InfiniteContamination.Results.theorem_7_8`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝓛» i ) ) ) ) , ∀ ( orders : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( ∀ i : ℕ , ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( orders i ) ) = ( «𝓛» i ) ) ) ) , ∀ ( ε M : ℝ ) , let «𝔾» := ( GenLimit.InfiniteContamination.algorithmNineSetGenerator «𝓛» orders ε M ) ; ∀ ( _ : ( 0 < ε ) ) , ∀ ( _ : ( ε < 1 ) ) , ∀ ( _ : ( 0 < M ) ) , ∀ ( target : ℕ ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.VanishingNoise x ( «𝓛» target ) ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.BoundedDisplacement ( orders target ) x ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( orders target ) ) M ) ) , ( ( ( GenLimit.InfiniteContamination.IsInfiniteSetGenerator «𝔾» ) ∧ ( GenLimit.InfiniteContamination.GeneratesSetInLimitOn «𝔾» ( «𝓛» target ) x ) ) ) ∧ ( depends_only% [ «𝓛» , orders , ε , M , target , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( ( ( 1 - ε ) / M ) ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( orders target ) ( GenLimit.InfiniteContamination.setOutput «𝔾» x t ) ) ) ) ) )
```

### Theorem 7.9 · `GenLimit.InfiniteContamination.Results.theorem_7_9`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
let N := ( GenLimit.KleinbergWei.OrderedLanguage.carrier GenLimit.InfiniteContamination.naturalOrder ) ; ∀ ( M : ℝ ) , ∀ ( _ : ( 1 ≤ M ) ) , ( ∃ K : GenLimit.KleinbergWei.OrderedLanguage , ∃ x : ( ℕ → ℕ ) , let Q := ( GenLimit.KleinbergWei.OrderedLanguage.carrier K ) ; ( ( HasSSubset.SSubset Q N ) ) ∧ ( ( ( GenLimit.InfiniteContamination.VanishingNoiseEnumeration x Q ) ) ∧ ( ( ( GenLimit.InfiniteContamination.VanishingNoiseEnumeration x N ) ) ∧ ( ( ( GenLimit.InfiniteContamination.BoundedDisplacement K x Q M ) ) ∧ ( ( ( GenLimit.InfiniteContamination.BoundedDisplacement GenLimit.InfiniteContamination.naturalOrder x N M ) ) ∧ ( ∀ ( «𝔾» : ( GenLimit.InfiniteContamination.SetGenerator ℕ ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.GeneratesSetInLimitOn «𝔾» Q x ) ) , ( ( GenLimit.InfiniteContamination.setBasedUpperDensity «𝔾» GenLimit.InfiniteContamination.naturalOrder x ) ≤ ( 1 / M ) ) ) ) ) ) ) )
```

### Theorem 7.10 · `GenLimit.InfiniteContamination.Results.theorem_7_10`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝓛» i ) ) ) ) , ∀ ( orders : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( ∀ i : ℕ , ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( orders i ) ) = ( «𝓛» i ) ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( StrictMono ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( orders i ) ) ) ) ) , ∀ ( ε M : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( _ : ( ε < 1 ) ) , ∀ ( _ : ( 0 < M ) ) , depends_only% [ «𝓛» , orders , ε , M ] ( ∃ «𝔾» : ( GenLimit.Generic.Generator ℕ ) , ∀ ( target : ℕ ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.VanishingNoise x ( «𝓛» target ) ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.BoundedDisplacement ( orders target ) x ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( orders target ) ) M ) ) , ( ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» ( «𝓛» target ) x ) ∧ ( ( ( 1 - ε ) / ( 2 * M ) ) ≤ ( GenLimit.InfiniteContamination.elementBasedLowerDensity «𝔾» ( orders target ) x ) ) ) )
```

### Theorem 7.11 · `GenLimit.InfiniteContamination.Results.theorem_7_11`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
let N := ( GenLimit.KleinbergWei.OrderedLanguage.carrier GenLimit.InfiniteContamination.naturalOrder ) ; ∀ ( M : ℝ ) , ∀ ( _ : ( 1 ≤ M ) ) , ( ∃ K : GenLimit.KleinbergWei.OrderedLanguage , ∃ x : ( ℕ → ℕ ) , let Q := ( GenLimit.KleinbergWei.OrderedLanguage.carrier K ) ; ( ( HasSSubset.SSubset Q N ) ) ∧ ( ( ( GenLimit.InfiniteContamination.VanishingNoiseEnumeration x Q ) ) ∧ ( ( ( GenLimit.InfiniteContamination.VanishingNoiseEnumeration x N ) ) ∧ ( ( ( GenLimit.InfiniteContamination.BoundedDisplacement K x Q M ) ) ∧ ( ( ( GenLimit.InfiniteContamination.BoundedDisplacement GenLimit.InfiniteContamination.naturalOrder x N M ) ) ∧ ( ∀ ( «𝔾» : ( GenLimit.Generic.Generator ℕ ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» Q x ) ) , ( ( GenLimit.InfiniteContamination.elementBasedUpperDensity «𝔾» GenLimit.InfiniteContamination.naturalOrder x ) ≤ ( 1 / M ) ) ) ) ) ) ) )
```

### Theorem B.2 · `GenLimit.InfiniteContamination.Results.theorem_B_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → GenLimit.Language ) ) , ∀ ( z : ℕ ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.VanishingNoise x ( «𝓛» z ) ) ) , ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn ( GenLimit.InfiniteContamination.activeCoreGenerator ( GenLimit.InfiniteContamination.algorithmTenCore «𝓛» ) ) ( «𝓛» z ) x )
```

### Theorem B.3 · `GenLimit.InfiniteContamination.Results.theorem_B_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( k : ℕ ) , ∀ ( _ : 2 ≤ k ) , ∀ ( c : ℝ ) , ( ∀ ( _ : ( ( 1 / ( ↑ k ) ) ≤ c ) ) , ( ∃ «𝓛» : ( ( Fin k ) → ( Set ℕ ) ) , ( ( Function.Injective «𝓛» ) ) ∧ ( ( ( ∀ i : ( Fin k ) , ( Set.Infinite ( «𝓛» i ) ) ) ) ∧ ( ( ∃ x : ( ℕ → ℕ ) , ( ( ∀ i : ( Fin k ) , ( GenLimit.InfiniteContamination.ConstantNoiseEnumeration x ( «𝓛» i ) c ) ) ) ∧ ( ( ¬ ( ∃ «𝔾» : ( GenLimit.Generic.Generator ℕ ) , ( ∀ i : ( Fin k ) , ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» ( «𝓛» i ) x ) ) ) ) ) ) ) ) ) ) ∧ ( ∀ ( _ : ( c < ( 1 / ( ↑ k ) ) ) ) , ∀ ( «𝓛» : ( ( Fin k ) → ( Set ℕ ) ) ) , depends_only% [ k , c , «𝓛» ] ( ∃ «𝔾» : ( GenLimit.Generic.Generator ℕ ) , ∀ ( i : ( Fin k ) ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.ConstantNoise x ( «𝓛» i ) c ) ) , ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» ( «𝓛» i ) x ) ) )
```

### Theorem B.4 · `GenLimit.InfiniteContamination.Results.theorem_B_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( k : ℕ ) , ∀ ( _ : ( 0 < k ) ) , ∀ ( «𝓛» : ( ( Fin k ) → ( Set ℕ ) ) ) , depends_only% [ k , «𝓛» ] ( ∃ «𝔾» : ( GenLimit.Generic.Generator ℕ ) , ∀ ( z : ( Fin k ) ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( _ : ( ( Filter.limsup ( GenLimit.InfiniteContamination.empiricalNoiseRate x ( «𝓛» z ) ) Filter.atTop ) < ( 1 / ( ↑ k ) ) ) ) , ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn «𝔾» ( «𝓛» z ) x ) )
```

Grammar regression for P17: 2186/2186 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P18

SHA-256 of the checked page: `7e5bc93b1443b556805f6e1d61551371744fd0408b510ed62ac34bdbcaf0e814`

### Theorem 3.1 · `GenLimit.SafeGeneration.Results.theorem_3_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
let K := ( GenLimit.SafeGeneration.SafeIdentification.candidateFamily 0 ) ; ( ( ∀ i : ℕ , ( Set.Infinite ( GenLimit.SafeGeneration.SafeIdentification.candidateFamily i ) ) ) ) ∧ ( ( ( ∀ j : ℕ , ( Set.Infinite ( GenLimit.SafeGeneration.SafeIdentification.harmfulFamily j ) ) ) ) ∧ ( ( ∀ ( j : ℕ ) , ( ∃ i : ℕ , ( ( GenLimit.SafeGeneration.SafeIdentification.candidateFamily i ) = ( K \ ( GenLimit.SafeGeneration.SafeIdentification.harmfulFamily j ) ) ) ) ) ∧ ( ( ¬ ( ∃ M : ( GenLimit.SafeGeneration.SafeIdentification.SafeIdentifier ( ℕ ⊕ ( ℕ ⊕ ℕ ) ) ) , ( ∀ j : ℕ , ( ∀ x : ( ℕ → ( ( ℕ ⊕ ( ℕ ⊕ ℕ ) ) × Bool ) ) , ( ( GenLimit.SafeGeneration.LabeledPresents x K ( GenLimit.SafeGeneration.SafeIdentification.harmfulFamily j ) ) → ( GenLimit.SafeGeneration.SafeIdentification.SafelyIdentifiesFrom M GenLimit.SafeGeneration.SafeIdentification.candidateFamily K ( GenLimit.SafeGeneration.SafeIdentification.harmfulFamily j ) x ) ) ) ) ) ) ) ) )
```

### Theorem 5.1 · `GenLimit.SafeGeneration.Results.theorem_5_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ ( G : ( GenLimit.SafeGeneration.SafeGenerator ( «𝒳» × ℕ ) ) ) , ∀ ( «𝓛» : ( ℕ → ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( hInfinite : ( ∀ i : ℕ , ( Set.Infinite ( «𝓛» i ) ) ) ) , ∀ ( _ : ( GenLimit.SafeGeneration.SafelyGeneratesFamilies G ( fun i => ( GenLimit.SafeGeneration.verticalPad ( «𝓛» i ) ) ) ( fun i => ( GenLimit.SafeGeneration.verticalPad ( «𝓛» i ) ) ) ) ) , ( GenLimit.Angluin.SemanticallyIdentifies ( GenLimit.SafeGeneration.identificationFromSafeGenerator G «𝓛» ( fun i => ( GenLimit.SafeGeneration.verticalPadPresentation ( «𝓛» i ) ( Set.Infinite.nonempty ( hInfinite i ) ) ) ) ) «𝓛» )
```

### Theorem 6.1 · `GenLimit.SafeGeneration.Results.theorem_6_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ¬ ( ∃ P : ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.LanguagePairCode → Prop ) , ( ( ComputablePred P ) ∧ ( ∀ pair : GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.LanguagePairCode , ( ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.IsValidLanguagePair pair ) → ( ( P pair ) ↔ ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.CodedDiffEmpty pair ) ) ) ) ) ) )
```

### Corollary 6.1 · `GenLimit.SafeGeneration.Results.corollary_6_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝓛_K» : ( ℕ → ( GenLimit.Generic.Language ( Bool × ( ℕ × ℕ ) ) ) ) , ∃ «𝓛_H» : ( ℕ → ( GenLimit.Generic.Language ( Bool × ( ℕ × ℕ ) ) ) ) , ( ∀ ( i : ℕ ) , ( ( Set.Infinite ( «𝓛_K» i ) ) ∧ ( Set.Infinite ( «𝓛_H» i ) ) ) ) ∧ ( ( ( ComputablePred ( fun p => ( ( Prod.snd p ) ∈ ( «𝓛_K» ( Prod.fst p ) ) ) ) ) ) ∧ ( ( ( ComputablePred ( fun p => ( ( Prod.snd p ) ∈ ( «𝓛_H» ( Prod.fst p ) ) ) ) ) ) ∧ ( ( ( ∃ I : ( ( List ( Bool × ( ℕ × ℕ ) ) ) → ℕ ) , ( ( Computable I ) ∧ ( GenLimit.Angluin.SemanticallyIdentifies I «𝓛_K» ) ) ) ) ∧ ( ( ( ∃ I : ( ( List ( Bool × ( ℕ × ℕ ) ) ) → ℕ ) , ( ( Computable I ) ∧ ( GenLimit.Angluin.SemanticallyIdentifies I «𝓛_H» ) ) ) ) ∧ ( ∀ ( A : ( ( List ( ( Bool × ( ℕ × ℕ ) ) × Bool ) ) → ( Option ( Bool × ( ℕ × ℕ ) ) ) ) ) , ∀ ( _ : ( Computable A ) ) , ( ¬ ( ( GenLimit.SafeGeneration.SafelyGeneratesFamilies ( fun x => ( fun xs => ( A ( List.ofFn xs ) ) ) ) «𝓛_K» «𝓛_H» ) ) ) ) ) ) ) ) )
```

### Corollary 6.1 printed reduction collapses · `GenLimit.SafeGeneration.Results.corollary_6_1_printed_reduction_collapses`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( G : ( GenLimit.SafeGeneration.SafeGenerator ℕ ) ) , ∀ ( x : ( ℕ → ( ℕ × Bool ) ) ) , ∀ ( c : Nat.Partrec.Code ) , let A := { n : ℕ | ( ¬ ( GenLimit.SafeGeneration.DiffEmpty.PrintedReduction.FirstBoundedHalt c n ) ) } ; ( ( GenLimit.SafeGeneration.SafelyGenerates G Set.univ A x ) ↔ ( GenLimit.SafeGeneration.EventuallyBottom G x ) )
```

### Theorem 6.2 · `GenLimit.SafeGeneration.Results.theorem_6_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝓛_K» : ( ℕ → ( GenLimit.Generic.Language ( ℕ × ℕ ) ) ) , ∃ «𝓛_H» : ( ℕ → ( GenLimit.Generic.Language ( ℕ × ℕ ) ) ) , ( ( ∀ i : ℕ , ( Set.Infinite ( «𝓛_K» i ) ) ) ) ∧ ( ( ( ∀ j : ℕ , ( Set.Infinite ( «𝓛_H» j ) ) ) ) ∧ ( ∀ ( O : ( GenLimit.SafeGeneration.SetDifferenceOracle ( ℕ × ℕ ) ) ) , ∀ ( _ : ( ∀ ( X Y : ( Set ( ℕ × ℕ ) ) ) , ( ( ( O X Y ) = Bool.true ) ↔ ( ( X \ Y ) = EmptyCollection.emptyCollection ) ) ) ) , ∀ ( A : ( GenLimit.SafeGeneration.OracleSafeAlgorithm ( ℕ × ℕ ) ) ) , ( ¬ ( ( GenLimit.SafeGeneration.SafelyGeneratesFamilies ( A O ) «𝓛_K» «𝓛_H» ) ) ) ) ) )
```

### Theorem 6.3 · `GenLimit.SafeGeneration.Results.theorem_6_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( «𝓛_K» «𝓛_H» : ( ℕ → ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( _ : ( ∀ ( i j : ℕ ) , ( Set.Infinite ( ( «𝓛_K» i ) \ ( «𝓛_H» j ) ) ) ) ) , ( GenLimit.SafeGeneration.SafelyGeneratesInfiniteDifferences ( GenLimit.SafeGeneration.infiniteDifferenceGenerator (hCross := by assumption) «𝓛_K» «𝓛_H» ) «𝓛_K» «𝓛_H» )
```

Grammar regression for P18: 692/692 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P19

SHA-256 of the checked page: `f64b0ba4247448861d3344a4931804f002a0c2a94779504dc650dc272b2f2322`

### Theorem 2.16 · `GenLimit.QuantifyingNoise.Results.theorem_2_16`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ [ Countable U ] , ∀ [ Nonempty U ] , ∀ ( «𝒞» : ( Set ( GenLimit.Generic.Language U ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝒞» , ( Set.Infinite L ) ) ) , ( ∀ ( i : ℕ ) , 1 ≤ i → ( ( ( GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel «𝒞» i ) ↔ ( GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel «𝒞» 1 ) ) ∧ ( ( GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel «𝒞» i ) ↔ ( GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel «𝒞» 1 ) ) ) )
```

### Theorem 2.17 · `GenLimit.QuantifyingNoise.Results.theorem_2_17`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒞» : ( Set ( GenLimit.Generic.Language ( ℕ × ℕ ) ) ) , ( ( GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel «𝒞» 0 ) ∧ ( ¬ ( GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel «𝒞» 1 ) ) ) )
```

### Theorem 2.18 · `GenLimit.QuantifyingNoise.Results.theorem_2_18`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ [ Countable U ] , ∀ [ Nonempty U ] , ∀ ( «𝒞» : ( Set ( GenLimit.Generic.Language U ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝒞» , ( Set.Infinite L ) ) ) , ( ( ( ( GenLimit.QuantifyingNoise.FiniteNoisyClosureDimensionAt «𝒞» 1 ) ) ↔ ( ( ∀ ( i : ℕ ) , 1 ≤ i → ( GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel «𝒞» i ) ) ) ) ∧ ( ( ( GenLimit.QuantifyingNoise.FiniteNoisyClosureDimensionAt «𝒞» 1 ) ↔ ( GenLimit.QuantifyingNoise.UniformNoiseDependentGeneratable «𝒞» ) ) ) ) ∧ ( ( ∃ D : ( Set ( GenLimit.Generic.Language ( ℕ × ℕ ) ) ) , ( ( GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel D 0 ) ∧ ( ¬ ( GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel D 1 ) ) ) ) )
```

### Theorem 2.19 · `GenLimit.QuantifyingNoise.Results.theorem_2_19`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ [ Countable U ] , ∀ [ Nonempty U ] , ∀ ( «𝒞» : ( Set ( GenLimit.Generic.Language U ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝒞» , ( Set.Infinite L ) ) ) , ( ( ( ( GenLimit.QuantifyingNoise.HasFiniteDimensionExhaustionAt «𝒞» 1 ) ) ↔ ( ( ∀ ( i : ℕ ) , 1 ≤ i → ( GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel «𝒞» i ) ) ) ) ∧ ( ( ( GenLimit.QuantifyingNoise.HasFiniteDimensionExhaustionAt «𝒞» 1 ) ↔ ( GenLimit.QuantifyingNoise.NonuniformNoiseDependentGeneratable «𝒞» ) ) ) ) ∧ ( ( ∃ D : ( Set ( GenLimit.Generic.Language ( ℕ × ℕ ) ) ) , ( ( GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel D 0 ) ∧ ( ¬ ( GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel D 1 ) ) ) ) )
```

Grammar regression for P19: 400/400 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P20

SHA-256 of the checked page: `65c0a006d9be2889b180569216e57131d9760ae7bd647d0ce59c10077373c6e3`

### Theorem 2.1 · `GenLimit.AgnosticLanguage.Results.theorem_2_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ [ Countable U ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language U ) ) ) , ∀ ( f : ( ℕ → ℕ ) ) , let «𝒜» := ( GenLimit.AgnosticLanguage.algorithmOne «𝒞» f ) ; ∀ ( _ : ( Filter.Tendsto f Filter.atTop Filter.atTop ) ) , ∀ ( «𝒟» : ( PMF U ) ) , ∀ ( _ : ( ∃ i : ℕ , ( GenLimit.AgnosticLanguage.Optimal «𝒞» «𝒟» i ) ) ) , ( ∀ᶠ ( n : ℕ ) in Filter.atTop , ( ( ( GenLimit.DiscreteIID.probability ( GenLimit.DiscreteIID.samples «𝒟» n ) { S : ( List U ) | ( ¬ ( GenLimit.AgnosticLanguage.Optimal «𝒞» «𝒟» ( «𝒜» S ) ) ) } ) ≤ ( ( 2 * ( ↑ ( f n ) ) ) * ( Real.exp ( ( - ( ↑ n ) ) / ( 2 * ( ( ↑ ( f n ) ) ^ 2 ) ) ) ) ) ) ∧ ( ( GenLimit.AgnosticLanguage.idErr «𝒞» ( GenLimit.AgnosticLanguage.deterministic «𝒜» ) «𝒟» n ) ≤ ( ( 2 * ( ↑ ( f n ) ) ) * ( Real.exp ( ( - ( ↑ n ) ) / ( 2 * ( ( ↑ ( f n ) ) ^ 2 ) ) ) ) ) ) ) )
```

### Theorem 2.2 · `GenLimit.AgnosticLanguage.Results.theorem_2_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language U ) ) ) , ∀ ( i j : ℕ ) , ∀ ( _ : ( ( «𝒞» i ) ≠ ( «𝒞» j ) ) ) , ∀ ( x y : U ) , ∀ ( _ : ( ∀ k : ℕ , ( ( x ∈ ( «𝒞» k ) ) ↔ ( ( «𝒞» k ) = ( «𝒞» i ) ) ) ) ) , ∀ ( _ : ( ∀ k : ℕ , ( ( y ∈ ( «𝒞» k ) ) ↔ ( ( «𝒞» k ) = ( «𝒞» j ) ) ) ) ) , ∀ ( «𝒜» : ( ( List U ) → ( PMF ℕ ) ) ) , ( ∃ «𝒟» : ( PMF U ) , ( ( ∃ k : ℕ , ( GenLimit.AgnosticLanguage.Optimal «𝒞» «𝒟» k ) ) ) ∧ ( ( ∃ᶠ ( n : ℕ ) in Filter.atTop , ( ( Real.exp ( ( - 5 ) * ( ↑ n ) ) ) ≤ ( GenLimit.AgnosticLanguage.idErr «𝒞» «𝒜» «𝒟» n ) ) ) ) )
```

### Theorem 2.3 · `GenLimit.AgnosticLanguage.Results.theorem_2_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒞» : ( ℕ → ( GenLimit.Generic.Language ( ℕ × ( Option Bool ) ) ) ) , ( ( ∀ i : ℕ , ( Set.Infinite ( «𝒞» i ) ) ) ) ∧ ( ∀ ( «𝒜» : ( ( List ( ℕ × ( Option Bool ) ) ) → ( PMF ℕ ) ) ) , ∀ ( R : ( ℕ → ℝ ) ) , ∀ ( _ : ( Filter.Tendsto R Filter.atTop ( nhds 0 ) ) ) , ( ∃ «𝒟» : ( PMF ( ℕ × ( Option Bool ) ) ) , ( ( ¬ ( ∃ i : ℕ , ( GenLimit.AgnosticLanguage.Optimal «𝒞» «𝒟» i ) ) ) ) ∧ ( ( ∃ᶠ ( n : ℕ ) in Filter.atTop , ( ( ( R n ) / 8 ) ≤ ( GenLimit.AgnosticLanguage.idErr «𝒞» «𝒜» «𝒟» n ) ) ) ) ) ) )
```

### Theorem 2.4 · `GenLimit.AgnosticLanguage.Results.theorem_2_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ [ Countable U ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language U ) ) ) , ∀ ( f : ( ℕ → ℕ ) ) , ∀ ( _ : ( Filter.Tendsto f Filter.atTop Filter.atTop ) ) , ∀ ( «𝒟» : ( PMF U ) ) , ∀ ( _ : ( GenLimit.AgnosticLanguage.HasSupportedTellTale «𝒞» «𝒟» ) ) , ( ∃ c : ℝ , ( ( c > 0 ) ) ∧ ( ( ∃ C : ℝ , ( ( C > 0 ) ∧ ( ∀ᶠ ( n : ℕ ) in Filter.atTop , ( ( GenLimit.AgnosticLanguage.idP «𝒞» ( GenLimit.AgnosticLanguage.deterministic ( GenLimit.AgnosticLanguage.algorithmTwo «𝒞» f ) ) «𝒟» n ) ≤ ( ( c * ( ↑ ( f n ) ) ) * ( Real.exp ( ( ( - C ) * ( ↑ n ) ) / ( ( ↑ ( f n ) ) ^ 2 ) ) ) ) ) ) ) ) ) )
```

### Theorem 2.5 · `GenLimit.AgnosticLanguage.Results.theorem_2_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒞» : ( ℕ → ( GenLimit.Generic.Language ( Bool × ℕ ) ) ) , ( ∀ ( i : ℕ ) , ( ( Set.Infinite ( «𝒞» i ) ) ) ∧ ( ( ∃ T : ( Finset ( Bool × ℕ ) ) , ( GenLimit.Generic.IsFiniteTellTale ( Set.range «𝒞» ) ( «𝒞» i ) T ) ) ) ) ∧ ( ∀ ( «𝒜» : ( ( List ( Bool × ℕ ) ) → ℕ ) ) , ( ∃ «𝒟» : ( PMF ( Bool × ℕ ) ) , ( ( ∃ i : ℕ , ( GenLimit.AgnosticLanguage.Optimal «𝒞» «𝒟» i ) ) ) ∧ ( ( ( ¬ ( ( GenLimit.AgnosticLanguage.HasSupportedTellTale «𝒞» «𝒟» ) ) ) ) ∧ ( ( ( Filter.liminf ( fun n => ( GenLimit.DiscreteIID.probability ( GenLimit.DiscreteIID.samples «𝒟» n ) { S : ( List ( Bool × ℕ ) ) | ( GenLimit.AgnosticLanguage.MinimalOptimal «𝒞» «𝒟» ( «𝒜» S ) ) } ) ) Filter.atTop ) ≤ ( 1 / 2 ) ) ) ) ) ) )
```

### Theorem 3.1 · `GenLimit.AgnosticLanguage.Results.theorem_3_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( «𝒜» : ( ( List ℕ ) → ( PMF ℕ ) ) ) , ( ∃ «𝒟» : ( PMF ℕ ) , ( ( Set.Infinite ( PMF.support «𝒟» ) ) ∧ ( ∃ᶠ ( n : ℕ ) in Filter.atTop , ( ( 1 - ε ) ≤ ( GenLimit.AgnosticLanguage.genErr «𝒜» «𝒟» n ) ) ) ) )
```

### Theorem 3.2 · `GenLimit.AgnosticLanguage.Results.theorem_3_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ ( u : ( ℕ ≃ U ) ) , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language U ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝒞» i ) ) ) ) , ∀ ( «𝒟» : ( PMF U ) ) , ∀ ( _ : ( GenLimit.AgnosticLanguage.FiniteWitnessIndex u «𝒞» «𝒟» ) ) , ∀ ( _ : ( ∃ i : ℕ , ( binrel% HasSubset.Subset ( «𝒞» i ) ( PMF.support «𝒟» ) ) ) ) , ( ∃ c : ℝ , ( ( c > 0 ) ) ∧ ( ( ∃ C : ℝ , ( ( C > 0 ) ) ∧ ( ( ∀ n : ℕ , ( ( GenLimit.AgnosticLanguage.genErr ( GenLimit.AgnosticLanguage.deterministic ( GenLimit.AgnosticLanguage.algorithmThree (hC := by assumption) u «𝒞» ) ) «𝒟» n ) ≤ ( c * ( Real.exp ( ( - C ) * ( ↑ n ) ) ) ) ) ) ) ) ) )
```

### Corollary 3.3 · `GenLimit.AgnosticLanguage.Results.corollary_3_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ ( u : ( ℕ ≃ U ) ) , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language U ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝒞» i ) ) ) ) , ∀ ( _ : ( Set.Finite ( Set.range «𝒞» ) ) ) , ∀ ( «𝒟» : ( PMF U ) ) , ∀ ( _ : ( ∃ i : ℕ , ( binrel% HasSubset.Subset ( «𝒞» i ) ( PMF.support «𝒟» ) ) ) ) , ( ∃ c : ℝ , ( ( c > 0 ) ) ∧ ( ( ∃ C : ℝ , ( ( C > 0 ) ) ∧ ( ( ∀ n : ℕ , ( ( GenLimit.AgnosticLanguage.genErr ( GenLimit.AgnosticLanguage.deterministic ( GenLimit.AgnosticLanguage.algorithmThree (hC := by assumption) u «𝒞» ) ) «𝒟» n ) ≤ ( c * ( Real.exp ( ( - C ) * ( ↑ n ) ) ) ) ) ) ) ) ) )
```

### Theorem 3.4 · `GenLimit.AgnosticLanguage.Results.theorem_3_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒞» : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) , ( ( ∀ i : ℕ , ( Set.Infinite ( «𝒞» i ) ) ) ) ∧ ( ∀ ( «𝒜» : ( ( List ℕ ) → ℕ ) ) , ( ∃ «𝒟» : ( PMF ℕ ) , ( ( ∃ i : ℕ , ( binrel% HasSubset.Subset ( «𝒞» i ) ( PMF.support «𝒟» ) ) ) ) ∧ ( ( ( ¬ ( GenLimit.AgnosticLanguage.FiniteWitnessIndex ( Equiv.refl Nat ) «𝒞» «𝒟» ) ) ) ∧ ( ( ( 1 / 2 ) ≤ ( Filter.limsup ( GenLimit.AgnosticLanguage.genErr ( GenLimit.AgnosticLanguage.deterministic «𝒜» ) «𝒟» ) Filter.atTop ) ) ) ) ) ) )
```

### Theorem 3.5 · `GenLimit.AgnosticLanguage.Results.theorem_3_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( U : Type _ ) , ∀ [ Countable U ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language U ) ) ) , ∀ ( i j : ℕ ) , ∀ ( _ : ( Set.Finite ( ( «𝒞» i ) ∩ ( «𝒞» j ) ) ) ) , ∀ ( x : U ) , ∀ ( _ : ( x ∉ ( ( «𝒞» i ) ∪ ( «𝒞» j ) ) ) ) , ∀ ( «𝒜» : ( ( List U ) → ( PMF U ) ) ) , ( ∃ «𝒟» : ( PMF U ) , ( ( ∃ k : ℕ , ( binrel% HasSubset.Subset ( «𝒞» k ) ( PMF.support «𝒟» ) ) ) ) ∧ ( ( ∃ᶠ ( n : ℕ ) in Filter.atTop , ( ( ( Real.exp ( ( - 2 ) * ( ↑ n ) ) ) / 4 ) ≤ ( GenLimit.AgnosticLanguage.genErr «𝒜» «𝒟» n ) ) ) ) )
```

Grammar regression for P20: 994/994 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P21

SHA-256 of the checked page: `66524b4e86a03d988922c35354c2f818877a5ea4224cf69ca2172c6ac0805deb`

### Theorem 3.1 · `GenLimit.MetricSpaces.Results.theorem_3_1`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ ( ρ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( ε_a ε_g : ℝ ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( ∀ x : «𝒳» , ( ( ρ x x ) = 0 ) ) ) , ∀ ( _ : ( 0 ≤ ε_a ) ) , ( ( GenLimit.MetricSpaces.UniformlyGeneratableAt ρ ε_a ε_g «ℋ» ) ↔ ( GenLimit.MetricSpaces.HasFiniteScaleClosureDimension ρ ε_a ε_g «ℋ» ) )
```

### Corollary 3.2 · `GenLimit.MetricSpaces.Results.corollary_3_2`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ ( ρ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( ε_a ε_g : ℝ ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( ∀ x : «𝒳» , ( ( ρ x x ) = 0 ) ) ) , ∀ ( _ : ( 0 ≤ ε_a ) ) , ∀ ( _ : ( ε_g ≤ ε_a ) ) , ∀ ( _ : ( Set.Finite «ℋ» ) ) , ( GenLimit.MetricSpaces.UniformlyGeneratableAt ρ ε_a ε_g «ℋ» )
```

### Theorem 3.3 · `GenLimit.MetricSpaces.Results.theorem_3_3`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ ( ρ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( ε_a ε_g : ℝ ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( ∀ x : «𝒳» , ( ( ρ x x ) = 0 ) ) ) , ∀ ( _ : ( 0 ≤ ε_a ) ) , ( ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt ρ ε_a ε_g «ℋ» ) ) ↔ ( ( ∃ classes : ( ℕ → ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ( ( GenLimit.Generic.IsNondecreasingCover «ℋ» classes ) ) ∧ ( ( ∀ n : ℕ , ( GenLimit.MetricSpaces.HasFiniteScaleClosureDimension ρ ε_a ε_g ( classes n ) ) ) ) ) )
```

### Corollary 3.4 · `GenLimit.MetricSpaces.Results.corollary_3_4`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Nonempty «𝒳» ] , ∀ ( ρ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( ε_a ε_g : ℝ ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( ∀ x : «𝒳» , ( ( ρ x x ) = 0 ) ) ) , ∀ ( _ : ( 0 ≤ ε_a ) ) , ∀ ( _ : ( ε_g ≤ ε_a ) ) , ∀ ( _ : ( Set.Countable «ℋ» ) ) , ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt ρ ε_a ε_g «ℋ» )
```

### Theorem 3.5 · `GenLimit.MetricSpaces.Results.theorem_3_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( r ε_a ε_g : ℝ ) , ∀ ( _ : ( 0 < r ) ) , ∀ ( _ : ( 0 < ε_a ) ) , ∀ ( _ : ( 0 < ε_g ) ) , ∀ ( _ : ( ε_a ≤ r ) ) , ∀ ( _ : ( ε_g ≤ r ) ) , ( ∃ «ℋ_1» : ( GenLimit.Generic.LanguageClass ℝ ) , ∃ «ℋ_2» : ( GenLimit.Generic.LanguageClass ℝ ) , ( ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt Dist.dist r «ℋ_1» ) ∧ ( ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt Dist.dist r «ℋ_2» ) ∧ ( ( GenLimit.MetricSpaces.UniformlyGeneratableAt Dist.dist ε_a ε_g «ℋ_1» ) ∧ ( ( GenLimit.MetricSpaces.UniformlyGeneratableAt Dist.dist ε_a ε_g «ℋ_2» ) ∧ ( ¬ ( GenLimit.MetricSpaces.GeneratableInLimitAt Dist.dist ε_a ε_g ( «ℋ_1» ∪ «ℋ_2» ) ) ) ) ) ) ) )
```

### Theorem 4.1 · `GenLimit.MetricSpaces.Results.theorem_4_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( ρ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( r : ℝ ) , ∀ ( _ : ( GenLimit.MetricSpaces.IsDoublingDistance ρ ) ) , ∀ ( _ : ( ∀ x : «𝒳» , ( ( ρ x x ) = 0 ) ) ) , ∀ ( _ : ( ∀ ( x y : «𝒳» ) , ( ( ρ x y ) = ( ρ y x ) ) ) ) , ∀ ( _ : ( ∀ ( x y z : «𝒳» ) , ( ( ρ x z ) ≤ ( ( ρ x y ) + ( ρ y z ) ) ) ) ) , ∀ ( _ : ( 0 < r ) ) , ∀ ( _ : ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt ρ r «ℋ» ) ) , ∀ ( r' : ℝ ) , ∀ ( _ : ( 0 < r' ) ) , ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt ρ r' «ℋ» )
```

### Theorem 4.2 · `GenLimit.MetricSpaces.Results.theorem_4_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( ρ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( δ_a δ_g ε_a ε_g : ℝ ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.MetricSpaces.IsDoublingDistance ρ ) ) , ∀ ( _ : ( ∀ x : «𝒳» , ( ( ρ x x ) = 0 ) ) ) , ∀ ( _ : ( ∀ ( x y : «𝒳» ) , ( ( ρ x y ) = ( ρ y x ) ) ) ) , ∀ ( _ : ( ∀ ( x y z : «𝒳» ) , ( ( ρ x z ) ≤ ( ( ρ x y ) + ( ρ y z ) ) ) ) ) , ∀ ( _ : ( 0 < δ_a ) ) , ∀ ( _ : ( δ_a < ε_a ) ) , ∀ ( _ : ( 0 < δ_g ) ) , ∀ ( _ : ( δ_g < ε_g ) ) , ( ( ( GenLimit.MetricSpaces.UniformlyGeneratableAt ρ ε_a ε_g «ℋ» ) ↔ ( GenLimit.MetricSpaces.UniformlyGeneratableAt ρ δ_a δ_g «ℋ» ) ) ) ∧ ( ( ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt ρ ε_a ε_g «ℋ» ) ↔ ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt ρ δ_a δ_g «ℋ» ) ) )
```

### Corollary 4.3 · `GenLimit.MetricSpaces.Results.corollary_4_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ NormedAddCommGroup «𝒳» ] , ∀ [ NormedSpace ℝ «𝒳» ] , ∀ [ FiniteDimensional ℝ «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( r δ_a δ_g ε_a ε_g : ℝ ) , ∀ ( _ : ( 0 < r ) ) , ∀ ( _ : ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt Dist.dist r «ℋ» ) ) , ∀ ( _ : ( 0 < δ_a ) ) , ∀ ( _ : ( 0 < δ_g ) ) , ∀ ( _ : ( 0 < ε_a ) ) , ∀ ( _ : ( 0 < ε_g ) ) , ( ( ( GenLimit.MetricSpaces.UniformlyGeneratableAt Dist.dist ε_a ε_g «ℋ» ) ↔ ( GenLimit.MetricSpaces.UniformlyGeneratableAt Dist.dist δ_a δ_g «ℋ» ) ) ) ∧ ( ( ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt Dist.dist ε_a ε_g «ℋ» ) ↔ ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt Dist.dist δ_a δ_g «ℋ» ) ) )
```

### Theorem 4.4 · `GenLimit.MetricSpaces.Results.theorem_4_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( ρ₁ ρ₂ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( M₁₂ M₂₁ r₁ r₂ ε₁ ε₁' ε₂ ε₂' : ℝ ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( GenLimit.MetricSpaces.IsDoublingDistance ρ₁ ) ) , ∀ ( _ : ( ∀ x : «𝒳» , ( ( ρ₁ x x ) = 0 ) ) ) , ∀ ( _ : ( ∀ ( x y : «𝒳» ) , ( ( ρ₁ x y ) = ( ρ₁ y x ) ) ) ) , ∀ ( _ : ( ∀ ( x y z : «𝒳» ) , ( ( ρ₁ x z ) ≤ ( ( ρ₁ x y ) + ( ρ₁ y z ) ) ) ) ) , ∀ ( _ : ( ∀ x : «𝒳» , ( ( ρ₂ x x ) = 0 ) ) ) , ∀ ( _ : ( ∀ ( x y : «𝒳» ) , ( ( ρ₂ x y ) = ( ρ₂ y x ) ) ) ) , ∀ ( _ : ( ∀ ( x y z : «𝒳» ) , ( ( ρ₂ x z ) ≤ ( ( ρ₂ x y ) + ( ρ₂ y z ) ) ) ) ) , ∀ ( _ : ( 0 < M₁₂ ) ) , ∀ ( _ : ( 0 < M₂₁ ) ) , ∀ ( _ : ( ( ∀ ( x y : «𝒳» ) , ( ( ρ₂ x y ) ≤ ( M₁₂ * ( ρ₁ x y ) ) ) ) ∧ ( ∀ ( x y : «𝒳» ) , ( ( ρ₁ x y ) ≤ ( M₂₁ * ( ρ₂ x y ) ) ) ) ) ) , ∀ ( _ : ( 0 < r₁ ) ) , ∀ ( _ : ( 0 < r₂ ) ) , ∀ ( _ : ( 0 < ε₁ ) ) , ∀ ( _ : ( 0 < ε₁' ) ) , ∀ ( _ : ( 0 < ε₂ ) ) , ∀ ( _ : ( 0 < ε₂' ) ) , ( ( ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt ρ₁ r₁ «ℋ» ) ↔ ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt ρ₂ r₂ «ℋ» ) ) ) ∧ ( ( ( ( GenLimit.MetricSpaces.UniformlyGeneratableAt ρ₁ ε₁ ε₁' «ℋ» ) ↔ ( GenLimit.MetricSpaces.UniformlyGeneratableAt ρ₂ ε₂ ε₂' «ℋ» ) ) ) ∧ ( ( ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt ρ₁ ε₁ ε₁' «ℋ» ) ↔ ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt ρ₂ ε₂ ε₂' «ℋ» ) ) ) )
```

### Example 4.5 · `GenLimit.MetricSpaces.Results.example_4_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ε_a : ℝ ) , ∀ ( _ : ( 0 < ε_a ) ) , ∀ ( _ : ( ε_a < 1 ) ) , ( ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt GenLimit.MetricSpaces.RealLineThreshold.realDistance 1 GenLimit.MetricSpaces.RealLineThreshold.languageClass ) ) ∧ ( ( ( GenLimit.MetricSpaces.GeneratableInLimitAt GenLimit.MetricSpaces.RealLineThreshold.realDistance ε_a 1 GenLimit.MetricSpaces.RealLineThreshold.languageClass ) ) ∧ ( ( ¬ ( GenLimit.MetricSpaces.GeneratableInLimitAt GenLimit.MetricSpaces.RealLineThreshold.realDistance 1 1 GenLimit.MetricSpaces.RealLineThreshold.languageClass ) ) ) )
```

### Theorem 4.6 · `GenLimit.MetricSpaces.Results.theorem_4_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( ρ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( δ_a δ_g ε_a ε_g : ℝ ) , ∀ ( _ : ( δ_a ≤ ε_a ) ) , ∀ ( _ : ( δ_g ≤ ε_g ) ) , ∀ ( _ : ( GenLimit.MetricSpaces.GeneratableInLimitAt ρ ε_a ε_g «ℋ» ) ) , ( GenLimit.MetricSpaces.GeneratableInLimitAt ρ δ_a δ_g «ℋ» )
```

### Theorem 4.7 · `GenLimit.MetricSpaces.Results.theorem_4_7`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( ρ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( ε_a ε_g δ_a δ_g : ℝ ) , ∀ ( _ : ( ε_a ≤ δ_a ) ) , ∀ ( _ : ( δ_g ≤ ε_g ) ) , ( ∀ ( _ : ( GenLimit.MetricSpaces.UniformlyGeneratableAt ρ ε_a ε_g «ℋ» ) ) , ( GenLimit.MetricSpaces.UniformlyGeneratableAt ρ δ_a δ_g «ℋ» ) ) ∧ ( ∀ ( _ : ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt ρ ε_a ε_g «ℋ» ) ) , ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt ρ δ_a δ_g «ℋ» ) )
```

### Example 4.8 · `GenLimit.MetricSpaces.Results.example_4_8`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( r ε_a ε_g : ℝ ) , ∀ ( _ : ( 0 < r ) ) , ∀ ( _ : ( 0 < ε_a ) ) , ∀ ( _ : ( ε_a ≤ r ) ) , ∀ ( _ : ( 0 < ε_g ) ) , ∀ ( _ : ( ε_g ≤ r ) ) , let «ℋ» := ( GenLimit.MetricSpaces.HilbertAxisReservoir.example48LanguageClass r ε_a ε_g ) ; ( ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt GenLimit.MetricSpaces.HilbertAxisReservoir.hilbertDistance r «ℋ» ) ) ∧ ( ( ∀ ( γ_a γ_g : ℝ ) , ∀ ( _ : ( 0 < γ_a ) ) , ∀ ( _ : ( γ_a ≤ r ) ) , ∀ ( _ : ( 0 < γ_g ) ) , ∀ ( _ : ( γ_g ≤ r ) ) , ( ( GenLimit.MetricSpaces.GeneratableInLimitAt GenLimit.MetricSpaces.HilbertAxisReservoir.hilbertDistance γ_a γ_g «ℋ» ) ) ↔ ( ( ( γ_a < ε_a ) ∧ ( γ_g < ε_g ) ) ) ) ∧ ( ∀ ( γ_a γ_g : ℝ ) , ∀ ( _ : ( 0 < γ_a ) ) , ∀ ( _ : ( γ_a < ε_a ) ) , ∀ ( _ : ( 0 < γ_g ) ) , ∀ ( _ : ( γ_g < ε_g ) ) , ( GenLimit.MetricSpaces.IsLimitGeneratorAt GenLimit.MetricSpaces.HilbertAxisReservoir.hilbertDistance γ_a γ_g ( GenLimit.MetricSpaces.HilbertAxisReservoir.example48CausalGenerator ε_a ε_g γ_g ) «ℋ» ) ) )
```

### Example 4.9 · `GenLimit.MetricSpaces.Results.example_4_9`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( r ε₁ ε₂ ε_g : ℝ ) , ∀ ( _ : ( 0 < r ) ) , ∀ ( _ : ( 0 < ε₁ ) ) , ∀ ( _ : ( ε₁ ≤ ε₂ ) ) , ∀ ( _ : ( ε₂ ≤ r ) ) , ∀ ( _ : ( 0 < ε_g ) ) , ∀ ( _ : ( ε_g ≤ r ) ) , ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ( ↥ GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2 ) ) , ( ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt Dist.dist r «ℋ» ) ) ∧ ( ( ∀ ( γ_a γ_g : ℝ ) , ∀ ( _ : ( ε₂ ≤ γ_a ) ) , ∀ ( _ : ( γ_a ≤ r ) ) , ∀ ( _ : ( 0 < γ_g ) ) , ∀ ( _ : ( γ_g < ε_g ) ) , ( GenLimit.MetricSpaces.UniformlyGeneratableAt Dist.dist γ_a γ_g «ℋ» ) ) ∧ ( ( ∀ ( γ_a γ_g : ℝ ) , ∀ ( _ : ( ε₁ ≤ γ_a ) ) , ∀ ( _ : ( γ_a < ε₂ ) ) , ∀ ( _ : ( 0 < γ_g ) ) , ∀ ( _ : ( γ_g < ε_g ) ) , ( ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt Dist.dist γ_a γ_g «ℋ» ) ∧ ( ¬ ( GenLimit.MetricSpaces.UniformlyGeneratableAt Dist.dist γ_a γ_g «ℋ» ) ) ) ) ∧ ( ( ∀ ( γ_a γ_g : ℝ ) , ∀ ( _ : ( 0 < γ_a ) ) , ∀ ( _ : ( γ_a < ε₁ ) ) , ∀ ( _ : ( 0 < γ_g ) ) , ∀ ( _ : ( γ_g < ε_g ) ) , ( ( GenLimit.MetricSpaces.GeneratableInLimitAt Dist.dist γ_a γ_g «ℋ» ) ∧ ( ¬ ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt Dist.dist γ_a γ_g «ℋ» ) ) ) ) ∧ ( ∀ ( γ_a γ_g : ℝ ) , ∀ ( _ : ( 0 < γ_a ) ) , ∀ ( _ : ( γ_a ≤ r ) ) , ∀ ( _ : ( ε_g ≤ γ_g ) ) , ∀ ( _ : ( γ_g ≤ r ) ) , ( ¬ ( GenLimit.MetricSpaces.GeneratableInLimitAt Dist.dist γ_a γ_g «ℋ» ) ) ) ) ) ) )
```

### Theorem 4.10 · `GenLimit.MetricSpaces.Results.theorem_4_10`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( ρ₁ ρ₂ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( M r ε_a ε_g : ℝ ) , ∀ ( _ : ( 0 < M ) ) , ∀ ( _ : ( ∀ ( x y : «𝒳» ) , ( ( ρ₂ x y ) ≤ ( M * ( ρ₁ x y ) ) ) ) ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ( ∀ ( _ : ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt ρ₂ r «ℋ» ) ) , ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt ρ₁ ( r / M ) «ℋ» ) ) ∧ ( ∀ ( _ : ( GenLimit.MetricSpaces.GeneratableInLimitAt ρ₂ ε_a ε_g «ℋ» ) ) , ( GenLimit.MetricSpaces.GeneratableInLimitAt ρ₁ ( ε_a / M ) ( ε_g / M ) «ℋ» ) )
```

### Proposition D.1 · `GenLimit.MetricSpaces.Results.proposition_D_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ DecidableEq «𝒳» ] , ∀ ( ε_a ε_g : ℝ ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( _ : ( 0 ≤ ε_a ) ) , ∀ ( _ : ( ε_a < 1 ) ) , ∀ ( _ : ( 0 ≤ ε_g ) ) , ∀ ( _ : ( ε_g < 1 ) ) , ( ( ( GenLimit.MetricSpaces.GeneratableInLimitAt GenLimit.MetricSpaces.discreteDistance ε_a ε_g «ℋ» ) ↔ ( GenLimit.LiRamanTewari.GeneratableInLimit «ℋ» ) ) ) ∧ ( ( ( ( GenLimit.MetricSpaces.UniformlyGeneratableAt GenLimit.MetricSpaces.discreteDistance ε_a ε_g «ℋ» ) ↔ ( GenLimit.LiRamanTewari.UniformlyGeneratable «ℋ» ) ) ) ∧ ( ( ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt GenLimit.MetricSpaces.discreteDistance ε_a ε_g «ℋ» ) ↔ ( GenLimit.LiRamanTewari.NonuniformlyGeneratable «ℋ» ) ) ) )
```

### Lemma C.1 · `GenLimit.MetricSpaces.Results.lemma_C_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( ρ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( ε_a ε_g : ℝ ) , ∀ ( «ℋ» «𝒮» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( q : ℕ ) , ∀ ( _ : ( 0 < q ) ) , ∀ ( T : ( ( Fin q ) → ( Set «𝒳» ) ) ) , ∀ ( _ : ( ( Set.iInter ( fun i => ( T i ) ) ) = EmptyCollection.emptyCollection ) ) , ∀ ( _ : ( ∀ S ∈ «𝒮» , ( ∀ i : ( Fin q ) , ( ( S ∪ ( T i ) ) ∈ «ℋ» ) ) ) ) , ∀ ( «𝒢» : ( GenLimit.Generic.Generator «𝒳» ) ) , ∀ ( _ : ( GenLimit.MetricSpaces.IsNonuniformGeneratorAt ρ ε_a ε_g «𝒢» «ℋ» ) ) , ∀ S ∈ «𝒮» , depends_only% [ «𝒳» , ρ , ε_a , ε_g , «ℋ» , «𝒮» , q , T , «𝒢» , S ] ( ∃ d_S : ℕ , ∀ ( x : ( ℕ → «𝒳» ) ) , ∀ ( _ : ( GenLimit.Generic.StreamIn x S ) ) , ∀ ( t : ℕ ) , ∀ ( _ : ( GenLimit.MetricSpaces.CoveringNumberAtLeast ρ ε_a ( Finset.toSet ( IRStatement.FirstTerms.firstTerms x t ) ) d_S ) ) , ( ∀ ( s : ℕ ) , t ≤ s → ( ( GenLimit.Generic.output «𝒢» x s ) ∈ ( S \ ( GenLimit.MetricSpaces.closedNeighborhood ρ ( Finset.toSet ( IRStatement.FirstTerms.firstTerms x s ) ) ε_g ) ) ) ) )
```

### Lemma C.2 · `GenLimit.MetricSpaces.Results.lemma_C_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( ρ : ( «𝒳» → ( «𝒳» → ℝ ) ) ) , ∀ ( ε_a ε_g : ℝ ) , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( y : ( List «𝒳» ) ) , ∀ ( x : ( ℕ → ( ℕ → «𝒳» ) ) ) , ∀ ( A : ( ℕ → ( Set «𝒳» ) ) ) , ∀ ( _ : ( GenLimit.MetricSpaces.RowDiagonal.Criterion ρ ε_a ε_g «ℋ» y x A ) ) , ( ¬ ( GenLimit.MetricSpaces.GeneratableInLimitAt ρ ε_a ε_g «ℋ» ) )
```

### Example B.3 · `GenLimit.MetricSpaces.Results.example_B_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( r ε_a ε_g : ℝ ) , ∀ ( _ : ( 0 < r ) ) , ∀ ( _ : ( 0 < ε_a ) ) , ∀ ( _ : ( ε_a < ε_g ) ) , ∀ ( _ : ( ε_g ≤ r ) ) , ( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ( ↥ GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2 ) ) , ( ( ( Set.ncard «ℋ» ) = 2 ) ∧ ( ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt Dist.dist r «ℋ» ) ∧ ( ¬ ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt Dist.dist ε_a ε_g «ℋ» ) ) ) ) )
```

Grammar regression for P21: 1890/1890 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P22

SHA-256 of the checked page: `00bf56baa650913493aa495e22ae710e09719ac573e415a578bcfd8e6b4b7348`

### Theorem 4.1 · `GenLimit.Replay.Results.theorem_4_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Inhabited «𝒳» ] , ∀ ( «ℋ» : ( GenLimit.Generic.LanguageClass «𝒳» ) ) , ∀ ( «d⋆» : ℕ ) , ∀ ( _ : ( 0 < «d⋆» ) ) , ( ( ∃ «𝒢» : ( GenLimit.Generic.Generator «𝒳» ) , ( GenLimit.Generic.IsUniformGeneratorAt «𝒢» «ℋ» «d⋆» ) ) ) ↔ ( ( ∃ «𝒢» : ( GenLimit.Generic.Generator «𝒳» ) , ( GenLimit.Replay.IsUniformReplayGeneratorAt «𝒢» «ℋ» «d⋆» ) ) )
```

### Theorem 5.1 · `GenLimit.Replay.Results.theorem_5_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( GenLimit.Generic.NonuniformlyGeneratable GenLimit.Replay.nonuniformHardClass ) ∧ ( ¬ ( GenLimit.Replay.NonuniformlyGeneratableWithReplay GenLimit.Replay.nonuniformHardClass ) ) )
```

### Theorem 6.1 · `GenLimit.Replay.Results.theorem_6_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( F : ( GenLimit.Replay.CountableDomainOracleFamily «𝒳» ) ) , ∀ [ Countable «𝒳» ] , ( ∃ e : ( «𝒳» ≃ ℕ ) , ( ( GenLimit.Replay.IsLimitReplayGenerator ( GenLimit.Replay.CountableDomainOracleFamily.carriedWitnessProtectionGenerator F e ) ( Set.range ( GenLimit.Replay.CountableDomainOracleFamily.language F ) ) ) ∧ ( GenLimit.OracleFamily.CarriedWitnessProtectionUsesFiniteQueries ( GenLimit.Replay.CountableDomainOracleFamily.encode F e ) ) ) )
```

### Theorem 6.6 · `GenLimit.Replay.Results.theorem_6_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «ℋ» : ( GenLimit.Generic.LanguageClass ( ℤ ⊕ ℕ ) ) , ( ( ¬ ( Set.Countable «ℋ» ) ) ∧ ( ( GenLimit.Generic.UUS «ℋ» ) ∧ ( ( GenLimit.Generic.GeneratableInLimit «ℋ» ) ∧ ( ¬ ( GenLimit.Replay.GeneratableInLimitWithReplay «ℋ» ) ) ) ) ) )
```

### Theorem 7.1 · `GenLimit.Replay.Results.theorem_7_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ¬ ( ∃ «𝒢» : GenLimit.Replay.ProperMembershipAlgorithm , ( ( Computable «𝒢» ) ∧ ( ∀ «ℋ» : GenLimit.LanguageFamily , ( ( GenLimit.Replay.IsRecursiveUUSFamily «ℋ» ) → ( GenLimit.Replay.ProperlyGeneratesInLimitUsingMembership «𝒢» «ℋ» ) ) ) ) ) )
```

### Theorem 7.3 · `GenLimit.Replay.Results.theorem_7_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «ℋ» : ( GenLimit.Replay.HardHypothesis → ( Set ℤ ) ) , ( ( ( Fintype.card GenLimit.Replay.HardHypothesis ) = 4 ) ) ∧ ( ( ( ∀ i : GenLimit.Replay.HardHypothesis , ( Set.Infinite ( «ℋ» i ) ) ) ) ∧ ( ( ¬ ( GenLimit.Replay.ProperlyGeneratableInLimitWithReplay «ℋ» ) ) ) ) )
```

Grammar regression for P22: 588/588 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P23

SHA-256 of the checked page: `eee4633f5b141d20b0a4770e05f9875452ca6a84a13910a556d1986c8ca26405`

### Theorem 2.2 · `GenLimit.KleinbergWei.Banach.Results.theorem_2_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒳» : ( Set ( Set ℕ ) ) , ( ( Set.Countable «𝒳» ) ) ∧ ( ( ( Set.univ ∈ «𝒳» ) ) ∧ ( ( ( ∀ K ∈ «𝒳» , ( Set.Infinite K ) ) ) ∧ ( ∀ ( A : ( ( List ℕ ) → ℕ ) ) , ∀ ( _ : ( ∀ K ∈ «𝒳» , ( ∀ s : ( ℕ → ℕ ) , ( ( Set.range s = K ) → ( ( Function.Injective s ) → ( ∃ T : ℕ , ( ∀ t : ℕ , ( ( t ≥ T ) → ( ( ( A ( GenLimit.textPrefix s t ) ) ∈ K ) ∧ ( ( A ( GenLimit.textPrefix s t ) ) ∉ ( GenLimit.textPrefix s t ) ) ) ) ) ) ) ) ) ) ) , ( ∃ s : ( ℕ → ℕ ) , ( ( Function.Injective s ) ∧ ( ( Set.range s = Set.univ ) ∧ ( ( GenLimit.KleinbergWei.Banach.lowerBanachDensity ( Set.range ( fun t => ( A ( GenLimit.textPrefix s ( t + 1 ) ) ) ) ) ) = 0 ) ) ) ) ) ) ) )
```

### Theorem 4.1 ambient · `GenLimit.KleinbergWei.Banach.Results.theorem_4_1_ambient`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( f : ( ℕ → ( WithTop ℕ ) ) ) , ∀ ( _ : ( Monotone f ) ) , ∀ ( _ : ( ∀ n : ℕ , ( ∃ k : ℕ , ( ( ↑ n ) ≤ ( f k ) ) ) ) ) , ( ∃ «𝒳» : ( Set ( Set ℕ ) ) , ( ( Set.Countable «𝒳» ) ) ∧ ( ( ( ∀ L ∈ «𝒳» , ( Set.Infinite L ) ) ) ∧ ( ( ∃ K : ( Set ℕ ) , ( ( K ∈ «𝒳» ) ) ∧ ( ∀ ( A : ( ( List ℕ ) → ( Finset ℕ ) ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.Banach.Adversary.ValidOn A «𝒳» ) ) , ( ∃ s : ( ℕ → ℕ ) , ( ( Set.range s = K ) ∧ ( ( Function.Injective s ) ∧ ( ( GenLimit.KleinbergWei.Banach.Adversary.ambientRelativeWindowDensity f { x : ℕ | ( ∃ t : ℕ , ( x ∈ ( A ( GenLimit.textPrefix s ( t + 1 ) ) ) ) ) } K ) = 0 ) ) ) ) ) ) ) ) )
```

### Corollary 4.3 · `GenLimit.KleinbergWei.Banach.Results.corollary_4_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝒳» : ( Set ( Set ℕ ) ) , ( ( Set.Countable «𝒳» ) ) ∧ ( ( ( Set.univ ∈ «𝒳» ) ) ∧ ( ( ( ∀ K ∈ «𝒳» , ( Set.Infinite K ) ) ) ∧ ( ∀ ( A : ( ( List ℕ ) → ( Finset ℕ ) ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.Banach.Adversary.ValidOn A «𝒳» ) ) , ( ∃ s : ( ℕ → ℕ ) , ( ( Function.Injective s ) ∧ ( ( Set.range s = Set.univ ) ∧ ( ( GenLimit.KleinbergWei.Banach.lowerBanachDensity { x : ℕ | ( ∃ t : ℕ , ( x ∈ ( A ( GenLimit.textPrefix s ( t + 1 ) ) ) ) ) } ) = 0 ) ) ) ) ) ) ) )
```

### Theorem 4.5 · `GenLimit.KleinbergWei.Banach.Results.theorem_4_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
let O := ( ENNReal.ofReal ( 1 / 2 ) ) ; ( ∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ z : ℕ , ( Set.Infinite ( «𝒳» z ) ) ) ) , ∀ ( R : ℕ ) , ∀ ( _ : ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost ( Set.range «𝒳» ) R ) ) , depends_only% [ «𝒳» , R ] ( ∃ A : ( ( List ℕ ) → ℕ ) , ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ℕ ) ) , let B := { i : ℕ | ( ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( GenLimit.KleinbergWei.OrderedLanguage.increasing (hK := by first | assumption | linarith | positivity | simp_all +zetaDelta) ( «𝒳» z ) ) i ) ∈ ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play A s ) ) ) } ; ∀ ( _ : ( Set.range s = ( «𝒳» z ) ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid s ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play A s ) ( «𝒳» z ) ) ∧ ( O ≤ ( GenLimit.KleinbergWei.Banach.lowerBanachDensity B ) ) ) ) ) ∧ ( ( ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost ( Set.range ( fun ( x : ℕ ) => Set.univ ) ) 1 ) ) ∧ ( ∀ ( A : ( ( List ℕ ) → ℕ ) ) , ∀ ( _ : ( ∀ s : ( ℕ → ℕ ) , ( ( Set.range s = Set.univ ) → ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid s ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play A s ) Set.univ ) ) ) ) , ( ∃ s : ( ℕ → ℕ ) , ( ( Function.Injective s ) ∧ ( ( Set.range s = Set.univ ) ∧ ( ( GenLimit.KleinbergWei.Banach.lowerBanachDensity ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play A s ) ) ) ≤ O ) ) ) ) ) )
```

### Corollary 4.6 · `GenLimit.KleinbergWei.Banach.Results.corollary_4_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ z : ℕ , ( Set.Infinite ( «𝒳» z ) ) ) ) , ∀ ( R : ℕ ) , ∀ ( _ : ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost ( Set.range «𝒳» ) R ) ) , depends_only% [ «𝒳» , R ] ( ∃ A : ( ( List ℕ ) → ℕ ) , ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ℕ ) ) , let B := { i : ℕ | ( ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( GenLimit.KleinbergWei.OrderedLanguage.increasing (hK := by first | assumption | linarith | positivity | simp_all +zetaDelta) ( «𝒳» z ) ) i ) ∈ ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play A s ) ) ) } ; ∀ ( _ : ( Set.range s = ( «𝒳» z ) ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid s ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play A s ) ( «𝒳» z ) ) ) ∧ ( ∀ ( f : ( ℕ → ( WithTop ℕ ) ) ) , ∀ ( _ : ( ( Monotone f ) ∧ ( ∀ k : ℕ , ( 1 ≤ ( f k ) ) ) ) ) , ( ( ENNReal.ofReal ( 1 / 2 ) ) ≤ ( GenLimit.KleinbergWei.Banach.lowerWindowDensity f B ) ) ) )
```

### Corollary 4.7 · `GenLimit.KleinbergWei.Banach.Results.corollary_4_7`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ z : ℕ , ( Set.Infinite ( «𝒳» z ) ) ) ) , ∀ ( R : ℕ ) , ∀ ( _ : ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost ( Set.range «𝒳» ) R ) ) , ∀ ( e : ( ℕ ≃ ℕ ) ) , depends_only% [ «𝒳» , R , e ] ( ∃ A : ( ( List ℕ ) → ℕ ) , ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ℕ ) ) , let B := { i : ℕ | ( ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( GenLimit.KleinbergWei.OrderedLanguage.increasing ( Set.preimage ( DFunLike.coe e ) ( «𝒳» z ) ) ( Set.Infinite.preimage (hs := by first | assumption | linarith | positivity | simp_all +zetaDelta) ( fun x => ( fun ( h : ( Membership.mem ( «𝒳» z ) x ) ) => ( Equiv.surjective e x ) ) ) ) ) i ) ∈ ( Set.preimage ( DFunLike.coe e ) ( Set.range ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play A s ) ) ) ) } ; ∀ ( _ : ( Set.range s = ( «𝒳» z ) ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid s ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play A s ) ( «𝒳» z ) ) ∧ ( ( ENNReal.ofReal ( 1 / 2 ) ) ≤ ( GenLimit.KleinbergWei.Banach.lowerBanachDensity B ) ) ) )
```

### Theorem 5.1 · `GenLimit.KleinbergWei.Banach.Results.theorem_5_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ( ∃ K : ( Set ( GenLimit.KleinbergWei.Banach.Lattice ( d + 2 ) ) ) , ( ( Set.Infinite K ) ) ∧ ( ∀ ( A : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice ( d + 2 ) ) ) → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 2 ) ) ) ) , ∀ ( _ : ( ∀ s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 2 ) ) ) , ( ( Set.range s = K ) → ( ( Function.Injective s ) → ( ∃ T : ℕ , ( ∀ t : ℕ , ( ( t ≥ T ) → ( ( ( A ( GenLimit.textPrefix s t ) ) ∈ K ) ∧ ( ( A ( GenLimit.textPrefix s t ) ) ∉ ( GenLimit.textPrefix s t ) ) ) ) ) ) ) ) ) ) , ( ∃ s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 2 ) ) ) , ( ( Set.range s = K ) ∧ ( ( Function.Injective s ) ∧ ( ( ( GenLimit.KleinbergWei.Banach.Rectangles.lowerDensity ( Set.range ( GenLimit.KleinbergWei.Banach.cubePlay A s ) ) K ) = 0 ) ∧ ( ( GenLimit.KleinbergWei.Banach.Rectangles.outputThresholdDensity ( Set.range ( GenLimit.KleinbergWei.Banach.cubePlay A s ) ) K ) = 0 ) ) ) ) ) ) )
```

### Corollary 5.4 corrected · `GenLimit.KleinbergWei.Banach.Results.corollary_5_4_corrected`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ( ∃ «𝒳» : ( Set ( Set ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) ) , ( ( Set.Countable «𝒳» ) ) ∧ ( ( ( ∀ L ∈ «𝒳» , ( Set.Infinite L ) ) ) ∧ ( ( ∃ K : ( Set ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) , ( ( K ∈ «𝒳» ) ) ∧ ( ∀ ( A : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) → ( Finset ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝒳» , ( ∀ s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) , ( ( Set.range s = L ) → ( ( Function.Injective s ) → ( ∃ T : ℕ , ( ∀ t : ℕ , ( ( t ≥ T ) → ( ∀ x ∈ ( A ( GenLimit.textPrefix s t ) ) , ( ( x ∈ L ) ∧ ( x ∉ ( GenLimit.textPrefix s t ) ) ) ) ) ) ) ) ) ) ) ) , ( ∃ s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) , ( ( Set.range s = K ) ) ∧ ( ( ( Function.Injective s ) ) ∧ ( ∀ ( f : ( ℕ → ℝ ) ) , ∀ ( _ : ( Monotone f ) ) , ∀ ( _ : ( Filter.Tendsto f Filter.atTop Filter.atTop ) ) , ∀ ( _ : ( ∀ n : ℕ , ( ∃ V : ℕ , ( ( 2 ≤ V ) ∧ ( ( n ≤ V ) ∧ ( ( 0 < ( f V ) ) ∧ ( ( ↑ n ) ≤ ( ( ↑ V ) / ( ( f V ) * ( Real.log ( ↑ V ) ) ) ) ) ) ) ) ) ) ) , ( ( GenLimit.KleinbergWei.Banach.filteredRectangularDensityOn GenLimit.KleinbergWei.Banach.MovingCubes.IsCube f { x : ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) | ( ∃ j : ℕ , ( x ∈ ( A ( GenLimit.textPrefix s ( j + 1 ) ) ) ) ) } K ) = 0 ) ) ) ) ) ) ) ) )
```

### Theorem 5.5 on chain targets · `GenLimit.KleinbergWei.Banach.Results.theorem_5_5_on_chain_targets`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ∀ ( e : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( _ : ( Function.Injective e ) ) , ∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ z : ℕ , ( Set.Infinite ( «𝒳» z ) ) ) ) , ∀ ( R : ℕ ) , ∀ ( _ : ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost ( Set.range «𝒳» ) R ) ) , ∀ ( f : ( ℕ → ℝ ) ) , ∀ ( _ : ( Filter.Tendsto f Filter.atTop Filter.atTop ) ) , depends_only% [ d , e , «𝒳» , R , f ] ( ∃ G : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice d ) ) → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) , ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( _ : ( Set.range s = ( Set.image e ( «𝒳» z ) ) ) ) , ( ( GenLimit.KleinbergWei.Banach.cubeValid G s ( Set.image e ( «𝒳» z ) ) ) ) ∧ ( ∀ ( _ : ( ∀ x ∈ ( «𝒳» z ) , ( ∀ y ∈ ( «𝒳» z ) , ( ( ( e x ) ≤ ( e y ) ) ∨ ( ( e y ) ≤ ( e x ) ) ) ) ) ) , ( ( ENNReal.ofReal ( 1 / 2 ) ) ≤ ( GenLimit.KleinbergWei.Banach.filteredRectangularDensity f ( Set.range ( GenLimit.KleinbergWei.Banach.cubePlay G s ) ) ( Set.image e ( «𝒳» z ) ) ) ) ) )
```

### Theorem 5.5 positive occupancy · `GenLimit.KleinbergWei.Banach.Results.theorem_5_5_positive_occupancy`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ∀ ( e : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( _ : ( Function.Injective e ) ) , ∀ ( «𝒳» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ z : ℕ , ( Set.Infinite ( «𝒳» z ) ) ) ) , ∀ ( R : ℕ ) , ∀ ( _ : ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost ( Set.range «𝒳» ) R ) ) , ∀ ( ε ρ : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( _ : ( 0 < ρ ) ) , depends_only% [ d , e , «𝒳» , R , ε , ρ ] ( ∃ A : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice d ) ) → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) , ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( _ : ( Set.range s = ( Set.image e ( «𝒳» z ) ) ) ) , ( ( GenLimit.KleinbergWei.Banach.cubeValid A s ( Set.image e ( «𝒳» z ) ) ) ) ∧ ( ∀ ( f : ( ℕ → ℝ ) ) , ∀ ( _ : ( Filter.Tendsto f Filter.atTop Filter.atTop ) ) , ∀ ( _ : ( ∃ N : ℕ , ( ∀ ( l u : ( GenLimit.KleinbergWei.Banach.Lattice d ) ) , ( ( GenLimit.KleinbergWei.Banach.admissibleBox f ( Set.image e ( «𝒳» z ) ) N ( l , u ) ) → ( ( ρ * ( ↑ ( GenLimit.KleinbergWei.Banach.geometricVolume l u ) ) ) ≤ ( ↑ ( Finset.card ( GenLimit.KleinbergWei.Banach.Rectangles.box ( Set.image e ( «𝒳» z ) ) l u ) ) ) ) ) ) ) ) , ( ( ENNReal.ofReal ( ( 1 / 2 ) - ε ) ) ≤ ( GenLimit.KleinbergWei.Banach.filteredRectangularDensity f ( Set.range ( GenLimit.KleinbergWei.Banach.cubePlay A s ) ) ( Set.image e ( «𝒳» z ) ) ) ) ) )
```

### Corollary 5.7 counterexample · `GenLimit.KleinbergWei.Banach.Results.corollary_5_7_counterexample`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ∀ ( R : ( ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) × ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) ) , ∀ ( _ : ( ∀ i : ( Fin ( d + 1 ) ) , ( ( Prod.fst R i ) < ( Prod.snd R i ) ) ) ) , ∀ ( ε : ℝ ) , ( ∃ «𝒳» : ( ℕ → GenLimit.Language ) , ∃ e : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) , ( ( Function.Injective e ) ) ∧ ( ( ( ∀ z : ℕ , ( Set.Infinite ( «𝒳» z ) ) ) ) ∧ ( ( ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost ( Set.range «𝒳» ) 2 ) ) ∧ ( ( depends_only% [ d , R , ε , «𝒳» , e ] ( ∃ G : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) , ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) ) , ∀ ( _ : ( Set.range s = ( Set.image e ( «𝒳» z ) ) ) ) , ( ( GenLimit.KleinbergWei.Banach.cubeValid G s ( Set.image e ( «𝒳» z ) ) ) ∧ ( ( ENNReal.ofReal ( 1 / 2 ) ) ≤ ( GenLimit.KleinbergWei.Banach.FixedShape.density R ( Set.range ( GenLimit.KleinbergWei.Banach.cubePlay G s ) ) ( Set.image e ( «𝒳» z ) ) ) ) ) ) ) ∧ ( ( ¬ ( ∃ M : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) → ( Set ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) ) , ( ∃ G : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) , ( ∀ z : ℕ , ( ∀ s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) , ( ( Set.range s = ( Set.image e ( «𝒳» z ) ) ) → ( ( Function.Injective s ) → ( ( ∃ T : ℕ , ( ∀ t : ℕ , ( ( t ≥ T ) → ( ( M ( GenLimit.textPrefix s t ) ) = ( Set.image e ( «𝒳» z ) ) ) ) ) ) ∧ ( ( ENNReal.ofReal ( ( 1 / 2 ) - ε ) ) ≤ ( GenLimit.KleinbergWei.Banach.FixedShape.density R ( Set.range ( GenLimit.KleinbergWei.Banach.cubePlay G s ) ) ( Set.image e ( «𝒳» z ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )
```

### Theorem 5.8 · `GenLimit.KleinbergWei.Banach.Results.theorem_5_8`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∀ ( d : ℕ ) , ∀ ( «𝒳» : ( ℕ → ( Set ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) ) , ∀ ( _ : ( ∀ z : ℕ , ( Set.Infinite ( «𝒳» z ) ) ) ) , depends_only% [ d , «𝒳» ] ( ∃ A : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice d ) ) → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) , ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( _ : ( Set.range s = ( «𝒳» z ) ) ) , ( ( GenLimit.KleinbergWei.Banach.cubeValid A s ( «𝒳» z ) ) ∧ ( ( 1 / 2 ) ≤ ( GenLimit.KleinbergWei.Banach.centeredLowerDensity ( Set.range ( GenLimit.KleinbergWei.Banach.cubePlay A s ) ) ( «𝒳» z ) ) ) ) ) ) ∧ ( ∀ ( d : ℕ ) , ( ∃ K : ( Set ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) , ( ( Set.Infinite K ) ) ∧ ( ∀ ( A : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) ) , ∀ ( _ : ( ∀ s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) , ( ( Set.range s = K ) → ( GenLimit.KleinbergWei.Banach.cubeValid A s K ) ) ) ) , ( ∃ s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice ( d + 1 ) ) ) , ( ( Function.Injective s ) ∧ ( ( Set.range s = K ) ∧ ( ( GenLimit.KleinbergWei.Banach.centeredLowerDensity ( Set.range ( GenLimit.KleinbergWei.Banach.cubePlay A s ) ) K ) ≤ ( 1 / 2 ) ) ) ) ) ) ) )
```

### Theorem 5.9 corrected · `GenLimit.KleinbergWei.Banach.Results.theorem_5_9_corrected`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ∀ ( _ : ( 0 < d ) ) , ∀ ( P : ( Set ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( ε α : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( _ : ( 0 < α ) ) , depends_only% [ d , P , ε , α ] ( ∃ χ : ( ( GenLimit.KleinbergWei.Banach.Lattice d ) → Bool ) , ∀ ( l u : ( GenLimit.KleinbergWei.Banach.Lattice d ) ) , let B := ( GenLimit.KleinbergWei.Banach.Rectangles.box P l u ) ; ∀ ( _ : ( Finset.Nonempty B ) ) , let m := ( Finset.card B ) ; let j := ( GenLimit.KleinbergWei.Banach.TierGeometry.tier (positive := by first | assumption | linarith | positivity | simp_all +zetaDelta) ( ( GenLimit.KleinbergWei.Banach.TierGeometry.baseline ε α d ) * ( ( ↑ ( GenLimit.KleinbergWei.Banach.TierGeometry.span l u ) ) ^ α ) ) m ) ; ( ( abs ( Finset.sum B ( fun v => ( GenLimit.KleinbergWei.Banach.RandomSigns.sign ( χ v ) ) ) ) ) ≤ ( GenLimit.KleinbergWei.Banach.TierWeights.threshold ε ( GenLimit.KleinbergWei.Banach.TierGeometry.scale d α ) m j ) ) )
```

Grammar regression for P23: 1298/1298 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P24

SHA-256 of the checked page: `f27dc69759050e140addbb46400b8701694814b921432d3f2aac234ef3deca6a`

### Theorem 3.4 · `GenLimit.PriceOfPrivacy.Results.theorem_3_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒰» : Type _ ) , ∀ [ Countable «𝒰» ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language «𝒰» ) ) ) , ∀ ( «𝒟» : ( PMF «𝒰» ) ) , ∀ ( f n : ℕ ) , let E := ( Real.exp ( ( - ( ↑ n ) ) / ( 8 * ( ( ↑ f ) ^ 2 ) ) ) ) ; ∀ [ NeZero f ] , ∀ ( _ : ( 3 ≤ f ) ) , ∀ ( _ : ( 0 < n ) ) , ∀ ( «i⋆» : ( Fin f ) ) , let R := ( GenLimit.AgnosticLanguage.risk «𝒟» ( «𝒞» ( Fin.val «i⋆» ) ) ) ; ∀ ( _ : ( R = ( GenLimit.AgnosticLanguage.optimalRisk «𝒞» «𝒟» ) ) ) , ∀ ( _ : ( ∀ j : ( Fin f ) , ( ( j < «i⋆» ) → ( ( 3 / ( ↑ f ) ) ≤ ( ( GenLimit.AgnosticLanguage.risk «𝒟» ( «𝒞» ( Fin.val j ) ) ) - R ) ) ) ) ) , ( ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ( ( GenLimit.PriceOfPrivacy.PrivateAt ε 0 n ( GenLimit.PriceOfPrivacy.Identification.pureIdentifier «𝒞» f n ε ) ) ∧ ( ( GenLimit.AgnosticLanguage.idErr «𝒞» ( GenLimit.PriceOfPrivacy.Identification.pureIdentifier «𝒞» f n ε ) «𝒟» n ) ≤ ( ( ( 2 * ( ↑ f ) ) * E ) + ( ( ↑ f ) * ( Real.exp ( ( ( - ε ) * ( ↑ n ) ) / ( 4 * ( ↑ f ) ) ) ) ) ) ) ) ) ∧ ( ∀ ( ε δ : ℝ ) , ∀ ( _ : ( ε ∈ ( Set.Ioo 0 1 ) ) ) , ∀ ( _ : ( δ ∈ ( Set.Ioo 0 1 ) ) ) , ( ( GenLimit.PriceOfPrivacy.PrivateAt ε δ n ( GenLimit.PriceOfPrivacy.Identification.gaussianIdentifier «𝒞» f n ε δ ) ) ∧ ( ( GenLimit.AgnosticLanguage.idErr «𝒞» ( GenLimit.PriceOfPrivacy.Identification.gaussianIdentifier «𝒞» f n ε δ ) «𝒟» n ) ≤ ( ( ( 2 * ( ↑ f ) ) * E ) + ( ( 2 * ( ↑ f ) ) * ( Real.exp ( ( ( - ( ε ^ 2 ) ) * ( ( ↑ n ) ^ 2 ) ) / ( ( 64 * ( ( ↑ f ) ^ 3 ) ) * ( Real.log ( ( 5 / 4 ) / δ ) ) ) ) ) ) ) ) ) )
```

### Theorem 4.4 · `GenLimit.PriceOfPrivacy.Results.theorem_4_4`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒰» : Type _ ) , ∀ ( u : ( ℕ ≃ «𝒰» ) ) , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language «𝒰» ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝒞» i ) ) ) ) , ∀ ( «𝒟» : ( PMF «𝒰» ) ) , ∀ ( f : ℕ ) , ∀ [ NeZero f ] , ∀ ( n W : ℕ ) , let P := ( GenLimit.PriceOfPrivacy.Generation.publicScores u «𝒞» f W ) ; ∀ ( _ : ( 0 < n ) ) , ∀ ( _ : ( GenLimit.PriceOfPrivacy.WitnessBy u «𝒞» «𝒟» W ) ) , ∀ ( t : ( Fin f ) ) , ∀ ( _ : ( binrel% HasSubset.Subset ( «𝒞» ( Fin.val t ) ) ( PMF.support «𝒟» ) ) ) , let m_W := ( GenLimit.PriceOfPrivacy.Generation.massFloor u ( «𝒞» ( Fin.val t ) ) «𝒟» W ) ; let E := ( Real.exp ( ( ( - ( ↑ n ) ) * m_W ) / 8 ) ) ; ( ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ( ( GenLimit.PriceOfPrivacy.PrivateAt ε 0 n ( GenLimit.PriceOfPrivacy.Generation.pureGenerator u «𝒞» n P ε ) ) ∧ ( ( GenLimit.AgnosticLanguage.genErr ( GenLimit.PriceOfPrivacy.Generation.pureGenerator u «𝒞» n P ε ) «𝒟» n ) ≤ ( ( ( ( ↑ W ) * E ) + ( ( ↑ f ) * ( Real.exp ( ( ( ( - ε ) * ( ↑ n ) ) * m_W ) / 4 ) ) ) ) + ( ( ↑ n ) / ( 2 ^ n ) ) ) ) ) ) ∧ ( ∀ ( ε δ : ℝ ) , ∀ ( _ : ( ε ∈ ( Set.Ioo 0 1 ) ) ) , ∀ ( _ : ( δ ∈ ( Set.Ioo 0 1 ) ) ) , ( ( GenLimit.PriceOfPrivacy.PrivateAt ε δ n ( GenLimit.PriceOfPrivacy.Generation.gaussianGenerator u «𝒞» n P ε δ ) ) ∧ ( ( GenLimit.AgnosticLanguage.genErr ( GenLimit.PriceOfPrivacy.Generation.gaussianGenerator u «𝒞» n P ε δ ) «𝒟» n ) ≤ ( ( ( ( ↑ W ) * E ) + ( ( 2 * ( ↑ f ) ) * ( Real.exp ( ( ( ( - ( ε ^ 2 ) ) * ( ( ↑ n ) ^ 2 ) ) * ( m_W ^ 2 ) ) / ( ( 64 * ( ↑ f ) ) * ( Real.log ( ( 5 / 4 ) / δ ) ) ) ) ) ) ) + ( ( ↑ n ) / ( 2 ^ n ) ) ) ) ) )
```

### Theorem 4.5 · `GenLimit.PriceOfPrivacy.Results.theorem_4_5`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒰» : Type _ ) , ∀ ( u : ( ℕ ≃ «𝒰» ) ) , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language «𝒰» ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝒞» i ) ) ) ) , ∀ ( «𝒟» : ( PMF «𝒰» ) ) , ∀ ( f : ℕ ) , ∀ [ NeZero f ] , ∀ ( n W : ℕ ) , ∀ ( _ : ( 0 < W ) ) , ∀ ( _ : ( GenLimit.PriceOfPrivacy.WitnessBy u «𝒞» «𝒟» W ) ) , ∀ ( t : ( Fin f ) ) , ∀ ( _ : ( binrel% HasSubset.Subset ( «𝒞» ( Fin.val t ) ) ( PMF.support «𝒟» ) ) ) , let m_W := ( GenLimit.PriceOfPrivacy.Generation.massFloor u ( «𝒞» ( Fin.val t ) ) «𝒟» W ) ; let E := ( Real.exp ( ( ( - ( ↑ n ) ) * m_W ) / 8 ) ) ; ∀ ( g : ℝ ) , let U := ( GenLimit.PriceOfPrivacy.Generation.unknownScores u «𝒞» f g ) ; ∀ ( _ : ( 0 < g ) ) , ∀ ( _ : ( g ≤ ( ( ( ↑ n ) * m_W ) / 2 ) ) ) , ( ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ( ( GenLimit.PriceOfPrivacy.PrivateAt ε 0 n ( GenLimit.PriceOfPrivacy.Generation.pureGenerator u «𝒞» n U ε ) ) ∧ ( ( GenLimit.AgnosticLanguage.genErr ( GenLimit.PriceOfPrivacy.Generation.pureGenerator u «𝒞» n U ε ) «𝒟» n ) ≤ ( ( ( ( ↑ W ) * E ) + ( ( ↑ f ) * ( Real.exp ( ( ( - ε ) * g ) / ( ( 2 * ( ↑ W ) ) * ( ( ↑ W ) + 1 ) ) ) ) ) ) + ( ( ↑ n ) / ( 2 ^ n ) ) ) ) ) ) ∧ ( ∀ ( ε δ : ℝ ) , ∀ ( _ : ( ε ∈ ( Set.Ioo 0 1 ) ) ) , ∀ ( _ : ( δ ∈ ( Set.Ioo 0 1 ) ) ) , ( ( GenLimit.PriceOfPrivacy.PrivateAt ε δ n ( GenLimit.PriceOfPrivacy.Generation.gaussianGenerator u «𝒞» n U ε δ ) ) ∧ ( ( GenLimit.AgnosticLanguage.genErr ( GenLimit.PriceOfPrivacy.Generation.gaussianGenerator u «𝒞» n U ε δ ) «𝒟» n ) ≤ ( ( ( ( ↑ W ) * E ) + ( ( 2 * ( ↑ f ) ) * ( Real.exp ( ( ( - ( ε ^ 2 ) ) * ( g ^ 2 ) ) / ( ( ( ( 16 * ( ( ↑ W ) ^ 2 ) ) * ( ( ( ↑ W ) + 1 ) ^ 2 ) ) * ( ↑ f ) ) * ( Real.log ( ( 5 / 4 ) / δ ) ) ) ) ) ) ) + ( ( ↑ n ) / ( 2 ^ n ) ) ) ) ) )
```

### Theorem 4.7 · `GenLimit.PriceOfPrivacy.Results.theorem_4_7`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒰» : Type _ ) , ∀ [ Countable «𝒰» ] , ∀ ( u : ( ℕ ≃ «𝒰» ) ) , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language «𝒰» ) ) ) , ∀ ( _ : ( Set.Finite ( Set.range «𝒞» ) ) ) , ∀ ( i j : ℕ ) , ∀ ( _ : ( Set.Infinite ( «𝒞» i ) ) ) , ∀ ( _ : ( Set.Infinite ( «𝒞» j ) ) ) , ∀ ( _ : ( Set.Finite ( ( «𝒞» i ) ∩ ( «𝒞» j ) ) ) ) , ∀ ( «𝒜» : ( ( List «𝒰» ) → ( PMF «𝒰» ) ) ) , ∀ ( _ : ( ∀ q : ( PMF «𝒰» ) , ( ( GenLimit.PriceOfPrivacy.GenerationAssumptions u «𝒞» q ) → ( Filter.Tendsto ( GenLimit.AgnosticLanguage.genErr «𝒜» q ) Filter.atTop ( nhds 0 ) ) ) ) ) , ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( «𝒟» : ( PMF «𝒰» ) ) , ∀ ( _ : ( ( PMF.support «𝒟» ) = ( «𝒞» i ) ) ) , ( ∀ ( _ : ( GenLimit.PriceOfPrivacy.IsPrivate ( ENNReal.ofReal ε ) «𝒜» ) ) , ∀ ( c : ℝ ) , ∀ ( _ : ( 0 < c ) ) , ( ∀ᶠ ( n : ℕ ) in Filter.atTop , ( ( ( 1 / 2 ) * ( Real.exp ( ( - c ) * ( ↑ n ) ) ) ) ≤ ( GenLimit.AgnosticLanguage.genErr «𝒜» «𝒟» n ) ) ) ) ∧ ( ∀ ( δ : ( ℕ → ℝ ) ) , ∀ ( _ : ( ∀ n : ℕ , ( 0 ≤ ( δ n ) ) ) ) , ∀ ( _ : ( ∀ n : ℕ , ( GenLimit.PriceOfPrivacy.PrivateAt ε ( δ n ) n «𝒜» ) ) ) , ∀ ( _ : ( ∃ s : ℝ , ( ( 0 < s ) ∧ ( ∀ n : ℕ , ( ( δ n ) ≤ ( Real.exp ( ( - s ) * ( ↑ n ) ) ) ) ) ) ) ) , ∀ ( c : ℝ ) , ∀ ( _ : ( 0 < c ) ) , ( ∀ᶠ ( n : ℕ ) in Filter.atTop , ( ( ( 1 / 2 ) * ( Real.exp ( ( - c ) * ( ↑ n ) ) ) ) ≤ ( GenLimit.AgnosticLanguage.genErr «𝒜» «𝒟» n ) ) ) )
```

### Theorem 5.2 · `GenLimit.PriceOfPrivacy.Results.theorem_5_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒰» : Type _ ) , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language «𝒰» ) ) ) , ∀ ( _ : ( GenLimit.PriceOfPrivacy.IntersectingPrivatePair «𝒞» ) ) , ( ∃ «𝒟_0» : ( PMF «𝒰» ) , ∃ «𝒟_1» : ( PMF «𝒰» ) , ( ( ∃ i : ℕ , ( ( GenLimit.AgnosticLanguage.risk «𝒟_0» ( «𝒞» i ) ) = ( GenLimit.AgnosticLanguage.optimalRisk «𝒞» «𝒟_0» ) ) ) ) ∧ ( ( ( ∃ j : ℕ , ( ( GenLimit.AgnosticLanguage.risk «𝒟_1» ( «𝒞» j ) ) = ( GenLimit.AgnosticLanguage.optimalRisk «𝒞» «𝒟_1» ) ) ) ) ∧ ( ∀ ( ε : ENNReal ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( «𝒜» : ( GenLimit.AgnosticLanguage.Identifier «𝒰» ) ) , ∀ ( _ : ( GenLimit.PriceOfPrivacy.IsPrivate ε ( GenLimit.PriceOfPrivacy.languageOutput «𝒞» «𝒜» ) ) ) , ( ∀ ( n : ℕ ) , 1 ≤ n → ( ( ( ( ( 1 - ( ( 1 - ( GenLimit.PriceOfPrivacy.retention ε ) ) / 4 ) ) ^ n ) / 8 ) ≤ ( Max.max ( GenLimit.AgnosticLanguage.idErr «𝒞» «𝒜» «𝒟_0» n ) ( GenLimit.AgnosticLanguage.idErr «𝒞» «𝒜» «𝒟_1» n ) ) ) ∧ ( ( ( Real.exp ( ( ( - ( ENNReal.toReal ( Min.min 1 ε ) ) ) * ( ↑ n ) ) / 3 ) ) / 8 ) ≤ ( ( ( 1 - ( ( 1 - ( GenLimit.PriceOfPrivacy.retention ε ) ) / 4 ) ) ^ n ) / 8 ) ) ) ) ) ) )
```

### Theorem 5.4 · `GenLimit.PriceOfPrivacy.Results.theorem_5_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒰» : Type _ ) , ∀ [ Countable «𝒰» ] , ∀ ( «𝒞» : ( ℕ → ( GenLimit.Generic.Language «𝒰» ) ) ) , ∀ ( _ : ( GenLimit.PriceOfPrivacy.IntersectingInfiniteDifferencePair «𝒞» ) ) , ( ∃ «𝒟_0» : ( PMF «𝒰» ) , ∃ «𝒟_1» : ( PMF «𝒰» ) , ( ( Set.Infinite ( PMF.support «𝒟_0» ) ) ) ∧ ( ( ( Set.Infinite ( PMF.support «𝒟_1» ) ) ) ∧ ( ∀ ( ε : ENNReal ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( «𝒜» : ( ( List «𝒰» ) → ( PMF «𝒰» ) ) ) , ∀ ( _ : ( GenLimit.PriceOfPrivacy.IsPrivate ε «𝒜» ) ) , ( ∀ ( n : ℕ ) , 1 ≤ n → ( ( ( ( ( 1 - ( ( 1 - ( GenLimit.PriceOfPrivacy.retention ε ) ) / 4 ) ) ^ n ) / 3 ) ≤ ( Max.max ( GenLimit.AgnosticLanguage.genErr «𝒜» «𝒟_0» n ) ( GenLimit.AgnosticLanguage.genErr «𝒜» «𝒟_1» n ) ) ) ∧ ( ( ( Real.exp ( ( ( - ( ENNReal.toReal ( Min.min 1 ε ) ) ) * ( ↑ n ) ) / 3 ) ) / 3 ) ≤ ( ( ( 1 - ( ( 1 - ( GenLimit.PriceOfPrivacy.retention ε ) ) / 4 ) ) ^ n ) / 3 ) ) ) ) ) ) )
```

Grammar regression for P24: 598/598 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P25

SHA-256 of the checked page: `e3d8e16ad2c1ea0dad8508d758526e9bb12725ffd281cfd542d8df78a5bac3e0`

### Theorem 1.1 · `GenLimit.PrivateLimit.Results.theorem_1_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , depends_only% [ ε ] ( ∃ «𝔾» : ( ( ℕ → GenLimit.Language ) → ( GenLimit.Privacy.ContinualRelease ℕ ℕ ) ) , ∀ ( «𝓛» : ( ℕ → GenLimit.Language ) ) , ( ( GenLimit.Privacy.DifferentiallyPrivate ε 0 ( GenLimit.Privacy.ContinualRelease.law ( «𝔾» «𝓛» ) ) ) ∧ ( GenLimit.PrivateLimit.Epoch.GeneratesOnline ( «𝔾» «𝓛» ) «𝓛» ) ) )
```

### Theorem 1.2 · `GenLimit.PrivateLimit.Results.theorem_1_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( k : ℕ ) , ∀ ( «𝓛» : ( ( Fin k ) → ( Set ℕ ) ) ) , ∀ ( d : ℤ ) , ∀ ( _ : ( ( - 1 ) ≤ d ) ) , ∀ ( _ : ( ∀ V : ( Set ( Set ℕ ) ) , ( ( binrel% HasSubset.Subset V ( Set.range «𝓛» ) ) → ( ( Set.Finite ( Set.sInter V ) ) → ( ( ↑ ( Set.ncard ( Set.sInter V ) ) ) ≤ d ) ) ) ) ) , ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ( ∃ M : ( GenLimit.Privacy.ContinualRelease ℕ ℕ ) , ( ( GenLimit.Privacy.DifferentiallyPrivate ε 0 ( GenLimit.Privacy.ContinualRelease.law M ) ) ) ∧ ( ∀ ( z : ( Fin k ) ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective s ) ) , ∀ ( _ : ( Set.range s ⊆ ( «𝓛» z ) ) ) , ∀ ( m : ℕ ) , let u := ( Int.toNat ( ( ↑ m ) - d ) ) ; ∀ ( _ : ( 33 ≤ u ) ) , ( ( MeasureTheory.Measure.real ( GenLimit.Privacy.ContinualRelease.law M s ) ( GenLimit.PrivateLimit.Epoch.failsAfter ( «𝓛» z ) s ( m - 1 ) ) ) ≤ ( 10 * ( Real.exp ( ( ( - ε ) * ( ↑ u ) ) / ( ( 8 * ( ↑ k ) ) * ( ( ( ↑ ( Nat.log 2 u ) ) + 2 ) ^ 2 ) ) ) ) ) ) ) )
```

### Theorem 1.3 corrected · `GenLimit.PrivateLimit.Results.theorem_1_3_corrected`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( k d : ℕ ) , ∀ ( _ : ( 2 ≤ k ) ) , ( ∃ «𝓛» : ( Set ( Set ℕ ) ) , ( ( Set.Finite «𝓛» ) ) ∧ ( ( ( ( Set.ncard «𝓛» ) = k ) ) ∧ ( ( ( ∀ L ∈ «𝓛» , ( Set.Infinite L ) ) ) ∧ ( ( ∀ ( S : ( Set ( Set ℕ ) ) ) , ∀ ( _ : ( binrel% HasSubset.Subset S «𝓛» ) ) , ∀ ( _ : ( Set.Finite ( Set.sInter S ) ) ) , ( ( Set.ncard ( Set.sInter S ) ) ≤ d ) ) ∧ ( ( ( Set.Finite ( Set.sInter «𝓛» ) ) ) ∧ ( ( ( ( Set.ncard ( Set.sInter «𝓛» ) ) = d ) ) ∧ ( ( ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( M : ( GenLimit.Privacy.ContinualRelease ℕ ℕ ) ) , ∀ ( _ : ( GenLimit.Privacy.DifferentiallyPrivate ε 0 ( GenLimit.Privacy.ContinualRelease.law M ) ) ) , ∀ ( m : ℕ ) , ∀ ( _ : ( 0 < m ) ) , ∀ ( _ : ( GenLimit.PrivateLimit.Packing.UniformFrom M «𝓛» m ) ) , ( ( ( ↑ d ) + ( ( ( GenLimit.PrivateLimit.Packing.coefficient / 3 ) * ( ↑ k ) ) / ε ) ) ≤ ( ↑ m ) ) ) ∧ ( depends_only% [ k , d , «𝓛» ] ( ∃ «𝔾» : ( GenLimit.Generic.Generator ℕ ) , ∀ K ∈ «𝓛» , ∀ ( n : ℕ ) , ∀ ( _ : ( d < n ) ) , ∀ ( xs : ( ( Fin n ) → ℕ ) ) , ∀ ( _ : ( Function.Injective xs ) ) , ∀ ( _ : ( Set.range xs ⊆ K ) ) , ( ( «𝔾» n xs ) ∈ ( K \ ( Set.range xs ) ) ) ) ) ) ) ) ) ) ) )
```

### Theorem 1.5 · `GenLimit.PrivateLimit.Results.theorem_1_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → GenLimit.Language ) ) , ∀ ( i j : ℕ ) , ∀ ( _ : ( ( «𝓛» i ) ≠ ( «𝓛» j ) ) ) , ∀ ( _ : ( Set.Infinite ( ( «𝓛» i ) ∩ ( «𝓛» j ) ) ) ) , ∀ ( _ : ( Set.Finite ( ( «𝓛» i ) \ ( «𝓛» j ) ) ) ) , ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ( ¬ ( ∃ M : ( GenLimit.Privacy.ContinualRelease ℕ ℕ ) , ( ( GenLimit.Privacy.DifferentiallyPrivate ε 0 ( GenLimit.Privacy.ContinualRelease.law M ) ) ∧ ( GenLimit.PrivateLimit.IdentifiesOnline M «𝓛» ) ) ) )
```

### Theorem 1.6 · `GenLimit.PrivateLimit.Results.theorem_1_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → GenLimit.Language ) ) , ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ( ( ∃ M : ( GenLimit.Privacy.ContinualRelease ℕ ℕ ) , ( ( GenLimit.Privacy.DifferentiallyPrivate ε 0 ( GenLimit.Privacy.ContinualRelease.law M ) ) ∧ ( GenLimit.PrivateLimit.IdentifiesStochastically M «𝓛» ) ) ) ) ↔ ( ∀ ( i : ℕ ) , ( ∃ T : ( Finset ℕ ) , ( GenLimit.Angluin.IsTellTale «𝓛» i T ) ) )
```

### Theorem C.5 · `GenLimit.PrivateLimit.Results.theorem_C_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : ( ℕ → GenLimit.Language ) ) , ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ( ( GenLimit.Privacy.DifferentiallyPrivate ε 0 ( GenLimit.Privacy.ContinualRelease.law ( GenLimit.PrivateLimit.OnlineIdentification.identifier «𝓛» ε ) ) ) ) ∧ ( ∀ ( _ : ( ∀ ( i j : ℕ ) , ( ( i ≠ j ) → ( Set.Finite ( ( «𝓛» i ) ∩ ( «𝓛» j ) ) ) ) ) ) , ( GenLimit.PrivateLimit.IdentifiesOnline ( GenLimit.PrivateLimit.OnlineIdentification.identifier «𝓛» ε ) «𝓛» ) )
```

Grammar regression for P25: 598/598 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P26

SHA-256 of the checked page: `eaa255a8a8561d6575f54e8467ee62039c27ad7b01f2d22bb1aab3202b92dbbd`

### Theorem 3.1 · `GenLimit.ComputationalTrace.Results.theorem_3_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ι : Type _ ) , ∀ ( code : ( ι ↪ ℕ ) ) , ∀ ( M : GenLimit.ComputationalTrace.Recognizer ) , ∀ ( _ : ( GenLimit.ComputationalTrace.Recognizer.Deterministic M ) ) , ∀ ( E : ( ℕ → ( GenLimit.ComputationalTrace.Example ι ) ) ) , ∀ ( _ : ( ( ∀ t : ℕ , ( GenLimit.ComputationalTrace.Recognizer.AcceptsTrace M code ( Prod.fst ( E t ) ) ( Prod.snd ( E t ) ) ) ) ∧ ( ( Set.range ( fun t => ( Prod.fst ( E t ) ) ) ) = ( GenLimit.ComputationalTrace.Recognizer.language M code ) ) ) ) , ( ∃ H : GenLimit.ComputationalTrace.Recognizer , ( ( GenLimit.ComputationalTrace.Recognizer.Deterministic H ) ) ∧ ( ( ( ( GenLimit.ComputationalTrace.Recognizer.language H code ) = ( GenLimit.ComputationalTrace.Recognizer.language M code ) ) ) ∧ ( depends_only% [ ι , code , M , E , H ] ( ∃ «t⋆» : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ «t⋆» ) ) , ( ( GenLimit.ComputationalTrace.traceLearner ( GenLimit.textPrefix E t ) ) = H ) ) ) ) )
```

### Theorem 4.1 · `GenLimit.ComputationalTrace.Results.theorem_4_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : ℝ ) , ∀ ( _ : ( ( 0 < α ) ∧ ( α < 1 ) ) ) , ∀ ( «ℓ» : ℕ ) , depends_only% [ α , «ℓ» ] ( ∃ d : ℕ , ∀ ( M : ( GenLimit.ComputationalTrace.BinaryDFA ℕ ) ) , ∀ ( E : ( ℕ → GenLimit.ComputationalTrace.DFAExample ) ) , ∀ ( _ : ( GenLimit.ComputationalTrace.DFAPresentation M α «ℓ» E ) ) , ( ∃ H : GenLimit.ComputationalTrace.DFAHypothesis , ( ( ( GenLimit.ComputationalTrace.BinaryDFA.language ( GenLimit.ComputationalTrace.DFAHypothesis.product H ) ) = ( GenLimit.ComputationalTrace.BinaryDFA.language M ) ) ) ∧ ( depends_only% [ α , «ℓ» , d , M , E , H ] ( ∃ «t⋆» : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ «t⋆» ) ) , ( ( GenLimit.ComputationalTrace.dfaLearner «ℓ» d ( GenLimit.textPrefix E t ) ) = H ) ) ) ) )
```

### Theorem 4.3 · `GenLimit.ComputationalTrace.Results.theorem_4_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∀ ( cut : ( ℝ → ℕ ) ) , ∀ ( P : ( GenLimit.ComputationalTrace.PDA.Program ℕ ) ) , ∀ ( E : ( ℕ → ( GenLimit.ComputationalTrace.Control.Sample GenLimit.ComputationalTrace.PDA.Memory ) ) ) , ∀ ( _ : ( GenLimit.ComputationalTrace.Control.Presentation GenLimit.ComputationalTrace.PDA.device ( GenLimit.ComputationalTrace.PDA.Program.machine P ) ( GenLimit.ComputationalTrace.AllRates cut ) E ) ) , ( GenLimit.IdentifiesInLimit ( fun H => ( GenLimit.ComputationalTrace.Control.Guess.language H GenLimit.ComputationalTrace.PDA.device ) ) ( GenLimit.ComputationalTrace.PDA.learner ( fun ( d : ℕ ) => ( cut ( 1 / ( ( ↑ d ) + 2 ) ) ) ) ) E ( GenLimit.ComputationalTrace.Control.language GenLimit.ComputationalTrace.PDA.device ( GenLimit.ComputationalTrace.PDA.Program.machine P ) ) ) ) ∧ ( ∀ ( α : ℝ ) , ∀ ( _ : ( 0 < α ) ) , ∀ ( H : Type ) , ∀ ( denote : ( H → ( Set ( List Bool ) ) ) ) , ∀ ( learn : ( ( List ( GenLimit.ComputationalTrace.Control.Sample GenLimit.ComputationalTrace.PDA.Memory ) ) → H ) ) , ( ¬ ( ( ∀ P : ( GenLimit.ComputationalTrace.PDA.Program ℕ ) , ( ∀ E : ( ℕ → ( GenLimit.ComputationalTrace.Control.Sample GenLimit.ComputationalTrace.PDA.Memory ) ) , ( ( GenLimit.ComputationalTrace.Control.Presentation GenLimit.ComputationalTrace.PDA.device ( GenLimit.ComputationalTrace.PDA.Program.machine P ) ( GenLimit.ComputationalTrace.RateBound α 1 ) E ) → ( GenLimit.IdentifiesInLimit denote learn E ( GenLimit.ComputationalTrace.Control.language GenLimit.ComputationalTrace.PDA.device ( GenLimit.ComputationalTrace.PDA.Program.machine P ) ) ) ) ) ) ) ) )
```

### Theorem 4.5 · `GenLimit.ComputationalTrace.Results.theorem_4_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∀ ( C «ℓ» : ℕ ) , ∀ ( M : ( GenLimit.ComputationalTrace.Control.Machine ℕ GenLimit.ComputationalTrace.TM.Observation GenLimit.ComputationalTrace.TM.Action ) ) , ∀ ( E : ( ℕ → ( GenLimit.ComputationalTrace.Control.Sample GenLimit.ComputationalTrace.TM.Memory ) ) ) , ∀ ( _ : ( GenLimit.ComputationalTrace.Control.Presentation GenLimit.ComputationalTrace.TM.device M ( GenLimit.ComputationalTrace.FiniteBound C «ℓ» ) E ) ) , ( GenLimit.IdentifiesInLimit ( fun H => ( GenLimit.ComputationalTrace.Control.Guess.language H GenLimit.ComputationalTrace.TM.device ) ) ( GenLimit.ComputationalTrace.Control.learner GenLimit.ComputationalTrace.TM.device C «ℓ» ) E ( GenLimit.ComputationalTrace.Control.language GenLimit.ComputationalTrace.TM.device M ) ) ) ∧ ( ( ∃ cut : ( ℝ → ℕ ) , ∀ ( H : Type ) , ∀ ( denote : ( H → ( Set ( List Bool ) ) ) ) , ∀ ( learn : ( ( List ( GenLimit.ComputationalTrace.Control.Sample GenLimit.ComputationalTrace.TM.Memory ) ) → H ) ) , ( ¬ ( ( ∀ M : ( GenLimit.ComputationalTrace.Control.Machine ℕ GenLimit.ComputationalTrace.TM.Observation GenLimit.ComputationalTrace.TM.Action ) , ( ∀ E : ( ℕ → ( GenLimit.ComputationalTrace.Control.Sample GenLimit.ComputationalTrace.TM.Memory ) ) , ( ( GenLimit.ComputationalTrace.Control.Presentation GenLimit.ComputationalTrace.TM.device M ( GenLimit.ComputationalTrace.AllRates cut ) E ) → ( GenLimit.IdentifiesInLimit denote learn E ( GenLimit.ComputationalTrace.Control.language GenLimit.ComputationalTrace.TM.device M ) ) ) ) ) ) ) ) )
```

Grammar regression for P26: 396/396 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P27

SHA-256 of the checked page: `ba533a0dc82e0934f135db0071fc84121db0fbcd18fdc282f5c561a3b50ca23a`

### Theorem 3.1 · `GenLimit.FeedbackQueries.Results.theorem_3_1`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «𝓛» : ( Set ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝓛» , ( Set.Infinite L ) ) ) , ( ( GenLimit.FeedbackQueries.SourceElementMistakeGeneratable «𝓛» ) ↔ ( GenLimit.FeedbackQueries.HasCountableInnerCover «𝓛» ) )
```

### Theorem 3.2 · `GenLimit.FeedbackQueries.Results.theorem_3_2`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «𝓛» : ( Set ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝓛» , ( Set.Infinite L ) ) ) , ( ( GenLimit.FeedbackQueries.SourceSetMistakeGeneratable «𝓛» ) ↔ ( GenLimit.FeedbackQueries.SourceElementMistakeGeneratable «𝓛» ) )
```

### Theorem 3.3 · `GenLimit.FeedbackQueries.Results.theorem_3_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝓛» : ( Set ( GenLimit.Generic.Language ℕ ) ) , ( ( GenLimit.FeedbackQueries.SourceElementQueryGeneratable «𝓛» ) ∧ ( ¬ ( GenLimit.FeedbackQueries.SourceSetQueryGeneratable «𝓛» ) ) ) )
```

### Theorem 3.4 · `GenLimit.FeedbackQueries.Results.theorem_3_4`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «𝓛» : ( Set ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝓛» , ( Set.Infinite L ) ) ) , ( ( GenLimit.FeedbackQueries.SourceSetQueryGeneratable «𝓛» ) ↔ ( GenLimit.FeedbackQueries.HasCountableInnerCover «𝓛» ) )
```

### Corollary 3.6 · `GenLimit.FeedbackQueries.Results.corollary_3_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «𝓛» : ( ℕ → ( Set ( GenLimit.Generic.Language «𝒳» ) ) ) ) , ∀ ( _ : ( ∀ i : ℕ , ( ∀ L ∈ ( «𝓛» i ) , ( Set.Infinite L ) ) ) ) , ( ∀ ( _ : ( ∀ i : ℕ , ( GenLimit.FeedbackQueries.SourceElementMistakeGeneratable ( «𝓛» i ) ) ) ) , ( GenLimit.FeedbackQueries.SourceElementMistakeGeneratable ( Set.iUnion ( fun i => ( «𝓛» i ) ) ) ) ) ∧ ( ∀ ( _ : ( ∀ i : ℕ , ( GenLimit.FeedbackQueries.SourceSetQueryGeneratable ( «𝓛» i ) ) ) ) , ( GenLimit.FeedbackQueries.SourceSetQueryGeneratable ( Set.iUnion ( fun i => ( «𝓛» i ) ) ) ) )
```

### Corollary 3.7 · `GenLimit.FeedbackQueries.Results.corollary_3_7`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «𝓛» : ( Set ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝓛» , ( Set.Infinite L ) ) ) , ( ∀ ( _ : ( GenLimit.FeedbackQueries.SourceElementMistakeGeneratable «𝓛» ) ) , ( GenLimit.FeedbackQueries.ZeroExampleElementMistakeGeneratable «𝓛» ) ) ∧ ( ∀ ( _ : ( GenLimit.FeedbackQueries.SourceSetQueryGeneratable «𝓛» ) ) , ( GenLimit.FeedbackQueries.ZeroExampleSetQueryGeneratable «𝓛» ) )
```

### Corollary 3.8 · `GenLimit.FeedbackQueries.Results.corollary_3_8`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «𝓛» : ( Set ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝓛» , ( Set.Infinite L ) ) ) , ( ( ( GenLimit.FeedbackQueries.EventuallyCorrectMistakeGeneratable «𝓛» ) ↔ ( GenLimit.FeedbackQueries.HasCountableInnerCover «𝓛» ) ) ) ∧ ( ( ( GenLimit.FeedbackQueries.EventuallyCorrectQueryGeneratable «𝓛» ) ↔ ( GenLimit.FeedbackQueries.HasCountableInnerCover «𝓛» ) ) )
```

### Theorem 3.9 · `GenLimit.FeedbackQueries.Results.theorem_3_9`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «𝓛» : ( Set ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝓛» , ( Set.Infinite L ) ) ) , ( ( GenLimit.Generic.SetGeneratableInLimit «𝓛» ) ↔ ( GenLimit.Generic.GeneratableInLimit «𝓛» ) )
```

### Theorem 3.10 · `GenLimit.FeedbackQueries.Results.theorem_3_10`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «𝓛» : ( Set ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( _ : ( ∀ L ∈ «𝓛» , ( Set.Infinite L ) ) ) , ( ∀ ( _ : ( GenLimit.FeedbackQueries.HasFiniteInnerCover «𝓛» ) ) , ( GenLimit.Generic.GeneratableInLimit «𝓛» ) ) ∧ ( ( ∀ ( _ : ( GenLimit.Generic.GeneratableInLimit «𝓛» ) ) , ( GenLimit.FeedbackQueries.HasCountableInnerCover «𝓛» ) ) ∧ ( ( ( ∃ K : ( Set ( GenLimit.Generic.Language ( ℕ ⊕ ( ℕ × ℕ ) ) ) ) , ( ( ∀ L ∈ K , ( Set.Infinite L ) ) ) ∧ ( ( ( GenLimit.FeedbackQueries.HasCountableInnerCover K ) ) ∧ ( ( ¬ ( GenLimit.Generic.GeneratableInLimit K ) ) ) ) ) ) ∧ ( ( ( ∃ K : ( Set ( GenLimit.Generic.Language ℕ ) ) , ( ( ∀ L ∈ K , ( Set.Infinite L ) ) ) ∧ ( ( ( GenLimit.Generic.GeneratableInLimit K ) ) ∧ ( ( GenLimit.FeedbackQueries.HasCountableInnerCover K ) ) ) ) ) ∧ ( ( ∃ K : ( Set ( GenLimit.Generic.Language ( ℕ × ℕ ) ) ) , ( ( ∀ L ∈ K , ( Set.Infinite L ) ) ) ∧ ( ( ( GenLimit.Generic.GeneratableInLimit K ) ) ∧ ( ( ¬ ( GenLimit.FeedbackQueries.HasFiniteInnerCover K ) ) ) ) ) ) ) ) )
```

Grammar regression for P27: 892/892 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P28

SHA-256 of the checked page: `adcb161a81b0f50c3629f455ef1c0e97faa20879a632cd7088307603124aece5`

### Infinite defect identification · `GenLimit.ContrastiveGeneration.Results.infinite_defect_identification`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( ∀ ( i j : ℕ ) , ( ( ( F i ) ≠ ( F j ) ) → ( ( GenLimit.ContrastiveGeneration.defectNumber ( F i ) ( F j ) ) = Top.top ) ) ) ) , ( GenLimit.ContrastiveGeneration.FinitelyCorruptionContrastivelyIdentifiable F )
```

### Proposition 4.2 · `GenLimit.ContrastiveGeneration.Results.proposition_4_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( h g : ( Set α ) ) , ∀ x₀ ∈ h , ∀ ( enumeration : ( ℕ → α ) ) , ∀ ( _ : ( binrel% HasSubset.Subset h ( Set.range enumeration ) ) ) , ( ( GenLimit.ContrastiveGeneration.NotEliminableFrom g h ) ↔ ( binrel% HasSubset.Subset h ( GenLimit.ContrastiveGeneration.commonVertices h g ) ) )
```

### Theorem 4.3 · `GenLimit.ContrastiveGeneration.Results.theorem_4_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( h g : ( Set α ) ) , ( ( ( binrel% HasSubset.Subset h ( GenLimit.ContrastiveGeneration.commonVertices h g ) ) ) ↔ ( ( ∀ ( _ : ( Set.Nonempty ( h ∩ g ) ) ) , ( Set.Nonempty ( HasCompl.compl ( h ∪ g ) ) ) ) ∧ ( ∀ ( _ : ( Set.Nonempty ( h \ g ) ) ) , ( Set.Nonempty ( g \ h ) ) ) ) ) ∧ ( ∀ [ Countable α ] , ∀ ( _ : ( Set.Nonempty h ) ) , ∀ ( _ : ( Set.Nonempty ( HasCompl.compl g ) ) ) , ∀ ( _ : ( h ≠ g ) ) , ( ( GenLimit.ContrastiveGeneration.NotEliminableFrom g h ) ) ↔ ( ( ( HasSSubset.SSubset h g ) ) ∨ ( ( ( ( GenLimit.ContrastiveGeneration.Incomparable h g ) ∧ ( Disjoint h g ) ) ) ∨ ( ( ( GenLimit.ContrastiveGeneration.Incomparable h g ) ∧ ( ( Set.Nonempty ( h ∩ g ) ) ∧ ( ( h ∪ g ) ≠ Set.univ ) ) ) ) ) ) )
```

### Theorem 4.7 · `GenLimit.ContrastiveGeneration.Results.theorem_4_7`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Nonempty α ] , ∀ [ Countable α ] , ∀ [ Infinite α ] , ∀ ( F : ( ℕ → ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( GenLimit.ContrastiveGeneration.AllProperNontrivial F ) ) , ( ( GenLimit.ContrastiveGeneration.ContrastivelyIdentifiable F ) ) ↔ ( ( ( GenLimit.ContrastiveGeneration.TextIdentifiable F ) ) ∧ ( ∀ h_3 ∈ ( Set.range F ) , ∀ g ∈ ( Set.range F ) , ∀ ( _ : ( GenLimit.ContrastiveGeneration.Incomparable h_3 g ) ) , ( GenLimit.ContrastiveGeneration.OverlappingCover h_3 g ) ) )
```

### Theorem 5.4 · `GenLimit.ContrastiveGeneration.Results.theorem_5_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Nonempty α ] , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ( ( ( GenLimit.ContrastiveGeneration.UniformlyContrastivelyGeneratable «𝓗» ) ↔ ( GenLimit.ContrastiveGeneration.FiniteContrastiveClosureDimension «𝓗» ) ) ) ∧ ( ∀ ( d : ℕ ) , ∀ ( _ : ( GenLimit.ContrastiveGeneration.ContrastiveClosureDimensionEquals «𝓗» d ) ) , ( GenLimit.ContrastiveGeneration.IsLeastPositiveUniformThreshold «𝓗» ( d + 1 ) ) )
```

### Theorem 5.5 · `GenLimit.ContrastiveGeneration.Results.theorem_5_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Nonempty α ] , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ( ( GenLimit.ContrastiveGeneration.NonuniformlyContrastivelyGeneratable «𝓗» ) ) ↔ ( ( ∃ classes : ( ℕ → ( Set ( Set α ) ) ) , ( ( ( Monotone classes ) ∧ ( «𝓗» = ( Set.iUnion ( fun n => ( classes n ) ) ) ) ) ) ∧ ( ( ∀ n : ℕ , ( GenLimit.ContrastiveGeneration.FiniteContrastiveClosureDimension ( classes n ) ) ) ) ) )
```

### Proposition 5.8 · `GenLimit.ContrastiveGeneration.Results.proposition_5_8`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Nonempty α ] , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ∀ ( _ : ( ∀ h_1 ∈ «𝓗» , ( ∀ P : ( ℕ → ( GenLimit.ContrastiveGeneration.Edge α ) ) , ( ( GenLimit.ContrastiveGeneration.IsContrastivePresentation P h_1 ) → ( ∀ t : ℕ , ( Set.Infinite ( GenLimit.ContrastiveGeneration.edgeClosure «𝓗» ( GenLimit.ContrastiveGeneration.streamPrefix P t ) ) ) ) ) ) ) ) , ( GenLimit.ContrastiveGeneration.ContrastivelyGeneratable «𝓗» )
```

### Proposition 5.11 · `GenLimit.ContrastiveGeneration.Results.proposition_5_11`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ∀ ( core : ( ℕ → α ) ) , ∀ ( _ : ( GenLimit.ContrastiveGeneration.IsEventualCore «𝓗» core ) ) , ( GenLimit.ContrastiveGeneration.ContrastivelyGeneratable «𝓗» )
```

### Proposition 5.12 · `GenLimit.ContrastiveGeneration.Results.proposition_5_12`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ∀ ( «ℱ» : ( Finset ( Set α ) ) ) , ∀ ( core : ( Finset α ) ) , ∀ ( P : ( ℕ → ( GenLimit.ContrastiveGeneration.Edge α ) ) ) , ∀ ( _ : ( Finset.Nonempty «ℱ» ) ) , ∀ ( _ : ( ∀ h ∈ «ℱ» , ( h ∈ «𝓗» ) ) ) , ∀ ( _ : ( GenLimit.ContrastiveGeneration.IsSharedPresentation P «ℱ» ) ) , ∀ ( _ : ( ∀ x : α , ( ( x ∈ core ) ↔ ( ∀ h ∈ «ℱ» , ( x ∈ h ) ) ) ) ) , ( ¬ ( GenLimit.ContrastiveGeneration.ContrastivelyGeneratable «𝓗» ) )
```

### Theorem 5.13 · `GenLimit.ContrastiveGeneration.Results.theorem_5_13`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
let CI := ( GenLimit.ContrastiveGeneration.cleanFamilies GenLimit.ContrastiveGeneration.ContrastivelyIdentifiable ) ; let TI := ( GenLimit.ContrastiveGeneration.cleanFamilies GenLimit.ContrastiveGeneration.TextIdentifiable ) ; let CG := ( GenLimit.ContrastiveGeneration.cleanFamilies ( fun F => ( GenLimit.ContrastiveGeneration.ContrastivelyGeneratable ( Set.range F ) ) ) ) ; let TG := ( GenLimit.ContrastiveGeneration.cleanFamilies ( fun F => ( GenLimit.Generic.GeneratableInLimit ( Set.range F ) ) ) ) ; ( ( HasSSubset.SSubset CI CG ) ) ∧ ( ( ( HasSSubset.SSubset CG TG ) ) ∧ ( ( ( HasSSubset.SSubset CI TI ) ) ∧ ( ( HasSSubset.SSubset TI TG ) ) ) )
```

### Theorem 5.14 · `GenLimit.ContrastiveGeneration.Results.theorem_5_14`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
let CG := ( GenLimit.ContrastiveGeneration.cleanFamilies ( fun F => ( GenLimit.ContrastiveGeneration.ContrastivelyGeneratable ( Set.range F ) ) ) ) ; let TI := ( GenLimit.ContrastiveGeneration.cleanFamilies GenLimit.ContrastiveGeneration.TextIdentifiable ) ; ( ( ¬ ( binrel% HasSubset.Subset CG TI ) ) ∧ ( ¬ ( binrel% HasSubset.Subset TI CG ) ) )
```

### Proposition 6.3 · `GenLimit.ContrastiveGeneration.Results.proposition_6_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Countable α ] , ∀ ( h_1 g : ( Set α ) ) , let κ := ( GenLimit.ContrastiveGeneration.defectNumber h_1 g ) ; ∀ ( _ : ( h_1 ≠ g ) ) , ∀ ( _ : ( GenLimit.ContrastiveGeneration.ProperNontrivialSupport h_1 ) ) , ∀ ( _ : ( GenLimit.ContrastiveGeneration.ProperNontrivialSupport g ) ) , ( ( ( GenLimit.ContrastiveGeneration.forcedWrongCutViolationInfimum h_1 g ) = κ ) ) ∧ ( ( ( GenLimit.ContrastiveGeneration.NotEliminableFrom g h_1 ) ↔ ( κ = 0 ) ) )
```

### Theorem 6.5 · `GenLimit.ContrastiveGeneration.Results.theorem_6_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ¬ ( GenLimit.ContrastiveGeneration.KTextIdentifiable 1 GenLimit.ContrastiveGeneration.coSingletonFamily ) )
```

### Theorem 6.6 · `GenLimit.ContrastiveGeneration.Results.theorem_6_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.ContrastiveGeneration.FinitelyCorruptionContrastivelyIdentifiable GenLimit.ContrastiveGeneration.coSingletonFamily )
```

### Theorem 6.8 · `GenLimit.ContrastiveGeneration.Results.theorem_6_8`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( k : ℕ ) , ∀ ( _ : 1 ≤ k ) , let «ℋ_k» := ( GenLimit.ContrastiveGeneration.robustBlockFamily k ) ; ( ( ( GenLimit.ContrastiveGeneration.KContrastivelyIdentifiable k GenLimit.ContrastiveGeneration.coSingletonFamily ) ∧ ( ¬ ( GenLimit.ContrastiveGeneration.KTextIdentifiable k GenLimit.ContrastiveGeneration.coSingletonFamily ) ) ) ) ∧ ( ( ( GenLimit.ContrastiveGeneration.KTextIdentifiable k «ℋ_k» ) ) ∧ ( ( ¬ ( GenLimit.ContrastiveGeneration.KContrastivelyIdentifiable k «ℋ_k» ) ) ) )
```

Grammar regression for P28: 1475/1475 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P29

SHA-256 of the checked page: `67319952e52c26a9df267bb920d091727397b63e20933b9575d241e41c72a470`

### Theorem 4.1 · `GenLimit.MistakeBounded.Results.theorem_4_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Infinite «𝒳» ] , ∀ ( f : ( ℕ → ℕ ) ) , ∀ ( w_0 : ( ℕ → ℝ ) ) , ∀ ( L : ( ℕ → ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( x : ( GenLimit.Generic.Stream «𝒳» ) ) , ∀ ( _ : ( Monotone f ) ) , ∀ ( _ : ( ∀ i : ℕ , ( 0 ≤ ( w_0 i ) ) ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( W : ℝ ) , ∀ ( _ : ( ∀ n : ℕ , ( ( Finset.sum ( Finset.range n ) ( fun i => ( w_0 i ) ) ) ≤ W ) ) ) , ∀ ( target activation budget : ℕ ) , ∀ ( _ : ( ( target < ( f activation ) ) ∧ ( ∀ ( t : ℕ ) , t < activation → ( ( f t ) ≤ target ) ) ) ) , ∀ ( _ : ( ∀ t : ℕ , ( ( x t ) ∈ ( L target ) ) ) ) , ∀ ( _ : ( 0 < ( w_0 target ) ) ) , ∀ ( _ : ( GenLimit.MistakeBounded.DyadicUpperBudget W ( w_0 target ) budget ) ) , ( GenLimit.MistakeBounded.TotalMistakesAtMost ( GenLimit.MistakeBounded.countableTargetTrace L ( GenLimit.MistakeBounded.countableSemanticGenerated f w_0 L x ) target ) ( activation + budget ) )
```

### Theorem 5.1 · `GenLimit.MistakeBounded.Results.theorem_5_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Infinite «𝒳» ] , ∀ ( N : ℕ ) , ∀ ( L : ( ( Fin N ) → ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( x : ( GenLimit.Generic.Stream «𝒳» ) ) , ∀ ( target : ( Fin N ) ) , ∀ ( _ : ( ∀ t : ℕ , ( ( x t ) ∈ ( L target ) ) ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( d : ℕ ) , ∀ ( _ : ( GenLimit.MistakeBounded.FiniteClassClosureDimensionAtMost L d ) ) , ( ( GenLimit.MistakeBounded.TotalMistakesAtMost ( GenLimit.MistakeBounded.finiteTargetTrace L ( GenLimit.MistakeBounded.finiteSemanticGenerated L x ) target ) ( Min.min ( Nat.log 2 N ) ( d + 1 ) ) ) ∧ ( GenLimit.MistakeBounded.LastMistakeBefore ( GenLimit.MistakeBounded.finiteTargetTrace L ( GenLimit.MistakeBounded.finiteSemanticGenerated L x ) target ) ( d + 1 ) ) )
```

### Theorem 6.1 · `GenLimit.MistakeBounded.Results.theorem_6_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Infinite «𝒳» ] , ∀ ( L : ( ℕ → ( GenLimit.Generic.Language «𝒳» ) ) ) , ∀ ( x : ( GenLimit.Generic.Stream «𝒳» ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( target : ℕ ) , ∀ ( _ : ( ∀ t : ℕ , ( ( x t ) ∈ ( L target ) ) ) ) , ( GenLimit.MistakeBounded.TotalMistakesAtMost ( GenLimit.MistakeBounded.countableTargetTrace L ( GenLimit.MistakeBounded.countableSemanticGenerated ( fun t => ( 2 ^ ( t + 1 ) ) ) ( fun ( i : ℕ ) => ( 1 / ( ( ↑ ( i + 1 ) ) ^ 2 ) ) ) L x ) target ) ( ( Nat.pred ( Nat.clog 2 ( target + 1 ) ) ) + ( GenLimit.MistakeBounded.polynomialPriorLogBudget target ) ) )
```

### Theorem 6.4 printed false · `GenLimit.MistakeBounded.Results.theorem_6_4_printed_false`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Infinite «𝒳» ] , ( ¬ ( ∃ L : ( ℕ → ( GenLimit.Generic.Language «𝒳» ) ) , ( ( ∀ i : ℕ , ( Set.Infinite ( L i ) ) ) ∧ ( ∀ «𝒢» : ( GenLimit.Generic.Generator «𝒳» ) , ( ( ∀ t : ℕ , ( ∀ xs : ( ( Fin t ) → «𝒳» ) , ( ( «𝒢» t xs ) ∉ ( GenLimit.Generic.sequenceSample xs ) ) ) ) → ( ( ∃ C : ℕ , ( ∀ i : ℕ , ( ∀ s : ( GenLimit.MistakeBounded.PositiveRun ( L i ) ) , ( GenLimit.MistakeBounded.LastMistakeBefore ( GenLimit.MistakeBounded.countableTargetTrace L ( GenLimit.Generic.output «𝒢» ( ↑ s ) ) i ) ( C * ( Max.max ( i + 1 ) ( GenLimit.MistakeBounded.prefixComplexity L i ) ) ) ) ) ) ) → ( ∀ ( i : ℕ ) , 1 ≤ i → ( ( ↑ i ) ≤ ( GenLimit.MistakeBounded.worstCaseMistakes ( fun ( s : ( GenLimit.MistakeBounded.PositiveRun ( L i ) ) ) => ( GenLimit.MistakeBounded.countableTargetTrace L ( GenLimit.Generic.output «𝒢» ( ↑ s ) ) i ) ) ) ) ) ) ) ) ) ) )
```

Grammar regression for P29: 400/400 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P30

SHA-256 of the checked page: `c997f780c14171111e534f54ca6d840ba65c1a6bd7eeadc951a84a28382a8fee`

### Theorem 1 · `GenLimit.TimeSensitive.Results.theorem_1`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Ω : Type _ ) , ∀ [ MeasurableSpace Ω ] , ∀ ( μ : ( MeasureTheory.Measure Ω ) ) , ∀ [ MeasureTheory.IsProbabilityMeasure μ ] , ∀ ( «𝒜» : ( GenLimit.TimeSensitive.RandomizedGenerator Ω ) ) , ∀ ( D : ( ℕ → ℕ ) ) , ∀ ( _ : ( ∀ z : ℕ , ( ∀ E : ( ℕ → ℕ ) , ( ( Set.range E = ( GenLimit.TimeSensitive.sparseFamily z ) ) → ( Filter.Eventually ( fun ω => ( ∀ᶠ ( t : ℕ ) in Filter.atTop , ( ( GenLimit.TimeSensitive.RandomizedGenerator.run «𝒜» E ω t ) ∈ ( GenLimit.TimeSensitive.sparseFamily z ) ) ) ) ( MeasureTheory.ae μ ) ) ) ) ) ) , ( ∃ E : ( ℕ → ℕ ) , ( ( Set.range E = ( GenLimit.TimeSensitive.sparseFamily 0 ) ) ∧ ( Filter.Eventually ( fun ω => ( ( Filter.liminf ( GenLimit.TimeSensitive.timelyDensity ( GenLimit.TimeSensitive.RandomizedGenerator.run «𝒜» E ω ) id D ) Filter.atTop ) = 0 ) ) ( MeasureTheory.ae μ ) ) ) )
```

### Theorem 2 · `GenLimit.TimeSensitive.Results.theorem_2`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Ω : Type _ ) , ∀ [ MeasurableSpace Ω ] , ∀ ( μ : ( MeasureTheory.Measure Ω ) ) , ∀ [ MeasureTheory.IsProbabilityMeasure μ ] , ∀ ( «𝒜» : ( GenLimit.TimeSensitive.RandomizedGenerator Ω ) ) , ∀ ( D : ( ℕ → ℕ ) ) , ∀ ( _ : ( ∃ c : ℕ , ( ∀ᶠ ( j : ℕ ) in Filter.atTop , ( ( D j ) ≤ ( c * ( j + 1 ) ) ) ) ) ) , ∀ ( _ : ( ∀ z : ℕ , ( ∀ E : ( ℕ → ℕ ) , ( ( Set.range E = ( GenLimit.TimeSensitive.sparseFamily z ) ) → ( Filter.Tendsto ( GenLimit.TimeSensitive.RandomizedGenerator.expectedRate «𝒜» μ E ( GenLimit.TimeSensitive.sparseFamily z ) ) Filter.atTop ( nhds 0 ) ) ) ) ) ) , ( ∃ E : ( ℕ → ℕ ) , ( ( Set.range E = ( GenLimit.TimeSensitive.sparseFamily 0 ) ) ∧ ( Filter.Eventually ( fun ω => ( ( Filter.liminf ( GenLimit.TimeSensitive.timelyDensity ( GenLimit.TimeSensitive.RandomizedGenerator.run «𝒜» E ω ) id D ) Filter.atTop ) = 0 ) ) ( MeasureTheory.ae μ ) ) ) )
```

### Theorem 3 uniform bound false · `GenLimit.TimeSensitive.Results.theorem_3_uniform_bound_false`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Ω : Type _ ) , ∀ [ MeasurableSpace Ω ] , ∀ ( μ : ( MeasureTheory.Measure Ω ) ) , ∀ [ MeasureTheory.IsProbabilityMeasure μ ] , ∀ ( «𝒜» : ( GenLimit.TimeSensitive.RandomizedGenerator Ω ) ) , ∀ ( H : ( ℕ → ℝ ) ) , ∀ ( _ : ( Filter.Tendsto H Filter.atTop ( nhds 0 ) ) ) , ( ¬ ( ( ∀ᶠ ( t : ℕ ) in Filter.atTop , ( ∀ z : ℕ , ( ∀ E : ( ℕ → ℕ ) , ( ( Set.range E = ( GenLimit.TimeSensitive.sharedRoot z ) ) → ( ( GenLimit.TimeSensitive.RandomizedGenerator.expectedRate «𝒜» μ E ( GenLimit.TimeSensitive.sharedRoot z ) t ) ≤ ( H t ) ) ) ) ) ) ) )
```

### Theorem 4 · `GenLimit.TimeSensitive.Results.theorem_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : GenLimit.TimeSensitive.CanonicallyOrderedFamily ) , ∀ ( z : ℕ ) , let R := ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( GenLimit.TimeSensitive.CanonicallyOrderedFamily.order «𝓛» z ) ) ; let K := ( GenLimit.TimeSensitive.CanonicallyOrderedFamily.language «𝓛» z ) ; ∀ ( _ : ( ∀ ( i : ℕ ) , i < z → ( ( GenLimit.TimeSensitive.CanonicallyOrderedFamily.language «𝓛» i ) ≠ K ) ) ) , ( ∀ ( E : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range E = K ) ) , ( depends_only% [ «𝓛» , z , E ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( ( GenLimit.TimeSensitive.totalizedGCGOutput «𝓛» E t ) ∈ K ) ) ) ) ∧ ( ( ( 1 / 2 ) ≤ ( Filter.limsup ( GenLimit.TimeSensitive.timelyDensity ( GenLimit.TimeSensitive.totalizedGCGOutput «𝓛» E ) R id ) Filter.atTop ) ) ) ) ∧ ( ( ∃ E : ( ℕ → ℕ ) , ( ( Set.range E = K ) ) ∧ ( ( depends_only% [ «𝓛» , z , E ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( ( GenLimit.TimeSensitive.totalizedGCGOutput «𝓛» E t ) ∈ K ) ) ) ) ∧ ( ( ( Filter.limsup ( GenLimit.TimeSensitive.timelyDensity ( GenLimit.TimeSensitive.totalizedGCGOutput «𝓛» E ) R id ) Filter.atTop ) = ( 1 / 2 ) ) ) ) ) )
```

Grammar regression for P30: 399/399 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P31

SHA-256 of the checked page: `9f16113fab0ed203600641909295017ebbd630b43721982b595e23f11f5ba1b8`

### Theorem 1.1 · `GenLimit.BoundedMemory.Results.theorem_1_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «𝓛» : ( Set ( Set «𝒳» ) ) ) , ∀ ( _ : ( Set.Countable «𝓛» ) ) , ∀ ( _ : ( ∀ K ∈ «𝓛» , ( Set.Infinite K ) ) ) , depends_only% [ «𝒳» , «𝓛» ] ( ∃ «𝒢» : ( «𝒳» → ( GenLimit.BoundedMemory.InfiniteOutput «𝒳» ) ) , ∀ K ∈ «𝓛» , ∀ ( x : ( ℕ → «𝒳» ) ) , ∀ ( _ : ( Set.range x = K ) ) , ∀ ( _ : ( GenLimit.BoundedMemory.FinitelyRepeating x ) ) , depends_only% [ «𝒳» , «𝓛» , «𝒢» , K , x ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ( binrel% HasSubset.Subset ( ↑ ( «𝒢» ( x t ) ) ) K ) ) )
```

### Theorem 3.1 · `GenLimit.BoundedMemory.Results.theorem_3_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( «𝓛» : ( Set ( Set «𝒳» ) ) ) , ( ( ( GenLimit.BoundedMemory.ArbitraryMemoryless «𝓛» ) ↔ ( GenLimit.BoundedMemory.FullMemoryAfterOne «𝓛» ) ) ) ∧ ( ( ( GenLimit.BoundedMemory.FullMemoryAfterOne «𝓛» ) ) ↔ ( ∀ x ∈ ( Set.sUnion «𝓛» ) , ( Set.Infinite ( GenLimit.BoundedMemory.singletonCore «𝓛» x ) ) ) )
```

### Theorem 3.2 · `GenLimit.BoundedMemory.Results.theorem_3_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ( ( ∀ i : ( Fin ( 1 + 1 ) ) , ( Set.Infinite ( GenLimit.BoundedMemory.indexLanguages i ) ) ) ) ∧ ( ( ∀ ( K : ( Set «𝒳» ) ) , ∀ ( _ : ( Set.Infinite K ) ) , ∀ ( «𝒢» : ( GenLimit.BoundedMemory.MemorylessElementGenerator «𝒳» ) ) , ( ¬ ( ( GenLimit.BoundedMemory.IsFinitelyRepeatingElementGeneratorOn «𝒢» K ) ) ) ) ∧ ( ( ∀ «𝒢» : ( GenLimit.BoundedMemory.MemorylessIndexGenerator ℕ ( Fin ( 1 + 1 ) ) ) , ( ¬ ( ( GenLimit.BoundedMemory.IsFinitelyRepeatingIndexGenerator «𝒢» GenLimit.BoundedMemory.indexLanguages ) ) ) ) ) )
```

### Theorem 4.1 · `GenLimit.BoundedMemory.Results.theorem_4_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( e : ( «𝒳» ≃ ℕ ) ) , ( ∀ ( k : ℕ ) , 1 ≤ k → ( ( SupSet.sSup { σ : ℝ | ( ( σ ∈ ( Set.Icc 0 1 ) ) ∧ ( GenLimit.BoundedMemory.RankedUniverse.Memoryless e k σ ) ) } ) = ( 1 / ( ↑ ( Nat.choose ( k - 1 ) ( ( k - 1 ) / 2 ) ) ) ) ) )
```

### Theorem 4.2 · `GenLimit.BoundedMemory.Results.theorem_4_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( e : ( «𝒳» ≃ ℕ ) ) , ∀ ( k : ℕ ) , ∀ ( _ : 3 ≤ k ) , depends_only% [ «𝒳» , e , k ] ( ∃ «𝓛» : ( GenLimit.BoundedMemory.RankedUniverse.Family «𝒳» k ) , ∃ i : ( Fin k ) , ∀ ( «𝒢» : ( GenLimit.BoundedMemory.MemorylessSetGenerator «𝒳» ) ) , ∀ ( _ : ( GenLimit.BoundedMemory.IsFinitelyRepeatingMemorylessGenerator «𝒢» ( Set.range ( GenLimit.BoundedMemory.RankedUniverse.Family.lang «𝓛» ) ) ) ) , ∀ ( x : ( ℕ → «𝒳» ) ) , ∀ ( _ : ( Set.range x = ( GenLimit.BoundedMemory.RankedUniverse.Family.lang «𝓛» i ) ) ) , ∀ ( _ : ( GenLimit.BoundedMemory.FinitelyRepeating x ) ) , depends_only% [ «𝒳» , e , k , «𝓛» , i , «𝒢» , x ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ( ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( GenLimit.KleinbergWei.OrderedLanguage.canonical ( GenLimit.BoundedMemory.RankedUniverse.Family.lang ( GenLimit.BoundedMemory.RankedUniverse.Family.map e «𝓛» ) i ) ( GenLimit.BoundedMemory.RankedUniverse.Family.infinite ( GenLimit.BoundedMemory.RankedUniverse.Family.map e «𝓛» ) i ) ) ( Set.image ( DFunLike.coe e ) ( «𝒢» ( x t ) ) ) ) = 0 ) ) )
```

### Theorem 4.10 · `GenLimit.BoundedMemory.Results.theorem_4_10`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( e : ( «𝒳» ≃ ℕ ) ) , ∀ ( k W : ℕ ) , ∀ ( _ : ( 1 ≤ k ) ) , ∀ ( _ : ( 0 < W ) ) , ( ( SupSet.sSup { σ : ℝ | ( ( σ ∈ ( Set.Icc 0 1 ) ) ∧ ( GenLimit.BoundedMemory.RankedUniverse.Windows e k W σ ) ) } ) = ( 1 / ( ↑ ( Nat.choose ( k - 1 ) ( ( k - 1 ) / 2 ) ) ) ) )
```

### Theorem 4.15 · `GenLimit.BoundedMemory.Results.theorem_4_15`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( e : ( «𝒳» ≃ ℕ ) ) , ∀ ( k b : ℕ ) , ∀ ( _ : ( 1 ≤ k ) ) , ( ( GenLimit.BoundedMemory.adaptiveBufferLowerValue k b ) ≤ ( SupSet.sSup { σ : ℝ | ( ( σ ∈ ( Set.Icc 0 1 ) ) ∧ ( GenLimit.BoundedMemory.RankedUniverse.Buffers e k b σ ) ) } ) )
```

### Proposition 5.1 · `GenLimit.BoundedMemory.Results.proposition_5_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ( ∀ i : ( Fin ( 2 + 1 ) ) , ( Set.Infinite ( GenLimit.BoundedMemory.exactObstructionLanguages i ) ) ) ) ∧ ( ( ( Function.Injective GenLimit.BoundedMemory.exactObstructionLanguages ) ) ∧ ( ( ¬ ( GenLimit.BoundedMemory.IncrementallyExactlyIdentifiableOnFinitelyRepeating GenLimit.BoundedMemory.exactObstructionLanguages ) ) ) )
```

### Theorem 5.2 · `GenLimit.BoundedMemory.Results.theorem_5_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ ( N : ℕ ) , ∀ ( «𝓛» : ( ( Fin ( N + 1 ) ) → ( Set «𝒳» ) ) ) , ( GenLimit.BoundedMemory.IncrementallyApproximatelyIdentifiable «𝓛» )
```

### Theorem A.1 · `GenLimit.BoundedMemory.Results.theorem_A_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( ∃ «𝓛» : ( ( Fin ( 2 + 1 ) ) → ( Set ℕ ) ) , ( ( Function.Injective «𝓛» ) ) ∧ ( ( ( ∀ i : ( Fin ( 2 + 1 ) ) , ( Set.Infinite ( «𝓛» i ) ) ) ) ∧ ( ( ¬ ( GenLimit.BoundedMemory.IncrementallyExactlyIdentifiableOnFinitelyRepeating «𝓛» ) ) ) ) )
```

### Proposition A.2 · `GenLimit.BoundedMemory.Results.proposition_A_2`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ ( T : ( Set «𝒳» ) ) , ∀ ( _ : ( Set.Infinite T ) ) , ∀ ( a b c : «𝒳» ) , ∀ ( _ : ( a ≠ b ) ) , ∀ ( _ : ( a ≠ c ) ) , ∀ ( _ : ( b ≠ c ) ) , ∀ ( _ : ( a ∉ T ) ) , ∀ ( _ : ( b ∉ T ) ) , ∀ ( _ : ( c ∉ T ) ) , ( ¬ ( GenLimit.BoundedMemory.IncrementallyIndexGenerableOnFinitelyRepeating ( GenLimit.BoundedMemory.appendixTriangleLanguages T a b c ) ) )
```

### Theorem A.4 · `GenLimit.BoundedMemory.Results.theorem_A_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( N : ℕ ) , ∀ ( «𝓛» : ( ( Fin ( N + 1 ) ) → ( Set «𝒳» ) ) ) , ∀ ( _ : ( ∀ i : ( Fin ( N + 1 ) ) , ( Set.Infinite ( «𝓛» i ) ) ) ) , ∀ ( M : ( ( List «𝒳» ) → ( Fin ( N + 1 ) ) ) ) , ∀ ( _ : ( ∀ target : ( Fin ( N + 1 ) ) , ( ∀ x : ( ℕ → «𝒳» ) , ( ( Set.range x = ( «𝓛» target ) ) → ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.BoundedMemory.AlmostContained ( «𝓛» ( M ( GenLimit.BoundedMemory.elementHistoryPrefix x t ) ) ) ( «𝓛» target ) ) ) ) ) ) ) ) , ( GenLimit.BoundedMemory.IncrementallyElementGenerable «𝓛» )
```

### Theorem A.5 · `GenLimit.BoundedMemory.Results.theorem_A_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒳» : Type _ ) , ∀ [ Countable «𝒳» ] , ∀ [ Infinite «𝒳» ] , ∀ ( N : ℕ ) , ∀ ( «𝓛» : ( ( Fin ( N + 1 ) ) → ( Set «𝒳» ) ) ) , ∀ ( _ : ( ∀ i : ( Fin ( N + 1 ) ) , ( Set.Infinite ( «𝓛» i ) ) ) ) , ( GenLimit.BoundedMemory.IncrementallyElementGenerable «𝓛» )
```

Grammar regression for P31: 1287/1287 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P32

SHA-256 of the checked page: `b33745a57439bc0e0e1d3169ee0d2deb16056e85f6d1e6b90fde4e5971f49a38`

### Theorem 2.1 · `GenLimit.InfinitelyManyHallucinations.Results.theorem_2_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( f : ( ℕ → ℕ ) ) , ∀ ( T : ( GenLimit.Generic.Language ℕ ) ) , ∀ ( G : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ∀ ( _ : ( Set.Infinite ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) ) , ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f G ) ) , ( ( SupSet.sSup ( GenLimit.InfinitelyManyHallucinations.boundedLowerPrecisionValues f T G ) ) = ( GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision T G ) )
```

### Theorem 3.5 · `GenLimit.InfinitelyManyHallucinations.Results.theorem_3_5`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒯» : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible «𝒯» ) ) , depends_only% [ «𝒯» ] ( ∃ «𝒢» : GenLimit.InfinitelyManyHallucinations.BatchGenerator , ∀ ( A : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , let M := ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ; ∀ ( z : ℕ ) , let T := ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( «𝒯» z ) ) ; ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep A ) ) , ∀ ( _ : ( Set.Infinite M ) ) , ∀ ( _ : ( binrel% HasSubset.Subset M T ) ) , let G := ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion «𝒢» A ) ; ( ( GenLimit.InfinitelyManyHallucinations.GeneratorNovel «𝒢» A ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep G ) ) ∧ ( ( ( Set.Infinite ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerTailPrecision T G ) = 1 ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision T G ) = 1 ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall ( «𝒯» z ) M ) / 2 ) ≤ ( GenLimit.InfinitelyManyHallucinations.lowerRecall ( «𝒯» z ) ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) ) ) ) ) ) ) )
```

### Theorem 3.6 · `GenLimit.InfinitelyManyHallucinations.Results.theorem_3_6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒢» : GenLimit.InfinitelyManyHallucinations.BatchGenerator ) , ( ∃ A : GenLimit.InfinitelyManyHallucinations.Exhaustion , let G := ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion «𝒢» A ) ; ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep A ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) = Set.univ ) ) ∧ ( ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.GeneratorNovel «𝒢» A ) ) , ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep G ) ) , ( ( GenLimit.InfinitelyManyHallucinations.upperRecall GenLimit.KleinbergWei.PartialEnumeration.Sharpness.natural ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) ≤ ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall GenLimit.KleinbergWei.PartialEnumeration.Sharpness.natural ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ) / 2 ) ) ) ) )
```

### Theorem 4.3 · `GenLimit.InfinitelyManyHallucinations.Results.theorem_4_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( target : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( T : ( GenLimit.Generic.Language ℕ ) ) , ∀ ( f : ( ℕ → ℕ ) ) , depends_only% [ target , T , f ] ( ∃ «𝒢» : GenLimit.InfinitelyManyHallucinations.BatchGenerator , ∀ ( A : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ∀ ( _ : ( Set.Infinite ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ) ) , ∀ ( _ : ( binrel% HasSubset.Subset ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) T ) ) , ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f A ) ) , let G := ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion «𝒢» A ) ; ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f G ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall target ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) = 1 ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision T G ) = 1 ) ) ) )
```

### Theorem 4.8 existence · `GenLimit.InfinitelyManyHallucinations.Results.theorem_4_8_existence`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒯» : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible «𝒯» ) ) , depends_only% [ «𝒯» ] ( ∃ «𝒢» : GenLimit.InfinitelyManyHallucinations.BatchGenerator , ∀ ( A : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , let M := ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ; ∀ ( z : ℕ ) , ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep A ) ) , ∀ ( _ : ( Set.Infinite M ) ) , ∀ ( _ : ( binrel% HasSubset.Subset M ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( «𝒯» z ) ) ) ) , let G := ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion «𝒢» A ) ; ( ( GenLimit.InfinitelyManyHallucinations.GeneratorNovel «𝒢» A ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsEnumeration G ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision ( GenLimit.KleinbergWei.OrderedLanguage.carrier ( «𝒯» z ) ) G ) = 1 ) ) ∧ ( ( ( Max.max ( 1 - ( GenLimit.InfinitelyManyHallucinations.upperRecall ( «𝒯» z ) M ) ) ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall ( «𝒯» z ) M ) / 3 ) ) ≤ ( GenLimit.InfinitelyManyHallucinations.lowerRecall ( «𝒯» z ) ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) ) ) ) ) )
```

### Theorem 4.8 counterexample · `GenLimit.InfinitelyManyHallucinations.Results.theorem_4_8_counterexample`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( R : GenLimit.InfinitelyManyHallucinations.ExplorationSet ) , let A := GenLimit.InfinitelyManyHallucinations.Pods.Counterexample.input ; let c := ( GenLimit.InfinitelyManyHallucinations.Pods.algorithm6 GenLimit.InfinitelyManyHallucinations.Pods.Counterexample.family R ( fun u => ( u + 1 ) ) ( Equiv.refl Nat ) ) ; ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep A ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) = Set.univ ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall GenLimit.KleinbergWei.PartialEnumeration.Sharpness.natural ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ) = 1 ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall GenLimit.KleinbergWei.PartialEnumeration.Sharpness.natural ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion ( GenLimit.InfinitelyManyHallucinations.WordRule.generator ( GenLimit.InfinitelyManyHallucinations.Pods.Config.rule c ) ) A ) ) ) = 0 ) ) ) )
```

### Theorem 4.9 · `GenLimit.InfinitelyManyHallucinations.Results.theorem_4_9`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒯» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝒯» i ) ) ) ) , ∀ ( R : GenLimit.InfinitelyManyHallucinations.ExplorationSet ) , ∀ ( γ : ℝ ) , ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.ExplorationSet.GammaAdmissible R γ ) ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( _ : ( ∀ u : ℕ , ( 0 < ( s u ) ) ) ) , ∀ ( scan : ( Equiv.Perm ℕ ) ) , ∀ ( A : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ∀ ( z : ℕ ) , ∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( _ : ( Set.Infinite ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ) ) , ∀ ( _ : ( binrel% HasSubset.Subset ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ( «𝒯» z ) ) ) , let G := ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion ( GenLimit.InfinitelyManyHallucinations.WordRule.generator ( GenLimit.InfinitelyManyHallucinations.Pods.Config.rule ( GenLimit.InfinitelyManyHallucinations.Pods.algorithm7 «𝒯» R s scan ) ) ) A ) ; ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsEnumeration G ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.GammaNovel γ A G ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall K ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) = 1 ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision ( «𝒯» z ) G ) = 1 ) ) ) )
```

### Theorem E.1 · `GenLimit.InfinitelyManyHallucinations.Results.theorem_E_1`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : ℝ ) , ( ∀ ( target : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( T : ( GenLimit.Generic.Language ℕ ) ) , ∀ ( f : ( ℕ → ℕ ) ) , ∀ ( A : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ∀ ( _ : ( Set.Infinite ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ) ) , ∀ ( _ : ( binrel% HasSubset.Subset ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) T ) ) , ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f A ) ) , ∀ ( _ : ( α ≤ ( GenLimit.InfinitelyManyHallucinations.lowerRecall target ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ) ) ) , let G := ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion GenLimit.InfinitelyManyHallucinations.parrotGenerator A ) ; ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f G ) ) ∧ ( ( ( α ≤ ( GenLimit.InfinitelyManyHallucinations.lowerRecall target ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision T G ) = 1 ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.lowerTailPrecision T G ) = 1 ) ) ) ) ) ∧ ( ∀ ( _ : ( α ∈ ( Set.Icc 0 1 ) ) ) , ( ∃ A : GenLimit.InfinitelyManyHallucinations.Exhaustion , ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep A ) ) ∧ ( ( ( Set.Infinite ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall GenLimit.KleinbergWei.PartialEnumeration.Sharpness.natural ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ) = α ) ) ∧ ( ∀ ( «𝒢» : GenLimit.InfinitelyManyHallucinations.BatchGenerator ) , ∀ ( c : ℕ ) , let G := ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion «𝒢» A ) ; ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy ( fun ( x : ℕ ) => c ) G ) ) , ∀ ( _ : ( ( GenLimit.InfinitelyManyHallucinations.lowerTailPrecision ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) G ) = 1 ) ) , ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall GenLimit.KleinbergWei.PartialEnumeration.Sharpness.natural ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) ≤ α ) ) ) ) ) )
```

### Theorem I.3 · `GenLimit.InfinitelyManyHallucinations.Results.theorem_I_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒯» : ( ℕ → GenLimit.Language ) ) , ∀ ( γ : ℝ ) , ∀ ( _ : ( γ < 1 ) ) , depends_only% [ «𝒯» , γ ] ( ∃ «𝒢» : GenLimit.InfinitelyManyHallucinations.BatchGenerator , ∀ ( A : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , let M := ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) ; ∀ ( z : ℕ ) , ∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier K ) = ( «𝒯» z ) ) ) , ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep A ) ) , ∀ ( _ : ( Set.Infinite M ) ) , ∀ ( _ : ( binrel% HasSubset.Subset M ( «𝒯» z ) ) ) , let G := ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion «𝒢» A ) ; ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsEnumeration G ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.GammaNovel γ A G ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall K M ) ≤ ( GenLimit.InfinitelyManyHallucinations.lowerRecall K ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision ( «𝒯» z ) G ) = 1 ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.lowerTailPrecision ( «𝒯» z ) G ) = 1 ) ) ) ) ) )
```

### Corollary I.2 · `GenLimit.InfinitelyManyHallucinations.Results.corollary_I_2`

- The body begins with Setting A; the check reads the setting's text in place of the mark
- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒯» : ( ℕ → GenLimit.Language ) ) , ∀ ( _ : ( ∀ i : ℕ , ( Set.Infinite ( «𝒯» i ) ) ) ) , ∀ ( R : GenLimit.InfinitelyManyHallucinations.ExplorationSet ) , ∀ ( γ : ℝ ) , ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.ExplorationSet.GammaAdmissible R γ ) ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( _ : ( ∀ u : ℕ , ( 0 < ( s u ) ) ) ) , ∀ ( scan : ( Equiv.Perm ℕ ) ) , ∀ ( A : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ∀ ( z : ℕ ) , ∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier K ) = ( «𝒯» z ) ) ) , ∀ ( _ : ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) = ( «𝒯» z ) ) ) , let G := ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion ( GenLimit.InfinitelyManyHallucinations.WordRule.generator ( GenLimit.InfinitelyManyHallucinations.Pods.Config.rule ( GenLimit.InfinitelyManyHallucinations.Pods.algorithm7 «𝒯» R s scan ) ) ) A ) ; ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsEnumeration G ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.GammaNovel γ A G ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall K ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) = 1 ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision ( GenLimit.KleinbergWei.OrderedLanguage.carrier K ) G ) = 1 ) ) ) )
```

### Corollary I.4 · `GenLimit.InfinitelyManyHallucinations.Results.corollary_I_4`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒯» : ( ℕ → GenLimit.Language ) ) , ∀ ( γ : ℝ ) , ∀ ( _ : ( γ < 1 ) ) , depends_only% [ «𝒯» , γ ] ( ∃ «𝒢» : GenLimit.InfinitelyManyHallucinations.BatchGenerator , ∀ ( A : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ∀ ( z : ℕ ) , ∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier K ) = ( «𝒯» z ) ) ) , ∀ ( _ : ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep A ) ) , ∀ ( _ : ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit A ) = ( «𝒯» z ) ) ) , let G := ( GenLimit.InfinitelyManyHallucinations.generatedExhaustion «𝒢» A ) ; ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsEnumeration G ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.GammaNovel γ A G ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall K ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit G ) ) = 1 ) ) ∧ ( ( ( ( GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision ( «𝒯» z ) G ) = 1 ) ) ∧ ( ( ( GenLimit.InfinitelyManyHallucinations.lowerTailPrecision ( «𝒯» z ) G ) = 1 ) ) ) ) ) )
```

Grammar regression for P32: 1094/1094 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.

## P39

SHA-256 of the checked page: `63454f41dcd6036b3bbb8ccaf5dfb0c75807499de6da023c944b8de230f99496`

### Theorem 3.15 · `GenLimit.DenseGeneration.Results.theorem_3_15`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : GenLimit.OracleFamily ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( z : ℕ ) , ∀ ( _ : ( Set.range x = ( «𝓛».language z ) ) ) , ( ( 1 / 2 ) ≤ ( GenLimit.PatientMachine.patientLowerDensity «𝓛» x z ) )
```

### Theorem B.3 · `GenLimit.DenseGeneration.Results.theorem_B_3`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the Lean export: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝓛» : GenLimit.OracleFamily ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( K' : GenLimit.Language ) , ∀ ( z : ℕ ) , ∀ ( _ : ( Set.range x = K' ) ) , ∀ ( _ : ( Set.Infinite K' ) ) , ∀ ( _ : ( binrel% HasSubset.Subset K' ( «𝓛».language z ) ) ) , ∀ ( α : ℝ ) , ∀ ( _ : ( ( GenLimit.PatientScope.relativeLowerDensity K' ( «𝓛».language z ) ( GenLimit.OracleFamily.infinite' «𝓛» z ) ) = α ) ) , ( ( α / 2 ) ≤ ( GenLimit.PartialEnumeration.partialPatientLowerDensity «𝓛» x z ) )
```

Grammar regression for P39: 196/196 random trees of the readings' grammars (fixed seed) came back as the unique parse of their own English.
