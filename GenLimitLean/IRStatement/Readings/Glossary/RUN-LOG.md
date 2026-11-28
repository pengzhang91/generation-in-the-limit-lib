# Glossary check log

Written by `glossary.py` from the saved glossary pages; do not edit.

- P00: 39/41 library labels have a checked definition; 2 without; 1939/1939 random trees recovered
- P00A: 13/16 library labels have a checked definition; 3 without; 648/648 random trees recovered
- P01: 0/0 library labels have a checked definition; 0 without; 0/0 random trees recovered
- P02: 19/20 library labels have a checked definition; 1 without; 948/948 random trees recovered
- P03: 32/44 library labels have a checked definition; 12 without; 1595/1595 random trees recovered
- P04: 6/7 library labels have a checked definition; 1 without; 300/300 random trees recovered
- P05: 36/46 library labels have a checked definition; 10 without; 1789/1789 random trees recovered
- P06: 8/8 library labels have a checked definition; 0 without; 399/399 random trees recovered
- P07: 21/26 library labels have a checked definition; 5 without; 1048/1048 random trees recovered
- P08: 5/5 library labels have a checked definition; 0 without; 248/248 random trees recovered
- P09: 8/8 library labels have a checked definition; 0 without; 399/399 random trees recovered
- P10: 10/10 library labels have a checked definition; 0 without; 500/500 random trees recovered
- P11: 29/66 library labels have a checked definition; 37 without; 1449/1449 random trees recovered
- P12: 19/19 library labels have a checked definition; 0 without; 949/949 random trees recovered
- P13: 11/18 library labels have a checked definition; 7 without; 549/549 random trees recovered
- P14: 9/9 library labels have a checked definition; 0 without; 448/448 random trees recovered
- P15: 13/19 library labels have a checked definition; 6 without; 646/646 random trees recovered
- P16: 9/12 library labels have a checked definition; 3 without; 450/450 random trees recovered
- P17: 32/48 library labels have a checked definition; 16 without; 1593/1593 random trees recovered
- P18: 16/21 library labels have a checked definition; 5 without; 794/794 random trees recovered
- P19: 6/6 library labels have a checked definition; 0 without; 299/299 random trees recovered
- P20: 10/14 library labels have a checked definition; 4 without; 497/497 random trees recovered
- P21: 21/26 library labels have a checked definition; 5 without; 1046/1046 random trees recovered
- P22: 17/22 library labels have a checked definition; 5 without; 847/847 random trees recovered
- P23: 15/29 library labels have a checked definition; 14 without; 746/746 random trees recovered
- P24: 18/20 library labels have a checked definition; 2 without; 896/896 random trees recovered
- P25: 4/13 library labels have a checked definition; 9 without; 199/199 random trees recovered
- P26: 17/30 library labels have a checked definition; 13 without; 849/849 random trees recovered
- P27: 12/12 library labels have a checked definition; 0 without; 600/600 random trees recovered
- P28: 26/28 library labels have a checked definition; 2 without; 1299/1299 random trees recovered
- P29: 11/17 library labels have a checked definition; 6 without; 547/547 random trees recovered
- P30: 4/11 library labels have a checked definition; 7 without; 198/198 random trees recovered
- P31: 17/30 library labels have a checked definition; 13 without; 842/842 random trees recovered
- P32: 20/28 library labels have a checked definition; 8 without; 997/997 random trees recovered
- P39: 3/5 library labels have a checked definition; 2 without; 149/149 random trees recovered

## P00

SHA-256 of the checked page: `ebf59334c3fe15b9dbae8288c965117055d4adc9e6cb457825ac25d69dc45f1f`

### *abstract identifiable* · `GenLimit.Gold.Abstract.Identifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Name Object Info : Type _ ) , ∀ ( naming : ( GenLimit.Gold.Abstract.Naming Name Object ) ) , ∀ ( allowable : ( GenLimit.Gold.Abstract.Allowable Info Object ) ) , ( ( GenLimit.Gold.Abstract.Identifiable naming allowable ) ) ↔ ( ( ∃ learner : ( GenLimit.Learner Info Name ) , ( GenLimit.Gold.Abstract.Identifies naming allowable learner ) ) )
```

### *allowable* · `GenLimit.Gold.Abstract.Allowable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Info Object : Type _ ) , ( ( GenLimit.Gold.Abstract.Allowable Info Object ) = ( Object → ( Set ( ℕ → Info ) ) ) )
```

### *anti domain generator* · `GenLimit.Gold.Effective.AntiDomainGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( e : Nat.Partrec.Code ) , ∀ ( L : GenLimit.Language ) , ( ( GenLimit.Gold.Effective.AntiDomainGenerator e L ) ) ↔ ( ( GenLimit.Gold.Effective.DomainGenerator e ( HasCompl.compl L ) ) )
```

### *arbitrary informant* · `GenLimit.Gold.Effective.arbitraryInformant`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( L : GenLimit.Language ) , ( ( GenLimit.Gold.Effective.arbitraryInformant L ) = { s : ( ℕ → GenLimit.Gold.Informant.InformantDatum ) | ( GenLimit.Gold.Informant.IsInformantFor s L ) } )
```

### *arbitrary text* · `GenLimit.Gold.Effective.arbitraryText`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( L : GenLimit.Language ) , ( ( GenLimit.Gold.Effective.arbitraryText L ) = { s : ( ℕ → ℕ ) | ( GenLimit.Presents s L ) } )
```

### *collapsing uncertainty* · `GenLimit.Gold.Abstract.CollapsingUncertainty`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Info Object : Type _ ) , ∀ ( allowable : ( GenLimit.Gold.Abstract.Allowable Info Object ) ) , ( ( GenLimit.Gold.Abstract.CollapsingUncertainty allowable ) ) ↔ ( ∀ ( target : Object ) , ∀ x ∈ ( allowable target ) , ∀ ( object : Object ) , ∀ ( _ : ( object ≠ target ) ) , depends_only% [ Info , Object , allowable , target , x , object ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( ¬ ( GenLimit.Gold.Abstract.Compatible allowable ( GenLimit.textPrefix x t ) object ) ) ) ) )
```

### *denotation* · `GenLimit.Gold.Effective.Denotation`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( N O : Type _ ) , ( ( GenLimit.Gold.Effective.Denotation N O ) = ( N → ( O → Prop ) ) )
```

### *distinguishable* · `GenLimit.Gold.Abstract.Distinguishable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Info Object : Type _ ) , ∀ ( allowable : ( GenLimit.Gold.Abstract.Allowable Info Object ) ) , ( ( GenLimit.Gold.Abstract.Distinguishable allowable ) ) ↔ ( ∀ ( object₁ object₂ : Object ) , ∀ x ∈ ( allowable object₁ ) , ∀ ( _ : ( x ∈ ( allowable object₂ ) ) ) , ( object₁ = object₂ ) )
```

### *domain generator* · `GenLimit.Gold.Effective.DomainGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( e : Nat.Partrec.Code ) , ∀ ( L : GenLimit.Language ) , ( ( GenLimit.Gold.Effective.DomainGenerator e L ) ) ↔ ( ∀ ( x : ℕ ) , ( ( x ∈ L ) ↔ ( Part.Dom ( Nat.Partrec.Code.eval e x ) ) ) )
```

### *effective identifiable* · `GenLimit.Gold.Effective.Identifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( I N O : Type _ ) , ∀ [ Primcodable I ] , ∀ [ Primcodable N ] , ∀ ( names : ( GenLimit.Gold.Effective.Denotation N O ) ) , ∀ ( method : ( GenLimit.Gold.Effective.Presentations I O ) ) , ∀ ( C : ( Set O ) ) , ( ( GenLimit.Gold.Effective.Identifiable names method C ) ) ↔ ( ( ∃ M : ( ( List I ) → N ) , ( ( Computable M ) ∧ ( GenLimit.Gold.Effective.Learns M names method C ) ) ) )
```

### *enumerable languages* · `GenLimit.Gold.Effective.enumerableLanguages`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Gold.Effective.enumerableLanguages = { L : GenLimit.Language | ( ∃ e : Nat.Partrec.Code , ( GenLimit.Gold.Effective.Generator e L ) ) } )
```

### *enumeration learner* · `GenLimit.Gold.Text.enumerationLearner`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ( ( GenLimit.Gold.Text.enumerationLearner C ) = ( GenLimit.Gold.Text.enumerationLearnerWithFallback C 0 ) )
```

### *finite languages* · `GenLimit.Gold.Text.finiteLanguages`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Gold.Text.finiteLanguages = { L : GenLimit.Language | ( Set.Finite L ) } )
```

### *generator* · `GenLimit.Gold.Effective.Generator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( e : Nat.Partrec.Code ) , ∀ ( L : GenLimit.Language ) , ( ( GenLimit.Gold.Effective.Generator e L ) ) ↔ ( ∀ ( x : ℕ ) , ( ( x ∈ L ) ) ↔ ( ( ∃ u : ℕ , ( x ∈ ( Nat.Partrec.Code.eval e u ) ) ) ) )
```

### *identification by enumeration* · `GenLimit.Gold.Abstract.identificationByEnumeration`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Name Object Info : Type _ ) , ∀ ( naming : ( GenLimit.Gold.Abstract.Naming Name Object ) ) , ∀ ( allowable : ( GenLimit.Gold.Abstract.Allowable Info Object ) ) , ∀ ( enumeration : ( ℕ → Object ) ) , ∀ ( history : ( List Info ) ) , ( ( GenLimit.Gold.Abstract.identificationByEnumeration naming allowable enumeration history ) = ( GenLimit.Gold.Abstract.Naming.nameOf naming ( enumeration ( GenLimit.Gold.Abstract.firstCompatibleIndex allowable enumeration history ) ) ) )
```

### *identifies* · `GenLimit.Gold.Abstract.Identifies`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Name Object Info : Type _ ) , ∀ ( naming : ( GenLimit.Gold.Abstract.Naming Name Object ) ) , ∀ ( allowable : ( GenLimit.Gold.Abstract.Allowable Info Object ) ) , ∀ ( learner : ( GenLimit.Learner Info Name ) ) , ( ( GenLimit.Gold.Abstract.Identifies naming allowable learner ) ) ↔ ( ∀ ( object : Object ) , ∀ x ∈ ( allowable object ) , ( GenLimit.Gold.Abstract.IdentifiesOn naming learner x object ) )
```

### *identifies family from informant* · `GenLimit.Gold.Informant.IdentifiesFamilyFromInformant`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( M : ( GenLimit.Gold.Informant.InformantLearner ℕ ) ) , ( ( GenLimit.Gold.Informant.IdentifiesFamilyFromInformant C M ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( info : GenLimit.Gold.Informant.InformantStream ) , ∀ ( _ : ( GenLimit.Gold.Informant.IsInformantFor info ( C z ) ) ) , ( GenLimit.Gold.Informant.IdentifiesOnInformant ( GenLimit.Gold.Text.familyNaming C ) M info ( C z ) ) )
```

### *informant enumeration learner* · `GenLimit.Gold.Informant.informantEnumerationLearner`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ( ( GenLimit.Gold.Informant.informantEnumerationLearner C ) = ( GenLimit.Gold.Informant.informantEnumerationLearnerWithFallback C 0 ) )
```

### *is superfinite* · `GenLimit.Gold.Text.IsSuperfinite`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒞» : ( Set GenLimit.Language ) ) , ( ( GenLimit.Gold.Text.IsSuperfinite «𝒞» ) ) ↔ ( ( ( GenLimit.Gold.Text.ContainsAllFiniteLanguages «𝒞» ) ) ∧ ( ( ∃ L ∈ «𝒞» , ( Set.Infinite L ) ) ) )
```

### *language family* · `GenLimit.LanguageFamily`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.LanguageFamily = ( ℕ → GenLimit.Language ) )
```

### *learner* · `GenLimit.Learner`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Info Name : Type _ ) , ( ( GenLimit.Learner Info Name ) = ( ( List Info ) → Name ) )
```

### *learns* · `GenLimit.Gold.Effective.Learns`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( I N O : Type _ ) , ∀ ( M : ( ( List I ) → N ) ) , ∀ ( names : ( GenLimit.Gold.Effective.Denotation N O ) ) , ∀ ( method : ( GenLimit.Gold.Effective.Presentations I O ) ) , ∀ ( C : ( Set O ) ) , ( ( GenLimit.Gold.Effective.Learns M names method C ) ) ↔ ( ∀ L ∈ C , ∀ s ∈ ( method L ) , ( ∃ n : N , ( ( names n L ) ) ∧ ( depends_only% [ I , N , O , M , names , method , C , L , s , n ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ( ( M ( GenLimit.textPrefix s t ) ) = n ) ) ) ) )
```

### *limit translation* · `GenLimit.Gold.Effective.LimitTranslation`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A B O : Type _ ) , ∀ [ Primcodable A ] , ∀ [ Primcodable B ] , ∀ ( src : ( GenLimit.Gold.Effective.Denotation A O ) ) , ∀ ( dst : ( GenLimit.Gold.Effective.Denotation B O ) ) , ∀ ( C : ( Set O ) ) , ( ( GenLimit.Gold.Effective.LimitTranslation src dst C ) ) ↔ ( ( ∃ g : ( A → ( ℕ → B ) ) , ( ( Computable₂ g ) ) ∧ ( ∀ L ∈ C , ∀ ( a : A ) , ∀ ( _ : ( src a L ) ) , ( ∃ b : B , ( ( dst b L ) ) ∧ ( depends_only% [ A , B , O , src , dst , C , g , L , a , b ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ( ( g a t ) = b ) ) ) ) ) ) )
```

### *method* · `GenLimit.Gold.Effective.Method`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( I : Type _ ) , ( ( GenLimit.Gold.Effective.Method I ) = ( GenLimit.Gold.Effective.Presentations I GenLimit.Language ) )
```

### *methodical* · `GenLimit.Gold.Effective.methodical`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( L : GenLimit.Language ) , ( ( GenLimit.Gold.Effective.methodical L ) = ( Singleton.singleton ( GenLimit.Gold.Effective.bit L ) ) )
```

### *name relation* · `GenLimit.Gold.Effective.NameRelation`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( N : Type _ ) , ( ( GenLimit.Gold.Effective.NameRelation N ) = ( GenLimit.Gold.Effective.Denotation N GenLimit.Language ) )
```

### *named* · `GenLimit.Gold.Effective.Named`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( N : Type _ ) , ∀ ( names : ( GenLimit.Gold.Effective.NameRelation N ) ) , ∀ ( C : ( Set GenLimit.Language ) ) , ( ( GenLimit.Gold.Effective.Named names C ) ) ↔ ( ∀ L ∈ C , ( ∃ n : N , ( names n L ) ) )
```

### *no slower* · `GenLimit.Gold.Abstract.NoSlower`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( N O I : Type _ ) , ∀ ( naming : ( GenLimit.Gold.Abstract.Naming N O ) ) , ∀ ( allowed : ( GenLimit.Gold.Abstract.Allowable I O ) ) , ∀ ( M G : ( GenLimit.Learner I N ) ) , ( ( GenLimit.Gold.Abstract.NoSlower naming allowed M G ) ) ↔ ( ∀ ( o : O ) , ∀ s ∈ ( allowed o ) , ∀ ( t : ℕ ) , ∀ ( _ : ( t > 0 ) ) , ∀ ( _ : ( GenLimit.Gold.Abstract.CorrectFrom naming G s o t ) ) , ( GenLimit.Gold.Abstract.CorrectFrom naming M s o t ) )
```

### *presentations* · `GenLimit.Gold.Effective.Presentations`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( I O : Type _ ) , ( ( GenLimit.Gold.Effective.Presentations I O ) = ( O → ( Set ( ℕ → I ) ) ) )
```

### *primitive languages* · `GenLimit.Gold.Effective.primitiveLanguages`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Gold.Effective.primitiveLanguages = { L : GenLimit.Language | ( Primrec ( GenLimit.Gold.Effective.bit L ) ) } )
```

### *primitive recursive text* · `GenLimit.Gold.Effective.primitiveRecursiveText`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( L : GenLimit.Language ) , ( ( GenLimit.Gold.Effective.primitiveRecursiveText L ) = { s : ( ℕ → ℕ ) | ( ( Primrec s ) ∧ ( GenLimit.Presents s L ) ) } )
```

### *recursive languages* · `GenLimit.Gold.Effective.recursiveLanguages`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Gold.Effective.recursiveLanguages = { L : GenLimit.Language | ( Computable ( GenLimit.Gold.Effective.bit L ) ) } )
```

### *recursive text* · `GenLimit.Gold.Effective.recursiveText`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( L : GenLimit.Language ) , ( ( GenLimit.Gold.Effective.recursiveText L ) = { s : ( ℕ → ℕ ) | ( ( Computable s ) ∧ ( GenLimit.Presents s L ) ) } )
```

### *request identifiable* · `GenLimit.Gold.Effective.RequestIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( N : Type _ ) , ∀ [ Primcodable N ] , ∀ ( names : ( GenLimit.Gold.Effective.NameRelation N ) ) , ∀ ( C : ( Set GenLimit.Language ) ) , ( ( GenLimit.Gold.Effective.RequestIdentifiable names C ) ) ↔ ( ( ∃ q : ( ( List ℕ ) → ℕ ) , ∃ M : ( ( List ℕ ) → N ) , ( ( Computable q ) ) ∧ ( ( ( Computable M ) ) ∧ ( ∀ L ∈ C , ( ∃ a : N , ( ( names a L ) ) ∧ ( depends_only% [ N , names , C , q , M , L , a ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ( ( M ( GenLimit.Gold.Effective.transcript q L t ) ) = a ) ) ) ) ) ) ) )
```

### *semantically identifiable* · `GenLimit.Gold.Text.SemanticallyIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( «𝒞» : ( Set GenLimit.Language ) ) , ( ( GenLimit.Gold.Text.SemanticallyIdentifiable «𝒞» ) ) ↔ ( ( ∃ M : ( GenLimit.Gold.Text.TextLearner GenLimit.Language ) , ( GenLimit.Gold.Text.SemanticallyIdentifiesClass M «𝒞» ) ) )
```

### *stabilizes to* · `GenLimit.StabilizesTo`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Name : Type _ ) , ∀ ( guess : ( ℕ → Name ) ) , ∀ ( name : Name ) , ( ( GenLimit.StabilizesTo guess name ) ) ↔ ( depends_only% [ Name , guess , name ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( ( guess t ) = name ) ) ) )
```

### *tester* · `GenLimit.Gold.Effective.Tester`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( e : Nat.Partrec.Code ) , ∀ ( L : GenLimit.Language ) , ( ( GenLimit.Gold.Effective.Tester e L ) ) ↔ ( ∀ ( x : ℕ ) , ( ∀ ( _ : ( x ∈ L ) ) , ( ( Nat.Partrec.Code.eval e x ) = ( Part.some 1 ) ) ) ∧ ( ∀ ( _ : ( x ∉ L ) ) , ( ( Nat.Partrec.Code.eval e x ) = ( Part.some 0 ) ) ) )
```

### *text prefix* · `GenLimit.textPrefix`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( ℕ → α ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.textPrefix x t ) = ( List.map x ( List.range t ) ) )
```

### *two recursive translation* · `GenLimit.Gold.Effective.TwoRecursiveTranslation`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( src dst : ( GenLimit.Gold.Effective.NameRelation Nat.Partrec.Code ) ) , ∀ ( C : ( Set GenLimit.Language ) ) , ( ( GenLimit.Gold.Effective.TwoRecursiveTranslation src dst C ) ) ↔ ( ( ∃ R : ( ( ( Nat.Partrec.Code × Nat.Partrec.Code ) × ℕ ) → ( ℕ → Bool ) ) , ( ( Computable₂ R ) ) ∧ ( let graph := ( fun a => ( fun b => ( ∃ w : ℕ , ( ∀ u : ℕ , ( ( R ( ( a , b ) , w ) u ) = Bool.true ) ) ) ) ) ; ( ∀ ( a b c : Nat.Partrec.Code ) , ∀ ( _ : ( graph a b ) ) , ∀ ( _ : ( graph a c ) ) , ( b = c ) ) ∧ ( ∀ L ∈ C , ∀ ( a : Nat.Partrec.Code ) , ∀ ( _ : ( src a L ) ) , ( ∃ b : Nat.Partrec.Code , ( ( graph a b ) ∧ ( dst b L ) ) ) ) ) ) )
```

## P00A

SHA-256 of the checked page: `48767785c9067b323c534b14081a1ef4b782a2760db53f5bdf59e196a1548895`

### *condition five* · `GenLimit.Angluin.ConditionFive`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ( ( GenLimit.Angluin.ConditionFive F ) ) ↔ ( ( ∃ select : ( PFun ( Finset ℕ ) ℕ ) , ( ( Partrec ( fun h => ( select ( List.toFinset h ) ) ) ) ) ∧ ( ∀ ( S : ( Finset ℕ ) ) , ∀ ( _ : ( Finset.Nonempty S ) ) , ∀ ( _ : ( ∃ j : ℕ , ( GenLimit.Angluin.Descriptive F S j ) ) ) , ( ∃ j ∈ ( select S ) , ( GenLimit.Angluin.Descriptive F S j ) ) ) ) )
```

### *condition four* · `GenLimit.Angluin.ConditionFour`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ( ( GenLimit.Angluin.ConditionFour F ) ) ↔ ( ( ∃ inclusion : ( ℕ → ( ℕ → Bool ) ) , ( ( Computable₂ inclusion ) ) ∧ ( ∀ ( i j : ℕ ) , ( ( ( inclusion i j ) = Bool.true ) ↔ ( binrel% HasSubset.Subset ( GenLimit.Angluin.EffectiveIndexedFamily.language F i ) ( GenLimit.Angluin.EffectiveIndexedFamily.language F j ) ) ) ) ) )
```

### *condition one* · `GenLimit.Angluin.ConditionOne`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ( ( GenLimit.Angluin.ConditionOne F ) ) ↔ ( ( ∃ emit : ( ℕ → ( ℕ → ( Option ℕ ) ) ) , ( ( Computable₂ emit ) ) ∧ ( ( ∀ i : ℕ , ( GenLimit.Angluin.IsEnumeratedTellTale ( GenLimit.Angluin.EffectiveIndexedFamily.language F ) i ( GenLimit.Angluin.enumeratedSet emit i ) ) ) ) ) )
```

### *condition one prime* · `GenLimit.Angluin.ConditionOnePrime`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ( ( GenLimit.Angluin.ConditionOnePrime F ) ) ↔ ( ( ∃ output : ( ℕ → ( List ℕ ) ) , ( ( Computable output ) ) ∧ ( ( ∀ i : ℕ , ( GenLimit.Angluin.IsTellTale ( GenLimit.Angluin.EffectiveIndexedFamily.language F ) i ( List.toFinset ( output i ) ) ) ) ) ) )
```

### *condition three* · `GenLimit.Angluin.ConditionThree`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.Angluin.ConditionThree C ) ) ↔ ( ∀ ( S : ( Finset ℕ ) ) , ∀ ( _ : ( Finset.Nonempty S ) ) , ( Set.Finite { L : ( Set ℕ ) | ( ( L ∈ ( Set.range C ) ) ∧ ( binrel% HasSubset.Subset S L ) ) } ) )
```

### *condition two* · `GenLimit.Angluin.ConditionTwo`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.Angluin.ConditionTwo C ) ) ↔ ( ∀ ( i : ℕ ) , ( ∃ T : ( Finset α ) , ( GenLimit.Angluin.IsTellTale C i T ) ) )
```

### *conservative* · `GenLimit.Angluin.InferenceMachine.Conservative`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( M : GenLimit.Angluin.InferenceMachine ) , ∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ( ( GenLimit.Angluin.InferenceMachine.Conservative M F ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( s : ( GenLimit.Generic.Stream ℕ ) ) , ∀ ( _ : ( GenLimit.Generic.Presents s ( GenLimit.Angluin.EffectiveIndexedFamily.language F i ) ) ) , ∀ ( n k j m l g : ℕ ) , ∀ ( _ : ( GenLimit.Angluin.InferenceMachine.Earlier n k m l ) ) , ∀ ( _ : ( GenLimit.Angluin.InferenceMachine.Guesses M s n k j ) ) , ∀ ( _ : ( GenLimit.Angluin.InferenceMachine.Guesses M s m l g ) ) , ∀ ( _ : ( g ≠ j ) ) , ( ∃ ( t : ℕ ) , t < m ∧ ( ( s t ) ∉ ( GenLimit.Angluin.EffectiveIndexedFamily.language F j ) ) ) )
```

### *consistent* · `GenLimit.Angluin.InferenceMachine.Consistent`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( M : GenLimit.Angluin.InferenceMachine ) , ∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ( ( GenLimit.Angluin.InferenceMachine.Consistent M F ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( s : ( GenLimit.Generic.Stream ℕ ) ) , ∀ ( _ : ( GenLimit.Generic.Presents s ( GenLimit.Angluin.EffectiveIndexedFamily.language F i ) ) ) , ∀ ( n k j : ℕ ) , ∀ ( _ : ( GenLimit.Angluin.InferenceMachine.Guesses M s n k j ) ) , ∀ ( t : ℕ ) , ∀ ( _ : ( t < n ) ) , ( ( s t ) ∈ ( GenLimit.Angluin.EffectiveIndexedFamily.language F j ) ) )
```

### *effective inferrable* · `GenLimit.Angluin.EffectiveInferrable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ( ( GenLimit.Angluin.EffectiveInferrable F ) ) ↔ ( ( ∃ M : GenLimit.Angluin.EffectiveIdentifier , ( ( Computable M ) ∧ ( GenLimit.Angluin.SemanticallyIdentifies M ( GenLimit.Angluin.EffectiveIndexedFamily.language F ) ) ) ) )
```

### *identifies* · `GenLimit.Angluin.InferenceMachine.Identifies`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( M : GenLimit.Angluin.InferenceMachine ) , ∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ( ( GenLimit.Angluin.InferenceMachine.Identifies M F ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( s : ( GenLimit.Generic.Stream ℕ ) ) , ∀ ( _ : ( GenLimit.Generic.Presents s ( GenLimit.Angluin.EffectiveIndexedFamily.language F i ) ) ) , ( ∃ n : ℕ , ∃ k : ℕ , ∃ j : ℕ , ( ( GenLimit.Angluin.InferenceMachine.Guesses M s n k j ) ) ∧ ( ( ( ( GenLimit.Angluin.EffectiveIndexedFamily.language F j ) = ( GenLimit.Angluin.EffectiveIndexedFamily.language F i ) ) ) ∧ ( ∀ ( m l g : ℕ ) , ∀ ( _ : ( GenLimit.Angluin.InferenceMachine.Earlier n k m l ) ) , ∀ ( _ : ( GenLimit.Angluin.InferenceMachine.Guesses M s m l g ) ) , ( g = j ) ) ) ) )
```

### *language family* · `GenLimit.Generic.LanguageFamily`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.LanguageFamily α ) = ( ℕ → ( GenLimit.Generic.Language α ) ) )
```

### *responsive* · `GenLimit.Angluin.InferenceMachine.Responsive`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( M : GenLimit.Angluin.InferenceMachine ) , ∀ ( F : GenLimit.Angluin.EffectiveIndexedFamily ) , ( ( GenLimit.Angluin.InferenceMachine.Responsive M F ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( s : ( GenLimit.Generic.Stream ℕ ) ) , ∀ ( _ : ( GenLimit.Generic.Presents s ( GenLimit.Angluin.EffectiveIndexedFamily.language F i ) ) ) , ∀ ( n : ℕ ) , ∀ ( k : ℕ ) , ∀ ( _ : ( Option.none ∈ ( GenLimit.Angluin.InferenceMachine.event M ( GenLimit.textPrefix s ( n + 1 ) ) k ) ) ) , ( 0 < k ) )
```

### *semantically inferrable* · `GenLimit.Angluin.SemanticallyInferrable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.Angluin.SemanticallyInferrable C ) ) ↔ ( ( ∃ M : ( GenLimit.Angluin.SemanticIdentifier α ) , ( GenLimit.Angluin.SemanticallyIdentifies M C ) ) )
```

## P01

SHA-256 of the checked page: `e7237929b36c807c88971be7ebd9d921ec0a896393e9fc1fd282e7724117f530`

## P02

SHA-256 of the checked page: `ff21383b98f46b67dd9b3e6bce69966d40cf275bef5aba4234ba3cce66b2745a`

### *eventually unbounded closure* · `GenLimit.LiRamanTewari.EventuallyUnboundedClosure`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.EventuallyUnboundedClosure H ) ) ↔ ( ∀ L ∈ H , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x L ) ) , ( ∃ t : ℕ , ( Set.Infinite ( GenLimit.LiRamanTewari.commonCore H ( IRStatement.FirstTerms.firstTerms x t ) ) ) ) )
```

### *generatable in limit* · `GenLimit.LiRamanTewari.GeneratableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.GeneratableInLimit H ) ) ↔ ( ( GenLimit.Generic.GeneratableInLimit H ) )
```

### *has closure dimension* · `GenLimit.LiRamanTewari.HasClosureDimension`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( d : ℕ ) , ( ( GenLimit.LiRamanTewari.HasClosureDimension H d ) ) ↔ ( ( GenLimit.Generic.HasClosureDimension H d ) )
```

### *has finite closure dimension* · `GenLimit.LiRamanTewari.HasFiniteClosureDimension`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.HasFiniteClosureDimension H ) ) ↔ ( ( GenLimit.Generic.HasFiniteClosureDimension H ) )
```

### *has finite littlestone dimension* · `GenLimit.LiRamanTewari.HasFiniteLittlestoneDimension`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.HasFiniteLittlestoneDimension H ) ) ↔ ( ( ∃ d : ℕ , ( ¬ ( GenLimit.LiRamanTewari.HasShatteredLittlestoneTree H ( d + 1 ) ) ) ) )
```

### *has finite prompted closure dimension* · `GenLimit.LiRamanTewari.HasFinitePromptedClosureDimension`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α ι : Type _ ) , ∀ ( H : ( GenLimit.LiRamanTewari.MulticlassHypothesisClass α ι ) ) , ( ( GenLimit.LiRamanTewari.HasFinitePromptedClosureDimension H ) ) ↔ ( ( ∃ d : ℕ , ( GenLimit.LiRamanTewari.HasPromptedClosureDimension H d ) ) )
```

### *has finite VC dimension* · `GenLimit.LiRamanTewari.HasFiniteVCDimension`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.HasFiniteVCDimension H ) ) ↔ ( depends_only% [ α , H ] ( ∃ d : ℕ , ∀ ( xs : ( ( Fin ( d + 1 ) ) → α ) ) , ( ¬ ( GenLimit.LiRamanTewari.VCShatters H xs ) ) ) )
```

### *is finite cover* · `GenLimit.LiRamanTewari.IsFiniteCover`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( n : ℕ ) , ∀ ( classes : ( ( Fin n ) → ( GenLimit.Generic.LanguageClass α ) ) ) , ( ( GenLimit.LiRamanTewari.IsFiniteCover H classes ) ) ↔ ( ( GenLimit.Generic.IsFiniteCover H classes ) )
```

### *is nondecreasing cover* · `GenLimit.LiRamanTewari.IsNondecreasingCover`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( classes : ( ℕ → ( GenLimit.Generic.LanguageClass α ) ) ) , ( ( GenLimit.LiRamanTewari.IsNondecreasingCover H classes ) ) ↔ ( ( GenLimit.Generic.IsNondecreasingCover H classes ) )
```

### *language class* · `GenLimit.Generic.LanguageClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.LanguageClass α ) = ( Set ( GenLimit.Generic.Language α ) ) )
```

### *multiclass hypothesis class* · `GenLimit.LiRamanTewari.MulticlassHypothesisClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α ι : Type _ ) , ( ( GenLimit.LiRamanTewari.MulticlassHypothesisClass α ι ) = ( Set ( GenLimit.LiRamanTewari.MulticlassHypothesis α ι ) ) )
```

### *nonuniformly generatable* · `GenLimit.LiRamanTewari.NonuniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.NonuniformlyGeneratable H ) ) ↔ ( ( GenLimit.Generic.NonuniformlyGeneratable H ) )
```

### *online learnable* · `GenLimit.LiRamanTewari.OnlineLearnable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.OnlineLearnable H ) ) ↔ ( ( ∃ A : ( GenLimit.LiRamanTewari.OnlinePredictor α ) , ∃ R : ( ℕ → ℕ ) , ( ∀ ( k : ℕ ) , depends_only% [ α , H , A , R , k ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ( ( k * ( R t ) ) ≤ t ) ) ) ∧ ( ∀ K ∈ H , ∀ ( xs : ( List ( α × Bool ) ) ) , ∀ ( _ : ( GenLimit.LiRamanTewari.labeledBy K xs ) ) , ( ( GenLimit.LiRamanTewari.mistakesFrom A [] xs ) ≤ ( R ( List.length xs ) ) ) ) ) )
```

### *PAC learnable* · `GenLimit.LiRamanTewari.PACLearnable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.PACLearnable H ) ) ↔ ( depends_only% [ α , H ] ( ∃ A : ( GenLimit.LiRamanTewari.PACPredictor α ) , ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ∀ ( _ : ( ε < 1 ) ) , ∀ ( δ : ℝ ) , ∀ ( _ : ( 0 < δ ) ) , ∀ ( _ : ( δ < 1 ) ) , depends_only% [ α , H , A , ε , δ ] ( ∃ N : ℕ , ∀ ( n : ℕ ) , ∀ ( _ : ( n ≥ N ) ) , ∀ ( p : ( PMF α ) ) , ∀ K ∈ H , ( ( GenLimit.DiscreteIID.probability ( GenLimit.DiscreteIID.samples p n ) { xs : ( List α ) | ( ε < ( GenLimit.LiRamanTewari.predictionRisk p ( A ( GenLimit.LiRamanTewari.labeledSample ( GenLimit.LiRamanTewari.languageLabel K ) xs ) ) ( GenLimit.LiRamanTewari.languageLabel K ) ) ) } ) ≤ δ ) ) ) )
```

### *prompted nonuniformly generatable* · `GenLimit.LiRamanTewari.PromptedNonuniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α ι : Type _ ) , ∀ ( H : ( GenLimit.LiRamanTewari.MulticlassHypothesisClass α ι ) ) , ( ( GenLimit.LiRamanTewari.PromptedNonuniformlyGeneratable H ) ) ↔ ( ( ∃ gen : ( GenLimit.LiRamanTewari.PromptedGenerator α ι ) , ( GenLimit.LiRamanTewari.IsPromptedNonuniformGenerator gen H ) ) )
```

### *prompted uniformly generatable* · `GenLimit.LiRamanTewari.PromptedUniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α ι : Type _ ) , ∀ ( H : ( GenLimit.LiRamanTewari.MulticlassHypothesisClass α ι ) ) , ( ( GenLimit.LiRamanTewari.PromptedUniformlyGeneratable H ) ) ↔ ( ( ∃ gen : ( GenLimit.LiRamanTewari.PromptedGenerator α ι ) , ∃ d : ℕ , ( GenLimit.LiRamanTewari.IsPromptedUniformGeneratorAt gen H d ) ) )
```

### *PUUS* · `GenLimit.LiRamanTewari.PUUS`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α ι : Type _ ) , ∀ ( H : ( GenLimit.LiRamanTewari.MulticlassHypothesisClass α ι ) ) , ( ( GenLimit.LiRamanTewari.PUUS H ) ) ↔ ( ∀ h ∈ H , ∀ ( y : ι ) , ( Set.Infinite ( GenLimit.LiRamanTewari.promptSupport h y ) ) )
```

### *uniformly generatable* · `GenLimit.LiRamanTewari.UniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.UniformlyGeneratable H ) ) ↔ ( ( GenLimit.Generic.UniformlyGeneratable H ) )
```

### *UUS* · `GenLimit.LiRamanTewari.UUS`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.UUS H ) ) ↔ ( ( GenLimit.Generic.UUS H ) )
```

## P03

SHA-256 of the checked page: `c893f7dae31e8ea1cee1f2c96da653e58e789fccb83b7e5fff57a733dbcf7298`

### *almost exponential identifiable* · `GenLimit.HallucinationModeCollapse.AlmostExponentialIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.AlmostExponentialIdentifiable C ) ) ↔ ( ∀ ( g : ( ℕ → ℝ ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.AdmissibleSublinearExponent g ) ) , ( ∃ A : ( GenLimit.Learner ℕ ℕ ) , ( GenLimit.HallucinationModeCollapse.AchievesIdentificationRate C ( GenLimit.HallucinationModeCollapse.deterministicIdentifier A ) ( fun n => ( Real.exp ( - ( g n ) ) ) ) ) ) )
```

### *always halts* · `GenLimit.Support.RandomBitMachine.Machine.AlwaysHalts`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( M : GenLimit.Support.RandomBitMachine.Machine ) , ( ( GenLimit.Support.RandomBitMachine.Machine.AlwaysHalts M ) ) ↔ ( ∀ ( input : ℕ ) , ∀ ( tape : ( ℕ → Bool ) ) , ( ∃ n : ℕ , ∃ output : ℕ , ( ( GenLimit.Support.RandomBitMachine.Machine.run M input tape n ) = ( Sum.inr output ) ) ) )
```

### *approximate breadth in limit* · `GenLimit.HallucinationModeCollapse.ApproximateBreadthInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( G : GenLimit.HallucinationModeCollapse.SupportGenerator ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.ApproximateBreadthInLimit G C ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream ℕ ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( C z ) ) ) , depends_only% [ G , C , z , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.HallucinationModeCollapse.ApproximateBreadthAt ( GenLimit.HallucinationModeCollapse.supportAt G x t ) ( C z ) ) ) ) )
```

### *certified breadth positive branch* · `GenLimit.HallucinationModeCollapse.CertifiedBreadthPositiveBranch`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ( ( GenLimit.HallucinationModeCollapse.CertifiedBreadthPositiveBranch O ) ) ↔ ( ( ∃ emit : ( ℕ → ( ℕ → ( Option ℕ ) ) ) , let K := ( GenLimit.HallucinationModeCollapse.tellTaleBreadthGenerator O emit ) ; ( ( ∀ i : ℕ , ( GenLimit.Angluin.IsEnumeratedTellTale ( O.language ) i ( GenLimit.Angluin.enumeratedSet emit i ) ) ) ) ∧ ( ( ( GenLimit.HallucinationModeCollapse.OracleMOP ( GenLimit.HallucinationModeCollapse.generationOracle O ) K ) ) ∧ ( ( ( GenLimit.HallucinationModeCollapse.ExponentialBreadth ( O.language ) K ) ) ∧ ( ( ∀ ( g : ( ℕ → ℝ ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.AdmissibleSublinearExponent g ) ) , ( GenLimit.HallucinationModeCollapse.AchievesBreadthRate ( O.language ) K ( fun n => ( Real.exp ( - ( g n ) ) ) ) ) ) ∧ ( ( ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query O ) ) ) , ( GenLimit.HallucinationModeCollapse.DecidableMOP K ) ) ∧ ( ∀ ( _ : ( Computable₂ ( GenLimit.OracleFamily.query O ) ) ) , ∀ ( _ : ( Computable₂ emit ) ) , ( ( GenLimit.HallucinationModeCollapse.HasComputableSampler K ) ∧ ( GenLimit.HallucinationModeCollapse.UniformDecidableMOP K ) ) ) ) ) ) ) ) )
```

### *certified KM* · `GenLimit.HallucinationModeCollapse.certifiedKM`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ( ( GenLimit.HallucinationModeCollapse.certifiedKM O ) = ( GenLimit.Support.OracleSearchProgram.run GenLimit.HallucinationModeCollapse.generationProgram ( GenLimit.HallucinationModeCollapse.generationOracle O ) ( GenLimit.HallucinationModeCollapse.generationProgram_terminates O ) ) )
```

### *decidable MOP* · `GenLimit.HallucinationModeCollapse.DecidableMOP`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.DecidableMOP G ) ) ↔ ( ∀ ( xs : ( List ℕ ) ) , ( ∃ query : ( ℕ → Bool ) , ( ( Computable query ) ) ∧ ( ∀ ( x : ℕ ) , ( ( ( query x ) = Bool.true ) ↔ ( x ∈ ( PMF.support ( G xs ) ) ) ) ) ) )
```

### *deterministic identifier* · `GenLimit.HallucinationModeCollapse.deterministicIdentifier`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A : ( GenLimit.Learner ℕ ℕ ) ) , ∀ ( xs : ( List ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.deterministicIdentifier A xs ) = ( PMF.pure ( A xs ) ) )
```

### *deterministic labeled identifier* · `GenLimit.HallucinationModeCollapse.deterministicLabeledIdentifier`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A : ( ( List GenLimit.HallucinationModeCollapse.LabeledDatum ) → ℕ ) ) , ∀ ( xs : ( List GenLimit.HallucinationModeCollapse.LabeledDatum ) ) , ( ( GenLimit.HallucinationModeCollapse.deterministicLabeledIdentifier A xs ) = ( PMF.pure ( A xs ) ) )
```

### *exponential generates* · `GenLimit.HallucinationModeCollapse.ExponentialGenerates`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.ExponentialGenerates C G ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( p : ( PMF ℕ ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ) , ( ∃ c : ℝ , ( ( 0 < c ) ) ∧ ( ( ∃ D : ℝ , ( ( 0 < D ) ) ∧ ( ( ∀ n : ℕ , ( ( GenLimit.HallucinationModeCollapse.generationError C G p i n ) ≤ ( D * ( Real.exp ( ( - c ) * ( ↑ n ) ) ) ) ) ) ) ) ) ) )
```

### *exponential identifies* · `GenLimit.HallucinationModeCollapse.ExponentialIdentifies`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( A : GenLimit.HallucinationModeCollapse.StatisticalIdentifier ) , ( ( GenLimit.HallucinationModeCollapse.ExponentialIdentifies C A ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( p : ( PMF ℕ ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ) , ( ∃ c : ℝ , ( ( 0 < c ) ) ∧ ( ( ∃ D : ℝ , ( ( 0 < D ) ) ∧ ( ( ∀ n : ℕ , ( ( GenLimit.HallucinationModeCollapse.identificationError C A p i n ) ≤ ( D * ( Real.exp ( ( - c ) * ( ↑ n ) ) ) ) ) ) ) ) ) ) )
```

### *exponential labeled identifies* · `GenLimit.HallucinationModeCollapse.ExponentialLabeledIdentifies`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( A : GenLimit.HallucinationModeCollapse.LabeledIdentifier ) , ( ( GenLimit.HallucinationModeCollapse.ExponentialLabeledIdentifies C A ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( p : ( PMF GenLimit.HallucinationModeCollapse.LabeledDatum ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.ValidLabeledDistribution C i p ) ) , ( ∃ c : ℝ , ( ( 0 < c ) ) ∧ ( ( ∃ D : ℝ , ( ( 0 < D ) ) ∧ ( ( ∀ n : ℕ , ( ( GenLimit.HallucinationModeCollapse.labeledIdentificationError C A p i n ) ≤ ( D * ( Real.exp ( ( - c ) * ( ↑ n ) ) ) ) ) ) ) ) ) ) )
```

### *generation error* · `GenLimit.HallucinationModeCollapse.generationError`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ∀ ( p : ( PMF ℕ ) ) , ∀ ( i n : ℕ ) , ( ( GenLimit.HallucinationModeCollapse.generationError C G p i n ) = ( GenLimit.DiscreteIID.probability ( PMF.bind ( GenLimit.DiscreteIID.samples p n ) ( fun xs => ( PMF.map ( fun y => ( xs , y ) ) ( G xs ) ) ) ) { z : ( ( List ℕ ) × ℕ ) | ( ( ( Prod.snd z ) ∉ ( C i ) ) ∨ ( ( Prod.snd z ) ∈ ( Prod.fst z ) ) ) } ) )
```

### *generation nontrivial* · `GenLimit.HallucinationModeCollapse.GenerationNontrivial`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.GenerationNontrivial C ) ) ↔ ( ( ∃ I : ( Finset ℕ ) , ( ( Finset.Nonempty I ) ) ∧ ( ( depends_only% [ C , I ] ( ∃ x : ℕ , ∀ i ∈ I , ( x ∈ ( C i ) ) ) ) ∧ ( ( Set.Finite { x : ℕ | ( ∀ i ∈ I , ( x ∈ ( C i ) ) ) } ) ) ) ) )
```

### *generation oracle* · `GenLimit.HallucinationModeCollapse.generationOracle`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( code : ℕ ) , ( ( GenLimit.HallucinationModeCollapse.generationOracle O code ) = ( ite ( Eq ( GenLimit.OracleFamily.query O ( Prod.fst ( Nat.unpair code ) ) ( Prod.snd ( Nat.unpair code ) ) ) Bool.true ) 1 0 ) )
```

### *has computable sampler* · `GenLimit.HallucinationModeCollapse.HasComputableSampler`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.HasComputableSampler G ) ) ↔ ( ( ∃ sample : ( ( ( List ℕ ) × ℕ ) → ℕ ) , ( ( Computable sample ) ) ∧ ( ( ∀ xs : ( List ℕ ) , ( ( G xs ) = ( PMF.map ( fun seed => ( sample ( xs , seed ) ) ) GenLimit.DiscreteIID.positiveGeometric ) ) ) ) ) )
```

### *identifiable in limit* · `GenLimit.HallucinationModeCollapse.IdentifiableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit C ) ) ↔ ( ( GenLimit.Angluin.SemanticallyInferrable C ) )
```

### *identification error* · `GenLimit.HallucinationModeCollapse.identificationError`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( A : GenLimit.HallucinationModeCollapse.StatisticalIdentifier ) , ∀ ( p : ( PMF ℕ ) ) , ∀ ( i n : ℕ ) , ( ( GenLimit.HallucinationModeCollapse.identificationError C A p i n ) = ( GenLimit.DiscreteIID.probability ( PMF.bind ( GenLimit.DiscreteIID.samples p n ) A ) { j : ℕ | ( ( C j ) ≠ ( C i ) ) } ) )
```

### *labeled datum* · `GenLimit.HallucinationModeCollapse.LabeledDatum`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.HallucinationModeCollapse.LabeledDatum = GenLimit.Gold.Informant.InformantDatum )
```

### *labeled enumeration learner* · `GenLimit.HallucinationModeCollapse.labeledEnumerationLearner`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( O : ( GenLimit.MembershipOracle C ) ) , ∀ ( xs : ( List GenLimit.HallucinationModeCollapse.LabeledDatum ) ) , ( ( GenLimit.HallucinationModeCollapse.labeledEnumerationLearner O xs ) = ( Option.getD ( GenLimit.Support.firstTrue ( GenLimit.HallucinationModeCollapse.labeledConsistent O ) xs ( List.length xs ) ) 0 ) )
```

### *labeled identification error* · `GenLimit.HallucinationModeCollapse.labeledIdentificationError`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( A : GenLimit.HallucinationModeCollapse.LabeledIdentifier ) , ∀ ( p : ( PMF GenLimit.HallucinationModeCollapse.LabeledDatum ) ) , ∀ ( i n : ℕ ) , ( ( GenLimit.HallucinationModeCollapse.labeledIdentificationError C A p i n ) = ( GenLimit.DiscreteIID.probability ( PMF.bind ( GenLimit.DiscreteIID.samples p n ) A ) { j : ℕ | ( ( C j ) ≠ ( C i ) ) } ) )
```

### *no approximate breadth rate* · `GenLimit.HallucinationModeCollapse.NoApproximateBreadthRate`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.NoApproximateBreadthRate C G ) ) ↔ ( ( ∃ i : ℕ , ∃ p : ( PMF ℕ ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ∧ ( 0 < ( Filter.limsup ( fun n => ( GenLimit.HallucinationModeCollapse.approximateBreadthError C G p i n ) ) Filter.atTop ) ) ) ) )
```

### *no breadth rate* · `GenLimit.HallucinationModeCollapse.NoBreadthRate`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.NoBreadthRate C G ) ) ↔ ( ( ∃ i : ℕ , ∃ p : ( PMF ℕ ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ∧ ( 0 < ( Filter.limsup ( fun n => ( GenLimit.HallucinationModeCollapse.breadthError C G p i n ) ) Filter.atTop ) ) ) ) )
```

### *no identification rate* · `GenLimit.HallucinationModeCollapse.NoIdentificationRate`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.NoIdentificationRate C ) ) ↔ ( ∀ ( A : GenLimit.HallucinationModeCollapse.StatisticalIdentifier ) , ( ∃ i : ℕ , ∃ p : ( PMF ℕ ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ∧ ( 0 < ( Filter.limsup ( fun n => ( GenLimit.HallucinationModeCollapse.identificationError C A p i n ) ) Filter.atTop ) ) ) ) )
```

### *no unambiguous rate* · `GenLimit.HallucinationModeCollapse.NoUnambiguousRate`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.NoUnambiguousRate C G ) ) ↔ ( ( ∃ i : ℕ , ∃ p : ( PMF ℕ ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ∧ ( 0 < ( Filter.limsup ( fun n => ( GenLimit.HallucinationModeCollapse.unambiguousError C G p i n ) ) Filter.atTop ) ) ) ) )
```

### *nontrivial collection* · `GenLimit.HallucinationModeCollapse.NontrivialCollection`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.NontrivialCollection C ) ) ↔ ( ( ∃ i : ℕ , ∃ j : ℕ , ∃ x : ℕ , ( ( ( C i ) ≠ ( C j ) ) ∧ ( ( x ∈ ( C i ) ) ∧ ( x ∈ ( C j ) ) ) ) ) )
```

### *oracle MOP* · `GenLimit.HallucinationModeCollapse.OracleMOP`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( oracle : ( ℕ → ℕ ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.OracleMOP oracle G ) ) ↔ ( ∀ ( xs : ( List ℕ ) ) , depends_only% [ oracle , G , xs ] ( ∃ P : GenLimit.Support.TruthTableProgram , ∀ ( x : ℕ ) , ( ( ( GenLimit.Support.TruthTableProgram.run P oracle [ x ] ) = 1 ) ↔ ( x ∈ ( PMF.support ( G xs ) ) ) ) ) )
```

### *statistical generator* · `GenLimit.HallucinationModeCollapse.StatisticalGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.HallucinationModeCollapse.StatisticalGenerator = ( ( List ℕ ) → ( PMF ℕ ) ) )
```

### *statistical stable* · `GenLimit.HallucinationModeCollapse.StatisticalStable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.StatisticalStable G C ) ) ↔ ( ( GenLimit.HallucinationModeCollapse.Stable ( GenLimit.HallucinationModeCollapse.statisticalSupportView G ) C ) )
```

### *subset identifier* · `GenLimit.HallucinationModeCollapse.subsetIdentifier`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( O : ( GenLimit.MembershipOracle C ) ) , ∀ ( S : ( GenLimit.SubsetOracle C ) ) , ( ( GenLimit.HallucinationModeCollapse.subsetIdentifier O S ) = ( GenLimit.Support.TruthTableProgram.run GenLimit.HallucinationModeCollapse.subsetIdentificationProgram ( GenLimit.HallucinationModeCollapse.subsetIdentificationOracle O S ) ) )
```

### *unambiguous in limit* · `GenLimit.HallucinationModeCollapse.UnambiguousInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( G : GenLimit.HallucinationModeCollapse.SupportGenerator ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.UnambiguousInLimit G C ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream ℕ ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( C z ) ) ) , depends_only% [ G , C , z , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.HallucinationModeCollapse.UnambiguousAt C z ( GenLimit.HallucinationModeCollapse.supportAt G x t ) ) ) ) )
```

### *valid distribution* · `GenLimit.HallucinationModeCollapse.ValidDistribution`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( i : ℕ ) , ∀ ( p : ( PMF ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ) ↔ ( ( ( PMF.support p ) = ( C i ) ) )
```

### *valid labeled distribution* · `GenLimit.HallucinationModeCollapse.ValidLabeledDistribution`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( i : ℕ ) , ∀ ( p : ( PMF GenLimit.HallucinationModeCollapse.LabeledDatum ) ) , ( ( GenLimit.HallucinationModeCollapse.ValidLabeledDistribution C i p ) ) ↔ ( ( ( PMF.support p ) = { z : GenLimit.HallucinationModeCollapse.LabeledDatum | ( GenLimit.HallucinationModeCollapse.CorrectLabel C i z ) } ) )
```

## P04

SHA-256 of the checked page: `226b9fc2bfc81323565e583b1b103a9887e12a96ead59cd74820b25f2276be22`

### *exhaustively generatable* · `GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable C ) ) ↔ ( ( ∃ A : ( GenLimit.CharikarPabbaraju.ExhaustiveAlgorithm α ) , ( GenLimit.CharikarPabbaraju.IsExhaustiveGenerator A C ) ) )
```

### *has finite GF dimension* · `GenLimit.CharikarPabbaraju.HasFiniteGFDimension`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.CharikarPabbaraju.HasFiniteGFDimension C ) ) ↔ ( ( ∃ d : ℕ , ( ¬ ( GenLimit.CharikarPabbaraju.GFDimensionAtLeast C d ) ) ) )
```

### *nonuniformly generatable* · `GenLimit.CharikarPabbaraju.NonuniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.CharikarPabbaraju.NonuniformlyGeneratable C ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.CharikarPabbaraju.IsNonuniformGenerator gen C ) ) )
```

### *two language membership algorithm* · `GenLimit.CharikarPabbaraju.TwoLanguageMembershipAlgorithm`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.CharikarPabbaraju.TwoLanguageMembershipAlgorithm = ( GenLimit.Support.AdaptiveMembershipDialogue.Algorithm ℕ GenLimit.CharikarPabbaraju.TwoLanguageQuery ℕ ) )
```

### *uniformly generatable with feedback* · `GenLimit.CharikarPabbaraju.UniformlyGeneratableWithFeedback`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.CharikarPabbaraju.UniformlyGeneratableWithFeedback C ) ) ↔ ( ( ∃ G : ( GenLimit.CharikarPabbaraju.FeedbackGeneratorStrategy α ) , ∃ d : ℕ , ( GenLimit.CharikarPabbaraju.IsUniformFeedbackGeneratorAt G C d ) ) )
```

### *weak angluin existence* · `GenLimit.CharikarPabbaraju.WeakAngluinExistence`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.CharikarPabbaraju.WeakAngluinExistence C ) ) ↔ ( ∀ L ∈ C , ( ∃ T : ( Finset α ) , ( ( binrel% HasSubset.Subset T L ) ) ∧ ( ∀ L' ∈ C , ∀ ( _ : ( binrel% HasSubset.Subset T L' ) ) , ∀ ( _ : ( HasSSubset.SSubset L' L ) ) , ( Set.Finite ( L \ L' ) ) ) ) )
```

## P05

SHA-256 of the checked page: `ad0f133a398dd0997c9ec8e950c2c00981356e434e85dc9ab914eb9d991d818e`

### *achieves scaled approximate breadth rate* · `GenLimit.HallucinationModeCollapse.AchievesScaledApproximateBreadthRate`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ∀ ( R : ( ℝ → ℝ ) ) , ( ( GenLimit.HallucinationModeCollapse.AchievesScaledApproximateBreadthRate C G R ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( p : ( PMF ℕ ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ) , ( ∃ c : ℝ , ( ( 0 < c ) ) ∧ ( ( ∃ D : ℝ , ( ( 0 < D ) ) ∧ ( ( ∀ n : ℕ , ( ( GenLimit.HallucinationModeCollapse.approximateBreadthError C G p i n ) ≤ ( D * ( R ( c * ( ↑ n ) ) ) ) ) ) ) ) ) ) )
```

### *approximate breadth at* · `GenLimit.HallucinationModeCollapse.ApproximateBreadthAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( S K : ( Set ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.ApproximateBreadthAt S K ) ) ↔ ( ( ( binrel% HasSubset.Subset S K ) ∧ ( Set.Finite ( K \ S ) ) ) )
```

### *approximate breadth correct at* · `GenLimit.BreadthCharacterizations.ApproximateBreadthCorrectAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.BreadthCharacterizations.SupportAlgorithm α ) ) , ∀ ( K : ( GenLimit.Generic.Language α ) ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( t : ℕ ) , let N := ( GenLimit.BreadthCharacterizations.supportAt G x t ) ; ( ( GenLimit.BreadthCharacterizations.ApproximateBreadthCorrectAt G K x t ) ) ↔ ( ( ( binrel% HasSubset.Subset N K ) ∧ ( Set.Finite ( K \ N ) ) ) )
```

### *condition two* · `GenLimit.Angluin.ConditionTwo`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.Angluin.ConditionTwo C ) ) ↔ ( ∀ ( i : ℕ ) , ( ∃ T : ( Finset α ) , ( GenLimit.Angluin.IsTellTale C i T ) ) )
```

### *critical sampler* · `GenLimit.BreadthCharacterizations.criticalSampler`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( S : ( GenLimit.SubsetOracle ( O.language ) ) ) , ( ( GenLimit.BreadthCharacterizations.criticalSampler O S ) = ( GenLimit.HallucinationModeCollapse.identifiedBreadth O ( GenLimit.HallucinationModeCollapse.subsetIdentifier ( GenLimit.HallucinationModeCollapse.familyMembership O ) S ) ) )
```

### *enumerated set* · `GenLimit.Angluin.enumeratedSet`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Angluin.enumeratedSet = GenLimit.Support.enumeratedSet )
```

### *enumerates exhaustively* · `GenLimit.BreadthCharacterizations.EnumeratesExhaustively`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( A : ( GenLimit.BreadthCharacterizations.Enumerator α ) ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.BreadthCharacterizations.EnumeratesExhaustively A F ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( s : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents s ( F i ) ) ) , depends_only% [ α , A , F , i , s ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , let R := ( Set.range ( A ( GenLimit.textPrefix s t ) ) ) ; ( ( Set.Finite ( R \ ( F i ) ) ) ∧ ( binrel% HasSubset.Subset ( F i ) ( ( ( Finset.toSet ( IRStatement.FirstTerms.firstTerms s t ) ) ∪ { x : α | ( ∃ ( j : ℕ ) , j < t ∧ ( ( A ( GenLimit.textPrefix s j ) 0 ) = x ) ) } ) ∪ R ) ) ) ) )
```

### *eventually generates with* · `GenLimit.BreadthCharacterizations.EventuallyGeneratesWith`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( P : ( ( List α ) → ( ( Set α ) → Prop ) ) ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.BreadthCharacterizations.EventuallyGeneratesWith P F ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( s : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents s ( F i ) ) ) , depends_only% [ α , P , F , i , s ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ( P ( GenLimit.textPrefix s t ) ( F i ) ) ) )
```

### *exact fresh sampler* · `GenLimit.HallucinationModeCollapse.exactFreshSampler`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( xs : ( List ℕ ) ) , ∀ ( j : ℕ ) , ( ( GenLimit.HallucinationModeCollapse.exactFreshSampler O xs j ) = ( PMF.map ( GenLimit.HallucinationModeCollapse.seededFreshSample O xs j ) GenLimit.DiscreteIID.positiveGeometric ) )
```

### *exponential breadth* · `GenLimit.HallucinationModeCollapse.ExponentialBreadth`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.ExponentialBreadth C G ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( p : ( PMF ℕ ) ) , ∀ ( _ : ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ) , ( ∃ c : ℝ , ( ( 0 < c ) ) ∧ ( ( ∃ D : ℝ , ( ( 0 < D ) ) ∧ ( ( ∀ n : ℕ , ( ( GenLimit.HallucinationModeCollapse.breadthError C G p i n ) ≤ ( D * ( Real.exp ( ( - c ) * ( ↑ n ) ) ) ) ) ) ) ) ) ) )
```

### *generates unambiguously* · `GenLimit.BreadthCharacterizations.GeneratesUnambiguously`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.BreadthCharacterizations.SupportAlgorithm α ) ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.BreadthCharacterizations.GeneratesUnambiguously G F ) ) ↔ ( ( GenLimit.BreadthCharacterizations.EventuallyGeneratesWith ( fun xs => ( fun K => ( GenLimit.BreadthCharacterizations.UnambiguousFor F ( G xs ) K ) ) ) F ) )
```

### *generation nontrivial* · `GenLimit.HallucinationModeCollapse.GenerationNontrivial`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.GenerationNontrivial C ) ) ↔ ( ( ∃ I : ( Finset ℕ ) , ( ( Finset.Nonempty I ) ) ∧ ( ( depends_only% [ C , I ] ( ∃ x : ℕ , ∀ i ∈ I , ( x ∈ ( C i ) ) ) ) ∧ ( ( Set.Finite { x : ℕ | ( ∀ i ∈ I , ( x ∈ ( C i ) ) ) } ) ) ) ) )
```

### *generation oracle* · `GenLimit.HallucinationModeCollapse.generationOracle`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( code : ℕ ) , ( ( GenLimit.HallucinationModeCollapse.generationOracle O code ) = ( ite ( Eq ( GenLimit.OracleFamily.query O ( Prod.fst ( Nat.unpair code ) ) ( Prod.snd ( Nat.unpair code ) ) ) Bool.true ) 1 0 ) )
```

### *has closure dimension* · `GenLimit.Generic.HasClosureDimension`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( d : ℕ ) , ( ( GenLimit.Generic.HasClosureDimension H d ) ) ↔ ( ( ( GenLimit.Generic.ClosureDimensionAtMost H d ) ) ∧ ( ( ( d = 0 ) ) ∨ ( ( ∃ S : ( Finset α ) , ( ( ( Finset.card S ) = d ) ∧ ( GenLimit.Generic.IsClosureWitness H S ) ) ) ) ) )
```

### *has computable sampler* · `GenLimit.HallucinationModeCollapse.HasComputableSampler`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.HasComputableSampler G ) ) ↔ ( ( ∃ sample : ( ( ( List ℕ ) × ℕ ) → ℕ ) , ( ( Computable sample ) ) ∧ ( ( ∀ xs : ( List ℕ ) , ( ( G xs ) = ( PMF.map ( fun seed => ( sample ( xs , seed ) ) ) GenLimit.DiscreteIID.positiveGeometric ) ) ) ) ) )
```

### *identifiable in limit* · `GenLimit.HallucinationModeCollapse.IdentifiableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.IdentifiableInLimit C ) ) ↔ ( ( GenLimit.Angluin.SemanticallyInferrable C ) )
```

### *identification oracle* · `GenLimit.HallucinationModeCollapse.identificationOracle`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( O : ( GenLimit.MembershipOracle C ) ) , ∀ ( emit : ( ℕ → ( ℕ → ( Option ℕ ) ) ) ) , ∀ ( code : ℕ ) , let U := ( Nat.unpair ( Prod.snd ( Nat.unpair code ) ) ) ; let N := ( Prod.fst U ) ; let Q := ( Prod.snd U ) ; let V := ( Prod.fst ( Nat.unpair code ) ) ; ( ( GenLimit.HallucinationModeCollapse.identificationOracle O emit code ) = ( ite ( Eq V 0 ) ( Encodable.encode ( emit N Q ) ) ( ite ( Eq V 1 ) ( ite ( Eq ( GenLimit.MembershipOracle.query O N Q ) Bool.true ) 1 0 ) 0 ) ) )
```

### *identification program* · `GenLimit.HallucinationModeCollapse.identificationProgram`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.HallucinationModeCollapse.identificationProgram = ( GenLimit.Support.TruthTableProgram.mk GenLimit.HallucinationModeCollapse.identificationQueries GenLimit.HallucinationModeCollapse.identificationQueries_primrec GenLimit.HallucinationModeCollapse.identificationPost GenLimit.HallucinationModeCollapse.identificationPost_computable ) )
```

### *is approximate breadth generator* · `GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.BreadthCharacterizations.SupportAlgorithm α ) ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.BreadthCharacterizations.IsApproximateBreadthGenerator G F ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( F z ) ) ) , depends_only% [ α , G , F , z , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.BreadthCharacterizations.ApproximateBreadthCorrectAt G ( F z ) x t ) ) ) )
```

### *is enumerated weak tell tale* · `GenLimit.CharikarPabbaraju.IsEnumeratedWeakTellTale`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( i : ℕ ) , ∀ ( T : ( Set ℕ ) ) , ( ( GenLimit.CharikarPabbaraju.IsEnumeratedWeakTellTale F i T ) ) ↔ ( ( ( Set.Finite T ) ) ∧ ( ( ( binrel% HasSubset.Subset T ( F i ) ) ) ∧ ( ∀ ( j : ℕ ) , ∀ ( _ : ( binrel% HasSubset.Subset T ( F j ) ) ) , ∀ ( _ : ( HasSSubset.SSubset ( F j ) ( F i ) ) ) , ( Set.Finite ( ( F i ) \ ( F j ) ) ) ) ) )
```

### *is exact breadth generator* · `GenLimit.BreadthCharacterizations.IsExactBreadthGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.BreadthCharacterizations.SupportAlgorithm α ) ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.BreadthCharacterizations.IsExactBreadthGenerator G F ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( F z ) ) ) , depends_only% [ α , G , F , z , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.BreadthCharacterizations.ExactBreadthCorrectAt G ( F z ) x t ) ) ) )
```

### *is infinite coverage generator* · `GenLimit.BreadthCharacterizations.IsInfiniteCoverageGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.BreadthCharacterizations.SupportAlgorithm α ) ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.BreadthCharacterizations.IsInfiniteCoverageGenerator G F ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( F z ) ) ) , depends_only% [ α , G , F , z , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.BreadthCharacterizations.InfiniteCoverageCorrectAt G ( F z ) x t ) ) ) )
```

### *is stable generator* · `GenLimit.BreadthCharacterizations.IsStableGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.BreadthCharacterizations.SupportAlgorithm α ) ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.BreadthCharacterizations.IsStableGenerator G F ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( F z ) ) ) , depends_only% [ α , G , F , z , x ] ( ∃ T : ℕ , ∀ ( n n' : ℕ ) , ∀ ( _ : ( T ≤ n ) ) , ∀ ( _ : ( T ≤ n' ) ) , ( ( GenLimit.BreadthCharacterizations.supportAt G x n ) = ( GenLimit.BreadthCharacterizations.supportAt G x n' ) ) ) )
```

### *is whole target generator* · `GenLimit.BreadthCharacterizations.IsWholeTargetGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.BreadthCharacterizations.SupportAlgorithm α ) ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.BreadthCharacterizations.IsWholeTargetGenerator G F ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( F z ) ) ) , depends_only% [ α , G , F , z , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.BreadthCharacterizations.WholeTargetCorrectAt G ( F z ) x t ) ) ) )
```

### *no breadth rate* · `GenLimit.HallucinationModeCollapse.NoBreadthRate`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.NoBreadthRate C G ) ) ↔ ( ( ∃ i : ℕ , ∃ p : ( PMF ℕ ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ∧ ( 0 < ( Filter.limsup ( fun n => ( GenLimit.HallucinationModeCollapse.breadthError C G p i n ) ) Filter.atTop ) ) ) ) )
```

### *nontrivial collection* · `GenLimit.HallucinationModeCollapse.NontrivialCollection`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.NontrivialCollection C ) ) ↔ ( ( ∃ i : ℕ , ∃ j : ℕ , ∃ x : ℕ , ( ( ( C i ) ≠ ( C j ) ) ∧ ( ( x ∈ ( C i ) ) ∧ ( x ∈ ( C j ) ) ) ) ) )
```

### *oracle MOP* · `GenLimit.HallucinationModeCollapse.OracleMOP`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( oracle : ( ℕ → ℕ ) ) , ∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.OracleMOP oracle G ) ) ↔ ( ∀ ( xs : ( List ℕ ) ) , depends_only% [ oracle , G , xs ] ( ∃ P : GenLimit.Support.TruthTableProgram , ∀ ( x : ℕ ) , ( ( ( GenLimit.Support.TruthTableProgram.run P oracle [ x ] ) = 1 ) ↔ ( x ∈ ( PMF.support ( G xs ) ) ) ) ) )
```

### *probability* · `GenLimit.DiscreteIID.probability`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( p : ( PMF α ) ) , ∀ ( E : ( Set α ) ) , ( ( GenLimit.DiscreteIID.probability p E ) = ( ENNReal.toReal ( DFunLike.coe ( PMF.toOuterMeasure p ) E ) ) )
```

### *run* · `GenLimit.Support.TruthTableProgram.run`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( P : GenLimit.Support.TruthTableProgram ) , ∀ ( oracle : ( ℕ → ℕ ) ) , ∀ ( xs : ( List ℕ ) ) , ( ( GenLimit.Support.TruthTableProgram.run P oracle xs ) = ( GenLimit.Support.TruthTableProgram.output P ( xs , ( List.map oracle ( GenLimit.Support.TruthTableProgram.queries P xs ) ) ) ) )
```

### *sample allowing infinite coverage* · `GenLimit.BreadthCharacterizations.SampleAllowingInfiniteCoverage`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.BreadthCharacterizations.SupportAlgorithm α ) ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.BreadthCharacterizations.SampleAllowingInfiniteCoverage G F ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( s : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents s ( F i ) ) ) , depends_only% [ α , G , F , i , s ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , let N := ( GenLimit.BreadthCharacterizations.supportAt G s t ) ; ∀ ( _ : ( t ≥ T ) ) , ( ( binrel% HasSubset.Subset N ( F i ) ) ∧ ( Set.Infinite N ) ) ) )
```

### *semantic identifier* · `GenLimit.Angluin.SemanticIdentifier`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Angluin.SemanticIdentifier α ) = ( GenLimit.Learner α ℕ ) )
```

### *semantically identifies* · `GenLimit.Angluin.SemanticallyIdentifies`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( M : ( GenLimit.Angluin.SemanticIdentifier α ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.Angluin.SemanticallyIdentifies M C ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( C z ) ) ) , ( GenLimit.IdentifiesInLimit C M x ( C z ) ) )
```

### *uniform decidable MOP* · `GenLimit.HallucinationModeCollapse.UniformDecidableMOP`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( G : GenLimit.HallucinationModeCollapse.StatisticalGenerator ) , ( ( GenLimit.HallucinationModeCollapse.UniformDecidableMOP G ) ) ↔ ( ( ∃ query : ( ( List ℕ ) → ( ℕ → Bool ) ) , ( ( Computable₂ query ) ) ∧ ( ∀ ( xs : ( List ℕ ) ) , ∀ ( x : ℕ ) , ( ( ( query xs x ) = Bool.true ) ↔ ( x ∈ ( PMF.support ( G xs ) ) ) ) ) ) )
```

### *valid distribution* · `GenLimit.HallucinationModeCollapse.ValidDistribution`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : ( GenLimit.Generic.LanguageFamily ℕ ) ) , ∀ ( i : ℕ ) , ∀ ( p : ( PMF ℕ ) ) , ( ( GenLimit.HallucinationModeCollapse.ValidDistribution C i p ) ) ↔ ( ( ( PMF.support p ) = ( C i ) ) )
```

### *weak angluin condition* · `GenLimit.BreadthCharacterizations.WeakAngluinCondition`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.BreadthCharacterizations.WeakAngluinCondition F ) ) ↔ ( ∀ ( i : ℕ ) , ( ∃ T : ( Finset α ) , ( GenLimit.BreadthCharacterizations.IsWeakTellTale F i T ) ) )
```

### *weak law* · `GenLimit.BreadthCharacterizations.weakLaw`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( emit : ( ℕ → ( ℕ → ( Option ℕ ) ) ) ) , ∀ ( xs : ( List ℕ ) ) , ( ( GenLimit.BreadthCharacterizations.weakLaw O emit xs ) = ( GenLimit.HallucinationModeCollapse.exactFreshSampler O ( List.range ( List.length xs ) ) ( GenLimit.Support.TruthTableProgram.run GenLimit.HallucinationModeCollapse.identificationProgram ( GenLimit.HallucinationModeCollapse.identificationOracle ( GenLimit.HallucinationModeCollapse.familyMembership O ) emit ) xs ) ) )
```

## P06

SHA-256 of the checked page: `83c89cf16ab7adfd9829111b764050c135170324e94365a44706878db3d65398`

### *common intersection* · `GenLimit.NoisyExamples.commonIntersection`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoisyExamples.commonIntersection H ) = ( GenLimit.Support.classIntersection H ) )
```

### *finite noisy closure dimension at* · `GenLimit.NoisyExamples.FiniteNoisyClosureDimensionAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( n : ℕ ) , ( ( GenLimit.NoisyExamples.FiniteNoisyClosureDimensionAt H n ) ) ↔ ( depends_only% [ α , H , n ] ( ∃ D : ℕ , ∀ ( d : ℕ ) , ∀ ( _ : ( D < d ) ) , ( ¬ ( GenLimit.NoisyExamples.NoisyClosureWitnessAt H n d ) ) ) )
```

### *language class* · `GenLimit.Generic.LanguageClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.LanguageClass α ) = ( Set ( GenLimit.Generic.Language α ) ) )
```

### *noisily generatable in limit* · `GenLimit.NoisyExamples.NoisilyGeneratableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoisyExamples.NoisilyGeneratableInLimit H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.NoisyExamples.IsNoisyLimitGenerator gen H ) ) )
```

### *nonuniformly generatable* · `GenLimit.Generic.NonuniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.NonuniformlyGeneratable H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.Generic.IsNonuniformGenerator gen H ) ) )
```

### *uniform noise dependent generatable* · `GenLimit.NoisyExamples.UniformNoiseDependentGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoisyExamples.UniformNoiseDependentGeneratable H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.NoisyExamples.IsUniformNoiseDependentGenerator gen H ) ) )
```

### *uniform noise independent generatable* · `GenLimit.NoisyExamples.UniformNoiseIndependentGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoisyExamples.UniformNoiseIndependentGeneratable H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ∃ d : ℕ , ( GenLimit.NoisyExamples.IsUniformNoiseIndependentGeneratorAt gen H d ) ) )
```

### *UUS* · `GenLimit.Generic.UUS`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.UUS H ) ) ↔ ( ∀ L ∈ H , ( Set.Infinite L ) )
```

## P07

SHA-256 of the checked page: `03f2d5a432443053a6f559b827b69dfb5ce85d1b2fccc885917c8e5b6ec73787`

### *accurate at* · `GenLimit.KleinbergWei.DensityMeasures.AccurateAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( z r : ℕ ) , ( ( GenLimit.KleinbergWei.DensityMeasures.AccurateAt C x z r ) ) ↔ ( ( ( C ( GenLimit.KleinbergWei.DensityMeasures.guessIndex C x r ) ) = ( C z ) ) )
```

### *bad inputs* · `GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.badInputs`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( input output : ( ℕ → ℕ ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.badInputs K input output ) = { x : ℕ | ( ∃ t : ℕ , ( ( ( input t ) = x ) ∧ ( GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.BadAt K input output t ) ) ) } )
```

### *compatible* · `GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) ↔ ( ∀ ( i j a b c d : ℕ ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O i ) a ) = ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O j ) c ) ) ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O i ) b ) = ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O j ) d ) ) ) , ∀ ( _ : ( a < b ) ) , ( c < d ) )
```

### *element valid* · `GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( s g : ( ℕ → ℕ ) ) , ∀ ( K : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid s g K ) ) ↔ ( depends_only% [ s , g , K ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ( ( ( g t ) ∈ K ) ) ∧ ( ( ∀ ( i : ℕ ) , ∀ ( _ : ( i ≤ t ) ) , ( ( s i ) ≠ ( g t ) ) ) ∧ ( ( ∀ ( i : ℕ ) , i < t → ( ( g i ) ≠ ( g t ) ) ) ) ) ) )
```

### *finite rank at most* · `GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : ( Set GenLimit.Language ) ) , ∀ ( r : ℕ ) , ( ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost X r ) ) ↔ ( ( ( GenLimit.KleinbergWei.TowerTopology.cbDerivative X r ) = EmptyCollection.emptyCollection ) )
```

### *has bad run from* · `GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.HasBadRunFrom`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( bad : GenLimit.Language ) , ∀ ( start length : ℕ ) , ( ( GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.HasBadRunFrom K bad start length ) ) ↔ ( ∀ ( offset : ℕ ) , ∀ ( _ : ( offset < length ) ) , ( ( GenLimit.KleinbergWei.OrderedLanguage.enumeration K ( start + offset ) ) ∈ bad ) )
```

### *has perfect tower bound* · `GenLimit.KleinbergWei.DensityMeasures.HasPerfectTowerBound`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : ( Set GenLimit.Language ) ) , ∀ ( terminal : ( GenLimit.KleinbergWei.TowerTopology.Point X ) ) , ∀ ( ordering : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( bound : ℝ ) , ( ( GenLimit.KleinbergWei.DensityMeasures.HasPerfectTowerBound X terminal ordering bound ) ) ↔ ( ( ( ( GenLimit.KleinbergWei.OrderedLanguage.carrier ordering ) = ( ↑ terminal ) ) ) ∧ ( ( ∃ tower : ( ℕ → ( GenLimit.KleinbergWei.TowerTopology.Point X ) ) , ( ( GenLimit.KleinbergWei.TowerTopology.PerfectTower X tower terminal ) ) ∧ ( ( ∀ n : ℕ , ( ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity ordering ( ↑ ( tower n ) ) ) ≤ bound ) ) ) ) ) )
```

### *index breadth* · `GenLimit.KleinbergWei.DensityMeasures.indexBreadth`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( O : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( A : ( ( List ℕ ) → ℕ ) ) , ∀ ( s : ( ℕ → ℕ ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.indexBreadth C O A s ) = ( Filter.liminf ( fun t => ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity O ( C ( A ( GenLimit.textPrefix s t ) ) ) ) ) Filter.atTop ) )
```

### *index upper density at* · `GenLimit.KleinbergWei.DensityMeasures.indexUpperDensityAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( ordering : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( t : ℕ ) , ( ( GenLimit.KleinbergWei.DensityMeasures.indexUpperDensityAt C x ordering t ) = ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity ordering ( C ( GenLimit.KleinbergWei.DensityMeasures.guessIndex C x t ) ) ) )
```

### *is limit point* · `GenLimit.KleinbergWei.TowerTopology.IsLimitPoint`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : ( Set GenLimit.Language ) ) , ∀ ( K : ( GenLimit.KleinbergWei.TowerTopology.Point X ) ) , ( ( GenLimit.KleinbergWei.TowerTopology.IsLimitPoint K ) ) ↔ ( ∀ ( O : ( Set ( GenLimit.KleinbergWei.TowerTopology.Point X ) ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.TowerTopology.KWOpen X O ) ) , ∀ ( _ : ( K ∈ O ) ) , ( ∃ L ∈ O , ( L ≠ K ) ) )
```

### *is truth index* · `GenLimit.KleinbergWei.DensityMeasures.IsTruthIndex`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : ( Set GenLimit.Language ) ) , ∀ ( terminal : ( GenLimit.KleinbergWei.TowerTopology.Point X ) ) , ∀ ( ordering : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( τ : ℝ ) , ( ( GenLimit.KleinbergWei.DensityMeasures.IsTruthIndex X terminal ordering τ ) ) ↔ ( ( ( 0 ≤ τ ) ) ∧ ( ( ( τ ≤ 1 ) ) ∧ ( ( ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.HasAnyPerfectTower X terminal ) ) , ( ∀ ( ε : ℝ ) , ∀ ( _ : ( 0 < ε ) ) , ( GenLimit.KleinbergWei.DensityMeasures.HasPerfectTowerBound X terminal ordering ( τ + ε ) ) ) ∧ ( ∀ ( σ : ℝ ) , ∀ ( _ : ( ∀ ε : ℝ , ( ( 0 < ε ) → ( GenLimit.KleinbergWei.DensityMeasures.HasPerfectTowerBound X terminal ordering ( σ + ε ) ) ) ) ) , ( τ ≤ σ ) ) ) ∧ ( ∀ ( _ : ( ¬ ( GenLimit.KleinbergWei.DensityMeasures.HasAnyPerfectTower X terminal ) ) ) , ( τ = 1 ) ) ) ) )
```

### *lower density* · `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( A : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K A ) = ( Filter.liminf ( GenLimit.KleinbergWei.OrderedLanguage.prefixRatio K A ) Filter.atTop ) )
```

### *perfect tower* · `GenLimit.KleinbergWei.DensityMeasures.PerfectTower`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : ( Set GenLimit.Language ) ) , ∀ ( tower : ( ℕ → ( GenLimit.KleinbergWei.TowerTopology.Point X ) ) ) , ∀ ( terminal : ( GenLimit.KleinbergWei.TowerTopology.Point X ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.PerfectTower X tower terminal ) ) ↔ ( ( GenLimit.KleinbergWei.TowerTopology.PerfectTower X tower terminal ) )
```

### *play* · `GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A : ( ( List ℕ ) → ℕ ) ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play A s t ) = ( A ( GenLimit.textPrefix s ( t + 1 ) ) ) )
```

### *selector* · `GenLimit.KleinbergWei.DensityMeasures.SetDriven.selector`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( S : ( Finset ℕ ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.selector C S ) = ( GenLimit.KleinbergWei.DensityMeasures.breadthSelector C ( Finset.toList S ) ) )
```

### *text prefix* · `GenLimit.textPrefix`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( ℕ → α ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.textPrefix x t ) = ( List.map x ( List.range t ) ) )
```

### *upper density* · `GenLimit.KleinbergWei.OrderedLanguage.upperDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( A : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity K A ) = ( Filter.limsup ( GenLimit.KleinbergWei.OrderedLanguage.prefixRatio K A ) Filter.atTop ) )
```

### *valid element on injective* · `GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidElementOnInjective`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( A : ( ( Finset ℕ ) → ℕ ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidElementOnInjective C A ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective s ) ) , ∀ ( _ : ( GenLimit.Presents s ( C z ) ) ) , ( ∀ᶠ ( t : ℕ ) in Filter.atTop , ( ( A ( IRStatement.FirstTerms.firstTerms s t ) ) ∈ ( ( C z ) \ ( IRStatement.FirstTerms.firstTerms s t ) ) ) ) )
```

### *valid index* · `GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidIndex`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( A : ( ( Finset ℕ ) → ℕ ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidIndex C A ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( _ : ( GenLimit.Presents s ( C z ) ) ) , ( ∀ᶠ ( t : ℕ ) in Filter.atTop , ( binrel% HasSubset.Subset ( C ( A ( IRStatement.FirstTerms.firstTerms s t ) ) ) ( C z ) ) ) )
```

### *valid index on injective* · `GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidIndexOnInjective`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( A : ( ( Finset ℕ ) → ℕ ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidIndexOnInjective C A ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective s ) ) , ∀ ( _ : ( GenLimit.Presents s ( C z ) ) ) , ( ∀ᶠ ( t : ℕ ) in Filter.atTop , ( binrel% HasSubset.Subset ( C ( A ( IRStatement.FirstTerms.firstTerms s t ) ) ) ( C z ) ) ) )
```

### *vanishing* · `GenLimit.KleinbergWei.DensityMeasures.SetDriven.Vanishing`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( z : ℕ ) , ∀ ( O : GenLimit.KleinbergWei.OrderedLanguage ) , ( ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.Vanishing C z O ) ) ↔ ( ∀ ( A : ( ( Finset ℕ ) → ℕ ) ) , ∀ ( _ : ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.ValidIndex C A ) ) , ( ∃ s : ( ℕ → ℕ ) , ( ( GenLimit.Presents s ( C z ) ) ∧ ( ( GenLimit.KleinbergWei.DensityMeasures.indexBreadth C O ( GenLimit.KleinbergWei.DensityMeasures.SetDriven.asHistory A ) s ) = 0 ) ) ) )
```

## P08

SHA-256 of the checked page: `a29362913f08f0f749028527774f88f77c15c184dd9f25631b83d6070386ee5a`

### *detector* · `GenLimit.HallucinationDetection.Detector`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.HallucinationDetection.Detector α ) = ( GenLimit.Generic.FiniteHistoryOperator α ( GenLimit.HallucinationDetection.OracleTree α ) ) )
```

### *detects hallucinations* · `GenLimit.HallucinationDetection.DetectsHallucinations`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( D : ( GenLimit.HallucinationDetection.Detector α ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.HallucinationDetection.DetectsHallucinations D C ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( C z ) ) ) , ∀ ( G : ( Set α ) ) , depends_only% [ α , D , C , z , x , G ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.HallucinationDetection.DetectorCorrectAt D G ( C z ) x t ) ) ) )
```

### *detects with negative examples* · `GenLimit.HallucinationDetection.DetectsWithNegativeExamples`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( D : ( GenLimit.HallucinationDetection.NegativeExampleDetector α ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.HallucinationDetection.DetectsWithNegativeExamples D C ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.HallucinationDetection.LabeledStream α ) ) , ∀ ( _ : ( GenLimit.HallucinationDetection.IsLabeledEnumeration x ( C z ) ) ) , ∀ ( G : ( Set α ) ) , depends_only% [ α , D , C , z , x , G ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.HallucinationDetection.NegativeDetectorCorrectAt D G ( C z ) x t ) ) ) )
```

### *identifiable in limit* · `GenLimit.HallucinationDetection.IdentifiableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.HallucinationDetection.IdentifiableInLimit C ) ) ↔ ( ( GenLimit.Angluin.SemanticallyInferrable C ) )
```

### *negative example detector* · `GenLimit.HallucinationDetection.NegativeExampleDetector`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.HallucinationDetection.NegativeExampleDetector α ) = ( GenLimit.Generic.FiniteHistoryOperator ( α × Bool ) ( GenLimit.HallucinationDetection.OracleTree α ) ) )
```

## P09

SHA-256 of the checked page: `760fec0439c611adc901e82221455928379edd130cec0eb84bb58c79f6feab42`

### *alpha representative uniformly generatable* · `GenLimit.RepresentativeGeneration.AlphaRepresentativeUniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( groups : ( ℕ → ( Set α ) ) ) , ∀ ( alpha : ℝ ) , ( ( GenLimit.RepresentativeGeneration.AlphaRepresentativeUniformlyGeneratable H groups alpha ) ) ↔ ( ( ∃ gen : ( GenLimit.RepresentativeGeneration.RandomizedGenerator α ) , ( ( GenLimit.RepresentativeGeneration.IsAlphaRepresentative gen groups alpha ) ) ∧ ( depends_only% [ α , H , groups , alpha , gen ] ( ∃ d : ℕ , ∀ L ∈ H , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.StreamIn x L ) ) , ∀ ( t : ℕ ) , ∀ ( _ : ( ( Finset.card ( IRStatement.FirstTerms.firstTerms x t ) ) = d ) ) , ( GenLimit.RepresentativeGeneration.IsConsistentFrom gen L x t ) ) ) ) )
```

### *finite exact profile points* · `GenLimit.RepresentativeGeneration.finiteExactProfilePoints`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ∀ ( groups : ( ℕ → ( Set α ) ) ) , ( ( GenLimit.RepresentativeGeneration.finiteExactProfilePoints L groups ) = { x : α | ( ( x ∈ L ) ∧ ( Set.Finite ( L ∩ ( GenLimit.RepresentativeGeneration.exactGroupCell groups x ) ) ) ) } )
```

### *has finite group closure dimension* · `GenLimit.RepresentativeGeneration.HasFiniteGroupClosureDimension`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( groups : ( ℕ → ( Set α ) ) ) , ∀ ( alpha : ℝ ) , ( ( GenLimit.RepresentativeGeneration.HasFiniteGroupClosureDimension H groups alpha ) ) ↔ ( depends_only% [ α , H , groups , alpha ] ( ∃ d : ℕ , ∀ ( S : ( Finset α ) ) , ∀ ( _ : ( GenLimit.RepresentativeGeneration.IsGroupClosureWitness H groups alpha S ) ) , ( ( Finset.card S ) ≤ d ) ) )
```

### *is countable partition* · `GenLimit.RepresentativeGeneration.IsCountablePartition`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( groups : ( ℕ → ( Set α ) ) ) , ( ( GenLimit.RepresentativeGeneration.IsCountablePartition groups ) ) ↔ ( ( ∀ ( i j : ℕ ) , ∀ ( _ : ( i ≠ j ) ) , ( Disjoint ( groups i ) ( groups j ) ) ) ∧ ( ( ( Set.iUnion ( fun i => ( groups i ) ) ) = Set.univ ) ) )
```

### *language class* · `GenLimit.Generic.LanguageClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.LanguageClass α ) = ( Set ( GenLimit.Generic.Language α ) ) )
```

### *representatively generatable in limit* · `GenLimit.RepresentativeGeneration.RepresentativelyGeneratableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( groups : ( ℕ → ( Set α ) ) ) , ( ( GenLimit.RepresentativeGeneration.RepresentativelyGeneratableInLimit H groups ) ) ↔ ( ∀ ( alpha : ℝ ) , ∀ ( _ : ( 0 < alpha ) ) , ( ∃ gen : ( GenLimit.RepresentativeGeneration.RandomizedGenerator α ) , ( ( GenLimit.RepresentativeGeneration.IsAlphaRepresentative gen groups alpha ) ) ∧ ( ∀ L ∈ H , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x L ) ) , ( ∃ T : ℕ , ( GenLimit.RepresentativeGeneration.IsConsistentFrom gen L x T ) ) ) ) )
```

### *representatively nonuniformly generatable* · `GenLimit.RepresentativeGeneration.RepresentativelyNonuniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( groups : ( ℕ → ( Set α ) ) ) , ( ( GenLimit.RepresentativeGeneration.RepresentativelyNonuniformlyGeneratable H groups ) ) ↔ ( ∀ ( alpha : ℝ ) , ∀ ( _ : ( 0 < alpha ) ) , ( ∃ gen : ( GenLimit.RepresentativeGeneration.RandomizedGenerator α ) , ( ( GenLimit.RepresentativeGeneration.IsAlphaRepresentative gen groups alpha ) ) ∧ ( ∀ L ∈ H , depends_only% [ α , H , groups , alpha , gen , L ] ( ∃ d : ℕ , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.StreamIn x L ) ) , ∀ ( t : ℕ ) , ∀ ( _ : ( ( Finset.card ( IRStatement.FirstTerms.firstTerms x t ) ) = d ) ) , ( GenLimit.RepresentativeGeneration.IsConsistentFrom gen L x t ) ) ) ) )
```

### *UUS* · `GenLimit.Generic.UUS`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.UUS H ) ) ↔ ( ∀ L ∈ H , ( Set.Infinite L ) )
```

## P10

SHA-256 of the checked page: `7782131bb4a238f6478121108064c5b214c13788ef304c9b422db3969cfb6677`

### *eventually unbounded closure* · `GenLimit.LiRamanTewari.EventuallyUnboundedClosure`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.EventuallyUnboundedClosure H ) ) ↔ ( ∀ L ∈ H , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x L ) ) , ( ∃ t : ℕ , ( Set.Infinite ( GenLimit.LiRamanTewari.commonCore H ( IRStatement.FirstTerms.firstTerms x t ) ) ) ) )
```

### *finite negative infinite positive class* · `GenLimit.UnionClosedness.finiteNegativeInfinitePositiveClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.UnionClosedness.finiteNegativeInfinitePositiveClass = { L : ( GenLimit.Generic.Language ℤ ) | ( ∃ A : ( Set ℤ ) , ( ∃ B : ( Set ℤ ) , ( ( binrel% HasSubset.Subset A GenLimit.UnionClosedness.negativeIntegers ) ∧ ( ( Set.Finite A ) ∧ ( ( binrel% HasSubset.Subset B GenLimit.UnionClosedness.positiveIntegers ) ∧ ( ( Set.Infinite B ) ∧ ( L = ( GenLimit.UnionClosedness.signedDeletionLanguage A B ) ) ) ) ) ) ) ) } )
```

### *generatable in limit on injective presentations* · `GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations H ) ) ↔ ( ( ∃ G : ( GenLimit.Generic.Generator α ) , ( GenLimit.UnionClosedness.IsLimitGeneratorOnInjectivePresentations G H ) ) )
```

### *infinite negative finite positive class* · `GenLimit.UnionClosedness.infiniteNegativeFinitePositiveClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.UnionClosedness.infiniteNegativeFinitePositiveClass = { L : ( GenLimit.Generic.Language ℤ ) | ( ∃ A : ( Set ℤ ) , ( ∃ B : ( Set ℤ ) , ( ( binrel% HasSubset.Subset A GenLimit.UnionClosedness.negativeIntegers ) ∧ ( ( Set.Infinite A ) ∧ ( ( binrel% HasSubset.Subset B GenLimit.UnionClosedness.positiveIntegers ) ∧ ( ( Set.Finite B ) ∧ ( L = ( GenLimit.UnionClosedness.signedDeletionLanguage A B ) ) ) ) ) ) ) ) } )
```

### *nonuniformly generatable* · `GenLimit.Generic.NonuniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.NonuniformlyGeneratable H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.Generic.IsNonuniformGenerator gen H ) ) )
```

### *nonuniformly generatable without adversary input* · `GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput H ) ) ↔ ( ( ∃ outputs : ( GenLimit.UnionClosedness.NoAdversaryInputSchedule α ) , ( GenLimit.UnionClosedness.IsNonuniformNoAdversaryInputSchedule outputs H ) ) )
```

### *theorem 43 first class* · `GenLimit.UnionClosedness.theorem43FirstClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.UnionClosedness.theorem43FirstClass = { L : ( GenLimit.Generic.Language ℤ ) | ( ∃ A : ( Set ℤ ) , ( ( binrel% HasSubset.Subset A GenLimit.UnionClosedness.positiveIntegers ) ∧ ( L = ( GenLimit.UnionClosedness.theorem43FirstLanguage A ) ) ) ) } )
```

### *theorem 43 second class* · `GenLimit.UnionClosedness.theorem43SecondClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.UnionClosedness.theorem43SecondClass = { L : ( GenLimit.Generic.Language ℤ ) | ( ∃ i : ℕ , ( ∃ B : ( Set ℤ ) , ( ( binrel% HasSubset.Subset B GenLimit.UnionClosedness.positiveIntegers ) ∧ ( ( Set.Finite B ) ∧ ( ( ( i = 0 ) → ( B = EmptyCollection.emptyCollection ) ) ∧ ( L = ( GenLimit.UnionClosedness.theorem43SecondLanguage i B ) ) ) ) ) ) ) } )
```

### *uniformly generatable* · `GenLimit.Generic.UniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.UniformlyGeneratable H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ∃ d : ℕ , ( GenLimit.Generic.IsUniformGeneratorAt gen H d ) ) )
```

### *uniformly generatable without adversary input* · `GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput H ) ) ↔ ( ( ∃ outputs : ( GenLimit.UnionClosedness.NoAdversaryInputSchedule α ) , ∃ T : ℕ , ( GenLimit.UnionClosedness.IsUniformNoAdversaryInputScheduleAt outputs H T ) ) )
```

## P11

SHA-256 of the checked page: `1472e51f57760c56a261e5fc46a375a06be472af81ab75ed9abdd9c99d7a798d`

### *has mass* · `GenLimit.LearningAlgorithmsLimit.NativeTape.HasMass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Γ α : Type ) , ∀ [ Inhabited Γ ] , ∀ [ DecidableEq Γ ] , ∀ [ Primcodable Γ ] , ∀ ( O : Type _ ) , ∀ ( R : Sort _ ) , ∀ ( ι : ( α ↪ Γ ) ) , ∀ ( A : ( ( Set ( ( List α ) × O ) ) → R ) ) , ∀ ( rep : ( R → ( ( List α ) → ( Option ( List α ) ) ) ) ) , ∀ ( obs : ( ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) → ( ( List α ) → O ) ) ) , ∀ ( cost : ( ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) → ( ( List α ) → ℕ ) ) ) , ∀ ( β : ( ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) → ℕ ) ) , ( ( GenLimit.LearningAlgorithmsLimit.NativeTape.HasMass ι A rep obs cost β ) ) ↔ ( ∀ ( P : ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.NativeTape.linearTotal ι P ) ) , ( ∃ S : ( Finset ( List α ) ) , ( ( GenLimit.LearningAlgorithmsLimit.NativeTape.Characteristic ι A rep obs P ( Finset.toSet S ) ) ∧ ( ( Finset.sum S ( fun x_3 => ( cost P x_3 ) ) ) ≤ ( β P ) ) ) ) )
```

### *has selector* · `GenLimit.LearningAlgorithmsLimit.NativeTape.HasSelector`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Γ α : Type ) , ∀ [ Inhabited Γ ] , ∀ [ DecidableEq Γ ] , ∀ [ Primcodable Γ ] , ∀ [ Primcodable α ] , ∀ ( O : Type _ ) , ∀ ( R : Sort _ ) , ∀ ( ι : ( α ↪ Γ ) ) , ∀ ( A : ( ( Set ( ( List α ) × O ) ) → R ) ) , ∀ ( rep : ( R → ( ( List α ) → ( Option ( List α ) ) ) ) ) , ∀ ( obs : ( ( GenLimit.LearningAlgorithmsLimit.TuringProgram Γ ) → ( ( List α ) → O ) ) ) , ( ( GenLimit.LearningAlgorithmsLimit.NativeTape.HasSelector ι A rep obs ) ) ↔ ( ( ∃ C : ( ( GenLimit.LearningAlgorithmsLimit.EffectiveTable.Table Γ ) → ( List ( List α ) ) ) , ( ( Computable C ) ) ∧ ( ( ∀ T : ( GenLimit.LearningAlgorithmsLimit.EffectiveTable.Table Γ ) , ( GenLimit.LearningAlgorithmsLimit.NativeTape.Characteristic ι A rep obs ( GenLimit.LearningAlgorithmsLimit.EffectiveTable.unpack T ) { x_4 : ( List α ) | ( x_4 ∈ ( C T ) ) } ) ) ) ) )
```

### *IO algorithm* · `GenLimit.LearningAlgorithmsLimit.Rational.IOAlgorithm`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A B : Type _ ) , ( ( GenLimit.LearningAlgorithmsLimit.Rational.IOAlgorithm A B ) = ( GenLimit.Learner ( GenLimit.LearningAlgorithmsLimit.LabeledObservation ( List A ) B ) ( GenLimit.LearningAlgorithmsLimit.Rational.Table B ) ) )
```

### *is MSM choice* · `GenLimit.LearningAlgorithmsLimit.IsMSMChoice`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Candidate Config : Type _ ) , ∀ [ DecidableEq Candidate ] , ∀ ( candidates : ( Config → ( Finset Candidate ) ) ) , ∀ ( score : ( Config → ( Candidate → ℕ ) ) ) , ∀ ( config : Config ) , ∀ ( choice : Candidate ) , ( ( GenLimit.LearningAlgorithmsLimit.IsMSMChoice candidates score config choice ) ) ↔ ( ( ( choice ∈ ( candidates config ) ) ) ∧ ( ( ( 0 < ( score config choice ) ) ) ∧ ( ( ∀ other ∈ ( candidates config ) , ( ( score config other ) ≤ ( score config choice ) ) ) ) ) )
```

### *labeled enumeration learner* · `GenLimit.LearningAlgorithmsLimit.labeledEnumerationLearner`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Output Input : Type _ ) , ∀ [ DecidableEq Output ] , ∀ ( semantics : ( ℕ → ( Input → ( Option Output ) ) ) ) , ( ( GenLimit.LearningAlgorithmsLimit.labeledEnumerationLearner semantics ) = ( GenLimit.LearningAlgorithmsLimit.enumerationLearner ( GenLimit.LearningAlgorithmsLimit.labeledFits semantics ) ) )
```

### *labeled stream* · `GenLimit.LearningAlgorithmsLimit.labeledStream`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Input Output : Type _ ) , ∀ ( target : ( Input → ( Option Output ) ) ) , ∀ ( x : ( ℕ → Input ) ) , ∀ ( n : ℕ ) , ( ( GenLimit.LearningAlgorithmsLimit.labeledStream target x n ) = ( GenLimit.LearningAlgorithmsLimit.LabeledObservation.mk ( x n ) ( target ( x n ) ) ) )
```

### *late split observation* · `GenLimit.LearningAlgorithmsLimit.lateSplitObservation`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( splitAt : ℕ ) , ∀ ( branch : Bool ) , ∀ ( inputLength : ℕ ) , ( ( GenLimit.LearningAlgorithmsLimit.lateSplitObservation splitAt branch inputLength ) = ( ite ( LE.le splitAt inputLength ) branch Bool.false ) )
```

### *learns by criterion* · `GenLimit.LearningAlgorithmsLimit.LearnsByCriterion`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Info Rep : Type _ ) , ∀ ( learner : ( GenLimit.Learner Info Rep ) ) , ∀ ( information : ( ℕ → Info ) ) , ∀ ( correct : ( Rep → Prop ) ) , ( ( GenLimit.LearningAlgorithmsLimit.LearnsByCriterion learner information correct ) ) ↔ ( ( ∃ representation : Rep , ( ( correct representation ) ∧ ( GenLimit.StabilizesTo ( fun t => ( learner ( GenLimit.textPrefix information t ) ) ) representation ) ) ) )
```

### *learns in limit* · `GenLimit.LearningAlgorithmsLimit.LearnsInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Info Rep Input Output : Type _ ) , ∀ ( learner : ( GenLimit.Learner Info Rep ) ) , ∀ ( information : ( ℕ → Info ) ) , ∀ ( semantics : ( Rep → ( Input → ( Option Output ) ) ) ) , ∀ ( target : ( Input → ( Option Output ) ) ) , ∀ ( source : ( Set Input ) ) , ( ( GenLimit.LearningAlgorithmsLimit.LearnsInLimit learner information semantics target source ) ) ↔ ( ( GenLimit.LearningAlgorithmsLimit.LearnsByCriterion learner information ( GenLimit.LearningAlgorithmsLimit.CorrectOn semantics target source ) ) )
```

### *learns with samples* · `GenLimit.LearningAlgorithmsLimit.MSM.Learning.LearnsWithSamples`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( σ : Type ) , ∀ [ Fintype σ ] , ∀ [ Encodable σ ] , ∀ [ DecidableEq σ ] , ∀ ( X Y : Type _ ) , ∀ ( en : ( ( GenLimit.LearningAlgorithmsLimit.Policy.Event σ ) → ( ℕ × ℕ ) ) ) , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO σ X Y ) ) , let K := ( GenLimit.LearningAlgorithmsLimit.TuringIO.blank io ) ; ∀ ( P : ( GenLimit.LearningAlgorithmsLimit.TuringProgram σ ) ) , ∀ ( f : ( X → Y ) ) , ∀ ( I : ( Set X ) ) , ∀ ( budget : ℕ ) , ( ( GenLimit.LearningAlgorithmsLimit.MSM.Learning.LearnsWithSamples en io P f I budget ) ) ↔ ( ( ∀ ( h : ( List ( GenLimit.LearningAlgorithmsLimit.Policy.Observation σ X Y ) ) ) , ∀ ( _ : ( ∀ o ∈ h , ( GenLimit.LearningAlgorithmsLimit.MSM.Learning.Valid io P f I o ) ) ) , ( GenLimit.LearningAlgorithmsLimit.MSM.Replay.IsMSMOutput en K ( GenLimit.LearningAlgorithmsLimit.MSM.Learning.samples h ) ( GenLimit.LearningAlgorithmsLimit.MSM.Learning.learner en K h ) ) ) ∧ ( ( ∃ core : ( Finset X ) , ( ( binrel% HasSubset.Subset core I ) ) ∧ ( ( ( ( Finset.card core ) ≤ budget ) ) ∧ ( ( ∃ Q : ( GenLimit.LearningAlgorithmsLimit.TuringProgram σ ) , ( ( GenLimit.LearningAlgorithmsLimit.TuringComputesOn io Q f I ) ) ∧ ( ( ∀ ( h : ( List ( GenLimit.LearningAlgorithmsLimit.Policy.Observation σ X Y ) ) ) , ∀ ( _ : ( ∀ o ∈ h , ( GenLimit.LearningAlgorithmsLimit.MSM.Learning.Valid io P f I o ) ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.MSM.Learning.HasCore h core ) ) , ( ( GenLimit.LearningAlgorithmsLimit.MSM.Learning.learner en K h ) = Q ) ) ∧ ( ∀ ( s : ( ℕ → ( GenLimit.LearningAlgorithmsLimit.Policy.Observation σ X Y ) ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.Covers ( fun n => ( GenLimit.LearningAlgorithmsLimit.Policy.Observation.input ( s n ) ) ) I ) ) , ∀ ( _ : ( ∀ n : ℕ , ( GenLimit.LearningAlgorithmsLimit.MSM.Learning.Valid io P f I ( s n ) ) ) ) , ( GenLimit.StabilizesTo ( fun t => ( GenLimit.LearningAlgorithmsLimit.MSM.Learning.learner en K ( GenLimit.textPrefix s t ) ) ) Q ) ) ) ) ) ) ) ) )
```

### *lift learner along forget* · `GenLimit.LearningAlgorithmsLimit.liftLearnerAlongForget`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Input Poor : Type _ ) , ∀ ( Rep : Sort _ ) , ∀ ( Rich : Type _ ) , ∀ ( learner : ( ( Set ( Input × Poor ) ) → Rep ) ) , ∀ ( forget : ( Rich → Poor ) ) , ∀ ( examples : ( Set ( Input × Rich ) ) ) , ( ( GenLimit.LearningAlgorithmsLimit.liftLearnerAlongForget learner forget examples ) = ( learner ( GenLimit.LearningAlgorithmsLimit.forgetExamples forget examples ) ) )
```

### *marker action* · `GenLimit.LearningAlgorithmsLimit.markerAction`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( State Tape : Type _ ) , ∀ ( transition : ( State × Tape ) ) , ( ( GenLimit.LearningAlgorithmsLimit.markerAction transition ) = ( GenLimit.LearningAlgorithmsLimit.TapeAction.mk ( Sum.inr transition ) GenLimit.LearningAlgorithmsLimit.HeadMove.stay ) )
```

### *min index diagnostic run* · `GenLimit.LearningAlgorithmsLimit.minIndexDiagnosticRun`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( budget representation : ℕ ) , ∀ ( x : Unit ) , ( ( GenLimit.LearningAlgorithmsLimit.minIndexDiagnosticRun budget representation x ) = ( ite ( Eq representation 0 ) ( ite ( LE.le 10 budget ) ( Option.some Bool.false ) Option.none ) ( ite ( Eq representation 1 ) ( ite ( LE.le 2 budget ) ( Option.some Bool.false ) Option.none ) Option.none ) ) )
```

### *MSM step* · `GenLimit.LearningAlgorithmsLimit.MSMStep`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Candidate Config : Type _ ) , ∀ [ DecidableEq Candidate ] , ∀ ( candidates : ( Config → ( Finset Candidate ) ) ) , ∀ ( score : ( Config → ( Candidate → ℕ ) ) ) , ∀ ( merge : ( Config → ( Candidate → Config ) ) ) , ∀ ( config next : Config ) , ( ( GenLimit.LearningAlgorithmsLimit.MSMStep candidates score merge config next ) ) ↔ ( ( ∃ choice : Candidate , ( ( GenLimit.LearningAlgorithmsLimit.IsMSMChoice candidates score config choice ) ∧ ( next = ( merge config choice ) ) ) ) )
```

### *QECTT* · `GenLimit.LearningAlgorithmsLimit.Quantitative.QECTT`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( σ X Y : Type _ ) , ∀ [ Encodable σ ] , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO σ X Y ) ) , ∀ ( q : ( ℕ → ( ℕ → ℕ ) ) ) , ∀ ( M : ( Set ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher X Y ) ) ) , ( ( GenLimit.LearningAlgorithmsLimit.Quantitative.QECTT io q M ) ) ↔ ( ∀ m ∈ M , depends_only% [ σ , X , Y , io , q , M , m ] ( ∃ c : ℕ , ∃ P : ( GenLimit.LearningAlgorithmsLimit.TuringProgram σ ) , ∀ x_1 ∈ ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.domain m ) , ( ( GenLimit.LearningAlgorithmsLimit.TuringProgram.runWithin ( q c ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.steps m x_1 ) ) io P x_1 ) = ( Option.some ( GenLimit.LearningAlgorithmsLimit.Quantitative.Teacher.value m x_1 ) ) ) ) )
```

### *rational semantics* · `GenLimit.LearningAlgorithmsLimit.rationalSemantics`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( State A B : Type _ ) , ∀ ( M : ( GenLimit.LearningAlgorithmsLimit.Mealy State A B ) ) , ∀ ( input : ( List A ) ) , ( ( GenLimit.LearningAlgorithmsLimit.rationalSemantics M input ) = ( Option.some ( Prod.snd ( GenLimit.LearningAlgorithmsLimit.Mealy.run M input ) ) ) )
```

### *reduced learner* · `GenLimit.LearningAlgorithmsLimit.Policy.reducedLearner`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( σ X Y : Type _ ) , ∀ [ Encodable σ ] , ∀ [ Fintype σ ] , ∀ ( R : ( GenLimit.LearningAlgorithmsLimit.Rational.IOAlgorithm σ ( GenLimit.LearningAlgorithmsLimit.Policy.Action σ ) ) ) , ∀ ( blank : σ ) , ∀ ( history : ( List ( GenLimit.LearningAlgorithmsLimit.Policy.Observation σ X Y ) ) ) , ( ( GenLimit.LearningAlgorithmsLimit.Policy.reducedLearner R blank history ) = ( GenLimit.LearningAlgorithmsLimit.Policy.product ( R ( GenLimit.LearningAlgorithmsLimit.Policy.convert blank ( fun a => ( fun ( x_2 : Bool ) => a ) ) history ) ) ( R ( GenLimit.LearningAlgorithmsLimit.Policy.convert blank ( fun ( x_2 : ( GenLimit.LearningAlgorithmsLimit.Policy.Action σ ) ) => ( fun done => ( GenLimit.LearningAlgorithmsLimit.Policy.marker blank done ) ) ) history ) ) blank ) )
```

### *run* · `GenLimit.LearningAlgorithmsLimit.Mealy.run`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( State Input Output : Type _ ) , ∀ ( M : ( GenLimit.LearningAlgorithmsLimit.Mealy State Input Output ) ) , ∀ ( w : ( List Input ) ) , ( ( GenLimit.LearningAlgorithmsLimit.Mealy.run M w ) = ( GenLimit.LearningAlgorithmsLimit.Mealy.runFrom M ( GenLimit.LearningAlgorithmsLimit.Mealy.start M ) w ) )
```

### *semantics* · `GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.semantics`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Input Output : Type _ ) , ∀ ( enumeration : ( GenLimit.LearningAlgorithmsLimit.BoundedEnumeration Input Output ) ) , ∀ ( candidate : ℕ ) , let D := ( GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.decode enumeration candidate ) ; ∀ ( input : Input ) , ( ( GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.semantics enumeration candidate input ) = ( GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.runWithin enumeration ( Prod.fst D ) ( Prod.snd D ) input ) )
```

### *solves* · `GenLimit.LearningAlgorithmsLimit.Rational.Solves`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A B : Type _ ) , ∀ [ Encodable A ] , ∀ ( R : ( GenLimit.LearningAlgorithmsLimit.Rational.IOAlgorithm A B ) ) , ( ( GenLimit.LearningAlgorithmsLimit.Rational.Solves R ) ) ↔ ( ∀ ( T : ( GenLimit.LearningAlgorithmsLimit.Rational.Table B ) ) , ∀ ( s : ( ℕ → ( List A ) ) ) , ∀ ( _ : ( ∀ n : ℕ , ( ( s n ) ≠ [] ) ) ) , ( GenLimit.LearningAlgorithmsLimit.LearnsByCriterion R ( GenLimit.LearningAlgorithmsLimit.labeledStream ( fun w => ( Option.some ( GenLimit.LearningAlgorithmsLimit.Rational.Table.output T w ) ) ) s ) ( fun E => ( ∀ w ∈ ( Set.range s ) , ( ( GenLimit.LearningAlgorithmsLimit.Rational.Table.output E w ) = ( GenLimit.LearningAlgorithmsLimit.Rational.Table.output T w ) ) ) ) ) )
```

### *solves turing TBO* · `GenLimit.LearningAlgorithmsLimit.SolvesTuringTBO`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Symbol Input Output : Type _ ) , ∀ [ Encodable Symbol ] , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO Symbol Input Output ) ) , ∀ ( learner : ( GenLimit.Learner ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation Input Output ) ℕ ) ) , ( ( GenLimit.LearningAlgorithmsLimit.SolvesTuringTBO io learner ) ) ↔ ( ∀ ( targetProgram : ( GenLimit.LearningAlgorithmsLimit.TuringProgram Symbol ) ) , ∀ ( source : ( Set Input ) ) , ∀ ( x : ( ℕ → Input ) ) , ∀ ( observation : ( Input → ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation Input Output ) ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.Covers x source ) ) , ∀ ( _ : ( GenLimit.LearningAlgorithmsLimit.IsTuringTimeBoundObservation io targetProgram observation source ) ) , ( GenLimit.LearningAlgorithmsLimit.LearnsByCriterion learner ( fun n => ( observation ( x n ) ) ) ( fun candidate => ( GenLimit.LearningAlgorithmsLimit.TuringCandidateComputesOn io candidate ( fun input => ( GenLimit.LearningAlgorithmsLimit.TimeBoundObservation.value ( observation input ) ) ) source ) ) ) )
```

### *states* · `GenLimit.LearningAlgorithmsLimit.Policy.states`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( σ : Type _ ) , ∀ ( P : ( GenLimit.LearningAlgorithmsLimit.TuringProgram σ ) ) , ( ( GenLimit.LearningAlgorithmsLimit.Policy.states P ) = ( Insert.insert 1 ( Insert.insert 0 ( List.toFinset ( List.map Prod.fst P ) ) ) ) )
```

### *tape behavior* · `GenLimit.LearningAlgorithmsLimit.PolicyMachine.tapeBehavior`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( State Tape : Type _ ) , ∀ ( M : ( GenLimit.LearningAlgorithmsLimit.PolicyMachine State Tape ) ) , ∀ ( scanned : ( List Tape ) ) , ( ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.tapeBehavior M scanned ) = ( Prod.snd ( GenLimit.LearningAlgorithmsLimit.Mealy.run ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST M ) scanned ) ) )
```

### *time observed learner* · `GenLimit.LearningAlgorithmsLimit.timeObservedLearner`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Output Input : Type _ ) , ∀ [ DecidableEq Output ] , ∀ ( simulate : ( ℕ → ( Input → ( ℕ → ( Option Output ) ) ) ) ) , ( ( GenLimit.LearningAlgorithmsLimit.timeObservedLearner simulate ) = ( GenLimit.LearningAlgorithmsLimit.enumerationLearner ( GenLimit.LearningAlgorithmsLimit.timeObservedFits simulate ) ) )
```

### *to FST* · `GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( State Tape : Type _ ) , ∀ ( M : ( GenLimit.LearningAlgorithmsLimit.PolicyMachine State Tape ) ) , ( ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST M ) = ( GenLimit.LearningAlgorithmsLimit.Mealy.mk ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.start M ) ( GenLimit.LearningAlgorithmsLimit.PolicyMachine.step M ) ) )
```

### *turing computes on* · `GenLimit.LearningAlgorithmsLimit.TuringComputesOn`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Symbol Input Output : Type _ ) , ∀ [ Encodable Symbol ] , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO Symbol Input Output ) ) , ∀ ( program : ( GenLimit.LearningAlgorithmsLimit.TuringProgram Symbol ) ) , ∀ ( target : ( Input → Output ) ) , ∀ ( source : ( Set Input ) ) , ( ( GenLimit.LearningAlgorithmsLimit.TuringComputesOn io program target source ) ) ↔ ( ∀ input ∈ source , ( ∃ budget : ℕ , ( ( GenLimit.LearningAlgorithmsLimit.TuringProgram.runWithin budget io program input ) = ( Option.some ( target input ) ) ) ) )
```

### *turing program* · `GenLimit.LearningAlgorithmsLimit.TuringProgram`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Symbol : Type _ ) , ( ( GenLimit.LearningAlgorithmsLimit.TuringProgram Symbol ) = ( List ( GenLimit.LearningAlgorithmsLimit.TuringInstruction Symbol ) ) )
```

### *turing TBO learner* · `GenLimit.LearningAlgorithmsLimit.turingTBOLearner`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Symbol Output Input : Type _ ) , ∀ [ Encodable Symbol ] , ∀ [ DecidableEq Output ] , ∀ ( io : ( GenLimit.LearningAlgorithmsLimit.TuringIO Symbol Input Output ) ) , ( ( GenLimit.LearningAlgorithmsLimit.turingTBOLearner io ) = ( GenLimit.LearningAlgorithmsLimit.enumerationLearner ( GenLimit.LearningAlgorithmsLimit.turingTBOFits io ) ) )
```

### *word observation* · `GenLimit.LearningAlgorithmsLimit.NativeTape.WordObservation`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α Γ : Type ) , ( ( GenLimit.LearningAlgorithmsLimit.NativeTape.WordObservation α Γ ) = ( ( Option ( List α ) ) × ( Unit ⊕ ( ℕ ⊕ ( List ( GenLimit.LearningAlgorithmsLimit.Policy.Event Γ ) ) ) ) ) )
```

## P12

SHA-256 of the checked page: `e354dff25f0c84737252a20cbddf7463c7acca7daadb2086e98b05eb61a0716e`

### *generatable in limit with noise level* · `GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( i : ℕ ) , ( ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel C i ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.NoiseLossFeedback.IsLimitGeneratorWithNoiseLevel gen C i ) ) )
```

### *generatable in limit with omissions* · `GenLimit.NoiseLossFeedback.GeneratableInLimitWithOmissions`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( i : ℕ ) , ( ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithOmissions C i ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.NoiseLossFeedback.IsLimitGeneratorWithOmissions gen C i ) ) )
```

### *generatable in limit with queries* · `GenLimit.NoiseLossFeedback.GeneratableInLimitWithQueries`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( budget : ℕ ) , ( ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithQueries C budget ) ) ↔ ( ( ∃ gen : ( GenLimit.NoiseLossFeedback.FeedbackGenerator α ) , ( GenLimit.NoiseLossFeedback.IsLimitFeedbackGeneratorWithQueries gen C budget ) ) )
```

### *generatable in limit with total feedback* · `GenLimit.NoiseLossFeedback.GeneratableInLimitWithTotalFeedback`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithTotalFeedback C ) ) ↔ ( ( ∃ gen : ( GenLimit.NoiseLossFeedback.TotalFeedbackGenerator α ) , ( GenLimit.NoiseLossFeedback.IsLimitTotalFeedbackGenerator gen C ) ) )
```

### *generatable in limit without repetitions* · `GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutRepetitions`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutRepetitions C ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.NoiseLossFeedback.IsLimitGeneratorWithoutRepetitions gen C ) ) )
```

### *generatable in limit without samples* · `GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutSamples`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.GeneratableInLimitWithoutSamples C ) ) ↔ ( ( ∃ gen : ( GenLimit.NoiseLossFeedback.WithoutSamplesGenerator α ) , ( GenLimit.NoiseLossFeedback.GeneratesInLimitWithoutSamples gen C ) ) )
```

### *generator* · `GenLimit.Generic.Generator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.Generator α ) = ( GenLimit.Generic.FiniteHistoryOperator α α ) )
```

### *has increasing infinite core cover* · `GenLimit.NoiseLossFeedback.HasIncreasingInfiniteCoreCover`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.HasIncreasingInfiniteCoreCover C ) ) ↔ ( ( ∃ classes : ( ℕ → ( GenLimit.Generic.LanguageClass α ) ) , ( GenLimit.NoiseLossFeedback.IsIncreasingInfiniteCoreCover C classes ) ) )
```

### *is nonuniform generator* · `GenLimit.NoiseLossFeedback.IsNonuniformGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.Generic.Generator α ) ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.IsNonuniformGenerator gen C ) ) ↔ ( ( GenLimit.Generic.IsTargetwiseEventuallyCorrect GenLimit.NoiseLossFeedback.CorrectAt GenLimit.NoiseLossFeedback.ExactEnumeration gen C ) )
```

### *is nonuniform infinite omission generator* · `GenLimit.NoiseLossFeedback.IsNonuniformInfiniteOmissionGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.Generic.Generator α ) ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.IsNonuniformInfiniteOmissionGenerator gen C ) ) ↔ ( ( GenLimit.Generic.IsTargetwiseEventuallyCorrect GenLimit.NoiseLossFeedback.CorrectAt GenLimit.NoiseLossFeedback.InfiniteOmissionEnumeration gen C ) )
```

### *is uniform generator* · `GenLimit.NoiseLossFeedback.IsUniformGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.Generic.Generator α ) ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.IsUniformGenerator gen C ) ) ↔ ( ( GenLimit.Generic.IsUniformEventuallyCorrect GenLimit.NoiseLossFeedback.CorrectAt GenLimit.NoiseLossFeedback.ExactEnumeration gen C ) )
```

### *is uniform infinite omission generator* · `GenLimit.NoiseLossFeedback.IsUniformInfiniteOmissionGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.Generic.Generator α ) ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.IsUniformInfiniteOmissionGenerator gen C ) ) ↔ ( ( GenLimit.Generic.IsUniformEventuallyCorrect GenLimit.NoiseLossFeedback.CorrectAt GenLimit.NoiseLossFeedback.InfiniteOmissionEnumeration gen C ) )
```

### *noisily generatable in limit* · `GenLimit.NoiseLossFeedback.NoisilyGeneratableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.NoisilyGeneratableInLimit C ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.NoiseLossFeedback.IsNoisyLimitGenerator gen C ) ) )
```

### *nonuniformly generatable without repetitions* · `GenLimit.NoiseLossFeedback.NonuniformlyGeneratableWithoutRepetitions`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.NonuniformlyGeneratableWithoutRepetitions C ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.NoiseLossFeedback.IsNonuniformGenerator gen C ) ) )
```

### *nonuniformly identifiable with feedback* · `GenLimit.NoiseLossFeedback.NonuniformlyIdentifiableWithFeedback`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.NoiseLossFeedback.NonuniformlyIdentifiableWithFeedback C ) ) ↔ ( ( ∃ identifier : ( GenLimit.NoiseLossFeedback.FeedbackIdentifier α ) , ( GenLimit.NoiseLossFeedback.NonuniformlyIdentifiesWithFeedback identifier C ) ) )
```

### *nonuniformly noisily generatable* · `GenLimit.NoiseLossFeedback.NonuniformlyNoisilyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.NonuniformlyNoisilyGeneratable C ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.NoiseLossFeedback.IsNonuniformNoisyGenerator gen C ) ) )
```

### *uniformly generatable without repetitions* · `GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutRepetitions`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutRepetitions C ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.NoiseLossFeedback.IsUniformGenerator gen C ) ) )
```

### *uniformly generatable without samples* · `GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutSamples`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.UniformlyGeneratableWithoutSamples C ) ) ↔ ( ( ∃ gen : ( GenLimit.NoiseLossFeedback.WithoutSamplesGenerator α ) , ( GenLimit.NoiseLossFeedback.UniformlyGeneratesWithoutSamples gen C ) ) )
```

### *uniformly noisily generatable* · `GenLimit.NoiseLossFeedback.UniformlyNoisilyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.NoiseLossFeedback.UniformlyNoisilyGeneratable C ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.NoiseLossFeedback.IsUniformNoisyGenerator gen C ) ) )
```

## P13

SHA-256 of the checked page: `122783a07e57618fb36f0abe27b7303c8fb74897400d105f04388984989e2b8b`

### *achieves noisy time vector* · `GenLimit.ParetoGeneration.AchievesNoisyTimeVector`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.ParetoGeneration.HistoryGenerator α ) ) , ∀ ( F : ( ℕ → ( Set α ) ) ) , ∀ ( noise : ( ℕ → ℕ ) ) , ∀ ( time : GenLimit.ParetoGeneration.TimeVector ) , ( ( GenLimit.ParetoGeneration.AchievesNoisyTimeVector G F noise time ) ) ↔ ( ∀ ( coordinate t : ℕ ) , ∀ ( xs : ( ( Fin t ) → α ) ) , ∀ ( _ : ( ( time coordinate ) ≤ t ) ) , ∀ ( _ : ( Function.Injective xs ) ) , ∀ ( _ : ( GenLimit.ParetoGeneration.NoiseContainedAt F noise coordinate ( GenLimit.Generic.sequenceSample xs ) ) ) , ( ( ( G t xs ) ∈ ( F coordinate ) ) ) ∧ ( ( ∀ k : ( Fin t ) , ( ( G t xs ) ≠ ( xs k ) ) ) ) )
```

### *achieves time vector* · `GenLimit.ParetoGeneration.AchievesTimeVector`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.ParetoGeneration.HistoryGenerator α ) ) , ∀ ( F : ( ℕ → ( Set α ) ) ) , ∀ ( time : GenLimit.ParetoGeneration.TimeVector ) , ( ( GenLimit.ParetoGeneration.AchievesTimeVector G F time ) ) ↔ ( ∀ ( i t : ℕ ) , ∀ ( xs : ( ( Fin t ) → α ) ) , ∀ ( _ : ( ( time i ) ≤ t ) ) , ∀ ( _ : ( Function.Injective xs ) ) , ∀ ( _ : ( ∀ k : ( Fin t ) , ( ( xs k ) ∈ ( F i ) ) ) ) , ( ( ( G t xs ) ∈ ( F i ) ) ) ∧ ( ( ∀ k : ( Fin t ) , ( ( G t xs ) ≠ ( xs k ) ) ) ) )
```

### *canonical complexity* · `GenLimit.ParetoGeneration.canonicalComplexity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( ℕ → ( Set α ) ) ) , ∀ ( i : ℕ ) , ( ( GenLimit.ParetoGeneration.canonicalComplexity F i ) = ( GenLimit.ParetoGeneration.ProcedureStage.complexity ( GenLimit.ParetoGeneration.canonicalProcedureStage F ( i + 1 ) ) i ) )
```

### *canonical noisy complexity* · `GenLimit.ParetoGeneration.canonicalNoisyComplexity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( ℕ → ( Set α ) ) ) , ∀ ( noise : ( ℕ → ℕ ) ) , ∀ ( coordinate : ℕ ) , ( ( GenLimit.ParetoGeneration.canonicalNoisyComplexity F noise coordinate ) = ( GenLimit.ParetoGeneration.NoisyProcedureStage.complexity ( GenLimit.ParetoGeneration.canonicalNoisyProcedureStage F noise ( coordinate + 1 ) ) coordinate ) )
```

### *generator* · `GenLimit.Generic.Generator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.Generator α ) = ( GenLimit.Generic.FiniteHistoryOperator α α ) )
```

### *is finite partition* · `GenLimit.RepresentativeGeneration.IsFinitePartition`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( k : ℕ ) , ∀ ( groups : ( ( Fin k ) → ( Set α ) ) ) , ( ( GenLimit.RepresentativeGeneration.IsFinitePartition groups ) ) ↔ ( ( GenLimit.RepresentativeGeneration.IsCountablePartition ( GenLimit.RepresentativeGeneration.extendFinitePartition groups ) ) )
```

### *noisy realizable time vectors* · `GenLimit.ParetoGeneration.NoisyRealizableTimeVectors`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( ℕ → ( Set α ) ) ) , ∀ ( noise : ( ℕ → ℕ ) ) , ( ( GenLimit.ParetoGeneration.NoisyRealizableTimeVectors F noise ) = { t : GenLimit.ParetoGeneration.TimeVector | ( ∃ G : ( GenLimit.ParetoGeneration.HistoryGenerator α ) , ( ( GenLimit.ParetoGeneration.AchievesNoisyTimeVector G F noise t ) ∧ ( GenLimit.ParetoGeneration.PositiveTimeVector t ) ) ) } )
```

### *pareto optimal* · `GenLimit.ParetoGeneration.ParetoOptimal`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Achievable : ( Set GenLimit.ParetoGeneration.TimeVector ) ) , ∀ ( t : GenLimit.ParetoGeneration.TimeVector ) , ( ( GenLimit.ParetoGeneration.ParetoOptimal Achievable t ) ) ↔ ( ∀ s ∈ Achievable , ∀ ( _ : ( GenLimit.ParetoGeneration.ImprovesSomewhere s t ) ) , ( GenLimit.ParetoGeneration.WorseSomewhere s t ) )
```

### *realizable* · `GenLimit.ParetoGeneration.Representative.Realizable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ DecidableEq α ] , ∀ ( F groups : ( ℕ → ( Set α ) ) ) , ∀ ( ε : ℝ ) , ( ( GenLimit.ParetoGeneration.Representative.Realizable F groups ε ) = { t : GenLimit.ParetoGeneration.TimeVector | ( ( GenLimit.ParetoGeneration.PositiveTimeVector t ) ∧ ( ∃ G : ( ( List α ) → ( GenLimit.RepresentativeGeneration.DiscreteDistribution α ) ) , ( ∀ xs : ( List α ) , ( ( Finset.Nonempty ( List.toFinset xs ) ) → ( ( ( GenLimit.RepresentativeGeneration.groupSupDistance ( G xs ) ( List.toFinset xs ) groups ) ≤ ( ENNReal.ofReal ε ) ) ∧ ( ∀ i : ℕ , ( ( ( t i ) ≤ Finset.card ( List.toFinset xs ) ) → ( ( binrel% HasSubset.Subset ( List.toFinset xs ) ( F i ) ) → ( GenLimit.RepresentativeGeneration.SupportedOn ( G xs ) ( ( F i ) \ ( List.toFinset xs ) ) ) ) ) ) ) ) ) ) ) } )
```

### *realizable time vectors* · `GenLimit.ParetoGeneration.RealizableTimeVectors`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( ℕ → ( Set α ) ) ) , ( ( GenLimit.ParetoGeneration.RealizableTimeVectors F ) = { t : GenLimit.ParetoGeneration.TimeVector | ( ∃ G : ( GenLimit.ParetoGeneration.HistoryGenerator α ) , ( ( GenLimit.ParetoGeneration.AchievesTimeVector G F t ) ∧ ( GenLimit.ParetoGeneration.PositiveTimeVector t ) ) ) } )
```

### *time vector* · `GenLimit.ParetoGeneration.TimeVector`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.ParetoGeneration.TimeVector = ( ℕ → ℕ ) )
```

## P14

SHA-256 of the checked page: `b34e5b3cb27dcb08ba2d0b39b18e73e8f9b0bed5c8a7c1584ce20205535356a6`

### *error* · `GenLimit.ListIdentification.Statistical.error`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( k : ℕ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( A : ( GenLimit.ListIdentification.Statistical.Kernel α k ) ) , ∀ ( p : ( PMF α ) ) , ∀ ( K : ( GenLimit.Generic.Language α ) ) , ∀ ( n : ℕ ) , ( ( GenLimit.ListIdentification.Statistical.error F A p K n ) = ( GenLimit.DiscreteIID.probability ( PMF.bind ( GenLimit.DiscreteIID.samples p n ) A ) ( GenLimit.ListIdentification.Statistical.misses F K ) ) )
```

### *exponential* · `GenLimit.ListIdentification.Statistical.Exponential`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( k : ℕ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( A : ( GenLimit.ListIdentification.Statistical.Kernel α k ) ) , ( ( GenLimit.ListIdentification.Statistical.Exponential F A ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( p : ( PMF α ) ) , ∀ ( _ : ( ( PMF.support p ) = ( F i ) ) ) , ( ∃ c : ℝ , ( ( c > 0 ) ) ∧ ( ( ∃ D : ℝ , ( ( D > 0 ) ) ∧ ( ( ∀ n : ℕ , ( ( GenLimit.ListIdentification.Statistical.error F A p ( F i ) n ) ≤ ( D * ( Real.exp ( ( - c ) * ( ↑ n ) ) ) ) ) ) ) ) ) ) )
```

### *has angluin stratification* · `GenLimit.ListIdentification.HasAngluinStratification`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( k : ℕ ) , ( ( GenLimit.ListIdentification.HasAngluinStratification F k ) ) ↔ ( ( ∃ layers : ( List ( Set ℕ ) ) , ( ( ( List.length layers ) = k ) ) ∧ ( ( ( GenLimit.ListIdentification.CoversAllIndices layers ) ) ∧ ( ( ∀ I ∈ layers , ( GenLimit.ListIdentification.RelativeConditionTwo F I ) ) ) ) ) )
```

### *infinite draws identifies* · `GenLimit.ListIdentification.InfiniteDraws.Identifies`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ MeasurableSpace α ] , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( k : ℕ ) , ∀ ( p : ℝ ) , ( ( GenLimit.ListIdentification.InfiniteDraws.Identifies F k p ) ) ↔ ( depends_only% [ α , F , k , p ] ( ∃ D : ( GenLimit.ListIdentification.ListIdentifier α k ) , ∀ ( z : ℕ ) , ∀ ( q : ( PMF α ) ) , ∀ ( _ : ( ( PMF.support q ) = ( F z ) ) ) , ( p ≤ ( MeasureTheory.Measure.real ( GenLimit.ListIdentification.InfiniteDraws.iid ( PMF.toMeasure q ) ) ( GenLimit.ListIdentification.InfiniteDraws.success F D z ) ) ) ) )
```

### *k angluin condition* · `GenLimit.ListIdentification.KAngluinCondition`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( k : ℕ ) , ( ( GenLimit.ListIdentification.KAngluinCondition F k ) ) ↔ ( ∀ ( i : ℕ ) , ( GenLimit.ListIdentification.Psi F i k ) )
```

### *kernel* · `GenLimit.ListIdentification.Statistical.Kernel`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( k : ℕ ) , ( ( GenLimit.ListIdentification.Statistical.Kernel α k ) = ( ( List α ) → ( PMF ( ( Fin k ) → ℕ ) ) ) )
```

### *list identifiable* · `GenLimit.ListIdentification.ListIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( k : ℕ ) , ( ( GenLimit.ListIdentification.ListIdentifiable F k ) ) ↔ ( ( ∃ A : ( GenLimit.ListIdentification.ListIdentifier α k ) , ( GenLimit.ListIdentification.ListIdentifies A F ) ) )
```

### *nontrivial for* · `GenLimit.ListIdentification.Statistical.NontrivialFor`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( k : ℕ ) , ( ( GenLimit.ListIdentification.Statistical.NontrivialFor F k ) ) ↔ ( ( ∃ S : ( Finset ( GenLimit.Generic.Language α ) ) , ∃ x : α , ( ( ( Finset.card S ) = ( k + 1 ) ) ) ∧ ( ∀ K ∈ S , ( ( K ∈ ( Set.range F ) ) ∧ ( x ∈ K ) ) ) ) )
```

### *probabilistic identifies* · `GenLimit.ListIdentification.Probabilistic.Identifies`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( k : ℕ ) , ∀ ( p : ℝ ) , ( ( GenLimit.ListIdentification.Probabilistic.Identifies F k p ) ) ↔ ( depends_only% [ α , F , k , p ] ( ∃ A : ( GenLimit.ListIdentification.Probabilistic.Identifier α k ) , ∀ ( z : ℕ ) , ∀ ( s : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents s ( F z ) ) ) , ( p ≤ ( MeasureTheory.Measure.real GenLimit.ListIdentification.Probabilistic.fair ( GenLimit.ListIdentification.Probabilistic.stableEvent F A s z ) ) ) ) )
```

## P15

SHA-256 of the checked page: `7a199318dafe68da078a71448c1b4adaa7dcd7b09f9dc791c6b3cd3e4da21307`

### *co single class* · `GenLimit.KleinbergWei.PartialEnumeration.PartialTopology.coSingleClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.KleinbergWei.PartialEnumeration.PartialTopology.coSingleClass = ( Insert.insert Set.univ ( Set.range ( fun a => ( HasCompl.compl ( Singleton.singleton a ) ) ) ) ) )
```

### *compatible* · `GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) ↔ ( ∀ ( i j a b c d : ℕ ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O i ) a ) = ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O j ) c ) ) ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O i ) b ) = ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O j ) d ) ) ) , ∀ ( _ : ( a < b ) ) , ( c < d ) )
```

### *element valid* · `GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( s g : ( ℕ → ℕ ) ) , ∀ ( K : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid s g K ) ) ↔ ( depends_only% [ s , g , K ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ( ( ( g t ) ∈ K ) ) ∧ ( ( ∀ ( i : ℕ ) , ∀ ( _ : ( i ≤ t ) ) , ( ( s i ) ≠ ( g t ) ) ) ∧ ( ( ∀ ( i : ℕ ) , i < t → ( ( g i ) ≠ ( g t ) ) ) ) ) ) )
```

### *generates from partial enumeration* · `GenLimit.KleinbergWei.PartialEnumeration.GeneratesFromPartialEnumeration`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( z : ℕ ) , ( ( GenLimit.KleinbergWei.PartialEnumeration.GeneratesFromPartialEnumeration C x z ) ) ↔ ( ( GenLimit.FreshGeneratesInLimit x ( GenLimit.KleinbergWei.PartialEnumeration.freshOutput C x ) ( C z ) ) )
```

### *identifiable on full texts* · `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.IdentifiableOnFullTexts`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : ( Set GenLimit.Language ) ) , ( ( GenLimit.KleinbergWei.PartialEnumeration.FullTopology.IdentifiableOnFullTexts X ) ) ↔ ( ( GenLimit.Angluin.ExtensionallyIdentifiable X ) )
```

### *intersection of* · `GenLimit.KleinbergWei.PartialEnumeration.intersectionOf`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( I : ( Finset ℕ ) ) , ( ( GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C I ) = { u : ℕ | ( ∀ i ∈ I , ( u ∈ ( C i ) ) ) } )
```

### *language* · `GenLimit.Language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Language = ( Set ℕ ) )
```

### *lower density* · `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( A : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K A ) = ( Filter.liminf ( GenLimit.KleinbergWei.OrderedLanguage.prefixRatio K A ) Filter.atTop ) )
```

### *partial identifiable* · `GenLimit.KleinbergWei.PartialEnumeration.PartialIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : ( Set GenLimit.Language ) ) , ( ( GenLimit.KleinbergWei.PartialEnumeration.PartialIdentifiable X ) ) ↔ ( ( ∃ A : ( ( List ℕ ) → GenLimit.Language ) , ( GenLimit.KleinbergWei.PartialEnumeration.IdentifiesPartial A X ) ) )
```

### *semi index generates* · `GenLimit.KleinbergWei.PartialEnumeration.SemiIndexGenerates`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( z : ℕ ) , ( ( GenLimit.KleinbergWei.PartialEnumeration.SemiIndexGenerates C x z ) ) ↔ ( ( ( ∀ t : ℕ , ( Set.Infinite ( GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C ( GenLimit.KleinbergWei.PartialEnumeration.selectedIndices C x t ) ) ) ) ) ∧ ( depends_only% [ C , x , z ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( binrel% HasSubset.Subset ( GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C ( GenLimit.KleinbergWei.PartialEnumeration.selectedIndices C x t ) ) ( C z ) ) ) ) ) )
```

### *semi index trace generates* · `GenLimit.KleinbergWei.PartialEnumeration.SemiIndexTraceGenerates`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( indices : ( ℕ → ( Finset ℕ ) ) ) , ∀ ( z : ℕ ) , ( ( GenLimit.KleinbergWei.PartialEnumeration.SemiIndexTraceGenerates C indices z ) ) ↔ ( ( ( ∀ t : ℕ , ( Set.Infinite ( GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C ( indices t ) ) ) ) ) ∧ ( depends_only% [ C , indices , z ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( binrel% HasSubset.Subset ( GenLimit.KleinbergWei.PartialEnumeration.intersectionOf C ( indices t ) ) ( C z ) ) ) ) ) )
```

### *TD space* · `GenLimit.KleinbergWei.PartialEnumeration.FullTopology.TDSpace`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : ( Set GenLimit.Language ) ) , ( ( GenLimit.KleinbergWei.PartialEnumeration.FullTopology.TDSpace X ) ) ↔ ( ∀ ( K : ( GenLimit.KleinbergWei.PartialEnumeration.FullTopology.Point X ) ) , ( GenLimit.KleinbergWei.PartialEnumeration.FullTopology.TDPoint K ) )
```

### *upper density* · `GenLimit.KleinbergWei.OrderedLanguage.upperDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( A : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity K A ) = ( Filter.limsup ( GenLimit.KleinbergWei.OrderedLanguage.prefixRatio K A ) Filter.atTop ) )
```

## P16

SHA-256 of the checked page: `e35e197257c61bf97418e00e46c04b56055c0998a92652198873efb3636ef845`

### *CFG language* · `GenLimit.ComplexityBarriers.CFG.language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( g : GenLimit.ComplexityBarriers.CFG.Description ) , ( ( GenLimit.ComplexityBarriers.CFG.language g ) = ( ContextFreeGrammar.language ( GenLimit.ComplexityBarriers.CFG.grammar g ) ) )
```

### *description* · `GenLimit.ComplexityBarriers.CFG.Description`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.ComplexityBarriers.CFG.Description = ( ℕ × ( List ( ℕ × ( List ( ℕ ⊕ ℕ ) ) ) ) ) )
```

### *DFA at most* · `GenLimit.ComplexityBarriers.Blocks.DFAAtMost`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( s : ℕ ) , ∀ ( L : ( Set ( List Bool ) ) ) , ( ( GenLimit.ComplexityBarriers.Blocks.DFAAtMost s L ) ) ↔ ( ( ∃ q : ℕ , ( ( q ≤ s ) ) ∧ ( ( ∃ M : ( DFA Bool ( Fin q ) ) , ( ( DFA.accepts M ) = L ) ) ) ) )
```

### *LTT at most* · `GenLimit.ComplexityBarriers.LTT.LTTAtMost`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( s : ℕ ) , ∀ ( L : ( Set ( List α ) ) ) , ( ( GenLimit.ComplexityBarriers.LTT.LTTAtMost s L ) ) ↔ ( ( ∃ Ps : ( List ( GenLimit.ComplexityBarriers.LTT.Profile α ) ) , ( ( ( List.sum ( List.map GenLimit.ComplexityBarriers.LTT.Profile.size Ps ) ) ≤ s ) ∧ ( L = { w : ( List α ) | ( ∃ P ∈ Ps , ( w ∈ ( GenLimit.ComplexityBarriers.LTT.Profile.language P ) ) ) } ) ) ) )
```

### *NFA at most* · `GenLimit.ComplexityBarriers.Automata.NFAAtMost`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( s : ℕ ) , ∀ ( L : ( Set ( List α ) ) ) , ( ( GenLimit.ComplexityBarriers.Automata.NFAAtMost s L ) ) ↔ ( ( ∃ q : ℕ , ( ( q ≤ s ) ) ∧ ( ( ∃ M : ( NFA α ( Fin q ) ) , ( ( NFA.accepts M ) = L ) ) ) ) )
```

### *pattern* · `GenLimit.ComplexityBarriers.Patterns.Pattern`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.ComplexityBarriers.Patterns.Pattern = ( List ( Bool ⊕ ℕ ) ) )
```

### *patterns language* · `GenLimit.ComplexityBarriers.Patterns.language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( p : GenLimit.ComplexityBarriers.Patterns.Pattern ) , ( ( GenLimit.ComplexityBarriers.Patterns.language p ) = { w : ( List Bool ) | ( ∃ v : ( ℕ → ( List Bool ) ) , ( ( ∀ i : ℕ , ( ( v i ) ≠ [] ) ) ∧ ( ( GenLimit.ComplexityBarriers.Patterns.eval v p ) = w ) ) ) } )
```

### *profile language* · `GenLimit.ComplexityBarriers.LTT.Profile.language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( P : ( GenLimit.ComplexityBarriers.LTT.Profile α ) ) , ( ( GenLimit.ComplexityBarriers.LTT.Profile.language P ) = { w : ( List α ) | ( ( List.IsPrefix ( GenLimit.ComplexityBarriers.LTT.Profile.front P ) w ) ∧ ( ( List.IsSuffix ( GenLimit.ComplexityBarriers.LTT.Profile.back P ) w ) ∧ ( ∀ c ∈ ( GenLimit.ComplexityBarriers.LTT.Profile.rules P ) , ( GenLimit.ComplexityBarriers.LTT.Comparison.test ( GenLimit.ComplexityBarriers.LTT.Constraint.cmp c ) ( GenLimit.ComplexityBarriers.LTT.occurrences ( GenLimit.ComplexityBarriers.LTT.Constraint.word c ) w ) ( GenLimit.ComplexityBarriers.LTT.Constraint.bound c ) ) ) ) ) } )
```

### *size* · `GenLimit.ComplexityBarriers.LTT.Profile.size`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( P : ( GenLimit.ComplexityBarriers.LTT.Profile α ) ) , ( ( GenLimit.ComplexityBarriers.LTT.Profile.size P ) = ( ( ( 7 + ( List.length ( GenLimit.ComplexityBarriers.LTT.Profile.front P ) ) ) + ( List.length ( GenLimit.ComplexityBarriers.LTT.Profile.back P ) ) ) + ( List.sum ( List.map ( fun c => ( ( 5 + ( List.length ( GenLimit.ComplexityBarriers.LTT.Constraint.word c ) ) ) + ( GenLimit.ComplexityBarriers.LTT.Constraint.bound c ) ) ) ( GenLimit.ComplexityBarriers.LTT.Profile.rules P ) ) ) ) )
```

## P17

SHA-256 of the checked page: `4b8314f37780148afa31b75f5cb34503ad471975799f700ad704625821c56c94`

### *algorithm five generator* · `GenLimit.InfiniteContamination.algorithmFiveGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( family : ( ℕ → ( Set ℕ ) ) ) , ∀ ( t : ℕ ) , ∀ ( history : ( ( Fin t ) → ℕ ) ) , ( ( GenLimit.InfiniteContamination.algorithmFiveGenerator family t history ) = ( ( GenLimit.InfiniteContamination.finiteCommonCore ( GenLimit.InfiniteContamination.indexedLanguages family ( GenLimit.InfiniteContamination.algorithmFiveIndices family ( GenLimit.InfiniteContamination.algorithmFivePrefixCompletion history ) t ) ) ) \ ( GenLimit.Generic.sequenceSample history ) ) )
```

### *algorithm nine set generator* · `GenLimit.InfiniteContamination.algorithmNineSetGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( family : ( ℕ → ( Set ℕ ) ) ) , ∀ ( orders : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( ε M : ℝ ) , ∀ ( x : ℕ ) , ∀ ( xs : ( ( Fin x ) → ℕ ) ) , ( ( GenLimit.InfiniteContamination.algorithmNineSetGenerator family orders ε M x xs ) = ( ( GenLimit.InfiniteContamination.algorithmNineRawCore family orders ε M xs ) \ ( GenLimit.Generic.sequenceSample xs ) ) )
```

### *bounded displacement* · `GenLimit.InfiniteContamination.BoundedDisplacement`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( x : ( GenLimit.Generic.Stream ℕ ) ) , ∀ ( L : ( Set ℕ ) ) , ∀ ( M : ℝ ) , ( ( GenLimit.InfiniteContamination.BoundedDisplacement K x L M ) ) ↔ ( depends_only% [ K , x , L , M ] ( ∃ N : ℕ , ( ∀ ( n : ℕ ) , N ≤ n → ( ( ↑ ( GenLimit.InfiniteContamination.canonicalRank K L ( x n ) ) ) ≤ ( M * ( ( ↑ n ) + 1 ) ) ) ) ) )
```

### *canonical family orders* · `GenLimit.InfiniteContamination.canonicalFamilyOrders`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( i : ℕ ) , ( ( GenLimit.InfiniteContamination.canonicalFamilyOrders O i ) = ( GenLimit.KleinbergWei.OrderedLanguage.canonical ( O.language i ) ( GenLimit.OracleFamily.infinite' O i ) ) )
```

### *constant noise* · `GenLimit.InfiniteContamination.ConstantNoise`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ∀ ( c : ℝ ) , ( ( GenLimit.InfiniteContamination.ConstantNoise x L c ) ) ↔ ( depends_only% [ α , x , L , c ] ( ∃ N : ℕ , ( ∀ ( n : ℕ ) , N ≤ n → ( ( GenLimit.InfiniteContamination.empiricalNoiseRate x L n ) ≤ c ) ) ) )
```

### *constant noise arbitrary omission enumeration* · `GenLimit.InfiniteContamination.ConstantNoiseArbitraryOmissionEnumeration`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ∀ ( c : ℝ ) , ( ( GenLimit.InfiniteContamination.ConstantNoiseArbitraryOmissionEnumeration x L c ) ) ↔ ( ( ( Function.Injective x ) ∧ ( ( GenLimit.InfiniteContamination.ArbitraryOmissions x L ) ∧ ( GenLimit.InfiniteContamination.ConstantNoise x L c ) ) ) )
```

### *constant noise dense set condition* · `GenLimit.InfiniteContamination.ConstantNoiseDenseSetCondition`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( family : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( orders : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( c ρ : ℝ ) , ( ( GenLimit.InfiniteContamination.ConstantNoiseDenseSetCondition family orders c ρ ) ) ↔ ( ∀ ( S : ( Finset ℕ ) ) , ∀ ( _ : ( Finset.Nonempty S ) ) , ∀ ( x : ( GenLimit.Generic.Stream ℕ ) ) , ∀ ( _ : ( ∀ i ∈ S , ( GenLimit.InfiniteContamination.ConstantNoiseArbitraryOmissionEnumeration x ( family i ) c ) ) ) , ∀ i ∈ S , ( ρ ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( orders i ) ( GenLimit.InfiniteContamination.finiteCommonCore ( GenLimit.InfiniteContamination.indexedLanguages family S ) ) ) ) )
```

### *constant noise enumeration* · `GenLimit.InfiniteContamination.ConstantNoiseEnumeration`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ∀ ( c : ℝ ) , ( ( GenLimit.InfiniteContamination.ConstantNoiseEnumeration x L c ) ) ↔ ( ( ( Function.Injective x ) ∧ ( ( GenLimit.InfiniteContamination.NoOmissions x L ) ∧ ( GenLimit.InfiniteContamination.ConstantNoise x L c ) ) ) )
```

### *constant noise generation property* · `GenLimit.InfiniteContamination.ConstantNoiseGenerationProperty`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( c : ℝ ) , ( ( GenLimit.InfiniteContamination.ConstantNoiseGenerationProperty C c ) ) ↔ ( ∀ ( S : ( Finset ( GenLimit.Generic.Language α ) ) ) , ∀ ( _ : ( Finset.Nonempty S ) ) , ∀ ( _ : ( binrel% HasSubset.Subset S C ) ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( ∀ L ∈ S , ( GenLimit.InfiniteContamination.ConstantNoiseArbitraryOmissionEnumeration x L c ) ) ) , ( Set.Infinite ( GenLimit.InfiniteContamination.finiteCommonCore S ) ) )
```

### *element based lower density* · `GenLimit.InfiniteContamination.elementBasedLowerDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( gen : ( GenLimit.Generic.Generator ℕ ) ) , ∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( x : ( GenLimit.Generic.Stream ℕ ) ) , ( ( GenLimit.InfiniteContamination.elementBasedLowerDensity gen K x ) = ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K ( GenLimit.InfiniteContamination.elementOutputLanguage gen x ) ) )
```

### *element based upper density* · `GenLimit.InfiniteContamination.elementBasedUpperDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( gen : ( GenLimit.Generic.Generator ℕ ) ) , ∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( x : ( GenLimit.Generic.Stream ℕ ) ) , ( ( GenLimit.InfiniteContamination.elementBasedUpperDensity gen K x ) = ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity K ( GenLimit.InfiniteContamination.elementOutputLanguage gen x ) ) )
```

### *finite noise* · `GenLimit.InfiniteContamination.FiniteNoise`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( stream : ( GenLimit.Generic.Stream α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ( ( GenLimit.InfiniteContamination.FiniteNoise stream L ) ) ↔ ( ( GenLimit.Generic.FinitelyManyViolations stream ( fun x => ( x ∈ L ) ) ) )
```

### *finite noise finite omission enumeration* · `GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ( ( GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration x L ) ) ↔ ( ( ( Function.Injective x ) ∧ ( ( GenLimit.InfiniteContamination.FiniteNoise x L ) ∧ ( GenLimit.InfiniteContamination.FiniteOmissions x L ) ) ) )
```

### *generates element in limit on* · `GenLimit.InfiniteContamination.GeneratesElementInLimitOn`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.Generic.Generator α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ( ( GenLimit.InfiniteContamination.GeneratesElementInLimitOn gen L x ) ) ↔ ( depends_only% [ α , gen , L , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.InfiniteContamination.FreshElementCorrectAt gen L x t ) ) ) )
```

### *generates set in limit on* · `GenLimit.InfiniteContamination.GeneratesSetInLimitOn`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.InfiniteContamination.SetGenerator α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ( ( GenLimit.InfiniteContamination.GeneratesSetInLimitOn gen L x ) ) ↔ ( depends_only% [ α , gen , L , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.InfiniteContamination.SetCorrectAt gen L x t ) ) ) )
```

### *generation oracle* · `GenLimit.HallucinationModeCollapse.generationOracle`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( code : ℕ ) , ( ( GenLimit.HallucinationModeCollapse.generationOracle O code ) = ( ite ( Eq ( GenLimit.OracleFamily.query O ( Prod.fst ( Nat.unpair code ) ) ( Prod.snd ( Nat.unpair code ) ) ) Bool.true ) 1 0 ) )
```

### *generator* · `GenLimit.Generic.Generator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.Generator α ) = ( GenLimit.Generic.FiniteHistoryOperator α α ) )
```

### *guarantees set based upper density under omissions on* · `GenLimit.InfiniteContamination.GuaranteesSetBasedUpperDensityUnderOmissionsOn`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ι : Sort _ ) , ∀ ( gen : ( GenLimit.InfiniteContamination.SetGenerator ℕ ) ) , ∀ ( family : ( ι → GenLimit.Language ) ) , ∀ ( orders : ( ι → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( c ρ : ℝ ) , ( ( GenLimit.InfiniteContamination.GuaranteesSetBasedUpperDensityUnderOmissionsOn gen family orders c ρ ) ) ↔ ( ∀ ( z : ι ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( _ : ( Function.Injective x ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.NoNoise x ( family z ) ) ) , ∀ ( _ : ( GenLimit.InfiniteContamination.OmissionsAtMost x ( orders z ) c ) ) , ( ( GenLimit.InfiniteContamination.GeneratesSetInLimitOn gen ( family z ) x ) ∧ ( ρ ≤ ( GenLimit.InfiniteContamination.setBasedUpperDensity gen ( orders z ) x ) ) ) )
```

### *is infinite set generator* · `GenLimit.InfiniteContamination.IsInfiniteSetGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.InfiniteContamination.SetGenerator α ) ) , ( ( GenLimit.InfiniteContamination.IsInfiniteSetGenerator gen ) ) ↔ ( ( GenLimit.Generic.IsInfiniteSetGenerator gen ) )
```

### *lower density* · `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( A : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K A ) = ( Filter.liminf ( GenLimit.KleinbergWei.OrderedLanguage.prefixRatio K A ) Filter.atTop ) )
```

### *replay generator* · `GenLimit.InfiniteContamination.replayGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( run : ( ( List ℕ ) → ℕ ) ) , ∀ ( x : ℕ ) , ∀ ( xs : ( ( Fin x ) → ℕ ) ) , ( ( GenLimit.InfiniteContamination.replayGenerator run x xs ) = ( GenLimit.InfiniteContamination.membershipReplay run ( List.ofFn xs ) ) )
```

### *set based lower density* · `GenLimit.InfiniteContamination.setBasedLowerDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( gen : ( GenLimit.InfiniteContamination.SetGenerator ℕ ) ) , ∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( x : ( GenLimit.Generic.Stream ℕ ) ) , ( ( GenLimit.InfiniteContamination.setBasedLowerDensity gen K x ) = ( Filter.liminf ( fun t => ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K ( GenLimit.InfiniteContamination.setOutput gen x t ) ) ) Filter.atTop ) )
```

### *set based upper density* · `GenLimit.InfiniteContamination.setBasedUpperDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( gen : ( GenLimit.InfiniteContamination.SetGenerator ℕ ) ) , ∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( x : ( GenLimit.Generic.Stream ℕ ) ) , ( ( GenLimit.InfiniteContamination.setBasedUpperDensity gen K x ) = ( Filter.limsup ( fun t => ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K ( GenLimit.InfiniteContamination.setOutput gen x t ) ) ) Filter.atTop ) )
```

### *set generator* · `GenLimit.InfiniteContamination.SetGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.InfiniteContamination.SetGenerator α ) = ( GenLimit.Generic.SetGenerator α ) )
```

### *set output* · `GenLimit.InfiniteContamination.setOutput`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.InfiniteContamination.SetGenerator α ) ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.InfiniteContamination.setOutput gen x t ) = ( gen t ( fun i => ( x ( Fin.val i ) ) ) ) )
```

### *terminates* · `GenLimit.Support.OracleSearchProgram.Terminates`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( P : GenLimit.Support.OracleSearchProgram ) , ∀ ( oracle : ( ℕ → ℕ ) ) , ( ( GenLimit.Support.OracleSearchProgram.Terminates P oracle ) ) ↔ ( ∀ ( xs : ( List ℕ ) ) , ( ∃ q : ℕ , ∃ y : ℕ , ( ( GenLimit.Support.OracleSearchProgram.stage P oracle xs q ) = ( Option.some y ) ) ) )
```

### *text prefix* · `GenLimit.textPrefix`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( ℕ → α ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.textPrefix x t ) = ( List.map x ( List.range t ) ) )
```

### *theorem six four family* · `GenLimit.InfiniteContamination.theoremSixFourFamily`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( p : ℝ ) , ∀ ( b : Bool ) , ( ( GenLimit.InfiniteContamination.theoremSixFourFamily p b ) = ( ite ( Eq b Bool.true ) Set.univ ( GenLimit.InfiniteContamination.floorIncrementLanguage p ) ) )
```

### *vanishing noise* · `GenLimit.InfiniteContamination.VanishingNoise`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ( ( GenLimit.InfiniteContamination.VanishingNoise x L ) ) ↔ ( ( Filter.Tendsto ( GenLimit.InfiniteContamination.empiricalNoiseRate x L ) Filter.atTop ( nhds 0 ) ) )
```

### *vanishing noise arbitrary omission enumeration* · `GenLimit.InfiniteContamination.VanishingNoiseArbitraryOmissionEnumeration`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ( ( GenLimit.InfiniteContamination.VanishingNoiseArbitraryOmissionEnumeration x L ) ) ↔ ( ( ( Function.Injective x ) ∧ ( ( GenLimit.InfiniteContamination.ArbitraryOmissions x L ) ∧ ( GenLimit.InfiniteContamination.VanishingNoise x L ) ) ) )
```

### *vanishing noise dense set condition* · `GenLimit.InfiniteContamination.VanishingNoiseDenseSetCondition`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( family : ( ℕ → ( GenLimit.Generic.Language ℕ ) ) ) , ∀ ( orders : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ∀ ( ρ : ℝ ) , ( ( GenLimit.InfiniteContamination.VanishingNoiseDenseSetCondition family orders ρ ) ) ↔ ( ∀ ( S : ( Finset ℕ ) ) , let F := ( GenLimit.InfiniteContamination.finiteCommonCore ( GenLimit.InfiniteContamination.indexedLanguages family S ) ) ; ∀ ( _ : ( Finset.Nonempty S ) ) , ∀ ( _ : ( Set.Infinite F ) ) , ∀ i ∈ S , ( ρ ≤ ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity ( orders i ) F ) ) )
```

### *vanishing noise enumeration* · `GenLimit.InfiniteContamination.VanishingNoiseEnumeration`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ( ( GenLimit.InfiniteContamination.VanishingNoiseEnumeration x L ) ) ↔ ( ( ( Function.Injective x ) ∧ ( ( GenLimit.InfiniteContamination.NoOmissions x L ) ∧ ( GenLimit.InfiniteContamination.VanishingNoise x L ) ) ) )
```

## P18

SHA-256 of the checked page: `c6faccb6e48182a670e2f7e57a6e506fd633c5522e0bb65887a61a79b891ec26`

### *coded diff empty* · `GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.CodedDiffEmpty`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( pair : GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.LanguagePairCode ) , ( ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.CodedDiffEmpty pair ) ) ↔ ( ( ( ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.codedLanguage ( Prod.fst pair ) ) \ ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.codedLanguage ( Prod.snd pair ) ) ) = EmptyCollection.emptyCollection ) )
```

### *eventually bottom* · `GenLimit.SafeGeneration.EventuallyBottom`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.SafeGeneration.SafeGenerator α ) ) , ∀ ( x : ( GenLimit.Generic.Stream ( GenLimit.SafeGeneration.Tagged α ) ) ) , ( ( GenLimit.SafeGeneration.EventuallyBottom G x ) ) ↔ ( depends_only% [ α , G , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( ( GenLimit.SafeGeneration.safeOutput G x t ) = Option.none ) ) ) )
```

### *first bounded halt* · `GenLimit.SafeGeneration.DiffEmpty.PrintedReduction.FirstBoundedHalt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( c : Nat.Partrec.Code ) , ∀ ( n : ℕ ) , ( ( GenLimit.SafeGeneration.DiffEmpty.PrintedReduction.FirstBoundedHalt c n ) ) ↔ ( ( ( ( GenLimit.SafeGeneration.DiffEmpty.boundedHalts c n ) = Bool.true ) ) ∧ ( ( ∀ ( k : ℕ ) , k < n → ( ( GenLimit.SafeGeneration.DiffEmpty.boundedHalts c k ) ≠ Bool.true ) ) ) )
```

### *is valid language pair* · `GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.IsValidLanguagePair`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( pair : GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.LanguagePairCode ) , ( ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.IsValidLanguagePair pair ) ) ↔ ( ( ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.TotalBooleanDecider ( Prod.fst pair ) ) ∧ ( ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.TotalBooleanDecider ( Prod.snd pair ) ) ∧ ( ( Set.Infinite ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.codedLanguage ( Prod.fst pair ) ) ) ∧ ( Set.Infinite ( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.codedLanguage ( Prod.snd pair ) ) ) ) ) ) )
```

### *labeled presents* · `GenLimit.SafeGeneration.LabeledPresents`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( GenLimit.Generic.Stream ( GenLimit.SafeGeneration.Tagged α ) ) ) , ∀ ( target harmful : ( GenLimit.Generic.Language α ) ) , ( ( GenLimit.SafeGeneration.LabeledPresents x target harmful ) ) ↔ ( ( ( ( GenLimit.SafeGeneration.taggedRange x Bool.true ) = target ) ∧ ( ( GenLimit.SafeGeneration.taggedRange x Bool.false ) = harmful ) ) )
```

### *language pair code* · `GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.LanguagePairCode`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.SafeGeneration.DiffEmpty.MachineEncoding.LanguagePairCode = ( Nat.Partrec.Code × Nat.Partrec.Code ) )
```

### *oracle safe algorithm* · `GenLimit.SafeGeneration.OracleSafeAlgorithm`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.SafeGeneration.OracleSafeAlgorithm α ) = ( ( GenLimit.SafeGeneration.SetDifferenceOracle α ) → ( GenLimit.SafeGeneration.SafeGenerator α ) ) )
```

### *safe generator* · `GenLimit.SafeGeneration.SafeGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.SafeGeneration.SafeGenerator α ) = ( GenLimit.Generic.FiniteHistoryOperator ( GenLimit.SafeGeneration.Tagged α ) ( Option α ) ) )
```

### *safe identifier* · `GenLimit.SafeGeneration.SafeIdentification.SafeIdentifier`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.SafeGeneration.SafeIdentification.SafeIdentifier α ) = ( GenLimit.Generic.FiniteHistoryOperator ( GenLimit.SafeGeneration.Tagged α ) ℕ ) )
```

### *safely generates* · `GenLimit.SafeGeneration.SafelyGenerates`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.SafeGeneration.SafeGenerator α ) ) , ∀ ( target harmful : ( GenLimit.Generic.Language α ) ) , ∀ ( x : ( GenLimit.Generic.Stream ( GenLimit.SafeGeneration.Tagged α ) ) ) , ( ( GenLimit.SafeGeneration.SafelyGenerates G target harmful x ) ) ↔ ( ( ∀ ( _ : ( Set.Infinite ( target \ harmful ) ) ) , depends_only% [ α , G , target , harmful , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.SafeGeneration.SafeCorrectAt G target harmful x t ) ) ) ) ∧ ( ∀ ( _ : ( Set.Finite ( target \ harmful ) ) ) , depends_only% [ α , G , target , harmful , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.SafeGeneration.BottomCorrectAt G target harmful x t ) ) ) ) )
```

### *safely generates families* · `GenLimit.SafeGeneration.SafelyGeneratesFamilies`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.SafeGeneration.SafeGenerator α ) ) , ∀ ( targets harmfuls : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.SafeGeneration.SafelyGeneratesFamilies G targets harmfuls ) ) ↔ ( ∀ ( i j : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream ( GenLimit.SafeGeneration.Tagged α ) ) ) , ∀ ( _ : ( GenLimit.SafeGeneration.LabeledPresents x ( targets i ) ( harmfuls j ) ) ) , ( GenLimit.SafeGeneration.SafelyGenerates G ( targets i ) ( harmfuls j ) x ) )
```

### *safely generates infinite differences* · `GenLimit.SafeGeneration.SafelyGeneratesInfiniteDifferences`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.SafeGeneration.SafeGenerator α ) ) , ∀ ( targets harmfuls : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.SafeGeneration.SafelyGeneratesInfiniteDifferences G targets harmfuls ) ) ↔ ( ∀ ( i j : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream ( GenLimit.SafeGeneration.Tagged α ) ) ) , ∀ ( _ : ( GenLimit.SafeGeneration.LabeledPresents x ( targets i ) ( harmfuls j ) ) ) , depends_only% [ α , G , targets , harmfuls , i , j , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.SafeGeneration.SafeCorrectAt G ( targets i ) ( harmfuls j ) x t ) ) ) )
```

### *safely identifies from* · `GenLimit.SafeGeneration.SafeIdentification.SafelyIdentifiesFrom`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( M : ( GenLimit.SafeGeneration.SafeIdentification.SafeIdentifier α ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( target harmful : ( GenLimit.Generic.Language α ) ) , ∀ ( x : ( GenLimit.Generic.Stream ( GenLimit.SafeGeneration.Tagged α ) ) ) , ( ( GenLimit.SafeGeneration.SafeIdentification.SafelyIdentifiesFrom M C target harmful x ) ) ↔ ( depends_only% [ α , M , C , target , harmful , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( ( C ( GenLimit.SafeGeneration.SafeIdentification.identifierOutput M x t ) ) = ( target \ harmful ) ) ) ) )
```

### *semantically identifies* · `GenLimit.Angluin.SemanticallyIdentifies`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( M : ( GenLimit.Angluin.SemanticIdentifier α ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.Angluin.SemanticallyIdentifies M C ) ) ↔ ( ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( C z ) ) ) , ( GenLimit.IdentifiesInLimit C M x ( C z ) ) )
```

### *set difference oracle* · `GenLimit.SafeGeneration.SetDifferenceOracle`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.SafeGeneration.SetDifferenceOracle α ) = ( ( Set α ) → ( ( Set α ) → Bool ) ) )
```

### *vertical pad* · `GenLimit.SafeGeneration.verticalPad`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ( ( GenLimit.SafeGeneration.verticalPad L ) = { p : ( α × ℕ ) | ( ( ( Prod.fst p ) ∈ L ) ∧ ( 0 < ( Prod.snd p ) ) ) } )
```

## P19

SHA-256 of the checked page: `0279990e89166ca7e37456e73ca579e8a72baed70219243d55c47486826abfe9`

### *finite noisy closure dimension at* · `GenLimit.QuantifyingNoise.FiniteNoisyClosureDimensionAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( i : ℕ ) , ( ( GenLimit.QuantifyingNoise.FiniteNoisyClosureDimensionAt C i ) ) ↔ ( depends_only% [ α , C , i ] ( ∃ D : ℕ , ∀ ( d : ℕ ) , ∀ ( _ : ( D < d ) ) , ( ¬ ( GenLimit.QuantifyingNoise.NoisyClosureWitnessAt C i d ) ) ) )
```

### *has finite dimension exhaustion at* · `GenLimit.QuantifyingNoise.HasFiniteDimensionExhaustionAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( i : ℕ ) , ( ( GenLimit.QuantifyingNoise.HasFiniteDimensionExhaustionAt C i ) ) ↔ ( ( ∃ layers : ( ℕ → ( GenLimit.Generic.LanguageClass α ) ) , ( ( Monotone layers ) ) ∧ ( ( ( C = ( Set.iUnion ( fun j => ( layers j ) ) ) ) ) ∧ ( ( ∀ j : ℕ , ( GenLimit.QuantifyingNoise.FiniteNoisyClosureDimensionAt ( layers j ) i ) ) ) ) ) )
```

### *nonuniform generatable at noise level* · `GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( i : ℕ ) , ( ( GenLimit.QuantifyingNoise.NonuniformGeneratableAtNoiseLevel C i ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.QuantifyingNoise.IsNonuniformGeneratorAtNoiseLevel gen C i ) ) )
```

### *nonuniform noise dependent generatable* · `GenLimit.QuantifyingNoise.NonuniformNoiseDependentGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.QuantifyingNoise.NonuniformNoiseDependentGeneratable C ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.QuantifyingNoise.IsNonuniformNoiseDependentGenerator gen C ) ) )
```

### *uniform generatable at noise level* · `GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( i : ℕ ) , ( ( GenLimit.QuantifyingNoise.UniformGeneratableAtNoiseLevel C i ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.QuantifyingNoise.IsUniformGeneratorAtNoiseLevel gen C i ) ) )
```

### *uniform noise dependent generatable* · `GenLimit.QuantifyingNoise.UniformNoiseDependentGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.QuantifyingNoise.UniformNoiseDependentGeneratable C ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.QuantifyingNoise.IsUniformNoiseDependentGenerator gen C ) ) )
```

## P20

SHA-256 of the checked page: `72ef85a2517761ba8dcef750e5f05b3cabec34903185c2da53fd0d5f8ace6486`

### *deterministic* · `GenLimit.AgnosticLanguage.deterministic`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α β : Type _ ) , ∀ ( A : ( ( List α ) → β ) ) , ∀ ( xs : ( List α ) ) , ( ( GenLimit.AgnosticLanguage.deterministic A xs ) = ( PMF.pure ( A xs ) ) )
```

### *finite witness index* · `GenLimit.AgnosticLanguage.FiniteWitnessIndex`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( u : ( ℕ ≃ α ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( p : ( PMF α ) ) , ( ( GenLimit.AgnosticLanguage.FiniteWitnessIndex u C p ) ) ↔ ( depends_only% [ α , u , C , p ] ( ∃ M : ℕ , ∀ ( i : ℕ ) , ∀ ( _ : ( ∀ ( r : ℕ ) , r < M → ( ( GenLimit.AgnosticLanguage.orderedWord u ( C i ) r ) ∈ ( PMF.support p ) ) ) ) , ( binrel% HasSubset.Subset ( C i ) ( PMF.support p ) ) ) )
```

### *gen err* · `GenLimit.AgnosticLanguage.genErr`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( A : ( GenLimit.AgnosticLanguage.StatisticalGenerator α ) ) , ∀ ( p : ( PMF α ) ) , ∀ ( n : ℕ ) , ( ( GenLimit.AgnosticLanguage.genErr A p n ) = ( GenLimit.DiscreteIID.probability ( PMF.bind ( GenLimit.DiscreteIID.samples p n ) ( fun xs => ( PMF.map ( Prod.mk xs ) ( A xs ) ) ) ) { z : ( ( List α ) × α ) | ( ( ( Prod.snd z ) ∉ ( PMF.support p ) ) ∨ ( ( Prod.snd z ) ∈ ( Prod.fst z ) ) ) } ) )
```

### *has supported tell tale* · `GenLimit.AgnosticLanguage.HasSupportedTellTale`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( p : ( PMF α ) ) , ( ( GenLimit.AgnosticLanguage.HasSupportedTellTale C p ) ) ↔ ( ( ∃ j : ℕ , ( ( GenLimit.AgnosticLanguage.Optimal C p j ) ) ∧ ( ( ∃ T : ( Finset α ) , ( ( GenLimit.Generic.IsFiniteTellTale ( Set.range C ) ( C j ) T ) ∧ ( binrel% HasSubset.Subset T ( PMF.support p ) ) ) ) ) ) )
```

### *id err* · `GenLimit.AgnosticLanguage.idErr`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( A : ( GenLimit.AgnosticLanguage.Identifier α ) ) , ∀ ( p : ( PMF α ) ) , ∀ ( n : ℕ ) , ( ( GenLimit.AgnosticLanguage.idErr C A p n ) = ( tsum ( fun j => ( ( ENNReal.toReal ( DFunLike.coe ( PMF.bind ( GenLimit.DiscreteIID.samples p n ) A ) j ) ) * ( ( GenLimit.AgnosticLanguage.risk p ( C j ) ) - ( GenLimit.AgnosticLanguage.optimalRisk C p ) ) ) ) ( SummationFilter.unconditional Nat ) ) )
```

### *id p* · `GenLimit.AgnosticLanguage.idP`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( A : ( GenLimit.AgnosticLanguage.Identifier α ) ) , ∀ ( p : ( PMF α ) ) , ∀ ( n : ℕ ) , ( ( GenLimit.AgnosticLanguage.idP C A p n ) = ( GenLimit.DiscreteIID.probability ( PMF.bind ( GenLimit.DiscreteIID.samples p n ) A ) { j : ℕ | ( ¬ ( GenLimit.AgnosticLanguage.MinimalOptimal C p j ) ) } ) )
```

### *is finite tell tale* · `GenLimit.Generic.IsFiniteTellTale`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ∀ ( T : ( Finset α ) ) , ( ( GenLimit.Generic.IsFiniteTellTale H L T ) ) ↔ ( ( ( binrel% HasSubset.Subset T L ) ) ∧ ( ∀ K ∈ H , ∀ ( _ : ( binrel% HasSubset.Subset T K ) ) , ∀ ( _ : ( binrel% HasSubset.Subset K L ) ) , ( K = L ) ) )
```

### *minimal optimal* · `GenLimit.AgnosticLanguage.MinimalOptimal`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( p : ( PMF α ) ) , ∀ ( j : ℕ ) , ( ( GenLimit.AgnosticLanguage.MinimalOptimal C p j ) ) ↔ ( ( ( GenLimit.AgnosticLanguage.Optimal C p j ) ) ∧ ( ∀ ( k : ℕ ) , ∀ ( _ : ( GenLimit.AgnosticLanguage.Optimal C p k ) ) , ( ¬ ( HasSSubset.SSubset ( C k ) ( C j ) ) ) ) )
```

### *optimal* · `GenLimit.AgnosticLanguage.Optimal`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( p : ( PMF α ) ) , ∀ ( j : ℕ ) , ( ( GenLimit.AgnosticLanguage.Optimal C p j ) ) ↔ ( ( ( GenLimit.AgnosticLanguage.risk p ( C j ) ) = ( GenLimit.AgnosticLanguage.optimalRisk C p ) ) )
```

### *probability* · `GenLimit.DiscreteIID.probability`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( p : ( PMF α ) ) , ∀ ( E : ( Set α ) ) , ( ( GenLimit.DiscreteIID.probability p E ) = ( ENNReal.toReal ( DFunLike.coe ( PMF.toOuterMeasure p ) E ) ) )
```

## P21

SHA-256 of the checked page: `052723e8d0e3079fd1532888dbaab577f027c5e8bfc8d721a8f4c41ab4a3fd4f`

### *closed neighborhood* · `GenLimit.MetricSpaces.closedNeighborhood`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( ρ : ( GenLimit.MetricSpaces.Distance α ) ) , ∀ ( A : ( Set α ) ) , ∀ ( r : ℝ ) , ( ( GenLimit.MetricSpaces.closedNeighborhood ρ A r ) = { y : α | ( GenLimit.MetricSpaces.InClosedNeighborhood ρ A r y ) } )
```

### *covering number at least* · `GenLimit.MetricSpaces.CoveringNumberAtLeast`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( ρ : ( GenLimit.MetricSpaces.Distance α ) ) , ∀ ( r : ℝ ) , ∀ ( A : ( Set α ) ) , ∀ ( d : ℕ ) , ( ( GenLimit.MetricSpaces.CoveringNumberAtLeast ρ r A d ) ) ↔ ( ∀ ( centers : ( Finset α ) ) , ∀ ( _ : ( binrel% HasSubset.Subset A ( GenLimit.MetricSpaces.closedNeighborhood ρ ( Finset.toSet centers ) r ) ) ) , ( d ≤ Finset.card centers ) )
```

### *discrete distance* · `GenLimit.MetricSpaces.discreteDistance`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ DecidableEq α ] , ∀ ( x_1 y : α ) , ( ( GenLimit.MetricSpaces.discreteDistance x_1 y ) = ( ite ( Eq x_1 y ) 0 1 ) )
```

### *example 48 language class* · `GenLimit.MetricSpaces.HilbertAxisReservoir.example48LanguageClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( r ε ε' : ℝ ) , ( ( GenLimit.MetricSpaces.HilbertAxisReservoir.example48LanguageClass r ε ε' ) = { L : ( GenLimit.Generic.Language ( ↥ GenLimit.MetricSpaces.HilbertAxisReservoir.Hilbert2 ) ) | ( ∃ I₁ : ( Set ℕ ) , ( ∃ I₂ : ( Set ℕ ) , ( ∃ I₃ : ( Set ℕ ) , ( ( Set.Infinite I₁ ) ∧ ( ( Set.Infinite I₂ ) ∧ ( ( Set.Infinite I₃ ) ∧ ( ( ∀ k ∈ I₁ , ( 0 < k ) ) ∧ ( ( ∀ k ∈ I₂ , ( 0 < k ) ) ∧ ( ( ∀ k ∈ I₃ , ( 0 < k ) ) ∧ ( L = ( GenLimit.MetricSpaces.HilbertAxisReservoir.example48Language r ε ε' I₁ I₂ I₃ ) ) ) ) ) ) ) ) ) ) ) } )
```

### *generatable in limit* · `GenLimit.LiRamanTewari.GeneratableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.GeneratableInLimit H ) ) ↔ ( ( GenLimit.Generic.GeneratableInLimit H ) )
```

### *generatable in limit at* · `GenLimit.MetricSpaces.GeneratableInLimitAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( ρ : ( GenLimit.MetricSpaces.Distance α ) ) , ∀ ( ε ε' : ℝ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.MetricSpaces.GeneratableInLimitAt ρ ε ε' H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.MetricSpaces.IsLimitGeneratorAt ρ ε ε' gen H ) ) )
```

### *generator* · `GenLimit.Generic.Generator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.Generator α ) = ( GenLimit.Generic.FiniteHistoryOperator α α ) )
```

### *generic language class* · `GenLimit.Generic.LanguageClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.LanguageClass α ) = ( Set ( GenLimit.Generic.Language α ) ) )
```

### *has finite scale closure dimension* · `GenLimit.MetricSpaces.HasFiniteScaleClosureDimension`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( ρ : ( GenLimit.MetricSpaces.Distance α ) ) , ∀ ( ε ε' : ℝ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.MetricSpaces.HasFiniteScaleClosureDimension ρ ε ε' H ) ) ↔ ( depends_only% [ α , ρ , ε , ε' , H ] ( ∃ D : ℕ , ∀ ( d : ℕ ) , ∀ ( _ : ( D < d ) ) , ( ¬ ( ∃ S : ( Finset α ) , ( GenLimit.MetricSpaces.IsScaleClosureWitness ρ ε ε' H S d ) ) ) ) )
```

### *is limit generator at* · `GenLimit.MetricSpaces.IsLimitGeneratorAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( ρ : ( GenLimit.MetricSpaces.Distance α ) ) , ∀ ( ε ε' : ℝ ) , ∀ ( gen : ( GenLimit.Generic.Generator α ) ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.MetricSpaces.IsLimitGeneratorAt ρ ε ε' gen H ) ) ↔ ( ∀ L ∈ H , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.MetricSpaces.MetricPresentation ρ ε x L ) ) , depends_only% [ α , ρ , ε , ε' , gen , H , L , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.MetricSpaces.MetricCorrectAt ρ ε' gen L x t ) ) ) )
```

### *is nondecreasing cover* · `GenLimit.Generic.IsNondecreasingCover`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( classes : ( ℕ → ( GenLimit.Generic.LanguageClass α ) ) ) , ( ( GenLimit.Generic.IsNondecreasingCover H classes ) ) ↔ ( ( ( Monotone classes ) ∧ ( H = ( Set.iUnion ( fun n => ( classes n ) ) ) ) ) )
```

### *is nonuniform generator at* · `GenLimit.MetricSpaces.IsNonuniformGeneratorAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( ρ : ( GenLimit.MetricSpaces.Distance α ) ) , ∀ ( ε ε' : ℝ ) , ∀ ( gen : ( GenLimit.Generic.Generator α ) ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.MetricSpaces.IsNonuniformGeneratorAt ρ ε ε' gen H ) ) ↔ ( ∀ L ∈ H , depends_only% [ α , ρ , ε , ε' , gen , H , L ] ( ∃ d : ℕ , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.StreamIn x L ) ) , ∀ ( t : ℕ ) , ∀ ( _ : ( GenLimit.MetricSpaces.CoveringNumberAtLeast ρ ε ( Finset.toSet ( IRStatement.FirstTerms.firstTerms x t ) ) d ) ) , ( ∀ ( s : ℕ ) , t ≤ s → ( GenLimit.MetricSpaces.MetricCorrectAt ρ ε' gen L x s ) ) ) )
```

### *nonuniformly generatable* · `GenLimit.LiRamanTewari.NonuniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.NonuniformlyGeneratable H ) ) ↔ ( ( GenLimit.Generic.NonuniformlyGeneratable H ) )
```

### *nonuniformly generatable at* · `GenLimit.MetricSpaces.NonuniformlyGeneratableAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( ρ : ( GenLimit.MetricSpaces.Distance α ) ) , ∀ ( ε ε' : ℝ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.MetricSpaces.NonuniformlyGeneratableAt ρ ε ε' H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.MetricSpaces.IsNonuniformGeneratorAt ρ ε ε' gen H ) ) )
```

### *output* · `GenLimit.Generic.output`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.Generic.Generator α ) ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.Generic.output G x t ) = ( G t ( fun i => ( x ( Fin.val i ) ) ) ) )
```

### *real distance* · `GenLimit.MetricSpaces.RealLineThreshold.realDistance`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( x y : ℝ ) , ( ( GenLimit.MetricSpaces.RealLineThreshold.realDistance x y ) = ( abs ( x - y ) ) )
```

### *real line threshold language class* · `GenLimit.MetricSpaces.RealLineThreshold.languageClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.MetricSpaces.RealLineThreshold.languageClass = { L : ( GenLimit.Generic.Language ℝ ) | ( ∃ p : ℕ , ( ( Nat.Prime p ) ∧ ( ( Odd p ) ∧ ( ∃ B : ( Set ℝ ) , ( ( binrel% HasSubset.Subset B GenLimit.MetricSpaces.RealLineThreshold.positiveEvenIntegers ) ∧ ( L = ( ( GenLimit.MetricSpaces.RealLineThreshold.primePairSupport p ) ∪ B ) ) ) ) ) ) ) } )
```

### *stream in* · `GenLimit.Generic.StreamIn`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ( ( GenLimit.Generic.StreamIn x L ) ) ↔ ( ( Set.range x ⊆ L ) )
```

### *uniformly generatable* · `GenLimit.LiRamanTewari.UniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.LiRamanTewari.UniformlyGeneratable H ) ) ↔ ( ( GenLimit.Generic.UniformlyGeneratable H ) )
```

### *uniformly generatable at* · `GenLimit.MetricSpaces.UniformlyGeneratableAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( ρ : ( GenLimit.MetricSpaces.Distance α ) ) , ∀ ( ε ε' : ℝ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.MetricSpaces.UniformlyGeneratableAt ρ ε ε' H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ∃ d : ℕ , ( GenLimit.MetricSpaces.IsUniformGeneratorAt ρ ε ε' gen H d ) ) )
```

### *uniformly unbounded support at* · `GenLimit.MetricSpaces.UniformlyUnboundedSupportAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( ρ : ( GenLimit.MetricSpaces.Distance α ) ) , ∀ ( r : ℝ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.MetricSpaces.UniformlyUnboundedSupportAt ρ r H ) ) ↔ ( ∀ L ∈ H , ( ( Set.Nonempty L ) ) ∧ ( ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.MetricSpaces.MetricPresentation ρ r x L ) ) , ∀ ( d : ℕ ) , ( ∃ t : ℕ , ( GenLimit.MetricSpaces.CoveringNumberAtLeast ρ r ( Finset.toSet ( IRStatement.FirstTerms.firstTerms x t ) ) d ) ) ) )
```

## P22

SHA-256 of the checked page: `c6cf12f6ee4b1f21f6f5a001327d7354848560ecaeab6cfd0628ea2fcba7d592`

### *carried witness protection generator* · `GenLimit.Replay.CountableDomainOracleFamily.carriedWitnessProtectionGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Replay.CountableDomainOracleFamily α ) ) , ∀ ( e : ( α ≃ ℕ ) ) , ( ( GenLimit.Replay.CountableDomainOracleFamily.carriedWitnessProtectionGenerator F e ) = ( GenLimit.Replay.CountableDomainOracleFamily.pullGenerator e ( GenLimit.OracleFamily.carriedWitnessProtectionGenerator ( GenLimit.Replay.CountableDomainOracleFamily.encode F e ) ) ) )
```

### *generatable in limit* · `GenLimit.Generic.GeneratableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.GeneratableInLimit H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.Generic.IsLimitGenerator gen H ) ) )
```

### *generatable in limit with replay* · `GenLimit.Replay.GeneratableInLimitWithReplay`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Replay.GeneratableInLimitWithReplay H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.Replay.IsLimitReplayGenerator gen H ) ) )
```

### *generator* · `GenLimit.Generic.Generator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.Generator α ) = ( GenLimit.Generic.FiniteHistoryOperator α α ) )
```

### *is limit replay generator* · `GenLimit.Replay.IsLimitReplayGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.Generic.Generator α ) ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Replay.IsLimitReplayGenerator gen H ) ) ↔ ( ∀ L ∈ H , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Replay.IsReplayEnumeration gen L x ) ) , depends_only% [ α , gen , H , L , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.Generic.CorrectAt gen L x t ) ) ) )
```

### *is recursive UUS family* · `GenLimit.Replay.IsRecursiveUUSFamily`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( family : GenLimit.LanguageFamily ) , ( ( GenLimit.Replay.IsRecursiveUUSFamily family ) ) ↔ ( ( ∃ oracle : ( GenLimit.MembershipOracle family ) , ( ( Computable₂ ( GenLimit.MembershipOracle.query oracle ) ) ) ∧ ( ( ∀ i : ℕ , ( Set.Infinite ( family i ) ) ) ) ) )
```

### *is uniform generator at* · `GenLimit.Generic.IsUniformGeneratorAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.Generic.Generator α ) ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( d : ℕ ) , ( ( GenLimit.Generic.IsUniformGeneratorAt gen H d ) ) ↔ ( ∀ L ∈ H , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.StreamIn x L ) ) , ∀ ( t : ℕ ) , ∀ ( _ : ( ( Finset.card ( IRStatement.FirstTerms.firstTerms x t ) ) = d ) ) , ( ∀ ( s : ℕ ) , t ≤ s → ( GenLimit.Generic.CorrectAt gen L x s ) ) )
```

### *is uniform replay generator at* · `GenLimit.Replay.IsUniformReplayGeneratorAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( gen : ( GenLimit.Generic.Generator α ) ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ∀ ( d : ℕ ) , ( ( GenLimit.Replay.IsUniformReplayGeneratorAt gen H d ) ) ↔ ( ∀ L ∈ H , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Replay.IsReplaySequence gen L x ) ) , ∀ ( t : ℕ ) , ∀ ( _ : ( 0 < t ) ) , ∀ ( _ : ( ( Finset.card ( IRStatement.FirstTerms.firstTerms x t ) ) = d ) ) , ( ∀ ( s : ℕ ) , t ≤ s → ( GenLimit.Generic.CorrectAt gen L x s ) ) )
```

### *language class* · `GenLimit.Generic.LanguageClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.LanguageClass α ) = ( Set ( GenLimit.Generic.Language α ) ) )
```

### *language family* · `GenLimit.LanguageFamily`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.LanguageFamily = ( ℕ → GenLimit.Language ) )
```

### *nonuniform hard class* · `GenLimit.Replay.nonuniformHardClass`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Replay.nonuniformHardClass = ( ( Singleton.singleton GenLimit.Replay.upperLanguage ) ∪ ( Set.range GenLimit.Replay.cutoffLanguage ) ) )
```

### *nonuniformly generatable* · `GenLimit.Generic.NonuniformlyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.NonuniformlyGeneratable H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.Generic.IsNonuniformGenerator gen H ) ) )
```

### *nonuniformly generatable with replay* · `GenLimit.Replay.NonuniformlyGeneratableWithReplay`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Replay.NonuniformlyGeneratableWithReplay H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.Replay.IsNonuniformReplayGenerator gen H ) ) )
```

### *proper membership algorithm* · `GenLimit.Replay.ProperMembershipAlgorithm`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Replay.ProperMembershipAlgorithm = ( GenLimit.Support.AdaptiveMembershipDialogue.Algorithm ℕ GenLimit.Replay.ProperMembershipQuery ℕ ) )
```

### *properly generatable in limit with replay* · `GenLimit.Replay.ProperlyGeneratableInLimitWithReplay`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ι α : Type _ ) , ∀ ( family : ( ι → ( GenLimit.Generic.Language α ) ) ) , ( ( GenLimit.Replay.ProperlyGeneratableInLimitWithReplay family ) ) ↔ ( ( ∃ gen : ( GenLimit.Replay.ProperGenerator ι α ) , ( GenLimit.Replay.IsProperLimitReplayGenerator family gen ) ) )
```

### *properly generates in limit using membership* · `GenLimit.Replay.ProperlyGeneratesInLimitUsingMembership`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A : GenLimit.Replay.ProperMembershipAlgorithm ) , ∀ ( family : GenLimit.LanguageFamily ) , ( ( GenLimit.Replay.ProperlyGeneratesInLimitUsingMembership A family ) ) ↔ ( ∀ ( target : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream ℕ ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( family target ) ) ) , ( ∀ ( t : ℕ ) , ( ∃ i : ℕ , ( GenLimit.Replay.ProperMembershipExecutionOutputsAt A family x t i ) ) ) ∧ ( depends_only% [ A , family , target , x ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : T ≤ t ) , ∀ ( i : ℕ ) , ∀ ( _ : ( GenLimit.Replay.ProperMembershipExecutionOutputsAt A family x t i ) ) , ( binrel% HasSubset.Subset ( family i ) ( family target ) ) ) ) )
```

### *UUS* · `GenLimit.Generic.UUS`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.UUS H ) ) ↔ ( ∀ L ∈ H , ( Set.Infinite L ) )
```

## P23

SHA-256 of the checked page: `0c6ba256eaf8430df1c83b65b9efad8af115e78885cfacafc3327c0d44c93488`

### *admissible box* · `GenLimit.KleinbergWei.Banach.admissibleBox`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ∀ ( f : ( ℕ → ℝ ) ) , ∀ ( P : ( Set ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( n : ℕ ) , ∀ ( r : ( ( GenLimit.KleinbergWei.Banach.Lattice d ) × ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ( ( GenLimit.KleinbergWei.Banach.admissibleBox f P n r ) ) ↔ ( let V := ( GenLimit.KleinbergWei.Banach.geometricVolume ( Prod.fst r ) ( Prod.snd r ) ) ; ( ( ∀ j : ( Fin d ) , ( ( Prod.fst r j ) < ( Prod.snd r j ) ) ) ) ∧ ( ( ( 2 ≤ V ) ) ∧ ( ( ( 0 < ( f V ) ) ) ∧ ( ( ( ↑ n ) ≤ ( ( ↑ ( Finset.card ( GenLimit.KleinbergWei.Banach.Rectangles.box P ( Prod.fst r ) ( Prod.snd r ) ) ) ) / ( ( f V ) * ( Real.log ( ↑ V ) ) ) ) ) ) ) ) )
```

### *cube play* · `GenLimit.KleinbergWei.Banach.cubePlay`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ∀ ( A : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice d ) ) → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.KleinbergWei.Banach.cubePlay A s t ) = ( A ( GenLimit.textPrefix s ( t + 1 ) ) ) )
```

### *cube valid* · `GenLimit.KleinbergWei.Banach.cubeValid`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ∀ ( A : ( ( List ( GenLimit.KleinbergWei.Banach.Lattice d ) ) → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( s : ( ℕ → ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ∀ ( K : ( Set ( GenLimit.KleinbergWei.Banach.Lattice d ) ) ) , ( ( GenLimit.KleinbergWei.Banach.cubeValid A s K ) ) ↔ ( depends_only% [ d , A , s , K ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , let M := ( GenLimit.KleinbergWei.Banach.cubePlay A s t ) ; ∀ ( _ : ( t ≥ T ) ) , ( ( M ∈ K ) ) ∧ ( ( ∀ ( i : ℕ ) , ∀ ( _ : ( i ≤ t ) ) , ( ( s i ) ≠ M ) ) ∧ ( ( ∀ ( i : ℕ ) , i < t → ( ( GenLimit.KleinbergWei.Banach.cubePlay A s i ) ≠ M ) ) ) ) ) )
```

### *element valid* · `GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( s g : ( ℕ → ℕ ) ) , ∀ ( K : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.ElementValid s g K ) ) ↔ ( depends_only% [ s , g , K ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ( ( ( g t ) ∈ K ) ) ∧ ( ( ∀ ( i : ℕ ) , ∀ ( _ : ( i ≤ t ) ) , ( ( s i ) ≠ ( g t ) ) ) ∧ ( ( ∀ ( i : ℕ ) , i < t → ( ( g i ) ≠ ( g t ) ) ) ) ) ) )
```

### *finite rank at most* · `GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : ( Set GenLimit.Language ) ) , ∀ ( r : ℕ ) , ( ( GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost X r ) ) ↔ ( ( ( GenLimit.KleinbergWei.TowerTopology.cbDerivative X r ) = EmptyCollection.emptyCollection ) )
```

### *geometric volume* · `GenLimit.KleinbergWei.Banach.geometricVolume`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ∀ ( l u : ( GenLimit.KleinbergWei.Banach.Lattice d ) ) , ( ( GenLimit.KleinbergWei.Banach.geometricVolume l u ) = ( Finset.prod Finset.univ ( fun i => ( Int.toNat ( ( u i ) - ( l i ) ) ) ) ) )
```

### *is cube* · `GenLimit.KleinbergWei.Banach.MovingCubes.IsCube`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ∀ ( R : ( GenLimit.KleinbergWei.Banach.MovingCubes.Box d ) ) , ( ( GenLimit.KleinbergWei.Banach.MovingCubes.IsCube R ) ) ↔ ( ( ∃ z : ( GenLimit.KleinbergWei.Banach.Lattice d ) , ∃ k : ℕ , ( ( 0 < k ) ) ∧ ( ( ( ∀ i : ( Fin d ) , ( ( Prod.fst R i ) = ( ( z i ) - ( ↑ k ) ) ) ) ) ∧ ( ( ∀ i : ( Fin d ) , ( ( Prod.snd R i ) = ( ( z i ) + ( ↑ k ) ) ) ) ) ) ) )
```

### *lattice* · `GenLimit.KleinbergWei.Banach.Lattice`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ( ( GenLimit.KleinbergWei.Banach.Lattice d ) = ( ( Fin d ) → ℤ ) )
```

### *lower banach density* · `GenLimit.KleinbergWei.Banach.lowerBanachDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.Banach.lowerBanachDensity A ) = ( Filter.liminf ( GenLimit.KleinbergWei.Banach.banachMinimum A ) Filter.atTop ) )
```

### *lower window density* · `GenLimit.KleinbergWei.Banach.lowerWindowDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( f : ( ℕ → ( WithTop ℕ ) ) ) , ∀ ( A : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.Banach.lowerWindowDensity f A ) = ( Filter.liminf ( GenLimit.KleinbergWei.Banach.windowMinimum f A ) Filter.atTop ) )
```

### *play* · `GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A : ( ( List ℕ ) → ℕ ) ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.play A s t ) = ( A ( GenLimit.textPrefix s ( t + 1 ) ) ) )
```

### *sign* · `GenLimit.KleinbergWei.Banach.RandomSigns.sign`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( b : Bool ) , ( ( GenLimit.KleinbergWei.Banach.RandomSigns.sign b ) = ( ite ( Eq b Bool.true ) 1 ( - 1 ) ) )
```

### *span* · `GenLimit.KleinbergWei.Banach.TierGeometry.span`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( d : ℕ ) , ∀ ( l u : ( GenLimit.KleinbergWei.Banach.Lattice d ) ) , ( ( GenLimit.KleinbergWei.Banach.TierGeometry.span l u ) = ( ( Finset.sup Finset.univ ( fun i => ( Int.toNat ( ( u i ) - ( l i ) ) ) ) ) + 1 ) )
```

### *text prefix* · `GenLimit.textPrefix`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( ℕ → α ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.textPrefix x t ) = ( List.map x ( List.range t ) ) )
```

### *valid on* · `GenLimit.KleinbergWei.Banach.Adversary.ValidOn`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( A : ( ( List ℕ ) → ( Finset ℕ ) ) ) , ∀ ( C : ( Set ( Set ℕ ) ) ) , ( ( GenLimit.KleinbergWei.Banach.Adversary.ValidOn A C ) ) ↔ ( ∀ K ∈ C , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( _ : ( Set.range s = K ) ) , ∀ ( _ : ( Function.Injective s ) ) , depends_only% [ A , C , K , s ] ( ∃ T : ℕ , ∀ ( t : ℕ ) , ∀ ( _ : ( t ≥ T ) ) , ∀ x ∈ ( A ( GenLimit.textPrefix s t ) ) , ( ( x ∈ K ) ∧ ( x ∉ ( GenLimit.textPrefix s t ) ) ) ) )
```

## P24

SHA-256 of the checked page: `2795fbff5e849fcd1d51e558f2148452cc332f52eb1c93709543a7f268007fd9`

### *gaussian generator* · `GenLimit.PriceOfPrivacy.Generation.gaussianGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : Type _ ) , ∀ ( u : ( ℕ ≃ X ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily X ) ) , ∀ ( f : ℕ ) , ∀ [ NeZero f ] , ∀ ( n : ℕ ) , ∀ ( s : ( ( List X ) → ( ( Fin f ) → ℝ ) ) ) , ∀ ( ε δ : ℝ ) , ( ( GenLimit.PriceOfPrivacy.Generation.gaussianGenerator u C n s ε δ ) = ( GenLimit.PriceOfPrivacy.Generation.release u C n ( GenLimit.PriceOfPrivacy.Selection.gaussianLaw s 1 ε δ ) ) )
```

### *gen err* · `GenLimit.AgnosticLanguage.genErr`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( A : ( GenLimit.AgnosticLanguage.StatisticalGenerator α ) ) , ∀ ( p : ( PMF α ) ) , ∀ ( n : ℕ ) , ( ( GenLimit.AgnosticLanguage.genErr A p n ) = ( GenLimit.DiscreteIID.probability ( PMF.bind ( GenLimit.DiscreteIID.samples p n ) ( fun xs => ( PMF.map ( Prod.mk xs ) ( A xs ) ) ) ) { z : ( ( List α ) × α ) | ( ( ( Prod.snd z ) ∉ ( PMF.support p ) ) ∨ ( ( Prod.snd z ) ∈ ( Prod.fst z ) ) ) } ) )
```

### *generation assumptions* · `GenLimit.PriceOfPrivacy.GenerationAssumptions`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : Type _ ) , ∀ ( u : ( ℕ ≃ X ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily X ) ) , ∀ ( p : ( PMF X ) ) , ( ( GenLimit.PriceOfPrivacy.GenerationAssumptions u C p ) ) ↔ ( ( ( ∃ W : ℕ , ( GenLimit.PriceOfPrivacy.WitnessBy u C p W ) ) ) ∧ ( ( ∃ i : ℕ , ( binrel% HasSubset.Subset ( C i ) ( PMF.support p ) ) ) ) )
```

### *id err* · `GenLimit.AgnosticLanguage.idErr`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( A : ( GenLimit.AgnosticLanguage.Identifier α ) ) , ∀ ( p : ( PMF α ) ) , ∀ ( n : ℕ ) , ( ( GenLimit.AgnosticLanguage.idErr C A p n ) = ( tsum ( fun j => ( ( ENNReal.toReal ( DFunLike.coe ( PMF.bind ( GenLimit.DiscreteIID.samples p n ) A ) j ) ) * ( ( GenLimit.AgnosticLanguage.risk p ( C j ) ) - ( GenLimit.AgnosticLanguage.optimalRisk C p ) ) ) ) ( SummationFilter.unconditional Nat ) ) )
```

### *identifier* · `GenLimit.AgnosticLanguage.Identifier`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.AgnosticLanguage.Identifier α ) = ( GenLimit.Learner α ( PMF ℕ ) ) )
```

### *intersecting infinite difference pair* · `GenLimit.PriceOfPrivacy.IntersectingInfiniteDifferencePair`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily X ) ) , ( ( GenLimit.PriceOfPrivacy.IntersectingInfiniteDifferencePair C ) ) ↔ ( ( ∃ i : ℕ , ∃ j : ℕ , ( ( Set.Nonempty ( ( C i ) ∩ ( C j ) ) ) ∧ ( ( Set.Infinite ( ( C i ) \ ( C j ) ) ) ∧ ( Set.Infinite ( ( C j ) \ ( C i ) ) ) ) ) ) )
```

### *intersecting private pair* · `GenLimit.PriceOfPrivacy.IntersectingPrivatePair`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily X ) ) , ( ( GenLimit.PriceOfPrivacy.IntersectingPrivatePair C ) ) ↔ ( ( ∃ i : ℕ , ∃ j : ℕ , ( ( ( C i ) ≠ ( C j ) ) ) ∧ ( ( ∃ a : X , ( ( a ∈ ( ( C i ) ∩ ( C j ) ) ) ) ∧ ( ( ∃ x : X , ( ( x ∈ ( C i ) ) ) ∧ ( ( ∃ y : X , ( ( y ∈ ( C j ) ) ) ∧ ( ( ∀ ( k : ℕ ) , ∀ ( _ : ( x ∈ ( C k ) ) ) , ( ( C k ) = ( C i ) ) ) ∧ ( ∀ ( k : ℕ ) , ∀ ( _ : ( y ∈ ( C k ) ) ) , ( ( C k ) = ( C j ) ) ) ) ) ) ) ) ) ) ) )
```

### *is private* · `GenLimit.PriceOfPrivacy.IsPrivate`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X Y : Type _ ) , ∀ ( ε : ENNReal ) , ∀ ( A : ( ( List X ) → ( PMF Y ) ) ) , ( ( GenLimit.PriceOfPrivacy.IsPrivate ε A ) ) ↔ ( ∀ ( _ : ( ε ≠ Top.top ) ) , ∀ ( pre : ( List X ) ) , ∀ ( x y : X ) , ∀ ( post : ( List X ) ) , ∀ ( F : ( Set Y ) ) , ( ( DFunLike.coe ( PMF.toOuterMeasure ( A ( HAppend.hAppend pre ( List.cons x post ) ) ) ) F ) ≤ ( ( ENNReal.ofReal ( Real.exp ( ENNReal.toReal ε ) ) ) * ( DFunLike.coe ( PMF.toOuterMeasure ( A ( HAppend.hAppend pre ( List.cons y post ) ) ) ) F ) ) ) )
```

### *language output* · `GenLimit.PriceOfPrivacy.languageOutput`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily X ) ) , ∀ ( A : ( GenLimit.AgnosticLanguage.Identifier X ) ) , ∀ ( xs : ( List X ) ) , ( ( GenLimit.PriceOfPrivacy.languageOutput C A xs ) = ( PMF.map C ( A xs ) ) )
```

### *mass floor* · `GenLimit.PriceOfPrivacy.Generation.massFloor`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : Type _ ) , ∀ ( u : ( ℕ ≃ X ) ) , ∀ ( L : ( Set X ) ) , ∀ ( p : ( PMF X ) ) , ∀ ( W : ℕ ) , ( ( GenLimit.PriceOfPrivacy.Generation.massFloor u L p W ) = ( GenLimit.PriceOfPrivacy.FiniteMinimum.lower 1 ( GenLimit.PriceOfPrivacy.Generation.prefixIndices u L W ) ( fun j => ( ENNReal.toReal ( DFunLike.coe p ( DFunLike.coe u j ) ) ) ) ) )
```

### *optimal risk* · `GenLimit.AgnosticLanguage.optimalRisk`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily α ) ) , ∀ ( p : ( PMF α ) ) , ( ( GenLimit.AgnosticLanguage.optimalRisk C p ) = ( iInf ( fun j => ( GenLimit.AgnosticLanguage.risk p ( C j ) ) ) ) )
```

### *private at* · `GenLimit.PriceOfPrivacy.PrivateAt`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X Y : Type _ ) , ∀ ( ε δ : ℝ ) , ∀ ( n : ℕ ) , ∀ ( A : ( ( List X ) → ( PMF Y ) ) ) , ( ( GenLimit.PriceOfPrivacy.PrivateAt ε δ n A ) ) ↔ ( ∀ ( pre : ( List X ) ) , ∀ ( x y : X ) , ∀ ( post : ( List X ) ) , ∀ ( _ : ( ( ( ( List.length pre ) + ( List.length post ) ) + 1 ) = n ) ) , ∀ ( F : ( Set Y ) ) , ( ( GenLimit.DiscreteIID.probability ( A ( HAppend.hAppend pre ( List.cons x post ) ) ) F ) ≤ ( ( ( Real.exp ε ) * ( GenLimit.DiscreteIID.probability ( A ( HAppend.hAppend pre ( List.cons y post ) ) ) F ) ) + δ ) ) )
```

### *public scores* · `GenLimit.PriceOfPrivacy.Generation.publicScores`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : Type _ ) , ∀ ( u : ( ℕ ≃ X ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily X ) ) , ∀ ( f W : ℕ ) , ∀ ( xs : ( List X ) ) , ∀ ( i : ( Fin f ) ) , ( ( GenLimit.PriceOfPrivacy.Generation.publicScores u C f W xs i ) = ( GenLimit.PriceOfPrivacy.Generation.prefixCount u ( C ( Fin.val i ) ) xs W ) )
```

### *pure generator* · `GenLimit.PriceOfPrivacy.Generation.pureGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : Type _ ) , ∀ ( u : ( ℕ ≃ X ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily X ) ) , ∀ ( f : ℕ ) , ∀ [ NeZero f ] , ∀ ( n : ℕ ) , ∀ ( s : ( ( List X ) → ( ( Fin f ) → ℝ ) ) ) , ∀ ( ε : ℝ ) , ( ( GenLimit.PriceOfPrivacy.Generation.pureGenerator u C n s ε ) = ( GenLimit.PriceOfPrivacy.Generation.release u C n ( GenLimit.PriceOfPrivacy.Selection.pureLaw s 1 ε ) ) )
```

### *retention* · `GenLimit.PriceOfPrivacy.retention`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ε : ENNReal ) , ( ( GenLimit.PriceOfPrivacy.retention ε ) = ( ite ( Eq ε Top.top ) 0 ( Real.exp ( - ( ENNReal.toReal ε ) ) ) ) )
```

### *risk* · `GenLimit.AgnosticLanguage.risk`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( p : ( PMF α ) ) , ∀ ( L : ( GenLimit.Generic.Language α ) ) , ( ( GenLimit.AgnosticLanguage.risk p L ) = ( GenLimit.DiscreteIID.probability p ( HasCompl.compl L ) ) )
```

### *unknown scores* · `GenLimit.PriceOfPrivacy.Generation.unknownScores`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : Type _ ) , ∀ ( u : ( ℕ ≃ X ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily X ) ) , ∀ ( f : ℕ ) , ∀ ( g : ℝ ) , ∀ ( xs : ( List X ) ) , ∀ ( i : ( Fin f ) ) , ( ( GenLimit.PriceOfPrivacy.Generation.unknownScores u C f g xs i ) = ( GenLimit.PriceOfPrivacy.Generation.depthScore u ( C ( Fin.val i ) ) xs g ) )
```

### *witness by* · `GenLimit.PriceOfPrivacy.WitnessBy`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( X : Type _ ) , ∀ ( u : ( ℕ ≃ X ) ) , ∀ ( C : ( GenLimit.Generic.LanguageFamily X ) ) , ∀ ( p : ( PMF X ) ) , ∀ ( W : ℕ ) , ( ( GenLimit.PriceOfPrivacy.WitnessBy u C p W ) ) ↔ ( ∀ ( i : ℕ ) , ∀ ( _ : ( ¬ ( binrel% HasSubset.Subset ( C i ) ( PMF.support p ) ) ) ) , ( ∃ ( t : ℕ ) , t < W ∧ ( ( DFunLike.coe u t ) ∈ ( ( C i ) \ ( PMF.support p ) ) ) ) )
```

## P25

SHA-256 of the checked page: `724dfc1ecec937aab842c00f5d64f1f7a044c266ed5aa6fad5d8faf93ae64b6c`

### *differentially private* · `GenLimit.Privacy.DifferentiallyPrivate`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ι X Y : Type _ ) , ∀ [ MeasurableSpace Y ] , ∀ ( ε : ℝ ) , ∀ ( δ : ENNReal ) , ∀ ( law : ( ( ι → X ) → ( MeasureTheory.Measure Y ) ) ) , ( ( GenLimit.Privacy.DifferentiallyPrivate ε δ law ) ) ↔ ( ∀ ( u v : ( ι → X ) ) , ∀ ( _ : ( GenLimit.Privacy.Neighbors u v ) ) , ∀ ( E : ( Set Y ) ) , ∀ ( _ : ( MeasurableSet E ) ) , ( ( DFunLike.coe ( law u ) E ) ≤ ( ( ( ENNReal.ofReal ( Real.exp ε ) ) * ( DFunLike.coe ( law v ) E ) ) + δ ) ) )
```

### *fails after* · `GenLimit.PrivateLimit.Epoch.failsAfter`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( K : ( Set ℕ ) ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.PrivateLimit.Epoch.failsAfter K s t ) = ( Set.iUnion ( fun n => ( Set.preimage ( Function.eval ( t + n ) ) ( GenLimit.PrivateLimit.Epoch.badWord K s ( ( t + n ) + 1 ) ) ) ) ) )
```

### *generator* · `GenLimit.Generic.Generator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.Generator α ) = ( GenLimit.Generic.FiniteHistoryOperator α α ) )
```

### *language* · `GenLimit.Language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Language = ( Set ℕ ) )
```

## P26

SHA-256 of the checked page: `67a204c6e7ba5a221405545260e4768876f098f9f77b2a6f153d0a9dc75a019a`

### *accepts trace* · `GenLimit.ComputationalTrace.Recognizer.AcceptsTrace`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ι : Type _ ) , ∀ ( M : GenLimit.ComputationalTrace.Recognizer ) , ∀ ( code : ( ι ↪ ℕ ) ) , ∀ ( x : ( List ι ) ) , ∀ ( tr : GenLimit.ComputationalTrace.Trace ) , ( ( GenLimit.ComputationalTrace.Recognizer.AcceptsTrace M code x tr ) ) ↔ ( ( ( ( GenLimit.ComputationalTrace.Trace.first tr ) = ( GenLimit.ComputationalTrace.Config.mk ( GenLimit.ComputationalTrace.Recognizer.initial M ) 0 ( GenLimit.ComputationalTrace.inputTape code x ) ) ) ∧ ( ( GenLimit.ComputationalTrace.LegalMoves ( GenLimit.ComputationalTrace.Trace.first tr ) ( GenLimit.ComputationalTrace.Trace.rest tr ) ) ∧ ( binrel% HasSubset.Subset ( GenLimit.ComputationalTrace.Trace.facts tr ) ( GenLimit.ComputationalTrace.Recognizer.table M ) ) ) ) )
```

### *action* · `GenLimit.ComputationalTrace.TM.Action`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.ComputationalTrace.TM.Action = ( GenLimit.ComputationalTrace.TM.Motion × ( GenLimit.ComputationalTrace.TM.Motion × ( Option Bool ) ) ) )
```

### *all rates* · `GenLimit.ComputationalTrace.AllRates`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( cut : ( ℝ → ℕ ) ) , ∀ ( n : ℕ ) , ∀ ( xs ys : ( List α ) ) , ( ( GenLimit.ComputationalTrace.AllRates cut n xs ys ) ) ↔ ( ∀ ( r : ℝ ) , ∀ ( _ : ( 0 < r ) ) , ∀ ( _ : ( r < 1 ) ) , ( GenLimit.ComputationalTrace.RateBound r ( cut r ) n xs ys ) )
```

### *binary DFA language* · `GenLimit.ComputationalTrace.BinaryDFA.language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( σ : Type ) , ∀ ( M : ( GenLimit.ComputationalTrace.BinaryDFA σ ) ) , ( ( GenLimit.ComputationalTrace.BinaryDFA.language M ) = { w : ( List Bool ) | ( ( GenLimit.ComputationalTrace.BinaryDFA.final M ( GenLimit.ComputationalTrace.BinaryDFA.run M ( GenLimit.ComputationalTrace.BinaryDFA.initial M ) w ) ) = Bool.true ) } )
```

### *control language* · `GenLimit.ComputationalTrace.Control.language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( μ O A σ : Type ) , ∀ ( D : ( GenLimit.ComputationalTrace.Control.Device μ O A ) ) , ∀ ( M : ( GenLimit.ComputationalTrace.Control.Machine σ O A ) ) , ( ( GenLimit.ComputationalTrace.Control.language D M ) = { w : ( List Bool ) | ( ∃ ds : ( List ( GenLimit.ComputationalTrace.Control.Frame σ μ ) ) , ( GenLimit.ComputationalTrace.Control.Finish D M ( ( GenLimit.ComputationalTrace.Control.Machine.initial M ) , ( GenLimit.ComputationalTrace.Control.Device.load D w ) ) ds ) ) } )
```

### *control learner* · `GenLimit.ComputationalTrace.Control.learner`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( μ O A : Type ) , ∀ [ Fintype O ] , ∀ [ DecidableEq O ] , ∀ [ Fintype A ] , ∀ ( D : ( GenLimit.ComputationalTrace.Control.Device μ O A ) ) , ∀ ( C cutoff : ℕ ) , ( ( GenLimit.ComputationalTrace.Control.learner D C cutoff ) = ( GenLimit.ComputationalTrace.Control.scopedLearner D ( fun e => ( ( List.length ( Prod.snd e ) ) + C ) ) ( fun S => ( cutoff , ( GenLimit.ComputationalTrace.Control.poolSize D ( Finset.card S ) C ) ) ) ) )
```

### *deterministic* · `GenLimit.ComputationalTrace.Recognizer.Deterministic`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( M : GenLimit.ComputationalTrace.Recognizer ) , ( ( GenLimit.ComputationalTrace.Recognizer.Deterministic M ) ) ↔ ( ∀ ( r s : GenLimit.ComputationalTrace.Instruction ) , ∀ ( _ : ( ( GenLimit.ComputationalTrace.Fact.rule r ) ∈ ( GenLimit.ComputationalTrace.Recognizer.table M ) ) ) , ∀ ( _ : ( ( GenLimit.ComputationalTrace.Fact.rule s ) ∈ ( GenLimit.ComputationalTrace.Recognizer.table M ) ) ) , ∀ ( _ : ( ( GenLimit.ComputationalTrace.Instruction.source r ) = ( GenLimit.ComputationalTrace.Instruction.source s ) ) ) , ∀ ( _ : ( ( GenLimit.ComputationalTrace.Instruction.read r ) = ( GenLimit.ComputationalTrace.Instruction.read s ) ) ) , ( r = s ) )
```

### *finite bound* · `GenLimit.ComputationalTrace.FiniteBound`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( budget cutoff inputLength : ℕ ) , ∀ ( xs ys : ( List α ) ) , ( ( GenLimit.ComputationalTrace.FiniteBound budget cutoff inputLength xs ys ) ) ↔ ( ∀ ( _ : ( cutoff ≤ inputLength ) ) , ( ∃ k : ℕ , ( ( k ≤ budget ) ∧ ( GenLimit.ComputationalTrace.EditScript k xs ys ) ) ) )
```

### *guess language* · `GenLimit.ComputationalTrace.Control.Guess.language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( μ O A : Type ) , ∀ ( H : ( GenLimit.ComputationalTrace.Control.Guess O A ) ) , ∀ ( D : ( GenLimit.ComputationalTrace.Control.Device μ O A ) ) , ( ( GenLimit.ComputationalTrace.Control.Guess.language H D ) = { w : ( List Bool ) | ( ∃ n : ℕ , ( ( GenLimit.ComputationalTrace.Control.Guess.test H D w n ) = Bool.true ) ) } )
```

### *identifies in limit* · `GenLimit.IdentifiesInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Info Name Object : Type _ ) , ∀ ( denote : ( Name → Object ) ) , ∀ ( learner : ( GenLimit.Learner Info Name ) ) , ∀ ( x : ( ℕ → Info ) ) , ∀ ( target : Object ) , ( ( GenLimit.IdentifiesInLimit denote learner x target ) ) ↔ ( ( ∃ name : Name , ( ( ( denote name ) = target ) ∧ ( GenLimit.StabilizesTo ( fun t => ( learner ( GenLimit.textPrefix x t ) ) ) name ) ) ) )
```

### *observation* · `GenLimit.ComputationalTrace.TM.Observation`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.ComputationalTrace.TM.Observation = ( ( Option Bool ) × Bool ) )
```

### *PDA device* · `GenLimit.ComputationalTrace.PDA.device`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.ComputationalTrace.PDA.device = ( GenLimit.ComputationalTrace.Control.Device.mk ( fun w => ( GenLimit.ComputationalTrace.PDA.Memory.mk w [ Bool.false ] ) ) ( fun m => ( ( List.head? ( GenLimit.ComputationalTrace.PDA.Memory.input m ) ) , ( List.head? ( GenLimit.ComputationalTrace.PDA.Memory.stack m ) ) ) ) ( fun m => ( fun a => ( GenLimit.ComputationalTrace.PDA.Memory.mk ( ite ( Eq ( Prod.fst a ) Bool.true ) ( List.tail ( GenLimit.ComputationalTrace.PDA.Memory.input m ) ) ( GenLimit.ComputationalTrace.PDA.Memory.input m ) ) ( GenLimit.ComputationalTrace.PDA.Op.apply ( Prod.snd a ) ( GenLimit.ComputationalTrace.PDA.Memory.stack m ) ) ) ) ) ( fun m => ( Bool.and ( List.isEmpty ( GenLimit.ComputationalTrace.PDA.Memory.input m ) ) ( List.isEmpty ( GenLimit.ComputationalTrace.PDA.Memory.stack m ) ) ) ) ) )
```

### *rate bound* · `GenLimit.ComputationalTrace.RateBound`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( rate : ℝ ) , ∀ ( cutoff inputLength : ℕ ) , ∀ ( xs ys : ( List α ) ) , ( ( GenLimit.ComputationalTrace.RateBound rate cutoff inputLength xs ys ) ) ↔ ( ∀ ( _ : ( cutoff ≤ inputLength ) ) , ( ∃ k : ℕ , ( ( GenLimit.ComputationalTrace.EditScript k xs ys ) ∧ ( ( ↑ k ) ≤ ( rate * ( ↑ ( List.length xs ) ) ) ) ) ) )
```

### *recognizer language* · `GenLimit.ComputationalTrace.Recognizer.language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ι : Type _ ) , ∀ ( M : GenLimit.ComputationalTrace.Recognizer ) , ∀ ( code : ( ι ↪ ℕ ) ) , ( ( GenLimit.ComputationalTrace.Recognizer.language M code ) = { x : ( List ι ) | ( ∃ tr : GenLimit.ComputationalTrace.Trace , ( GenLimit.ComputationalTrace.Recognizer.AcceptsTrace M code x tr ) ) } )
```

### *text prefix* · `GenLimit.textPrefix`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( ℕ → α ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.textPrefix x t ) = ( List.map x ( List.range t ) ) )
```

### *TM device* · `GenLimit.ComputationalTrace.TM.device`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.ComputationalTrace.TM.device = ( GenLimit.ComputationalTrace.Control.Device.mk ( fun w => ( GenLimit.ComputationalTrace.TM.Memory.mk w 0 0 ( fun ( x : ℤ ) => Bool.false ) ) ) ( fun m => ( ( GenLimit.ComputationalTrace.TM.readInput ( GenLimit.ComputationalTrace.TM.Memory.input m ) ( GenLimit.ComputationalTrace.TM.Memory.inputHead m ) ) , ( GenLimit.ComputationalTrace.TM.Memory.tape m ( GenLimit.ComputationalTrace.TM.Memory.workHead m ) ) ) ) ( fun m => ( fun a => ( GenLimit.ComputationalTrace.TM.Memory.mk ( GenLimit.ComputationalTrace.TM.Memory.input m ) ( ( GenLimit.ComputationalTrace.TM.Memory.inputHead m ) + ( GenLimit.ComputationalTrace.TM.Motion.offset ( Prod.fst a ) ) ) ( ( GenLimit.ComputationalTrace.TM.Memory.workHead m ) + ( GenLimit.ComputationalTrace.TM.Motion.offset ( Prod.fst ( Prod.snd a ) ) ) ) ( Option.elim ( Prod.snd ( Prod.snd a ) ) ( GenLimit.ComputationalTrace.TM.Memory.tape m ) ( fun bit => ( Function.update ( GenLimit.ComputationalTrace.TM.Memory.tape m ) ( GenLimit.ComputationalTrace.TM.Memory.workHead m ) bit ) ) ) ) ) ) ( fun ( x : GenLimit.ComputationalTrace.TM.Memory ) => Bool.true ) ) )
```

### *trace learner* · `GenLimit.ComputationalTrace.traceLearner`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( ι : Type _ ) , ∀ ( xs : ( List ( GenLimit.ComputationalTrace.Example ι ) ) ) , ( ( GenLimit.ComputationalTrace.traceLearner xs ) = ( GenLimit.ComputationalTrace.Recognizer.mk ( Option.getD ( Option.map ( fun e => ( GenLimit.ComputationalTrace.Config.state ( GenLimit.ComputationalTrace.Trace.first ( Prod.snd e ) ) ) ) ( List.head? xs ) ) 0 ) ( List.foldr ( fun x => ( fun x_1 => ( x ∪ x_1 ) ) ) EmptyCollection.emptyCollection ( List.map ( fun e => ( GenLimit.ComputationalTrace.Trace.facts ( Prod.snd e ) ) ) xs ) ) ) )
```

## P27

SHA-256 of the checked page: `2f00ca13919f073b37d9224f29d62c8743aa026e593752dad6cb91f6d63d27ba`

### *eventually correct mistake generatable* · `GenLimit.FeedbackQueries.EventuallyCorrectMistakeGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( targets : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.FeedbackQueries.EventuallyCorrectMistakeGeneratable targets ) ) ↔ ( ( ∃ strategy : ( GenLimit.FeedbackQueries.SourceElementMistakeStrategy α ) , ( GenLimit.FeedbackQueries.EventuallyCorrectMistakeGenerates strategy targets ) ) )
```

### *eventually correct query generatable* · `GenLimit.FeedbackQueries.EventuallyCorrectQueryGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( targets : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.FeedbackQueries.EventuallyCorrectQueryGeneratable targets ) ) ↔ ( ( ∃ strategy : ( GenLimit.FeedbackQueries.SourceSetQueryStrategy α ) , ( GenLimit.FeedbackQueries.EventuallyCorrectQueryGenerates strategy targets ) ) )
```

### *generatable in limit* · `GenLimit.Generic.GeneratableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.GeneratableInLimit H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.Generic.IsLimitGenerator gen H ) ) )
```

### *has countable inner cover* · `GenLimit.FeedbackQueries.HasCountableInnerCover`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( targets : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.FeedbackQueries.HasCountableInnerCover targets ) ) ↔ ( ( Nonempty ( GenLimit.FeedbackQueries.CountableInnerCover targets ) ) )
```

### *has finite inner cover* · `GenLimit.FeedbackQueries.HasFiniteInnerCover`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( targets : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.FeedbackQueries.HasFiniteInnerCover targets ) ) ↔ ( ( Nonempty ( GenLimit.FeedbackQueries.FiniteInnerCover targets ) ) )
```

### *set generatable in limit* · `GenLimit.Generic.SetGeneratableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.SetGeneratableInLimit H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.SetGenerator α ) , ( GenLimit.Generic.IsSetLimitGenerator gen H ) ) )
```

### *source element mistake generatable* · `GenLimit.FeedbackQueries.SourceElementMistakeGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( targets : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.FeedbackQueries.SourceElementMistakeGeneratable targets ) ) ↔ ( ( ∃ strategy : ( GenLimit.FeedbackQueries.SourceElementMistakeStrategy α ) , ( GenLimit.FeedbackQueries.SourceElementMistakeGenerates strategy targets ) ) )
```

### *source element query generatable* · `GenLimit.FeedbackQueries.SourceElementQueryGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( targets : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.FeedbackQueries.SourceElementQueryGeneratable targets ) ) ↔ ( ( ∃ strategy : ( GenLimit.FeedbackQueries.SourceElementQueryStrategy α ) , ( GenLimit.FeedbackQueries.SourceElementQueryGenerates strategy targets ) ) )
```

### *source set mistake generatable* · `GenLimit.FeedbackQueries.SourceSetMistakeGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Countable α ] , ∀ ( targets : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.FeedbackQueries.SourceSetMistakeGeneratable targets ) ) ↔ ( ( ∃ strategy : ( GenLimit.FeedbackQueries.SourceSetMistakeStrategy α ) , ( GenLimit.FeedbackQueries.SourceSetMistakeGenerates strategy targets ) ) )
```

### *source set query generatable* · `GenLimit.FeedbackQueries.SourceSetQueryGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( targets : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.FeedbackQueries.SourceSetQueryGeneratable targets ) ) ↔ ( ( ∃ strategy : ( GenLimit.FeedbackQueries.SourceSetQueryStrategy α ) , ( GenLimit.FeedbackQueries.SourceSetQueryGenerates strategy targets ) ) )
```

### *zero example element mistake generatable* · `GenLimit.FeedbackQueries.ZeroExampleElementMistakeGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( targets : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.FeedbackQueries.ZeroExampleElementMistakeGeneratable targets ) ) ↔ ( ( ∃ strategy : ( GenLimit.FeedbackQueries.ZeroExampleElementMistakeStrategy α ) , ( GenLimit.FeedbackQueries.ZeroExampleElementMistakeGenerates strategy targets ) ) )
```

### *zero example set query generatable* · `GenLimit.FeedbackQueries.ZeroExampleSetQueryGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( targets : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.FeedbackQueries.ZeroExampleSetQueryGeneratable targets ) ) ↔ ( ( ∃ strategy : ( GenLimit.FeedbackQueries.ZeroExampleSetQueryStrategy α ) , ( GenLimit.FeedbackQueries.ZeroExampleSetQueryGenerates strategy targets ) ) )
```

## P28

SHA-256 of the checked page: `c61dd5e1633df1d68473ad884131ea2b2d5c643e2b7eae591547459fe8b3ed58`

### *all proper nontrivial* · `GenLimit.ContrastiveGeneration.AllProperNontrivial`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.ContrastiveGeneration.AllProperNontrivial F ) ) ↔ ( ∀ ( i : ℕ ) , ( ( Set.Nonempty ( F i ) ) ∧ ( Set.Nonempty ( HasCompl.compl ( F i ) ) ) ) )
```

### *clean families* · `GenLimit.ContrastiveGeneration.cleanFamilies`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( P : ( ( GenLimit.Generic.LanguageFamily ℕ ) → Prop ) ) , ( ( GenLimit.ContrastiveGeneration.cleanFamilies P ) = { F : ( GenLimit.Generic.LanguageFamily ℕ ) | ( ( ∀ i : ℕ , ( Set.Infinite ( F i ) ) ) ∧ ( ( GenLimit.ContrastiveGeneration.AllProperNontrivial F ) ∧ ( P F ) ) ) } )
```

### *co singleton family* · `GenLimit.ContrastiveGeneration.coSingletonFamily`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.ContrastiveGeneration.coSingletonFamily = GenLimit.ContrastiveGeneration.coSingletonSupport )
```

### *common vertices* · `GenLimit.ContrastiveGeneration.commonVertices`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( h g : ( Set α ) ) , ( ( GenLimit.ContrastiveGeneration.commonVertices h g ) = { x : α | ( ∃ e : ( GenLimit.ContrastiveGeneration.Edge α ) , ( ( GenLimit.ContrastiveGeneration.CommonCrossing h g e ) ∧ ( GenLimit.ContrastiveGeneration.Incident x e ) ) ) } )
```

### *contrastive closure dimension equals* · `GenLimit.ContrastiveGeneration.ContrastiveClosureDimensionEquals`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ∀ ( d : ℕ ) , ( ( GenLimit.ContrastiveGeneration.ContrastiveClosureDimensionEquals «𝓗» d ) ) ↔ ( ( ( GenLimit.ContrastiveGeneration.ContrastiveClosureDimensionAtMost «𝓗» d ) ) ∧ ( ∀ ( b : ℕ ) , ∀ ( _ : ( GenLimit.ContrastiveGeneration.ContrastiveClosureDimensionAtMost «𝓗» b ) ) , ( d ≤ b ) ) )
```

### *contrastively generatable* · `GenLimit.ContrastiveGeneration.ContrastivelyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ( ( GenLimit.ContrastiveGeneration.ContrastivelyGeneratable «𝓗» ) ) ↔ ( depends_only% [ α , «𝓗» ] ( ∃ G : ( GenLimit.ContrastiveGeneration.ContrastiveGenerator α ) , ∀ h ∈ «𝓗» , ( GenLimit.ContrastiveGeneration.GeneratesFrom G h ) ) )
```

### *contrastively identifiable* · `GenLimit.ContrastiveGeneration.ContrastivelyIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.ContrastiveGeneration.ContrastivelyIdentifiable F ) ) ↔ ( ( ∃ I : ( GenLimit.ContrastiveGeneration.ContrastiveIdentifier α ) , ( GenLimit.ContrastiveGeneration.ContrastivelyIdentifies I F ) ) )
```

### *defect number* · `GenLimit.ContrastiveGeneration.defectNumber`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( h g : ( Set α ) ) , ( ( GenLimit.ContrastiveGeneration.defectNumber h g ) = ( Set.encard ( GenLimit.ContrastiveGeneration.positiveDefectSet h g ) ) )
```

### *finite contrastive closure dimension* · `GenLimit.ContrastiveGeneration.FiniteContrastiveClosureDimension`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ( ( GenLimit.ContrastiveGeneration.FiniteContrastiveClosureDimension «𝓗» ) ) ↔ ( ( ∃ d : ℕ , ( GenLimit.ContrastiveGeneration.ContrastiveClosureDimensionAtMost «𝓗» d ) ) )
```

### *finitely corruption contrastively identifiable* · `GenLimit.ContrastiveGeneration.FinitelyCorruptionContrastivelyIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.ContrastiveGeneration.FinitelyCorruptionContrastivelyIdentifiable F ) ) ↔ ( depends_only% [ α , F ] ( ∃ I : ( GenLimit.ContrastiveGeneration.ContrastiveIdentifier α ) , ∀ ( k z : ℕ ) , ∀ ( x : ( ℕ → ( GenLimit.ContrastiveGeneration.Edge α ) ) ) , ( GenLimit.ContrastiveGeneration.KContrastivelyIdentifiesFrom k I F z x ) ) )
```

### *generatable in limit* · `GenLimit.Generic.GeneratableInLimit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( GenLimit.Generic.LanguageClass α ) ) , ( ( GenLimit.Generic.GeneratableInLimit H ) ) ↔ ( ( ∃ gen : ( GenLimit.Generic.Generator α ) , ( GenLimit.Generic.IsLimitGenerator gen H ) ) )
```

### *incomparable* · `GenLimit.ContrastiveGeneration.Incomparable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( h g : ( Set α ) ) , ( ( GenLimit.ContrastiveGeneration.Incomparable h g ) ) ↔ ( ( ( ¬ ( binrel% HasSubset.Subset h g ) ) ∧ ( ¬ ( binrel% HasSubset.Subset g h ) ) ) )
```

### *is contrastive presentation* · `GenLimit.ContrastiveGeneration.IsContrastivePresentation`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( stream : ( ℕ → ( GenLimit.ContrastiveGeneration.Edge α ) ) ) , ∀ ( h : ( Set α ) ) , ( ( GenLimit.ContrastiveGeneration.IsContrastivePresentation stream h ) ) ↔ ( ( ( ∀ n : ℕ , ( GenLimit.ContrastiveGeneration.Crosses h ( stream n ) ) ) ) ∧ ( ( binrel% HasSubset.Subset h { x : α | ( ∃ n : ℕ , ( GenLimit.ContrastiveGeneration.Incident x ( stream n ) ) ) } ) ) )
```

### *is eventual core* · `GenLimit.ContrastiveGeneration.IsEventualCore`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ∀ ( core : ( ℕ → α ) ) , ( ( GenLimit.ContrastiveGeneration.IsEventualCore «𝓗» core ) ) ↔ ( ( ( Function.Injective core ) ) ∧ ( ( ∀ h ∈ «𝓗» , ( Set.Finite { m : ℕ | ( ( core m ) ∉ h ) } ) ) ) )
```

### *is least positive uniform threshold* · `GenLimit.ContrastiveGeneration.IsLeastPositiveUniformThreshold`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ∀ ( d : ℕ ) , ( ( GenLimit.ContrastiveGeneration.IsLeastPositiveUniformThreshold «𝓗» d ) ) ↔ ( ( ( 0 < d ) ) ∧ ( ( ( GenLimit.ContrastiveGeneration.UniformlyContrastivelyGeneratableAt «𝓗» d ) ) ∧ ( ∀ ( k : ℕ ) , ∀ ( _ : ( 0 < k ) ) , ∀ ( _ : ( GenLimit.ContrastiveGeneration.UniformlyContrastivelyGeneratableAt «𝓗» k ) ) , ( d ≤ k ) ) ) )
```

### *is shared presentation* · `GenLimit.ContrastiveGeneration.IsSharedPresentation`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( ℕ → ( GenLimit.ContrastiveGeneration.Edge α ) ) ) , ∀ ( family : ( Finset ( Set α ) ) ) , ( ( GenLimit.ContrastiveGeneration.IsSharedPresentation x family ) ) ↔ ( ∀ h ∈ family , ( GenLimit.ContrastiveGeneration.IsContrastivePresentation x h ) )
```

### *k contrastively identifiable* · `GenLimit.ContrastiveGeneration.KContrastivelyIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( k : ℕ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.ContrastiveGeneration.KContrastivelyIdentifiable k F ) ) ↔ ( depends_only% [ α , k , F ] ( ∃ I : ( GenLimit.ContrastiveGeneration.ContrastiveIdentifier α ) , ∀ ( z : ℕ ) , ∀ ( x : ( ℕ → ( GenLimit.ContrastiveGeneration.Edge α ) ) ) , ( GenLimit.ContrastiveGeneration.KContrastivelyIdentifiesFrom k I F z x ) ) )
```

### *k text identifiable* · `GenLimit.ContrastiveGeneration.KTextIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( k : ℕ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.ContrastiveGeneration.KTextIdentifiable k F ) ) ↔ ( depends_only% [ α , k , F ] ( ∃ M : ( GenLimit.Angluin.SemanticIdentifier α ) , ∀ ( z : ℕ ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ( GenLimit.ContrastiveGeneration.KTextIdentifiesFrom k M F z x ) ) )
```

### *nonuniformly contrastively generatable* · `GenLimit.ContrastiveGeneration.NonuniformlyContrastivelyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ( ( GenLimit.ContrastiveGeneration.NonuniformlyContrastivelyGeneratable «𝓗» ) ) ↔ ( ( ∃ G : ( GenLimit.ContrastiveGeneration.ContrastiveGenerator α ) , ( GenLimit.ContrastiveGeneration.NonuniformlyContrastivelyGenerates G «𝓗» ) ) )
```

### *not eliminable from* · `GenLimit.ContrastiveGeneration.NotEliminableFrom`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( g h : ( Set α ) ) , ( ( GenLimit.ContrastiveGeneration.NotEliminableFrom g h ) ) ↔ ( ( ∃ x : ( ℕ → ( GenLimit.ContrastiveGeneration.Edge α ) ) , ( ( GenLimit.ContrastiveGeneration.IsContrastivePresentation x h ) ) ∧ ( ( ∀ n : ℕ , ( GenLimit.ContrastiveGeneration.Crosses g ( x n ) ) ) ) ) )
```

### *overlapping cover* · `GenLimit.ContrastiveGeneration.OverlappingCover`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( h g : ( Set α ) ) , ( ( GenLimit.ContrastiveGeneration.OverlappingCover h g ) ) ↔ ( ( ( Set.Nonempty ( h ∩ g ) ) ∧ ( ( h ∪ g ) = Set.univ ) ) )
```

### *proper nontrivial support* · `GenLimit.ContrastiveGeneration.ProperNontrivialSupport`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( h : ( Set α ) ) , ( ( GenLimit.ContrastiveGeneration.ProperNontrivialSupport h ) ) ↔ ( ( ( Set.Nonempty h ) ∧ ( Set.Nonempty ( HasCompl.compl h ) ) ) )
```

### *robust block family* · `GenLimit.ContrastiveGeneration.robustBlockFamily`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( k : ℕ ) , ( ( GenLimit.ContrastiveGeneration.robustBlockFamily k ) = ( GenLimit.ContrastiveGeneration.robustBlockSupport k ) )
```

### *stream prefix* · `GenLimit.ContrastiveGeneration.streamPrefix`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( x : ( ℕ → ( GenLimit.ContrastiveGeneration.Edge α ) ) ) , ∀ ( t : ℕ ) , ∀ ( i : ( Fin t ) ) , ( ( GenLimit.ContrastiveGeneration.streamPrefix x t i ) = ( x ( Fin.val i ) ) )
```

### *text identifiable* · `GenLimit.ContrastiveGeneration.TextIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( F : ( GenLimit.Generic.LanguageFamily α ) ) , ( ( GenLimit.ContrastiveGeneration.TextIdentifiable F ) ) ↔ ( ( ∃ M : ( GenLimit.Angluin.SemanticIdentifier α ) , ( GenLimit.Angluin.SemanticallyIdentifies M F ) ) )
```

### *uniformly contrastively generatable* · `GenLimit.ContrastiveGeneration.UniformlyContrastivelyGeneratable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( «𝓗» : ( Set ( Set α ) ) ) , ( ( GenLimit.ContrastiveGeneration.UniformlyContrastivelyGeneratable «𝓗» ) ) ↔ ( ( ∃ d : ℕ , ( GenLimit.ContrastiveGeneration.UniformlyContrastivelyGeneratableAt «𝓗» d ) ) )
```

## P29

SHA-256 of the checked page: `47756fbf9370fb7c4f49c7f5b9d04bc0428087a50f6bf60d017347145b643f46`

### *countable semantic generated* · `GenLimit.MistakeBounded.countableSemanticGenerated`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Infinite α ] , ∀ ( activeCount : ( ℕ → ℕ ) ) , ∀ ( initialWeight : ( ℕ → ℝ ) ) , ∀ ( language : ( ℕ → ( Set α ) ) ) , ∀ ( observed : ( ℕ → α ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.MistakeBounded.countableSemanticGenerated activeCount initialWeight language observed t ) = ( GenLimit.MistakeBounded.infiniteFreshWeightedMaximizer ( Finset.range ( activeCount t ) ) ( GenLimit.MistakeBounded.countableSemanticWeight activeCount initialWeight language observed t ) language ( IRStatement.FirstTerms.firstTerms observed t ) ) )
```

### *finite class closure dimension at most* · `GenLimit.MistakeBounded.FiniteClassClosureDimensionAtMost`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( N : ℕ ) , ∀ ( language : ( ( Fin N ) → ( Set α ) ) ) , ∀ ( d : ℕ ) , ( ( GenLimit.MistakeBounded.FiniteClassClosureDimensionAtMost language d ) ) ↔ ( ∀ ( active : ( Finset ( Fin N ) ) ) , let F := ( GenLimit.MistakeBounded.finiteClassIntersection language active ) ; ∀ ( _ : ( Set.Finite F ) ) , ( ( Set.ncard F ) ≤ d ) )
```

### *finite semantic generated* · `GenLimit.MistakeBounded.finiteSemanticGenerated`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ [ Infinite α ] , ∀ ( N : ℕ ) , ∀ ( language : ( ( Fin N ) → ( Set α ) ) ) , ∀ ( observed : ( ℕ → α ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.MistakeBounded.finiteSemanticGenerated language observed t ) = ( GenLimit.MistakeBounded.infiniteFreshWeightedMaximizer Finset.univ ( GenLimit.MistakeBounded.finiteSemanticWeight language observed t ) language ( IRStatement.FirstTerms.firstTerms observed t ) ) )
```

### *generator* · `GenLimit.Generic.Generator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.Generator α ) = ( GenLimit.Generic.FiniteHistoryOperator α α ) )
```

### *language* · `GenLimit.Generic.Language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.Language α ) = ( Set α ) )
```

### *last mistake before* · `GenLimit.MistakeBounded.LastMistakeBefore`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( trace : GenLimit.MistakeBounded.MistakeTrace ) , ∀ ( last : ℕ ) , ( ( GenLimit.MistakeBounded.LastMistakeBefore trace last ) ) ↔ ( ( ∀ ( t : ℕ ) , last ≤ t → ( ( trace t ) = Bool.false ) ) )
```

### *output* · `GenLimit.Generic.output`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.Generic.Generator α ) ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.Generic.output G x t ) = ( G t ( fun i => ( x ( Fin.val i ) ) ) ) )
```

### *prefix complexity* · `GenLimit.MistakeBounded.prefixComplexity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( L : ( ℕ → ( Set α ) ) ) , ∀ ( i : ℕ ) , ( ( GenLimit.MistakeBounded.prefixComplexity L i ) = ( Finset.sup ( Finset.powerset ( Finset.range i ) ) ( fun J => ( Set.ncard ( GenLimit.MistakeBounded.modifiedGreedyFiniteIntersection L i J ) ) ) ) )
```

### *stream* · `GenLimit.Generic.Stream`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.Stream α ) = ( ℕ → α ) )
```

### *total mistakes at most* · `GenLimit.MistakeBounded.TotalMistakesAtMost`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( trace : GenLimit.MistakeBounded.MistakeTrace ) , ∀ ( bound : ℕ ) , ( ( GenLimit.MistakeBounded.TotalMistakesAtMost trace bound ) ) ↔ ( ∀ ( t : ℕ ) , ( ( GenLimit.MistakeBounded.mistakeCount trace t ) ≤ bound ) )
```

### *worst case mistakes* · `GenLimit.MistakeBounded.worstCaseMistakes`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Run : Type _ ) , ∀ ( trace : ( Run → GenLimit.MistakeBounded.MistakeTrace ) ) , ( ( GenLimit.MistakeBounded.worstCaseMistakes trace ) = ( iSup ( fun ( run : Run ) => ( iSup ( fun ( t : ℕ ) => ( ↑ ( GenLimit.MistakeBounded.mistakeCount ( trace run ) t ) ) ) ) ) ) )
```

## P30

SHA-256 of the checked page: `48b00a86b7c0e64c190fd5dc262a689d6f1de0b53fb6ed0aa5aece9295b216a2`

### *expected rate* · `GenLimit.TimeSensitive.RandomizedGenerator.expectedRate`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Ω : Type _ ) , ∀ [ MeasurableSpace Ω ] , ∀ ( A : ( GenLimit.TimeSensitive.RandomizedGenerator Ω ) ) , ∀ ( μ : ( MeasureTheory.Measure Ω ) ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( K : ( Set ℕ ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.TimeSensitive.RandomizedGenerator.expectedRate A μ s K t ) = ( MeasureTheory.integral μ ( fun ω => ( GenLimit.TimeSensitive.RandomizedGenerator.loss A s K t ω ) ) ) )
```

### *run* · `GenLimit.TimeSensitive.RandomizedGenerator.run`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( Ω : Type _ ) , ∀ [ MeasurableSpace Ω ] , ∀ ( A : ( GenLimit.TimeSensitive.RandomizedGenerator Ω ) ) , ∀ ( s : ( ℕ → ℕ ) ) , ∀ ( ω : Ω ) , ∀ ( t : ℕ ) , ( ( GenLimit.TimeSensitive.RandomizedGenerator.run A s ω t ) = ( GenLimit.TimeSensitive.RandomizedGenerator.choose A t ( fun i => ( s ( Fin.val i ) ) ) ω ) )
```

### *shared root* · `GenLimit.TimeSensitive.sharedRoot`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( z : ℕ ) , ( ( GenLimit.TimeSensitive.sharedRoot z ) = ( Insert.insert 0 ( Set.range ( fun j => ( ( Nat.pair z j ) + 1 ) ) ) ) )
```

### *totalized GCG output* · `GenLimit.TimeSensitive.totalizedGCGOutput`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( F : GenLimit.TimeSensitive.CanonicallyOrderedFamily ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( t : ℕ ) , ( ( GenLimit.TimeSensitive.totalizedGCGOutput F x t ) = ( GenLimit.TimeSensitive.totalizedRoundOutput F x t ( GenLimit.TimeSensitive.totalizedGCGRun F x t ) ) )
```

## P31

SHA-256 of the checked page: `5869ec09a66775dd7355489f19b9dc184ee1f4de28995bdf255e494434741bd2`

### *almost contained* · `GenLimit.BoundedMemory.AlmostContained`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( A B : ( Set α ) ) , ( ( GenLimit.BoundedMemory.AlmostContained A B ) ) ↔ ( ( Set.Finite ( A \ B ) ) )
```

### *arbitrary memoryless* · `GenLimit.BoundedMemory.ArbitraryMemoryless`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( Set ( Set α ) ) ) , ( ( GenLimit.BoundedMemory.ArbitraryMemoryless H ) ) ↔ ( ( ∃ G : ( α → ( GenLimit.BoundedMemory.InfiniteOutput α ) ) , ( GenLimit.BoundedMemory.IsArbitraryPresentationMemorylessGenerator ( fun ( x : α ) => ( ↑ ( G x ) ) ) H ) ) )
```

### *finitely repeating* · `GenLimit.BoundedMemory.FinitelyRepeating`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Sort _ ) , ∀ ( stream : ( ℕ → α ) ) , ( ( GenLimit.BoundedMemory.FinitelyRepeating stream ) ) ↔ ( ∀ ( x : α ) , ( Set.Finite { t : ℕ | ( ( stream t ) = x ) } ) )
```

### *full memory after one* · `GenLimit.BoundedMemory.FullMemoryAfterOne`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( Set ( Set α ) ) ) , ( ( GenLimit.BoundedMemory.FullMemoryAfterOne H ) ) ↔ ( depends_only% [ α , H ] ( ∃ G : ( ( List α ) → ( GenLimit.BoundedMemory.InfiniteOutput α ) ) , ∀ K ∈ H , ∀ ( x : α ) , ∀ ( xs : ( List α ) ) , ∀ ( _ : ( x ∈ K ) ) , ∀ ( _ : ( ∀ y ∈ xs , ( y ∈ K ) ) ) , ( binrel% HasSubset.Subset ( ↑ ( G ( List.cons x xs ) ) ) K ) ) )
```

### *incrementally approximately identifiable* · `GenLimit.BoundedMemory.IncrementallyApproximatelyIdentifiable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( N : ℕ ) , ∀ ( langs : ( ( Fin ( N + 1 ) ) → ( Set α ) ) ) , ( ( GenLimit.BoundedMemory.IncrementallyApproximatelyIdentifiable langs ) ) ↔ ( depends_only% [ α , N , langs ] ( ∃ learner : ( GenLimit.BoundedMemory.IncrementalLearner α ( Fin ( N + 1 ) ) ) , ∃ initial : ( Fin ( N + 1 ) ) , ∀ ( target : ( Fin ( N + 1 ) ) ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( langs target ) ) ) , ( GenLimit.BoundedMemory.ApproximatelyIdentifiesRun langs learner initial target x ) ) )
```

### *incrementally element generable* · `GenLimit.BoundedMemory.IncrementallyElementGenerable`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( N : ℕ ) , ∀ ( α : Type _ ) , ∀ ( langs : ( ( Fin ( N + 1 ) ) → ( Set α ) ) ) , ( ( GenLimit.BoundedMemory.IncrementallyElementGenerable langs ) ) ↔ ( depends_only% [ N , α , langs ] ( ∃ G : ( GenLimit.BoundedMemory.IncrementalLearner α α ) , ∃ initial : α , ∀ ( target : ( Fin ( N + 1 ) ) ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( langs target ) ) ) , ( GenLimit.BoundedMemory.IncrementalElementGeneratesRun ( langs target ) G initial x ) ) )
```

### *incrementally exactly identifiable on finitely repeating* · `GenLimit.BoundedMemory.IncrementallyExactlyIdentifiableOnFinitelyRepeating`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α ι : Type _ ) , ∀ ( langs : ( ι → ( Set α ) ) ) , ( ( GenLimit.BoundedMemory.IncrementallyExactlyIdentifiableOnFinitelyRepeating langs ) ) ↔ ( depends_only% [ α , ι , langs ] ( ∃ learner : ( GenLimit.BoundedMemory.IncrementalLearner α ι ) , ∃ initial : ι , ∀ ( target : ι ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( langs target ) ) ) , ∀ ( _ : ( GenLimit.BoundedMemory.FinitelyRepeating x ) ) , ( GenLimit.BoundedMemory.ExactlyIdentifiesRun learner initial target x ) ) )
```

### *incrementally index generable on finitely repeating* · `GenLimit.BoundedMemory.IncrementallyIndexGenerableOnFinitelyRepeating`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α ι : Type _ ) , ∀ ( langs : ( ι → ( Set α ) ) ) , ( ( GenLimit.BoundedMemory.IncrementallyIndexGenerableOnFinitelyRepeating langs ) ) ↔ ( depends_only% [ α , ι , langs ] ( ∃ generator : ( GenLimit.BoundedMemory.IncrementalLearner α ι ) , ∃ initial : ι , ∀ ( target : ι ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( langs target ) ) ) , ∀ ( _ : ( GenLimit.BoundedMemory.FinitelyRepeating x ) ) , ( GenLimit.BoundedMemory.IncrementalIndexGeneratesRun langs generator initial target x ) ) )
```

### *is finitely repeating element generator on* · `GenLimit.BoundedMemory.IsFinitelyRepeatingElementGeneratorOn`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.BoundedMemory.MemorylessElementGenerator α ) ) , ∀ ( K : ( Set α ) ) , ( ( GenLimit.BoundedMemory.IsFinitelyRepeatingElementGeneratorOn G K ) ) ↔ ( ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x K ) ) , ∀ ( _ : ( GenLimit.BoundedMemory.FinitelyRepeating x ) ) , depends_only% [ α , G , K , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.BoundedMemory.ElementCorrectAt G K x t ) ) ) )
```

### *is finitely repeating index generator* · `GenLimit.BoundedMemory.IsFinitelyRepeatingIndexGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α ι : Type _ ) , ∀ ( G : ( GenLimit.BoundedMemory.MemorylessIndexGenerator α ι ) ) , ∀ ( langs : ( ι → ( Set α ) ) ) , ( ( GenLimit.BoundedMemory.IsFinitelyRepeatingIndexGenerator G langs ) ) ↔ ( ∀ ( target : ι ) , ∀ ( x : ( GenLimit.Generic.Stream α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x ( langs target ) ) ) , ∀ ( _ : ( GenLimit.BoundedMemory.FinitelyRepeating x ) ) , depends_only% [ α , ι , G , langs , target , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( binrel% HasSubset.Subset ( langs ( G ( x t ) ) ) ( langs target ) ) ) ) )
```

### *is finitely repeating memoryless generator* · `GenLimit.BoundedMemory.IsFinitelyRepeatingMemorylessGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( G : ( GenLimit.BoundedMemory.MemorylessSetGenerator α ) ) , ∀ ( H : ( Set ( Set α ) ) ) , ( ( GenLimit.BoundedMemory.IsFinitelyRepeatingMemorylessGenerator G H ) ) ↔ ( ∀ K ∈ H , ∀ ( x : ( ℕ → α ) ) , ∀ ( _ : ( GenLimit.Generic.Presents x K ) ) , ∀ ( _ : ( GenLimit.BoundedMemory.FinitelyRepeating x ) ) , depends_only% [ α , G , H , K , x ] ( ∃ T : ℕ , ( ∀ ( t : ℕ ) , T ≤ t → ( GenLimit.BoundedMemory.ValidSetOutput G K ( x t ) ) ) ) )
```

### *lower density* · `GenLimit.KleinbergWei.OrderedLanguage.lowerDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( K : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( A : GenLimit.Language ) , ( ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity K A ) = ( Filter.liminf ( GenLimit.KleinbergWei.OrderedLanguage.prefixRatio K A ) Filter.atTop ) )
```

### *memoryless* · `GenLimit.BoundedMemory.RankedUniverse.Memoryless`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( e : ( α ≃ ℕ ) ) , ∀ ( k : ℕ ) , ∀ ( σ : ℝ ) , ( ( GenLimit.BoundedMemory.RankedUniverse.Memoryless e k σ ) ) ↔ ( ( GenLimit.BoundedMemory.RankedUniverse.Uniform e ( GenLimit.BoundedMemory.RankedUniverse.setRule e ) ( fun L => ( fun G => ( ( ∀ x : ℕ , ( Set.Infinite ( G x ) ) ) ∧ ( ( GenLimit.BoundedMemory.IsFinitelyRepeatingMemorylessGenerator G ( Set.range ( GenLimit.BoundedMemory.RankedUniverse.Family.lang L ) ) ) ∧ ( ∀ i : ( Fin k ) , ( ∀ s : ( GenLimit.Generic.Stream ℕ ) , ( ( GenLimit.Generic.Presents s ( GenLimit.BoundedMemory.RankedUniverse.Family.lang L i ) ) → ( ( GenLimit.BoundedMemory.FinitelyRepeating s ) → ( σ ≤ ( GenLimit.BoundedMemory.memorylessRunUpperDensity ( GenLimit.KleinbergWei.OrderedLanguage.canonical ( GenLimit.BoundedMemory.RankedUniverse.Family.lang L i ) ( GenLimit.BoundedMemory.RankedUniverse.Family.infinite L i ) ) G s ) ) ) ) ) ) ) ) ) ) ) )
```

### *memoryless element generator* · `GenLimit.BoundedMemory.MemorylessElementGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.BoundedMemory.MemorylessElementGenerator α ) = ( α → α ) )
```

### *memoryless index generator* · `GenLimit.BoundedMemory.MemorylessIndexGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α ι : Type _ ) , ( ( GenLimit.BoundedMemory.MemorylessIndexGenerator α ι ) = ( α → ι ) )
```

### *memoryless set generator* · `GenLimit.BoundedMemory.MemorylessSetGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.BoundedMemory.MemorylessSetGenerator α ) = ( α → ( Set α ) ) )
```

### *singleton core* · `GenLimit.BoundedMemory.singletonCore`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ∀ ( H : ( Set ( Set α ) ) ) , ∀ ( x : α ) , ( ( GenLimit.BoundedMemory.singletonCore H x ) = { y : α | ( ∀ K ∈ H , ( ( x ∈ K ) → ( y ∈ K ) ) ) } )
```

## P32

SHA-256 of the checked page: `254cfc42440930ee056fa87afd1046ee7772949e4c640c80852c0746c0926de2`

### *algorithm 6* · `GenLimit.InfinitelyManyHallucinations.Pods.algorithm6`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( E : GenLimit.InfinitelyManyHallucinations.ExplorationSet ) , ∀ ( size : ( ℕ → ℕ ) ) , ∀ ( scan : ( Equiv.Perm ℕ ) ) , ( ( GenLimit.InfinitelyManyHallucinations.Pods.algorithm6 C E size scan ) = ( GenLimit.InfinitelyManyHallucinations.Pods.Config.mk C ( GenLimit.InfinitelyManyHallucinations.ExplorationSet.carrier E ) Bool.false size scan ) )
```

### *algorithm 7* · `GenLimit.InfinitelyManyHallucinations.Pods.algorithm7`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( C : GenLimit.LanguageFamily ) , ∀ ( E : GenLimit.InfinitelyManyHallucinations.ExplorationSet ) , ∀ ( size : ( ℕ → ℕ ) ) , ∀ ( scan : ( Equiv.Perm ℕ ) ) , ( ( GenLimit.InfinitelyManyHallucinations.Pods.algorithm7 C E size scan ) = ( GenLimit.InfinitelyManyHallucinations.Pods.Config.mk C ( GenLimit.InfinitelyManyHallucinations.ExplorationSet.carrier E ) Bool.true size scan ) )
```

### *bounded by* · `GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( f : ( ℕ → ℕ ) ) , ∀ ( E : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f E ) ) ↔ ( ∀ ( n : ℕ ) , ( ( Finset.card ( GenLimit.InfinitelyManyHallucinations.Exhaustion.increment E ( n + 1 ) ) ) ≤ ( f ( n + 1 ) ) ) )
```

### *bounded lower precision values* · `GenLimit.InfinitelyManyHallucinations.boundedLowerPrecisionValues`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( f : ( ℕ → ℕ ) ) , ∀ ( L : GenLimit.InfinitelyManyHallucinations.Language ) , ∀ ( guess : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ( ( GenLimit.InfinitelyManyHallucinations.boundedLowerPrecisionValues f L guess ) = { r : ℝ | ( ∃ target : GenLimit.InfinitelyManyHallucinations.Exhaustion , ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.Exhausts target L ) ∧ ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy f target ) ∧ ( r = ( GenLimit.InfinitelyManyHallucinations.exhaustionLowerPrecision target guess ) ) ) ) ) } )
```

### *compatible* · `GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : ( ℕ → GenLimit.KleinbergWei.OrderedLanguage ) ) , ( ( GenLimit.KleinbergWei.DensityMeasures.OrderedFocus.Compatible O ) ) ↔ ( ∀ ( i j a b c d : ℕ ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O i ) a ) = ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O j ) c ) ) ) , ∀ ( _ : ( ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O i ) b ) = ( GenLimit.KleinbergWei.OrderedLanguage.enumeration ( O j ) d ) ) ) , ∀ ( _ : ( a < b ) ) , ( c < d ) )
```

### *gamma admissible* · `GenLimit.InfinitelyManyHallucinations.ExplorationSet.GammaAdmissible`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( E : GenLimit.InfinitelyManyHallucinations.ExplorationSet ) , ∀ ( γ : ℝ ) , ( ( GenLimit.InfinitelyManyHallucinations.ExplorationSet.GammaAdmissible E γ ) ) ↔ ( ∀ ( m : ℕ ) , ( ( ↑ ( GenLimit.InfinitelyManyHallucinations.explorationCount ( GenLimit.InfinitelyManyHallucinations.ExplorationSet.carrier E ) m ) ) ≤ ( ( 1 - γ ) * ( ↑ m ) ) ) )
```

### *gamma novel* · `GenLimit.InfinitelyManyHallucinations.GammaNovel`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( γ : ℝ ) , ∀ ( adversary guess : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ( ( GenLimit.InfinitelyManyHallucinations.GammaNovel γ adversary guess ) ) ↔ ( ∀ ( n : ℕ ) , ∀ ( _ : ( 0 < ( Finset.card ( GenLimit.InfinitelyManyHallucinations.Exhaustion.stage guess n ) ) ) ) , ( γ ≤ ( ( ↑ ( Finset.card ( GenLimit.InfinitelyManyHallucinations.novelHistory adversary guess n ) ) ) / ( ↑ ( Finset.card ( GenLimit.InfinitelyManyHallucinations.Exhaustion.stage guess n ) ) ) ) ) )
```

### *generator novel* · `GenLimit.InfinitelyManyHallucinations.GeneratorNovel`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( G : GenLimit.InfinitelyManyHallucinations.BatchGenerator ) , ∀ ( adversary : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ( ( GenLimit.InfinitelyManyHallucinations.GeneratorNovel G adversary ) ) ↔ ( ∀ ( n : ℕ ) , let K := ( GenLimit.InfinitelyManyHallucinations.generatedStages G adversary n ) ; ( Disjoint ( G ( n + 1 ) ( fun i => ( GenLimit.InfinitelyManyHallucinations.Exhaustion.stage adversary ( Fin.val i ) ) ) K ) ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.stage adversary ( n + 1 ) ) ∪ K ) ) )
```

### *generic language* · `GenLimit.Generic.Language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( α : Type _ ) , ( ( GenLimit.Generic.Language α ) = ( Set α ) )
```

### *input* · `GenLimit.InfinitelyManyHallucinations.Pods.Counterexample.input`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.InfinitelyManyHallucinations.Pods.Counterexample.input = ( GenLimit.InfinitelyManyHallucinations.BatchedRace.blocks 1 GenLimit.InfinitelyManyHallucinations.Pods.Counterexample.word ) )
```

### *is enumeration* · `GenLimit.InfinitelyManyHallucinations.Exhaustion.IsEnumeration`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( E : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsEnumeration E ) ) ↔ ( ∀ ( n : ℕ ) , ( ( Finset.card ( GenLimit.InfinitelyManyHallucinations.Exhaustion.increment E ( n + 1 ) ) ) = 1 ) )
```

### *is single step* · `GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( E : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.IsSingleStep E ) ) ↔ ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.BoundedBy ( fun ( x : ℕ ) => 1 ) E ) )
```

### *limit* · `GenLimit.InfinitelyManyHallucinations.Exhaustion.limit`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( E : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ( ( GenLimit.InfinitelyManyHallucinations.Exhaustion.limit E ) = { x : ℕ | ( ∃ n : ℕ , ( x ∈ ( GenLimit.InfinitelyManyHallucinations.Exhaustion.stage E n ) ) ) } )
```

### *lower membership precision* · `GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( L : GenLimit.InfinitelyManyHallucinations.Language ) , ∀ ( guess : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ( ( GenLimit.InfinitelyManyHallucinations.lowerMembershipPrecision L guess ) = ( Filter.liminf ( fun n => ( GenLimit.InfinitelyManyHallucinations.membershipFraction L ( GenLimit.InfinitelyManyHallucinations.Exhaustion.stage guess n ) ) ) Filter.atTop ) )
```

### *lower recall* · `GenLimit.InfinitelyManyHallucinations.lowerRecall`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( target : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( guess : GenLimit.InfinitelyManyHallucinations.Language ) , ( ( GenLimit.InfinitelyManyHallucinations.lowerRecall target guess ) = ( GenLimit.KleinbergWei.OrderedLanguage.lowerDensity target guess ) )
```

### *lower tail precision* · `GenLimit.InfinitelyManyHallucinations.lowerTailPrecision`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( L : GenLimit.InfinitelyManyHallucinations.Language ) , ∀ ( guess : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ( ( GenLimit.InfinitelyManyHallucinations.lowerTailPrecision L guess ) = ( Filter.liminf ( GenLimit.InfinitelyManyHallucinations.stepTailPrecision L guess ) Filter.atTop ) )
```

### *natural* · `GenLimit.KleinbergWei.PartialEnumeration.Sharpness.natural`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.KleinbergWei.PartialEnumeration.Sharpness.natural = ( GenLimit.KleinbergWei.OrderedLanguage.mk (range_enumeration := by first | assumption | linarith | positivity | simp_all +zetaDelta) Set.univ id Function.injective_id ) )
```

### *parrot generator* · `GenLimit.InfinitelyManyHallucinations.parrotGenerator`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( n : ℕ ) , ∀ ( adversaryHistory : ( ( Fin ( n + 1 ) ) → ( Finset ℕ ) ) ) , ∀ ( x : ( Finset ℕ ) ) , ( ( GenLimit.InfinitelyManyHallucinations.parrotGenerator n adversaryHistory x ) = ( adversaryHistory ( Fin.mk (isLt := by first | assumption | linarith | positivity | simp_all +zetaDelta) n ) ) )
```

### *rule* · `GenLimit.InfinitelyManyHallucinations.Pods.Config.rule`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( c : GenLimit.InfinitelyManyHallucinations.Pods.Config ) , ∀ ( A : GenLimit.InfinitelyManyHallucinations.Exhaustion ) , ∀ ( t : ℕ ) , ∀ ( prev : ( Finset ℕ ) ) , ( ( GenLimit.InfinitelyManyHallucinations.Pods.Config.rule c A t prev ) = ( GenLimit.InfinitelyManyHallucinations.Pods.Config.output c A t ( GenLimit.InfinitelyManyHallucinations.Pods.State.pool ( GenLimit.InfinitelyManyHallucinations.Pods.Config.run c A t ) ) prev ) )
```

### *upper recall* · `GenLimit.InfinitelyManyHallucinations.upperRecall`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( target : GenLimit.KleinbergWei.OrderedLanguage ) , ∀ ( guess : GenLimit.InfinitelyManyHallucinations.Language ) , ( ( GenLimit.InfinitelyManyHallucinations.upperRecall target guess ) = ( GenLimit.KleinbergWei.OrderedLanguage.upperDensity target guess ) )
```

## P39

SHA-256 of the checked page: `7fc6137fd29e5d8c6f6d2e443d32972158396f5633ca26346c3768bcf0209776`

### *language* · `GenLimit.Language`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
( GenLimit.Language = ( Set ℕ ) )
```

### *partial patient lower density* · `GenLimit.PartialEnumeration.partialPatientLowerDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( z : ℕ ) , ( ( GenLimit.PartialEnumeration.partialPatientLowerDensity O x z ) = ( GenLimit.PatientScope.relativeLowerDensity ( ( GenLimit.GeneratorFirst x ( GenLimit.PatientMachine.output ( GenLimit.PartialEnumeration.closure O ) x ) ) ∩ ( O.language z ) ) ( O.language z ) ( GenLimit.OracleFamily.infinite' O z ) ) )
```

### *patient lower density* · `GenLimit.PatientMachine.patientLowerDensity`

- GF parses of the saved body: 1 complete
- Parsed tree equals the tree selected from the definition statement: True
- Saved body is the canonical rendering of the parsed tree: True
- Lean: accepted

Recovered proposition P′:

```lean
∀ ( O : GenLimit.OracleFamily ) , ∀ ( x : ( ℕ → ℕ ) ) , ∀ ( z : ℕ ) , ( ( GenLimit.PatientMachine.patientLowerDensity O x z ) = ( GenLimit.PatientScope.relativeLowerDensity ( ( GenLimit.GeneratorFirst x ( GenLimit.PatientMachine.output O x ) ) ∩ ( O.language z ) ) ( O.language z ) ( GenLimit.OracleFamily.infinite' O z ) ) )
```
