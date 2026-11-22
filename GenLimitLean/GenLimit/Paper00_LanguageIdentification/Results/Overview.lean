import GenLimit.Paper00_LanguageIdentification.Abstract.LearningTime
import GenLimit.Paper00_LanguageIdentification.Effective
import GenLimit.Paper00_LanguageIdentification.Text.Enumeration
import GenLimit.Paper00_LanguageIdentification.Text.Finite
import GenLimit.Paper00_LanguageIdentification.Text.Superfinite
import GenLimit.Paper00_LanguageIdentification.Informant.Enumeration

/-!
# Paper 0: main-results overview

This module is the public results facade for E. Mark Gold,
*Language Identification in the Limit* (1967).  Its declarations are thin
wrappers around the canonical proof modules and do not duplicate their
proofs.

The results below distinguish the two theorems printed as 10.1 and state
Corollary 10.1 in its corrected direction.
The two text impossibility theorems carry Gold's nameability convention.
-/

namespace GenLimit.Gold.Results

universe uInfo uObject uName

/-! ## Section 7. Methods of identification in the limit -/

/-- Gold's Theorem 7.1, bundling necessity of distinguishability,
identification by enumeration under collapsing uncertainty, and the
converse under countability of each object's set of allowable streams. -/
theorem theorem_7_1
    {I O N : Type*} [Countable I] [Countable O] [Nonempty O]
    (naming : Abstract.Naming N O) (allowed : Abstract.Allowable I O) :
    (Abstract.Identifiable naming allowed → Abstract.Distinguishable allowed) ∧
    (Abstract.CollapsingUncertainty allowed → ∀ e : ℕ → O, Function.Surjective e →
      Abstract.Identifies naming allowed (Abstract.identificationByEnumeration naming allowed e)) ∧
    ((∀ o, (allowed o).Countable) → Abstract.Distinguishable allowed →
      Abstract.Identifiable naming allowed) :=
  Abstract.theorem_7_1_clauses naming allowed

/-! ## Section 8. Ineffective identifiability in the limit -/

/-- A countable class whose languages all have names is learnable from arbitrary
complete informants. -/
theorem section_8_named_informants
    {N : Type*} [Nonempty N] (names : Effective.NameRelation N)
    (C : Set Language) (hc : C.Countable) (hn : ∀ L ∈ C, ∃ n, names n L) :
    ∃ M, Effective.Learns M names Effective.arbitraryInformant C :=
  Effective.countable_arbitrary_informant names C hc hn

/-- Every explicitly indexed family is semantically identifiable from
complete correct informants by least-compatible enumeration. -/
theorem complete_informant_enumeration (C : LanguageFamily) :
    Informant.IdentifiesFamilyFromInformant C
      (Informant.informantEnumerationLearner C) :=
  Informant.informantEnumerationLearner_identifiesFamily C

/-- A countable class whose languages all have names is learnable from recursive
texts and from primitive recursive texts. -/
theorem section_8_restricted_texts
    {N : Type*} [Nonempty N] (names : Effective.NameRelation N)
    (C : Set Language) (hc : C.Countable) (hn : ∀ L ∈ C, ∃ n, names n L) :
    (∃ M, Effective.Learns M names Effective.recursiveText C) ∧
    (∃ M, Effective.Learns M names Effective.primitiveRecursiveText C) :=
  Effective.section_8_restricted_texts names C hc hn

/-- Gold's sharp arbitrary-text semantic boundary from Section 8: finite
languages are identifiable, while every proper superclass is not. -/
theorem section_8_finite_superfinite_boundary :
    Text.SemanticallyIdentifiable Text.finiteLanguages ∧
      ∀ 𝒸 : Set Language, Text.finiteLanguages ⊂ 𝒸 →
        ¬ Text.SemanticallyIdentifiable 𝒸 :=
  Text.finiteLanguages_maximal_semanticallyIdentifiable

/-! ## Section 9. The weakness of text -/

/-- The canonical positive-text enumeration learner converges to the least
indexed language containing the target.  This records the precise semantic
limit when positive evidence cannot eliminate strict superlanguages. -/
theorem positive_text_enumeration_limit
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    StabilizesTo
      (fun t => Text.enumerationLearner C (textPrefix stream t))
      (Text.leastCover C z) :=
  Text.enumerationLearner_stabilizesTo_leastCover hP

/-! ## Section 10. Learning time -/

/-- The learning-time Theorem 10.1. Any learner that meets every deadline met by
enumeration has all of its own successful deadlines matched by enumeration. -/
theorem theorem_10_1_learning_time
    {N O I : Type*} (naming : Abstract.Naming N O) (allowed : Abstract.Allowable I O)
    (e : ℕ → O) (onto : Function.Surjective e) (M : Learner I N) :
    let G := Abstract.identificationByEnumeration naming allowed e
    Abstract.NoSlower naming allowed M G → Abstract.NoSlower naming allowed G M :=
  Abstract.enumeration_learning_time naming allowed e onto M

/-! ## Section 11. Translation from generators to testers -/

/-- The translation Theorem 10.1. A limiting translation of names transfers
effective identification to the destination naming relation. -/
theorem theorem_10_1_translation
    {I A B O : Type*} [Primcodable I] [Primcodable A] [Primcodable B]
    {method : Effective.Presentations I O} {src : Effective.Denotation A O}
    {dst : Effective.Denotation B O} {C : Set O}
    (h : Effective.Identifiable src method C) (tr : Effective.LimitTranslation src dst C) :
    Effective.Identifiable dst method C :=
  Effective.identification_of_limitTranslation h tr

/-- The corrected Corollary 10.1 rules out a limiting translation from generators
to testers on any class containing all finite languages and an infinite recursive language.
Gold printed the translation direction in reverse. `Effective.printed_corollary_10_1_is_false`
refutes the printed statement using the computable translation from testers to generators. -/
theorem corollary_10_1_corrected
    {C : Set Language} (finite : Text.finiteLanguages ⊆ C)
    {L : Language} (hl : L ∈ C) (hi : L.Infinite) (hr : L ∈ Effective.recursiveLanguages) :
    ¬ Effective.LimitTranslation Effective.Generator Effective.Tester C :=
  Effective.no_generator_to_tester_limit finite hl hi hr

/-- Theorem 10.2 rules out a two-recursive translation from domain generators to
complement-domain generators under the hypotheses of the corrected Corollary 10.1. -/
theorem theorem_10_2
    {C : Set Language} (finite : Text.finiteLanguages ⊆ C)
    {L : Language} (hl : L ∈ C) (hi : L.Infinite) (hr : L ∈ Effective.recursiveLanguages) :
    ¬ Effective.TwoRecursiveTranslation Effective.DomainGenerator Effective.AntiDomainGenerator C :=
  Effective.no_two_recursive_domain_to_antidomain finite hl hi hr

/-! ## Appendix I -/

/-- Appendix Theorem I.1 transfers identification with tester names to generator
names for the same presentation method. -/
theorem theorem_I_1
    {I : Type*} [Primcodable I] {m : Effective.Method I} {C : Set Language}
    (h : Effective.Identifiable Effective.Tester m C) :
    Effective.Identifiable Effective.Generator m C :=
  Effective.generator_identification_of_tester h

/-- Appendix Corollary I.2 gives the contrapositive of Theorem I.1. -/
theorem corollary_I_2
    {I : Type*} [Primcodable I] {m : Effective.Method I} {C : Set Language}
    (h : ¬ Effective.Identifiable Effective.Generator m C) :
    ¬ Effective.Identifiable Effective.Tester m C :=
  Effective.not_tester_identification_of_not_generator h

/-- Appendix Theorem I.3 equates identification from arbitrary, methodical,
and request informants. -/
theorem theorem_I_3
    {N : Type*} [Primcodable N] (names : Effective.NameRelation N) (C : Set Language) :
    (Effective.Identifiable names Effective.arbitraryInformant C ↔
      Effective.Identifiable names Effective.methodical C) ∧
    (Effective.Identifiable names Effective.methodical C ↔ Effective.RequestIdentifiable names C) :=
  Effective.informants_equivalent names C

/-- Appendix Theorem I.4 identifies the primitive recursive languages with tester
names from methodical informants. -/
theorem theorem_I_4 :
    Effective.Identifiable Effective.Tester Effective.methodical Effective.primitiveLanguages :=
  Effective.primitive_languages_methodical

/-- Appendix Theorem I.5 rules out generator identification of all recursive
languages from methodical informants. -/
theorem theorem_I_5 :
    ¬ Effective.Identifiable Effective.Generator Effective.methodical Effective.recursiveLanguages :=
  Effective.no_generator_recursive_methodical

/-- Appendix Theorem I.6 identifies the finite languages with tester names from
arbitrary texts. The explicit finite-set learner `Text.finiteLearner` guesses
the set of words seen so far. `Text.finiteLearner_identifiesFiniteLanguages`
proves that these guesses stabilize on each finite target. -/
theorem theorem_I_6 :
    Effective.Identifiable Effective.Tester Effective.arbitraryText Text.finiteLanguages :=
  Effective.finite_tester_identification

/-- Appendix Theorem I.7 identifies the recursively enumerable languages with
generator names from primitive recursive texts. -/
theorem theorem_I_7 :
    Effective.Identifiable Effective.Generator Effective.primitiveRecursiveText
      Effective.enumerableLanguages :=
  Effective.enumerable_languages_primitive_text

/-- Appendix Theorem I.8 rules out generator identification from recursive texts
for generator-named superfinite classes. -/
theorem theorem_I_8 {C : Set Language} (hs : Text.IsSuperfinite C) :
    ¬ (Effective.Named Effective.Generator C ∧
      Effective.Identifiable Effective.Generator Effective.recursiveText C) :=
  Effective.superfinite_generator_recursive_text hs

/-- Appendix Theorem I.9 rules out tester identification from primitive recursive
texts for tester-named superfinite classes. -/
theorem theorem_I_9 {C : Set Language} (hs : Text.IsSuperfinite C) :
    ¬ (Effective.Named Effective.Tester C ∧
      Effective.Identifiable Effective.Tester Effective.primitiveRecursiveText C) :=
  Effective.superfinite_tester_primitive_text hs

end GenLimit.Gold.Results
