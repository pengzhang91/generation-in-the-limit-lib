import GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration
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

## Coverage boundary

Theorem 7.1 is formalized at Gold's semantic, possibly ineffective level.
The wrapper for Appendix Theorem I.6 covers the finite-set learner and its
semantic convergence, using finite sets themselves as names; compilation to
indices of tester Turing machines is not formalized.  The Section 8 wrapper
states the exact arbitrary-text semantic finite/superfinite boundary, but
does not construct the recursive or primitive-recursive bad texts required
by Appendix Theorems I.8 and I.9.

The complete-informant enumeration result is likewise semantic and
noncomputable.  Effective naming relations, computable learners, and the
paper's recursive and primitive-recursive presentation restrictions remain
outside the current development.  Because positive texts are total streams
without a pause symbol, the identification obligation for the empty
language is vacuous.
-/

namespace GenLimit.Gold.Results

universe uInfo uObject uName

/-- Gold's Theorem 7.1, bundling necessity of distinguishability,
identification by enumeration under collapsing uncertainty, and the
countable semantic converse. -/
theorem theorem_7_1
    [Countable Info] [Countable Object] [Nonempty Object]
    (naming : Abstract.Naming Name Object)
    (allowable : Abstract.Allowable Info Object)
    (hcountable : ∀ object, (allowable object).Countable) :
    (Abstract.Identifiable naming allowable →
      Abstract.Distinguishable allowable) ∧
    (Abstract.CollapsingUncertainty allowable →
      ∀ enumeration : ℕ → Object,
        Function.Surjective enumeration →
        Abstract.Identifies naming allowable
          (Abstract.identificationByEnumeration
            naming allowable enumeration)) ∧
    (Abstract.Distinguishable allowable →
      Abstract.Identifiable naming allowable) :=
  Abstract.gold_theorem_7_1 naming allowable hcountable

/-- The explicit finite-set learner component of Appendix Theorem I.6. -/
theorem theorem_I_6_learner_semantic :
    Text.IdentifiesClass Text.finiteNaming Text.finiteLearner
      Text.finiteLanguages :=
  Text.finiteLearner_identifiesFiniteLanguages

/-- The semantic existence component of Appendix Theorem I.6, under
finite-set names rather than tester-machine indices. -/
theorem theorem_I_6_semantic :
    Text.IdentifiableWith Text.finiteNaming Text.finiteLanguages :=
  Text.finiteLanguages_identifiableWith

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

/-- Gold's sharp arbitrary-text semantic boundary from Section 8: finite
languages are identifiable, while every proper superclass is not. -/
theorem section_8_finite_superfinite_boundary :
    Text.SemanticallyIdentifiable Text.finiteLanguages ∧
      ∀ 𝒸 : Set Language, Text.finiteLanguages ⊂ 𝒸 →
        ¬ Text.SemanticallyIdentifiable 𝒸 :=
  Text.finiteLanguages_maximal_semanticallyIdentifiable

/-- The superfinite half of the Section 8 arbitrary-text semantic boundary. -/
theorem section_8_superfinite_obstruction
    {𝒸 : Set Language} (h𝒸 : Text.IsSuperfinite 𝒸) :
    ¬ Text.SemanticallyIdentifiable 𝒸 :=
  Text.superfinite_not_semanticallyIdentifiable h𝒸

/-- Every explicitly indexed family is semantically identifiable from
complete correct informants by least-compatible enumeration. -/
theorem complete_informant_enumeration (C : LanguageFamily) :
    Informant.IdentifiesFamilyFromInformant C
      (Informant.informantEnumerationLearner C) :=
  Informant.informantEnumerationLearner_identifiesFamily C

end GenLimit.Gold.Results
