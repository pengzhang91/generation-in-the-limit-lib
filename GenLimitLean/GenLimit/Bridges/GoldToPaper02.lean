import GenLimit.Bridges.BasicToGeneric
import GenLimit.Bridges.AngluinToPaper02
import GenLimit.Bridges.Paper00ToPaper01
import GenLimit.Bridges.Paper01ToPaper02

/-!
# Gold identification and #02 Learning Theory

The co-singleton family already used to compare Gold and KM supplies the
countable non-identifiable class cited in #02.  Reusing it here avoids a second
finite-tell-tale obstruction proof inside the #02 development.
-/

namespace GenLimit.Gold

open Text

/-- Gold index identification of an infinite family implies the generic
#02 limit-generation conclusion through the shared Core theorem. -/
theorem identifiesFamily_implies_genericGeneratableInLimit
    (C : GenLimit.LanguageFamily)
    (hInfinite : ∀ i, (C i).Infinite)
    (M : TextLearner ℕ) (hM : IdentifiesFamily C M) :
    GenLimit.Generic.GeneratableInLimit (Set.range C) := by
  apply GenLimit.Generic.stabilizingIndexIdentifier_implies_generatableInLimit
    C hInfinite M
  intro z stream hPresentation
  exact hM z stream
    ((GenLimit.Bridge.basicPresents_iff_genericPresents _ _).mpr hPresentation)

/-- Gold's Nat-specific language-valued semantic predicate and P02's literal
extensional identifier predicate express the same notion. -/
theorem semanticallyIdentifiable_iff_paper02ExtensionallyIdentifiable
    (H : GenLimit.Generic.LanguageClass ℕ) :
    Text.SemanticallyIdentifiable H ↔
      GenLimit.Angluin.ExtensionallyIdentifiable H := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro L hL stream hPresentation
    simpa [Text.SemanticallyIdentifiesClass, Text.IdentifiesClass,
      Text.IdentifiesLanguage, Text.IdentifiesOnText, Text.semanticNaming] using
      hM L hL stream
        ((GenLimit.Bridge.basicPresents_iff_genericPresents _ _).mpr
          hPresentation)
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro L hL stream hPresentation
    simpa [Text.SemanticallyIdentifiesClass, Text.IdentifiesClass,
      Text.IdentifiesLanguage, Text.IdentifiesOnText, Text.semanticNaming] using
      hM L hL stream
        ((GenLimit.Bridge.basicPresents_iff_genericPresents _ _).mp
          hPresentation)

end GenLimit.Gold

namespace GenLimit.GoldP02Separation

open GoldKMSeparation

/-- P02 Theorem 2.2 at the shared semantic Gold interface: a countable UUS
class need not be identifiable in the limit from arbitrary positive text. -/
theorem theorem_2_2_countable_uus_not_identifiable :
    ∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ GenLimit.Generic.UUS H ∧
        ¬GenLimit.Angluin.ExtensionallyIdentifiable H := by
  refine ⟨coSingletonClass, Set.countable_range coSingletonLanguage, ?_,
    ?_⟩
  · intro L hL
    obtain ⟨i, rfl⟩ := hL
    exact coSingletonLanguage_infinite i
  · intro hIdent
    exact coSingleton_not_semanticallyIdentifiable
      ((GenLimit.Gold.semanticallyIdentifiable_iff_paper02ExtensionallyIdentifiable
        coSingletonClass).mpr hIdent)

/-- The same witness exposes the strict logical relation relevant to #02:
it is non-uniformly generatable even though Gold identification fails. -/
theorem nonuniform_generation_without_identification :
    ∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ GenLimit.Generic.UUS H ∧
        GenLimit.Generic.NonuniformlyGeneratable H ∧
        ¬GenLimit.Angluin.ExtensionallyIdentifiable H := by
  refine ⟨coSingletonClass, Set.countable_range coSingletonLanguage, ?_, ?_,
    ?_⟩
  · intro L hL
    obtain ⟨i, rfl⟩ := hL
    exact coSingletonLanguage_infinite i
  · simpa [coSingletonClass, coSingletonOracle, coSingletonLanguage] using
      GenLimit.KM.SetInterface.range_nonuniformlyGeneratable_via_paper02
        coSingletonOracle
  · intro hIdent
    exact coSingleton_not_semanticallyIdentifiable
      ((GenLimit.Gold.semanticallyIdentifiable_iff_paper02ExtensionallyIdentifiable
        coSingletonClass).mpr hIdent)

end GenLimit.GoldP02Separation
