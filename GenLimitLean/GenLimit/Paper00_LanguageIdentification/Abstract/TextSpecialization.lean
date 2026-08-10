import GenLimit.Paper00_LanguageIdentification.Abstract.Model
import GenLimit.Paper00_LanguageIdentification.Text.Model

/-!
# Arbitrary positive text as an abstract identification situation

This file makes explicit that the concrete semantic Gold text model is a
special case of Gold's abstract identification model.  Information symbols
are natural numbers, objects are languages, and the allowable information
sequences for a language are exactly its arbitrary positive texts.

For a class `𝒞`, languages outside `𝒞` are assigned no allowable sequences.
Consequently, abstract identification for `classTextAllowable 𝒞` is exactly
concrete semantic identification of `𝒞`.  In particular, the absence of an
exact text for the empty language has the same vacuous interpretation on both
sides of the bridge.
-/

namespace GenLimit
namespace Gold
namespace Abstract

open Gold.Text

/-- The abstract allowability assignment whose information sequences are
exact arbitrary positive texts for their target languages. -/
def exactTextAllowable : Allowable ℕ Language :=
  fun language => {stream | Presents stream language}

@[simp] theorem mem_exactTextAllowable
    {language : Language} {stream : ℕ → ℕ} :
    stream ∈ exactTextAllowable language ↔ Presents stream language := by
  rfl

/-- Restrict exact positive texts to a specified class of target languages.
Objects outside the class have no allowable information sequences. -/
def classTextAllowable (𝒞 : Set Language) : Allowable ℕ Language :=
  fun language =>
    {stream | language ∈ 𝒞 ∧ Presents stream language}

@[simp] theorem mem_classTextAllowable
    {𝒞 : Set Language} {language : Language}
    {stream : ℕ → ℕ} :
    stream ∈ classTextAllowable 𝒞 language ↔
      language ∈ 𝒞 ∧ Presents stream language := by
  rfl

/-- In the semantic specialization, each language is its own chosen name. -/
def semanticLanguageNaming : Naming Language Language where
  denotes := id
  nameOf := id
  denotes_nameOf := fun _ => rfl

@[simp] theorem semanticLanguageNaming_denotes (language : Language) :
    semanticLanguageNaming.denotes language = language := by
  rfl

@[simp] theorem semanticLanguageNaming_nameOf (language : Language) :
    semanticLanguageNaming.nameOf language = language := by
  rfl

/-- On one exact text, abstract identification with semantic language names is
the concrete `IdentifiesOnText` predicate. -/
theorem identifiesOn_exactText_iff
    (learner : TextLearner Language)
    (stream : ℕ → ℕ) (language : Language) :
    IdentifiesOn semanticLanguageNaming learner stream language ↔
      IdentifiesOnText Gold.Text.semanticNaming learner stream language := by
  rfl

/-- Abstract identification under the class-restricted text assignment is
exactly concrete semantic identification of that class. -/
theorem identifies_classTextAllowable_iff
    (learner : TextLearner Language) (𝒞 : Set Language) :
    Identifies semanticLanguageNaming (classTextAllowable 𝒞) learner ↔
      SemanticallyIdentifiesClass learner 𝒞 := by
  constructor
  · intro hAbstract language hLanguage stream hPresents
    apply (identifiesOn_exactText_iff learner stream language).mp
    exact hAbstract language stream ⟨hLanguage, hPresents⟩
  · intro hConcrete language stream hAllowable
    apply (identifiesOn_exactText_iff learner stream language).mpr
    exact hConcrete language hAllowable.1 stream hAllowable.2

/-- Existential abstract identifiability under exact class texts is exactly
concrete semantic identifiability of the class. -/
theorem identifiable_classTextAllowable_iff (𝒞 : Set Language) :
    Identifiable semanticLanguageNaming (classTextAllowable 𝒞) ↔
      SemanticallyIdentifiable 𝒞 := by
  constructor
  · rintro ⟨learner, hLearner⟩
    exact ⟨learner,
      (identifies_classTextAllowable_iff learner 𝒞).mp hLearner⟩
  · rintro ⟨learner, hLearner⟩
    exact ⟨learner,
      (identifies_classTextAllowable_iff learner 𝒞).mpr hLearner⟩

theorem exactTextAllowable_eq_classTextAllowable_univ :
    exactTextAllowable = classTextAllowable Set.univ := by
  ext language stream
  simp

/-- The unrestricted assignment corresponds to concrete semantic
identification of the class of all languages. -/
theorem identifies_exactTextAllowable_iff
    (learner : TextLearner Language) :
    Identifies semanticLanguageNaming exactTextAllowable learner ↔
      SemanticallyIdentifiesClass learner Set.univ := by
  rw [exactTextAllowable_eq_classTextAllowable_univ]
  exact identifies_classTextAllowable_iff learner Set.univ

/-- The existential version of `identifies_exactTextAllowable_iff`. -/
theorem identifiable_exactTextAllowable_iff :
    Identifiable semanticLanguageNaming exactTextAllowable ↔
      SemanticallyIdentifiable Set.univ := by
  rw [exactTextAllowable_eq_classTextAllowable_univ]
  exact identifiable_classTextAllowable_iff Set.univ

end Abstract
end Gold
end GenLimit
