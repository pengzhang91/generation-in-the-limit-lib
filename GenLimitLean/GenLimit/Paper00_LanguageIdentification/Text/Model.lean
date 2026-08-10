import GenLimit.Core.Identification

/-!
# #0 Language Identification: arbitrary positive text

This file specializes the paper-independent identification notions to
languages over `ℕ` presented by arbitrary exact positive texts.

A learner receives the ordered finite history, so it may depend on order and
repetition.  Identification is explanatory (syntactic): the learner must
eventually use one fixed name for the target.  A Lean learner in this semantic
layer need not be computable.

Because a text is a total stream `ℕ → ℕ`, no text presents the empty language.
Universal identification claims for the empty language are therefore vacuous;
no pause symbol is built into the model.
-/

namespace GenLimit
namespace Gold
namespace Text

/-- A naming relation represented as a not-necessarily-injective map from
names to languages. -/
structure Naming (Name : Type*) where
  language : Name → Language

/-- A Gold text learner is the natural-number-information specialization of
the shared ordered-history learner. -/
abbrev TextLearner (Name : Type*) := Learner ℕ Name

/-- Identification on one arbitrary positive text. -/
def IdentifiesOnText {Name : Type*}
    (N : Naming Name) (M : TextLearner Name)
    (stream : ℕ → ℕ) (L : Language) : Prop :=
  IdentifiesInLimit N.language M stream L

/-- A learner identifies one language from every arbitrary text for it. -/
def IdentifiesLanguage {Name : Type*}
    (N : Naming Name) (M : TextLearner Name) (L : Language) : Prop :=
  ∀ stream, Presents stream L → IdentifiesOnText N M stream L

/-- A learner identifies every member of a class from every arbitrary text. -/
def IdentifiesClass {Name : Type*}
    (N : Naming Name) (M : TextLearner Name)
    (𝒞 : Set Language) : Prop :=
  ∀ L, L ∈ 𝒞 → IdentifiesLanguage N M L

/-- A class is identifiable relative to a fixed naming relation. -/
def IdentifiableWith {Name : Type*}
    (N : Naming Name) (𝒞 : Set Language) : Prop :=
  ∃ M, IdentifiesClass N M 𝒞

/-- The indexed family itself supplies natural-number names. -/
def familyNaming (C : LanguageFamily) : Naming ℕ where
  language := C

/-- Identification of an indexed family using its indices as names. -/
def IdentifiesFamily
    (C : LanguageFamily) (M : TextLearner ℕ) : Prop :=
  ∀ z stream, Presents stream (C z) →
    IdentifiesOnText (familyNaming C) M stream (C z)

/-- Languages name themselves in the semantic specialization. -/
def semanticNaming : Naming Language where
  language := id

/-- A semantic learner identifies a class when its language-valued guesses
eventually stabilize extensionally to every presented target. -/
def SemanticallyIdentifiesClass
    (M : TextLearner Language) (𝒞 : Set Language) : Prop :=
  IdentifiesClass semanticNaming M 𝒞

/-- Existence of a possibly noncomputable semantic identifier. -/
def SemanticallyIdentifiable (𝒞 : Set Language) : Prop :=
  ∃ M, SemanticallyIdentifiesClass M 𝒞

/-- Compose a named learner with the denotation map. -/
def semanticLearner {Name : Type*}
    (N : Naming Name) (M : TextLearner Name) : TextLearner Language :=
  fun history => N.language (M history)

/-- Exact-name identification implies semantic identification. -/
theorem identifiesClass_semanticLearner
    {Name : Type*} {N : Naming Name} {M : TextLearner Name}
    {𝒞 : Set Language} (hM : IdentifiesClass N M 𝒞) :
    SemanticallyIdentifiesClass (semanticLearner N M) 𝒞 := by
  intro L hL stream hP
  obtain ⟨n, hn, T, hT⟩ := hM L hL stream hP
  refine ⟨L, rfl, T, ?_⟩
  intro t ht
  simp only [semanticLearner]
  rw [show M (textPrefix stream t) = n from hT t ht, hn]

theorem identifiableWith_implies_semanticallyIdentifiable
    {Name : Type*} {N : Naming Name} {𝒞 : Set Language}
    (h : IdentifiableWith N 𝒞) :
    SemanticallyIdentifiable 𝒞 := by
  obtain ⟨M, hM⟩ := h
  exact ⟨semanticLearner N M, identifiesClass_semanticLearner hM⟩

end Text
end Gold
end GenLimit
