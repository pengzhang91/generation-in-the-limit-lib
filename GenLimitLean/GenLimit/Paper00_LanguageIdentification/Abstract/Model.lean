import GenLimit.Core.Identification
import Mathlib.Data.Set.Countable

/-!
# #0 Language Identification: abstract identification situations

Section 6 of Gold's paper separates identification in the limit from the
special case of language learning.  An object is associated with a set of
allowable infinite information sequences.  Ordered histories and generic
learners come from `GenLimit.Core`; this module adds only Gold's abstract,
paper-specific structure.

This file formalizes that abstract semantic model.  As in the rest of the
Gold Layer 1 development, no effectiveness claim is made.
-/

namespace GenLimit
namespace Gold
namespace Abstract

universe uInfo uObject uName

/-- The allowable information sequences for each object. -/
abbrev Allowable
    (Info : Type uInfo) (Object : Type uObject) :=
  Object → Set (ℕ → Info)

/-- A naming relation together with a chosen name for every object.

Gold assumes in Theorem 7.1 that every object has at least one name.  Choosing
one such name is harmless in the ineffective layer and is exactly what the
enumeration learner needs in order to issue a conjecture. -/
structure Naming (Name : Type uName) (Object : Type uObject) where
  denotes : Name → Object
  nameOf : Object → Name
  denotes_nameOf : ∀ object, denotes (nameOf object) = object

/-- A finite history is compatible with an object when some allowable
information sequence for that object has exactly this prefix. -/
def Compatible
    (allowable : Allowable Info Object)
    (history : List Info) (object : Object) : Prop :=
  ∃ stream, stream ∈ allowable object ∧
    textPrefix stream history.length = history

/-- Every prefix of an allowable sequence is compatible with its object. -/
theorem compatible_textPrefix
    {allowable : Allowable Info Object}
    {object : Object} {stream : ℕ → Info}
    (hstream : stream ∈ allowable object) (t : ℕ) :
    Compatible allowable (textPrefix stream t) object := by
  refine ⟨stream, hstream, ?_⟩
  simp

/-- Gold's distinguishability condition: no allowable information sequence
describes two different objects. -/
def Distinguishable
    (allowable : Allowable Info Object) : Prop :=
  ∀ ⦃object₁ object₂ stream⦄,
    stream ∈ allowable object₁ →
    stream ∈ allowable object₂ →
    object₁ = object₂

/-- Gold's collapsing-uncertainty condition.

Along every allowable sequence for `target`, each different object is
eventually absent from the set of objects compatible with the observed
prefix. -/
def CollapsingUncertainty
    (allowable : Allowable Info Object) : Prop :=
  ∀ ⦃target stream⦄,
    stream ∈ allowable target →
    ∀ object, object ≠ target →
      ∃ T, ∀ t, T ≤ t →
        ¬ Compatible allowable (textPrefix stream t) object

/-- Identification on one fixed information sequence. -/
def IdentifiesOn
    (naming : Naming Name Object)
    (learner : Learner Info Name)
    (stream : ℕ → Info) (object : Object) : Prop :=
  IdentifiesInLimit naming.denotes learner stream object

/-- A learner identifies every object on each of its allowable information
sequences. -/
def Identifies
    (naming : Naming Name Object)
    (allowable : Allowable Info Object)
    (learner : Learner Info Name) : Prop :=
  ∀ object stream, stream ∈ allowable object →
    IdentifiesOn naming learner stream object

/-- Existence of a possibly noncomputable identifier. -/
def Identifiable
    (naming : Naming Name Object)
    (allowable : Allowable Info Object) : Prop :=
  ∃ learner, Identifies naming allowable learner

/-- The first occurrence of an object in a surjective enumeration. -/
noncomputable def firstEnumerationIndex
    {Object : Type uObject}
    (enumeration : ℕ → Object)
    (henumeration : Function.Surjective enumeration)
    (object : Object) : ℕ := by
  classical
  exact Nat.find (henumeration object)

theorem firstEnumerationIndex_spec
    {Object : Type uObject}
    (enumeration : ℕ → Object)
    (henumeration : Function.Surjective enumeration)
    (object : Object) :
    enumeration (firstEnumerationIndex enumeration henumeration object) =
      object := by
  classical
  exact Nat.find_spec (henumeration object)

theorem firstEnumerationIndex_minimal
    {Object : Type uObject}
    (enumeration : ℕ → Object)
    (henumeration : Function.Surjective enumeration)
    (object : Object) {i : ℕ}
    (hi :
      i < firstEnumerationIndex enumeration henumeration object) :
    enumeration i ≠ object := by
  classical
  exact Nat.find_min (henumeration object) hi

/-- The least enumerated object compatible with a finite history.  Histories
with no compatible enumerated object use index `0`; this fallback is never
used on an allowable information sequence when the enumeration is
surjective. -/
noncomputable def firstCompatibleIndex
    (allowable : Allowable Info Object)
    (enumeration : ℕ → Object) (history : List Info) : ℕ :=
  by
    classical
    exact
      if h : ∃ i, Compatible allowable history (enumeration i) then
        Nat.find h
      else
        0

/-- Gold's identification-by-enumeration learner. -/
noncomputable def identificationByEnumeration
    (naming : Naming Name Object)
    (allowable : Allowable Info Object)
    (enumeration : ℕ → Object) :
    Learner Info Name :=
  fun history =>
    naming.nameOf
      (enumeration (firstCompatibleIndex allowable enumeration history))

/-- The set of all information sequences allowable for at least one object. -/
def allowableSequences
    (allowable : Allowable Info Object) :
    Set (ℕ → Info) :=
  {stream | ∃ object, stream ∈ allowable object}

theorem allowableSequences_eq_iUnion
    (allowable : Allowable Info Object) :
    allowableSequences allowable = ⋃ object, allowable object := by
  ext stream
  simp [allowableSequences]

end Abstract
end Gold
end GenLimit
