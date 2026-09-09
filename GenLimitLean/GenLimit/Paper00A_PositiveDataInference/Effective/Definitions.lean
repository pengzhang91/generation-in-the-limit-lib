import GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions
import GenLimit.Support.FiniteEnumeration
import Mathlib.Computability.Partrec

/-!
# Effective positive-data identification

This file adds the computability hypotheses from Angluin's source theorem to
the shared ordered-history semantic interface.
-/

namespace GenLimit.Angluin

open GenLimit.Generic

/-- An indexed family of recursive languages: membership is uniformly
decidable and computable from the language index and the encoded word. -/
structure EffectiveIndexedFamily where
  language : Generic.LanguageFamily ℕ
  membership : ℕ → ℕ → Bool
  membership_spec : ∀ i x, membership i x = true ↔ x ∈ language i
  membership_computable : Computable₂ membership
  nonempty : AllNonempty language

/-- An effective identifier has the shared ordered-history learner type;
effectivity is imposed separately by `Computable`. -/
abbrev EffectiveIdentifier := SemanticIdentifier ℕ

/-- The left side of Theorem 1: a computable learner semantically identifies
every language in the effective indexed family.  `Computable M` is the
recursive-function form of Angluin's effective Turing-machine requirement,
modulo standard encodings. -/
def EffectiveInferrable (F : EffectiveIndexedFamily) : Prop :=
  ∃ M : EffectiveIdentifier, Computable M ∧
    SemanticallyIdentifies M F.language

/-- Compatibility name for the shared stage-by-stage enumeration API. -/
abbrev enumeratedSet := GenLimit.Support.enumeratedSet

/-- Set-valued tell-tale property for an enumeration without a halting
certificate. -/
def IsEnumeratedTellTale
    (C : Generic.LanguageFamily ℕ) (i : ℕ) (T : Set ℕ) : Prop :=
  T.Finite ∧ T ⊆ C i ∧
    ∀ j, T ⊆ C j → C j ⊆ C i → C i ⊆ C j

/-- Condition 1: one computable procedure, uniform in `i`, enumerates a finite
tell-tale for the language at index `i`. -/
def ConditionOne (F : EffectiveIndexedFamily) : Prop :=
  ∃ emit : ℕ → ℕ → Option ℕ, Computable₂ emit ∧
    ∀ i, IsEnumeratedTellTale F.language i (enumeratedSet emit i)

/-- Condition 3 (finite thickness): only finitely many distinct family
languages contain any fixed nonempty finite sample. -/
def ConditionThree (C : Generic.LanguageFamily ℕ) : Prop :=
  ∀ S : Finset ℕ, S.Nonempty →
    {L : Set ℕ | L ∈ Set.range C ∧ (↑S : Set ℕ) ⊆ L}.Finite

/-- Condition 4: language inclusion is uniformly computable from indices. -/
def ConditionFour (F : EffectiveIndexedFamily) : Prop :=
  ∃ inclusion : ℕ → ℕ → Bool, Computable₂ inclusion ∧
    ∀ i j, inclusion i j = true ↔ F.language i ⊆ F.language j

end GenLimit.Angluin

/-!
## Source-facing statements from Angluin (1980)
-/

namespace GenLimit.Angluin

/-- The exact effective biconditional asserted by Theorem 1. -/
def TheoremOneStatement (F : EffectiveIndexedFamily) : Prop :=
  EffectiveInferrable F ↔ ConditionOne F

/-- Corollary 1: effective inference implies a finite tell-tale for every
indexed language. -/
def CorollaryOneStatement (F : EffectiveIndexedFamily) : Prop :=
  EffectiveInferrable F → ConditionTwo F.language

/-- Corollary 2: finite thickness suffices for effective inference. -/
def CorollaryTwoStatement (F : EffectiveIndexedFamily) : Prop :=
  ConditionThree F.language → EffectiveInferrable F

/-- Corollary 3: finite tell-tales and computable inclusion suffice for
effective inference. -/
def CorollaryThreeStatement (F : EffectiveIndexedFamily) : Prop :=
  ConditionTwo F.language → ConditionFour F → EffectiveInferrable F

/-- Theorem 2: nonuniform finite tell-tales do not suffice for effective
positive-data inference. -/
def TheoremTwoStatement : Prop :=
  ∃ F : EffectiveIndexedFamily,
    ConditionTwo F.language ∧ ¬EffectiveInferrable F

end GenLimit.Angluin
