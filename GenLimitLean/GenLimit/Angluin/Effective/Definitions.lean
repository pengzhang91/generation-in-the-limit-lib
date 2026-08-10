import GenLimit.Angluin.Semantic.Definitions
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

/-- The set enumerated for index `i` by a stage-by-stage output procedure. -/
def enumeratedSet
    (emit : ℕ → ℕ → Option ℕ) (i : ℕ) : Set ℕ :=
  {x | ∃ stage, emit i stage = some x}

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

/-- Theorem 2: nonuniform finite tell-tales do not suffice for effective
positive-data inference. -/
def TheoremTwoStatement : Prop :=
  ∃ F : EffectiveIndexedFamily,
    ConditionTwo F.language ∧ ¬EffectiveInferrable F

end GenLimit.Angluin
