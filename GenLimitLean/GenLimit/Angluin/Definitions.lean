import GenLimit.Core.GenericGeneration
import Mathlib.Computability.Partrec

/-!
# Angluin's positive-data identification framework

This file records the hypotheses and quantifiers of Dana Angluin's 1980
characterization theorem without conflating its effective and semantic parts.

Source: Dana Angluin, *Inductive Inference of Formal Languages from Positive
Data*, Information and Control **45** (1980), 117--135,
doi:10.1016/S0019-9958(80)90285-5.  The indexed-family and inference-machine
definitions occur on pp. 118--120, Condition 1 and Theorem 1 on pp. 121--123,
and Condition 2 / Corollary 1 on p. 123.

Publisher record:
https://www.sciencedirect.com/science/article/pii/S0019995880902855

The source theorem concerns an *effective indexed family*: membership is
uniformly recursive in the language index and the word, the inference machine
is effective, and the finite tell-tales are uniformly enumerable.  The
`EffectiveIndexedFamily`, `EffectiveInferrable`, and `ConditionOne` declarations
below retain those hypotheses using Mathlib's `Computable` predicate.

The generic declarations are deliberately called `Semantic...`.  They isolate
the set-theoretic correctness argument used inside the proof of Theorem 1, but
do not claim that an arbitrary Lean function is a recursive procedure.
-/

namespace GenLimit.Angluin

open GenLimit.Generic

/-! ## Positive-data identifiers and convergence -/

/-- A semantic identifier maps every finite positive-data history to a
language index. -/
abbrev SemanticIdentifier (α : Type*) := ∀ t : ℕ, (Fin t → α) → ℕ

/-- Run an identifier on the prefix strictly before time `t`. -/
def identifierOutput
    (M : SemanticIdentifier α) (stream : Stream α) (t : ℕ) : ℕ :=
  M t (fun i => stream i)

/-- The guesses of `M` stabilize syntactically to the single index `j`.

This is the convergence notion in Angluin's inference-machine definition.  It
is stronger than merely requiring every sufficiently late guessed language to
be extensionally correct when the family contains duplicate indices. -/
def ConvergesTo
    (M : SemanticIdentifier α) (stream : Stream α) (j : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t → identifierOutput M stream t = j

/-- `M` identifies index `z` from one exact positive presentation.  The stable
index may depend on the presentation, but must denote the target language. -/
def IdentifiesFrom
    (M : SemanticIdentifier α) (C : Generic.LanguageFamily α)
    (z : ℕ) (stream : Stream α) : Prop :=
  ∃ j, C j = C z ∧ ConvergesTo M stream j

/-- Semantic identification of an indexed family from every positive
presentation of each member. -/
def SemanticallyIdentifies
    (M : SemanticIdentifier α) (C : Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : Stream α, Generic.Presents stream (C z) →
    IdentifiesFrom M C z stream

/-- The source assumes every member of the indexed family is nonempty, so that
it has a positive presentation with no pause symbol. -/
def AllNonempty (C : Generic.LanguageFamily α) : Prop :=
  ∀ i, (C i).Nonempty

/-! ## Tell-tales -/

/-- Angluin's finite tell-tale condition for index `i`.

The final two inclusions say exactly that no family member containing `T` is a
proper subset of `C i`: if `T ⊆ C j ⊆ C i`, then `C i ⊆ C j`, hence equality.
The definition is index-sensitive and therefore allows repeated languages. -/
def IsTellTale
    (C : Generic.LanguageFamily α) (i : ℕ) (T : Finset α) : Prop :=
  (↑T : Set α) ⊆ C i ∧
    ∀ j, (↑T : Set α) ⊆ C j → C j ⊆ C i → C i ⊆ C j

theorem IsTellTale.eq_of_between
    {C : Generic.LanguageFamily α} {i j : ℕ} {T : Finset α}
    (hT : IsTellTale C i T)
    (hTj : (↑T : Set α) ⊆ C j) (hji : C j ⊆ C i) :
    C j = C i := by
  exact Set.Subset.antisymm hji (hT.2 j hTj hji)

/-- Condition 2 of the source: a finite tell-tale merely exists for each
indexed language.  Angluin proves this is necessary (Corollary 1), but Theorem
2 shows it is not sufficient for *effective* inference. -/
def ConditionTwo (C : Generic.LanguageFamily α) : Prop :=
  ∀ i, ∃ T : Finset α, IsTellTale C i T

/-! ## Finite-stage approximations used by the proof of sufficiency -/

/-- A finite-stage approximation to uniformly enumerated tell-tales.

`A i n` is the content emitted for index `i` by stage `n`.  Monotonicity and
eventual equality to a finite tell-tale are precisely the semantic facts about
the enumeration used in the sufficiency proof of Theorem 1. -/
def IsTellTaleApproximation
    (C : Generic.LanguageFamily α) (A : ℕ → ℕ → Finset α) : Prop :=
  (∀ i n m, n ≤ m → A i n ⊆ A i m) ∧
    ∀ i, ∃ T : Finset α, IsTellTale C i T ∧
      ∃ N, ∀ n, N ≤ n → A i n = T

theorem IsTellTaleApproximation.conditionTwo
    {C : Generic.LanguageFamily α} {A : ℕ → ℕ → Finset α}
    (hA : IsTellTaleApproximation C A) : ConditionTwo C := by
  intro i
  obtain ⟨T, hT, -⟩ := hA.2 i
  exact ⟨T, hT⟩

/-! ## Exact effective statement of the source hypotheses -/

/-- An indexed family of recursive languages in the source sense: membership
is decided uniformly and computably from the index and encoded word. -/
structure EffectiveIndexedFamily where
  /-- The indexed languages. -/
  language : Generic.LanguageFamily ℕ
  /-- A total Boolean membership decider, uniform in both arguments. -/
  membership : ℕ → ℕ → Bool
  /-- Correctness of the decider. -/
  membership_spec : ∀ i x, membership i x = true ↔ x ∈ language i
  /-- Recursiveness, not merely the existence of a Lean function. -/
  membership_computable : Computable₂ membership
  /-- Angluin's paper excludes the empty language. -/
  nonempty : AllNonempty language

/-- An effective identifier is represented on encoded finite histories by a
total computable function on lists. -/
abbrev EffectiveIdentifier := List ℕ → ℕ

/-- The first `t` values of a stream as a list, in chronological order. -/
def streamPrefix (stream : Stream α) (t : ℕ) : List α :=
  List.ofFn (fun i : Fin t => stream i)

/-- Syntactic convergence for the list-based effective interface. -/
def EffectiveConvergesTo
    (M : EffectiveIdentifier) (stream : Stream ℕ) (j : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t → M (streamPrefix stream t) = j

/-- The left side of Angluin's Theorem 1, including effectivity of the
inference machine. -/
def EffectiveInferrable (F : EffectiveIndexedFamily) : Prop :=
  ∃ M : EffectiveIdentifier, Computable M ∧
    ∀ z, ∀ stream : Stream ℕ, Generic.Presents stream (F.language z) →
      ∃ j, F.language j = F.language z ∧
        EffectiveConvergesTo M stream j

/-- The set enumerated for index `i` by a stage-by-stage output procedure. -/
def enumeratedSet
    (emit : ℕ → ℕ → Option ℕ) (i : ℕ) : Set ℕ :=
  {x | ∃ stage, emit i stage = some x}

/-- Set-valued form of the tell-tale property, convenient for a procedure
whose finite output set is not supplied with a halting certificate. -/
def IsEnumeratedTellTale
    (C : Generic.LanguageFamily ℕ) (i : ℕ) (T : Set ℕ) : Prop :=
  T.Finite ∧ T ⊆ C i ∧
    ∀ j, T ⊆ C j → C j ⊆ C i → C i ⊆ C j

/-- Condition 1 on p. 121 of Angluin (1980): one computable procedure,
uniform in `i`, enumerates a finite tell-tale for `C i`.

The procedure is represented by a total stage function which either emits one
word or emits nothing at a stage.  This is extensionally equivalent to the
paper's ordinary effective enumeration convention. -/
def ConditionOne (F : EffectiveIndexedFamily) : Prop :=
  ∃ emit : ℕ → ℕ → Option ℕ, Computable₂ emit ∧
    ∀ i, IsEnumeratedTellTale F.language i (enumeratedSet emit i)

/-! ## Source theorem statements

The following declarations pin the exact propositions asserted in the source.
They are definitions of statements, not proofs; completed proof components live
in the other files in this directory.  This naming prevents the semantic lemmas
from being mistaken for the full effective characterization.
-/

/-- The exact effective biconditional asserted by Theorem 1. -/
def TheoremOneStatement (F : EffectiveIndexedFamily) : Prop :=
  EffectiveInferrable F ↔ ConditionOne F

/-- Corollary 1: effective positive-data inference implies existence of a
finite tell-tale for every indexed language. -/
def CorollaryOneStatement (F : EffectiveIndexedFamily) : Prop :=
  EffectiveInferrable F → ConditionTwo F.language

/-- Theorem 2: the non-effective existence condition is not sufficient for
effective positive-data inference. -/
def TheoremTwoStatement : Prop :=
  ∃ F : EffectiveIndexedFamily,
    ConditionTwo F.language ∧ ¬EffectiveInferrable F

end GenLimit.Angluin
