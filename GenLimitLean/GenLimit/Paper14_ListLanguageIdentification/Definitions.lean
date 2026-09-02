import GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions

/-!
# List identification in the limit

Definitions 1 and 2 of Charikar--Pabbaraju--Tewari,
*A Characterization of List Language Identification in the Limit*,
arXiv:2511.04103v1.

The family remains indexed and guesses are indices.  Correctness is
extensional in the denoted language, as required by the source's relation
`L ∈id μ`; this matters when several indices denote the same language.
-/

namespace GenLimit.ListIdentification

/-- Definition 1: a `k`-list identifier outputs exactly `k` index slots.
Algorithms returning fewer indices can be padded without changing
correctness. -/
abbrev ListIdentifier (α : Type*) (k : ℕ) :=
  ∀ t : ℕ, (Fin t → α) → (Fin k → ℕ)

/-- Run a list identifier on the prefix strictly before time `t`. -/
def listOutput
    (A : ListIdentifier α k)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Fin k → ℕ :=
  A t (fun i => stream i)

/-- The paper's relation `L_z ∈id μ`: one guessed index denotes the target
language extensionally. -/
def TargetInGuess
    (F : GenLimit.Generic.LanguageFamily α) (z : ℕ)
    (μ : Fin k → ℕ) : Prop :=
  ∃ r : Fin k, F (μ r) = F z

/-- Definition 2 on one target presentation. -/
def IdentifiesFrom
    (A : ListIdentifier α k)
    (F : GenLimit.Generic.LanguageFamily α)
    (z : ℕ) (stream : GenLimit.Generic.Stream α) : Prop :=
  ∃ T, ∀ t, T ≤ t → TargetInGuess F z (listOutput A stream t)

/-- Definition 2: eventual list identification on every exact positive-data
presentation of every indexed target. -/
def ListIdentifies
    (A : ListIdentifier α k)
    (F : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream (F z) →
      IdentifiesFrom A F z stream

/-- The collection is `k`-list identifiable in the limit. -/
def ListIdentifiable
    (F : GenLimit.Generic.LanguageFamily α) (k : ℕ) : Prop :=
  ∃ A : ListIdentifier α k, ListIdentifies A F

/-- A list-valued implementation may output at most `k` entries before being
padded to Definition 1's fixed-width output. -/
abbrev BoundedListIdentifier (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → List ℕ

/-- Length invariant for a list-valued implementation. -/
def HasListBound
    (A : BoundedListIdentifier α) (k : ℕ) : Prop :=
  ∀ t xs, (A t xs).length ≤ k

/-- Extensional correctness for a variable-length list of indices. -/
def TargetInIndexList
    (F : GenLimit.Generic.LanguageFamily α) (z : ℕ)
    (μ : List ℕ) : Prop :=
  ∃ i ∈ μ, F i = F z

end GenLimit.ListIdentification
