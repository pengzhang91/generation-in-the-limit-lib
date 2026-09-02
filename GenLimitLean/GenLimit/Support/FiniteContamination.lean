import GenLimit.Core.FiniteContamination

/-!
# Finite contamination compatibility names

The canonical paper-independent predicates now live in
`GenLimit.Core.FiniteContamination`.  These aliases preserve the former
`GenLimit.Support` API for downstream developments.
-/

namespace GenLimit.Support

/-- `A` has at most `n` elements outside `B`.  The finite witness exposes the
exception set used by constructions that must enumerate those elements. -/
abbrev MissingAtMost (A B : Set α) (n : ℕ) : Prop :=
  GenLimit.Generic.SetDifferenceAtMost A B n

theorem missingAtMost_mono
    {A B : Set α} {i j : ℕ} (hij : i ≤ j)
    (h : MissingAtMost A B i) :
    MissingAtMost A B j :=
  GenLimit.Generic.setDifferenceAtMost_mono hij h

theorem missingAtMost_zero_iff_subset
    (A B : Set α) :
    MissingAtMost A B 0 ↔ A ⊆ B :=
  GenLimit.Generic.setDifferenceAtMost_zero_iff_subset A B

/-- An injective enumeration that covers `L` and contains at most `n`
distinct values outside `L`. -/
abbrev EnumerationWithNoiseAtMost
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) : Prop :=
  GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost stream L n

theorem enumerationWithNoiseAtMost_mono
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {i j : ℕ}
    (hij : i ≤ j) (h : EnumerationWithNoiseAtMost stream L i) :
    EnumerationWithNoiseAtMost stream L j :=
  GenLimit.Generic.injectiveValueContaminatedPresentationAtMost_mono hij h

end GenLimit.Support
