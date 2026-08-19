import GenLimit.Support.Presentations
import GenLimit.Core.ClassGeneration

/-!
# Presentation semantics for union-closedness

The paper states its lower bounds for duplicate-free exact enumerations.  The
shared library notion `GenLimit.Generic.IsLimitGenerator` is intentionally
stronger: it quantifies over all exact presentations, including presentations
with repetitions.  This module isolates the paper-specific convention and the
one-way bridge between the two semantics.

These definitions remain local to this paper development.  They should move to
`GenLimit.Core` only if a second independent development needs the same
duplicate-free presentation API.
-/

namespace GenLimit.UnionClosedness

open GenLimit.Generic

/-- Packaged form of the source's duplicate-free exact-presentation
assumption.  The public generator predicate below keeps its original curried
arguments for compatibility, while this alias records the shared Support
concept used by Paper12. -/
abbrev InjectivePresentation
    (stream : Stream α) (L : Language α) : Prop :=
  GenLimit.Support.InjectivePresentation stream L

/-- A generator succeeds on every duplicate-free exact presentation of every
language in `H`. -/
def IsLimitGeneratorOnInjectivePresentations
    (G : Generator α) (H : LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∀ stream : Stream α,
    Function.Injective stream →
    Presents stream L →
    ∃ T, ∀ t, T ≤ t → CorrectAt G L stream t

/-- Generation in the limit under the paper's duplicate-free presentation
convention. -/
def GeneratableInLimitOnInjectivePresentations
    (H : LanguageClass α) : Prop :=
  ∃ G : Generator α, IsLimitGeneratorOnInjectivePresentations G H

/-- Success on all exact presentations implies success on duplicate-free exact
presentations. -/
theorem isLimitGeneratorOnInjectivePresentations_of_isLimitGenerator
    {G : Generator α} {H : LanguageClass α}
    (hG : GenLimit.Generic.IsLimitGenerator G H) :
    IsLimitGeneratorOnInjectivePresentations G H := by
  intro L hL stream _hinjective hpresents
  exact hG L hL stream hpresents

/-- A lower bound proved for duplicate-free presentations also gives a lower
bound for the library's stronger all-presentations semantics. -/
theorem not_generatableInLimit_of_not_generatableOnInjectivePresentations
    {H : LanguageClass α}
    (h : ¬GeneratableInLimitOnInjectivePresentations H) :
    ¬GenLimit.Generic.GeneratableInLimit H := by
  rintro ⟨G, hG⟩
  exact h ⟨G,
    isLimitGeneratorOnInjectivePresentations_of_isLimitGenerator hG⟩

end GenLimit.UnionClosedness
