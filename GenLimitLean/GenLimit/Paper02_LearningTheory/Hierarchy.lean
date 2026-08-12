import GenLimit.Paper02_LearningTheory.Definitions

/-!
# The LRT quantifier hierarchy

Source-facing wrappers for the paper-independent implication chain
`uniform ⇒ non-uniform ⇒ generation in the limit`.  The chain is displayed
immediately before Proposition 2.1 in the source; Proposition 2.1 itself is
the strictness result and is packaged in the paper umbrella after importing
its two Section 3 witnesses.
-/

namespace GenLimit.LiRamanTewari

/-- Both implications in the generation hierarchy are strict on `α`:
there is a non-uniformly but not uniformly generatable class, and there is
a class generatable in the limit but not non-uniformly generatable. -/
def GenerationHierarchyStrictOn (α : Type*) : Prop :=
  (∃ H₁ : GenLimit.Generic.LanguageClass α,
    UUS H₁ ∧ NonuniformlyGeneratable H₁ ∧ ¬UniformlyGeneratable H₁) ∧
  (∃ H₂ : GenLimit.Generic.LanguageClass α,
    UUS H₂ ∧ GeneratableInLimit H₂ ∧ ¬NonuniformlyGeneratable H₂)

theorem uniform_implies_nonuniform
    {H : GenLimit.Generic.LanguageClass α} (h : UniformlyGeneratable H) :
    NonuniformlyGeneratable H :=
  GenLimit.Generic.uniform_implies_nonuniform h

theorem nonuniform_implies_limit
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (h : NonuniformlyGeneratable H) :
    GeneratableInLimit H :=
  GenLimit.Generic.nonuniform_implies_limit hUUS h

theorem uniform_implies_limit
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (h : UniformlyGeneratable H) :
    GeneratableInLimit H :=
  GenLimit.Generic.uniform_implies_limit hUUS h

end GenLimit.LiRamanTewari
