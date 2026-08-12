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
