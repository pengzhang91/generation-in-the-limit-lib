import GenLimit.LiRamanTewari.Definitions

/-!
# The LRT quantifier hierarchy

Source-facing wrappers for the paper-independent implication chain
`uniform ⇒ non-uniform ⇒ generation in the limit`.
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
