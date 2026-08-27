import GenLimit.Core.GenericGeneration

/-!
# Finite tell-tales for set-valued classes

This file contains the paper-independent finite positive witness used by both
Gold-style identification and the full-enumeration topology. The class is a
set of languages rather than an indexed family, so repetitions and index
choices play no role here.
-/

namespace GenLimit.Generic

/-- `T` is a finite tell-tale for `L` relative to `H` when it is contained in
`L` and every member of `H` between `T` and `L` is equal to `L`.

Membership of `L` in `H` is deliberately not part of the predicate. This
keeps the definition useful for statements whose target-membership assumption
is supplied separately, while class points can simply pass their membership
proof to the second conjunct. -/
def IsFiniteTellTale
    (H : LanguageClass α) (L : Language α) (T : Finset α) : Prop :=
  (↑T : Set α) ⊆ L ∧
    ∀ K, K ∈ H → (↑T : Set α) ⊆ K → K ⊆ L → K = L

/-- A tell-tale identifies any class member lying between its finite sample
and its target. -/
theorem IsFiniteTellTale.eq_of_between
    {H : LanguageClass α} {L K : Language α} {T : Finset α}
    (hT : IsFiniteTellTale H L T)
    (hKH : K ∈ H) (hTK : (↑T : Set α) ⊆ K) (hKL : K ⊆ L) :
    K = L :=
  hT.2 K hKH hTK hKL

end GenLimit.Generic
