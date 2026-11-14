import GenLimit.Paper09_RepresentativeLanguageGeneration.GroupClosure
import GenLimit.Paper09_RepresentativeLanguageGeneration.NonuniformCharacterization
import GenLimit.Paper09_RepresentativeLanguageGeneration.ExactProfileSupport

/-!
# Main theorems of Representative Language Generation

This is the main-theorem overview for Peale--Raman--Reingold,
*Representative Language Generation* (ICML 2025 / PMLR 267).  It states
Theorem 3.3, a stronger form of Theorem 3.7, and the separately named
correction of Theorem 4.4, delegating their proofs to the canonical modules.

Theorem 4.4 is false as printed.  `corrected_theorem_4_4` uses finite exact
group-profile support in place of the printed positive-membership support.
It is a corrected result, not a formalization of the printed statement.

Supporting corollaries, lemmas, and counterexamples are collected separately
in `Results.Supporting` and remain available through the P09 umbrella.
-/

namespace GenLimit.RepresentativeGeneration.Published

/-- Published Theorem 3.3 (group-closure characterization). -/
theorem theorem_3_3
    [Nonempty α] [Countable α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ)
    (_hUUS : GenLimit.Generic.UUS H)
    (hpartition : IsCountablePartition groups)
    (halpha : 0 < alpha) :
    AlphaRepresentativeUniformlyGeneratable H groups alpha ↔
      HasFiniteGroupClosureDimension H groups alpha :=
  alphaRepresentativeUniformlyGeneratable_iff_finite_groupClosureDimension
    hpartition halpha

/-- Theorem 3.7 (non-uniform characterization), in a stronger form than the
published statement.

The paper assumes a countable domain, a class satisfying UUS, and a countable
partition of the domain.  The Lean proof does not need these assumptions:
`α` is arbitrary, `H` need not satisfy UUS, and `groups : ℕ → Set α` may
overlap or fail to cover `α`.  The equivalence and the order of quantifiers
are otherwise unchanged; the cover may depend on the positive tolerance. -/
theorem theorem_3_7
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} :
    RepresentativelyNonuniformlyGeneratable H groups ↔
      ∀ alpha : ℝ, 0 < alpha →
        ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
          GenLimit.Generic.IsNondecreasingCover H classes ∧
          ∀ n, AlphaRepresentativeUniformlyGeneratable
            (classes n) groups alpha :=
  representative_nonuniform_iff_uniform_nondecreasing_cover

/-- Corrected published Theorem 4.4, using finite exact-profile support. -/
theorem corrected_theorem_4_4
    [Nonempty α] [Countable α]
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α)
    (hHcountable : H.Countable)
    (hUUS : GenLimit.Generic.UUS H)
    (hcover : GroupsCover groups)
    (hsupport : HasFiniteExactProfileSupport H groups) :
    RepresentativelyGeneratableInLimit H groups :=
  GenLimit.RepresentativeGeneration.corrected_theorem_4_4
    H groups hHcountable hUUS hcover hsupport

end GenLimit.RepresentativeGeneration.Published
