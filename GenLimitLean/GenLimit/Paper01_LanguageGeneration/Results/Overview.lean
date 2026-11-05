import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Main
import GenLimit.Paper01_LanguageGeneration.FiniteFamily
import GenLimit.Paper01_LanguageGeneration.Prompted.Strings

/-!
# #01 Language Generation: main results

One statement for each NeurIPS 2024 headline theorem:

* Theorem 2.1: generation in the limit over `ℕ`.
* Theorem 2.2: uniform finite-family generation from one fixed sample over `ℕ`.
* Theorem 7.1: generation extending robust string prompts.

The proofs use finite membership queries. General-universe and countable
variants are exposed separately in `Results/Transport.lean`; the semantic
and observed-set constructions remain available through the paper umbrella.
-/

namespace GenLimit.KM.Results

/-- NeurIPS Theorem 2.1 over the implementation universe `ℕ`. -/
theorem theorem_2_1
    (O : GenLimit.OracleFamily)
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : GenLimit.Presents stream (O.language z)) :
    O.GeneratesInLimit stream z :=
  O.kleinbergMullainathan_main hP

/-- NeurIPS Theorem 2.2 over the implementation universe `ℕ`. -/
theorem theorem_2_2
    (O : GenLimit.OracleFamily) (members : Finset ℕ) :
    ∃ tC : ℕ, ∀ (S : Finset ℕ), tC ≤ S.card →
      ∀ z ∈ members, (↑S : Set ℕ) ⊆ O.language z →
        ∃ hInfinite :
            (GenLimit.KM.FiniteFamily.acceptedSet O members S).Infinite,
          GenLimit.KM.FiniteFamily.ProducesFromSample O S z
            (GenLimit.KM.FiniteFamily.enumerateAccepted
              O members S hInfinite) :=
  GenLimit.KM.FiniteFamily.theorem_2_2 O members

/-- NeurIPS Theorem 7.1: eventual fresh target strings extending each robust
prompt, via the finite-membership-query algorithm of Appendix A.5. -/
theorem theorem_7_1 {A : Type*} [DecidableEq A]
    (e : List A ≃ ℕ) (O : GenLimit.KM.Transport.IndexedOracleFamily (List A))
    {stream : ℕ → List A} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (O.language z))
    (prompts : ℕ → List A)
    (hrob : ∀ t, GenLimit.KM.Prompted.RobustPrompt O (prompts t)) :
    GenLimit.KM.Prompted.GeneratesInLimit e O stream prompts hrob z :=
  GenLimit.KM.Prompted.theorem_7_1 e O hP prompts hrob

end GenLimit.KM.Results
