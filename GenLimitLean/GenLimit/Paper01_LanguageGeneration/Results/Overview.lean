import GenLimit.Paper01_LanguageGeneration.Semantic
import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Main
import GenLimit.Paper01_LanguageGeneration.SetInterface
import GenLimit.Paper01_LanguageGeneration.Transport

/-!
# #01 Language Generation: main results

This facade exposes the two NeurIPS numbered results through source-facing
names without duplicating their proofs.

* Theorem 2.1 is complete as a concrete finite-membership-query algorithm over
  `ℕ`, with explicit-equivalence and classical countable-universe transports.
* Theorem 2.2 is complete as a fixed-sample finite-family oracle scan whose
  output is an infinite pairwise-distinct sequence in the target minus the
  sample, again with explicit and classical transports.
* Theorem 7.1, the robust-prompt extension, remains open.

The separate Section 4 semantic and observed-set interfaces remain available
from their canonical modules and through the paper umbrella.
-/

namespace GenLimit.KM.Results

/-- NeurIPS Theorem 2.1 over the implementation universe `ℕ`. -/
theorem theorem_2_1
    (O : GenLimit.OracleFamily)
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : GenLimit.Presents stream (O.language z)) :
    O.GeneratesInLimit stream z :=
  O.kleinbergMullainathan_main hP

/-- NeurIPS Theorem 2.1 transported along an explicit universe coding. -/
theorem theorem_2_1_of_equiv
    (e : α ≃ ℕ) (O : GenLimit.KM.Transport.IndexedOracleFamily α)
    {stream : GenLimit.Generic.Stream α} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (O.language z)) :
    GenLimit.KM.Transport.GeneratesInLimit e O stream z :=
  GenLimit.KM.Transport.kleinbergMullainathan_main_of_equiv e O hP

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

/-- NeurIPS Theorem 2.2 transported along an explicit universe coding. -/
theorem theorem_2_2_of_equiv
    (e : α ≃ ℕ) (O : GenLimit.KM.Transport.IndexedOracleFamily α)
    (members : Finset ℕ) :
    ∃ tC : ℕ, ∀ (S : Finset α), tC ≤ S.card →
      ∀ z ∈ members, (↑S : Set α) ⊆ O.language z →
        ∃ hInfinite :
            (GenLimit.KM.FiniteFamily.acceptedSet
              (GenLimit.KM.Transport.encodeFamily e O) members
              (GenLimit.KM.Transport.FiniteFamily.encodeSample e S)).Infinite,
          GenLimit.KM.Transport.FiniteFamily.ProducesFromSample O S z
            (GenLimit.KM.Transport.FiniteFamily.outputOfEquiv
              e O members S hInfinite) :=
  GenLimit.KM.Transport.FiniteFamily.theorem_2_2_of_equiv e O members

end GenLimit.KM.Results
