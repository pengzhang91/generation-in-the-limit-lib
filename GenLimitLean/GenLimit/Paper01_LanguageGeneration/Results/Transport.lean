import GenLimit.Paper01_LanguageGeneration.Transport
import GenLimit.Paper01_LanguageGeneration.Prompted.Universe

/-!
# #01 Language Generation: universe transport wrappers

Additional universe-coding and countability interfaces for the three main
results. `Overview.lean` contains one statement per headline theorem. These
wrappers retain their public declaration names and theorem statements when
moved out of the overview, including the reviewed Theorems 2.1/2.2 interfaces.
-/

namespace GenLimit.KM.Results

/-- NeurIPS Theorem 2.1 transported along an explicit universe coding. -/
theorem theorem_2_1_of_equiv
    (e : α ≃ ℕ) (O : GenLimit.KM.Transport.IndexedOracleFamily α)
    {stream : GenLimit.Generic.Stream α} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (O.language z)) :
    GenLimit.KM.Transport.GeneratesInLimit e O stream z :=
  GenLimit.KM.Transport.kleinbergMullainathan_main_of_equiv e O hP

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

/-- Abstract countable-alphabet Theorem 7.1; the universe coding is chosen
classically, while the preceding interface accepts an explicit coding. -/
theorem theorem_7_1_countable {A : Type*} [DecidableEq A] [Countable A]
    (O : GenLimit.KM.Transport.IndexedOracleFamily (List A))
    {stream : ℕ → List A} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (O.language z))
    (prompts : ℕ → List A)
    (hrob : ∀ t, GenLimit.KM.Prompted.RobustPrompt O (prompts t)) :
    GenLimit.KM.Prompted.GeneratesInLimit
      (GenLimit.KM.Transport.countableEquivNat O) O stream prompts hrob z :=
  GenLimit.KM.Prompted.theorem_7_1_countable O hP prompts hrob

/-- Theorem 7.1 in a supplied enumerable string universe, which may be a
proper subset of all words. Its threshold is uniform over robust prompts. -/
theorem theorem_7_1_in_universe {A U : Type*} [DecidableEq A] [DecidableEq U]
    (word : U → List A) (e : U ≃ ℕ) (O : GenLimit.KM.Transport.IndexedOracleFamily U)
    {stream : ℕ → U} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (O.language z)) :
    ∃ T, ∀ (prompts : ℕ → List A)
      (hrob : ∀ t, GenLimit.KM.Prompted.RobustPromptIn word O (prompts t)),
      ∀ t, T ≤ t →
        prompts t <+: word (GenLimit.KM.Prompted.generatorIn word e O stream prompts hrob t) ∧
        GenLimit.KM.Prompted.generatorIn word e O stream prompts hrob t ∈ O.language z ∧
        GenLimit.KM.Prompted.generatorIn word e O stream prompts hrob t ∉
          GenLimit.Generic.sample stream t :=
  GenLimit.KM.Prompted.theorem_7_1_in_universe word e O hP

end GenLimit.KM.Results
