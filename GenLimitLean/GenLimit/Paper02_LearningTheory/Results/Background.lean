import GenLimit.Paper02_LearningTheory.Introductory
import GenLimit.Bridges.GoldToPaper02
import GenLimit.Bridges.AngluinToPaper02

/-!
# #02 Learning Theory: background restatements

Section 2.5 of arXiv:2410.13714v5 restates earlier results under the source
numbers 2.2--2.5. Theorem 2.2 is attributed to Gold (1967) and Angluin
(1979, 1980); Theorem 2.3 to Angluin (1980), Theorem 1; and Theorems 2.4
and 2.5 to Kleinberg--Mullainathan (2024). These are background results,
separate from P02's new main results in `Results.Overview`.

Every wrapper delegates to an existing theorem. The identification results
reuse the Gold/Angluin bridges. The generation results retain their short
native P02 derivations, while their attribution records KM's earlier results.

Theorem 2.2 uses the existing stronger UUS witness on `ℕ`; it does not assert
a false separation on every finite universe. Theorem 2.3 restores the
countability of the language class required by the semantic identifier
interface. The printed arbitrary-class version remains refuted separately.

This facade is available through `GenLimit.Bridges` and `GenLimit`, or by
explicit import. It is deliberately outside the independent P02 umbrella:
its Gold bridge imports that umbrella, so importing it back would create a
cycle. The public names `Results.theorem_2_4` and `Results.theorem_2_5` retain
their statements. Moving them here does not extend any human-audit scope.
-/

namespace GenLimit.LiRamanTewari.Results

/-- P02 Theorem 2.2, restating Gold/Angluin: a countable class of infinite
languages over `ℕ` need not be identifiable from positive text. -/
theorem theorem_2_2 :
    ∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ GenLimit.Generic.UUS H ∧
        ¬GenLimit.Angluin.ExtensionallyIdentifiable H :=
  GenLimit.GoldP02Separation.theorem_2_2_countable_uus_not_identifiable

/-- P02 Theorem 2.3, restating Angluin's tell-tale characterization with the
countable-class hypothesis restored. -/
theorem theorem_2_3_countable
    {α : Type*} [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hCountable : H.Countable) :
    GenLimit.Angluin.ExtensionallyIdentifiable H ↔
      GenLimit.Angluin.ExtensionalTellTaleCondition H :=
  GenLimit.Angluin.theorem_2_3_countable hCountable

/-- P02 Theorem 2.4, restating Kleinberg--Mullainathan (2024): every
countable UUS class is generatable in the limit. The native P02 proof passes
through its stronger nonuniform-generation result. -/
theorem theorem_2_4
    {α : Type*} [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : UUS H) (hCountable : H.Countable) :
    GeneratableInLimit H :=
  GenLimit.LiRamanTewari.theorem_2_4 hUUS hCountable

/-- P02 Theorem 2.5, restating Kleinberg--Mullainathan (2024): every finite
UUS class is uniformly generatable. The native P02 proof uses its closure
characterization. -/
theorem theorem_2_5
    {α : Type*} [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : UUS H) (hFinite : H.Finite) :
    UniformlyGeneratable H :=
  GenLimit.LiRamanTewari.theorem_2_5 hUUS hFinite

end GenLimit.LiRamanTewari.Results
