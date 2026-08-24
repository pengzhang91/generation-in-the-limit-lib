import GenLimit.Core.ClassGeneration
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.SignedIntegers

/-!
# Fresh one-sided sweep generators

The positive results in detailed Theorems 4.1 and 4.4 use the same simple
idea: at time `t`, emit the first point at or beyond index `t` that has not
appeared in the finite history.  This module packages the negative and
positive versions independently of any particular language class.
-/

namespace GenLimit.UnionClosedness

private theorem exists_fresh_negative_index {t : ℕ} (xs : Fin t → ℤ) :
    ∃ n : ℕ, t ≤ n ∧
      negativeCode n ∉ GenLimit.Generic.sequenceSample xs := by
  classical
  obtain ⟨z, hzTail, hzFresh⟩ :=
    ((negativeTail_infinite t).diff
      (GenLimit.Generic.sequenceSample xs).finite_toSet).nonempty
  obtain ⟨k, rfl⟩ := hzTail
  exact ⟨t + k, Nat.le_add_right t k, hzFresh⟩

/-- The first fresh negative index at least the current time. -/
noncomputable def firstFreshNegativeIndex {t : ℕ} (xs : Fin t → ℤ) : ℕ :=
  Nat.find (exists_fresh_negative_index xs)

/-- The descending fresh sweep `-1, -2, ...`, with the lower index bounded
by the current time. -/
noncomputable def descendingNegativeGenerator : GenLimit.Generic.Generator ℤ :=
  fun _t xs => negativeCode (firstFreshNegativeIndex xs)

theorem descendingNegativeGenerator_spec {t : ℕ} (xs : Fin t → ℤ) :
    ∃ n : ℕ,
      t ≤ n ∧
      descendingNegativeGenerator t xs = negativeCode n ∧
      descendingNegativeGenerator t xs ∉
        GenLimit.Generic.sequenceSample xs := by
  classical
  have hspec := Nat.find_spec (exists_fresh_negative_index xs)
  exact ⟨firstFreshNegativeIndex xs, hspec.1, rfl, hspec.2⟩

private theorem exists_fresh_positive_index {t : ℕ} (xs : Fin t → ℤ) :
    ∃ n : ℕ, t ≤ n ∧
      positiveCode n ∉ GenLimit.Generic.sequenceSample xs := by
  classical
  obtain ⟨z, hzTail, hzFresh⟩ :=
    ((positiveTail_infinite t).diff
      (GenLimit.Generic.sequenceSample xs).finite_toSet).nonempty
  obtain ⟨k, rfl⟩ := hzTail
  exact ⟨t + k, Nat.le_add_right t k, hzFresh⟩

/-- The first fresh positive index at least the current time. -/
noncomputable def firstFreshPositiveIndex {t : ℕ} (xs : Fin t → ℤ) : ℕ :=
  Nat.find (exists_fresh_positive_index xs)

/-- The ascending fresh sweep `1, 2, ...`, with the lower index bounded by
the current time. -/
noncomputable def ascendingPositiveGenerator : GenLimit.Generic.Generator ℤ :=
  fun _t xs => positiveCode (firstFreshPositiveIndex xs)

theorem ascendingPositiveGenerator_spec {t : ℕ} (xs : Fin t → ℤ) :
    ∃ n : ℕ,
      t ≤ n ∧
      ascendingPositiveGenerator t xs = positiveCode n ∧
      ascendingPositiveGenerator t xs ∉
        GenLimit.Generic.sequenceSample xs := by
  classical
  have hspec := Nat.find_spec (exists_fresh_positive_index xs)
  exact ⟨firstFreshPositiveIndex xs, hspec.1, rfl, hspec.2⟩

end GenLimit.UnionClosedness
