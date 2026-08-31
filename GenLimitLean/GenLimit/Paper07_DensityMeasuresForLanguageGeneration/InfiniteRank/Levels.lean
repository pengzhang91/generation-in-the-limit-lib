import Mathlib.Order.Extension.Linear
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Data.Set.Countable
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.ParentForest

/-!
# Rational inclusion levels for the infinite-rank construction

The family of indexed languages is countable.  Extending strict inclusion to
a countable linear order and embedding that order into `ℚ` supplies the level
map used in the infinite-rank argument of Kleinberg--Wei Theorem 6.12.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank

open FiniteRankParent

noncomputable section

variable (C : LanguageFamily)

private noncomputable def familyPointCountable :
    Countable (FamilyPoint C) :=
  (Set.countable_range C).to_subtype

private noncomputable def linearExtensionCountable :
    Countable (LinearExtension (FamilyPoint C)) :=
  letI : Countable (FamilyPoint C) := familyPointCountable C
  Function.Injective.countable
    (f := fun x : LinearExtension (FamilyPoint C) =>
      (show FamilyPoint C from x))
    (fun _ _ h => h)

/-- Rational levels obtained by extending inclusion to a linear order and
embedding the resulting countable linear order into the rationals. -/
noncomputable def rationalInclusionLevel (L : FamilyPoint C) : ℚ := by
  letI : Countable (FamilyPoint C) := familyPointCountable C
  letI : Countable (LinearExtension (FamilyPoint C)) :=
    linearExtensionCountable C
  exact
    (Order.embedding_from_countable_to_dense
      (α := LinearExtension (FamilyPoint C)) (β := ℚ)).some
      (toLinearExtension L)

theorem rationalInclusionLevel_strictMono :
    StrictMono (rationalInclusionLevel C) := by
  letI : Countable (FamilyPoint C) := familyPointCountable C
  letI : Countable (LinearExtension (FamilyPoint C)) :=
    linearExtensionCountable C
  intro L M hLM
  exact
    (Order.embedding_from_countable_to_dense
      (α := LinearExtension (FamilyPoint C)) (β := ℚ)).some.strictMono
      ((Monotone.strictMono_of_injective
        (toLinearExtension :
          FamilyPoint C →o LinearExtension (FamilyPoint C)).monotone
          (fun _ _ h => h)) hLM)

/-- Existence form matching the level-map premise used in Theorem 6.12. -/
theorem exists_strictMono_rationalInclusionLevel :
    ∃ level : FamilyPoint C → ℚ, StrictMono level :=
  ⟨rationalInclusionLevel C, rationalInclusionLevel_strictMono C⟩

theorem rationalInclusionLevel_lt_of_ssubset
    {L M : FamilyPoint C} (hLM : L.1 ⊂ M.1) :
    rationalInclusionLevel C L < rationalInclusionLevel C M := by
  apply rationalInclusionLevel_strictMono C
  exact hLM

/-- The same level map, expressed on family indices. Duplicate indices
representing the same language intentionally receive the same level. -/
noncomputable def rationalFamilyLevel (n : ℕ) : ℚ :=
  rationalInclusionLevel C (familyPoint C n)

theorem rationalFamilyLevel_lt_of_ssubset
    {i j : ℕ} (hij : C i ⊂ C j) :
    rationalFamilyLevel C i < rationalFamilyLevel C j :=
  rationalInclusionLevel_lt_of_ssubset C hij

end

end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
