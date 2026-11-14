import GenLimit.Core.CanonicalDensity
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

/-!
# Canonical orderings for the finite-expansion reduction

Paper 17 obtains every language ordering from the same ambient order. These
constructions implement that convention on natural-number strings and prove
the density equalities needed by Theorem 6.18.
-/

namespace GenLimit.InfiniteContamination

open GenLimit.KleinbergWei

/-- Give every language its increasing enumeration in the common ambient
natural-number order, as required by the paper's density convention. -/
noncomputable def canonicalFamilyOrders
    (O : GenLimit.OracleFamily) (i : ℕ) : OrderedLanguage :=
  OrderedLanguage.canonical (O.language i) (O.infinite' i)

@[simp] theorem canonicalFamilyOrders_carrier
    (O : GenLimit.OracleFamily) (i : ℕ) :
    (canonicalFamilyOrders O i).carrier = O.language i := rfl

theorem canonicalFamilyOrders_strictMono
    (O : GenLimit.OracleFamily) (i : ℕ) :
    StrictMono (canonicalFamilyOrders O i).enumeration :=
  OrderedLanguage.canonical_strictMono (O.language i) (O.infinite' i)

/-- A finite expansion and its base language give the same densities to
every set in their canonical orderings. This derives the measure compatibility
used in Theorem 6.18 instead of assuming it. -/
theorem finiteExpansion_canonical_density
    (O : GenLimit.OracleFamily) (j : ℕ) (A : Set ℕ) :
    (canonicalFamilyOrders (finiteExpansionOracleFamily O) j).lowerDensity A =
        (finiteExpansionMeasure (canonicalFamilyOrders O) j).lowerDensity A ∧
      (canonicalFamilyOrders (finiteExpansionOracleFamily O) j).upperDensity A =
        (finiteExpansionMeasure (canonicalFamilyOrders O) j).upperDensity A := by
  let data := finiteExpansionCode j
  have hdiff :
      (((finiteExpansionOracleFamily O).language j \
          O.language (finiteExpansionBaseIndex j)).Finite ∧
        (O.language (finiteExpansionBaseIndex j) \
          (finiteExpansionOracleFamily O).language j).Finite) := by
    exact finiteExpansion_symmetricDifference_finite
      (O.language data.1)
      (Finset.equivBitIndices data.2.1)
      (Finset.equivBitIndices data.2.2)
  constructor
  · exact OrderedLanguage.lowerDensity_eq_of_finite_carrier_difference
      (canonicalFamilyOrders (finiteExpansionOracleFamily O) j)
      (canonicalFamilyOrders O (finiteExpansionBaseIndex j))
      (canonicalFamilyOrders_strictMono (finiteExpansionOracleFamily O) j)
      (canonicalFamilyOrders_strictMono O (finiteExpansionBaseIndex j))
      hdiff.1 hdiff.2 A
  · exact OrderedLanguage.upperDensity_eq_of_finite_carrier_difference
      (canonicalFamilyOrders (finiteExpansionOracleFamily O) j)
      (canonicalFamilyOrders O (finiteExpansionBaseIndex j))
      (canonicalFamilyOrders_strictMono (finiteExpansionOracleFamily O) j)
      (canonicalFamilyOrders_strictMono O (finiteExpansionBaseIndex j))
      hdiff.1 hdiff.2 A

end GenLimit.InfiniteContamination
