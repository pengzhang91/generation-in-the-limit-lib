import GenLimit.Paper15_PartialEnumeration.FullTopology

/-!
# Separation hierarchy for the full-enumeration topology

Section 4.1 of Kleinberg--Wei records the standard implication chain

`T₁ → T_D → T₀`.

This file checks that chain for the paper's full-enumeration topology using
the source-oriented specialization preorder and the existing local
characterization of `T_D`.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration
namespace FullTopology

/-- `T₀` in specialization-preorder form. -/
def TZeroSpace (X : Set Language) : Prop :=
  ∀ K L : Point X, Specializes K L → Specializes L K → K = L

/-- The first implication in the Section 4.1 separation hierarchy:
`T₁ → T_D`. -/
theorem tOneSpace_implies_tdSpace
    {X : Set Language} (hX : TOneSpace X) :
    TDSpace X := by
  intro K
  refine ⟨Set.univ, fullOpen_univ X, Set.mem_univ K, ?_⟩
  intro L _ hLK
  exact hX L K (specializes_iff_subset.mpr hLK)

/-- The second implication in the Section 4.1 separation hierarchy:
`T_D → T₀`. -/
theorem tdSpace_implies_tZeroSpace
    {X : Set Language} (hX : TDSpace X) :
    TZeroSpace X := by
  intro K L hKL hLK
  obtain ⟨O, hO, hKO, hsep⟩ := hX K
  have hLO : L ∈ O := hKL O hO hKO
  exact (hsep L hLO (specializes_iff_subset.mp hLK)).symm

/-- The implication hierarchy displayed after Theorem 4.9. -/
theorem separation_hierarchy (X : Set Language) :
    (TOneSpace X → TDSpace X) ∧
      (TDSpace X → TZeroSpace X) :=
  ⟨tOneSpace_implies_tdSpace, tdSpace_implies_tZeroSpace⟩

end FullTopology
end PartialEnumeration
end KleinbergWei
end GenLimit
