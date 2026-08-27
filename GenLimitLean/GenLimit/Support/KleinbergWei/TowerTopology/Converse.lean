import GenLimit.Support.KleinbergWei.TowerTopology

/-!
# Extracting convergent towers from limit points

The choice-based converse selects the nth approximant from the neighborhood
fixed by the first n+1 elements of a presentation of the terminal language.
-/

namespace GenLimit.KleinbergWei.TowerTopology

/-- `K` is approached through `Y` in every basic neighborhood. -/
def ApproachedFrom
    {X : Set Language} (Y : Set (Point X)) (K : Point X) : Prop :=
  ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ K.1 →
    ∃ L : Point X,
      L ∈ Y ∧ L ≠ K ∧ L ∈ basicNeighborhood X K F

/-- An approximant through `Y`, selected from the neighborhood fixed by the
first `n + 1` presentation points. -/
noncomputable def relativeApproximant
    {X : Set Language} (Y : Set (Point X)) (K : Point X)
    (hK : ApproachedFrom Y K)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1)
    (n : ℕ) : Point X := by
  have hsample : (↑(sample enumeration (n + 1)) : Set ℕ) ⊆ K.1 := by
    intro u hu
    exact mem_language_of_mem_sample_of_presents hP hu
  exact Classical.choose (hK (sample enumeration (n + 1)) hsample)

theorem relativeApproximant_spec
    {X : Set Language} (Y : Set (Point X)) (K : Point X)
    (hK : ApproachedFrom Y K)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1)
    (n : ℕ) :
    relativeApproximant Y K hK enumeration hP n ∈ Y ∧
      relativeApproximant Y K hK enumeration hP n ≠ K ∧
      relativeApproximant Y K hK enumeration hP n ∈
        basicNeighborhood X K (sample enumeration (n + 1)) := by
  have hsample : (↑(sample enumeration (n + 1)) : Set ℕ) ⊆ K.1 := by
    intro u hu
    exact mem_language_of_mem_sample_of_presents hP hu
  simpa only [relativeApproximant] using
    Classical.choose_spec (hK (sample enumeration (n + 1)) hsample)

theorem relativeApproximants_converge
    {X : Set Language} (Y : Set (Point X)) (K : Point X)
    (hK : ApproachedFrom Y K)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1) :
    ConvergentProperTower X
      (fun n => relativeApproximant Y K hK enumeration hP n) K := by
  refine ⟨?_, ?_⟩
  · intro n
    have hs := relativeApproximant_spec Y K hK enumeration hP n
    exact Set.ssubset_iff_subset_ne.mpr
      ⟨hs.2.2.2, fun heq => hs.2.1 (Subtype.ext heq)⟩
  · intro u hu
    rw [← hP] at hu
    obtain ⟨s, rfl⟩ := hu
    refine ⟨s, ?_⟩
    intro n hsn
    exact (relativeApproximant_spec Y K hK enumeration hP n).2.2.1
      (value_mem_sample (by omega))

/-- A basis limit point is approached through the ambient point space. -/
theorem approachedFrom_univ_of_basisLimitPoint
    {X : Set Language} {K : Point X} (hK : BasisLimitPoint K) :
    ApproachedFrom Set.univ K := by
  intro F hF
  obtain ⟨L, hne, hLF⟩ := hK F hF
  exact ⟨L, Set.mem_univ L, hne, hLF⟩

noncomputable def approximant
    {X : Set Language} (K : Point X) (hK : BasisLimitPoint K)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1)
    (n : ℕ) : Point X :=
  relativeApproximant Set.univ K
    (approachedFrom_univ_of_basisLimitPoint hK) enumeration hP n

theorem approximant_spec
    {X : Set Language} (K : Point X) (hK : BasisLimitPoint K)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1)
    (n : ℕ) :
    approximant K hK enumeration hP n ≠ K ∧
      approximant K hK enumeration hP n ∈
        basicNeighborhood X K (sample enumeration (n + 1)) := by
  have hs := relativeApproximant_spec Set.univ K
    (approachedFrom_univ_of_basisLimitPoint hK) enumeration hP n
  simpa only [approximant] using hs.2

theorem approximants_converge
    {X : Set Language} (K : Point X) (hK : BasisLimitPoint K)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1) :
    ConvergentProperTower X
      (fun n => approximant K hK enumeration hP n) K := by
  simpa only [approximant] using
    relativeApproximants_converge Set.univ K
      (approachedFrom_univ_of_basisLimitPoint hK) enumeration hP

/-- Limit-point characterization at the convergence-core level. -/
theorem basisLimitPoint_iff_exists_convergentProperTower
    {X : Set Language} {K : Point X}
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1) :
    BasisLimitPoint K ↔
      ∃ tower : ℕ → Point X, ConvergentProperTower X tower K := by
  constructor
  · intro hK
    exact ⟨fun n => approximant K hK enumeration hP n,
      approximants_converge K hK enumeration hP⟩
  · rintro ⟨tower, htower⟩
    exact basisLimitPoint_of_convergentProperTower htower

theorem isLimitPoint_iff_exists_convergentProperTower
    {X : Set Language} {K : Point X}
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1) :
    IsLimitPoint K ↔
      ∃ tower : ℕ → Point X, ConvergentProperTower X tower K := by
  rw [← basisLimitPoint_iff_isLimitPoint]
  exact basisLimitPoint_iff_exists_convergentProperTower enumeration hP

end GenLimit.KleinbergWei.TowerTopology
