import GenLimit.Support.KleinbergWei.TowerTopology

/-!
# Extracting convergent towers from limit points

The choice-based converse selects the nth approximant from the neighborhood
fixed by the first n+1 elements of a presentation of the terminal language.
-/

namespace GenLimit.KleinbergWei.TowerTopology

noncomputable def approximant
    {X : Set Language} (K : Point X) (hK : BasisLimitPoint K)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1)
    (n : ℕ) : Point X := by
  have hsample : (↑(sample enumeration (n + 1)) : Set ℕ) ⊆ K.1 := by
    intro u hu
    exact mem_language_of_mem_sample_of_presents hP hu
  exact Classical.choose (hK (sample enumeration (n + 1)) hsample)

theorem approximant_spec
    {X : Set Language} (K : Point X) (hK : BasisLimitPoint K)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1)
    (n : ℕ) :
    approximant K hK enumeration hP n ≠ K ∧
      approximant K hK enumeration hP n ∈
        basicNeighborhood X K (sample enumeration (n + 1)) := by
  have hsample : (↑(sample enumeration (n + 1)) : Set ℕ) ⊆ K.1 := by
    intro u hu
    exact mem_language_of_mem_sample_of_presents hP hu
  simpa only [approximant] using
    Classical.choose_spec (hK (sample enumeration (n + 1)) hsample)

theorem approximants_converge
    {X : Set Language} (K : Point X) (hK : BasisLimitPoint K)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration K.1) :
    ConvergentProperTower X
      (fun n => approximant K hK enumeration hP n) K := by
  refine ⟨?_, ?_⟩
  · intro n
    have hs := approximant_spec K hK enumeration hP n
    exact Set.ssubset_iff_subset_ne.mpr
      ⟨hs.2.2, fun heq => hs.1 (Subtype.ext heq)⟩
  · intro u hu
    rw [← hP] at hu
    obtain ⟨s, rfl⟩ := hu
    refine ⟨s, ?_⟩
    intro n hsn
    exact (approximant_spec K hK enumeration hP n).2.1
      (value_mem_sample (by omega))

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
