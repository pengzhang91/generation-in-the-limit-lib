import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Topology

/-!
# #07 Cantor--Bendixson levels

Claims 6.3 and 6.4. Claim 6.4 selects level-i approximants from successively
longer presentation prefixes of a terminal point at level i+1.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

open TowerTopology

/-- K is approached through Y in every basic neighborhood. -/
def ApproachedFrom
    {X : Set Language} (Y : Set (Point X)) (K : Point X) : Prop :=
  ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ K.1 →
    ∃ L : Point X,
      L ∈ Y ∧ L ≠ K ∧ L ∈ basicNeighborhood X K F

theorem perfectTower_terminal_mem_nextDerivative
    {X : Set Language} {i : ℕ} {tower : ℕ → Point X}
    {terminal : Point X}
    (hterminal : terminal ∈ cbDerivative X i)
    (htower : PerfectTower X tower terminal)
    (hlevels : ∀ n, tower n ∈ cbDerivative X i) :
    terminal ∈ cbDerivative X (i + 1) := by
  rw [cbDerivative_succ]
  refine ⟨hterminal, ?_⟩
  intro F hF
  obtain ⟨N, hN⟩ :=
    finite_eventually_contained htower.toConvergentProperTower F hF
  refine ⟨tower N, hlevels N, ?_, ?_⟩
  · intro heq
    exact (htower.proper N).ne (congrArg Subtype.val heq)
  · exact ⟨hN N le_rfl, (htower.proper N).le⟩

/-- Claim 6.3: a level-i point cannot terminate a perfect tower contained in
the ith derivative. -/
theorem claim_6_3
    {X : Set Language} {i : ℕ} {terminal : Point X}
    (hterminal : terminal ∈ cbLevel X i) :
    ¬∃ tower : ℕ → Point X,
        PerfectTower X tower terminal ∧
          ∀ n, tower n ∈ cbDerivative X i := by
  rintro ⟨tower, htower, hlevels⟩
  exact hterminal.2
    (perfectTower_terminal_mem_nextDerivative hterminal.1 htower hlevels)

/-- Neighborhood form of Claim 6.4. -/
theorem approachedFrom_previousLevel
    {X : Set Language} {i : ℕ} {terminal : Point X}
    (hterminal : terminal ∈ cbLevel X (i + 1)) :
    ApproachedFrom (cbLevel X i) terminal := by
  have hrelative : RelativeLimitPoint (cbDerivative X i) terminal := by
    simpa only [cbDerivative_succ, derivative] using hterminal.1
  intro F hF
  by_contra hnone
  have hnext : terminal ∈ cbDerivative X ((i + 1) + 1) := by
    rw [cbDerivative_succ]
    refine ⟨hterminal.1, ?_⟩
    intro G hG
    have hFG : (↑(F ∪ G) : Set ℕ) ⊆ terminal.1 := by
      intro u hu
      simp only [Finset.mem_coe, Finset.mem_union] at hu
      exact hu.elim (fun h => hF h) (fun h => hG h)
    obtain ⟨L, hLi, hne, hLFG⟩ := hrelative.2 (F ∪ G) hFG
    have hLF : L ∈ basicNeighborhood X terminal F := by
      exact ⟨fun u hu => hLFG.1 (by simp [hu]), hLFG.2⟩
    have hLG : L ∈ basicNeighborhood X terminal G := by
      exact ⟨fun u hu => hLFG.1 (by simp [hu]), hLFG.2⟩
    have hLi1 : L ∈ cbDerivative X (i + 1) := by
      by_contra hnot
      exact hnone ⟨L, ⟨hLi, hnot⟩, hne, hLF⟩
    exact ⟨L, hLi1, hne, hLG⟩
  exact hterminal.2 hnext

/-- Level-i approximant selected from the first n+1 presentation points. -/
noncomputable def levelApproximant
    {X : Set Language} (Y : Set (Point X)) (terminal : Point X)
    (hterminal : ApproachedFrom Y terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    (n : ℕ) : Point X := by
  have hsample :
      (↑(sample enumeration (n + 1)) : Set ℕ) ⊆ terminal.1 := by
    intro u hu
    exact mem_language_of_mem_sample_of_presents hP hu
  exact Classical.choose
    (hterminal (sample enumeration (n + 1)) hsample)

theorem levelApproximant_spec
    {X : Set Language} (Y : Set (Point X)) (terminal : Point X)
    (hterminal : ApproachedFrom Y terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    (n : ℕ) :
    levelApproximant Y terminal hterminal enumeration hP n ∈ Y ∧
      levelApproximant Y terminal hterminal enumeration hP n ≠ terminal ∧
      levelApproximant Y terminal hterminal enumeration hP n ∈
        basicNeighborhood X terminal (sample enumeration (n + 1)) := by
  have hsample :
      (↑(sample enumeration (n + 1)) : Set ℕ) ⊆ terminal.1 := by
    intro u hu
    exact mem_language_of_mem_sample_of_presents hP hu
  simpa only [levelApproximant] using
    Classical.choose_spec
      (hterminal (sample enumeration (n + 1)) hsample)

theorem levelApproximants_converge
    {X : Set Language} (Y : Set (Point X)) (terminal : Point X)
    (hterminal : ApproachedFrom Y terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    ConvergentProperTower X
      (fun n => levelApproximant Y terminal hterminal enumeration hP n)
      terminal := by
  refine ⟨?_, ?_⟩
  · intro n
    have hs := levelApproximant_spec Y terminal hterminal enumeration hP n
    exact Set.ssubset_iff_subset_ne.mpr
      ⟨hs.2.2.2, fun heq => hs.2.1 (Subtype.ext heq)⟩
  · intro u hu
    rw [← hP] at hu
    obtain ⟨s, rfl⟩ := hu
    refine ⟨s, ?_⟩
    intro n hsn
    exact
      (levelApproximant_spec Y terminal hterminal enumeration hP n).2.2.1
        (value_mem_sample (by omega))

/-- Claim 6.4: every level-(i+1) point is the limit of proper level-i
languages. -/
theorem claim_6_4
    {X : Set Language} {i : ℕ} {terminal : Point X}
    (hterminal : terminal ∈ cbLevel X (i + 1))
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    ∃ tower : ℕ → Point X,
      (∀ n, tower n ∈ cbLevel X i) ∧
        ConvergentProperTower X tower terminal := by
  let hlevel : ApproachedFrom (cbLevel X i) terminal :=
    approachedFrom_previousLevel hterminal
  refine
    ⟨fun n => levelApproximant (cbLevel X i) terminal hlevel enumeration hP n,
      ?_, ?_⟩
  · intro n
    exact
      (levelApproximant_spec
        (cbLevel X i) terminal hlevel enumeration hP n).1
  · exact
      levelApproximants_converge
        (cbLevel X i) terminal hlevel enumeration hP

end GenLimit.KleinbergWei.DensityMeasures
