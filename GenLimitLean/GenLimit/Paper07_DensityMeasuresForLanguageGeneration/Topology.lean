import GenLimit.Support.KleinbergWei.CantorBendixson
import GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse

/-!
# #07 Perfect towers and topology

Overview Definition 2.3, detailed Definition 4.3, and the topological Claim
6.1 of Kleinberg--Wei,
*Density Measures for Language Generation*.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

/-- Overview Definition 2.3 and detailed Definition 4.3. -/
abbrev PerfectTower
    (X : Set Language) (tower : ℕ → TowerTopology.Point X)
    (terminal : TowerTopology.Point X) : Prop :=
  TowerTopology.PerfectTower X tower terminal

theorem claim_6_1_forward
    {X : Set Language} {tower : ℕ → TowerTopology.Point X}
    {terminal : TowerTopology.Point X}
    (h : PerfectTower X tower terminal) :
    TowerTopology.IsLimitPoint terminal :=
  TowerTopology.limitPoint_of_perfectTower h

theorem claim_6_1_convergence_core
    {X : Set Language} {terminal : TowerTopology.Point X}
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    TowerTopology.IsLimitPoint terminal ↔
      ∃ tower : ℕ → TowerTopology.Point X,
        TowerTopology.ConvergentProperTower X tower terminal :=
  TowerTopology.isLimitPoint_iff_exists_convergentProperTower enumeration hP

/-- Claim 6.1 in the literal nonredundant perfect-tower form. -/
theorem claim_6_1
    {X : Set Language} {terminal : TowerTopology.Point X}
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    TowerTopology.IsLimitPoint terminal ↔
      ∃ tower : ℕ → TowerTopology.Point X,
        PerfectTower X tower terminal :=
  TowerTopology.isLimitPoint_iff_exists_perfectTower enumeration hP

theorem containment_topology_hausdorff (X : Set Language) :
    TowerTopology.Hausdorff X :=
  TowerTopology.hausdorff X

/-- Finite Cantor--Bendixson layers. -/
abbrev cbLevel
    (X : Set Language) (n : ℕ) : Set (TowerTopology.Point X) :=
  TowerTopology.cbLevel X n

theorem cbLevels_disjoint
    {X : Set Language} {i j : ℕ} (hij : i < j) :
    Disjoint (cbLevel X i) (cbLevel X j) :=
  TowerTopology.cbLevel_disjoint_of_lt hij

end GenLimit.KleinbergWei.DensityMeasures
