import GenLimit.Support.KleinbergWei.CantorBendixson
import GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse

/-!
# #23 Topological preliminaries

The shared containment topology specialized to Section 3.3 of the
Kleinberg--Wei Banach-density paper.
-/

namespace GenLimit.KleinbergWei.Banach

/-- Section 3.3's perfect-tower Definition 3.1. -/
abbrev PerfectTower
    (X : Set Language) (tower : ℕ → TowerTopology.Point X)
    (terminal : TowerTopology.Point X) : Prop :=
  TowerTopology.PerfectTower X tower terminal

/-- Section 3.3 Definition 3.7 restricted to finite natural-number derivatives. -/
abbrev cbDerivative
    (X : Set Language) (n : ℕ) : Set (TowerTopology.Point X) :=
  TowerTopology.cbDerivative X n

/-- Empty-kernel finite rank at most r. -/
abbrev FiniteRankAtMost (X : Set Language) (r : ℕ) : Prop :=
  TowerTopology.FiniteRankAtMost X r

theorem topology_hausdorff (X : Set Language) :
    TowerTopology.Hausdorff X :=
  TowerTopology.hausdorff X

theorem topology_firstCountable_at
    {X : Set Language} {K : TowerTopology.Point X}
    {enumeration : ℕ → ℕ} (hP : Presents enumeration K.1) :
    ∀ O : Set (TowerTopology.Point X), TowerTopology.KWOpen X O → K ∈ O →
      ∃ n, TowerTopology.basicNeighborhood X K (sample enumeration n) ⊆ O :=
  TowerTopology.presentation_is_localBasis hP

/-- Claim 3.6, perfect-tower-to-limit-point direction. -/
theorem claim_3_6_forward
    {X : Set Language} {tower : ℕ → TowerTopology.Point X}
    {terminal : TowerTopology.Point X}
    (h : PerfectTower X tower terminal) :
    TowerTopology.IsLimitPoint terminal :=
  TowerTopology.limitPoint_of_perfectTower h

/-- Claim 3.6 at the convergence-core level. -/
theorem claim_3_6_convergence_core
    {X : Set Language} {terminal : TowerTopology.Point X}
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    TowerTopology.IsLimitPoint terminal ↔
      ∃ tower : ℕ → TowerTopology.Point X,
        TowerTopology.ConvergentProperTower X tower terminal :=
  TowerTopology.isLimitPoint_iff_exists_convergentProperTower enumeration hP

/-- Claim 3.6 in the literal nonredundant perfect-tower form. -/
theorem claim_3_6
    {X : Set Language} {terminal : TowerTopology.Point X}
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    TowerTopology.IsLimitPoint terminal ↔
      ∃ tower : ℕ → TowerTopology.Point X,
        PerfectTower X tower terminal :=
  TowerTopology.isLimitPoint_iff_exists_perfectTower enumeration hP

/-- Finite derivatives form a decreasing hierarchy. -/
theorem derivative_monotone_decreasing (X : Set Language) :
    Antitone (cbDerivative X) :=
  TowerTopology.cbDerivative_antitone X

end GenLimit.KleinbergWei.Banach
