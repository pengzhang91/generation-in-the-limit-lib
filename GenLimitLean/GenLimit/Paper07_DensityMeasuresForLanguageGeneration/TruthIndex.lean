import GenLimit.Core.OrderedDensity
import GenLimit.Support.KleinbergWei.TowerTopology

/-!
# #07 Truth index

`IsTruthIndex` characterizes the least asymptotic upper-density threshold
specified in Definition 4.5, and the value one when no tower exists. This file
proves conditional uniqueness, not existence or the paper's minimax theorem.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

open TowerTopology

/-- A perfect tower whose stages have ordered upper density at most bound. -/
def HasPerfectTowerBound
    (X : Set Language) (terminal : Point X)
    (ordering : OrderedLanguage) (bound : ℝ) : Prop :=
  ordering.carrier = terminal.1 ∧
    ∃ tower : ℕ → Point X,
      PerfectTower X tower terminal ∧
        ∀ n, ordering.upperDensity (tower n).1 ≤ bound

def HasAnyPerfectTower
    (X : Set Language) (terminal : Point X) : Prop :=
  ∃ tower : ℕ → Point X, PerfectTower X tower terminal

/-- Definition 4.5 in its epsilon and least-bound formulation. -/
def IsTruthIndex
    (X : Set Language) (terminal : Point X)
    (ordering : OrderedLanguage) (τ : ℝ) : Prop :=
  0 ≤ τ ∧ τ ≤ 1 ∧
    (HasAnyPerfectTower X terminal →
      (∀ ε : ℝ, 0 < ε →
        HasPerfectTowerBound X terminal ordering (τ + ε)) ∧
      ∀ σ : ℝ,
        (∀ ε : ℝ, 0 < ε →
          HasPerfectTowerBound X terminal ordering (σ + ε)) →
        τ ≤ σ) ∧
    (¬HasAnyPerfectTower X terminal → τ = 1)

theorem isTruthIndex_unique
    {X : Set Language} {terminal : Point X}
    {ordering : OrderedLanguage} {τ σ : ℝ}
    (hτ : IsTruthIndex X terminal ordering τ)
    (hσ : IsTruthIndex X terminal ordering σ) :
    τ = σ := by
  by_cases htower : HasAnyPerfectTower X terminal
  · have hτcore := hτ.2.2.1 htower
    have hσcore := hσ.2.2.1 htower
    exact le_antisymm
      (hτcore.2 σ hσcore.1)
      (hσcore.2 τ hτcore.1)
  · exact (hτ.2.2.2 htower).trans (hσ.2.2.2 htower).symm

end GenLimit.KleinbergWei.DensityMeasures
