import GenLimit.Core.OrderedDensity
import GenLimit.Support.KleinbergWei.TowerTopology

/-!
# #07 Truth index

`IsTruthIndex` characterizes the least asymptotic upper-density threshold
specified in Definition 4.5, and the value one when no tower exists. This file
constructs this threshold from the infimum of the realized tower bounds.
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

/-- Every ordered target has a truth index. With towers present this is the
infimum of the realizable bounds, whether or not a tower realizes that infimum. -/
theorem exists_truthIndex {X : Set Language} (terminal : Point X)
    (ordering : OrderedLanguage) (hcarrier : ordering.carrier = terminal.1) :
    ∃ τ, IsTruthIndex X terminal ordering τ := by
  classical
  by_cases h : HasAnyPerfectTower X terminal
  · let B : Set ℝ := {b | HasPerfectTowerBound X terminal ordering b}
    obtain ⟨tower, ht⟩ := h
    have h1 : 1 ∈ B :=
      ⟨hcarrier, tower, ht, fun i ↦ ordering.upperDensity_le_one _⟩
    have h0 : ∀ b ∈ B, 0 ≤ b := by
      rintro b ⟨_, t, _, hb⟩
      exact (ordering.upperDensity_nonneg _).trans (hb 0)
    have hbdd : BddBelow B := ⟨0, h0⟩
    refine ⟨sInf B, le_csInf ⟨1,h1⟩ h0, csInf_le hbdd h1, fun _ ↦ ⟨?_, ?_⟩,
      fun hn ↦ (hn ⟨tower, ht⟩).elim⟩
    · intro ε hε
      obtain ⟨b, hb, hlt⟩ := exists_lt_of_csInf_lt (show B.Nonempty from ⟨1,h1⟩)
        (show sInf B < sInf B + ε by linarith)
      obtain ⟨_,t,htower,hb⟩ := hb
      exact ⟨hcarrier, t, htower, fun i ↦ (hb i).trans hlt.le⟩
    · intro σ hσ
      by_contra! hlt
      have hmid := csInf_le hbdd (show σ + (sInf B - σ) / 2 ∈ B from
        hσ _ (by linarith))
      linarith
  · exact ⟨1, zero_le_one, le_rfl, fun ht ↦ (h ht).elim, fun _ ↦ rfl⟩

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
