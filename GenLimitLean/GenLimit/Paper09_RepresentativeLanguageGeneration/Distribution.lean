import Mathlib.Data.ENNReal.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Representative generation: discrete distributions and group profiles

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Definitions 2.5--2.7 and the randomized-generator prose in
Section 2.1.

The source universe is countable, so a probability distribution is represented
by a nonnegative summable mass function of total mass one.  Definition 2.7 calls
its distance a supremum but prints `max` over countably many coordinates.
A maximum need not be attained.  `groupSupDistance` implements the intended
supremum as an `iSup` in `ENNReal`; this repair is explicit and is not a
claim that the displayed `max` is always defined.
-/

namespace GenLimit.RepresentativeGeneration

/-- A countably supported discrete probability distribution. -/
structure DiscreteDistribution (α : Type*) where
  mass : α → ℝ
  mass_nonnegative : ∀ x, 0 ≤ mass x
  summable_mass : Summable mass
  total_mass : ∑' x, mass x = 1

/-- Every probability distribution has a point of nonzero mass.  Keeping this
fact next to the paper-local distribution API lets relationship modules
extract deterministic generators without adding probability notions to
Core. -/
theorem DiscreteDistribution.exists_mass_ne_zero
    (mu : DiscreteDistribution α) :
    ∃ x, mu.mass x ≠ 0 := by
  by_contra h
  push_neg at h
  have hsum : ∑' x, mu.mass x = 0 := by
    simp [h]
  linarith [mu.total_mass]

/-- A fixed support point of a discrete distribution. -/
noncomputable def DiscreteDistribution.supportPoint
    (mu : DiscreteDistribution α) : α :=
  Classical.choose mu.exists_mass_ne_zero

theorem DiscreteDistribution.supportPoint_mass_ne_zero
    (mu : DiscreteDistribution α) :
    mu.mass mu.supportPoint ≠ 0 :=
  Classical.choose_spec mu.exists_mass_ne_zero

/-- Convert Mathlib's `ENNReal`-valued probability mass functions to the
real-valued discrete distributions used by the paper-facing API.  This is
useful for finite-support constructions: `PMF.ofFinset` and `PMF.map` handle
the normalization and pushforward bookkeeping, while the theorem below
shows that no mass is lost by taking finite real values. -/
noncomputable def DiscreteDistribution.ofPMF (p : PMF α) :
    DiscreteDistribution α where
  mass x := (p x).toReal
  mass_nonnegative x := ENNReal.toReal_nonneg
  summable_mass := ENNReal.summable_toReal (by
    rw [p.tsum_coe]
    exact ENNReal.one_ne_top)
  total_mass := by
    rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x),
      p.tsum_coe]
    simp

@[simp] theorem DiscreteDistribution.ofPMF_mass
    (p : PMF α) (x : α) :
    (DiscreteDistribution.ofPMF p).mass x = (p x).toReal :=
  rfl

/-- The randomized-generator interface described in published Section 2.1. -/
abbrev RandomizedGenerator (α : Type*) :=
  ∀ t : ℕ, (Fin t → α) → DiscreteDistribution α

/-- The mass function restricted to a set. -/
noncomputable def restrictedMass
    (μ : DiscreteDistribution α) (A : Set α) (x : α) : ℝ := by
  classical
  exact if x ∈ A then μ.mass x else 0

/-- Probability assigned by `μ` to the set `A`. -/
noncomputable def groupMass
    (μ : DiscreteDistribution α) (A : Set α) : ℝ := by
  exact ∑' x, restrictedMass μ A x

/-- Set mass is preserved by `DiscreteDistribution.ofPMF`. -/
theorem groupMass_ofPMF
    (p : PMF α) (A : Set α) :
    groupMass (DiscreteDistribution.ofPMF p) A =
      (p.toOuterMeasure A).toReal := by
  classical
  rw [groupMass, PMF.toOuterMeasure_apply,
    ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro x
    by_cases hx : x ∈ A
    · simp [restrictedMass, hx]
    · simp [restrictedMass, hx]
  · intro x
    by_cases hx : x ∈ A
    · simpa [Set.indicator_of_mem hx] using p.apply_ne_top x
    · simp [Set.indicator_of_notMem hx]

theorem groupMass_summable
    (μ : DiscreteDistribution α) (A : Set α) :
    Summable (restrictedMass μ A) := by
  classical
  apply Summable.of_nonneg_of_le
  · intro x
    simp only [restrictedMass]
    split <;> simp_all [μ.mass_nonnegative]
  · intro x
    simp only [restrictedMass]
    split
    · exact le_rfl
    · exact μ.mass_nonnegative x
  · exact μ.summable_mass

theorem groupMass_nonnegative
    (μ : DiscreteDistribution α) (A : Set α) :
    0 ≤ groupMass μ A := by
  classical
  apply tsum_nonneg
  intro x
  simp only [restrictedMass]
  split <;> simp_all [μ.mass_nonnegative]

theorem groupMass_le_one
    (μ : DiscreteDistribution α) (A : Set α) :
    groupMass μ A ≤ 1 := by
  classical
  rw [← μ.total_mass]
  apply Summable.tsum_le_tsum
  · intro x
    simp only [restrictedMass]
    split
    · exact le_rfl
    · exact μ.mass_nonnegative x
  · exact groupMass_summable μ A
  · exact μ.summable_mass

theorem groupMass_univ (μ : DiscreteDistribution α) :
    groupMass μ Set.univ = 1 := by
  classical
  simpa [groupMass, restrictedMass] using μ.total_mass

/-- Pointwise support, useful as an equivalent form of probability one. -/
def SupportedOn (μ : DiscreteDistribution α) (A : Set α) : Prop :=
  ∀ x, μ.mass x ≠ 0 → x ∈ A

theorem groupMass_eq_one_of_supportedOn
    {μ : DiscreteDistribution α} {A : Set α}
    (h : SupportedOn μ A) :
    groupMass μ A = 1 := by
  classical
  rw [groupMass, ← μ.total_mass]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ A
  · simp [restrictedMass, hx]
  · have hzero : μ.mass x = 0 := by
      by_contra hne
      exact hx (h x hne)
    simp [restrictedMass, hx, hzero]

theorem groupMass_add_compl (μ : DiscreteDistribution α) (A : Set α) :
    groupMass μ A + groupMass μ Aᶜ = 1 := by
  classical
  calc
    groupMass μ A + groupMass μ Aᶜ =
        ∑' x, (restrictedMass μ A x + restrictedMass μ Aᶜ x) := by
      rw [Summable.tsum_add (groupMass_summable μ A)
        (groupMass_summable μ Aᶜ)]
      rfl
    _ = ∑' x, μ.mass x := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ A <;> simp [restrictedMass, hx]
    _ = 1 := μ.total_mass

theorem supportedOn_of_groupMass_eq_one
    {μ : DiscreteDistribution α} {A : Set α}
    (h : groupMass μ A = 1) :
    SupportedOn μ A := by
  classical
  have hcompl : groupMass μ Aᶜ = 0 := by
    have hadd := groupMass_add_compl μ A
    linarith
  intro x hmass
  by_contra hx
  have hxcompl : x ∈ Aᶜ := hx
  have hle : μ.mass x ≤ groupMass μ Aᶜ := by
    rw [groupMass]
    have hterm :=
      (groupMass_summable μ Aᶜ).le_tsum x (fun y _hy => by
        simp only [restrictedMass]
        split
        · exact μ.mass_nonnegative y
        · exact le_rfl)
    simpa [restrictedMass, hxcompl] using hterm
  have hzero : μ.mass x = 0 := by
    have hnonneg := μ.mass_nonnegative x
    rw [hcompl] at hle
    linarith
  exact hmass hzero

theorem supportedOn_iff_groupMass_eq_one
    {μ : DiscreteDistribution α} {A : Set α} :
    SupportedOn μ A ↔ groupMass μ A = 1 :=
  ⟨groupMass_eq_one_of_supportedOn, supportedOn_of_groupMass_eq_one⟩

/-- A supported distribution assigns zero mass to a disjoint set. -/
theorem groupMass_eq_zero_of_supportedOn_of_disjoint
    {μ : DiscreteDistribution α} {U A : Set α}
    (hμ : SupportedOn μ U) (hdisjoint : Disjoint U A) :
    groupMass μ A = 0 := by
  classical
  have hzero : restrictedMass μ A = 0 := by
    funext x
    by_cases hxA : x ∈ A
    · have hmass : μ.mass x = 0 := by
        by_contra hne
        exact Set.disjoint_left.mp hdisjoint (hμ x hne) hxA
      simp [restrictedMass, hxA, hmass]
    · simp [restrictedMass, hxA]
  rw [groupMass, hzero]
  simp

/-- Published Definition 2.5, for a countably indexed collection of possibly overlapping
groups. -/
noncomputable def inducedGroupProbability
    (μ : DiscreteDistribution α) (groups : ℕ → Set α) (i : ℕ) : ℝ :=
  groupMass μ (groups i)

/-- Published Definition 2.6: empirical group probability of the distinct sample.
The paper only evaluates nonempty histories.  We totalize the empty sample at
zero and explicitly require positive history length in representativeness. -/
noncomputable def empiricalGroupProbability
    (S : Finset α) (groups : ℕ → Set α) (i : ℕ) : ℝ := by
  classical
  exact if S.Nonempty then
    ((S.filter fun x => x ∈ groups i).card : ℝ) / S.card
  else 0

theorem empiricalGroupProbability_nonnegative
    (S : Finset α) (groups : ℕ → Set α) (i : ℕ) :
    0 ≤ empiricalGroupProbability S groups i := by
  classical
  rw [empiricalGroupProbability]
  split
  · positivity
  · exact le_rfl

/-- Published Definition 2.7, with the intended supremum (`iSup`) replacing the
non-attained `max` printed in the source. -/
noncomputable def groupSupDistance
    (μ : DiscreteDistribution α) (S : Finset α)
    (groups : ℕ → Set α) : ENNReal :=
  ⨆ i : ℕ, ENNReal.ofReal
    |inducedGroupProbability μ groups i -
      empiricalGroupProbability S groups i|

theorem coordinate_le_groupSupDistance
    (μ : DiscreteDistribution α) (S : Finset α)
    (groups : ℕ → Set α) (i : ℕ) :
    ENNReal.ofReal
        |inducedGroupProbability μ groups i -
          empiricalGroupProbability S groups i| ≤
      groupSupDistance μ S groups := by
  exact le_iSup (fun j : ℕ => ENNReal.ofReal
    |inducedGroupProbability μ groups j -
      empiricalGroupProbability S groups j|) i

end GenLimit.RepresentativeGeneration
