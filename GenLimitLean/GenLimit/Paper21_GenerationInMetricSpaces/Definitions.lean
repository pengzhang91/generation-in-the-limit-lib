import GenLimit.Core.GenericGeneration
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith

/-!
# Generation in metric spaces: source-facing semantic definitions

Source: Jiaxun Li, Vinod Raman, and Ambuj Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1.

The source writes the closed neighbourhood of a set `A` as
`{y | inf_{x ∈ A} ρ(x,y) ≤ r}`.  Rather than introduce an extended-real
infimum (and its special empty-set convention), `InClosedNeighborhood`
uses the equivalent order characterization

`∀ η > r, ∃ x ∈ A, ρ x y < η`.

For a genuine metric and nonempty `A`, this is exactly the displayed
infimum inequality.  It also gives the intended empty-set value: no point
is close to the empty set.

Distances are explicit functions.  The principal monotonicity and
Lipschitz-transfer arguments below use only inequalities between distances;
metric axioms are therefore not unnecessarily repeated as hypotheses.
-/

namespace GenLimit.MetricSpaces

/-- An explicit real-valued distance kernel.  Paper-level theorems quantify
over metrics, while the order arguments need only the displayed kernel. -/
abbrev Distance (α : Type*) := α → α → ℝ

/-- Membership in the source's closed radius-`r` neighbourhood `B(A,r)`.

This order characterization says that the infimum distance from `y` to `A`
is at most `r`, without selecting a nearest point. -/
def InClosedNeighborhood
    (ρ : Distance α) (A : Set α) (r : ℝ) (y : α) : Prop :=
  ∀ η : ℝ, r < η → ∃ x ∈ A, ρ x y < η

/-- The source's set-valued closed neighbourhood `B(A,r)`. -/
def closedNeighborhood
    (ρ : Distance α) (A : Set α) (r : ℝ) : Set α :=
  {y | InClosedNeighborhood ρ A r y}

theorem inClosedNeighborhood_mono_radius
    {ρ : Distance α} {A : Set α} {r s : ℝ} (hrs : r ≤ s) :
    closedNeighborhood ρ A r ⊆ closedNeighborhood ρ A s := by
  intro y hy η hsη
  exact hy η (lt_of_le_of_lt hrs hsη)

theorem inClosedNeighborhood_mono_centers
    {ρ : Distance α} {A B : Set α} {r : ℝ} (hAB : A ⊆ B) :
    closedNeighborhood ρ A r ⊆ closedNeighborhood ρ B r := by
  intro y hy η hrη
  obtain ⟨x, hxA, hxy⟩ := hy η hrη
  exact ⟨x, hAB hxA, hxy⟩

theorem not_inClosedNeighborhood_anti_radius
    {ρ : Distance α} {A : Set α} {r s : ℝ} (hrs : r ≤ s)
    {y : α} (hy : y ∉ closedNeighborhood ρ A s) :
    y ∉ closedNeighborhood ρ A r :=
  fun hyr ↦ hy (inClosedNeighborhood_mono_radius hrs hyr)

/-- For one center, the order definition reduces to the ordinary closed-ball
inequality. -/
theorem mem_closedNeighborhood_singleton_iff
    {ρ : Distance α} {x y : α} {r : ℝ} :
    y ∈ closedNeighborhood ρ {x} r ↔ ρ x y ≤ r := by
  constructor
  · intro hy
    by_contra hnot
    have hrho : r < ρ x y := lt_of_not_ge hnot
    let η := (r + ρ x y) / 2
    have hrη : r < η := by
      dsimp [η]
      linarith
    obtain ⟨z, hz, hzη⟩ := hy η hrη
    have hzx : z = x := by simpa using hz
    subst z
    dsimp [η] at hzη
    linarith
  · intro hxy η hrη
    exact ⟨x, by simp, lt_of_le_of_lt hxy hrη⟩

/-- Definition 2.2 without choosing an extended-natural value for the
covering number: `A` has a finite radius-`r` covering. -/
def HasFiniteCover
    (ρ : Distance α) (r : ℝ) (A : Set α) : Prop :=
  ∃ centers : Finset α,
    A ⊆ closedNeighborhood ρ (centers : Set α) r

/-- The proposition `N(r;A,ρ) ≥ d`.

It remains true for every `d` when no finite cover exists, matching the
paper's value `∞`. -/
def CoveringNumberAtLeast
    (ρ : Distance α) (r : ℝ) (A : Set α) (d : ℕ) : Prop :=
  ∀ centers : Finset α,
    A ⊆ closedNeighborhood ρ (centers : Set α) r →
      d ≤ centers.card

/-- The proposition `N(r;A,ρ) = d`, expressed without an extended-natural
covering-number type. -/
def CoveringNumberEq
    (ρ : Distance α) (r : ℝ) (A : Set α) (d : ℕ) : Prop :=
  CoveringNumberAtLeast ρ r A d ∧
    ∃ centers : Finset α,
      centers.card = d ∧
      A ⊆ closedNeighborhood ρ (centers : Set α) r

theorem finiteCover_mono_radius
    {ρ : Distance α} {A : Set α} {r s : ℝ}
    (hrs : r ≤ s) :
    HasFiniteCover ρ r A → HasFiniteCover ρ s A := by
  rintro ⟨centers, hcover⟩
  exact ⟨centers, hcover.trans (inClosedNeighborhood_mono_radius hrs)⟩

theorem coveringNumberAtLeast_anti_radius
    {ρ : Distance α} {A : Set α} {r s : ℝ} {d : ℕ}
    (hrs : r ≤ s) :
    CoveringNumberAtLeast ρ s A d →
      CoveringNumberAtLeast ρ r A d := by
  intro hs centers hcover
  exact hs centers
    (hcover.trans (inClosedNeighborhood_mono_radius hrs))

theorem coveringNumberAtLeast_mono_set
    {ρ : Distance α} {A B : Set α} {r : ℝ} {d : ℕ}
    (hAB : A ⊆ B) :
    CoveringNumberAtLeast ρ r A d →
      CoveringNumberAtLeast ρ r B d := by
  intro hA centers hcover
  exact hA centers (hAB.trans hcover)

/-- Definition 2.3: every member support has infinite radius-`r` covering
number. -/
def UniformlyUnboundedSupportAt
    (ρ : Distance α) (r : ℝ)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ¬ HasFiniteCover ρ r L

/-! ## Version spaces and scale-sensitive closure dimension -/

/-- The positive version space after a finite sample. -/
def versionSpace
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    Set (GenLimit.Generic.Language α) :=
  {L | L ∈ H ∧ (S : Set α) ⊆ L}

/-- Intersection of the positive version space. -/
def commonCore
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    GenLimit.Generic.Language α :=
  {x | ∀ L, L ∈ versionSpace H S → x ∈ L}

/-- Definition 3.1's witness at covering number exactly `d`. -/
def IsScaleClosureWitness
    (ρ : Distance α) (ε ε' : ℝ)
    (H : GenLimit.Generic.LanguageClass α)
    (S : Finset α) (d : ℕ) : Prop :=
  (versionSpace H S).Nonempty ∧
    CoveringNumberEq ρ ε (S : Set α) d ∧
    HasFiniteCover ρ ε' (commonCore H S)

/-- The paper statement `C^ε'ε(H) < ∞`: scale-closure witnesses have a
uniformly bounded covering number. -/
def HasFiniteScaleClosureDimension
    (ρ : Distance α) (ε ε' : ℝ)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ D : ℕ, ∀ d : ℕ, D < d →
    ¬ ∃ S : Finset α, IsScaleClosureWitness ρ ε ε' H S d

/-! ## Metric generation semantics (Definitions 2.4--2.7) -/

/-- The adversary stream lies in `L` and its range is an `ε`-cover of `L`. -/
def MetricPresentation
    (ρ : Distance α) (ε : ℝ)
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  GenLimit.Generic.StreamIn stream L ∧
    L ⊆ closedNeighborhood ρ (Set.range stream) ε

/-- The output is target-valid and outside the closed `ε'`-neighbourhood of
the observed prefix. -/
def MetricCorrectAt
    (ρ : Distance α) (ε' : ℝ)
    (gen : GenLimit.Generic.Generator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  GenLimit.Generic.output gen stream t ∈ L ∧
    GenLimit.Generic.output gen stream t ∉
      closedNeighborhood ρ
        (GenLimit.Generic.sample stream t : Set α) ε'

/-- A fixed generator witnesses Definition 2.5 at novelty scales
`(ε,ε')`. -/
def IsLimitGeneratorAt
    (ρ : Distance α) (ε ε' : ℝ)
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H →
    ∀ stream : GenLimit.Generic.Stream α,
      MetricPresentation ρ ε stream L →
        ∃ T, ∀ t, T ≤ t →
          MetricCorrectAt ρ ε' gen L stream t

/-- Definition 2.5: generation in the limit at scales `(ε,ε')`. -/
def GeneratableInLimitAt
    (ρ : Distance α) (ε ε' : ℝ)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α,
    IsLimitGeneratorAt ρ ε ε' gen H

/-- A fixed generator and threshold witness Definition 2.6. -/
def IsUniformGeneratorAt
    (ρ : Distance α) (ε ε' : ℝ)
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∀ L, L ∈ H →
    ∀ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.StreamIn stream L →
        ∀ t,
          CoveringNumberAtLeast ρ ε
              (GenLimit.Generic.sample stream t : Set α) d →
            ∀ s, t ≤ s →
              MetricCorrectAt ρ ε' gen L stream s

/-- Definition 2.6: uniform generation at scales `(ε,ε')`. -/
def UniformlyGeneratableAt
    (ρ : Distance α) (ε ε' : ℝ)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α,
    ∃ d : ℕ, IsUniformGeneratorAt ρ ε ε' gen H d

/-- A fixed generator witnesses Definition 2.7.  Its threshold may depend on
the target language, but not on the stream. -/
def IsNonuniformGeneratorAt
    (ρ : Distance α) (ε ε' : ℝ)
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H →
    ∃ d : ℕ,
      ∀ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.StreamIn stream L →
          ∀ t,
            CoveringNumberAtLeast ρ ε
                (GenLimit.Generic.sample stream t : Set α) d →
              ∀ s, t ≤ s →
                MetricCorrectAt ρ ε' gen L stream s

/-- Definition 2.7: non-uniform generation at scales `(ε,ε')`. -/
def NonuniformlyGeneratableAt
    (ρ : Distance α) (ε ε' : ℝ)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α,
    IsNonuniformGeneratorAt ρ ε ε' gen H

end GenLimit.MetricSpaces
