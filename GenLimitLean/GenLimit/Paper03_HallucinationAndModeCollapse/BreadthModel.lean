import GenLimit.Paper03_HallucinationAndModeCollapse.GenerationModel
import GenLimit.Paper03_HallucinationAndModeCollapse.UniversalRates

/-!
# Statistical exact fresh breadth and support membership

Source: Definitions 5--6, the loss before Theorem 3.3, and Definition 13 of
arXiv:2411.09642v3. Training returns one PMF; the outer probability concerns
the IID training sample. Breadth error tests equality of the entire support,
not the success of a single random output.

`DecidableMOP` follows Definition 6's pointwise quantifiers. The stronger
`UniformDecidableMOP` supplies one decider uniform in the training sample.
The positive constructions below supply that stronger interface whenever
their training and membership procedures are ordinarily computable.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.DiscreteIID Filter
open scoped Topology

noncomputable def breadthError (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : ℝ :=
  probability (samples p n) {xs | (G xs).support ≠ C i \ {x | x ∈ xs}}

def AchievesBreadthRate (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (R : ℕ → ℝ) : Prop :=
  ∀ i p, ValidDistribution C i p → ∃ D : ℝ, 0 < D ∧
    ∀ n, breadthError C G p i n ≤ D * R n

def NoBreadthRate (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator) : Prop :=
  ∃ i p, ValidDistribution C i p ∧
    0 < limsup (fun n => breadthError C G p i n) atTop

def ExponentialBreadth (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator) : Prop :=
  ∀ i p, ValidDistribution C i p →
    ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
      ∀ n, breadthError C G p i n ≤ D * Real.exp (-c * n)

def DecidableMOP (G : StatisticalGenerator) : Prop :=
  ∀ xs, ∃ query : ℕ → Bool, Computable query ∧
    ∀ x, query x = true ↔ x ∈ (G xs).support

def UniformDecidableMOP (G : StatisticalGenerator) : Prop :=
  ∃ query : List ℕ → ℕ → Bool, Computable₂ query ∧
    ∀ xs x, query xs x = true ↔ x ∈ (G xs).support

theorem UniformDecidableMOP.pointwise {G : StatisticalGenerator}
    (h : UniformDecidableMOP G) : DecidableMOP G := by
  obtain ⟨query, hq, hspec⟩ := h
  exact fun xs => ⟨query xs, hq.comp (Computable.const xs) Computable.id, hspec xs⟩

theorem breadthError_nonneg (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : 0 ≤ breadthError C G p i n := probability_nonneg _ _

theorem breadthError_le_one (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : breadthError C G p i n ≤ 1 := probability_le_one _ _

theorem breadthError_tendsto_zero_of_rate (C : Generic.LanguageFamily ℕ)
    (G : StatisticalGenerator) (R : ℕ → ℝ) (hG : AchievesBreadthRate C G R)
    (hR : Tendsto R atTop (𝓝 0)) (i : ℕ) (p : PMF ℕ) (hp : ValidDistribution C i p) :
    Tendsto (fun n => breadthError C G p i n) atTop (𝓝 0) := by
  obtain ⟨D, _, hb⟩ := hG i p hp
  apply squeeze_zero (breadthError_nonneg C G p i) hb
  simpa using tendsto_const_nhds.mul hR

theorem NoBreadthRate.excludes_rate {C : Generic.LanguageFamily ℕ} {G : StatisticalGenerator}
    (h : NoBreadthRate C G) (R : ℕ → ℝ) (hR : Tendsto R atTop (𝓝 0)) :
    ¬AchievesBreadthRate C G R := by
  intro hG
  obtain ⟨i, p, hp, hpos⟩ := h
  rw [(breadthError_tendsto_zero_of_rate C G R hG hR i p hp).limsup_eq] at hpos
  exact lt_irrefl _ hpos

end GenLimit.HallucinationModeCollapse
