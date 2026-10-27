import GenLimit.Paper03_HallucinationAndModeCollapse.BreadthModel
import GenLimit.Paper03_HallucinationAndModeCollapse.Definitions

/-!
# Statistical unambiguous generation and its rate interfaces

Source: Definitions 7--8 and the loss before Theorem 3.6 of
arXiv:2411.09642v3. Training returns a PMF; only the IID training sample is
random in the support-level loss. Repetition of training examples is allowed.
The strict extended-cardinality comparison is the existing `UnambiguousAt`.

The printed display puts one on success. `unambiguousError` deliberately puts
one on failure, as required by the surrounding error/rate convention. The
complement identity below makes this correction explicit.
-/

namespace GenLimit.HallucinationModeCollapse

noncomputable section

open GenLimit.Generic GenLimit.DiscreteIID Filter
open scoped Topology

/-- View the support of a statistical generator through the existing online
interface. The Boolean query is semantic; no computability is inferred. -/
def statisticalSupportView (G : StatisticalGenerator) : SupportGenerator := by
  classical
  exact {
    support := fun _ xs => (G (List.ofFn xs)).support
    query := fun _ xs x => decide (x ∈ (G (List.ofFn xs)).support)
    query_spec := by intro t xs x; simp }

theorem statisticalSupportView_supportAt (G : StatisticalGenerator) (stream : Stream ℕ) (t : ℕ) :
    supportAt (statisticalSupportView G) stream t = (G (GenLimit.textPrefix stream t)).support := by
  change (G (List.ofFn (fun i : Fin t => stream i))).support = _
  rw [← GenLimit.textPrefix_eq_ofFn]

/-- Definition 7, using exactly the existing online stability predicate. -/
def StatisticalStable (G : StatisticalGenerator) (C : Generic.LanguageFamily ℕ) : Prop :=
  Stable (statisticalSupportView G) C

theorem statisticalStable_iff (G : StatisticalGenerator) (C : Generic.LanguageFamily ℕ) :
    StatisticalStable G C ↔
      ∀ i stream, Generic.Presents stream (C i) → ∃ N, ∀ s t, N ≤ s → N ≤ t →
        (G (GenLimit.textPrefix stream s)).support = (G (GenLimit.textPrefix stream t)).support := by
  simp only [StatisticalStable, Stable, statisticalSupportView_supportAt]

/-- Failure probability for the strict-closest-target condition. In
particular equal infinite symmetric differences are a failure. -/
def unambiguousError (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : ℝ :=
  probability (samples p n) {xs | ¬UnambiguousAt C i (G xs).support}

/-- The literal success-indicator polarity printed before Theorem 3.6,
recorded separately rather than used as a vanishing-error objective. -/
def printedUnambiguousError (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : ℝ :=
  probability (samples p n) {xs | UnambiguousAt C i (G xs).support}

theorem unambiguousError_eq_one_sub_printed (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) :
    unambiguousError C G p i n = 1 - printedUnambiguousError C G p i n :=
  probability_compl (samples p n) {xs | UnambiguousAt C i (G xs).support}

def AchievesUnambiguousRate (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (R : ℕ → ℝ) : Prop :=
  ∀ i p, ValidDistribution C i p → ∃ D : ℝ, 0 < D ∧
    ∀ n, unambiguousError C G p i n ≤ D * R n

/-- The source's distribution-dependent horizontal and vertical scales.
A real-domain rate gives a precise meaning to `R (c * n)`. The no-rate
conclusion below also handles every vanishing natural-domain rate directly. -/
def AchievesScaledUnambiguousRate (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (R : ℝ → ℝ) : Prop :=
  ∀ i p, ValidDistribution C i p → ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
    ∀ n, unambiguousError C G p i n ≤ D * R (c * (n : ℝ))

/-- One fixed valid distribution witnesses a positive limsup error. -/
def NoUnambiguousRate (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator) : Prop :=
  ∃ i p, ValidDistribution C i p ∧
    0 < limsup (fun n => unambiguousError C G p i n) atTop

theorem unambiguousError_nonneg (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : 0 ≤ unambiguousError C G p i n := probability_nonneg _ _

theorem unambiguousError_le_one (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (p : PMF ℕ) (i n : ℕ) : unambiguousError C G p i n ≤ 1 := probability_le_one _ _

theorem unambiguousError_tendsto_zero_of_rate (C : Generic.LanguageFamily ℕ)
    (G : StatisticalGenerator) (R : ℕ → ℝ) (hG : AchievesUnambiguousRate C G R)
    (hR : Tendsto R atTop (𝓝 0)) (i : ℕ) (p : PMF ℕ) (hp : ValidDistribution C i p) :
    Tendsto (fun n => unambiguousError C G p i n) atTop (𝓝 0) := by
  obtain ⟨D, _, hb⟩ := hG i p hp
  apply squeeze_zero (unambiguousError_nonneg C G p i) hb
  simpa using tendsto_const_nhds.mul hR

theorem NoUnambiguousRate.excludes_rate {C : Generic.LanguageFamily ℕ} {G : StatisticalGenerator}
    (h : NoUnambiguousRate C G) (R : ℕ → ℝ) (hR : Tendsto R atTop (𝓝 0)) :
    ¬AchievesUnambiguousRate C G R := by
  intro hG
  obtain ⟨i, p, hp, hpos⟩ := h
  rw [(unambiguousError_tendsto_zero_of_rate C G R hG hR i p hp).limsup_eq] at hpos
  exact lt_irrefl _ hpos

theorem NoUnambiguousRate.excludes_scaled_rate {C : Generic.LanguageFamily ℕ} {G : StatisticalGenerator}
    (h : NoUnambiguousRate C G) (R : ℝ → ℝ) (hR : Tendsto R atTop (𝓝 0)) :
    ¬AchievesScaledUnambiguousRate C G R := by
  intro hG
  obtain ⟨i, p, hp, hpos⟩ := h
  obtain ⟨c, hc, D, _, hb⟩ := hG i p hp
  have hs : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n => unambiguousError C G p i n) atTop (𝓝 0) := by
    apply squeeze_zero (unambiguousError_nonneg C G p i) hb
    simpa using tendsto_const_nhds.mul (hR.comp hs)
  rw [he.limsup_eq] at hpos
  exact lt_irrefl _ hpos

end
end GenLimit.HallucinationModeCollapse
