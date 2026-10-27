import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalModel
import GenLimit.Paper00_LanguageIdentification.Informant.Model

/-!
# Labeled IID identification (Definition 16)

We reuse Gold's Boolean informant data and compatibility predicate. Validity
means exactly one correctly labeled atom above every domain point has positive
mass. Equivalently, labels are deterministic and correct and the domain
marginal has full support. Loss compares languages, allowing duplicate names.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.DiscreteIID GenLimit.Gold.Informant

abbrev LabeledDatum := InformantDatum
abbrev LabeledIdentifier := List LabeledDatum → PMF ℕ

def CorrectLabel (C : Generic.LanguageFamily ℕ) (i : ℕ) (z : LabeledDatum) : Prop :=
  z.2 = true ↔ z.1 ∈ C i

def ValidLabeledDistribution (C : Generic.LanguageFamily ℕ) (i : ℕ)
    (p : PMF LabeledDatum) : Prop :=
  p.support = {z | CorrectLabel C i z}

/-- Definition 16 expressed as full marginal support and deterministic labels. -/
theorem validLabeledDistribution_iff (C : Generic.LanguageFamily ℕ) (i : ℕ)
    (p : PMF LabeledDatum) :
    ValidLabeledDistribution C i p ↔
      (p.map Prod.fst).support = Set.univ ∧ ∀ z ∈ p.support, CorrectLabel C i z := by
  classical
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    swap
    · intro z hz
      change z ∈ {z | CorrectLabel C i z}
      rw [← hp]
      exact hz
    apply Set.eq_univ_of_forall
    intro x
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨(x, decide (x ∈ C i)), ?_, rfl⟩
    rw [hp]
    simp [CorrectLabel]
  · rintro ⟨hm, hs⟩
    apply Set.ext
    intro z
    constructor
    · exact hs z
    · intro hz
      have hx : z.1 ∈ (p.map Prod.fst).support := by rw [hm]; trivial
      obtain ⟨w, hw, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      have hc := hs w hw
      change w.2 = true ↔ w.1 ∈ C i at hc
      rw [he] at hc
      have hb : w.2 = z.2 := Bool.eq_iff_iff.mpr (hc.trans hz.symm)
      have hwz : w = z := Prod.ext he hb
      exact hwz ▸ hw

noncomputable def deterministicLabeledIdentifier (A : List LabeledDatum → ℕ) : LabeledIdentifier :=
  fun xs => PMF.pure (A xs)

noncomputable def labeledIdentificationError (C : Generic.LanguageFamily ℕ) (A : LabeledIdentifier)
    (p : PMF LabeledDatum) (i n : ℕ) : ℝ :=
  probability ((samples p n).bind A) {j | C j ≠ C i}

def ExponentialLabeledIdentifies (C : Generic.LanguageFamily ℕ) (A : LabeledIdentifier) : Prop :=
  ∀ i p, ValidLabeledDistribution C i p →
    ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
      ∀ n : ℕ, labeledIdentificationError C A p i n ≤ D * Real.exp (-c * n)

def FiniteLabeledWitnessIdentifies (C : Generic.LanguageFamily ℕ)
    (A : List LabeledDatum → ℕ) : Prop :=
  ∀ i, ∃ T : Finset LabeledDatum, (∀ z ∈ T, CorrectLabel C i z) ∧ ∃ N : ℕ,
    ∀ xs : List LabeledDatum, N ≤ xs.length → InformantCompatible xs (C i) →
      (∀ z ∈ T, z ∈ xs) → C (A xs) = C i

theorem labeledIdentificationError_deterministic (C : Generic.LanguageFamily ℕ)
    (A : List LabeledDatum → ℕ) (p : PMF LabeledDatum) (i n : ℕ) :
    labeledIdentificationError C (deterministicLabeledIdentifier A) p i n =
      probability (samples p n) {xs | C (A xs) ≠ C i} := by
  unfold labeledIdentificationError deterministicLabeledIdentifier probability
  change (((samples p n).map A).toOuterMeasure {j | C j ≠ C i}).toReal = _
  rw [PMF.toOuterMeasure_map_apply]
  rfl

end GenLimit.HallucinationModeCollapse
