import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.DeterministicDiagonal
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Proposition A.2. A deterministic presentation defeating a randomized generator

The random tape may be shared across rounds. The stream depends only on the
output laws on finite histories. A summable geometric bound suffices for the
first Borel–Cantelli lemma, which requires no independence of the outputs.
-/
namespace GenLimit.UnionClosedness

open MeasureTheory Filter GenLimit.Generic
open scoped ENNReal Topology

private theorem exists_tail_cutoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℕ) (hY : Measurable Y) (t : ℕ) :
    ∃ k : ℕ, μ {ω | k < Y ω} ≤ (2⁻¹ : ℝ≥0∞) ^ t := by
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun k : ℕ ↦ {ω | k < Y ω})
    (fun k ↦ (hY (MeasurableSet.of_discrete (s := Set.Ioi k))).nullMeasurableSet)
    (fun _ _ hab _ hw ↦ hab.trans_lt hw) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ k : ℕ, {ω | k < Y ω}) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hall ↦ (lt_irrefl _ (hall (Y ω)))
  rw [he, measure_empty] at h
  have hev := h.eventually_lt_const (show (0 : ℝ≥0∞) < 2⁻¹ ^ t from (pow_ne_zero t (by norm_num)).bot_lt)
  obtain ⟨k, hk⟩ := hev.exists
  exact ⟨k, hk.le⟩

/-- Proposition A.2 in random-tape form. For every measurable randomized
algorithm there is a fixed injective exact presentation of an infinite
target on which, almost surely, only finitely many rounds succeed. -/
theorem proposition_A_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : (t : ℕ) → (Fin t → ℕ) → Ω → ℕ)
    (hG : ∀ t xs, Measurable (G t xs)) :
    ∃ K ∈ allInfiniteNatLanguages, ∃ E : ℕ → ℕ, Function.Injective E ∧ Presents E K ∧
      ∀ᵐ ω ∂μ, {t : ℕ | G t (fun i ↦ E i) ω ∈ K \ (sample E t : Set ℕ)}.Finite := by
  classical
  let cutoff : Generic.Generator ℕ := fun t xs ↦
    (exists_tail_cutoff μ (G t xs) (hG t xs) t).choose
  let E := deterministicDiagonalStream cutoff
  let good (t : ℕ) := {ω | G t (fun i ↦ E i) ω ∈ Set.range E \ (sample E t : Set ℕ)}
  have hp (t : ℕ) (ht : 0 < t) : μ (good t) ≤ (2⁻¹ : ℝ≥0∞) ^ t := by
    apply le_trans (measure_mono _) (exists_tail_cutoff μ (G t (fun i ↦ E i)) (hG _ _) t).choose_spec
    rintro ω ⟨⟨k, hk⟩, hfresh⟩
    have htk : t ≤ k := by
      by_contra! hbad
      exact hfresh (mem_sample_iff.mpr ⟨k,hbad,hk⟩)
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    exact (deterministicDiagonal_output_lt cutoff j).trans_le
      (((deterministicDiagonalStream_strictMono cutoff).monotone htk).trans hk.le)
  have hsum : (∑' t, μ (good t)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ∑' t : ℕ, (2⁻¹ : ℝ≥0∞) ^ t)
    · simp
    · apply ENNReal.tsum_le_tsum
      intro t
      cases t with
      | zero => simpa using prob_le_one (μ := μ) (s := good 0)
      | succ t => exact hp _ (Nat.zero_lt_succ _)
  exact ⟨Set.range E, deterministicDiagonalTarget_infinite cutoff,
    E, deterministicDiagonalStream_injective cutoff, rfl, ae_finite_setOf_mem hsum⟩

/-- The paper's distribution-valued interface. One product coordinate samples
each finite history from its prescribed law. Along a fixed presentation the
queried coordinates have distinct lengths. -/
abbrev RandomizedHistory := (t : ℕ) × (Fin t → ℕ)

noncomputable def historyOutputLaw (G : (t : ℕ) → (Fin t → ℕ) → PMF ℕ) :
    Measure (RandomizedHistory → ℕ) :=
  Measure.infinitePi (fun h : RandomizedHistory ↦ (G h.1 h.2).toMeasure)

theorem historyOutputLaw_marginal (G : (t : ℕ) → (Fin t → ℕ) → PMF ℕ)
    (h : RandomizedHistory) :
    (historyOutputLaw G).map (Function.eval h) = (G h.1 h.2).toMeasure :=
  (measurePreserving_eval_infinitePi (fun h : RandomizedHistory ↦ (G h.1 h.2).toMeasure) h).map_eq

theorem proposition_A_2_pmf (G : (t : ℕ) → (Fin t → ℕ) → PMF ℕ) :
    ∃ K ∈ allInfiniteNatLanguages, ∃ E : ℕ → ℕ, Function.Injective E ∧ Presents E K ∧
      ∀ᵐ outputs ∂historyOutputLaw G,
        {t : ℕ | outputs ⟨t, fun i ↦ E i⟩ ∈ K \ (sample E t : Set ℕ)}.Finite := by
  letI : IsProbabilityMeasure (historyOutputLaw G) := by unfold historyOutputLaw; infer_instance
  exact proposition_A_2 (historyOutputLaw G) (fun t xs ↦ Function.eval (⟨t,xs⟩ : RandomizedHistory))
    (fun _ _ ↦ measurable_pi_apply _)

end GenLimit.UnionClosedness
