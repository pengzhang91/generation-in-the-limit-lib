import GenLimit.Paper14_ListLanguageIdentification.InfiniteDraws
import Mathlib.Analysis.SpecificLimits.Basic

namespace GenLimit.ListIdentification.InfiniteDraws
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Any positive-probability event is eventually observed under independent draws. -/
theorem ae_some {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {H : Set α} (hm : MeasurableSet H) (hp : 0 < μ H) :
    ∀ᵐ x ∂iid μ, ∃ j : ℕ, x j ∈ H := by
  rw [ae_iff]
  apply le_antisymm _ (zero_le _)
  have hlt : μ Hᶜ < 1 := lt_of_le_of_ne (prob_le_one)
    (fun h ↦ hp.ne' ((prob_compl_eq_one_iff hm).mp h))
  apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt)
  intro n
  let box := (Finset.range n : Set ℕ).pi (fun _ ↦ Hᶜ)
  have sub : {x : ℕ → α | ¬ ∃ j, x j ∈ H} ⊆ box :=
    fun _ hx j _ hj ↦ hx ⟨j,hj⟩
  calc
    _ ≤ iid μ box := measure_mono sub
    _ = _ := by
      change Measure.infinitePi (fun _ : ℕ ↦ μ) ((Finset.range n : Set ℕ).pi _) = _
      rw [Measure.infinitePi_pi _ (fun _ _ ↦ hm.compl)]
      simp

private def test (Q : ℕ → Prop) (j : ℕ) := Q j ∨ (¬ ∃ i, Q i) ∧ j = 0

private theorem hasTest (Q : ℕ → Prop) : ∃ j, test Q j := by
  by_cases h : ∃ j, Q j
  · exact ⟨h.choose,Or.inl h.choose_spec⟩
  · exact ⟨0,Or.inr ⟨h,rfl⟩⟩

noncomputable def first (Q : ℕ → Prop) : ℕ := @Nat.find _ (Classical.decPred _) (hasTest Q)

theorem first_spec {Q : ℕ → Prop} (h : ∃ j, Q j) : Q (first Q) := by
  classical
  exact (Nat.find_spec (hasTest Q)).elim id (fun e ↦ (e.1 h).elim)

theorem first_le {Q : ℕ → Prop} {j} (h : Q j) : first Q ≤ j := by
  classical
  exact Nat.find_min' (hasTest Q) (Or.inl h)

theorem first_eq {Q : ℕ → Prop} {j} (h : Q j) (hn : ∀ i < j, ¬ Q i) : first Q = j :=
  le_antisymm (first_le h) (le_of_not_gt fun hlt ↦ hn _ hlt (first_spec ⟨j,h⟩))

theorem measurable_first {X : Type*} [MeasurableSpace X] {Q : X → ℕ → Prop}
    (hm : ∀ j, MeasurableSet {x | Q x j}) : Measurable (fun x ↦ first (Q x)) := by
  classical
  apply measurable_find (fun x ↦ hasTest (Q x))
  intro j
  have hex : MeasurableSet {x | ∃ i, Q x i} := by
    simpa only [setOf_exists] using MeasurableSet.iUnion hm
  by_cases h : j = 0
  · subst j
    convert (hm 0).union hex.compl using 1
    ext x
    simp [test]
  · convert hm j using 1
    ext x
    simp [test,h]

noncomputable abbrev coin := (PMF.uniformOfFintype Bool).toMeasure

theorem coin_pos (b : Bool) : 0 < coin {b} := by
  rw [PMF.toMeasure_apply_singleton _ b (measurableSet_singleton _), PMF.uniformOfFintype_apply]
  simp

noncomputable def bitIndex (b : ℕ → Bool) := first fun j ↦ b j = true

theorem measurable_bitIndex : Measurable bitIndex := by
  have hm (j : ℕ) : Measurable (fun x : ℕ → Bool ↦ x j) := measurable_pi_apply j
  exact measurable_first (fun j ↦ hm j (measurableSet_singleton true))

theorem ae_true : ∀ᵐ x ∂iid coin, ∃ j : ℕ, x j = true :=
  ae_some (α := Bool) coin (H := {true}) (measurableSet_singleton true) (coin_pos true)

/-- Every possible first-success index has positive probability. -/
theorem index_pos (j : ℕ) : 0 < iid coin {x | bitIndex x = j} := by
  let t (i : ℕ) : Set Bool := {decide (i = j)}
  let S := Finset.range (j+1)
  have hsub : (S : Set ℕ).pi t ⊆ {x | bitIndex x = j} := by
    intro x hx
    apply first_eq
    · simpa [t] using (hx (i := j) (by simp [S]))
    · intro i hi
      have h := hx (i := i) (Finset.mem_range.mpr (by omega))
      simpa [t,hi.ne] using h
  apply lt_of_lt_of_le _ (measure_mono hsub)
  change 0 < Measure.infinitePi (fun _ : ℕ ↦ coin) ((S : Set ℕ).pi t)
  rw [Measure.infinitePi_pi _ (fun _ _ ↦ measurableSet_singleton _)]
  exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ (coin_pos _).ne'))

end GenLimit.ListIdentification.InfiniteDraws
