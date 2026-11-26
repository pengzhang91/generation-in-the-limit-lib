import GenLimit.Paper25_PrivateGenerationAndIdentification.IdentificationBarrier
import GenLimit.Bridges.Paper03ToPaper08IID

/-! Necessity in Theorem 1.6. Causality turns the majority language under
the output marginal into a deterministic learner on finite input prefixes.
The least index for this language resolves duplicate hypotheses. -/
namespace GenLimit.PrivateLimit

open MeasureTheory Set Privacy HallucinationDetection
open scoped ENNReal Classical
noncomputable section

/-- Almost every IID stream yields almost-sure stabilization at one
correct index under the continual output law (Definition 7). -/
def IdentifiesStochastically (M : ContinualRelease ℕ ℕ) (C : LanguageFamily) : Prop :=
  ∀ z (p : PMF ℕ), p.support = C z →
    ∀ᵐ s ∂Measure.infinitePi (fun _ : ℕ => p.toMeasure),
      ∀ᵐ y ∂M.law s, ∃ j, C j = C z ∧ ∃ T, ∀ t ≥ T, y t = j

private def major (M : ContinualRelease ℕ ℕ) (C : LanguageFamily) (xs : List ℕ) (j : ℕ) : Prop :=
  1/2 < (M.law (Support.prependStream xs (fun _ => 0))).real {y | C (y (xs.length-1)) = C j}

private def majorityLearner (M : ContinualRelease ℕ ℕ) (C : LanguageFamily) (xs : List ℕ) : ℕ :=
  if h : ∃ j, major M C xs j then Nat.find h else 0

private theorem same_major {M : ContinualRelease ℕ ℕ} {C : LanguageFamily}
    {xs : List ℕ} {i j : ℕ} (hi : major M C xs i) (hj : major M C xs j) : C i = C j := by
  let μ := M.law (Support.prependStream xs fun _ => 0)
  letI : IsProbabilityMeasure μ := M.probability _
  let E (i : ℕ) := {y : ℕ → ℕ | C (y (xs.length-1)) = C i}
  change 1/2 < μ.real (E i) at hi
  change 1/2 < μ.real (E j) at hj
  by_contra ne
  have dis : E i ⊆ (E j)ᶜ := fun y hy hz => ne (hy.symm.trans hz)
  have m : MeasurableSet (E j) := by
    change MeasurableSet ((fun y : ℕ → ℕ => y (xs.length-1)) ⁻¹' {a | C a = C j})
    exact (measurable_pi_apply (xs.length-1)) (Set.to_countable _).measurableSet
  have upper := measureReal_mono (μ := μ) dis
  rw [measureReal_compl m,measureReal_univ_eq_one] at upper
  linarith

theorem stochastic_condition_necessary (C : LanguageFamily) (M : ContinualRelease ℕ ℕ)
    (ok : IdentifiesStochastically M C) : Angluin.ConditionTwo C := by
  apply (Bridge.Paper03ToPaper08IID.iid_detection_iff_conditionTwo C).mp
  apply (iid_detectable_iff_identifiable C).mpr
  refine ⟨majorityLearner M C,?_⟩
  intro z p hp
  filter_upwards [ok z p hp] with s hs
  let B := {j | C j = C z}
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  have stable : ∀ᵐ y ∂M.law s, ∃ T, ∀ t ≥ T, y t ∈ B := by
    filter_upwards [hs] with y hy
    obtain ⟨j,hj,T,ht⟩ := hy
    exact ⟨T,fun t h => (congrArg C (ht t h)).trans hj⟩
  obtain ⟨N,above⟩ := M.eventual_majority s hB stable
  have names : ∃ j, C j = C z := ⟨z,rfl⟩
  refine ⟨Nat.find names,Nat.find_spec names,N+1,?_⟩
  intro n hn
  let xs := textPrefix s n
  have len : xs.length = n := textPrefix_length s n
  have agree (k : ℕ) (hk : k ≤ n-1) : Support.prependStream xs (fun _ => 0) k = s k := by
    have hkn : k < n := by omega
    rw [Support.prependStream_apply_of_lt xs _ (len ▸ hkn)]
    simp [xs,textPrefix,List.get_eq_getElem]
  have eq := M.marginal_congr (n-1) agree hB
  have maj : major M C xs z := by
    unfold major; rw [len,Measure.real_def]
    change 1/2 < ((M.law _) {y | y (n-1) ∈ B}).toReal
    rw [eq]; exact above _ (by omega)
  have all : ∃ j, major M C xs j := ⟨z,maj⟩
  change majorityLearner M C xs = Nat.find names
  rw [majorityLearner,dif_pos all]
  apply le_antisymm
  · apply Nat.find_min' all
    simpa only [major,Nat.find_spec names] using maj
  · exact Nat.find_min' names (same_major (Nat.find_spec all) maj)

end
end GenLimit.PrivateLimit
