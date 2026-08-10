import GenLimit.Paper39_DenseGeneration.Partial.Critical
import GenLimit.Paper39_DenseGeneration.Patient.Validity

/-!
# Lemma 3.16: validity under partial enumeration

The scope-growth proof is stated against an arbitrary presented set `E` and
an on-model run.  It therefore reuses the patient-scope recurrence without
pretending that `E` is itself one of the transformed languages.
-/

namespace GenLimit
namespace PartialEnumeration

/-- Lemma 3.16: patient-scope over the filtered finite-intersection closure
eventually outputs only elements of the true language. -/
theorem lemma_3_16_validity
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hE : E.Infinite)
    (hsub : E ⊆ O.language z) :
    ∃ T, ∀ t, T ≤ t →
      PatientMachine.output (closure O) stream t ∈ O.language z := by
  obtain ⟨w, Tc, hwTarget, hcrit⟩ :=
    exists_eventually_critical_subset_target O hP hE hsub
  have hOn := closure_onModel O hP hsub
  obtain ⟨Ts, hscope⟩ :=
    PatientMachine.critical_witness_eventually_in_scope
      (closure O) stream hP hOn hcrit
  refine ⟨max Tc Ts, ?_⟩
  intro t ht
  have ht' : max Tc Ts ≤ t + 1 := le_trans ht (Nat.le_succ t)
  have hfocus :=
    PatientMachine.run_focus_isFocus_of_onModel (closure O) hOn (t + 1)
  have hfocusSub :
      (closure O).language
          (PatientMachine.run (closure O) stream (t + 1)).focus ⊆
        (closure O).language w :=
    focus_subset_target hfocus
      (hscope (t + 1) (le_trans (Nat.le_max_right _ _) ht'))
      (hcrit (t + 1) (le_trans (Nat.le_max_left _ _) ht'))
  exact hwTarget
    (hfocusSub
      (PatientMachine.output_mem_run_succ_focus (closure O) stream t))

/-- Lemma 3.16 together with the standard novelty guarantees of the semantic
patient-scope machine. -/
theorem lemma_3_16_generation
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hE : E.Infinite)
    (hsub : E ⊆ O.language z) :
    ∃ T, ∀ t, T ≤ t →
      PatientMachine.output (closure O) stream t ∈ O.language z ∧
      (∀ s, s ≤ t →
        stream s ≠ PatientMachine.output (closure O) stream t) ∧
      (∀ s, s < t →
        PatientMachine.output (closure O) stream s ≠
          PatientMachine.output (closure O) stream t) := by
  obtain ⟨T, hvalid⟩ := lemma_3_16_validity O hP hE hsub
  refine ⟨T, ?_⟩
  intro t ht
  exact ⟨hvalid t ht,
    PatientMachine.stream_ne_output (closure O) stream t,
    fun s hs => PatientMachine.output_ne_of_lt (closure O) stream hs⟩

end PartialEnumeration
end GenLimit
