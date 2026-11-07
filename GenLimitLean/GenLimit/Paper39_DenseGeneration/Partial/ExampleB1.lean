import GenLimit.Paper39_DenseGeneration.Partial.Counterexample
import GenLimit.Paper39_DenseGeneration.Patient.Main

/-!
# ArXiv v2 Example B.1: zero density and failure of validity

The increasing multiples-of-four enumeration and odd-output trace are proved
in `Counterexample`. Here the same trace is connected to the operational
lower-density metric used in Theorem 3.15.
-/

namespace GenLimit.PartialEnumeration.Counterexample

open PatientMachine

theorem generatorFirst_inter_target_eq_empty :
    GeneratorFirst stream (output oracle stream) ∩ trueLanguage = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨⟨t, rfl, _⟩, hx⟩
  exact output_not_mem_trueLanguage t hx

/-- The untransformed patient-scope machine has zero target-relative density
on the partial presentation in Example B.1. -/
theorem lowerDensity_eq_zero : patientLowerDensity oracle stream 1 = 0 := by
  change PatientScope.relativeLowerDensity
    (GeneratorFirst stream (output oracle stream) ∩ trueLanguage) trueLanguage
      (oracle.infinite' 1) = 0
  rw [generatorFirst_inter_target_eq_empty]
  rw [PatientScope.relativeLowerDensity_eq_liminf _ trueLanguage (oracle.infinite' 1)
    (Set.empty_subset _)]
  simp [PatientScope.prefixCount, PatientScope.prefixFinset]

/-- Full counterexample endpoint: an infinite partial presentation of the
target, the exact odd outputs, failure of eventual validity, and zero density. -/
theorem example_B_1 :
    Presents stream enumeratedLanguage ∧ enumeratedLanguage.Infinite ∧
    enumeratedLanguage ⊆ trueLanguage ∧
    (∀ t, output oracle stream t = 2 * t + 1) ∧
    (¬ ∃ T, ∀ t, T ≤ t → output oracle stream t ∈ trueLanguage) ∧
    patientLowerDensity oracle stream 1 = 0 := by
  refine ⟨presents_enumeratedLanguage, enumeratedLanguage_infinite,
    enumeratedLanguage_subset_trueLanguage, output_eq_odd, ?_, lowerDensity_eq_zero⟩
  rintro ⟨T, hT⟩
  exact output_not_mem_trueLanguage T (hT T le_rfl)

end GenLimit.PartialEnumeration.Counterexample
