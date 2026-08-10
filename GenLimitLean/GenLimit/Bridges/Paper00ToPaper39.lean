import GenLimit.Bridges.Paper00ToPaper01
import GenLimit.Paper39_DenseGeneration.Patient.Main

/-!
# #0 Language Identification to #39 Dense Generation

This semantic bridge instantiates the deterministic patient-scope theorem on
the co-singleton family used for the #0/#01 separation. Thus the same
uniformly decidable countable family of infinite languages that cannot be
identified from arbitrary positive text admits a run with eventual validity,
adversary freshness through the current round, no repeated generator output,
and target-relative lower density at least `1 / 2`.
-/

namespace GenLimit
namespace GoldDenseSeparation

open GoldKMSeparation

/-- Patient Scope gives both #39-style novelty and its target-
relative lower-density bound on every exact text for a co-singleton target. -/
theorem coSingleton_patientScope_generation_and_lowerDensity
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (coSingletonOracle.language z)) :
    NovelGeneratesInLimit stream
        (PatientMachine.output coSingletonOracle stream)
        (coSingletonOracle.language z) ∧
      (1 / 2 : ℝ) ≤
        PatientMachine.patientLowerDensity coSingletonOracle stream z := by
  obtain ⟨hgeneration, hdensity⟩ :=
    PatientMachine.patientScope_generation_and_lowerDensity
      coSingletonOracle stream hP
  refine ⟨?_, hdensity⟩
  obtain ⟨T, hT⟩ := hgeneration
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hvalid, hadversary, hnovel⟩ := hT t ht
  refine ⟨hvalid, ?_, hnovel⟩
  intro hsample
  rw [mem_sample_iff] at hsample
  obtain ⟨s, hst, hs⟩ := hsample
  exact hadversary s (Nat.lt_succ_iff.mp hst) hs

/-- The trace-level novelty conclusion of Patient Scope on the co-singleton
family. -/
theorem coSingleton_patientScope_novelGenerates
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (coSingletonOracle.language z)) :
    NovelGeneratesInLimit stream
      (PatientMachine.output coSingletonOracle stream)
      (coSingletonOracle.language z) :=
  (coSingleton_patientScope_generation_and_lowerDensity hP).1

/-- The operational Patient Scope run achieves target-relative lower density
at least one half on every co-singleton target. -/
theorem coSingleton_patientScope_lowerDensity_half
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (coSingletonOracle.language z)) :
    (1 / 2 : ℝ) ≤
      PatientMachine.patientLowerDensity coSingletonOracle stream z :=
  (coSingleton_patientScope_generation_and_lowerDensity hP).2

/-- Same-family separation strengthened from #01 freshness to deterministic
dense generation with output novelty and a quantitative lower bound. -/
theorem dense_generation_without_identification :
    (¬ Gold.Text.SemanticallyIdentifiable coSingletonClass) ∧
      ∀ z stream,
        Presents stream (coSingletonOracle.language z) →
          NovelGeneratesInLimit stream
              (PatientMachine.output coSingletonOracle stream)
              (coSingletonOracle.language z) ∧
            (1 / 2 : ℝ) ≤
              PatientMachine.patientLowerDensity
                coSingletonOracle stream z := by
  exact ⟨coSingleton_not_semanticallyIdentifiable,
    fun _ _ hP => coSingleton_patientScope_generation_and_lowerDensity hP⟩

end GoldDenseSeparation
end GenLimit
