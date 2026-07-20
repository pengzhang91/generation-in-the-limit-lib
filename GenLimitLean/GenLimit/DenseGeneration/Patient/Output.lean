import GenLimit.DenseGeneration.Patient.MachineInvariant

/-!
# Output facts for the semantic patient-scope machine

The round-`t` output is the least value available in the focus stored in the
post-round state `run (t + 1)`.  These indexing lemmas isolate that fact for
the predecessor comparison in Fact 3.12.
-/

namespace GenLimit
namespace PatientMachine

theorem output_available_post_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    Available O.language stream (t + 1) (run O stream t).used
      (run O stream (t + 1)).focus (output O stream t) := by
  simpa using output_available O stream t

theorem output_minimal_post_focus
    (O : OracleFamily) (stream : ℕ → ℕ) (t x : ℕ)
    (hx : Available O.language stream (t + 1) (run O stream t).used
      (run O stream (t + 1)).focus x) :
    output O stream t ≤ x := by
  rw [output_eq_leastAvailable]
  rw [run_succ_focus] at hx
  exact leastAvailable_minimal O.language O.infinite' stream (t + 1)
    (run O stream t).used
    (decide O.language stream t (run O stream t)).focus x hx

/-- The previous-round form used by Fact 3.12. -/
theorem previous_output_le
    (O : OracleFamily) (stream : ℕ → ℕ) {t x : ℕ}
    (ht : 0 < t)
    (hx : Available O.language stream t (run O stream (t - 1)).used
      (run O stream t).focus x) :
    output O stream (t - 1) ≤ x := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simpa using output_minimal_post_focus O stream s x hx

end PatientMachine
end GenLimit
