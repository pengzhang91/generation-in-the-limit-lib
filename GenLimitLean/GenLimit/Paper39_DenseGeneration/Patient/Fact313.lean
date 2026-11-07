import GenLimit.Paper39_DenseGeneration.Patient.Pairing

/-!
# ArXiv v2 Fact 3.13

Both clauses of the source observation hold at every positive round, without
an eventual-validity hypothesis: a fresh adversary-first non-switch value is
in the preceding focus and strictly exceeds the preceding output. Strictness
strengthens the source's weak inequality using first-announcer novelty.
-/

namespace GenLimit.PatientMachine

/-- Fact 3.13, including preceding-focus membership. `hfresh` specifies the
first occurrence if the presentation repeats a value. -/
theorem fact_3_13
    (O : OracleFamily) (stream : ℕ → ℕ) {t : ℕ}
    (ht : 0 < t)
    (hattacker : stream t ∈ AdversaryFirst stream (output O stream))
    (hfresh : stream t ∉ sample stream t)
    (hnotSwitch : ¬ SwitchRound O stream t) :
    stream t ∈ O.language (run O stream t).focus ∧
      output O stream (t - 1) < stream t := by
  have hfocus : stream t ∈ O.language (run O stream t).focus := by
    by_contra hout
    exact hnotSwitch hout
  refine ⟨hfocus, ?_⟩
  have havailable : Available O.language stream t
      (run O stream (t - 1)).used (run O stream t).focus (stream t) :=
    ⟨hfocus, hfresh, fresh_attacker_not_mem_used O stream hattacker hfresh⟩
  exact lt_of_le_of_ne (previous_output_le O stream ht havailable)
    (no_output_before_fresh_attacker O stream hattacker hfresh
      (t - 1) (Nat.sub_lt ht Nat.zero_lt_one))

end GenLimit.PatientMachine
