import GenLimit.Support.OracleSearchProgram

/-! # A successful first stage determines an oracle-search result -/

namespace GenLimit.Support.OracleSearchProgram

theorem run_eq_of_stage_zero (P : OracleSearchProgram) (oracle : ℕ → ℕ)
    (h : P.Terminates oracle) (xs : List ℕ) (y : ℕ)
    (hy : P.stage oracle xs 0 = some y) : P.run oracle h xs = y := by
  have hz : 0 ∈ Nat.rfind (fun n => ((P.stage oracle xs n).isSome : Part Bool)) := by
    apply Nat.mem_rfind.mpr
    exact ⟨by simp [hy], fun {m} hm => (Nat.not_lt_zero m hm).elim⟩
  have he : P.partialRun oracle xs = Part.some y := by
    unfold partialRun Nat.rfindOpt
    rw [Part.eq_some_iff.mpr hz]
    simp [hy]
  exact Part.mem_unique (Part.get_mem (P.run_dom oracle h xs))
    (Part.eq_some_iff.mp he)

end GenLimit.Support.OracleSearchProgram
