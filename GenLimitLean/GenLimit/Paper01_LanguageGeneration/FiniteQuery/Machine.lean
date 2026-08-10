import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Round

/-!
# The finite-query stateful generator

The machine stores a strict cutoff and the most recent output. Before round
`t + 1`, the cutoff is raised above the new observation `stream t`; a successful
search then raises it again. This gives the freshness invariant required by the
corrected form of equation (5.6).
-/

namespace GenLimit
namespace OracleFamily

variable (O : OracleFamily)

structure MachineState where
  counter : ℕ
  output : ℕ
deriving Repr

def processRound
    (stream : ℕ → ℕ) (t b : ℕ) : MachineState :=
  if h : O.HasConsistent stream t then
    let q := O.roundCounter stream t h b
    ⟨q, q - 1⟩
  else
    ⟨b, 0⟩

theorem processRound_counter_ge_start
    (stream : ℕ → ℕ) (t b : ℕ) :
    b ≤ (O.processRound stream t b).counter := by
  unfold processRound
  split
  · exact Nat.le_of_lt (O.roundCounter_gt _ b)
  · exact Nat.le_refl b

theorem processRound_of_hasConsistent
    {stream : ℕ → ℕ} {t b : ℕ} (h : O.HasConsistent stream t) :
    O.processRound stream t b =
      ⟨O.roundCounter stream t h b,
        O.roundCounter stream t h b - 1⟩ := by
  simp [processRound, h]

/-- The state after the first `t` observations and rounds. -/
def run (O : OracleFamily) (stream : ℕ → ℕ) : ℕ → MachineState
  | 0 => ⟨0, 0⟩
  | t + 1 =>
      let previous := run O stream t
      let start := max previous.counter (stream t + 1)
      O.processRound stream (t + 1) start

theorem run_succ_counter_ge_start
    (stream : ℕ → ℕ) (t : ℕ) :
    max (O.run stream t).counter (stream t + 1) ≤
      (O.run stream (t + 1)).counter := by
  simpa [run] using O.processRound_counter_ge_start stream (t + 1)
    (max (O.run stream t).counter (stream t + 1))

/-- Every observation processed by time `t` lies strictly below the stored
cutoff. -/
theorem run_counter_bounds
    {stream : ℕ → ℕ} :
    ∀ {t k}, k < t → stream k < (O.run stream t).counter := by
  intro t
  induction t with
  | zero =>
      intro k hk
      exact False.elim (Nat.not_lt_zero k hk)
  | succ t ih =>
      intro k hk
      have hstart := O.run_succ_counter_ge_start stream t
      have hkstart :
          stream k < max (O.run stream t).counter (stream t + 1) := by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkt | rfl
        · exact lt_of_lt_of_le (ih hkt) (Nat.le_max_left _ _)
        · exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
      exact lt_of_lt_of_le hkstart hstart

/-- Every item in the current sample is below the cutoff at which the current
round begins. -/
theorem sample_lt_roundStart
    {stream : ℕ → ℕ} {t u : ℕ} (hu : u ∈ sample stream (t + 1)) :
    u < max (O.run stream t).counter (stream t + 1) := by
  rw [mem_sample_iff] at hu
  obtain ⟨k, hk, hku⟩ := hu
  rw [← hku]
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkt | rfl
  · exact lt_of_lt_of_le (O.run_counter_bounds hkt) (Nat.le_max_left _ _)
  · exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

/-- Corrected equation (5.6): at every successful round the output lies in the
selected finite prefix and is fresh. The selected candidate is maximal among
all finite-critical candidates below `t`. -/
theorem run_round_spec
    {stream : ℕ → ℕ} {t : ℕ} (ht : 0 < t)
    (h : O.HasConsistent stream t) :
    ∃ n,
      n < t ∧
      FinitelyCritical O.language stream t (O.run stream t).counter n ∧
      (∀ j, j < t →
        FinitelyCritical O.language stream t (O.run stream t).counter j →
        j ≤ n) ∧
      (O.run stream t).output ∈
        O.finitePrefix n (O.run stream t).counter ∧
      (O.run stream t).output ∉ sample stream t := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  let b := max (O.run stream s).counter (stream s + 1)
  let q := O.roundCounter stream (s + 1) h b
  have hrun : O.run stream (s + 1) = ⟨q, q - 1⟩ := by
    rw [run]
    exact O.processRound_of_hasConsistent h
  let n := O.selected stream (s + 1) q h
  refine ⟨n, ?_, ?_, ?_, ?_, ?_⟩
  · exact O.selected_lt h
  · rw [hrun]
    exact O.selected_finitelyCritical h
  · intro j hjt hjfc
    rw [hrun] at hjfc
    exact O.selected_max h hjt (O.finitelyCriticalAt_iff.mpr hjfc)
  · rw [hrun]
    exact O.roundCounter_output_mem_selectedPrefix h b
  · rw [hrun]
    intro hout
    have houtlt : q - 1 < b := by
      exact O.sample_lt_roundStart hout
    have hbq : b < q := O.roundCounter_gt h b
    have hbout : b ≤ q - 1 := Nat.le_sub_one_of_lt hbq
    exact (Nat.not_lt_of_ge hbout) houtlt

end OracleFamily
end GenLimit
