import GenLimit.KM.FiniteQuery.Selection
import Mathlib.Order.Interval.Finset.Nat

/-!
# Termination of one search round

This is the zero-based form of the Proceedings algorithm. A cutoff `q` means
that membership has been inspected below `q`; the newly reached element is
`q - 1`. The search stops when that endpoint belongs to the currently selected
finite-critical language.
-/

namespace GenLimit
namespace OracleFamily

variable (O : OracleFamily)

def Stop
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t) (q : ℕ) : Prop :=
  O.query (O.selected stream t q h) (q - 1) = true

instance stopDecidable
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t) (q : ℕ) :
    Decidable (O.Stop stream t h q) := by
  unfold Stop
  infer_instance

/-- Equation (5.5): the endpoint search terminates at every round having a
consistent candidate. -/
theorem stop_exists
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    ∃ q, b < q ∧ O.Stop stream t h q := by
  obtain ⟨M, hM⟩ := O.selected_eventually_constant h
  let n := O.selected stream t M h
  obtain ⟨e, he, hbe⟩ := (O.infinite' n).exists_gt (max b M)
  have hMe : M < e := lt_of_le_of_lt (Nat.le_max_right b M) hbe
  have hMq : M ≤ e + 1 :=
    le_trans (Nat.le_of_lt hMe) (Nat.le_succ e)
  refine ⟨e + 1, lt_trans (lt_of_le_of_lt (Nat.le_max_left b M) hbe)
    (Nat.lt_succ_self e), ?_⟩
  unfold Stop
  rw [hM (e + 1) hMq, Nat.succ_sub_one]
  exact (O.query_spec n e).mpr he

/-- The first stopping cutoff strictly after `b`. -/
def roundCounter
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t) (b : ℕ) : ℕ :=
  Nat.find (O.stop_exists h b)

theorem roundCounter_spec
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    b < O.roundCounter stream t h b ∧
      O.Stop stream t h (O.roundCounter stream t h b) := by
  exact Nat.find_spec (O.stop_exists h b)

theorem roundCounter_gt
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    b < O.roundCounter stream t h b :=
  (O.roundCounter_spec h b).1

theorem roundCounter_output_mem_selectedPrefix
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    O.roundCounter stream t h b - 1 ∈
      O.finitePrefix
        (O.selected stream t (O.roundCounter stream t h b) h)
        (O.roundCounter stream t h b) := by
  let q := O.roundCounter stream t h b
  have hspec := O.roundCounter_spec h b
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le b) hspec.1
  apply O.mem_finitePrefix.mpr
  refine ⟨Nat.sub_one_lt (Nat.ne_of_gt hqpos), ?_⟩
  exact (O.query_spec (O.selected stream t q h) (q - 1)).mp hspec.2

end OracleFamily
end GenLimit
