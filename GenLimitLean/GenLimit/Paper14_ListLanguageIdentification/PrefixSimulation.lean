import GenLimit.Paper14_ListLanguageIdentification.Definitions
import Mathlib.Data.Nat.Find

/-! # Simulating a stream transformation on finite histories

An output symbol may need more than one input symbol. A finite-history
learner feeds its inner learner the longest prefix already determined by
its observations, up to the current round. If every output coordinate is
eventually determined, the inner learner's permanent successes transfer.
-/
namespace GenLimit.ListIdentification.PrefixSimulation

def LocalAt (g : (ℕ → α) → ℕ → β) (s : ℕ → α) :=
  ∀ j, ∃ N, ∀ t : ℕ → α, (∀ i < N, t i = s i) → g t j = g s j

private def Ready (g : (ℕ → α) → ℕ → β) {n} (h : Fin n → α) (m : ℕ) :=
  ∃ u : Fin m → β, ∀ t : ℕ → α, (∀ i : Fin n, t i = h i) → ∀ j : Fin m, g t j = u j

private theorem ready_zero (g : (ℕ → α) → ℕ → β) {n} (h : Fin n → α) : Ready g h 0 :=
  ⟨Fin.elim0, fun _ _ j ↦ j.elim0⟩

private noncomputable def clock (g : (ℕ → α) → ℕ → β) {n} (h : Fin n → α) :=
  @Nat.findGreatest (Ready g h) (Classical.decPred _) n

private theorem clock_ready (g : (ℕ → α) → ℕ → β) {n} (h : Fin n → α) : Ready g h (clock g h) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le n) (ready_zero g h)

noncomputable def simulate (g : (ℕ → α) → ℕ → β)
    (D : Generic.FiniteHistoryOperator β γ) : Generic.FiniteHistoryOperator α γ :=
  fun _ h ↦ D (clock g h) (clock_ready g h).choose

theorem local_prefix {g : (ℕ → α) → ℕ → β} {s : ℕ → α} (hs : LocalAt g s) (m : ℕ) :
    ∃ N, ∀ t : ℕ → α, (∀ i < N, t i = s i) → ∀ j < m, g t j = g s j := by
  induction m with
  | zero => exact ⟨0, fun _ _ _ hj ↦ (Nat.not_lt_zero _ hj).elim⟩
  | succ m ih =>
    obtain ⟨N,hN⟩ := ih
    obtain ⟨K,hK⟩ := hs m
    refine ⟨max N K,fun t ht j hj ↦ ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | rfl
    · exact hN t (fun i hi ↦ ht i (hi.trans_le (le_max_left ..))) j h
    · exact hK t (fun i hi ↦ ht i (hi.trans_le (le_max_right ..)))

theorem eventual_simulation {g : (ℕ → α) → ℕ → β} {s : ℕ → α} (hl : LocalAt g s)
    {D : Generic.FiniteHistoryOperator β γ} {P : γ → Prop}
    (hd : ∃ T, ∀ m ≥ T, P (D m (fun i ↦ g s i))) :
    ∃ T, ∀ n ≥ T, P (simulate g D n (fun i ↦ s i)) := by
  classical
  obtain ⟨T,hT⟩ := hd
  obtain ⟨N,hN⟩ := local_prefix hl T
  refine ⟨max T N,fun n hn ↦ ?_⟩
  let h : Fin n → α := fun i ↦ s i
  have hr : Ready g h T := ⟨fun j ↦ g s j, fun t ht j ↦
    hN t (fun i hi ↦ ht ⟨i,hi.trans_le ((le_max_right ..).trans hn)⟩) j j.isLt⟩
  have hc : T ≤ clock g h := Nat.le_findGreatest ((le_max_left ..).trans hn) hr
  have hu : (clock_ready g h).choose = fun j : Fin (clock g h) ↦ g s j := by
    funext j
    exact ((clock_ready g h).choose_spec s (fun _ ↦ rfl) j).symm
  change P (D (clock g h) _)
  rw [hu]
  exact hT _ hc

end GenLimit.ListIdentification.PrefixSimulation
