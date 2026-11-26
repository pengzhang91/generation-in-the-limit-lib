import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-! The logarithmic bound for one phase of the finite-rank interval game
(Claim 4.24). Coordinates are ranks in the current fixed visibility set,
translated so the interior ranks lie in [1,ℓ]. At a leak the algorithm
minimizes distance among the available ranks, including at least one
interior rank. A later leak input and a later chosen output were both
available at the earlier leak. -/
namespace GenLimit.KleinbergWei.Banach.IntervalGame

open Set

/-- Each left leak more than doubles the previous leak distance. At the
last leak there is still an available interior candidate, so the distance
is at most ℓ−1. The resulting integer bound is 2^k ≤ ℓ. -/
theorem left_leak_bound (k len : ℕ) (positive : 0 < len)
    (a o : ℕ → ℤ) (available : ℕ → Set ℤ)
    (input : ∀ i < k, 1 ≤ a i ∧ a i ≤ len) (left : ∀ i < k, o i ≤ 0)
    (inside : ∀ i < k, ∃ v ∈ available i, 1 ≤ v ∧ v ≤ len)
    (greedy : ∀ i < k, ∀ v ∈ available i, |a i-o i| ≤ |a i-v|)
    (future : ∀ i, i+1 < k → a (i+1) ∈ available i ∧ o (i+1) ∈ available i)
    (distinct : ∀ i, i+1 < k → o (i+1) ≠ o i) : 2^k ≤ len := by
  have dist (i : ℕ) (hi : i < k) : |a i-o i| = a i-o i :=
    abs_of_nonneg (by have := (input i hi).1; have := left i hi; omega)
  have growth (i : ℕ) (hi : i+1 < k) :
      2*(a i-o i)+1 ≤ a (i+1)-o (i+1) := by
    have bound : i < k := by omega
    obtain ⟨inputNext,outputNext⟩ := future i hi
    have a_near := greedy i bound _ inputNext
    have o_near := greedy i bound _ outputNext
    have ai := (input i bound).1; have aj := (input (i+1) hi).1
    have oi := left i bound; have oj := left (i+1) hi
    rw [dist i bound] at a_near o_near
    rw [abs_of_nonneg (by omega : 0 ≤ a i-o (i+1))] at o_near
    have ne := distinct i hi
    by_cases sorted : a i < a (i+1)
    · rw [abs_of_nonpos (by omega : a i-a (i+1) ≤ 0)] at a_near
      omega
    · rw [abs_of_nonneg (by omega : 0 ≤ a i-a (i+1))] at a_near
      omega
  have power (i : ℕ) (hi : i < k) : (2:ℤ)^(i+1) ≤ a i-o i+1 := by
    induction i with
    | zero =>
      have := (input 0 hi).1; have := left 0 hi
      norm_num; omega
    | succ i ih =>
      have prev := ih (by omega)
      have next := growth i hi
      rw [pow_succ _ (i+1)]
      omega
  cases k with
  | zero => simpa using positive
  | succ t =>
    have ht := Nat.lt_succ_self t
    obtain ⟨v,hv,lv,uv⟩ := inside t ht
    have opt := greedy t ht v hv
    rw [dist t ht] at opt
    have ai := input t ht
    have bounded : |a t-v| ≤ (len:ℤ)-1 := abs_le.mpr ⟨by omega,by omega⟩
    have pw := power t ht
    exact_mod_cast (show (2:ℤ)^(t+1) ≤ len by omega)

end GenLimit.KleinbergWei.Banach.IntervalGame
