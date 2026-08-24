import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Countable

/-!
# The signed-integer universe used by the union-closedness constructions

The paper's concrete witnesses split `ℤ` into the strictly negative and
strictly positive integers.  This small module contains only that shared
encoding.  The language classes and their generators live in later modules.

The split is intentionally local to this paper: unlike the nonpositive side
used by some other developments, neither side below contains zero.
-/

namespace GenLimit.UnionClosedness

/-- The paper's `ℤ₋ = {-1, -2, ...}`. -/
def negativeIntegers : Set ℤ := {z | z < 0}

/-- The canonical enumeration `-1, -2, ...` of the negative integers. -/
def negativeCode (n : ℕ) : ℤ := Int.negSucc n

theorem negativeCode_injective : Function.Injective negativeCode := by
  intro m n h
  exact Int.negSucc.inj h

theorem negativeCode_mem (n : ℕ) : negativeCode n ∈ negativeIntegers := by
  exact Int.negSucc_lt_zero n

theorem range_negativeCode : Set.range negativeCode = negativeIntegers := by
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    exact negativeCode_mem n
  · intro hz
    obtain ⟨n, hn⟩ := Int.eq_negSucc_of_lt_zero hz
    exact ⟨n, hn.symm⟩

theorem negativeIntegers_infinite : negativeIntegers.Infinite := by
  rw [← range_negativeCode]
  exact Set.infinite_range_of_injective negativeCode_injective

/-- Negative integers whose canonical indices start at `t`. -/
def negativeTail (t : ℕ) : Set ℤ :=
  Set.range (fun k : ℕ => negativeCode (t + k))

theorem negativeTail_infinite (t : ℕ) : (negativeTail t).Infinite := by
  apply Set.infinite_range_of_injective
  intro i j h
  exact Nat.add_left_cancel (negativeCode_injective h)

/-- The paper's `ℤ₊ = {1, 2, ...}`. -/
def positiveIntegers : Set ℤ := {z | 0 < z}

/-- The canonical enumeration `1, 2, ...` of the positive integers. -/
def positiveCode (n : ℕ) : ℤ := Int.ofNat (n + 1)

theorem positiveCode_injective : Function.Injective positiveCode := by
  intro m n h
  have hnat : m + 1 = n + 1 := Int.ofNat_inj.mp h
  omega

theorem positiveCode_mem (n : ℕ) : positiveCode n ∈ positiveIntegers := by
  simp [positiveCode, positiveIntegers]

theorem range_positiveCode : Set.range positiveCode = positiveIntegers := by
  apply Set.Subset.antisymm
  · rintro z ⟨n, rfl⟩
    exact positiveCode_mem n
  · intro z hz
    rcases z with n | n
    · have hn : 0 < n := by
        simpa [positiveIntegers] using hz
      obtain ⟨k, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      exact ⟨k, rfl⟩
    · simp [positiveIntegers] at hz

theorem positiveIntegers_infinite : positiveIntegers.Infinite := by
  rw [← range_positiveCode]
  exact Set.infinite_range_of_injective positiveCode_injective

/-- Positive integers whose canonical indices start at `t`. -/
def positiveTail (t : ℕ) : Set ℤ :=
  Set.range (fun k : ℕ => positiveCode (t + k))

theorem positiveTail_infinite (t : ℕ) : (positiveTail t).Infinite := by
  apply Set.infinite_range_of_injective
  intro i j h
  exact Nat.add_left_cancel (positiveCode_injective h)

end GenLimit.UnionClosedness
