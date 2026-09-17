import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Countable
import Mathlib.Data.Nat.Find

/-!
# Fresh selection from infinite sets

One paper-independent choice used throughout generation proofs: an infinite
set contains a point outside every finite set.
-/

namespace GenLimit.Support

/-- Choose a point of an infinite set outside a finite forbidden set. -/
noncomputable def freshFromInfinite
    (C : Set α) (hC : C.Infinite) (seen : Finset α) : α :=
  Classical.choose (hC.diff seen.finite_toSet).nonempty

theorem freshFromInfinite_mem
    (C : Set α) (hC : C.Infinite) (seen : Finset α) :
    freshFromInfinite C hC seen ∈ C :=
  (Classical.choose_spec (hC.diff seen.finite_toSet).nonempty).1

theorem freshFromInfinite_not_mem
    (C : Set α) (hC : C.Infinite) (seen : Finset α) :
    freshFromInfinite C hC seen ∉ seen :=
  (Classical.choose_spec (hC.diff seen.finite_toSet).nonempty).2

/-- The combined membership/freshness interface most generator constructions
need at their call site. -/
theorem freshFromInfinite_spec
    (C : Set α) (hC : C.Infinite) (seen : Finset α) :
    freshFromInfinite C hC seen ∈ C \ (seen : Set α) :=
  ⟨freshFromInfinite_mem C hC seen,
    freshFromInfinite_not_mem C hC seen⟩

/-! ## Least fresh natural numbers -/

/-- Choose the least member of an infinite set of naturals outside a finite
forbidden set.  Unlike `freshFromInfinite`, this selector exposes the order
property needed by the Kleinberg--Wei priority constructions. -/
noncomputable def leastFreshFromInfinite
    (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (hC.exists_notMem_finset seen)

theorem leastFreshFromInfinite_spec
    (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    leastFreshFromInfinite C hC seen ∈ C ∧
      leastFreshFromInfinite C hC seen ∉ seen := by
  classical
  exact Nat.find_spec (hC.exists_notMem_finset seen)

theorem leastFreshFromInfinite_mem
    (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    leastFreshFromInfinite C hC seen ∈ C :=
  (leastFreshFromInfinite_spec C hC seen).1

theorem leastFreshFromInfinite_not_mem
    (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    leastFreshFromInfinite C hC seen ∉ seen :=
  (leastFreshFromInfinite_spec C hC seen).2

theorem leastFreshFromInfinite_le
    (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ)
    {x : ℕ} (hxC : x ∈ C) (hxFresh : x ∉ seen) :
    leastFreshFromInfinite C hC seen ≤ x := by
  classical
  exact Nat.find_min' (hC.exists_notMem_finset seen) ⟨hxC, hxFresh⟩

end GenLimit.Support
