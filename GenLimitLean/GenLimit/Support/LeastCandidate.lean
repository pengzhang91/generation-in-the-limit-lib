import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find

/-!
# Least candidates with a fallback

Paper-independent selection from a finite candidate set.  The fallback makes
the selector total; whenever a candidate exists, the selector is exactly the
least candidate and inherits the usual membership and minimality facts.

The module also supplies the least index naming the same object as a given
entry of an indexed family.  This is the shared duplicate-name convention
used by identification and generation reductions.
-/

namespace GenLimit.Support

/-- Select the least member of `candidates`, or `fallback` when the candidate
set is empty. -/
def leastCandidateWithFallback [LinearOrder α]
    (candidates : Finset α) (fallback : α) : α :=
  if h : candidates.Nonempty then candidates.min' h else fallback

theorem leastCandidateWithFallback_eq_min'
    [LinearOrder α] {candidates : Finset α} {fallback : α}
    (hne : candidates.Nonempty) :
    leastCandidateWithFallback candidates fallback = candidates.min' hne := by
  simp [leastCandidateWithFallback, hne]

theorem leastCandidateWithFallback_mem
    [LinearOrder α] {candidates : Finset α} {fallback : α}
    (hne : candidates.Nonempty) :
    leastCandidateWithFallback candidates fallback ∈ candidates := by
  rw [leastCandidateWithFallback_eq_min' hne]
  exact Finset.min'_mem _ _

theorem leastCandidateWithFallback_le
    [LinearOrder α] {candidates : Finset α} {fallback i : α}
    (hi : i ∈ candidates) :
    leastCandidateWithFallback candidates fallback ≤ i := by
  have hne : candidates.Nonempty := ⟨i, hi⟩
  rw [leastCandidateWithFallback_eq_min' hne]
  exact Finset.min'_le _ _ hi

/-! ## Least equivalent family indices -/

/-- The least index whose family entry is equal to the entry at `z`.
Repeated names are allowed, and no decidable equality on the entries is
required. -/
noncomputable def leastEquivalentIndex
    {β : Type*} (family : ℕ → β) (z : ℕ) : ℕ := by
  classical
  exact Nat.find
    (show ∃ i, family i = family z from ⟨z, rfl⟩)

theorem leastEquivalentIndex_spec
    {β : Type*} (family : ℕ → β) (z : ℕ) :
    family (leastEquivalentIndex family z) = family z := by
  classical
  exact Nat.find_spec
    (show ∃ i, family i = family z from ⟨z, rfl⟩)

theorem leastEquivalentIndex_minimal
    {β : Type*} (family : ℕ → β) (z i : ℕ)
    (hi : family i = family z) :
    leastEquivalentIndex family z ≤ i := by
  classical
  exact Nat.find_min'
    (show ∃ j, family j = family z from ⟨z, rfl⟩) hi

theorem leastEquivalentIndex_le_self
    {β : Type*} (family : ℕ → β) (z : ℕ) :
    leastEquivalentIndex family z ≤ z :=
  leastEquivalentIndex_minimal family z z rfl

theorem leastEquivalentIndex_ne_of_lt
    {β : Type*} (family : ℕ → β) (z : ℕ) {i : ℕ}
    (hi : i < leastEquivalentIndex family z) :
    family i ≠ family z := by
  intro heq
  exact (Nat.not_lt_of_ge
    (leastEquivalentIndex_minimal family z i heq)) hi

end GenLimit.Support
