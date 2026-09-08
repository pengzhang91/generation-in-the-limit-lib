import Mathlib.Data.Finset.Max

/-!
# Least candidates with a fallback

Paper-independent selection from a finite candidate set.  The fallback makes
the selector total; whenever a candidate exists, the selector is exactly the
least candidate and inherits the usual membership and minimality facts.
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

end GenLimit.Support
