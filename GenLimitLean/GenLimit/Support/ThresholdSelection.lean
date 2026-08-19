import Mathlib.Data.Finset.Max

/-!
# Threshold-based component selection

Paper-independent helpers for combining a nondecreasing sequence of
component algorithms.  Padding a component threshold by its index makes the
eligible set finite; selecting its largest member lets later components take
over without losing an already-reached correctness threshold.
-/

namespace GenLimit.Support

/-- Pad a component threshold by its index. -/
def paddedThreshold (threshold : ℕ → ℕ) (n : ℕ) : ℕ :=
  max n (threshold n)

/-- Components whose padded threshold has been reached at size `k`. -/
def eligibleIndices (threshold : ℕ → ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter
    (fun n => paddedThreshold threshold n ≤ k)

theorem mem_eligibleIndices_iff
    {threshold : ℕ → ℕ} {n k : ℕ} :
    n ∈ eligibleIndices threshold k ↔
      paddedThreshold threshold n ≤ k := by
  simp only [eligibleIndices, Finset.mem_filter, Finset.mem_range,
    Nat.lt_add_one_iff]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(le_max_left n (threshold n)).trans h, h⟩

/-- The largest eligible component, with the irrelevant default `0` when no
component is eligible. -/
noncomputable def largestEligible
    (threshold : ℕ → ℕ) (k : ℕ) : ℕ := by
  classical
  let eligible := eligibleIndices threshold k
  exact if h : eligible.Nonempty then eligible.max' h else 0

theorem largestEligible_mem
    (threshold : ℕ → ℕ) (k : ℕ)
    (h : (eligibleIndices threshold k).Nonempty) :
    largestEligible threshold k ∈ eligibleIndices threshold k := by
  classical
  simp only [largestEligible, dif_pos h]
  exact Finset.max'_mem _ h

theorem le_largestEligible
    (threshold : ℕ → ℕ) (k n : ℕ)
    (hn : n ∈ eligibleIndices threshold k) :
    n ≤ largestEligible threshold k := by
  classical
  have h : (eligibleIndices threshold k).Nonempty := ⟨n, hn⟩
  simp only [largestEligible, dif_pos h]
  exact Finset.le_max' _ n hn

theorem largestEligible_threshold_le
    (threshold : ℕ → ℕ) (k : ℕ)
    (h : (eligibleIndices threshold k).Nonempty) :
    threshold (largestEligible threshold k) ≤ k := by
  have hpadded :
      paddedThreshold threshold (largestEligible threshold k) ≤ k :=
    mem_eligibleIndices_iff.mp (largestEligible_mem threshold k h)
  exact (le_max_right _ _).trans hpadded

end GenLimit.Support
