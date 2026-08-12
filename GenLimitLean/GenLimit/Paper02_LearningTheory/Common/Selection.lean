import GenLimit.Core.GenericGeneration
import Mathlib.Data.Finset.Max

/-!
# Small selection helpers for #02 Learning Theory

These definitions collect concrete choices repeated by several proofs in the
paper development.  They deliberately live under the paper namespace rather
than in `GenLimit.Core`: they are proof machinery, not part of the shared
semantic interface.
-/

namespace GenLimit.LiRamanTewari.Common

/-- Choose a point of an infinite set outside a finite observed sample. -/
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

/-- Pad a component threshold by its index.  This makes the set of eligible
indices finite without changing the validity of the threshold. -/
def paddedThreshold (threshold : ℕ → ℕ) (n : ℕ) : ℕ :=
  max n (threshold n)

/-- Components whose padded threshold has been reached at sample size `k`. -/
def eligibleIndices (threshold : ℕ → ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun n ↦ paddedThreshold threshold n ≤ k)

theorem mem_eligibleIndices_iff
    {threshold : ℕ → ℕ} {n k : ℕ} :
    n ∈ eligibleIndices threshold k ↔ paddedThreshold threshold n ≤ k := by
  simp only [eligibleIndices, Finset.mem_filter, Finset.mem_range,
    Nat.lt_add_one_iff]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨(le_max_left n (threshold n)).trans h, h⟩

/-- The largest component whose padded threshold has been reached, with the
irrelevant default `0` when no component is eligible. -/
noncomputable def largestEligible (threshold : ℕ → ℕ) (k : ℕ) : ℕ := by
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

end GenLimit.LiRamanTewari.Common
